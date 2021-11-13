
using Catlab.WiringDiagrams
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSetDataStructures: struct_acset
using Catlab.GAT
using Catlab.GAT: Theory, TermConstructor, AxiomConstructor,strip_type, equations,
              get_type, has_type, Context

using AutoHashEquals
using DataStructures

const PSI = Pair{Symbol,Int}
const VPSI = Vector{PSI}
const VPII = Vector{Pair{Int,Int}}
const Expr0 = Union{Symbol,Expr}

"""
A rewrite rule encoded as a pair of wiring diagrams. Inputs/outputs get
identified with each other, and any other mappings are manually specified (e.g.
to say that the "e" of one monoid diagram is the same "e" in another - otherwise
a new "e" box would be introduced via the chase).
"""
@auto_hash_equals struct Eq
  name::Symbol
  l::WiringDiagram
  r::WiringDiagram
  rev::Bool
  mapping::Vector{Pair{Symbol,Vector{Pair{Int,Int}}}}
  function Eq(n,l,r,v,m)
    # Basic validation
    ipl, ipr = input_ports(l), input_ports(r)
    ipl == ipr || error("$n: Input port mismatch: $ipl != $ipr")
    opl, opr = output_ports(l), output_ports(r)
    opl == opr || error("$n: Output port mismatch: $opl != $opr")
    for (_, kvs) in m
      length(kvs) == length(Set(first.(kvs))) || error("bad function $n: $m")
    end
    return new(n,l,r,v,m)
  end
end
# Assume Eq is reversible by default
Eq(n,l,r) = Eq(n,l,r,true,Pair{Symbol,VPII}[])
# Assume there are no other mappings by default
Eq(n,l,r,b::Bool) = Eq(n,l,r,b,Pair{Symbol,VPII}[])
# If there are other mappings, assume it is NOT reversible by default
Eq(n,l,r,m::Vector{Pair{Symbol,VPII}}) = Eq(n,l,r,false,m)

function Base.isless(x::Eq, y::Eq)::Bool
  return Base.isless(x.name, y.name)
end

"""Helper function for `flip`"""
function invert(h::Vector{Pair{Symbol,VPII}})::Vector{Pair{Symbol,VPII}}
  return [k=>[(b=>a) for (a,b) in v] for (k,v) in h]
end

"""Reverse a rewrite rule"""
flip(x::Eq)::Eq = x.rev ? Eq(Symbol("$(x.name)_rev"), x.r, x.l, x.rev,
  invert(x.mapping)) : error("Cannot flip $(x.name)")

"""Default introduction rule for operation assumes it is total"""
function intro_rule(gen::Box{Symbol})::Eq
  l, r = [WiringDiagram(gen.input_ports, Symbol[]) for _ in 1:2]
  rb = add_box!(r, gen)
  for (i, typ) in enumerate(gen.input_ports)
    b = add_box!(l, Junction(typ, 1, 0))
    add_wire!(l, (input_id(l), i)=>(b,1))
    add_wire!(r, (input_id(r), i)=>(rb,i))
  end
  for (i, typ) in enumerate(gen.output_ports)
    b = add_box!(r, Junction(typ, 1, 0))
    add_wire!(r, (rb, i)=>(b, 1))
  end
  return Eq(Symbol(string(gen.value)*"_intro"), l, r, false)
end

"""Create Eq asserting that an operation is singlevalued"""
function singlevalued_rule(gen::Box{Symbol})::Eq
  op = gen.output_ports
  no = length(op)
  l, r = [WiringDiagram(gen.input_ports, [op...,op...]) for _ in 1:2]
  lb1, lb2 = add_boxes!(l, [gen, gen])
  rb = add_box!(r, gen)

  for (i, typ) in enumerate(gen.input_ports)
    lδ = add_box!(l, Junction(typ, 1, 2))
    add_wires!(l, Pair[
      (input_id(l), i)=>(lδ,1),
      (lδ, 1) => (lb1, i),
      (lδ, 2) => (lb2, i)])
    add_wire!(r, (input_id(r), i)=>(rb,i))
  end
  for (i, typ) in enumerate(op)
    rδ = add_box!(r, Junction(typ, 1, 2))
    add_wires!(r, Pair[
      (rb, i)=>(rδ,1),
      (rδ, 1) => (output_id(r), i),
      (rδ, 2) => (output_id(r), i+no)])
    add_wires!(l, Pair[
      (lb1,i)=>(output_id(l), i),
      (lb2,i)=>(output_id(l), i+no)])
    end

  return Eq(Symbol(string(gen.value)*"_sv"), l, r, false,
            [gen.value=>[1=>1, 2=>1]])

end
"""A named theory with a signature (possible relations) and equations"""
struct EqTheory
  name :: Symbol
  gens :: Vector{Box{Symbol}}
  eqs  :: Vector{Eq}
  function EqTheory(n::Symbol, gs::Vector{Box{Symbol}}, es::Vector{Eq}; cartesian::Union{Nothing,Vector{Symbol}}=nothing)

    Σd = DefaultDict{Symbol, Vector{Pair{Vector{Symbol}, Vector{Symbol}}}}(()->[])
    for b in gs
      push!(Σd[b.value], (b.input_ports => b.output_ports))
    end
    es = deepcopy(es)
    esyms = Set{Symbol}()
    for eq in es
      for (k,_) in eq.mapping
        haskey(Σd, k) || error("bad symbol in mapping $k")
      end
      for wd in [eq.l, eq.r]
        # Converting left and right into ACSets should not throw error
        wd_to_acset(new(n, gs,es), wd)
        for b in boxes(wd)
          if haskey(Σd, b.value)
            ps = b.input_ports => b.output_ports
            e = "Wd $wd Box $b has mismatch with signature $Σd"
            ps ∈ Σd[b.value] || error(e)
          else
            e = "Wd $wd Unknown box symbol $(b.value) for $Σd"
            b isa Junction || error(e)
          end
        end
      end
      push!(esyms, eq.name)
    end
    # Create total intro and singlevalued axioms for each gen if not in eqs.
    # (if `cartesian` is true)
    for gen in gs
      v = gen.value
      si, ss = [Symbol(string(v)*x) for x in ["_intro", "_sv"]]
      cnone = !isnothing(cartesian)
      (cnone && (v ∉ cartesian)) || si ∈ esyms || push!(es, intro_rule(gen))
      (cnone && (v ∉ cartesian)) || ss ∈ esyms || push!(es, singlevalued_rule(gen))
    end
    return new(n, gs,[collapse(n, gs, e) for e in es])
  end
end

"""List all axioms, including reverses"""
eq_w_rev(t::EqTheory)::Vector{Eq} = vcat(
  [e.rev ? [e, flip(e)] : [e] for e in t.eqs]...)

function Base.show(io::IO, ::MIME"text/plain", t::EqTheory)
  println(io,"generators: $(join([g.value for g in t.gens], " "))")
  println(io,"equations: $(string([eq.name for eq in eq_w_rev(t)]))")
end

function Base.union(n::Symbol, t::EqTheory, g::Vector{Box{Symbol}},
                    eq::Vector{Eq})::EqTheory
  return EqTheory(n, union(t.gens, g), union(t.eqs, eq))
end

"""Get an axiom by name, including <AXIOM>_rev if it's reversible"""
function Base.getindex(t::EqTheory, x::Symbol)::Eq
  sx = string(x)
  x_ = length(sx) > 4 && sx[end-3:end] == "_rev" ? Symbol(sx[1:end-4]) : nothing
  for eq in t.eqs
    if eq.name == x
      return eq
    elseif eq.name == x_ && eq.rev
      return flip(eq)
    end
  end
  throw(KeyError(x))
end

"""Signature of a box type when viewed as a relation"""
function arity(t::EqTheory, x::Symbol)
  for g in t.gens
    if g.value == x
      return vcat(g.input_ports, g.output_ports)
    end
  end
  throw(KeyError(x))
end

"""
All of the base sorts (i.e. vertex colors, if viewing ACSet instances as
hypergraphs)
"""
sorts(t::EqTheory)::Vector{Symbol} = sorts(t.gens)

function sorts(gens::Vector{Box{Symbol}})::Vector{Symbol}
  sort(collect(Set(vcat([vcat(g.input_ports,g.output_ports) for g in gens]...))))
end


"""
Get a vector of relation/table names given an Eq theory. Complicated by the fact
that box names need not be unique (can be differentiated by arg types).
"""
function rel_syms(gens::Vector{Box{Symbol}})::Vector{Symbol}
  counter = DefaultDict{Symbol, Int}(()->0)
  symbs = Symbol[]
  for g in gens
    counter[g.value] += 1
    suffix = counter[g.value] == 1 ? "" : "__$(counter[g.value])"
    push!(symbs, Symbol("$(g.value)$suffix"))
  end
  return symbs
end

"""
The boxes of an EqTheory determine an ACSet type

We may need to disambiguate different boxes with the same symbol
"""
theory_to_acset_type(t::EqTheory) = theory_to_acset_type(t.name, t.gens)

function theory_to_acset_type(name::Symbol, t::Vector{Box{Symbol}})
  pres = Presentation(FreeSchema)
  sortobs = Dict([s=>Ob(FreeSchema, s) for s in sorts(t)])
  for s in values(sortobs)
    add_generator!(pres, s)
  end

  for (g, s) in zip(t, rel_syms(t))
    b = add_generator!(pres, Ob(FreeSchema, s))
    for (i, p) in enumerate(vcat(g.input_ports, g.output_ports))
      add_generator!(pres, Hom(Symbol("$(s)_$i"), b, sortobs[p]))
    end
  end
  expr = struct_acset(name, StructACSet, pres)
  try
    eval(name)
  catch _
    eval(expr) # needs to run in order to declare the acset
  end
  return eval(name) # acset type as variable
end

"""
Convert wiring diagram to ACSet representation. Any connected wire component is
converted to an element of a sort type (e.g. `Ob`, `Hom`). Each type of box is
a relation on these. Keep track of which elements are inputs/outputs through
two vectors which are also returned.
"""
wd_to_acset(t::EqTheory, wd::WiringDiagram)::Tuple{StructACSet, VPSI, VPSI} = wd_to_acset(t.name, t.gens, wd)

function wd_to_acset(name::Symbol, t::Vector{Box{Symbol}}, wd::WiringDiagram
                     )::Tuple{StructACSet, VPSI, VPSI}
  wd = deepcopy(wd)
  d = wd.diagram
  # Preprocess
  for op in parts(d, :OuterOutPort)
    if isempty(incident(d, op, :out_tgt))
      add_wire!(wd,
        (add_box!(wd, Junction(d[op, :outer_out_port_type], 0, 1)), 1)
          => (output_id(wd), op))
    end
  end

  for ip in parts(d, :OuterInPort)
    if isempty(incident(d, ip, :in_src))
      add_wire!(wd,
        (input_id(wd), ip)
           => (add_box!(wd, Junction(d[ip, :outer_in_port_type], 1, 0)), 1))
    end
  end

  for bx in parts(d, :Box)
    for (op_ind, op) in enumerate(incident(d, bx, :out_port_box))
      if isempty(incident(d, op, :src))
        b, typ = d[op, :out_port_box], d[op, :out_port_type]
        add_wire!(wd, (b,op_ind)=>(add_box!(wd, Junction(typ, 1, 0)), 1))
      end
    end
    for (ip_ind, ip) in enumerate(incident(d, bx, :in_port_box))
      if isempty(incident(d, ip, :tgt))
        b, typ = d[ip, :in_port_box], d[ip, :in_port_type]
        add_wire!(wd, (add_box!(wd, Junction(typ, 0, 1)), 1)=>(b,ip_ind))
      end
    end
  end

  syms = Dict([b=>s for (s, b) in zip(rel_syms(t), t)])

  I = Base.invokelatest(theory_to_acset_type(name, t))
  allports = Dict([p=>i for (i,p) in enumerate(sort(collect(Set(vcat(
    [[w.source,w.target] for w in wires(wd)]...)))))])
  eq = IntDisjointSets(length(allports))
  for w in wires(wd)
    union!(eq, allports[w.source], allports[w.target])
  end
  for (i, _) in filter(x->x[2] isa Junction, collect(enumerate(boxes(wd))))
    bports = [p_i for (p, p_i) in allports if p.box == i]
    for (i1, i2) in zip(bports, bports[2:end])
      union!(eq, i1, i2)
    end
  end

  id_map = Dict{Int,Int}()
  for (x, i) in allports
    parent = find_root(eq, i)
    if !haskey(id_map, parent)
      id_map[parent] = add_part!(I, port_value(wd, x))
    end
  end

  for (i, b) in filter(x->x[2] isa Box, collect(enumerate(boxes(wd))))
    sym = syms[b]
    ps = vcat(sort(collect(values(Dict([
      iw.target.port=>iw.target for iw in in_wires(wd, i)]))), by=x->x.port),
      sort(collect(values(Dict([ow.source.port=>ow.source
      for ow in out_wires(wd, i)]))), by=x->x.port))
    vs = [id_map[find_root(eq, allports[p])] for p in ps]
    di = Dict([Symbol("$(sym)_$i") => v for (i, v) in enumerate(vs)])
    add_part!(I, sym; di...)
  end
  i_ids = last.(sort(collect(Dict([w.source.port => id_map[find_root(eq, allports[w.target])]
                      for w in out_wires(wd, input_id(wd))]))))
  o_ids = last.(sort(collect(Dict([w.target.port => id_map[find_root(eq, allports[w.source])]
                      for w in in_wires(wd, output_id(wd))]))))
  i_psi, o_psi = [[a=>b for (a,b) in zip(f(wd), ids)]
                  for (f, ids) in [input_ports=>i_ids, output_ports=>o_ids]]
  return I, i_psi, o_psi
end

"""Hypergraph cospans: go from ACSet representation to WD representation"""
acset_to_wd(t::EqTheory, I::StructACSet, ins::VPSI=PSI[],
  outs::VPSI=PSI[])::WiringDiagram = acset_to_wd(t.gens, I, ins, outs)

acset_to_wd(t::EqTheory, Iio::Tuple{T_,VPSI,VPSI}
            ) where T_<:StructACSet = acset_to_wd(t, Iio[1], Iio[2], Iio[3])

function acset_to_wd(t::Vector{Box{Symbol}}, I::StructACSet, ins::VPSI=PSI[],
                     outs::VPSI=PSI[])::WiringDiagram
  wd = WiringDiagram(first.(ins),first.(outs))
  ind, outd = [[(k=>v)=>i for (i, (k, v)) in enumerate(x)] for x in [ins, outs]]
  juncts = Dict{Pair{Symbol, Int}, Int}()
  for s in sorts(t)
    for i in parts(I, s)
      juncts[s=>i] = add_box!(wd, Junction(s, 1,1))
      for v in last.(filter(kv->kv[1]==(s=>i), ind))
        add_wire!(wd, (input_id(wd), v)=>(juncts[s=>i], 1))
      end
      for v in last.(filter(kv->kv[1]==(s=>i), outd))
        add_wire!(wd, (juncts[s=>i], 1) => (output_id(wd), v))
      end
    end
  end
  for (g, s) in zip(t, rel_syms(t))
    for i in parts(I, s)
      b = add_box!(wd, g)
      for (i_in, typ) in enumerate(g.input_ports)
        col = Symbol("$(s)_$i_in")
        add_wire!(wd, (juncts[typ=>I[col][i]], 1)=>(b, i_in))
      end
      for (i_out, typ) in enumerate(g.output_ports)
        col = Symbol("$(s)_$(length(g.input_ports)+i_out)")
        add_wire!(wd, (b, i_out)=>(juncts[typ=>I[col][i]], 1))
      end
    end
  end
  return wd
end

"""Take connected components and compress them into a single junction"""
collapse(t::EqTheory, wd::WiringDiagram)::WiringDiagram = collapse(
  t.name, t.gens, wd)
collapse(name::Symbol, gens::Vector{Box{Symbol}}, eq::Eq)::Eq = Eq(
  eq.name, collapse(name, gens, eq.l), collapse(name, gens, eq.r),
  eq.rev, eq.mapping)
function collapse(name::Symbol, gens::Vector{Box{Symbol}}, wd::WiringDiagram)::WiringDiagram
  a,b,c = wd_to_acset(name, gens, wd)
  return  acset_to_wd(gens, a, b, c)
end

"""Helper function for eq_to_ed and csp_homomorphism"""
function add_vertex!(sym::Symbol, xs::Int, xt::Int,
                     hs::DefaultDict{Symbol,Vector{Int}},
                     ht::DefaultDict{Symbol,Vector{Int}},
                     overlap::StructACSet)::Int
  push!(hs[sym], xs)
  push!(ht[sym], xt)
  return add_part!(overlap, sym)
end

"""
Convert constraint from pair-of-wiring-diagrams form into homomorphism form
TODO: this breaks when the EqTheory has overloaded symbols, currently.
"""
function eq_to_ed(th::EqTheory, e::Eq)::ED
  (S, si, so), (T, ti, to) = [wd_to_acset(th, x) for x in [e.l, e.r]]
  overlap = Base.invokelatest(theory_to_acset_type(th))
  hs, ht = [DefaultDict{Symbol,Vector{Int}}(()->Int[]) for _ in 1:2]

  for ((sym, xs), (_, xt)) in [zip(si, ti)..., zip(so, to)...]
    add_vertex!(sym, xs, xt, hs, ht, overlap)
  end
  for (k, sts) in e.mapping
    for (s, t) in sts
      svals = [S[Symbol("$(k)_$i")][s] for i in 1:length(arity(th, k))]
      tvals = [T[Symbol("$(k)_$i")][t] for i in 1:length(arity(th, k))]
      ovals = Dict([Symbol("$(k)_$i")=>add_vertex!(srt, sv, tv, hs, ht, overlap)
        for (i, (srt, sv, tv)) in enumerate(zip(arity(th, k), svals, tvals))])
      add_part!(overlap, k; ovals...)
      push!(hs[k], s)
      push!(ht[k], t)
    end
  end
  h = legs(pushout(ACSetTransformation(overlap,S; hs...),
                   ACSetTransformation(overlap,T; ht...)))[1]
  return ED(h)
end

"""Convert Eq's of a theory into ED homomorphisms"""
function all_eds(t::EqTheory, eqs::Vector{Symbol}=Symbol[])::Vector{ED}
  return filter(x->!isnothing(x),[
    (e.name in eqs)  || isempty(eqs) ? eq_to_ed(t,e) : nothing
    for e in eq_w_rev(t)])
end

"""
Run chase algorithm on a wiring diagram, return result as a wiring diagram.
"""
function chase_theory(t::EqTheory, I::WiringDiagram, n::Int,
                      eqs::Vector{Symbol}=Symbol[])::WiringDiagram
  res, ri, ro = chase(wd_to_acset(t, I), all_eds(t,eqs), n)
  return acset_to_wd(t, res, ri, ro)
end

"""
Cospan homomorphism: morphism of wiring diagrams that fixes the inputs/outputs

  X1
 ↗   ↖
I  ↓  O
 ↘   ↙
   X2
"""
function csp_homomorphism(th::EqTheory, s::WiringDiagram,t::WiringDiagram
                          )::Union{Nothing, ACSetTransformation}
  (S, si, so), (T, ti, to) = [wd_to_acset(th, x) for x in [s, t]]
  interface = Base.invokelatest(typeof(S))
  h_s, h_t = [DefaultDict{Symbol,Vector{Int}}(()->Int[]) for _ in 1:2]
  for ((sym, xs), (_, xt)) in [zip(si, ti)..., zip(so, to)...]
    add_vertex!(sym, xs, xt, h_s, h_t, interface)
  end
  i_s = ACSetTransformation(interface, S; h_s...)
  i_t = ACSetTransformation(interface, T; h_t...)
  mc = morphism_constraint(i_s, i_t)
  return mc === nothing ? nothing : homomorphism(S, T, initial=mc)
end

"""Whether or not a cospan homomorphism exists"""
function csp_homomorphic(th::EqTheory, s::WiringDiagram,t::WiringDiagram
  )::Bool
  !(csp_homomorphism(th,s,t)===nothing)
end

# Helper functions for WD construction
######################################

"""
Helper function to construct string diagram equations with @program macro.

Co-diagonals only merge wires when they are passed to an output, so sometimes we
must create 'fake' outputs and then trim them away (replacing with a junction).
We keep the first `O` outputs and `I` inputs, defaulting to keeping all inputs
and no outputs.
"""
function trim(wd::WiringDiagram, n_out::Int=0, n_in::Int=-1)::WiringDiagram
  wd = deepcopy(wd)
  n_in = n_in < 0 ? length(input_ports(wd)) : n_in
  d = Dict{Port, Int}()
  for (i, p) in enumerate(input_ports(wd))
      if i > n_in
          d[Port(input_id(wd), OutputPort, i)] = add_box!(wd,Junction(p,0,1))
      end
  end
  for (i, p) in enumerate(output_ports(wd))
      if i > n_out
          d[Port(output_id(wd), InputPort, i)] = add_box!(wd,Junction(p,1,0))
      end
  end
  for w in wires(wd)
      if haskey(d, w.source)
          add_wire!(wd, Port(d[w.source],OutputPort, 1) => w.target)
      end
      if haskey(d, w.target)
          add_wire!(wd,w.source =>  Port(d[w.target],InputPort, 1))
      end
      if haskey(d, w.source) || haskey(d, w.target)
          rem_wire!(wd, w)
      end
  end
  rem_parts!(wd.diagram, :OuterInPort, n_in+1:length(input_ports(wd)))
  rem_parts!(wd.diagram, :OuterOutPort, n_out+1:length(output_ports(wd)))
  return wd
end


"""
Convert a signature into a catlab theory that can construct string diagram
equations via the @program macro. TODO: handle overloaded names better if
possible. Currently just keep the first seen generator with a given name.
"""
function get_pres(gs::Vector{Box{Symbol}})::Presentation
  p = Presentation(FreeBiproductCategory)
  srts = Set(vcat([vcat(g.input_ports,g.output_ports) for g in gs]...))
  for x in srts
    add_generator!(p, Ob(FreeBiproductCategory,x))
  end
  for g in gs
    if !has_generator(p, g.value)
      s, t = [isempty(ps) ? munit(FreeBiproductCategory.Ob) : otimes([p[x] for x in ps])
              for ps in [g.input_ports, g.output_ports]]
      add_generator!(p, Hom(g.value, s, t))
    end
  end
  return p
end


# Substitutions / transformations
#--------------------------------
"""
This could be generally useful: reverse diagram directionality
"""
function invert_wd(wd::WiringDiagram)::WiringDiagram
  wd2 = deepcopy(wd);
  d, d2 = wd.diagram, wd2.diagram;
  ports = [:InPort, :OutPort]
  oports = [ :OuterInPort, :OuterOutPort]
  owires = [:InWire, :OutWire]
  for x in vcat([:Wire, :PassWire], ports, oports, owires)
    rem_parts!(d2, x, parts(d2, x));
  end

  add_parts!(d2,  :InPort, nparts(d, :OutPort);
             in_port_box=d[:out_port_box], in_port_type=d[:out_port_type])
  add_parts!(d2, :OutPort, nparts(d, :InPort);
             out_port_box=d[:in_port_box], out_port_type=d[:in_port_type])
  add_parts!(d2, :OuterInPort, nparts(d, :OuterOutPort);
             outer_in_port_type=d[:outer_out_port_type])
  add_parts!(d2, :OuterOutPort, nparts(d, :OuterInPort);
             outer_out_port_type=d[:outer_in_port_type])
  add_parts!(d2, :Wire, nparts(d, :Wire);
             src=d[:tgt], tgt=d[:src], wire_value=d[:wire_value])
  add_parts!(d2, :PassWire, nparts(d, :PassWire);
             pass_src=d[:pass_tgt], pass_tgt=d[:pass_src],
             pass_wire_value=d[:pass_wire_value])
  add_parts!(d2,  :InWire, nparts(d, :OutWire); in_src=d[:out_tgt],
             in_tgt=d[:out_src], in_wire_value=d[:out_wire_value])
  add_parts!(d2, :OutWire, nparts(d, :InWire); out_tgt=d[:in_src],
             out_src=d[:in_tgt], out_wire_value=d[:in_wire_value])
  return wd2
end

"""Substituting symbols in the wiring diagrams of Eqs"""
substitute_syms(syms::Vector{Pair{String, String}},
                         names::Vector{Pair{String, String}},
                         eqs::Vector{Eq}; invert::Bool=false)::Vector{Eq} = [
  substitute_syms(syms, names, e; invert=invert) for e in eqs]

substitute_syms(syms::Vector{Pair{String, String}}, names::Vector{Symbol},
                eqs::Vector{Eq}; invert::Bool=false)::Vector{Eq} = [
  substitute_syms(syms, name, e; invert=invert) for (e, name) in zip(eqs,names)]

"""Substituting symbols in the wiring diagrams of an Eq"""
substitute_syms(syms::Vector{Pair{String, String}},
  names::Vector{Pair{String, String}},
  eq::Eq; invert::Bool=false)::Eq = substitute_syms(
    syms, Symbol(replaces(string(eq.name), names)), eq; invert=invert)

function substitute_syms(syms::Vector{Pair{String, String}}, name::Symbol,
                         eq::Eq; invert::Bool=false)::Eq
  inv = x-> invert ? invert_wd(x) : x
  syms_ = [Symbol(a)=>Symbol(b) for (a,b) in syms]
  sympairs = Dict{Symbol,Symbol}(vcat([[a=>b,b=>a] for (a,b) in syms_]...))
  new_map = [get(sympairs, k, k)=>v for (k,v) in eq.mapping]
  return Eq(name, inv(substitute_syms(sympairs, eq.l)),
            inv(substitute_syms(sympairs, eq.r)), eq.rev, new_map)
end

"""Perform substitution on box symbols"""
function substitute_syms(symd::Dict{Symbol, Symbol}, wd::WiringDiagram
                         )::WiringDiagram
  wd = deepcopy(wd)
  set_subpart!(wd.diagram, :value,
               map(x->get(symd, x, x), wd.diagram[:value]))
  return wd
end

"""
Multiple disjoint replacements.
We do not resubstitute for the result of something that's already been
  substituted. And we prioritize bigger subsitutions over smaller, e.g.

  replaces(plusop_zero, [plus=>1, plusop=>2,zero=>3, op_zer=>4])
  should return: 2_3
"""
function replaces(x,ys)
  ys2 = vcat([[[a,b],[b,a]] for (a,b) in ys]...)
  ysort = sort(ys2, by=x->length(x[1]), rev=true)
  ydict = Dict(ys)
  xtokens = [x => false]
  for y1 in first.(ysort)
    xtokens = vcat(map( sb -> sb[2] ? sb : vcat([[y1=>true, x=>false]
                for x in split(sb[1], y1)]...)[2:end], xtokens)...)
  end
  return join(map(x->get(ydict, x, x), first.(xtokens)))
end


# Conversion of Catlab Theories to EqTheories
#############################################

"""
Convert Catlab theory to an EqTheory.
"""
function EqTheory(x::DataType)::EqTheory
  t = theory(x)

  # Boxes that correspond to parameters to type constructors are total/s.v.
  cart_boxes = Box{Symbol}[]
  for typ in t.types
    for (fun, funtype) in collect(typ.context)
        push!(cart_boxes, Box(fun, [typ.name], [funtype]))
    end
  end
  cart = [b.value for b in cart_boxes]

  # Generate suffixes for overloaded term constructors
  tcount = DefaultDict{Symbol, Int}(()->0)
  suffixes = Symbol[]
  for trm in t.terms
    tcount[trm.name] += 1
    push!(suffixes, Symbol(
      tcount[trm.name] == 1 ? "" : "__$(tcount[trm.name])"))
  end
  # Create boxes and intro rules
  box_intros = [make_box(t, trm, s) for (trm, s) in zip(t.terms, suffixes)]
  bs = first.(box_intros)
  # Create singlevalued rules for every operation
  box_svs = [Eq(Symbol("$(string(eq.name)[1:end-3])$(s)_sv"),
                eq.l, eq.r, eq.rev, eq.mapping)
             for (eq, s) in zip(singlevalued_rule.(bs), suffixes)]
  # Create Eqs for all axioms
  eqs = Eq[[make_eq(t, i, eq) for (i, eq) in enumerate(t.axioms)]...,
        last.(box_intros)..., box_svs...]
  # Assemble an EqTheory
  thry= EqTheory(x.name.name, vcat(cart_boxes, bs), eqs; cartesian=cart)
  # Simplify terms of the theory
  return trim_theory(x, thry)
end

"""
Simplify the expressions that are automatically generated when converting a
Catlab theory into an EqTheory. This is called as the final step in that process
"""
function trim_theory(x::DataType, thry::EqTheory)::EqTheory
  t = theory(x)
  # Apply collapse . trim_term to each left and right pattern
  neweqs = [Eq(eq.name,
    collapse(thry, trim_term(t, eq.l)),
    collapse(thry, trim_term(t, eq.r)),
    eq.rev, eq.mapping) for eq in thry.eqs]
  newthry = EqTheory(x.name.name, thry.gens, neweqs)

  # Confirm this new theory has the same # of boxes and Eqs
  nen, en = [[e.name for e in z.eqs] for z in [newthry, thry]]
  length(nen)==length(en) || error("eq # \n$nen\n$en")
  length(newthry.gens)==length(thry.gens) || error("gen #")
  return newthry
end

"""Convert GAT term into a wiring diagram"""
function term_to_wd(t::Theory, ctx, trm, ins=Symbol[])::WiringDiagram
    ityps = [k=>strip_type(v) for (k, v) in ctx if (isempty(ins) || k in ins)]
    wd = WiringDiagram(last.(ityps), [nothing])
    d = Dict{Expr0, Int}()
    add_ctx!(wd,d, t, ctx)
    add_term!(wd, d, trm, t)
    set_output_ports!(wd, box(wd, d[trm]).output_ports)
    add_wires!(wd, [(d[trm],1)=>(output_id(wd), 1),[
                (input_id(wd), i)=>(d[p], 1)
                for (i,p) in enumerate(first.(ityps))]...])
    return wd
end

"""Determine if axiom contains a given symbol"""
function ax_contains(eq::AxiomConstructor, k::Symbol)::Bool
    return term_contains(eq.left, k) || term_contains(eq.right, k)
end
term_contains(trm::Symbol, k::Symbol) = trm == k
term_contains(trm::Expr, k::Symbol) = any(
    term_contains(arg,k) for arg in trm.args[2:end])

"""Recursively compute which boxes are redundant"""
function get_redun(wd, t::Theory, redun::Set{Int})::Set{Int}
    d = wd.diagram
    # wires out for each box
    b_ows = [incident(d, b, [:src, :out_port_box]) for b in parts(d, :Box)]
    # # of wires into each box
    b_iws = [length(vcat(incident(d, b, [:tgt, :in_port_box]),
                         incident(d,b,[:in_tgt, :in_port_box])))
             for b in parts(d, :Box)]

    # target boxes for each wire
    tgts = d[parts(d, :Wire), [:tgt, :in_port_box]]
    # target boxes for each box
    btgts = [union([tgts[ow] for ow in ows]) for ows in b_ows]
    # boxes connected to output
    outbxs = Set(d[[:out_src, :out_port_box]])

    connames = vcat([typ.params for typ in t.types]...)
    junc_cons = Set([i for (i,b) in enumerate(boxes(wd))
                     if b isa Junction || b.value in connames])
    f = i -> all([i ∉ outbxs, i ∈ junc_cons, b_iws[i] <= 1,
                  isempty(setdiff(btgts[i], redun))])
    return Set(filter(f, parts(d, :Box)))
end

"""
Remove redundant pieces of a wiring diagram.
"""
function trim_term(t::Theory,wd::WiringDiagram)::WiringDiagram
    redun = Set{Int}()
    changed = true
    while changed
        new_redun = get_redun(wd, t, redun)
        changed = redun != new_redun
        redun = new_redun
    end
    return remove_boxes(wd, sort(collect(redun)))
end

"""
This seems generally useful: delete DWD boxes without worrying about index order
"""
function remove_boxes(wd::WiringDiagram, boxes::Vector{Int})
  old_d = wd.diagram
  wd = deepcopy(wd)
  d = wd.diagram
  dic = Dict{Symbol, Vector{Int}}()
  # Get in/outports and wires connected to them
  ip = vcat(incident(d, boxes, :in_port_box)...)
  op = vcat(incident(d, boxes, :out_port_box)...)
  wi = vcat(incident(d, ip, :tgt)..., incident(d, op, :src)...)
  wo = vcat(incident(d, op, :src)..., incident(d, op, :tgt)...)
  rem = Dict((Box=boxes, OutPort=op, InPort=ip, Wire=vcat(wi,wo)))
  for prt in [:Box, :InPort, :OutPort, :OuterInPort, :OuterOutPort,
              :Wire, :OutWire, :InWire]
      rem_parts!(d, prt, parts(d, prt))
      dic[prt] = setdiff(parts(old_d, prt), get(rem, prt, Int[]))
  end
  copy_parts!(d, old_d; dic...)
  for (ip, (_, typ)) in filter(x->x[2][1]==0, collect(enumerate(zip(
                               d[:in_tgt], d[[:in_src, :outer_in_port_type]]))))
    set_subpart!(d, ip, :in_tgt, add_box!(wd, Junction(typ, 1, 0)))
  end
  return wd
end

"""
Convert an axiom into an Eq

TODO: determine the Eq.mapping automatically.
"""
function make_eq(t::Theory, i::Int, eq::AxiomConstructor)::Eq
  # Only keep inputs that are featured in the left or right terms
  ins = filter(k->ax_contains(eq,k), keys(eq.context))
  l = term_to_wd(t,eq.context, eq.left, ins)
  r = term_to_wd(t,eq.context, eq.right, ins)
  return Eq(Symbol("$(eq.name)_$i"), l, r)
end

"""
Modify the wiring diagram and update dict which points (sub)terms to their
vertices in the wiring diagram.
"""
function add_term!(wd::WiringDiagram, d::Dict{Expr0, Int}, e::Expr0, t::Theory
                   )::Int
  # check if we've already added this term
  if haskey(d, e) || e isa Symbol
    return d[e]
  end

  # outermost operation of the expression
  ehead = strip_type(e)

  # recursively add subterms
  args = [add_term!(wd, d, arg, t) for arg in e.args[2:end]]

  # sorts for the arguments
  argtypes = [box(wd, arg).value for arg in args]
  restype = Symbol() # TBD, will compute later

  # Three cases: term constructor, type constructor, or type parameter
  # 1.) Search for `ehead` through term constructors
  for trm in t.terms
    targs = [strip_type(trm.context[p]) for p in trm.params]
    argmatch = argtypes == targs     # differentiate ops with same name
    if trm.name == ehead && argmatch # e.g. e = compose(f, compose(g, id(C)))
        restype = strip_type(trm.typ)
        # box corresponding to outermost operation
        bx = add_box!(wd, Box(ehead, argtypes, [restype]))
        # vertex corresponding to the value of the result of this operation
        d[e] = add_box!(wd, Junction(restype, 1,1)) # cache result
        # connect inputs and outputs to the new box
        add_wires!(wd, [[(arg,1)=>(bx,i) for (i, arg) in enumerate(args)]...,
                        (bx,1)=>(d[e],1)])
    end
  end
  # 2.) In case it's not a term constructor, check type constructors
  if has_type(t, ehead) # e.g. e = Hom(A, codom(f))
    typ = get_type(t, ehead)
    d[e] = add_box!(wd, Junction(ehead, 1, 1)) # cache result
    # If we create a new instance of a type, we need to freely add terms
    # corresponding to its parameters. E.g. if we add a Hom, it needs dom/codom
    for (con, tgtid, tgttyp) in zip(typ.params, args, argtypes)
        bx = add_box!(wd, Box(con, [ehead], [tgttyp]))
        add_wires!(wd, [(d[e],1)=>(bx,1), (bx,1)=>(tgtid, 1)])
    end
  else
    # 3.) Check if it's a parameter to a type, e.g. `dom` of Hom(dom, codom)
    for typ in t.types
      if ehead in typ.params # e.g. e = dom(id(f))
        restype = strip_type(typ.context[ehead])
        d[e] = add_box!(wd, Junction(typ.name, 1,1))
        bx = add_box!(wd, Box(ehead, argtypes, [typ.name]))
        add_wires!(wd, [[(arg,1)=>(bx,i) for (i, arg) in enumerate(args)]...,
                        (bx,1)=>(d[e],1)])
      end
    end
  end
  return d[e]
end

"""
Add context to a wiring diagram. Update the dict of subterms to vertex IDs too.
"""
function add_ctx!(wd::WiringDiagram, refs::Dict{Expr0, Int}, t::Theory,
                  ctx::Context)::Nothing
  # add junctions corresponding to each term in the context
  for (csym, ctype) in collect(ctx)
      refs[csym] = add_box!(wd, Junction(strip_type(ctype), 1, 1))
  end
  # Process terms in context that depend on other terms in the context
  for (csym, ctype) in filter!(x->x[2] isa Expr, collect(ctx))
      tc = only([tc for tc in t.types if tc.name==strip_type(ctype)])
      for ((fun, _), funtgt) in zip(tc.context, ctype.args[2:end])
          srci, tgti = refs[csym], refs[funtgt]
          srct, tgtt = box(wd,srci).value, box(wd, tgti).value
          refs[Expr(:call, fun, csym)] = tgti
          bx = add_box!(wd, Box(fun, [srct],[tgtt]))
          add_wires!(wd, [(srci, 1)=>(bx,1), (bx,1)=>(tgti,1)])
      end
  end
end

"""
Create a box and an intro rule for a theory's term constructor, e.g. "compose"
"""
function make_box(t::Theory, trm::TermConstructor, suffix::Symbol
                  )::Pair{Box{Symbol}, Eq}
  # Initialize wiring diagram
  ctx = trm.context
  ins = strip_type.([ctx[arg] for arg in trm.params]) # input sorts
  out = strip_type(trm.typ) # output sort
  wd = WiringDiagram(ins, Symbol[])
  refs = Dict{Expr0, Int}()
  add_ctx!(wd,refs, t, ctx)

  # Connect inputs
  add_wires!(wd, [(input_id(wd), i)=>(refs[p], 1)
              for (i,p) in enumerate(trm.params)])

  r = deepcopy(wd) # right pattern is left patter plus extra stuff

  # We add the box corresponding to this constructor
  bx = Box(trm.name, ins, [out])
  box_ind = add_box!(r, bx)
  # Connect it to its inputs
  add_wires!(r, [(refs[in_ind], 1)=>(box_ind, i)
                 for (i, in_ind) in enumerate(trm.params)])
  # Add node corresponding to output
  tgt_point = add_box!(r, Junction(out, 1, 0))
  add_wire!(r, (box_ind, 1) => (tgt_point, 1))

  # Assemble rewrite rule
  return bx => Eq(Symbol("$(trm.name)$(suffix)_intro"), wd, r, false)
end


