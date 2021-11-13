"""Destructive rewriting"""

using DataStructures: DefaultDict
using Catlab.CategoricalAlgebra

"""Convert an Eq (L=>R) into a span L<-I->R for DPO rewriting"""
function eq_to_rewrite(t::EqTheory, e::Eq
                       )::Pair{ACSetTransformation,ACSetTransformation}
  # mapping defines the interface
  (L, li, lo), (R, ri, ro) = wd_to_acset(t, e.l), wd_to_acset(t, e.r)
  G = Base.invokelatest(typeof(L))
  ml, mr = [DefaultDict{Symbol, Vector{Int}}(()->Int[]) for _ in 1:2]
  for ((it, i), (_, o)) in zip(vcat(li,lo), vcat(ri, ro))
    add_part!(G, it)
    push!(ml[it], i)
    push!(mr[it], o)
  end
  for (k, lrs) in e.mapping
    for (vl, vr) in lrs
      add_part!(G, k)
      push!(ml[k], vl)
      push!(mr[k], vr)
    end
  end
  l = ACSetTransformation(G, L; ml...)
  r = ACSetTransformation(G, R; mr...)
  return l => r
end

struct Traj
  state::WiringDiagram
  hist::Vector{Pair{Eq, TightACSetTransformation}}
end

function Traj(wd::WiringDiagram)
  return Traj(wd, Pair{Eq, TightACSetTransformation}[])
end

function next_traj(t::Traj, s::WiringDiagram, e::Eq, m::TightACSetTransformation
                   )::Traj
  return Traj(s, vcat(t.hist, [e=>m]))
end

function next_trajs(t::Traj,
                    ns::Vector{Tuple{W, Eq, T}}
                    )::Vector{Traj} where {W<:WiringDiagram,
                                           T<:ACSetTransformation}
  return [next_traj(t, s, e, m) for (s, e, m) in ns]
end

"""Apply rewrite destructively via DPO to underlying ACSet representation"""
function apply_rewrite(t::EqTheory, e::Eq, I::W
    ) where {W<:WiringDiagram}
  G, i, o = wd_to_acset(t, I)
  L, R = eq_to_rewrite(t, e)
  res = []
  for mtch in filter(m->can_pushout_complement(L, m), homomorphisms(codom(L), G))

    # We also need to forbid deletion of i/o vertices! Get deleted vertices:
    orphans = map(components(L), components(mtch)) do l_comp, m_comp
        image = Set(collect(l_comp))  # duplicated code from dangling_condition
        Set([ m_comp(x) for x in codom(l_comp) if x ∉ image ])
      end
    no_deleted_io = !any([v ∈ orphans[k] for (k, v) in vcat(i, o)])
    if no_deleted_io

      _, kg, _, kh = rewrite_match_maps(L, R, mtch)  # perform the rewrite
      H = codom(kh)

      # Invert K->G and compose with K->H to get map from G->H
      i2, o2 = [[k=> kh[k](findfirst(==(v), collect(kg[k]))) for (k,v) in io]
                for io in [i, o]]

      push!(res, acset_to_wd(t, H, i2, o2) => mtch)
    end
  end
  return res
end

# Plumbing for calls to apply_rewrite

function rewrite_step(t::EqTheory, It::Traj)::Vector{Traj}
  next_trajs(It, vcat([let wms = apply_rewrite(t, e, It.state);
    Tuple{WiringDiagram, Eq, ACSetTransformation}[(w,e,m) for (w,m) in wms] end
    for e in eq_w_rev(t)]...))
end

"""Does *not* use CSetAutomorphisms to quotient curr_pool by equivalence"""
function saturate(t::EqTheory, I::Traj; n::Int=1)::Vector{Traj}
  curr_pool = Traj[I]
  for _ in 1:n
    curr_pool = vcat([rewrite_step(t, trj) for trj in curr_pool]...)
  end
  return curr_pool
end

# WD versions of the above, ignoring trajectory history
function rewrite_step(t::EqTheory, I::WiringDiagram)::Vector{WiringDiagram}
  [trj.state for trj in rewrite_step(t, Traj(I))]
end

function saturate(t::EqTheory, I::WiringDiagram; n::Int=1
                  )::Vector{WiringDiagram}
  [trj.state for trj in saturate(t, Traj(I); n=n)]
end

