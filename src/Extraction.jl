using JuMP
import GLPK

boxcosts = Dict([:⁺=> 2,:₊=>2, :ᵒ=> 0, :ₒ=>0, :A=>3,:B=>3, :X=>0, :□=>1])

"""We can use a more sophisticated model that estimates sparsity, etc."""
function get_cost(wd::WiringDiagram)::Int
    sum([boxcosts[b.value] for b in boxes(wd)])
end

"""Use linear programming to find optimal subwiring diagram"""
function optimal_subdiagram(wd::WiringDiagram)::WiringDiagram
    m = Model()
    set_optimizer(m, GLPK.Optimizer)
    vs = findall(x->x isa Junction, boxes(wd)) # hypergraph vertices
    bs = findall(x->x isa Box, boxes(wd))      # hypergraph relations

    @variable(m, nodevar[1:length(vs)], Bin)
    @variable(m, boxvar[1:length(bs)], Bin)
    @objective(m, Min, sum(boxvar[i]*boxcosts[box(wd,b).value]
                           for (i,b) in enumerate(bs)))
    # Constraint: we must provide a value for each output wire
    for op in 1:length(output_ports(wd))
        b_id = only([w.source.box
                     for w in in_wires(wd, output_id(wd))
                     if w.target.port==op])
        v_id = only(findall(==(b_id), vs))
        @constraint(m, nodevar[v_id]==true)
    end
    # For each vertex used, at least one box/overall input must produce it
    for (v_id,v) in enumerate(vs)
        if isempty(filter(w -> w.target.box == v,
                          out_wires(wd, input_id(wd))))
            parents = findall(x -> x in inneighbors(wd, v), bs)
            @constraint(m, nodevar[v_id] <= sum(boxvar[parents]))
        end
    end
    # For each box used, all of its inputs must be turned on
    for (b_id, b) in enumerate(bs)
        parents = inneighbors(wd, b)
        for parent_id in findall(x -> x in parents, vs)
            @constraint(m, boxvar[b_id] <= nodevar[parent_id])
        end
    end

    optimize!(m)

    # Use optimal model results to prune the wiring diagram
    keep = vcat([ids[findall(v -> v > 0.99, value.(xs))]
                 for (xs,ids) in [nodevar => vs, boxvar => bs]]...)
    wd2 = deepcopy(wd)
    rem_boxes!(wd2, filter(x->!(x in keep), 1:nboxes(wd2)))
    return wd2
end

