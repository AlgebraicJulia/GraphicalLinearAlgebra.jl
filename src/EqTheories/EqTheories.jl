

"""
Many definitions taken from "Functorial Semantics for Partial Theories" by
Sobocinski et al. (2020)
"""

include("Monoid.jl")
include("Group.jl")
include("ReflGraph.jl")
include("Category.jl")
include("MonoidalCategory.jl")
include("SMC.jl")
include("CRC.jl")
include("DCRC.jl")
include("CartesianCategory.jl")
include("PosCommMonoid.jl")
include("GLA.jl")

# TODO
# T_mca  = union(:monoidal_category_additive, T_cat, Σ_mca, I_smca)
# T_hgc = union(:hypergraph_category, T_smc, Σ_hgc, I_hgc)
# T_abr = union(:abelian_bicategory_relations, T_hca, Σ_abr, I_abr)
# T_lr = union(:linear_relations, T_abr, Σ_lr, I_lr)
# T_flr = union(:free_linear_relations, T_lr, Σ_flr, I_flr)
