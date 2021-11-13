using Test
using GraphicalLinearAlgebra: T_monoid, idxxid, saturate

@test length(saturate(T_monoid, idxxid)) == 34