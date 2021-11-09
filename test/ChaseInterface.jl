
using Catlab.WiringDiagrams
using Catlab.Programs
using Catlab.Present
using Catlab.Theories
using Test

using CategoricalLinearAlgebra: csp_homomorphic, chase_theory, T_monoid, x_squared, idxxid


# We can't immediately prove that (e*x)*(x*e) = x*x
@test !csp_homomorphic(T_monoid, x_squared, idxxid)
# But if we propagate all monoid rules for one step...
res = chase_theory(T_monoid, idxxid, 1)
# ...then we can prove it
@test csp_homomorphic(T_monoid, x_squared, res)

