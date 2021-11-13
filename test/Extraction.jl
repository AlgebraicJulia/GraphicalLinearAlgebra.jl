using Test
using LinearAlgebra
using GraphicalLinearAlgebra: C_gla, chase_theory, T_gla, optimal_subdiagram
using Catlab.Programs
using Catlab.CategoricalAlgebra


Aabb = @program C_gla (x::X) ⁺(⁺(A(x), B(x)),⁺(A(x), B(x)))

Aabb_ = chase_theory(T_gla, Aabb, 1, [:B_sv, :A_sv]); # A and B are single valued

optimal = chase_theory(T_gla, Aabb_, 1, [:⁺_sv]); # + is single-valued

lessoptimal = chase_theory(T_gla, Aabb_, 1, [:add_sym, :add_asc, :add_unit,:⁺_sv]);

# Call the optimizer on our big term
@test is_isomorphic(optimal_subdiagram(lessoptimal), optimal)