using Test


@testset "ChaseInterface.jl" begin
  include("ChaseInterface.jl")
end

@testset "Extraction" begin
  include("Extraction.jl")
end

@testset "Programs" begin
  include("linear_algebra/LinearAlgebra.jl")
end
