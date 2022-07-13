using Documenter
using GraphicalLinearAlgebra

# Set Literate.jl config if not being compiled on recognized service.
config = Dict{String,String}()
if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
  config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/AlgebraicJulia/GraphicalLinearAlgebra.jl/blob/gh-pages/dev"
  config["repo_root_url"] = "https://github.com/AlgebraicJulia/GraphicalLinearAlgebra.jl/blob/main/docs"
end

makedocs(
    sitename = "GraphicalLinearAlgebra",
    format = Documenter.HTML(),
    modules = [GraphicalLinearAlgebra]
)


@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/AlgebraicJulia/GraphicalLinearAlgebra.jl.git",
  branch = "gh-pages",
  devbranch = "main"
)