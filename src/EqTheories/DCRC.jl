using Catlab.WiringDiagrams
using Catlab.Programs

# Discrete cartesian restriction categories
#------------------------------------------
mu = Box(:μ, [:O], [:A])
Σ_dcr = vcat(Σ_crc, [mu])
C_dcr = get_pres(Σ_dcr)

delmu_t = @program C_dcr (a::O) cmp(δ(a), μ(a))
idbox = @program C_dcr (a::O) Id(a)
bone = Eq(:bone, delmu_t, idbox)

proj1 = Eq(:mu_s, @program(C_dcr,(a::O),s(μ(a))), passo)
proj2 = Eq(:mu_t, @program(C_dcr,(a::O),t(μ(a))), passo)

frobr = @program C_dcr (a::O) cmp(μ(a),δ(a))
frobll = @program C_dcr (a::O) let x=Id(a); cmp(o_a(x,δ(a)),o_a(μ(a),x)) end
frob1   = Eq(:frob_l, frobll, frobr)

frobrl = @program C_dcr (a::O) let x=Id(a); cmp(o_a(δ(a),x),o_a(x,μ(a))) end
frob2   = Eq(:frob_r, frobrl, frobr)

I_dcr = [bone, proj1, proj2, frob1, frob2]
T_dcr = union(:dcr, T_crc,   Σ_dcr, I_dcr);
