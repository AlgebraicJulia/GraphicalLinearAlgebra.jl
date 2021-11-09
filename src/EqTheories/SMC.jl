using Catlab.WiringDiagrams
using Catlab.Programs

# Symmetric (Strict) Monoidal categories
#---------------------------------------
σ = Box(:σ,  [:O, :O], [:A])
Σ_smc = vcat(Σ_mc, [σ])
C_smc = get_pres(Σ_smc)

bb_1 = @program C_smc (a::O,b::O) cmp(σ(a,b),σ(b,a))
bb_2 = @program C_smc (a::O,b::O) Id(o_o(a,b))
braidbraid = Eq(:braidbraid, bb_1,     bb_2);

braid_tl = @program C_smc (a::O,b::O) t(σ(a,b))
braid_tr = @program C_smc (a::O,b::O) o_o(b,a)
braid_t = Eq(:braid_t, braid_tl, braid_tr)

braid_sl = @program C_smc (a::O,b::O) s(σ(a,b))
braid_sr = @program C_smc (a::O,b::O) o_o(a,b)
braid_s = Eq(:braid_s, braid_sl, braid_sr)

braid_ots_t = @program C_smc (a::A,b::A) cmp(o_a(a,b), σ(t(a),t(b)))
braid_ots_s = @program C_smc (a::A,b::A) cmp(σ(s(a),s(b)),o_a(b,a))
braid_ots = Eq(:braid_ots, braid_ots_t, braid_ots_s);

I_smc  = [braidbraid, braid_t, braid_s, braid_ots]
T_smc = union(:smc, T_mc,  Σ_smc, I_smc);