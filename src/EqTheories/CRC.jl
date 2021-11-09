using Catlab.WiringDiagrams
using Catlab.Programs

# Cartesian restriction categories
#---------------------------------
del = Box(:δ, [:O], [:A])
eps = Box(:ϵ, [:O], [:A])
Σ_crc = vcat(Σ_smc, [del, eps])
C_crc = get_pres(Σ_crc)

eps_s_l = @program C_crc (a::O) s(ϵ(a))
eps_s = Eq(:eps_s, eps_s_l, passo)

del_s_l = @program C_crc (a::O) s(δ(a))
del_s = Eq(:del_s, del_s_l, passo)

e_t = @program C_crc (a::O) t(ϵ(a))
eps_t_2 = @program C_crc (_::O) ⊤()
eps_t = Eq(:eps_o,   e_t, eps_t_2);

d_t = @program C_crc (a::O) t(δ(a))
del_t_2 = @program C_crc (a::O) o_o(a,a)
del_t   = Eq(:del_t, d_t, del_t_2);

eps_coh_1 = @program C_crc (a::O,b::O) ϵ(o_o(a,b))
eps_coh_2 = @program C_crc (a::O,b::O) o_a(ϵ(a),ϵ(b))
eps_coh = Eq(:eps_coh, eps_coh_1, eps_coh_2);

del_coh_1 = @program C_crc (a::O,b::O) δ(o_o(a,b))
del_coh_2 = @program C_crc (a::O,b::O) [
  o_a(δ(a),δ(b)),o_a(o_a(Id(a),σ(a,b)),Id(b))]
del_coh = Eq(:del_coh, del_coh_1, del_coh_2);

del_nat_1 = @program C_crc (a::O) cmp(δ(a),σ(a,a))
del_nat_2 =@program C_crc (a::O) δ(a)
del_nat = Eq(:del_nat, del_nat_1, del_nat_2);

cc1_tt = @program C_crc (a::O) let x=δ(a); cmp(x,o_a(x,Id(a))) end
cc1_ft = @program C_crc (a::O) let x=δ(a); cmp(x,o_a(Id(a),x)) end
cc1 = Eq(:cc1, cc1_tt, cc1_ft);

cc1_tf = @program C_crc (a::O) cmp(δ(a),o_a(ϵ(a),Id(a)))
cc1_ff = @program C_crc (a::O) cmp(δ(a),o_a(Id(a),ϵ(a)))
cc2 = Eq(:cc2, cc1_tf, cc1_ff);

cc3_1 = @program C_crc (a::A) cmp(δ(s(a)), o_a(a,a))
cc3_2 = @program C_crc (a::A) cmp(a, δ(t(a)))
cc3 = Eq(:cc3, cc3_1, cc3_2);

I_crc = [eps_s, del_s, eps_t, del_t, eps_coh, del_coh, del_nat, cc1, cc2, cc3]
T_crc = union(:crc, T_smc,   Σ_crc, I_crc);
