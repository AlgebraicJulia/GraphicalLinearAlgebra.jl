using Catlab.WiringDiagrams
using Catlab.Programs

# Cartesian categories
#--------------------
epsnat1 = @program C_dcr (a::A) cmp(a,ϵ(t(a)))
epsnat2 = @program C_dcr (a::A) ϵ(s(a))
eps_nat = Eq(:epsnat, epsnat1, epsnat2)

I_cc = [eps_nat]
T_cc  = union(:cc, T_dcr, Box{Symbol}[], I_cc)

# Cartesian closed categories
#----------------------------
ev = Box(:ev,   [:O, :O], [:A])
Exp = Box(:exp, [:O, :O], [:O])
lam = Box(:lam, [:O, :O, :O, :A], [:A])
Σ_ccc = vcat(Σ_dcr, [ev, Exp, lam])
C_ccc = get_pres(Σ_ccc)

ev_s = @program C_ccc (a::O,b::O) s(ev(a,b))
evs2 = @program C_ccc (a::O,b::O) o_o(exp(a,b),a)
evs = Eq(:evs, ev_s, evs2)

ev_t = @program C_ccc (a::O,b::O) t(ev(a,b))
evt2 = @program C_ccc (_::O,b::O) (b,)
evt = Eq(:evt, ev_t, evt2)

lam_intro1 = trim(@program C_ccc (x::O,y::O,z::O,q::A) ([o_o(x,y),s(q)],[z,t(q)]))
lam_intro2 = trim(@program C_ccc (x::O,y::O,z::O,q::A) lam(x,y,z,q))
λ_intro = Eq(:λ_intro, lam_intro1, lam_intro2, false)

lam_s_ =  @program C_ccc (a::O,b::O,c::O,d::A) s(lam(a,b,c,d))
lam_s2 = @program C_ccc (x::O,_::O,_::O,_::A) (x,)
lam_s = Eq(:lam_s, lam_s_, lam_s2)

lam_t_ =  @program C_ccc (a::O,b::O,c::O,d::A) t(lam(a,b,c,d))
lam_t2 = @program C_ccc (_::O,x::O,y::O,_::A) exp(x,y)
lam_t = Eq(:lam_t, lam_t_, lam_t2)

lam_eqf1 = @program C_ccc (a::O,b::O,c::O,d::A) cmp(o_a(lam(a,b,c,d),Id(b)),ev(b,c))
lam_eqf2 = trim(@program(C_ccc, (a::O,b::O,c::O,d::A), (d, [o_o(a,b),s(d)],[c,t(d)])), 1)
lam_eqf = Eq(:lam_eqf, lam_eqf1, lam_eqf2)

lam_eqg1 = trim(@program(C_ccc, (a::O,b::O,c::O,d::A), (d, [a,s(d)], [exp(b,c),t(d)])), 1)
lam_eqg2 =  @program C_ccc (a::O,b::O,c::O,d::A) lam(a,b,c,cmp(o_a(d, Id(b)), ev(b,c)))
lam_eqg = Eq(:lam_eqg, lam_eqg1, lam_eqg2)

I_ccc = [evs, evt, λ_intro, lam_s, lam_t, lam_eqf, lam_eqg]
T_ccc = union(:ccc, T_cc,  Σ_ccc, I_ccc)