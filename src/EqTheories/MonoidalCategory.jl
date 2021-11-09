using Catlab.WiringDiagrams
using Catlab.Programs

# (Strict) Monoidal categories
#--------------------
o_o = Box(:o_o, [:O,:O], [:O]); # ⊗ₒ
o_a = Box(:o_a, [:A,:A], [:A]); # ⊗ₐ
ounit = Box(:⊤, Symbol[], [:O])
Σ_mc = vcat(Σ_cat, [o_o, o_a, ounit])
C_mc = get_pres(Σ_mc)

ma1 = @program C_mc (x::O,y::O,z::O) -> o_o(x, o_o(y, z))
ma2 = @program C_mc (x::O,y::O,z::O) -> o_o(o_o(x, y), z)
o_o_assoc = Eq(:o_o_assoc, ma1, ma2);

ma1 = @program C_mc (x::A,y::A,z::A) -> o_a(x, o_a(y, z))
ma2 = @program C_mc (x::A,y::A,z::A) -> o_a(o_a(x, y), z)
o_a_assoc = Eq(:o_a_assoc, ma1, ma2);

o_func_sl = @program C_mc (a::A, b::A) s(o_a(a,b))
o_func_sr = @program C_mc (a::A, b::A) o_o(t(a),t(b))
o_func_s = Eq(:o_func_s,o_func_sl, o_func_sr)

o_func_tl = @program C_mc (a::A, b::A) t(o_a(a,b))
o_func_tr = @program C_mc (a::A, b::A) o_o(t(a),t(b))
o_func_t = Eq(:o_func_t,o_func_tl,o_func_tr)

o_f_c_1 =  @program C_mc (a::A,b::A,c::A,d::A) cmp(o_a(a,b),o_a(c,d))
o_f_c_2 =  @program C_mc (a::A,b::A,c::A,d::A) o_a(cmp(a,c),cmp(b,d))
o_func_cmp = Eq(:o_func_cmp, o_f_c_1, o_f_c_2);

lunit_o_a_ = @program C_mc (a::A) o_a(Id(⊤()), a)
lunit_o_a  = Eq(:lunit_o_a,  lunit_o_a_,   passa);

runit_o_a_ = @program C_mc (a::A) o_a(a, Id(⊤()))
runit_o_a  = Eq(:runit_o_a,  runit_o_a_,   passa);

lunit_o_o_ = @program C_mc (a::O) o_o(⊤(), a)
lunit_o_o  = Eq(:lunit_o_o,  lunit_o_o_,   passo);

runit_o_o_ = @program C_mc (a::O) o_o(a, ⊤())
runit_o_o  = Eq(:runit_o_o,  runit_o_o_,   passo);

I_mc = [o_o_assoc, o_a_assoc, o_func_s, o_func_t, o_func_cmp,
        lunit_o_a, runit_o_a, lunit_o_o, runit_o_o]
T_mc  = union(:monoidal_cat, T_cat,   Σ_mc,  I_mc);