using Catlab.WiringDiagrams
using Catlab.Programs


# Categories
#------------
cmp = Box(:cmp, [:A,:A], [:A]);
Σ_cat = vcat(Σ_reflG, [cmp]);
C_cat = get_pres(Σ_cat)

ma1 = @program C_cat (x::A,y::A,z::A) -> cmp(x, cmp(y, z))
ma2 = @program C_cat (x::A,y::A,z::A) -> cmp(cmp(x, y), z)
cmp_assoc = Eq(:cmp_assoc, ma1, ma2);

cmp_1 = trim(@program(C_cat,(ff::A,gg::A),(s(ff),[t(ff),s(gg)],t(gg))))
cmp_2 = trim(@program(C_cat,(ff::A,gg::A),begin
  cm = cmp(ff,gg)
  ([s(cm),s(ff)],[t(gg),t(cm)]) end ))
cmp_intro = Eq(:cmp, cmp_1, cmp_2, false);

passa = @program C_reflG (x::A) -> x
id_s = @program C_cat (a::A) cmp(Id(s(a)),a)
l_unit = Eq(:l_unit, id_s, passa);

id_t = @program C_cat (a::A) cmp(a,Id(t(a)))
r_unit = Eq(:r_unit, id_t, passa);

I_cat = [cmp_assoc, l_unit, r_unit, cmp_intro]
T_cat = union(:cat, T_reflG, Σ_cat, I_cat);