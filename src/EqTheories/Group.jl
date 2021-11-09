
using Catlab.WiringDiagrams
using Catlab.Programs

# Groups
#-------
inv  = Box(:inv, [:X],   [:X]);
Σ_group    = vcat(Σ_monoid, [inv]);
C_group = get_pres(Σ_group)

e2x = trim(@program(C_monoid, (x::X), let y=e(); (y, y, x) end), 2)
ri = @program(C_group, (x::X), (e(), mul(x, inv(x))))
li = @program(C_group, (x::X), (e(), mul(inv(x), x)))
rightinv = Eq(:rightinv, ri, e2x, false);
leftinv  = Eq(:leftinv,  li, e2x, false);

uniq_inv_1 = trim(@program(C_group,(a::X,b::X,c::X),[mul(a, b),mul(b, c),e()]))
uniq_inv_2 = trim(@program(C_group,(a::X,b::X,c::X),[a,c]))
uniq_inv   = Eq(:uniq_inv,   uniq_inv_1,   uniq_inv_2);

div_1 =  @program C_group (a::X,b::X,c::X) [mul(a,b),c]
div_2 =  @program C_group (a::X,b::X,c::X) [mul(inv(a),c),b]
gdiv     = Eq(:gdiv,     div_1,    div_2);

I_group = [leftinv, rightinv];
T_group  = union(:group, T_monoid, Σ_group,  I_group);

# Other terms in this theory
leftcancel_1 = @program C_monoid (a::X,b::X,c::X) [mul(a, b), mul(a, c)]
leftcancel_2 = @program C_monoid (a::X,b::X,c::X) [b, c]
leftcancel   = Eq(:leftcancel, leftcancel_1, leftcancel_2);


# Dihedrial group D3h
#--------------------
gens = Box(:s_,  Symbol[],  [:X]);
genr = Box(:r_,  Symbol[],  [:X]);
Σ_dihedral = vcat(Σ_group, [gens, genr]);
C_dihedral = get_pres(Σ_dihedral)
e_wd = @program C_monoid () e()

ss = @program C_dihedral () let x=s_(); mul(x,x) end
s_order_2 = Eq(:s_ord_2, ss, e_wd);

rrr = @program C_dihedral () let x=r_(); mul(x,mul(x,x)) end
r_order_3 = Eq(:r_ord_3,  rrr, e_wd);

I_d3h = [s_order_2, r_order_3];
T_d3h  = union(:d3h, T_group,  Σ_dihedral, I_d3h);

# Other terms in this theory
srs = @program C_dihedral () let x=r_(), y=s_(); mul(mul(y, x), inv(y)) end
rinv = @program C_dihedral () inv(r_())
sr2 =  @program C_dihedral () let x=mul(s_(), r_()); mul(x,x) end
