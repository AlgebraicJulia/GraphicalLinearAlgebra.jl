
using Catlab.WiringDiagrams
using Catlab.Programs

# Monoids
#---------
mmul = Box(:mul, [:X,:X],   [:X]);
e    = Box(:e,   Symbol[],  [:X]);
Σ_monoid   = [mmul, e];
C_monoid = get_pres(Σ_monoid)
X = generator(C_monoid, :X)

e11 = @program C_monoid (x::X) (e(),x)
ll = @program(C_monoid, (x::X), let y=e(); (y, mul(y, x)) end)
leftid = Eq(:leftid, ll, e11, false, [:e=>[1=>1]]);

rr = @program(C_monoid, (x::X), let y=e(); (y, mul(x, y)) end)
rightid = Eq(:rightid, rr, e11, false, [:e=>[1=>1]]);

ma1 = @program C_monoid (x::X,y::X,z::X) -> mul(x, mul(y, z))
ma2 = @program C_monoid (x::X,y::X,z::X) -> mul(mul(x, y), z)
mul_assoc = Eq(:mul_assoc, ma1, ma2);

I_monoid = [mul_assoc, leftid, rightid];
T_monoid = EqTheory(:monoid, Σ_monoid, I_monoid);

# Other terms in this theory
idxxid = @program C_monoid (x::X) let y=e(); mul(mul(y,x), mul(x, y)) end
x_squared = @program C_monoid (x::X) mul(x,x)

