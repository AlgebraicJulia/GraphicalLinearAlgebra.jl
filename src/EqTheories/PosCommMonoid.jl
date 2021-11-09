using Catlab.WiringDiagrams
using Catlab.Programs

# Positive symmetric monoids
#---------------------------
posl = trim(@program(C_monoid, (x::X,y::X), [mul(x,y), e()]))
posr = trim(@program(C_monoid, (x::X,y::X), [x, e(), y]))
pos = Eq(:pos,  posl, posr, false)

cancell = trim(@program(C_monoid, (x::X,y::X), (e(), [mul(x,y), y])), 1)
cancelr = @program(C_monoid, (x::X,y::X), [x, e()])
cancel = Eq(:cancel, cancell, cancelr, false)

sym = Eq(:sym, @program(C_monoid, (x::X,y::X) -> mul(x,y)),
               @program(C_monoid, (x::X,y::X) -> mul(y,x)))

I_pcs_mon = [mul_assoc, leftid, pos,cancel,sym]
T_pcs_mon = EqTheory(:positive_commutative_monoid, Σ_monoid, I_pcs_mon);

