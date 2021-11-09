using Catlab.WiringDiagrams
using Catlab.Programs


# Reflexive graphs
#------------------
s = Box(:s,   [:A],  [:O]);
t = Box(:t,   [:A],  [:O]);
Id = Box(:Id,  [:O],  [:A]);
Σ_reflG = [s, t, Id];
C_reflG = get_pres(Σ_reflG)
O, A = (generator(C_reflG, name) for name in [:O,:A])

passo = @program C_reflG (x::O) -> x

refl_s = @program C_reflG (a::O) s(Id(a))
refls = Eq(:refls, refl_s, passo);

refl_t = @program C_reflG (a::O) t(Id(a))
reflt = Eq(:reflt, refl_t, passo);

I_reflG = [refls, reflt]
T_reflG = EqTheory(:reflexive_graph, Σ_reflG, I_reflG);
