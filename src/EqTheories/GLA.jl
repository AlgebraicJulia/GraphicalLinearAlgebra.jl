using Catlab.WiringDiagrams
using Catlab.Programs

add = Box(Symbol("⁺"),   [:X, :X], [:X]);
addop = Box(Symbol("₊"),   [:X], [:X,:X]);
antipode, A, B = [Box(Symbol(x), [:X], [:X]) for x in ["□", "A", "B"]];
zero = Box(Symbol("ᵒ"), Symbol[], [:X]);
zeroop = Box(Symbol("ₒ"), [:X], Symbol[]);

Σ_gla = [add, addop, antipode, zero, zeroop, A, B]
C_gla = get_pres(Σ_gla)

opsyms2 = ["⁺"=> "₊", "ᵒ" => "ₒ"]
opnames2 = ["cup"=>"cap", "left"=>"right",
            [x => (x*"op") for x in ["add", "zero"]]...];

# Adding / addingᵒᵖ
add_1_l = @program C_gla (a::X,b::X) ⁺(a,b)
add_1_r = @program C_gla (a::X,b::X) ⁺(b,a)
add_1 = Eq(:add_sym, add_1_l, add_1_r)
add_2_l = @program C_gla (a::X,b::X, c::X) ⁺(a,⁺(b,c))
add_2_r = @program C_gla (a::X,b::X, c::X) ⁺(⁺(a,b),c)
add_2 = Eq(:add_asc, add_2_l, add_2_r)
add_3_l = @program C_gla (a::X) let e=ᵒ(); (⁺(a, e),e) end
add_3_r = @program C_gla (a::X) (a,ᵒ())
add_3 = Eq(:add_unit, add_3_l, add_3_r, true, [:ᵒ=>[1=>1]])

addop_1, addop_2, addop_3 = substitute_syms(
    opsyms2, opnames2, [add_1, add_2, add_3]; invert=true)

# Antipode (neg copy/neg delete handled automatically)
a_1_l = @program C_gla (a::X) let e=ᵒ();(e,e) end
a_1_r = @program C_gla (a::X) (⁺(□(a),a),ᵒ())
a_1 = Eq(:neg_left, a_1_l, a_1_r, [:ᵒ=>[1=>1]])
a_3_l = @program C_gla (a::X, b::X) □(⁺(a,b))
a_3_r = @program C_gla (a::X, b::X) ⁺(□(a),□(b))
a_3 = Eq(:neg_add, a_3_l, a_3_r)
a_5_l = @program C_gla () □(ᵒ())
a_5_r = @program C_gla () ᵒ()
a_5 = Eq(:neg_zero, a_5_l, a_5_r, true, [:ᵒ=>[1=>1]])

ao_1, ao_3, ao_5 = substitute_syms(
  opsyms2, opnames2, [a_1, a_3, a_5]; invert=true)

# Adding meets adding op
aao_1_l = @program C_gla (a::X, b::X) let (b1,b2)= ₊(b); (⁺(a,b1), b2) end
aao_1_r = @program C_gla (a::X, b::X) let (a1,a2)= ₊(a); (a1,⁺(a2,b)) end
aao_1 = Eq(:add_addop, aao_1_l, aao_1_r)

aao_2_l = @program C_gla (a::X) let (a1,a2)= ₊(a); ⁺(a1, a2) end
aao_2_r = @program C_gla (a::X) (a,)
aao_2 = Eq(:add_addop, aao_2_l, aao_2_r)

aao_3_l = trim(@program(C_gla, (x::X), let e1=ᵒ(), e2=ₒ(x); (e1) end), 0,0)
aao_3_r = @program C_gla ()  ₒ(ᵒ())
aao_3 = Eq(:zero_zeroop, aao_3_l, aao_3_r, [:ᵒ=>[1=>1], :ₒ=>[1=>1]])

# Cups and caps (can be inferred ... is this true?)

I_Gla = Eq[add_1, add_2, add_3,
         addop_1,
         addop_2,
         addop_3,
         a_1, a_3, a_5,
         ao_1, ao_3, ao_5,
         aao_1, aao_2, aao_3
]

T_gla = EqTheory(:Gla, Σ_gla, I_Gla);

