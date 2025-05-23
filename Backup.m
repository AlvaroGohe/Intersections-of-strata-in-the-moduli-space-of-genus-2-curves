F<f0, f1, f2, f3, f4, f5, f6, g0, g1, g2, g3> :=PolynomialRing(GF(2),11);
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, f6]),Polynomial([g0, g1, g2, g3]));
GenC;
K<f0, f1, f2, f3, f4, f5, f6, g0, g1, g2, g3> :=BaseField(GenC);
IgusaInvariants(GenC);
F<f0, f1, f2, f3, f4, f5> :=PolynomialRing(GF(2),6);
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, 1]),Polynomial([0, 0, f1*0, 1]));
GenC;
K<f0, f1, f2, f3, f4, f5> :=BaseField(GenC);
IgusaInvariants(GenC);
F<f0, f1, f2, f3, f4, f5> :=PolynomialRing(GF(2),6);
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, 1]),Polynomial([0, f1*0, 1, 1]));
GenC;
K<f0, f1, f2, f3, f4, f5> :=BaseField(GenC);
IgusaInvariants(GenC);

F<f0, f1, f2, f3, f4, f5> := PolynomialRing(GF(3),6);
GenC := HyperellipticCurve(Polynomial([f0, (f2*f4)/f5, f2, f3, f4, f5, 1]));
GenC;
K<f0, f1, f2, f3, f4, f5> :=BaseField(GenC);
IgusaInvariants(GenC);

F<f1, f2, f3, f4, f5, f6> := PolynomialRing(GF(5),6);
GenC := HyperellipticCurve(Polynomial([(2*(3*f2^2*f4^2 + f1*f3*f4^2 + f2^2*f3*f5 + 2*f1*f3^2*f5 + 3*f1*f2*f4*f5 + f2^3*f6))/(3*f4^3 + 4*f3^2*f6 + f2*f4*f6), f1, f2, f3, f4, f5, f6]));
GenC;
K<f1, f2, f3, f4, f5, f6> :=BaseField(GenC);
IgusaInvariants(GenC);



Q0 := Rationals();
K<f0,f1,f2,f3,f4,f5,f6>:= PolynomialRing(Rationals(),7);
GenC := HyperellipticCurve([f0,f1,f2,f3,f4,f5,f6]);
K<f0,f1,f2,f3,f4,f5,f6>:= BaseField(GenC);
II := IgusaInvariants(GenC);
P<f0,f1,f2,f3,f4,f5,f6>:=ProjectiveSpace(Q0,6);
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(Q0,[1,2,3,4,5]);
eqsII := [Numerator(i): i in IgusaInvariants(GenC)];
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..6]] >;
MinimalBasis(J);
M2 := Scheme(IP,-J4^2 + J2*J6 - 4*J8);
JacobianSubrankScheme(M2);



K<f0,f1,f2,g0,g1>:= PolynomialRing(Rationals(),5);
GenC := C3Curve(K,[f0,f1,f2,g0,g1]);
K<f0,f1,f2,g0,g1>:= BaseRing(GenC);
II := IgusaInvariants(GenC);
Q0 := Rationals();
P<g0,g1,f0,f1,f2>:=ProjectiveSpace(Q0,[1,1,2,2,2]);
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(Q0,[1,2,3,4,5]);
IP<J10,J8,J6,J4,J2> := ProjectiveSpace(Q0,[5,4,3,2,1]);
eqsII := [Numerator(i): i in IgusaInvariants(C)];
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..6]] >;
D6 := Scheme(IP,MinimalBasis(J));
Ipproj<J2,J4,J6> := ProjectiveSpace(Q0,[1,2,3]);
proj := map<D6 -> Ipproj|[J2,J4,J6]>;
D6c := Image(proj);

Q0 := GF(5);
P<g0,g1,f0,f1,f2>:=ProjectiveSpace(Q0,[1,1,2,2,2]);
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(Q0,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..6]] >;
D6 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D6)));



Q0 := GF(2);
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(Q0,[1,2,3,4,5]);
S := Scheme(IP,[J4^2 + J2*J6, J4*J6 + J10, J2^3*J6 + J4^3 + J2^2*J8 + J6^2]);
IsSingular(S);

Q3<t> := PolynomialRing(GF(3));
PolQ3<x> := PolynomialRing(Q3);
C := HyperellipticCurve((x^3-x)*(x^3-x-t));
Q3<t> := BaseRing(C);
IgusaInvariants(C);

[Factorisation(pol): pol in II];
  

// Create a polynomial ring over the rationals with six variables ai
F<a1, a2, a3, a4, a5, a6> := PolynomialRing(Rationals(),6);
PolF<x> := PolynomialRing(F);
C := HyperellipticCurve((x-a1)*(x-a2)*(x-a3)*(x-a4)*(x-a5)*(x-a6));
F<a1, a2, a3, a4, a5, a6> := BaseField(C);
II := IgusaInvariants(C);
Write("Igusa_invariants.txt", II);
// Prepare the string with variable names and values
output := "Igusa Invariants:\n";
for i in [1..#II] do
    output cat:= Sprintf("II[%o] = %o\n", i, II[i]);
end for;

// Save the output to a text file
Write("Igusa_Invariants.txt", output);


IP<J2,J4,J6,J8,J10> := ProjectiveSpace(Q0,[1,2,3,4,5]);
M2 := Scheme(IP, )

// The curve with automorphism group C10
K := CyclotomicField(5);
P<x> := PolynomialRing(K);
CC10 := HyperellipticCurve(x^5,1);
G, aut := AutomorphismGroup(CC10);
GroupName(G);
aut(G.5);
M2!IgusaInvariants(CC10);

// The curve with automorphism group GL(2,3)
K<zeta8> := CyclotomicField(8);
P<x> := PolynomialRing(K);
CG<X,Y,Z> := HyperellipticCurve(x^5-x);
G, aut := AutomorphismGroup(CG);
GroupName(G);
// We are going to find an explicit isomorphism between GL(2,3) and the automorphism group of the hyperelliptic curve
// In order to do this, we need to find possibles elements of orders 2 and 3 in the automorphism group that can be the images of the generators of GL(2,3)
[Order(g): g in G];
[aut(g): g in G | Order(g) eq 2];
beta2 := [g: g in G | Order(g) eq 2][2];
[aut(g): g in G | Order(g) eq 3];
beta3 := [g: g in G | Order(g) eq 3][1];
GL23 := GL(2, GF(3));
phi := hom< GL23 -> G | [beta2, beta3]>; // This is the explicit isomorphism
GroupName(Image(phi)); // We can check that the image of the map is the whole group
aut(phi(Matrix([[1,1],[0,1]])));
aut(phi(Matrix([[1,0],[1,1]])));
aut(phi(Matrix([[-1,0],[0,1]])));
M2!IgusaInvariants(CG);
DifferentialSpace(Divisor(X));
<aut(beta2)(X),aut(beta2)(Y)>;



// The curve with automorphism group C3:D4
K := CyclotomicField(6);
P<x> := PolynomialRing(K);
// CG<X,Y,Z> := HyperellipticCurve(x^6,2);
CG<X,Y,Z> := HyperellipticCurve(x^6+1);
G, aut := AutomorphismGroup(CG);
GroupName(G);
iota := G.(-5);
tau2 := G.2;
tau6 := G.(-10);
gens := [aut(G.(-5)),aut(G.2),aut(G.(-10))];
[iota^2, tau2^2, tau6^6, (iota,tau2), (tau2,tau6), tau6^iota/tau6^5/tau2];
M2!IgusaInvariants(CG);

// The curve with automorphism group C2 wr C5
K<zeta5> := ext<GF(2)| Polynomial([1,1,1,1,1])>; 
P<x> := PolynomialRing(K);
CG := HyperellipticCurve(x^5,1);
// G, aut  := AutomorphismGroupOfHyperellipticCurve(CG: explicit := true, geometric := true);
G := GeometricAutomorphismGroupFromIgusaInvariants(IgusaInvariants(CG));
GroupName(G);
aut(G.5);
M2!IgusaInvariants(CG);


// The curve with automorphism group SL(2,5)
K := GF(5);
P<x> := PolynomialRing(K);
CG<X,Y,Z> := HyperellipticCurve(x^5-x);
G, aut := AutomorphismGroup(CG);
GroupName(G);
// We are going to find an explicit isomorphism between SL(2,5) and the automorphism group of the hyperelliptic curve as before
// We need to find possibles elements of orders 3 and 4 in the automorphism group that can be the images of the generators of SL(2,5)
[Order(g): g in G];
[aut(g): g in G | Order(g) eq 3];
beta3 := [g: g in G | Order(g) eq 3][18];
[aut(g): g in G | Order(g) eq 4];
beta4 := [g: g in G | Order(g) eq 4][22];
SL25 := SL(2, GF(5));
phi := hom< SL25 -> G | [beta4, beta3]>; // This is the explicit isomorphism
GroupName(Image(phi)); // We can check that the image of the map is the whole group
aut(phi(Matrix([[1,1],[0,1]])));
aut(phi(Matrix([[1,0],[1,1]])));

BasisOfHolomorphicDifferentials(CG);
SheafOfDifferentials(CG);   
for beta3 in [g: g in G | Order(g) eq 3] do
    for beta4 in [g: g in G | Order(g) eq 4] do
        SL25 := SL(2, GF(5));
        phi := hom< SL25 -> G | [beta4, beta3]>; // This is the explicit isomorphism
        if GroupName(Image(phi)) eq "SL(2,5)" then
        <beta3,beta4,DefiningEquations(aut(phi(Matrix([[1,1],[0,1]]))))>; // We can check that the image of the map is the whole group
        end if;
            end for;
end for;
[g: g in G | Order(g) eq 4][23];

M2!IgusaInvariants(CG);




// Study of the stratum associated to the curve C2xC2

K := Rationals();
p := 23;
//K := GF(p);
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
// GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -2*f1 + 2*f2 + f3, -f1 + f2 + 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1]));
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, 0, 0, f3, 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1]));
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
// singV4 := ReducedSubscheme(JacobianSubrankScheme(V4));
// IrreducibleComponents(singV));
// [Dimension(C): C in IrreducibleComponents(singV4))];
// [ArithmeticGenus(C): C in IrreducibleComponents(singV4))];
// [IsSingular(C): C in IrreducibleComponents(singV4))];
P112<h1, h2, h3> := ProjectiveSpace(K,[1,1,2]);
rat := map<P112->V4 | [h1, h1*h2 + 2*h3, -((2*h1 + h2)*(74*h1^2 + 79*h1*h2 + 20*h2^2 + 4*h3)), -37*h1^4 - 58*h1^3*h2 - 30*h1^2*h2^2 - 5*h1*h2^3 - 2*h1^2*h3 - 2*h1*h2*h3 - h3^2,  (2*h1 + h2)*(11*h1^2 + 12*h1*h2 + 3*h2^2 + h3)^2]>;
IrreducibleComponents(BaseScheme(rat));
Pullback(rat, singV4);
invrat := map<V4->P112 | [J2*(240*J10*J2^3 - 12800*J10*J2*J4 + J2^4*J4^2 - 64*J2^2*J4^3 + 1024*J4^4 - 288000*J10*J6 + 3*J2^5*J6 - 172*J2^3*J4*J6 + 2304*J2*J4^2*J6 + 756*J2^2*J6^2 - 17280*J4*J6^2), 
 -2*(222*J10*J2^4 - 11760*J10*J2^2*J4 - 12800*J10*J4^2 + J2^5*J4^2 - 64*J2^3*J4^3 + 1024*J2*J4^4 - 292800*J10*J2*J6 + 3*J2^6*J6 - 174*J2^4*J4*J6 + 2418*J2^2*J4^2*J6 - 
   1344*J4^3*J6 + 750*J2^3*J6^2 - 17496*J2*J4*J6^2 + 3240*J6^3), 
 ((240*J10*J2^3 - 12800*J10*J2*J4 + J2^4*J4^2 - 64*J2^2*J4^3 + 1024*J4^4 - 288000*J10*J6 + 3*J2^5*J6 - 172*J2^3*J4*J6 + 2304*J2*J4^2*J6 + 756*J2^2*J6^2 - 17280*J4*J6^2)*
   (444*J10*J2^5 - 23280*J10*J2^3*J4 - 38400*J10*J2*J4^2 + 2*J2^6*J4^2 - 127*J2^4*J4^3 + 1984*J2^2*J4^4 + 1024*J4^5 - 585600*J10*J2^2*J6 + 6*J2^7*J6 - 288000*J10*J4*J6 - 
    345*J2^5*J4*J6 + 4664*J2^3*J4^2*J6 - 384*J2*J4^3*J6 + 1500*J2^4*J6^2 - 34236*J2^2*J4*J6^2 - 17280*J4^2*J6^2 + 6480*J2*J6^3))/2]>;
IrreducibleComponents(BaseScheme(invrat));
Expand(rat*invrat);


K := Rationals();
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -2*f1 + 2*f2 + f3, -f1 + f2 + 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1]));
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)[[1,2,3,4,5]]];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
Factorisation(Numerator(Discriminant(GenV4)));
[Factorisation(eqs): eqs in eqsII];
E1<x,y,z> := EllipticCurve([g1, -f1 + f2, f3*g0, f1*f3, f0*f3^2]);
E1;
P2<x,y,z> := ProjectiveSpace(FF,2);
phi1 := map<GenV4->E1 | [f3*x*(x+z)*z,f3*y,z^3]>;
Degree(phi1);
jInvariant(E1);
Factorisation(Denominator(jInvariant(E1)));
lambda := (64*f0 - 20*f1 + 4*f2 - f3 + 16*g0^2 - 8*g0*g1 + g1^2);
E2<x,y,z> := EllipticCurve([-4*g0 + g1, 48*f0 - 9*f1 + f2 + 8*g0^2 - 2*g0*g1,-g0*lambda, (12*f0 - f1 + g0^2)*lambda, f0*lambda^2]);
phi2 := map<GenV4->E2 | [-lambda*x*(x + z)*(2*x + z),lambda*(g1*x^3 + y + 2*g1*x^2*z + g0*x*z^2 + g1*x*z^2 + g0*z^3),(2*x+z)^3]>;
Degree(phi2);
jInvariant(E2);
numdif := Factorisation(Evaluate(Numerator(jInvariant(E1)-jInvariant(E2))),);
Factorisation(Numerator(Discriminant(GenV4)));
Factorisation(Denominator(jInvariant(E1)));
Factorisation(Denominator(jInvariant(E2)));
num1 := Scheme(P,numdif[1,1]);
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,num1,d)) : d in  [1..6]] >;
MinimalBasis(J);
Z := Scheme(IP,MinimalBasis(J));
num2 := Scheme(P,numdif[2,1]);
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,num2,d)) : d in  [1..6]] >;
MinimalBasis(J);
D4 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(Intersection(Z,D4)));




K := GF(2);
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f2, f1, f0]),Polynomial([g0, g1, g1, g0])); // This takes a long time to evaluate, so to simplify the calculations, we usually work with the model of the curve of the following line, which outputs the same result.
//GenV4<x,y,z> := HyperellipticCurve(Polynomial([0, f1, 0, f3, 0, f1, 0]),Polynomial([g0, 0, 0, g0])); 
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -2*f1 + 2*f2 + f3, -f1 + f2 + 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1]));
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)));
P2<x0, x1, x2> := ProjectiveSpace(K,2);
rat := map<P2->V4 | [x0, x0*x1, x0*x1^2, x0^3*x2, x1*(x0*x1^3 + x1^4 + x0^3*x2)]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<V4->P2 | [J2^4, J2^2*J4, J8]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));



// Construction of the strata of almost ordinary curves in characteristic 2
K := GF(2);
P := ProjectiveSpace(K,[2,2,2,2,2,2,2,1,1,1,1]);
F<f0, f1, f2, f3, f4, f5, f3, g3> := CoordinateRing(P);
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, f3]),Polynomial([0, 0, g3, 0]));
FF<f0, f1, f2, f3, f4, f5, f3, g3> := BaseRing(GenC);
eqsII := [Numerator(i): i in IgusaInvariants(GenC)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
AO2 := Scheme(IP,MinimalBasis(J));
Int1V4 := Scheme(AO2, [J4^2 + J2*J6, J4^4 + J4*J6^2 + J2^2*J4*J8 + J2^3*J10, J4^3*J6 + J6^3 + J2*J4^2*J8 + J2^2*J4*J10]);
IsIrreducible(AO2);
IsReduced(AO2);
#IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(AO2)));
#IrreducibleComponents(ReducedSubscheme(Int1V4));




// Construction of the strata of supersingular curves in characteristic 2
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, f6]),Polynomial([g3, 0, 0, 0]));
FF<f0, f1, f2, f3, f4, f5, f6, g3> := BaseRing(GenC);
eqsII := [Numerator(i): i in IgusaInvariants(GenC)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
SS2 := Scheme(IP,MinimalBasis(J));
IsIrreducible(SS2);
IsReduced(SS2);
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(SS2)));




// Study of the stratum associated to the curve D4

K := Rationals();
// K := GF(5);
P := ProjectiveSpace(K,2);
F<f1, f3, f5> := CoordinateRing(P);
GenD4<x,y,z> := HyperellipticCurve(Polynomial([0, f1, 0, f3, 0, f5])); 
FF<f1, f3, f5>:= BaseRing(GenD4);
eqsII := [Numerator(i): i in IgusaInvariants(GenD4)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in [1..15]] >;
MinimalBasis(J);
D4 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D4)));
[<Dimension(C), Degree(C)>: C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D4)))];
sptD4 := D4![120, 330, -320, -36825, 11664];
IsSingular(sptD4);
sC := HyperellipticCurveFromIgusaInvariants([120, 330, -320, -36825, 11664]);
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->D4 | [x0, (5*x0^2 - 17*x0*x1 + 15*x1^2)/8, -1/16*((3*x0 - 5*x1)*(x0 - 2*x1)^2), (-37*x0^4 + 238*x0^3*x1 - 567*x0^2*x1^2 + 590*x0*x1^3 - 225*x1^4)/256, ((2*x0 - 3*x1)^3*(x0 - 2*x1)^2)/1024]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<D4->P1 | [J2*(11*J2^2 - 480*J4), 5*J2^3 - 224*J2*J4 - 720*J6]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
Expand(rat*invrat);
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);
[(-(x0 - 5/2*x1)/8)^i*Evaluate(eqsII[i],[(2*x0 - 3*x1)/(-8*x0 + 20*x1),1,1]): i in [1..5]];


// Study of the stratum associated to the curve D6
// In characteristic not three

K<w> := ext<Rationals() | Polynomial([1,1,1])>;
// K<w> := GF(5,2);
P := ProjectiveSpace(K,[2,2,2,1,1]);
F<f0, f1, f2, g0, g1> := CoordinateRing(P);
GenD6<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -10*f0 - 5*f1 - 2*f2, 15*f0 + 5*f1 + f2, -6*f0 - f1, f0]),Polynomial([g0, g1, -3*g0 - g1, g0])); 
GenD6alt<x,y,z> := HyperellipticCurve(Polynomial([f0, 0, 0, f1, 0, 0, f2]),Polynomial([g0, 0, 0, g1])); 
FF<f0, f1, f2, g0, g1>:= BaseRing(GenD6);
eqsII := [Numerator(i): i in IgusaInvariants(GenD6)];
FF<f0, f1, f2, g0, g1>:= BaseRing(GenD6alt);
eqsIIalt := [Numerator(i): i in IgusaInvariants(GenD6alt)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..10]] >;
MinimalBasis(J);
D6 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D6)));
[<Dimension(C), Degree(C)>: C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D6)))];
sptD6 := D4![20, 30, -20, -325, 64];
IsSingular(sptD6);
sC := HyperellipticCurveFromIgusaInvariants([20, 30, -20, -325, 64]);
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->D6 | [x0, -3*x1*(x0 + 10*x1), -(x1^2*(3*x0 + 40*x1)), -(x1^2*(3*x0^2 + 55*x0*x1 + 225*x1^2)), -(x1^3*(x0 + 12*x1)^2)]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<D6->P1 | [J2*(3*J2^2 - 40*J4), -(J2*J4) - 30*J6]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
Expand(rat*invrat);
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);
[(-(x0 + 120*x1)/27)^i*Evaluate(eqsIIalt[i],[(-x0 - 93*x1)/(3*x0 + 360*x1),0,-1,1,1]): i in [1..5]];
[(x0 + 120*x1)^i*Evaluate(eqsII[i],[(4*x0 + 453*x1)/(81*(x0 + 120*x1)), (2*w*(x0 + 3*w*x0 + 93*x1 + 360*w*x1))/(27*(x0 + 120*x1)), (5*w*(3*x0 + w*x0 + 360*x1 + 93*w*x1))/(27*(x0 + 120*x1)), 0, 1]): i in [1..5]];


// In characteristic three
K<w> := GF(3);
P := ProjectiveSpace(K,[2,2,2,1,1]);
F<f0, f1, f2, g0, g1> := CoordinateRing(P);
GenD6<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -10*f0 - 5*f1 - 2*f2, 15*f0 + 5*f1 + f2, -6*f0 - f1, f0]),Polynomial([g0, g1, -3*g0 - g1, g0])); 
FF<f0, f1, f2, g0, g1>:= BaseRing(GenD6);
eqsII := [Numerator(i): i in IgusaInvariants(GenD6)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..10]] >;
MinimalBasis(J);
D6 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D6)));
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->D6 | [x0, -3*x1*(x0 + 10*x1), -(x1^2*(3*x0 + 40*x1)), -(x1^2*(3*x0^2 + 55*x0*x1 + 225*x1^2)), -(x1^3*(x0 + 12*x1)^2)]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<D6->P1 | [J2^3, J6]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
Expand(rat*invrat);
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);
[(x0)^(-i)*Evaluate(eqsII[i],[x1,0,x0-1,0,1]): i in [1..5]];



// Study of the stratum associated to the curve C2^5

K<zeta5> := ext<GF(2)| Polynomial([1,1,1,1,1])>; 
P := ProjectiveSpace(K,[2,2,1]);
F<f3, f5, g0> := CoordinateRing(P);
GenC25<x,y,z> := HyperellipticCurve(Polynomial([0,0,0,f3,0,f5]),g0); 
FF<f3, f5, g0>:= BaseRing(GenC25);
eqsII := [Numerator(i): i in IgusaInvariants(GenC25)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..10]] >;
MinimalBasis(J);
C25 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(C25)));
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->C25 | [0, 0, 0, x0^4, x1^5]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<C25->P1 | [J8^5, J10^4]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);



//
p := 17;
K<a>:= GF(p,2);
Z := Integers();
P := ProjectiveSpace(K,3); // y^2 = x (x - 1) (f3 x^3 + f2 x^2 + f1 x + f0)
F<f0, f1, f2, f3> := CoordinateRing(P);
f<x> := Polynomial([0, -f0, f0 - f1, f1 - f2, f2 - f3, f3]);
GenC := HyperellipticCurve(f);
FF<f0, f1, f2, f3> := BaseRing(GenC);
eqsII := [Numerator(i): i in IgusaInvariants(GenC)[[1,2,3,5]]];
IP<J2,J4,J6,J10> := ProjectiveSpace(K,[1,2,3,5]);
n := ((p-1)/2);
pow := f^(Z!n);
HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
prank1 := ReducedSubscheme(Scheme(P, Determinant(HWmat)));
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,prank1,d)) : d in  [1..10]] >;
MinimalBasis(J);
AOp := Scheme(IP,MinimalBasis(J));
IsIrreducible(AOp);
IsReduced(AOp);
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(AOp)));

for p in PrimesInInterval(3,50) do 
SplittingField(SupersingularPolynomial(p));
Degree(SupersingularPolynomial(p));
end for;

// Make sure that we have defined the HW Matrix correctly as in Achter and Howe
K<a> := ext<GF(5) | Polynomial([3,3,0,1])>;
f<x> := Polynomial([0, a^(56), a^(18), a^(92), 1, 1]);
p := 5;
n := ((p-1)/2);
Z := Integers();
pow := f^(Z!n);
HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
HWmatfr := Matrix([[Coefficient(pow, p-1)^p, Coefficient(pow, 2*p-1)^p],[Coefficient(pow, p-2)^p,Coefficient(pow, 2*p-2)^p]]);
rankmat := HWmat*HWmatfr;

//
for p in PrimesInInterval(3,13) do 
  K<a>:= GF(p,2);
  Z := Integers();
  P := ProjectiveSpace(K,3); // y^2 = x (x - 1) (f3 x^3 + f2 x^2 + f1 x + f0)
  F<f0, f1, f2, f3> := CoordinateRing(P);
  f<x> := Polynomial([0, -f0, f0 - f1, f1 - f2, f2 - f3, f3]);
  GenC := HyperellipticCurve(f);
  FF<f0, f1, f2, f3> := BaseRing(GenC);
  eqsII := [Numerator(i): i in IgusaInvariants(GenC)[[1,2,3,5]]];
  IP<J2,J4,J6,J10> := ProjectiveSpace(K,[1,2,3,5]);
  n := ((p-1)/2);
  pow := f^(Z!n);
  HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
  prank1 := ReducedSubscheme(Scheme(P, Determinant(HWmat)));
  phi := map<P->IP | eqsII>;
  J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,prank1,d)) : d in  [1..(p-1)/2]] >;
  AOp := Scheme(IP,MinimalBasis(J));
  Int1V4 := Scheme(AOp, J2^4*J4^4*J6 - 64*J2^2*J4^5*J6 + 1024*J4^6*J6 - 2*J2^5*J4^2*J6^2 + 136*J2^3*J4^3*J6^2 - 2304*J2*J4^4*J6^2 + J2^6*J6^3 - 72*J2^4*J4*J6^3 +         1080*J2^2*J4^2*J6^3 + 6912*J4^3*J6^3 + 216*J2^3*J6^4 - 7776*J2*J4*J6^4 + 11664*J6^5 + 8*J2^4*J4^3*J10 - 512*J2^2*J4^4*J10 + 8192*J4^5*J10 -         72*J2^5*J4*J6*J10 + 4816*J2^3*J4^2*J6*J10 - 84480*J2*J4^3*J6*J10 - 48*J2^4*J6^2*J10 - 12960*J2^2*J4*J6^2*J10 + 691200*J4^2*J6^2*J10 -         129600*J2*J6^3*J10 - 432*J2^5*J10^2 + 28800*J2^3*J4*J10^2 - 512000*J2*J4^2*J10^2 - 96000*J2^2*J6*J10^2 + 11520000*J4*J6*J10^2 + 51200000*J10^3);
  printf "\n\n Prime: %o\n", p;
  printf "Irreducible p-rank 1 strata?: %o\n", IsIrreducible(AOp);
  printf "Reduced p-rank 1 strata?: %o\n", IsReduced(AOp);
  printf "Number of singular points: %o\n", #IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(AOp)));
  AOp;
  // IrreducibleComponents(ReducedSubscheme(Int1V4));
  printf "Number of components of the intersection with C2xC2 strata: %o\n\n", #IrreducibleComponents(ReducedSubscheme(Int1V4));
  Degree(SupersingularPolynomial(p));
end for;



p := 5;
K<a>:= GF(p,2);
Z := Integers();
P := ProjectiveSpace(K,3); // y^2 = x (x - 1) (f3 x^3 + f2 x^2 + f1 x + f0)
F<f0, f1, f2, f3> := CoordinateRing(P);
f<x> := Polynomial([0, -f0, f0 - f1, f1 - f2, f2 - f3, f3]);
GenC := HyperellipticCurve(f);
FF<f0, f1, f2, f3> := BaseRing(GenC);
eqsII := [Numerator(i): i in IgusaInvariants(GenC)[[1,2,3,5]]];
IP<J2,J4,J6,J10> := ProjectiveSpace(K,[1,2,3,5]);
n := ((p-1)/2);
pow := f^(Z!n);
HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
prank1 := ReducedSubscheme(Scheme(P, Determinant(HWmat)));
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,prank1,d)) : d in  [1..10]] >;
MinimalBasis(J);
AOp := Scheme(IP,MinimalBasis(J));
IsIrreducible(AOp);
IsReduced(AOp);
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(AOp)));
Int1V4 := Scheme(AOp, J2^4*J4^4*J6 - 64*J2^2*J4^5*J6 + 1024*J4^6*J6 - 2*J2^5*J4^2*J6^2 + 136*J2^3*J4^3*J6^2 - 2304*J2*J4^4*J6^2 + J2^6*J6^3 - 72*J2^4*J4*J6^3 +         1080*J2^2*J4^2*J6^3 + 6912*J4^3*J6^3 + 216*J2^3*J6^4 - 7776*J2*J4*J6^4 + 11664*J6^5 + 8*J2^4*J4^3*J10 - 512*J2^2*J4^4*J10 + 8192*J4^5*J10 -         72*J2^5*J4*J6*J10 + 4816*J2^3*J4^2*J6*J10 - 84480*J2*J4^3*J6*J10 - 48*J2^4*J6^2*J10 - 12960*J2^2*J4*J6^2*J10 + 691200*J4^2*J6^2*J10 -         129600*J2*J6^3*J10 - 432*J2^5*J10^2 + 28800*J2^3*J4*J10^2 - 512000*J2*J4^2*J10^2 - 96000*J2^2*J6*J10^2 + 11520000*J4*J6*J10^2 + 51200000*J10^3);
#IrreducibleComponents(ReducedSubscheme(Int1V4));





p := 5;
K<a>:= GF(p,2);
Z := Integers();
P := ProjectiveSpace(K,3); // y^2 = x (x - 1) (f3 x^3 + f2 x^2 + f1 x + f0)
F<f0, f1, f2, f3> := CoordinateRing(P);
f<x> := Polynomial([0, -f0, f0 - f1, f1 - f2, f2 - f3, f3]);
GenC := HyperellipticCurve(f);
FF<f0, f1, f2, f3> := BaseRing(GenC);
eqsII := [Numerator(i): i in IgusaInvariants(GenC)[[1,2,3,5]]];
IP<J2,J4,J6,J10> := ProjectiveSpace(K,[1,2,3,5]);
n := ((p-1)/2);
pow := f^(Z!n);
HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
HWmatfr := Matrix([[Coefficient(pow, p-1)^p, Coefficient(pow, 2*p-1)^p],[Coefficient(pow, p-2)^p,Coefficient(pow, 2*p-2)^p]]);
rankmat := HWmat*HWmatfr;
P4<a,b,c,d> := ProjectiveSpace(K,4);
dummat := Matrix([[a,b],[c,d]])*Matrix([[a^p,b^p],[c^p,d^p]]);
MinimalBasis(ReducedSubscheme(Scheme(P4,[dummat[1,1],dummat[2,2],dummat[1,2],dummat[2,1],Determinant(dummat)])));
prank0 := Scheme(P, [rankmat[1,1],rankmat[2,1], rankmat[1,2], rankmat[2,2]]);
prank0IC := IrreducibleComponents(ReducedSubscheme(prank0));
anumber2 := Scheme(P, [HWmat[1,1], HWmat[1,2], HWmat[2,1], HWmat[2,2]]);
anumber2IC := IrreducibleComponents(ReducedSubscheme(anumber2));
phi := map<P->IP | eqsII>;
J := [ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi, ic,d)) : d in  [1..15]]>: ic in prank0IC];
SSp := [Scheme(IP,MinimalBasis(j)):j in J];
SSp;
IsIrreducible(SSp);
IrreducibleComponents(SSp);
IsReduced(SSp);
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(SSp)));




p := 5;
K<a>:= GF(p,3);
a^3+3*a+3;
Z := Integers();
f<x> := Polynomial([0, a^56, a^18, a^92, 1, 1]);
GenC := HyperellipticCurve(f);
n := ((p-1)/2);
pow := f^(Z!n);
CMmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
CMmatfr := Matrix([[Coefficient(pow, p-1)^p, Coefficient(pow, 2*p-1)^p],[Coefficient(pow, p-2)^p,Coefficient(pow, 2*p-2)^p]]);

K := Rationals();
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
// GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f2, f1, f0]),Polynomial([g0, g1, g1, g0])); // This takes a long time to evaluate, so to simplify the calculations, we usually work with the model of the curve of the following line, which outputs the same result.
GenV4<x,y,z> := HyperellipticCurve(Polynomial([0, f1, 0, f3, 0, f1, 0]),Polynomial([g0, 0, 0, g0])); 
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)[[1,2,3,5]]];
IP<J2,J4,J6,J10> := ProjectiveSpace(K,[1,2,3,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
DefiningEquations(V4);

K := Rationals();
// K := GF(3);
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -2*f1 + 2*f2 + f3, -f1 + f2 + 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1]));
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)[[1,2,3,4,5]]];
Factorisation(Numerator(Discriminant(GenV4)));
[Factorisation(eqs): eqs in eqsII];
E1<x,y,z> := EllipticCurve([g1, -f1 + f2, f3*g0, f1*f3, f0*f3^2]);
E1;
P2<x,y,z> := ProjectiveSpace(FF,2);
phi1 := map<GenV4->E1 | [f3*x*(x+z)*z,f3*y,z^3]>;
Degree(phi1);
jInvariant(E1);
lambda := (64*f0 - 20*f1 + 4*f2 - f3 + 16*g0^2 - 8*g0*g1 + g1^2);
E2<x,y,z> := EllipticCurve([-4*g0 + g1, 48*f0 - 9*f1 + f2 + 8*g0^2 - 2*g0*g1,-g0*lambda, (12*f0 - f1 + g0^2)*lambda, f0*lambda^2]);
phi2 := map<GenV4->E2 | [-lambda*x*(x + z)*(2*x + z),lambda*(g1*x^3 + y + 2*g1*x^2*z + g0*x*z^2 + g1*x*z^2 + g0*z^3),(2*x+z)^3]>;
Degree(phi2);
jInvariant(E2);
Factorisation(Numerator(Evaluate(jInvariant(E1)+jInvariant(E2),[f0,f3,0,f3,0,g1])));
[Factorisation(Numerator(Evaluate(i,[f0,f3,0,f3,0,g1]))): i  in eqsII];
[Numerator(Evaluate(i,[f0,f3,0,f3,0,g1])): i  in eqsII];
Factorisation(Numerator(jInvariant(E1)-jInvariant(E2)));


K := Rationals();
// K := GF(3);
P := ProjectiveSpace(K,3);
F<l,m,c1,c2> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([-1,0,1])*Polynomial([-l,0,1])*Polynomial([-m,0,1]));
FF<l,m,c1,c2> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)[[1,2,3,4,5]]];
Factorisation(Numerator(Discriminant(GenV4)));
[Factorisation(eqs): eqs in eqsII];
E1<x,y,z> := EllipticCurve(Polynomial([-1,1])*Polynomial([-l,1])*Polynomial([-m,1]));
phi1 := map<GenV4->E1 | [x^2*z,y,z^3]>;
E1;
P2<x,y,z> := ProjectiveSpace(FF,2);
jInvariant(E1);
Factorisation(Numerator(jInvariant(E1)));
Factorisation(Denominator(jInvariant(E1)));
E2<x,y,z> := EllipticCurve(Polynomial([-1,1])*Polynomial([-1/l,1])*Polynomial([-1/m,1]));
jInvariant(E2);
Evaluate(jInvariant(E1),[c1*(c2-1)/(c1-1)/c2,c1/c2,0,0]);
Evaluate(jInvariant(E2),[c1*(c2-1)/(c1-1)/c2,c1/c2,0,0]);
Factorisation(Numerator(jInvariant(E2)));
Factorisation(Denominator(jInvariant(E2)));
Factorisation(Numerator(Evaluate(Discriminant(GenV4),[c1*(c2-1)/(c1-1)/c2,c1/c2,0,0])));

