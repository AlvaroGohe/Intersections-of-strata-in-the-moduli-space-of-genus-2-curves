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
tau2 := [g: g in G | Order(g) eq 2][2];
[aut(g): g in G | Order(g) eq 3];
tau3 := [g: g in G | Order(g) eq 3][1];
GL23 := GL(2, GF(3));
phi := hom< GL23 -> G | [tau2, tau3]>; // This is the explicit isomorphism
GroupName(Image(phi)); // We can check that the image of the map is the whole group
aut(phi(Matrix([[1,1],[0,1]])));
aut(phi(Matrix([[1,0],[1,1]])));
aut(phi(Matrix([[-1,0],[0,1]])));
M2!IgusaInvariants(CG);



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
tau3 := [g: g in G | Order(g) eq 3][18];
[aut(g): g in G | Order(g) eq 4];
tau4 := [g: g in G | Order(g) eq 4][22];
SL25 := SL(2, GF(5));
phi := hom< SL25 -> G | [tau4, tau3]>; // This is the explicit isomorphism
GroupName(Image(phi)); // We can check that the image of the map is the whole group
aut(phi(Matrix([[1,1],[0,1]])));
aut(phi(Matrix([[1,0],[1,1]])));

for tau3 in [g: g in G | Order(g) eq 3] do
    for tau4 in [g: g in G | Order(g) eq 4] do
        SL25 := SL(2, GF(5));
        phi := hom< SL25 -> G | [tau4, tau3]>; // This is the explicit isomorphism
        if GroupName(Image(phi)) eq "SL(2,5)" then
        <tau3,tau4,DefiningEquations(aut(phi(Matrix([[1,1],[0,1]]))))>; // We can check that the image of the map is the whole group
        end if;
            end for;
end for;
[g: g in G | Order(g) eq 4][23];

M2!IgusaInvariants(CG);




// Study of the stratum associated to the curve C2xC2

K := Rationals();
K := GF(5);
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
// GenC2<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f2, f1, f0]),Polynomial([g0, g1, g1, g0])); // This takes a long time to evaluate, so to simplify the calculations, we usually work with the model of the curve of the following line, which outputs the same result.
GenC2<x,y,z> := HyperellipticCurve(Polynomial([0, f1, 0, f3, 0, f1, 0]),Polynomial([g0, 0, 0, g0])); 
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenC2);
eqsII := [Numerator(i): i in IgusaInvariants(GenC2)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)));
[Dimension(C): C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)))];
[ArithmeticGenus(C): C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)))];
[IsSingular(C): C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)))];
singV4 := ReducedSubscheme(JacobianSubrankScheme(V4));
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


K := GF(2);
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
GenC2<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f2, f1, f0]),Polynomial([g0, g1, g1, g0])); // This takes a long time to evaluate, so to simplify the calculations, we usually work with the model of the curve of the following line, which outputs the same result.
//GenC2<x,y,z> := HyperellipticCurve(Polynomial([0, f1, 0, f3, 0, f1, 0]),Polynomial([g0, 0, 0, g0])); 
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenC2);
eqsII := [Numerator(i): i in IgusaInvariants(GenC2)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)));
P112<h1, h2, h3> := ProjectiveSpace(K,[1,1,2]);
rat := map<P112->V4 | [h1, h1*h2 + 2*h3, -((2*h1 + h2)*(74*h1^2 + 79*h1*h2 + 20*h2^2 + 4*h3)), -37*h1^4 - 58*h1^3*h2 - 30*h1^2*h2^2 - 5*h1*h2^3 - 2*h1^2*h3 - 2*h1*h2*h3 - h3^2,  (2*h1 + h2)*(11*h1^2 + 12*h1*h2 + 3*h2^2 + h3)^2]>;
IrreducibleComponents(BaseScheme(rat));





