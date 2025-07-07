// This is code accompanying the paper "Intersections of the automorphism and the Ekedahl-Oort strata inside of M_2".

// If you find any bug or mistake, or if you have any question, please don't hesitate in contacting me :)
// email: alvaro.gohe@gmail.com


// INTRODUCTION
// The description of the Igusa invariants for a general genus two curve in the form y^2=f(x).
Q0 := Rationals();
K<f0,f1,f2,f3,f4,f5,f6>:= PolynomialRing(Rationals(),7);
GenC := HyperellipticCurve([f0,f1,f2,f3,f4,f5,f6]);
K<f0,f1,f2,f3,f4,f5,f6>:= BaseField(GenC);
II := IgusaInvariants(GenC);
P<f0,f1,f2,f3,f4,f5,f6>:=ProjectiveSpace(Q0,6);
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(Q0,[1,2,3,4,5]); // This is the weighted projective space with weights [1,2,3,4,5].
eqsII := [Numerator(i): i in IgusaInvariants(GenC)];
[Factorisation(pol): pol in eqsII];
phi := map<P->IP | eqsII>; // We construct the map from the space of 7 variables fi to P(1,2,3,4,5) given by the Igusa invariants.
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..6]] >;
MinimalBasis(J); // We can check there is a relation between the elements, namely -J4^2 + J2*J6 - 4*J8=0.
M2 := Scheme(IP,-J4^2 + J2*J6 - 4*J8);
JacobianSubrankScheme(M2);


// This is the comparison with the invariants of a curve written as y^2 equal the polymomial with six roots ai.
// Create a polynomial ring over the rationals with six variables ai.
F<a1, a2, a3, a4, a5, a6> := PolynomialRing(Rationals(),6);
PolF<x> := PolynomialRing(F);
C := HyperellipticCurve((x-a1)*(x-a2)*(x-a3)*(x-a4)*(x-a5)*(x-a6));
F<a1, a2, a3, a4, a5, a6> := BaseField(C);
II := IgusaInvariants(C);
Write("Igusa_invariants.txt", II); // As we are interested in saving these on a text file, we prepare a string with variable names and values.
output := "Igusa Invariants:\n";
for i in [1..#II] do
    output cat:= Sprintf("II[%o] = %o\n", i, II[i]);
end for;
Write("Igusa_Invariants.txt", output); // Save the output to a text file.
 

// PART I: THE AUTOMORPHISM STRATA
// Let us start by describing the curves with big automorphism group:

// The curve with automorphism group C10.
K := CyclotomicField(5);
P<x> := PolynomialRing(K);
CC10 := HyperellipticCurve(x^5,1);
G, aut := AutomorphismGroup(CC10);
GroupName(G);
aut(G.5);
M2!IgusaInvariants(CC10);

// The curve with automorphism group GL(2,3).
K<zeta8> := CyclotomicField(8);
P<x> := PolynomialRing(K);
CG<X,Y,Z> := HyperellipticCurve(x^5-x);
G, aut := AutomorphismGroup(CG);
GroupName(G);
// We are going to find an explicit isomorphism between GL(2,3) and the automorphism group of the hyperelliptic curve.
// In order to do this, we need to find possibles elements of orders 2 and 3 in the automorphism group that can be the images of the generators of GL(2,3).
[Order(g): g in G];
[aut(g): g in G | Order(g) eq 2];
beta2 := [g: g in G | Order(g) eq 2][2];
[aut(g): g in G | Order(g) eq 3];
beta3 := [g: g in G | Order(g) eq 3][1];
GL23 := GL(2, GF(3));
phi := hom< GL23 -> G | [beta2, beta3]>; // This is the explicit isomorphism.
GroupName(Image(phi)); // We can check that the image of the map is the whole group.
aut(phi(Matrix([[1,1],[0,1]])));
aut(phi(Matrix([[1,0],[1,1]])));
aut(phi(Matrix([[-1,0],[0,1]])));
M2!IgusaInvariants(CG);
DifferentialSpace(Divisor(X));
<aut(beta2)(X),aut(beta2)(Y)>;

// The curve with automorphism group C3:D4.
K := CyclotomicField(6);
P<x> := PolynomialRing(K);
// CG<X,Y,Z> := HyperellipticCurve(x^6,2);
CG<X,Y,Z> := HyperellipticCurve(x^6+1);
G, aut := AutomorphismGroup(CG);
GroupName(G);
iota := G.(-5); // We have manually identified the generators of the group.
tau2 := G.2;
tau6 := G.(-10);
gens := [aut(G.(-5)),aut(G.2),aut(G.(-10))];
[iota^2, tau2^2, tau6^6, (iota,tau2), (tau2,tau6), tau6^iota/tau6^5/tau2]; // This is a check that the generators we have selected match the presentation of the group that can be found in LMFDB.
M2!IgusaInvariants(CG);

// The curve with automorphism group C2 wr C5.
K<zeta5> := ext<GF(2)| Polynomial([1,1,1,1,1])>; 
P<x> := PolynomialRing(K);
CG := HyperellipticCurve(x^5,1);
// G, aut  := AutomorphismGroupOfHyperellipticCurve(CG: explicit := true, geometric := true);
G := GeometricAutomorphismGroupFromIgusaInvariants(IgusaInvariants(CG));
GroupName(G);
aut(G.5);
M2!IgusaInvariants(CG);

// The curve with automorphism group SL(2,5).
K := GF(5);
P<x> := PolynomialRing(K);
CG<X,Y,Z> := HyperellipticCurve(x^5-x);
G, aut := AutomorphismGroup(CG);
GroupName(G);
// We are going to find an explicit isomorphism between SL(2,5) and the automorphism group of the hyperelliptic curve as before.
// We need to find possibles elements of orders 3 and 4 in the automorphism group that can be the images of the generators of SL(2,5).
[Order(g): g in G];
[aut(g): g in G | Order(g) eq 3];
beta3 := [g: g in G | Order(g) eq 3][18]; // Here, we have also manually identified generators for the group. You can see below how.
[aut(g): g in G | Order(g) eq 4];
beta4 := [g: g in G | Order(g) eq 4][22];
SL25 := SL(2, GF(5));
phi := hom< SL25 -> G | [beta4, beta3]>; // This is the explicit isomorphism.
GroupName(Image(phi)); // We can check that the image of the map is the whole group.
aut(phi(Matrix([[1,1],[0,1]])));
aut(phi(Matrix([[1,0],[1,1]])));
BasisOfHolomorphicDifferentials(CG);
SheafOfDifferentials(CG);   

// In order to find manually what the generators are, we looped over all elements of order 3 and 4 and see when the elements generated SL(2,5).
for beta3 in [g: g in G | Order(g) eq 3] do
    for beta4 in [g: g in G | Order(g) eq 4] do
        SL25 := SL(2, GF(5));
        phi := hom< SL25 -> G | [beta4, beta3]>; 
        if GroupName(Image(phi)) eq "SL(2,5)" then
        <beta3,beta4,DefiningEquations(aut(phi(Matrix([[1,1],[0,1]]))))>; // We can check that the image of the map is the whole group.
        end if;
            end for;
end for;

// We know proceed to study the automorphism strata corresponding to the groups C2xC2, D4, D6 and C2^5.

// The strategy is going to be similar in the first three cases. We first identify an automorphism that allows us to find a model of the curve depending on parameters fi, gj.
// We create a copy of a weighted projective space with variables fi, gj; where the fi have weight 2 and the gj have weight 1.
// Then, we define a map from this space to the weighted projective space with weights 1,2,3,4,5 whose equations are given by the Igusa invariants of our model of the curve.
// The strata that we are looking for is precisely the image under this map.


// Study of the stratum associated to the group C2xC2.
// Over a field of characteristic not two.
K := Rationals();
// p := 23;
// K := GF(p); // Some computations take quite a long time to perform if we are working over the rationals, which is why it is useful to test the code over finite fields (not characteristic two, we will deal with that later).
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
// GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -2*f1 + 2*f2 + f3, -f1 + f2 + 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1])); This would be the model, but it takes a long time to evaluate, so to simplify the calculations, we usually work with the model of the curve of the following line, which outputs the same result.
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, 0, 0, f3, 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1]));
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
// singV4 := ReducedSubscheme(JacobianSubrankScheme(V4)); // Over the rationals, computing the singular locus takes a long time.
// IrreducibleComponents(singV));
// [Dimension(C): C in IrreducibleComponents(singV4))];
// [ArithmeticGenus(C): C in IrreducibleComponents(singV4))];
// [IsSingular(C): C in IrreducibleComponents(singV4))];

// This is a birational map between our strata and the wps with weights 1, 1 and 2.
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
// IrreducibleComponents(BaseScheme(invrat));
Expand(rat*invrat);

// Study of the stratum associated to the group C2xC2.
// Over a field of characteristic two.
K := GF(2);
P := ProjectiveSpace(K,[2,2,2,2,1,1]);
F<f0, f1, f2, f3, g0, g1> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -2*f1 + 2*f2 + f3, -f1 + f2 + 3*f3, 3*f3, f3]),Polynomial([g0, g1, g1])); // In characteristic two we can work with the full model.
FF<f0, f1, f2, f3, g0, g1> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..15]] >;
MinimalBasis(J);
V4 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(V4)));
P2<x0, x1, x2> := ProjectiveSpace(K,2); // In characteristic two we can find a birational map to P^2.
rat := map<P2->V4 | [x0, x0*x1, x0*x1^2, x0^3*x2, x1*(x0*x1^3 + x1^4 + x0^3*x2)]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<V4->P2 | [J2^4, J2^2*J4, J8]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));


// Here we analyse how to construct from genus two curves C with an automorphism group C2xC2, the two elliptic curves that are isogenous to the Jacobian of C.
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
E1<x,y,z> := EllipticCurve([g1, -f1 + f2, f3*g0, f1*f3, f0*f3^2]); // This is the first elliptic curve.
E1;
P2<x,y,z> := ProjectiveSpace(FF,2);
phi1 := map<GenV4->E1 | [f3*x*(x+z)*z,f3*y,z^3]>; // As we mentioned in the paper, this is the quotient map
Degree(phi1);
jInvariant(E1);
Factorisation(Denominator(jInvariant(E1))); // We can compute the j-invariant.
lambda := (64*f0 - 20*f1 + 4*f2 - f3 + 16*g0^2 - 8*g0*g1 + g1^2); 
E2<x,y,z> := EllipticCurve([-4*g0 + g1, 48*f0 - 9*f1 + f2 + 8*g0^2 - 2*g0*g1,-g0*lambda, (12*f0 - f1 + g0^2)*lambda, f0*lambda^2]); // This is the second elliptic curve.
phi2 := map<GenV4->E2 | [-lambda*x*(x + z)*(2*x + z),lambda*(g1*x^3 + y + 2*g1*x^2*z + g0*x*z^2 + g1*x*z^2 + g0*z^3),(2*x+z)^3]>; // And this is the quotient map.
Degree(phi2);
jInvariant(E2);
numdif := Factorisation(Numerator(jInvariant(E1)-jInvariant(E2))); // The difference between the j-invariants of the two curves factorises into two factors. Whenever either of these factors are zero, our curves are isomorphic.
Factorisation(Numerator(Discriminant(GenV4)));
Factorisation(Denominator(jInvariant(E1)));
Factorisation(Denominator(jInvariant(E2)));
num1 := Scheme(P,numdif[1,1]); // This is the variety defined by the first factor, as a scheme inside of the wps with variables fi, gj.
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,num1,d)) : d in  [1..6]] >; // The image of that variety with respect to the map given by the Igusa invariants tell us what this locus looks like inside of M2.
MinimalBasis(J);
Z := Scheme(IP,MinimalBasis(J)); // In the case of the first factor, this defines a rational curve.
num2 := Scheme(P,numdif[2,1]); // We do the same with the second factor.
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,num2,d)) : d in  [1..6]] >;
MinimalBasis(J);
D4 := Scheme(IP,MinimalBasis(J)); // We will see later that this second factor matches with the description of the strata D4.
IrreducibleComponents(ReducedSubscheme(Intersection(Z,D4)));

// This part of the code concerns the proof of Theorem 3.1, where we prove that given any two elliptic curves with a level 2 structure, we can construct a genus two curve by gluing the curves along their 2-torsion points.
// First, we start with a curve of the form y^2=(x^2-1)(x^2-l)(x^2-m), and construct the quotient maps to E1: y^2=(x-1)(x-l)(x-m) and E2: y^2=(x-1)(x-1/l)(x-1/m).
// Turns out, if you pick l=-c1/c2 and m=-c1*(c2-1)/(c2*(c1-1)), then we can check by computing the j-invariants that E1 is isomorphic to y^2=x(x-1)(x-l1) and E2 is isomorphic to y^2=x(x-1)(x-l2).

K := Rationals();
P := ProjectiveSpace(K,3);
F<l,m,c1,c2> := CoordinateRing(P);
GenV4<x,y,z> := HyperellipticCurve(Polynomial([-1,0,1])*Polynomial([-l,0,1])*Polynomial([-m,0,1]));
FF<l,m,c1,c2> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)[[1,2,3,4,5]]];
GeqsII := [i: i in G2Invariants(GenV4)];
Factorisation(Numerator(Discriminant(GenV4)));
Factorisation(Denominator(Discriminant(GenV4)));
[Factorisation(eqs): eqs in eqsII];
E1<x,y,z> := EllipticCurve(Polynomial([-1,1])*Polynomial([-l,1])*Polynomial([-m,1]));
phi1 := map<GenV4->E1 | [x^2*z,y,z^3]>;
E1;
P2<x,y,z> := ProjectiveSpace(FF,2);
jInvariant(E1);
Evaluate(jInvariant(E1),[c1*(c2-1)/(c1-1)/c2,c1/c2,0,0]) eq Evaluate(jInvariant(E1),[0,c1,0,0]); // This is a check that the choice of l and m gives us an elliptic curve isomorphic to the Legendre curve with parameter c1.
E2<x,y,z> := EllipticCurve(Polynomial([-1,1])*Polynomial([-1/l,1])*Polynomial([-1/m,1]));
jInvariant(E2);
Evaluate(jInvariant(E2),[c1*(c2-1)/(c1-1)/c2,c1/c2,0,0]) eq Evaluate(jInvariant(E1),[0,c2,0,0]); // Same for the second elliptic curve, which is isomorphic to the Legendre curve with parameter c2.
eqsid := [Evaluate(eqsII[i]/eqsII[1]^i, [c1*(c2-1)/(c1-1)/c2,c1/c2,0,0]): i in [1..5]]; // These are the Igusa invariants corresponding to the curve that in the paper we referred to as $\mathcal{C}_{\lambda_1, \lambda_2}$.
// The following curves corresponding to applying the transformation f_{\tau} simultaneously to c1 and c2.
eqs12 := [Evaluate(eqsII[i]/eqsII[1]^i, [((1-c1)*c2)/(c1*(1-c2)),(1-c1)/(1-c2),0,0]): i in [1..5]]; 
eqs13 := [Evaluate(eqsII[i]/eqsII[1]^i, [((-1+c2^(-1))*c2)/((-1+c1^(-1))*c1),c2/c1,0,0]): i in [1..5]];
eqs23 := [Evaluate(eqsII[i]/eqsII[1]^i, [c1/c2,(c1*(-1+ c2))/((-1+c1)*c2),0,0]): i in [1..5]];
eqs123 := [Evaluate(eqsII[i]/eqsII[1]^i, [(-1+c1)/(-1+c2),((-1+c1)*c2)/(c1*(-1+c2)),0,0]): i in [1..5]];
eqs132 := [Evaluate(eqsII[i]/eqsII[1]^i, [c2/c1,(-1+c2)/(-1+c1),0,0]): i in [1..5]];
perms := [eqsid, eqs12, eqs13, eqs23, eqs123, eqs132]; // This shows that the six curves have the same Igusa invariants, showing that they are isomorphic.
[[i eq j: i in perms]: j in perms];

[Evaluate(eqsII[i]/eqsII[1]^i, [c1^2/(-1 + c1)^2, -(c1/(-1 + c1)), 0, 0]): i in [1..5]]; // This is the result of making c2->1-c1.  
[Evaluate(eqsII[i]/eqsII[1]^i, [-c1, c1^2, 0, 0]): i in [1..5]]; // This is the result of making c2->1/c1.  
[Evaluate(eqsII[i]/eqsII[1]^i, [(-1 + c1)^(-1), -1 + c1, 0, 0]): i in [1..5]]; // This is the result of making c2->c1/(c1-1).  
// One can check that these all correspond to D4, by substituting c1 and c2 in the equations of the D4 stratum.

[Evaluate(eqsII[i]/eqsII[1]^i, [-(c1/(-1 + c1)^2), c1^2/(-1 + c1), 0, 0]): i in [1..5]]; // This is the result of making c2->(c1-1)/c1. 
[Evaluate(eqsII[i]/eqsII[1]^i, [c1^2/(-1 + c1), -((-1 + c1)*c1), 0, 0]): i in [1..5]]; // This is the result of making c2->1/(1-c1). 
[Evaluate(eqsII[i]/eqsII[1]^i, [-(c1/(-1 + c1)^2), c1^2/(-1 + c1), 0, 0]): i in [1..5]] eq [Evaluate(eqsII[i]/eqsII[1]^i, [c1^2/(-1 + c1), -((-1 + c1)*c1), 0, 0]): i in [1..5]];
// These all correspond to Z

// In the case of curves with automorphism group D4, we are also going to check that depending on the choice of automorphism we quotient by, we can get non-isomorphic pairs of elliptic curves.
K<i> := CyclotomicField(4);
P := ProjectiveSpace(K,3);
F<l> := FieldOfFractions(PolynomialRing(K));
GenV4<x,y,z> := HyperellipticCurve(Polynomial([-1,0,1])*Polynomial([-l,0,1])*Polynomial([-1/l,0,1])); // We consider the following model of curve, which admits an automorphism of order 4, which sends x->1/x, y->iy/x^3.
FF<l> := BaseRing(GenV4);
eqsII := [Numerator(i): i in IgusaInvariants(GenV4)[[1,2,3,4,5]]];
GeqsII := [i: i in G2Invariants(GenV4)];
Factorisation(Numerator(Discriminant(GenV4)));
[Factorisation(eqs): eqs in eqsII];
// As before, we construct the elliptic curves that are quotients by the action of the automorphism x->-x
E1<x,y,z> := EllipticCurve(Polynomial([-1,1])*Polynomial([-l,1])*Polynomial([-1/l,1]));
phi1 := map<GenV4->E1 | [x^2*z,y,z^3]>;
E1;
P2<x,y,z> := ProjectiveSpace(FF,2);
jInvariant(E1);
Factorisation(Numerator(jInvariant(E1)));
Factorisation(Denominator(jInvariant(E1)));
E2<x,y,z> := EllipticCurve(Polynomial([-1,1])*Polynomial([-1/l,1])*Polynomial([-l,1]));
phi2 := map<GenV4->E2 | [x*z^2,i*y,x^3]>;
jInvariant(E2);
// Now we construct the quotient maps by the automorphism of order 2, given by x->-1/x, y->iy/x^3.
phisp1 := map<GenV4->P2 | [x*(x-i*z)*z,y,(x-i*z)^3]>;
comp := map<P2->P2 | [(-1/2*i*l/(l^2 + 2*l + 1))*x,(-1/2*i*l/(l^2 + 2*l + 1))^2*y,z]>;
Image(phisp1*comp);
El1<x,y,z> := EllipticCurve(Polynomial([-1/16*l^4/(l^8 + 8*l^7 + 28*l^6 + 56*l^5 + 70*l^4 + 56*l^3 + 28*l^2 + 8*l + 1), 3/4*l^3/(l^6 + 6*l^5 + 15*l^4 + 20*l^3 + 15*l^2 + 6*l + 1), (-1/4*l^3 - 5/2*l^2 - 1/4*l)/(l^4 + 4*l^3 + 6*l^2 + 4*l + 1), 1])); 
Expand(phisp1*comp);
phisp1 := map<GenV4->El1 | [-1/2*i*l/(l^2 + 2*l + 1)*x^2*z + -1/2*l/(l^2 + 2*l + 1)*x*z^2,-1/4*i*l^2/(l^4 + 4*l^3 + 6*l^2 + 4*l + 1)*y,x^3 + -3*i*x^2*z + -3*x*z^2 + i*z^3]>;
phisp2 := map<GenV4->P2 | [x*(x+i*z)*z,y,(x+i*z)^3]>;
Image(phisp2*comp);
El2<x,y,z> := EllipticCurve(Polynomial([1/16*l^4/(l^8 + 8*l^7 + 28*l^6 + 56*l^5 + 70*l^4 + 56*l^3 + 28*l^2 + 8*l + 1), 3/4*l^3/(l^6 + 6*l^5 + 15*l^4 + 20*l^3 + 15*l^2 + 6*l + 1), (1/4*l^3 + 5/2*l^2 + 1/4*l)/(l^4 + 4*l^3 + 6*l^2 + 4*l + 1), 1])); 
Expand(phisp2*comp);
phisp2 := map<GenV4->El2 | [-1/2*i*l/(l^2 + 2*l + 1)*x^2*z + 1/2*l/(l^2 + 2*l + 1)*x*z^2, -1/4*l^2/(l^4 + 4*l^3 + 6*l^2 + 4*l + 1)*y, x^3 + 3*i*x^2*z - 3*x*z^2 - i*z^3]>;
j1 := jInvariant(E1);
j2 := jInvariant(E2);
jl1 := jInvariant(El1);
jl2 := jInvariant(El2);
j1 eq j2;
jl1 eq jl2;
j1 eq jl1; // We can check that E1 and E2 are isomorphic, and the same is true for El1 and El2. However, E1 and El1 are not isomorphic.

// The following part of the code allows us to compute a model for the moduli space $\mathcal{M}_{ell}\C_2$ described in the paper, and for the sets $E_0$.
K<l> := FieldOfFractions(PolynomialRing(Rationals()));
// K := Rationals();
P11<x0,x1,y0,y1>:= ProductProjectiveSpace(K,[1,1]); // This is P^1 x P^1.
P2<z0,z1,z2> := ProjectiveSpace(K,2);
symphi := map<P11->P2 | [x0*y0,x1*y0+x0*y1,x1*y1]>; // This map one can check describes the quotient map by the involution that interchanges the two factors of P^1 x P^1, which is isomorphic to P2.
tau2 := map<P11->P11 | [x0,x0-x1,y0,y0-y1]>; // This corresponds to the simultaneous action of f_(12)(z)=1-z in the two factors of P^1 x P^1.
Expand(tau2*tau2); // We check that this is the identity map.
Expand(tau2*symphi);
M2 := Matrix(K, 3, 3, [1, 0, 0, 2, -1, 0, 1, -1, 1]); // From expanding the composition of tau2 and symphi, we can see that the matrix that describes the action of the group on P2 is this one.

tau3 := map<P11->P11 | [x1,x1-x0,y1,y1-y0]>; // This corresponds to the simultaneous action of f_(132)(z)=1/(1-z) in the two factors of P^1 x P^1.
Expand(tau3*tau3*tau3);
Expand(tau3*symphi);
M3 := Matrix(K, 3, 3, [0, 0, 1, 0, -1, 2, 1, -1, 1]); // From expanding the composition of tau3 and symphi, we can see that the matrix that describes the action of the group on P2 is this one.

G := sub<GL(3, K) | M3, M2>; // We know compute the group generated by the two matrices and its invariants.
R := InvariantRing(G);
inv := FundamentalInvariants(R); // The invariants have weights 1,2,3.
Relations(R);
hom<CoordinateRing(P2)->PolynomialRing(R) | [z0,z1,z2]>;
PR := PolynomialRing(R);
id := hom<PR->CoordinateRing(P2) | [PR.1,PR.2,PR.3]>;
Pw<w1,w2,w3> := ProjectiveSpace(K, [1,2,3]); // We define a weighted projective space with weights 1,2,3.
newinv := [2*id(inv[1]), +3/2*id(inv[1])^2-1/2*id(inv[2]), -1/27*(-45/4*id(inv[1])^3+27/4*id(inv[1])*id(inv[2])+9/2*id(inv[3]))]; // These combination of invariants make it more elegant the map to P(1,2,3).
emb := map<P2->Pw | newinv>;
IrreducibleComponents(BaseScheme(emb)); // The invariants define a morphism from P2 to the weighted projective space Pw, which contains the quotient space $\mathcal{M}_{ell}\C_2$ as an open subset.
[Factorisation(inv): inv in DefiningEquations(Expand(symphi*emb))];
Expand(symphi*emb); // We can check that the action of the tau2 and tau3 is trivial on the quotient space, as expected.
Expand(tau3*symphi*emb); 
Expand(tau2*symphi*emb);
Cl := Scheme(P11,x1-l*x0); // This is the curve corresponding to (E_0,\phi_0) x X(2) inside of P^1 x P^1.
sing := IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(Clim)))[1];
Clim := emb(symphi(Cl)); // The image inside of the weighted projective space.

Csing := Scheme(P11, x0); // This is the curve corresponding to the points of P^1 that do not define an elliptic curve.
Climsing := emb(symphi(Csing)); // The image of the previous curve is the closed subvariety whose complement defines $\mathcal{M}_{ell}\C_2$.

Csing2 := Scheme(P11, y0*x1-x0*y1); // This corresponds to the diagonal inside of P1 x P1. 
Climsing2 := emb(symphi(Csing2)); // The $\bar{\mathcal{M}}_{ell}$.

CD412 := Scheme(P11, y0*x0-x1*y1); // This is the curve corresponding to the pairs of elliptic curves isogenous to a curve with automorphism group D4.
IrreducibleComponents(ReducedSubscheme(emb(symphi(CD412))));
CD413 := Scheme(P11, y0*(x0-x1)-x0*y1);
IrreducibleComponents(ReducedSubscheme(emb(symphi(CD413))));



// Study of the stratum associated to the curve D4
K := Rationals();
// K := GF(3); // Changing to GF(3) we can see how the singular points change.
// K := GF(5); // Chamging to GF(5) we can see how the equations change.
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
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D4))); // Here we compute the singular locus of the D4 strata.
[<Dimension(C), Degree(C)>: C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D4)))]; // We can see that it is only one point.
sptD4 := D4![120, 330, -320, -36825, 11664];
IsSingular(sptD4);
sC := HyperellipticCurveFromIgusaInvariants([120, 330, -320, -36825, 11664]); // We check that the singular point corresponds to the curve with automorphism group C3:D4.
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->D4 | [x0, (5*x0^2 - 17*x0*x1 + 15*x1^2)/8, -1/16*((3*x0 - 5*x1)*(x0 - 2*x1)^2), (-37*x0^4 + 238*x0^3*x1 - 567*x0^2*x1^2 + 590*x0*x1^3 - 225*x1^4)/256, ((2*x0 - 3*x1)^3*(x0 - 2*x1)^2)/1024]>; // This is a parametrisation of the D4 stratum.
IrreducibleComponents(BaseScheme(rat));
invrat := map<D4->P1 | [J2*(11*J2^2 - 480*J4), 5*J2^3 - 224*J2*J4 - 720*J6]>; // This is the inverse map.
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
Expand(rat*invrat);
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);
[(-(x0 - 5/2*x1)/8)^i*Evaluate(eqsII[i],[(2*x0 - 3*x1)/(-8*x0 + 20*x1),1,1]): i in [1..5]]; // Here we can check that when we choose f1=(2*x0 - 3*x1)/(-8*x0 + 20*x1), f3=1, f5=1, we can parametrise all elements in the strata.


// Study of the stratum associated to the curve D6
// In characteristic not three
K<w> := ext<Rationals() | Polynomial([1,1,1])>; // Here we work over the extension of Q by a third root of unity.
// K<w> := GF(5,2);
P := ProjectiveSpace(K,[2,2,2,1,1]);
F<f0, f1, f2, g0, g1> := CoordinateRing(P);
GenD6<x,y,z> := HyperellipticCurve(Polynomial([f0, f1, f2, -10*f0 - 5*f1 - 2*f2, 15*f0 + 5*f1 + f2, -6*f0 - f1, f0]),Polynomial([g0, g1, -3*g0 - g1, g0])); 
GenD6alt<x,y,z> := HyperellipticCurve(Polynomial([f0, 0, 0, f1, 0, 0, f2]),Polynomial([g0, 0, 0, g1])); // We have an alternative model corresponding to curves where the automorphism of order 3 is given by the action of a root of unity.
FF<f0, f1, f2, g0, g1>:= BaseRing(GenD6);
eqsII := [Numerator(i): i in IgusaInvariants(GenD6)];
FF<f0, f1, f2, g0, g1>:= BaseRing(GenD6alt);
eqsIIalt := [Numerator(i): i in IgusaInvariants(GenD6alt)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..10]] >;
MinimalBasis(J);
D6 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D6))); // This is the singular locus of the D6 stratum.
[<Dimension(C), Degree(C)>: C in IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(D6)))]; // One can check that it is only one point, corresponding to the curve with automorphism group GL(2,3).
sptD6 := D4![20, 30, -20, -325, 64];
IsSingular(sptD6);
sC := HyperellipticCurveFromIgusaInvariants([20, 30, -20, -325, 64]);
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->D6 | [x0, -3*x1*(x0 + 10*x1), -(x1^2*(3*x0 + 40*x1)), -(x1^2*(3*x0^2 + 55*x0*x1 + 225*x1^2)), -(x1^3*(x0 + 12*x1)^2)]>; // This is a parametrisation of the D6 stratum.
IrreducibleComponents(BaseScheme(rat));
invrat := map<D6->P1 | [J2*(3*J2^2 - 40*J4), -(J2*J4) - 30*J6]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
Expand(rat*invrat);
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);
[(-(x0 + 120*x1)/27)^i*Evaluate(eqsIIalt[i],[(-x0 - 93*x1)/(3*x0 + 360*x1),0,-1,1,1]): i in [1..5]]; // Once again, here we check that we can choose values of f0, f1, f2, g0, g1 that allow us to parametrise the D6 stratum.
[(x0 + 120*x1)^i*Evaluate(eqsII[i],[(4*x0 + 453*x1)/(81*(x0 + 120*x1)), (2*w*(x0 + 3*w*x0 + 93*x1 + 360*w*x1))/(27*(x0 + 120*x1)), (5*w*(3*x0 + w*x0 + 360*x1 + 93*w*x1))/(27*(x0 + 120*x1)), 0, 1]): i in [1..5]]; // A parametrisation for the alternative model of the curve we defined.


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
GenC25<x,y,z> := HyperellipticCurve(Polynomial([0,0,0,f3,0,f5]),g0); // This is the parametrisation of the strata found by Igusa.
FF<f3, f5, g0>:= BaseRing(GenC25);
eqsII := [Numerator(i): i in IgusaInvariants(GenC25)];
IP<J2,J4,J6,J8,J10> := ProjectiveSpace(K,[1,2,3,4,5]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,P,d)) : d in  [1..10]] >;
MinimalBasis(J); // We can check that corresponds to the line J2=J4=J6=0.
C25 := Scheme(IP,MinimalBasis(J));
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(C25)));
P1<x0, x1> := ProjectiveSpace(K,1);
rat := map<P1->C25 | [0, 0, 0, x0^4, x1^5]>;
IrreducibleComponents(BaseScheme(rat));
invrat := map<C25->P1 | [J8^5, J10^4]>;
IrreducibleComponents(ReducedSubscheme(BaseScheme(invrat)));
F<x0,x1> := FieldOfFractions(CoordinateRing(P1));
DefiningEquations(rat);


// PART II: THE EKEDAHL-OORT STRATA
// Construction of the strata of curves in characteristic 2 with p-rank 1
K := GF(2);
P := ProjectiveSpace(K,[2,2,2,2,2,2,2,1,1,1,1]);
F<f0, f1, f2, f3, f4, f5, f6, g3> := CoordinateRing(P);
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, f3]),Polynomial([0, 0, g3, 0])); // The curves that have p-rank 1 are those where the g(x) has two repeated roots
FF<f0, f1, f2, f3, f4, f5, f6, g3> := BaseRing(GenC);
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
GenC := HyperellipticCurve(Polynomial([f0, f1, f2, f3, f4, f5, f6]),Polynomial([0, 0, 0, g3])); // The curves that have p-rank 1 are those where the g(x) has three repeated roots
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

// For higher primes, we will make use of the Hasse-Witt matrix to construct the Ekedahl-Oort strata. We will use the description of the Hasse-Witt matrix given in Achter and Howe.
// Make sure that we have defined the HW Matrix correctly, by replicating the example given in the paper.
K<a> := ext<GF(5) | Polynomial([3,3,0,1])>;
f<x> := Polynomial([0, a^(56), a^(18), a^(92), 1, 1]);
p := 5;
n := ((p-1)/2);
Z := Integers();
pow := f^(Z!n);
HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
HWmatfr := Matrix([[Coefficient(pow, p-1)^p, Coefficient(pow, 2*p-1)^p],[Coefficient(pow, p-2)^p,Coefficient(pow, 2*p-2)^p]]);
rankmat := HWmat*HWmatfr;


for p in PrimesInInterval(3,50) do 
SplittingField(SupersingularPolynomial(p));
Degree(SupersingularPolynomial(p));
end for;


// This piece of code allows us to construct the strata of EO type (1,1), and the intersection with the C2 x C2 strata, for primes p in a range.
for p in PrimesInInterval(3, 23) do 
  K<a>:= GF(p,2);
  Z := Integers();
  P := ProjectiveSpace(K,3); 
  F<a0, a1, a2, a3> := CoordinateRing(P);
  f<x> := Polynomial([0, -a0, a0 - a1, a1 - a2, a2 - a3, a3]);
  GenC := HyperellipticCurve(f); // We define the generic curve depending on {a0, a1, a2, a3}, y^2 = x (x - 1) (a3 x^3 + a2 x^2 + a1 x + a0).
  FF<a0, a1, a2, a3> := BaseRing(GenC); 
  eqsII := [Numerator(i): i in IgusaInvariants(GenC)[[1,2,3,5]]];
  IP<J2,J4,J6,J10> := ProjectiveSpace(K,[1,2,3,5]);
  n := ((p-1)/2);
  pow := f^(Z!n);
  HWmat := Matrix([[Coefficient(pow, p-1), Coefficient(pow, 2*p-1)],[Coefficient(pow, p-2),Coefficient(pow, 2*p-2)]]);
  prank1 := ReducedSubscheme(Scheme(P, Determinant(HWmat))); // We compute the scheme inside of P^3 that corresponds to the determinant of the Hasse-Witt matrix.
  phi := map<P->IP | eqsII>;
  J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi,prank1,d)) : d in  [1..(p-1)/2]] >; // Based on what happens for small primes, it seems like there is always a relation of degree (p-1)/2.
  AOp := Scheme(IP,MinimalBasis(J));
  Int1V4 := Scheme(AOp, J2^4*J4^4*J6 - 64*J2^2*J4^5*J6 + 1024*J4^6*J6 - 2*J2^5*J4^2*J6^2 + 136*J2^3*J4^3*J6^2 - 2304*J2*J4^4*J6^2 + J2^6*J6^3 - 72*J2^4*J4*J6^3 + 1080*J2^2*J4^2*J6^3 + 6912*J4^3*J6^3 + 216*J2^3*J6^4 - 7776*J2*J4*J6^4 + 11664*J6^5 + 8*J2^4*J4^3*J10 - 512*J2^2*J4^4*J10 + 8192*J4^5*J10 - 72*J2^5*J4*J6*J10 + 4816*J2^3*J4^2*J6*J10 - 84480*J2*J4^3*J6*J10 - 48*J2^4*J6^2*J10 - 12960*J2^2*J4*J6^2*J10 + 691200*J4^2*J6^2*J10 - 129600*J2*J6^3*J10 - 432*J2^5*J10^2 + 28800*J2^3*J4*J10^2 - 512000*J2*J4^2*J10^2 - 96000*J2^2*J6*J10^2 + 11520000*J4*J6*J10^2 + 51200000*J10^3); // This was the degree 15 polynomial defining the stratum curves with automorphism group C2 x C2.
  printf "\n\n Prime: %o\n", p;
  AOp;
  printf "Irreducible p-rank 1 strata?: %o\n", IsIrreducible(AOp);
  printf "Reduced p-rank 1 strata?: %o\n", IsReduced(AOp);
  printf "Number of singular points: %o\n", #IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(AOp)));
  // printf "Number of components of the intersection with C2xC2 strata: %o\n", #IrreducibleComponents(ReducedSubscheme(Int1V4)); // This is the slowest command in this for loop.
  printf "Number of supersingular elliptic curves in characteristic p: %o\n\n", Degree(SupersingularPolynomial(p));
end for;






p := 5;
K<a>:= GF(p,2);
K := Rationals();
Z := Integers();
P := ProjectiveSpace(K,3); // y^2 = x (x - 1) (a3 x^3 + a2 x^2 + a1 x + a0)
F<a0, a1, a2, a3> := CoordinateRing(P);
f<x> := Polynomial([0, -a0, a0 - a1, a1 - a2, a2 - a3, a3]);
GenC := HyperellipticCurve(f);
FF<a0, a1, a2, a3> := BaseRing(GenC);
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
prank0 := Scheme(P, rankmat[1,1]);
anumber2 := Scheme(P, [HWmat[1,1], HWmat[1,2], HWmat[2,1], HWmat[2,2]]);
phi := map<P->IP | eqsII>;
J := ideal< CoordinateRing(IP) | &cat[ DefiningEquations(Image(phi, prank0, d)) : d in  [1..15]]>;
SSp := Scheme(IP,MinimalBasis(J));
SSp;
IsIrreducible(SSp);
IrreducibleComponents(SSp);
IsReduced(SSp);
IrreducibleComponents(ReducedSubscheme(JacobianSubrankScheme(SSp)));
