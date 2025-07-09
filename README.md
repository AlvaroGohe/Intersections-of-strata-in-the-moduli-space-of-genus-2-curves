# Intersections of strata in the moduli space of genus 2 curves
This is some code for my article on **Intersections of the automorphism and Ekedahl-Oort strata in the moduli space of genus two curves**.

There are two main files, a Magma file where most of the computations of the paper are done, and a Mathematica file that I have used to help with some easier tasks.

This Magma file `Strata_in_the_moduli_space_of_genus_2_curves.m` contains explicit computations in the moduli space of genus 2 curves, such as:
- The description of the automorphism strata in terms of the Igusa invariants, and the study of their geometric properties.
- The construction of universal families of genus two curves with those automorphism groups.
- The construction of the quotients of genus two curves by automorphisms of order 2, as described in the paper.
- The computation of the Ekedahl-Oort strata in positive characteristic using Hasse-Witt matrices.

In the Mathematica file `Some_calculations_related_to_the_description_of_strata.nb`, we check the formulas to express the Igusa invariants in terms of the $x$-coordinates of the Weierstrass points of the curves, and we compute models for the curves admitting a given automorphism group.
