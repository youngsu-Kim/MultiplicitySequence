newPackage(
        "jMult",
        Version => "0.6", 
        Date => "Aug. 31, 2016",
        Authors => {
	     {Name => "Youngsu Kim", 
                  Email => "youngsu.kim@ucr.edu", 
                  HomePage => "https://sites.google.com/site/jmultiplicity/"}
	     },
        Headline => "computing j-Multiplicity and other related invariants of an ideal",
        DebuggingMode => true,
	Reload => "false"
        )

--------------------------
-- Necessary packages
--------------------------
needsPackage "Polyhedra"
needsPackage "Normaliz"

--------------------------
-- methods to be exported
--------------------------
export {jmult, grGr, egrGr, lengthij, length10ij,length11ij, cSubi, multSeq, mon2Exp, isBddFacet, pyrF, box, NP, monReduction, monjMult, gHilb
 }


--------------------------
-- gHilb 
--------------------------
gHilb = method()
gHilb(ZZ, Ideal) := Module => (n, III) -> (
     RRR := ring III;
     Inp1 := sub((intclMonIdeal trim III^(n+1))_0 , RRR );
     In := sub((intclMonIdeal trim III^n)_0, RRR  );
     HH^0( (In / Inp1) )
     )

--------------------------
--- mon2Exp extracts the exponent of a monomial ideal as a vector
--------------------------
mon2Exp = method ()
mon2Exp(Ideal) := Matrix => (III) -> (
     if ((isMonomialIdeal III) == false) then (print "The input is not a monomial ideal", break);
     J := trim III;
     n := numgens J;
     transpose (matrix flatten apply( for i from 0 to (n - 1) list J_i, exponents ))
     )

--------------------------
-- monReduction computes a minimal monomial reduction of a monomial ideal
--------------------------
monReduction = method()
monReduction(Ideal) := Ideal => (I) -> (
     R := ring I;
     P := NP (I);
     M := vertices P;
     s := rank source M;
     J := ideal (0_R);
     for i from 0 to (s-1) do J = J + ideal R_((entries transpose M_{i})_0);
     trim J
     )
     
--------------------------     
--- from a matrix MMM isBddFacet extracts rows where all the entries are not zero
--------------------------
isBddFacet = method ()
isBddFacet(ZZ, Matrix) := ZZ => (nnn, MMM) -> (
     --- rrr := rank target MMM; --- # of rows
     sss := rank source MMM; --- # of columns
     mutableM := mutableIdentity (ZZ,sss); --- row as a vector
     for iii from 0 to (sss - 1) do (mutableM_(iii,iii) = MMM_(nnn,iii));
     determinant matrix mutableM --- No if 0, Yes otherwise
     )

--------------------------
-- 
--------------------------
pyrF = method ()
pyrF(Matrix) := Matrix => (FacetMatrix) -> (
     rrr := rank target FacetMatrix; --- # of rows
     --- sss := rank source FacetMatrix; --- # of columns
     FacetMatrix | transpose map(ZZ^1, rrr, i -> 0)
     )

--------------------------
---- gives a matrix of the from where all the entries are zero except one spot i,i
--------------------------
box = method ()
box(ZZ,ZZ) := Matrix => (i,n) -> (
     MMM := mutableIdentity (ZZ,n);
     for rrr from 0 to (n-1) do if ( rrr != (i-1)) then MMM_(rrr,rrr) = 0;
     matrix MMM
     )

--------------------------
-- NP computes the Newton polyhedron
--------------------------
NP = (II) -> (
     ddd := sub(dim ring II,ZZ);
     convexHull (mon2Exp II) + posHull (id_(ZZ^(ddd)))     
     )

---- monomial j-multiplicity
---- Dependency: needsPackage "Polyhedra", pryF, isBddFacet, mon2Exp, NP 
monjMult = method ()
monjMult(Ideal) := ZZ => (III) -> (
     if ((isMonomialIdeal III) == false) then (print "The input is not a monomial ideal", break);     
     II := III; --- unnecssary, one could change every II to III     
     ddd := sub(dim ring II,ZZ);
     PPP := convexHull (mon2Exp II) + posHull (id_(ZZ^(ddd)));
     MMM := halfspaces PPP;
     MMMm := (MMM)_0;
     MMMv := (MMM)_1;
     r := rank target MMMm;  --- # of rows
     s := rank source MMMm;  --- # of columns
     monj := 0_(QQ);
     for ppp from 0 to (r-1) do ( if (isBddFacet(ppp, MMMm) != 0) then (monj = monj + (ddd)! * (volume convexHull pyrF (vertices intersection (MMMm, MMMv, MMMm^{ppp}, MMMv^{ppp} ) ) ) ) ) ;
     sub(monj, ZZ)
)

--------------------------
-- multSeq computes the multiplicity sequence of an ideal
--------------------------
multSeq = method ()
multSeq Ideal := List => (I) -> (
      for i from 0 to (dim ring I) list cSubi (i,I)
      )


--------------------------
-- 
--------------------------
cSubi = method ()
cSubi (ZZ, Ideal) := ZZ => (i,I) -> (
     hilbertS := reduceHilbert hilbertSeries grGr I;
     poinP := numerator hilbertS;
     dPoinP := denominator hilbertS;
     A := ring poinP;
     B := newRing (A, Degrees => {{1,0}, {0,1},{0,0}});
     use B;
     topP := sub (poinP, B);
     botP := value toString dPoinP;
     firVar := (ultimate (flatten, entries (vars B)_{0}))_0;
     secVar := (ultimate (flatten, entries (vars B)_{1}))_0;
     powerFirVar := (degree botP)_0;     
     powerSecVar := (degree botP)_1;     
     d := dim ring I;
     a := powerFirVar - i;
     b := powerSecVar - (d-i);
     c := topP;
     for i from 1 to a do (c = diff( firVar, c));
     c = sub (c, firVar => 1);
     for i from 1 to b do (c = diff (secVar, c));
     c = sub (c, secVar => 1); 
     c = c*(-1)^(a+b);
     if (c <= 0 or a < 0 or b < 0) then 0 else (sub(c,ZZ) / (a! * b!))
)

lengthij = method ()
lengthij (ZZ, ZZ, Ideal) := ZZ => (i,j,I) -> (
     R := ring I;
     m := ideal vars R;
     M := (trim (m^i*I^j + I^(j+1)) ) / (  trim (m^(i+1)*I^j + I^(j+1)) );
     degree (M^1)
     )

length10ij = method ()
length10ij (ZZ, ZZ, Ideal) := ZZ => (i,j,I) -> (
     R := ring I;
     m := ideal vars R;
     M := (trim (I^j ) ) / (  trim (m^(i+1)*I^j + I^(j+1)) );
     degree (M^1)
     )     

length11ij = method()
length11ij (ZZ,ZZ, Ideal) := ZZ => (i,j,I) -> (
     L := 0;
     for k from 0 to j do (L = L + length10ij(i,k,I));
     sub (L, ZZ)
     )

grGr = method ()
grGr (Ideal) := Ring => (I) -> (
     R := ring I;
     m := ideal vars R;
     n := numgens I;
     d := numgens m;
     if (I == m) then print "I is m" else assert ( (ideal (1_R) == I:m) == false ); -- To check if the ideal is inside of the maximal ideal m
     -- Start of gr_I(R)
     K1 := reesIdeal I; 
     reesRingI := ring K1;
     v := "v";
     R1 := (R) ( monoid[ VariableBaseName => v, Variables => (n)]); -- The source of the first Rees ring with the right ordering
     phi1 := map(R1, reesRingI, vars R1);
     IR1 := phi1 sub(I, reesRingI);
     K1R1 := phi1 K1;
     G1 := R1 / (IR1 + K1R1);
     -- Start of gr_M(gr_I(R))
     mG1 := sub (phi1 sub(m, reesRingI), G1);
     K2 := reesIdeal mG1;
     reesRingm := ring K2;
     u := "u";
     R2 := (G1) ( monoid[VariableBaseName => u, Variables => (d)]);
     phi2 := map(R2, reesRingm, vars R2);
     mG1R2 := phi2 sub(mG1, reesRingm);
     K2R2 := phi2 K2;
     TTT := R2 / (mG1R2 + K2R2);
     -- modification of TTT to have the right degrees
     (TT, map3) := flattenRing TTT; 
     TT
     --minimalPresentation TT
     -- hilbertSeries oo
)

egrGr = method ()
egrGr (Ideal) := ZZ => (I) -> (
     A := grGr I;
     B := newRing (A, Degrees => splice{ (#gens A) : 1});
     degree B
     )

--------------------------
-- jmult computes the j-multiplicity of an ideal following the method in Nishida-Ulrich. 
-- The primary version of the code was writting by H. Schenk and J. Validashti.
--------------------------
jmult = method ()
jmult (Ideal) := ZZ => (I) -> (
     	     if ((isIdeal I) == false) then (print "input is not an ideal", break);
             R := ring I;
             r := rank source vars R;
             G := gens I;
             g := rank source G;
             M := random(R^r,R^g)*transpose G;
             J := ideal(submatrix(M,{0..r-2},));
             UI := saturate(J,I) + ideal(submatrix(M,{r-1..r-1},));
	     N := monoid[Variables=>r, MonomialOrder=>{Weights=>{-1,-1},RevLex},Global=>false];
--           L := leadTerm gb UI;
     	     L := tangentCone UI;
             S := (ZZ/101) N;
             f := map(S,R,vars S);
             C := S/f(L);
--     	     dim (R/ ideal(submatrix(M,{0..r-1},)))
             if (dim C == 0) then length (C^1) else print "analytic spread not maximal"	     
	     )





--------------------------
-- Documentation
--------------------------
beginDocumentation()

doc ///
 Key
   "jMult"
 Headline
   "Computing the j-Multiplicity of an ideal"
 Description
   Text
    This package includes a few functions related the j-multiplicity and multiplicity sequence of an ideal. 
--    The package contains the method "jmult" which computes the j-multiplicity of an ideal using Theorem 3.6 in Nishida-Ulrich (Computing j-multiplicities, J. of Alg 2010). 
   Example
 Caveat
    - The function jmult is based on the code written by H.Schenck and J. Validashti.	  
    
    - The function monjMult comuputes the j-multiplicity for an monomial ideal by computing the volumn of the pyramid. This is a result of J. Jeffries and J. Montano, The $j$-Multiplicity of Monomial Ideals, to appear in Math. Res. Letters.


    
    - The author thanks D. Eisenbud, D. Grayson, and M. Stillman for organizing a Macaulay2 day during the special year in commutative algebra 2012-2013 at MSRI where he learned how to write a package.
 SeeAlso
///

doc ///
 Key 
   "jmult"
 Headline
   "Computing the j-multiplicity"
 Usage
   jmult(I)
 Inputs
   I:Ideal
 Outputs
   :ZZ
    j-multiplicity
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y];
    	 I = ideal"x2,xy";
    	 jmult I
   Code
   Pre
 Caveat
 SeeAlso
///



doc ///
 Key 
   "grGr"
 Headline
   "Computing the bigraded ring Gr_m(Gr_I(R))"
 Usage
   grGr(I)
 Inputs
   I:Ideal
 Outputs
   :Ring
    The bigraded ring Gr_m(Gr_I(R)) as a minimal presentation from a bigraded polynomial ring in variables s and t. 
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y];
    	 I = ideal"x2,xy";
    	 A = grGr I;
	 describe A 
	 hilbertSeries A
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "lengthij"
 Headline
   "Comuting the length of the module $(m^i*I^j + I^{j+1}) / (m^(i+1)*I^j + I^{j+1})$"
 Usage
   lengthij(i,j,I)
 Inputs
   i: ZZ
   j: ZZ
   I:Ideal
 Outputs
   :ZZ
    The length of the module $(m^i*I^j + I^{j+1}) / (m^(i+1)*I^j + I^{j+1})$.
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y];
    	 I = ideal"x2,xy";
    	 lengthij (2,3, I)
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "cSubi"
 Headline
   "Comuting the c_i in the multiplicity sequence of an ideal"
 Usage
   cSubi (i, I)
 Inputs
   i: ZZ
   I: Ideal
 Outputs
   :ZZ
    c_i.
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y];
    	 I = ideal"x2,xy";
    	 cSubi(0,I)
	 jmult I
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "multSeq"
 Headline
   "Comuting the multiplicity sequence of an ideal"
 Usage
   multSeq I
 Inputs
   I: Ideal
 Outputs
   :List
    The multiplicity sequence $c_0,...,c_d$.
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y];
    	 I = ideal"x2,xy";
    	 multSeq I
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "monjMult"
 Headline
   "Comuting the j-multiplicity of a ideal by computing the volumn of the pyramid of an ideal"
 Usage
   monjMult I
 Inputs 
   I: Ideal
 Outputs
   :ZZ
    The j-multiplicity of a monomial ideal.
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y,z];
	 I = ideal"x6,y6,z6,x2yz,xy2z,xyz2";
	 monjMult (I)
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "mon2Exp"
 Headline
   "Obtaining the exponent vector of the generation set of a monomial ideal"
 Usage
   mon2Exp I
 Inputs
   I: Ideal
 Outputs
   :Matrix
    The matrix whose cloumns correspond to the exponents.
 Consequences
 Description
   Text
   Example
   	 R = QQ[x,y];
    	 I = ideal"x2,xy";
    	 mon2Exp I
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "isBddFacet"
 Headline
   "Checking if the halfspace determining the Newton Polyheron of an ideal I is a bounded facet"
 Usage
   isBddFacet M
 Inputs
   M: Matrix
 Outputs
   :ZZ
    0 if and only if unbounded facet
 Consequences
 Description
   Text
   Example
   	 -- loadPackage "Polyhedra"
	 needsPackage "Polyhedra"
	 matrix {{0,2},{1,1}}
	 convexHull oo
	 -- P = convexHull transpose matrix {{0,2},{1,1}} + posHull (id_(ZZ^2))
	 -- N = halfspaces P;
	 -- for i from 0 to (rank target N_0) - 1 list isBddFacet (i, N_0)
   Code
   Pre
 Caveat
 SeeAlso
///

doc ///
 Key 
   "box"
 Headline
   "Constructing a square matrix where all the entries are zero except at one entry on the diagonal"
 Usage
   box (i,n)
 Inputs
   i : ZZ
   n : ZZ
 Outputs
   :Matrix
 Consequences
 Description
   Text
   Example
   	 box (2,3)
   Code
   Pre
 Caveat
 SeeAlso
///


doc ///
 Key 
   "pyrF"
 Headline
   "Add the origion to a given vertex set"
 Usage
   pyrF M
 Inputs
   M: Matrix
 Outputs
   :Matrix
    Matrix with vertices
 Consequences
 Description
   Text
   Example
   	 -- loadPackage "Polyhedra, Reload => true";
	 M = transpose matrix {{0,2},{1,1}}
	 pyrF M 	 
   Code
   Pre
 Caveat
 SeeAlso
///

end







