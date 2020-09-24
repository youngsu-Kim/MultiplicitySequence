newPackage(
        "MultiplicitySequence",
        Version => "0.1", 
        Date => "Sep. 22, 2020",
        Authors => {
	     {Name => "Justin Chen", 
                  Email => "??@??.edu", 
                  --HomePage => "https://sites.google.com/site/jmultiplicity/"}
	     },
	     {Name => "Youngsu Kim", 
                  Email => "youngsu.kim@csusb.edu", 
                  --HomePage => "https://sites.google.com/site/jmultiplicity/"}
	     },
	     {Name => "Jonathan Montaño", 
                  Email => "??@??.edu", 
                  --HomePage => "https://sites.google.com/site/jmultiplicity/"}
	     }
	},
        Headline => "computing the multiplicity sequence of an ideal",
        DebuggingMode => true,
	PackageExports => {"ReesAlgebra", 
	    "TangentCone", 
	    "OldPolyhedra",
	    "Normaliz",
	    "PrimaryDecomposition",
	    "MinimalPrimes"
	    },
	Reload => "true"
        )

export {"jmult", 
    "grGr", 
--    "egrGr", 
--    "lengthij", 
--    "length10ij",
--    "length11ij", 
    "cSubi", 
    "multSeq", 
--    "mon2Exp", 
--    "isBddFacet", 
--    "pyrF", 
--    "box", 
    "NP", 
    "monReduction", 
    "monjMult", 
    "gHilb",
    "hilbertSamuelMultiplicity",
    "getGenElts",
    "multiplicitySequence",
    "indexedMultiplicitySequence",
    "randomSubset",
    "numCandidates",
    "minTerms"
 }

installMinprimes() -- for MinimalPrimes.m2

gHilb = method()
gHilb(ZZ, MonomialIdeal) := Module => (n, I) -> (
     R := ring I;
     Inp1 := sub((intclMonIdeal trim I^(n+1))_0 , R );
     In := sub((intclMonIdeal trim I^n)_0, R  );
     HH^0( (In / Inp1) )
     )
gHilb(ZZ, Ideal) := MonomialIdeal => (I) -> (
    J := monomialIdeal I;
    if ( J != I ) then error "Expected monomial ideal";
    gHilb J
    )

---- extract the exponent of a monomial ideal
mon2Exp = method ()
mon2Exp(Ideal) := Matrix => (III) -> (
     if ((isMonomialIdeal III) == false) then (print "The input is not a monomial ideal", break);
     J := trim III;
     n := numgens J;
     transpose (matrix flatten apply( for i from 0 to (n - 1) list J_i, exponents ))
     )

monReduction = method()
monReduction(MonomialIdeal) := MonomialIdeal => (I) -> (
     R := ring I;
     P := NP (I);
     M := vertices P;
     s := rank source M;
     J := ideal (0_R);
     for i from 0 to (s-1) do J = J + ideal R_((entries transpose M_{i})_0);
     trim J
     )
monReduction(Ideal) := MonomialIdeal => (I) -> (
    J := monomialIdeal I;
    if ( J != I ) then error "Expected monomial ideal";
    monReduction J
    )
     
--- from a matrix MMM extract the rows where all the entries are not zero
isBddFacet = method ()
isBddFacet(ZZ, Matrix) := ZZ => (nnn, MMM) -> (
     --- rrr := rank target MMM; --- # of rows
     sss := rank source MMM; --- # of columns
     mutableM := mutableIdentity (ZZ,sss); --- row as a vector
     for iii from 0 to (sss - 1) do (mutableM_(iii,iii) = MMM_(nnn,iii));
     determinant matrix mutableM --- No if 0, Yes otherwise
     )

---- 
pyrF = method ()
pyrF(Matrix) := Matrix => (FacetMatrix) -> (
     --rrr := rank target FacetMatrix; --- # of rows
     --sss := rank source FacetMatrix; --- # of columns
     FacetMatrix | transpose map(ZZ^1, rank target FacetMatrix, 0)
     )

---- gives a matrix of the from where all the entries are zero except one spot i,i
box = method ()
box(ZZ,ZZ) := Matrix => (i,n) -> (
     MMM := mutableIdentity (ZZ,n);
     for rrr from 0 to (n-1) do if ( rrr != (i-1)) then MMM_(rrr,rrr) = 0;
     matrix MMM
     )

NP = method ()
NP(Ideal) := Polyhedron => (I) -> (
     -- ddd := sub(dim ring I,ZZ);
     convexHull (mon2Exp I) + posHull (id_(ZZ^(sub(dim ring I,ZZ))))     
     )

---- monomial j-multiplicity
---- Dependency: loadPackage "Polyhedra", pryF, isBddFacet, mon2Exp, NP 
monjMult = method ()
monjMult(Ideal) := ZZ => (III) -> (
     if ((isMonomialIdeal III) == false) then (print "The input is not a monomial ideal", break);     
     II := III; --- unnecssary one one could change every II to III     
     ddd := sub(dim ring II,ZZ);
     PPP := convexHull (mon2Exp II) + posHull (id_(ZZ^(ddd)));
     MMM := halfspaces PPP;
     MMMm := (MMM)_0;
     MMMv := (MMM)_1;
     r := rank target MMMm;  --- # of rows
     s := rank source MMMm;  --- # of columns
     monj := 0_(QQ);
     for ppp from 0 to (r-1) do ( 
	 if (isBddFacet(ppp, MMMm) != 0) then (
	     halfSpace := intersection (MMMm, MMMv, MMMm^{ppp}, MMMv^{ppp});
	     monj = monj + (ddd)! * (volume convexHull pyrF (vertices halfSpace)); 
	     ); 
	 );
     sub(monj, ZZ)
)


multSeq = method ()
multSeq Ideal := List => (I) -> (
      for i from 0 to (dim ring I) list cSubi (i,I)
      )


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
     if I.cache#?"gr_mGr_I" then return I.cache#"gr_mGr_I";
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
     -- T := R2 / (mG1R2 + K2R2); 
     -- modification of T to have the right degrees
     I.cache#"gr_mGr_I" = first flattenRing (R2 / (mG1R2 + K2R2))
     --minimalPresentation T
     -- hilbertSeries oo
)

egrGr = method ()
egrGr (Ideal) := ZZ => (I) -> (
     A := grGr I;
     B := newRing (A, Degrees => splice{ (#gens A) : 1});
     degree B
     )

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

--------------
--------------
--------------
--------------
--------------
-- Patching
hilbertSamuelMultiplicity := (I)-> ( -- computes e(m, R/I)
    R := (ring I)/I;
    maxR := ideal vars R;
    if (dim R == 0) then return (degree comodule primaryComponent (I, maxR)); -- finite colength case; 
    genLinComMat := (gens maxR) * random (ZZ^(numgens maxR), ZZ^(dim R));
    colInGenLinComMat := numcols genLinComMat;
    genRedIdeal := ideal (0_R);
    if (dim R == 1) then genRedIdeal = saturate (ideal (0_R), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    -- the case of dim R/I >= 2
        else genRedIdeal = saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat;     
    -- if (codim genRedIdeal != dim R) then return "Elements chosen are not general. Try again."; 
    -- use ring I;
    -- the length method doesn't handle the non-graded case, but the degree function does.
    degree comodule primaryComponent (genRedIdeal,maxR) 
)

getGenElts = method(Options => {symbol minTerms => 1, symbol numCandidates => 10})
getGenElts (Ideal, ZZ) := List => opts -> (I, n) -> (
    G := flatten entries mingens I; -- I_*;
    R := ring I;
    J := ideal(0_R);
    result := {};
    for i from 1 to n do (
        foundNext := false;
        t := opts.minTerms;
        while not foundNext and t <= #G do (
            if debugLevel > 0 then print("Trying" | (if t > 1 then " sums of " | toString(t) else "") | " generators of I");
            cands := if t < 3 then random(subsets(G, t)/sum) 
                else unique apply(opts.numCandidates, i -> (matrix{randomSubset(G, t)} *random(R^t, R^1))_(0,0));
            for c in cands do (
                if codim(saturate(J, I) + ideal c) == i then (
                    result = append(result, c);
                    if member(c, G) then G = delete(c, G);
                    foundNext = true;
                    break;
                );
            );
            t = t+1;
        );
        if foundNext then J = ideal result else error "Could not find general element";
    );
    result
)

multiplicitySequence = method(Options => options getGenElts ++ {Strategy => "DoubleSat"})
multiplicitySequence (ZZ, Ideal) := ZZ => opts -> (j, I) -> (
    I = trim I;
    c := codim I; -- dim R - dim I;
    l := analyticSpread I;
    if j < c then ( print "Requested index is less than codimension"; return; );
    if j > l then ( print "Requested index is greater than analytic spread"; return; );
    if not I.cache#?"colonIdeals" then (
        (G, numTries) := ({}, 0);
        if debugLevel > 0 then print "Finding general elements...";
        while #G < l and numTries < 10 do (
            try ( G = getGenElts(I, l, minTerms  => numgens I); );
            numTries = numTries + 1;
        );
        if #G < l then error "Could not find general elements. Consider running this function again, possibly with a higher value of minTerms (e.g. minTerms => 3)";
        if debugLevel > 0 then print "Finding colon ideals...";
	candidates := apply(toList(max{c,2}..l), i -> (i, saturate(ideal(G_{0..i-2}), I) + ideal(G#(i-1))));
	if c == 1 then candidates = prepend((1,ideal((ring I)_0-(ring I)_0)+ideal(G#(0))),candidates);
--        candidates := apply(toList(c..l), i -> (i, saturate(ideal(G_{0..i-2}), I) + ideal(G#(i-1))));
        I.cache#"colonIdeals" = candidates;
    );
    colonIdeals := I.cache#"colonIdeals";
    idealIn21 := ((select (colonIdeals, i-> i_0 == j))_0)_1;
    if debugLevel > 0 then print "Computing minimal primes...";
    if isHomogeneous I then (
        K := if opts.Strategy == "DoubleSat" then (
            saturate(idealIn21, intersect minimalPrimes(idealIn21+I))
        ) else if opts.Strategy == "FullColon" then (
            primesIn21 := select(minimalPrimes(idealIn21), p -> not isSubset(I, p));
            if #primesIn21 > 0 then intersect primesIn21 else ideal(0_(ring I)) -- todo: check
        );
        if debugLevel > 0 then print "Computing saturation...";
        J := if K == 0 then idealIn21 else saturate(idealIn21, K); -- todo: check
        if debugLevel > 0 then print "Finding degree...";
        degree J
    ) else (
        minPrimesOfColonIdeals := apply(colonIdeals, s -> (s#0, minimalPrimes(I+s#1)));
        primesIn21 = ((select(minPrimesOfColonIdeals, i-> i_0 == j))_0)_1;
        if debugLevel > 0 then print "Finding degree via general elements...";
        sum apply(primesIn21, p -> hilbertSamuelMultiplicity localize(idealIn21, p))
    )
)
multiplicitySequence Ideal := Sequence => opts -> I -> apply(codim I..analyticSpread I, j -> multiplicitySequence(j, I, opts))

indexedMultiplicitySequence = method(Options => options multiplicitySequence)
indexedMultiplicitySequence Ideal := Sequence => opts -> I -> hashTable toList apply(codim I..analyticSpread I, j -> {j, multiplicitySequence(j, I, opts)})

randomSubset = method()
randomSubset (List, ZZ) := List => (L, k) -> (
    i := random(#L);
    if k == 1 then {L#i} else {L#i} | randomSubset(L_(delete(i, toList(0..<#L))), k-1)
)
--------------
--------------
--------------
--------------

end

-- Documentation

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

-- Examples
(m,n)=(6,6)
R = QQ[x_0..x_(n-1),y_0..y_(m-1)]
I = ideal flatten table(n,m,(i,j)->x_i*y_j)
J1 = ideal apply(m,k-> sum(min(m-k,n),i->x_i*y_(k+i)));
J2 = ideal apply(1..(n-1),k-> sum(min(n-k,m),i->x_(k+i)*y_i));
J= J1+J2
elapsedTime isReduction (I,J)
elapsedTime grGr I

end
loadPackage "MultiplicitySequence" --("MultiplicitySequence", Reload=>true)
needsPackage "MinimalPrimes"
installMinprimes()

R = QQ[x,y]
I = ideal "x2y,xy2" -- jmult 3 
monjMult I
jmult I
indexedMultiplicitySequence I

-- Monomial ideal, not generated in single degree
R = QQ[x,y,z]
I = ideal(x^2*y^2, y*z^2, x*z^2, z^3) -- Weird minimal presentation with grGr I
getGenElts(I, l, minTerms => 3)

-- Aug 21, 2020
R = QQ[x_1..x_8]
M = genericMatrix(R,4,2)
I = minors(2, M)

R = ZZ/31[x_1..x_10]; M = genericMatrix(R,5,2)
R = QQ[x_1..x_9]; M = genericMatrix(R,3,3)

--
R = QQ[x,y,z]
I = ideal"xyz2"*ideal(z^3, y*z^2, x*z^2, x^2*y^2)

R = QQ[x,y,z]
I = ideal(z^3,  y*z^2, x*z^2)

R = QQ[x,y,z]
I = ideal(x*y^3*z^3, x^3*y)

R = QQ[x,y,z]
I = ideal"xyz3, x2y2z, xy2z2, xy2z4x"

R = QQ[x,y,z]
I = ideal" x4y2,  x2yz3"

