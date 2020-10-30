newPackage(
    "MultiplicitySequence",
    Version => "0.1", 
    Date => "Oct. 14, 2020",
    Authors => {
        {Name => "Justin Chen", 
            Email => "justin.chen@math.gatech.edu"
        },
        {Name => "Youngsu Kim", 
            Email => "youngsu.kim@csusb.edu"
        },
        {Name => "Jonathan Montaño", 
            Email => "jmon@nmsu.edu"
        }
    },
    Headline => "computing the multiplicity sequence of an ideal",
    DebuggingMode => true,
    PackageExports => {
        "ReesAlgebra", 
        "TangentCone", 
        "OldPolyhedra",
        "Normaliz",
        "PrimaryDecomposition",
        "MinimalPrimes"
    },
	Reload => "true"
)

export {
    "jmult",
    "grGr",
    "cSubi",
    -- "multiplicitySequence",
    "NP",
    "monReduction",
    "monjMult",
    "gHilb",
    "hilbertSamuelMultiplicity",
    "getGenElts",
    "multiplicitySequence",
    "randomSubset",
    "numCandidates",
    "minTerms",
    "monAnalyticSpread"
 }

installMinprimes() -- for MinimalPrimes.m2

gHilb = method()
gHilb (ZZ, MonomialIdeal) := Module => (n, I) -> (
    R := ring I;
    Inp1 := sub((intclMonIdeal trim I^(n+1))_0 , R );
    In := sub((intclMonIdeal trim I^n)_0, R  );
    HH^0( (In / Inp1) )
)
gHilb (ZZ, Ideal) := Module => (n, I) -> ( 
    J := monomialIdeal I;
    if J != I then error "Expected a monomial ideal";
    gHilb (n, J)
)

---- extract the exponent of a monomial ideal
mon2Exp = method()
mon2Exp MonomialIdeal := Matrix => I -> (
    -- J := trim I;
    -- n := numgens J;
    -- transpose (matrix flatten apply( for i from 0 to (n - 1) list J_i, exponents ))
    transpose matrix flatten apply(I_*, exponents)
)
mon2Exp Ideal := Matrix => I -> (
    J := monomialIdeal I;
    if J != I then error "Expected a monomial ideal";
    mon2Exp monomialIdeal I
)

monReduction = method()
monReduction MonomialIdeal := MonomialIdeal => I -> (
    -- R := ring I;
    -- P := NP (I);
    -- M := vertices P;
    -- s := rank source M;
    -- J := ideal (0_R);
    -- for i from 0 to (s-1) do J = J + ideal R_((entries transpose M_{i})_0);
    -- trim J
    sum(entries transpose sub(vertices NP I, ZZ), e -> monomialIdeal((ring I)_e))
)
monReduction Ideal := MonomialIdeal => I -> (
    J := monomialIdeal I;
    if J != I then error "Expected a monomial ideal";
    monReduction J
)

--- from a matrix M extract the rows where all the entries are not zero
isBddFacet := (n, M) -> (
    --- r := rank target M; --- # of rows
    s := rank source M; --- # of columns
    mutableM := mutableIdentity (ZZ,s); --- row as a vector
    for i from 0 to (s - 1) do (mutableM_(i,i) = M_(n,i));
    det mutableM != 0 --- No if 0, Yes otherwise
)

pyrF := M -> M | transpose map(ZZ^1, rank target M, 0)

---- gives a matrix of the from where all the entries are zero except one spot i,i
box := (i,n) -> (
    M := mutableIdentity (ZZ,n);
    for r from 0 to (n-1) do if ( r != (i-1)) then M_(r,r) = 0;
    matrix M
)

NP = method()
NP MonomialIdeal := Polyhedron => I -> (
    -- ddd := sub(dim ring I,ZZ);
    convexHull (mon2Exp I) + posHull (id_(ZZ^(sub(dim ring I,ZZ))))     
)
NP Ideal := Polyhedron => I -> (
    J := monomialIdeal I;
    if J != I then error "Expected a monomial ideal";
    NP J
)

monAnalyticSpread = method()
monAnalyticSpread MonomialIdeal := MonomialIdeal => I -> (
    d := dim ring I;
    P := NP(I);
    M := halfspaces P;
    Mm := M_0;
    Mv := M_1;
    r := rank target Mm;  --- # of rows
    -- s := rank source Mm;  --- # of columns
    monAS := 0;
    for p from 0 to r-1 do (
        face := intersection (Mm, Mv, Mm^{p}, Mv^{p});
        monAS = max(monAS,dim convexHull vertices face);      
    );
    sub(monAS, ZZ)+1
)
monAnalyticSpread Ideal := MonomialIdeal => I -> (
    J := monomialIdeal I;
    if J != I then error "Expected a monomial ideal";
    monAnalyticSpread J
)


---- monomial j-multiplicity
---- Dependency: loadPackage "Polyhedra", pryF, isBddFacet, mon2Exp, NP 
monjMult = method()
monjMult MonomialIdeal := ZZ => I -> (
    -- if ((isMonomialIdeal III) == false) then (print "The input is not a monomial ideal", break);
    -- II := III; --- unnecssary one one could change every II to III
    d := dim ring I;
    P := NP(I);
    M := halfspaces P;
    Mm := M_0;
    Mv := M_1;
    r := rank target Mm;  --- # of rows
    -- s := rank source Mm;  --- # of columns
    monj := 0;
    for p from 0 to r-1 do (
    if isBddFacet(p, Mm) then (
        face := intersection (Mm, Mv, Mm^{p}, Mv^{p});
        monj = monj + (d!)*(volume convexHull pyrF(vertices face));
        );
    );
    sub(monj, ZZ)
)
monjMult Ideal := ZZ => I -> (
    J := monomialIdeal I;
    if J != I then error "Expected a monomial ideal";
    monjMult J
)

-- multSeq = method()
-- multSeq Ideal := List => I -> (
    -- hashTable for i from codim I to analyticSpread I list (i, cSubi (i,I))
-- )

-- lengthij, length10ij, length11ij do not seem to be used elsewhere, and have been commented out
-- lengthij = method()
-- lengthij (ZZ, ZZ, Ideal) := ZZ => (i,j,I) -> (
    -- R := ring I;
    -- m := ideal vars R;
    -- M := (trim (m^i*I^j + I^(j+1)) ) / (  trim (m^(i+1)*I^j + I^(j+1)) );
    -- degree (M^1)
-- )

-- length10ij = method()
-- length10ij (ZZ, ZZ, Ideal) := ZZ => (i,j,I) -> (
    -- R := ring I;
    -- m := ideal vars R;
    -- M := (trim (I^j ) ) / (  trim (m^(i+1)*I^j + I^(j+1)) );
    -- degree (M^1)
-- )

-- length11ij = method()
-- length11ij (ZZ,ZZ, Ideal) := ZZ => (i,j,I) -> (
    -- L := 0;
    -- for k from 0 to j do (L = L + length10ij(i,k,I));
    -- sub (L, ZZ)
-- )

cSubi = method()
cSubi (ZZ, Ideal) := ZZ => (i,I) -> (
    G := grGr I;
    if not G.cache#?"hilbertSeries" then G.cache#"hilbertSeries" = hilbertSeries(G, Reduce => true);
    hS := G.cache#"hilbertSeries";
    -- hilbertS := reduceHilbert hilbertSeries G;
    poinP := numerator hS;
    dPoinP := denominator hS;
    A := ring poinP;
    -- B := newRing (A, Degrees => {{1,0}, {0,1},{0,0}});
    B := newRing (A, Degrees => {{1,0}, {0,1}});
    use B;
    topP := sub (poinP, B);
    botP := value toString dPoinP;
    firVar := (ultimate (flatten, entries (vars B)_{0}))_0;
    secVar := (ultimate (flatten, entries (vars B)_{1}))_0;
    powerFirVar := (degree botP)_0;     
    powerSecVar := (degree botP)_1;     
    d := dim ring I;
    a := powerFirVar - (d - i);
    b := powerSecVar - i;
    c := topP;
    for i from 1 to a do (c = diff( firVar, c));
    c = sub (c, firVar => 1);
    for i from 1 to b do (c = diff (secVar, c));
    c = sub (c, secVar => 1); 
    c = c*(-1)^(a+b);
    if (c <= 0 or a < 0 or b < 0) then 0 else (sub(c,ZZ) // (a! * b!))
)

grGr = method()
grGr Ideal := Ring => I -> (
    if I.cache#?"gr_mGr_I" then I.cache#"gr_mGr_I" else I.cache#"gr_mGr_I" = (
        G1 := normalCone(I, Variable => "v");
        G2 := normalCone(sub(ideal gens ring I, G1), Variable => "u");
        newRing(minimalPresentation G2, Degrees => splice({numgens ring I : {1,0}} | {numgens G1 : {0,1}}))
        -- R := ring I;
        -- m := ideal vars R;
        -- n := numgens I;
        -- d := numgens m;
        -- if (I == m) then print "I is m" else assert ( (ideal (1_R) == I:m) == false ); -- To check if the ideal is inside of the maximal ideal m
        -- K1 := reesIdeal I; 
        -- reesRingI := ring K1;
        -- v := "v";
        -- R1 := (R) ( monoid[ VariableBaseName => v, Variables => (n)]); -- The source of the first Rees ring with the right ordering
        -- phi1 := map(R1, reesRingI, vars R1);
        -- IR1 := phi1 sub(I, reesRingI);
        -- K1R1 := phi1 K1;
        -- G1 := R1 / (IR1 + K1R1);
        -- mG1 := sub (phi1 sub(m, reesRingI), G1);
        -- K2 := reesIdeal mG1;
        -- reesRingm := ring K2;
        -- u := "u";
        -- R2 := (G1) ( monoid[VariableBaseName => u, Variables => (d)]);
        -- phi2 := map(R2, reesRingm, vars R2);
        -- mG1R2 := phi2 sub(mG1, reesRingm);
        -- K2R2 := phi2 K2;
        -- first flattenRing (R2 / (mG1R2 + K2R2))
        -- T := R2 / (mG1R2 + K2R2); 
        -- modification of T to have the right degrees
        --minimalPresentation T
        -- hilbertSeries oo
    )
)

egrGr = method()
egrGr Ideal := ZZ => I -> (
    A := grGr I;
    B := newRing (A, Degrees => splice{ (#gens A) : 1});
    degree B
)

jmult = method()
jmult Ideal := ZZ => I -> (
    if ((isIdeal I) == false) then (print "input is not an ideal", break);
    R := ring I;
    r := rank source vars R;
    G := gens I;
    g := rank source G;
    M := random(R^r,R^g)*transpose G;
    J := ideal(submatrix(M,{0..r-2},));
    UI := saturate(J,I) + ideal(submatrix(M,{r-1..r-1},));
    N := monoid[Variables=>r, MonomialOrder=>{Weights=>{-1,-1},RevLex},Global=>false];
--        L := leadTerm gb UI;
    L := tangentCone UI;
    S := (ZZ/101) N;
    f := map(S,R,vars S);
    C := S/f(L);
--        dim (R/ ideal(submatrix(M,{0..r-1},)))
    if dim C == 0 then length(C^1) else print "analytic spread not maximal"	     
)


----------------------------------------------------------------------
-- Patching


hilbertSamuelMultiplicity := I -> ( -- computes e(m, R/I) (need to fix)
    R := (ring I)/I;
    k := coefficientRing ring I;
    maxR := ideal vars R;
    if (dim R == 0) then return (degree comodule primaryComponent (I, maxR)); -- finite colength case; 
    genLinComMat := (gens maxR) * random (k^(numgens maxR), k^(dim R));
    colInGenLinComMat := numcols genLinComMat;
    genRedIdeal := ideal (0_R);
    if (dim R == 1) then genRedIdeal = saturate (ideal (0_R), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    -- the case of dim R/I >= 2
        else genRedIdeal = saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat;     
    -- if (codim genRedIdeal != dim R) then return "Elements chosen are not general. Try again."; 
    -- use ring I;
    -- the length method doesn't handle the non-graded case, but the degree function does.
    degree comodule primaryComponent (genRedIdeal,maxR) -- alternatively normalCone?
)

getGenElts = method(Options => {symbol minTerms => -1, symbol numCandidates => 3})
getGenElts (Ideal, ZZ) := List => opts -> (I, n) -> (
    G := flatten entries mingens I; -- I_*;
    R := ring I;
    J := ideal(0_R);
    result := {};
    for i from 1 to n do (
        foundNext := false;
        t := if opts.minTerms < 0 then #G else opts.minTerms;
        while not foundNext and t <= #G do (
            if debugLevel > 0 then print("Trying" | (if t > 1 then " sums of " | toString(t) else "") | " generators of I");
            cands := unique apply(opts.numCandidates, i -> (matrix{randomSubset(G, t)} *random(R^t, R^1))_(0,0));
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
        if foundNext then J = ideal result else error "Could not find general element. Consider running this function again, e.g. with a higher value of minTerms";
    );
    result
)

multiplicitySequence = method(Options => options getGenElts ++ {Strategy => "grGr"})
multiplicitySequence (ZZ, Ideal) := ZZ => opts -> (j, I) -> (
    -- I = trim I;
    c := codim I; -- dim R - dim I;
    l := analyticSpread I;
    if j < c then ( print "Requested index is less than codimension"; return 0; );
    if j > l then ( print "Requested index is greater than analytic spread"; return 0; );
    if opts.Strategy == "genElts" then (
        if not I.cache#?"colonIdeals" then I.cache#"colonIdeals" = new MutableHashTable;
        idealIn21 := if I.cache#"colonIdeals"#?j then I.cache#"colonIdeals"#j else (
            if not I.cache#?"genElts" or #I.cache#"genElts" < j then I.cache#"genElts" = (
                if debugLevel > 0 then print "Finding general elements...";
                getGenElts(I, j, minTerms => opts.minTerms)
            );
            G := I.cache#"genElts";
            if debugLevel > 0 then print "Finding colon ideal...";
            I.cache#"colonIdeals"#j = saturate(sub(ideal(G_{0..j-2}), ring I), I) + ideal(G#(j-1))
        );
        -- if dim(idealIn21 + I) < dim R - j then return 0;
        if debugLevel > 0 then print "Computing minimal primes...";
        primesIn21 := select(minimalPrimes(idealIn21), p -> not isSubset(I, p));
        K := if #primesIn21 > 0 then intersect primesIn21 else ideal(0_(ring I));
        if debugLevel > 0 then print "Computing saturation...";
        J := if K == 0 then idealIn21 else saturate(idealIn21, K);
        if debugLevel > 0 then print "Finding degree...";
        -- if isHomogeneous J then degree J else hilbertSamuelMultiplicity J
        -- degree(if isHomogeneous J then J else ( A := (ring J)/J; normalCone ideal gens A ))
        degree(if isHomogeneous J then J else tangentCone J)
    ) else cSubi(j, I)
)
multiplicitySequence Ideal := Sequence => opts -> I -> hashTable toList apply(codim I..analyticSpread I, j -> {j, multiplicitySequence(j, I, opts)})

randomSubset = method()
randomSubset (List, ZZ) := List => (L, k) -> (
    i := random(#L);
    if k == 1 then {L#i} else {L#i} | randomSubset(L_(delete(i, toList(0..<#L))), k-1)
)

--------------------------------------------------------

TEST ///
R = QQ[x,y,z]
I = ideal "x4z, y3z"
assert(multiplicitySequence I === hashTable {(1, 1), (2, 15)})
///

TEST ///
R = QQ[x,y,z,t]
I = ideal "x3,y4,z5" * ideal "t"
assert(multiplicitySequence I === hashTable {(1, 1), (2, 3), (3, 72)})
///

TEST ///
R = QQ[x_1..x_8]
M = genericMatrix(R,4,2)
I = minors(2, M)
assert(multiplicitySequence I === hashTable {(3, 4), (4, 6), (5, 4)})
///

TEST ///
R = QQ[x_1..x_9]
M = genericMatrix(R,3,3)
I = minors(2, M)
assert(multiplicitySequence I === hashTable {(4, 6), (5, 12), (6, 12), (7, 6), (8, 3), (9, 2)})
///

-- Documentation

beginDocumentation()

doc ///
    Key
        MultiplicitySequence
    Headline
        multiplicity sequences of ideals
    Description
        Text
            This package contains various functions to compute the multiplicity sequence of an ideal.
        Text
            The package contains the method "jmult" which computes the j-multiplicity of an ideal using Theorem 3.6 in Nishida-Ulrich (Computing j-multiplicities, J. of Alg 2010). 
            The function jmult is based on the code written by H.Schenck and J. Validashti.	  
        Text
            The function monjMult comuputes the j-multiplicity for an monomial ideal by computing the volume of a pyramid. This is a result of J. Jeffries and J. Montano, The $j$-Multiplicity of Monomial Ideals, to appear in Math. Res. Letters.
        Text
            The author thanks D. Eisenbud, D. Grayson, and M. Stillman for organizing a Macaulay2 day during the special year in commutative algebra 2012-2013 at MSRI where he learned how to write a package.
///

doc ///
    Key
        jmult
        (jmult, Ideal)
    Headline
        the j-multiplicity
    Usage
        jmult(I)
    Inputs
        I:Ideal
    Outputs
        :ZZ
            the j-multiplicity of I
    Description
        Text
        Example
            R = QQ[x,y]
            I = ideal"x2,xy"
            jmult I
    SeeAlso
///

doc ///
    Key
        grGr
        (grGr, Ideal)
    Headline
        the bigraded ring Gr_m(Gr_I(R))
    Usage
        grGr(I)
    Inputs
        I:Ideal
    Outputs
        :Ring
            The bigraded ring Gr_m(Gr_I(R)), presented as a quotient of a bigraded polynomial ring with variables names u and v.
    Description
        Text
        Example
            R = QQ[x,y]
            I = ideal"x2,xy"
            A = grGr I
            describe A
            hilbertSeries A
///

doc ///
    Key
        cSubi
        (cSubi, ZZ, Ideal)
    Headline
        the components of the multiplicity sequence, via iterated associated graded ring
    Usage
        cSubi(i, I)
    Inputs
        i:ZZ
        I:Ideal
    Outputs
        :ZZ
            the ith term of the multiplicity sequence of I
    Description
        Text
        Example
            R = QQ[x,y]
            I = ideal"x2,xy"
            cSubi(0,I)
            jmult I
    SeeAlso
///

doc ///
    Key
        multiplicitySequence
        (multiplicitySequence, Ideal)
        [multiplicitySequence, minTerms]
        [multiplicitySequence, numCandidates]
        [multiplicitySequence, Strategy]
    Headline
        the multiplicity sequence
    Usage
        multiplicitySequence I
    Inputs
        I:Ideal
    Outputs
        :HashTable
            The multiplicity sequence $\{c_i\}$, where $codim I \le$ $i  \le$  $\ell(I)$.
    Description
        Text
        Example
            R = QQ[x,y]
            I = ideal"x2,xy"
            multiplicitySequence I
    SeeAlso
///

doc ///
    Key
        monjMult
        (monjMult, Ideal)
        (monjMult, MonomialIdeal)
    Headline
        j-multiplicity of a monomial ideal
    Usage
        monjMult I
    Inputs
        I:Ideal
    Outputs
        :ZZ
            the j-multiplicity of a monomial ideal.
    Description
        Text
        Example
            R = QQ[x,y,z]
            I = ideal"x6,y6,z6,x2yz,xy2z,xyz2"
            monjMult (I)
    SeeAlso
///

doc ///
    Key
        NP
        (NP, Ideal)
	--(NP, MonomialIdeal)
    Headline
        the Newton-Polyhedron of a mominial ideal
    Usage
        NP(I)
    Inputs
        I:Ideal
    Outputs
        :Polyhedron
            The Newton-Polyhedron of the monomial ideal I
    Description
        Text
        Example
            R = QQ[x,y]
            I = ideal"x2,xy"
            NP I
///

doc ///
    Key
        monReduction
        (monReduction, Ideal)
	(monReduction, MonomialIdeal)
    Headline
        The minimal monomial reduction of a monomial ideal
    Usage
        monReduction(I)
    Inputs
        I:MonomialIdeal
    Outputs
        :MonomialIdeal
            The minimal monomial of reduction of a monomial ideal I
    Description
        Text
        Example
            R = QQ[x,y]
            monReduction (ideal vars R)^2
///

doc ///
    Key
        gHilb
	(gHilb, ZZ, MonomialIdeal)
	(gHilb, ZZ, Ideal)
    Headline
        The length of the module ??
    Usage
        gHilb(n,I)
    Inputs
        n:ZZ
	I:MonomialIdeal
    Outputs
        :ZZ
            The length of the module ??
    Description
        Text
        Example
            R = QQ[x,y]
            I = ideal "x2,y2"
	    gHilb(2,I)
///

undocumented {
    --"NP",
    --"monReduction",
    --"gHilb",
    "hilbertSamuelMultiplicity",
    "getGenElts",
    "randomSubset",
    "numCandidates",
    "minTerms",
     "monAnaltyticSpread"
 }

end--

restart
loadPackage "MultiplicitySequence" --("MultiplicitySequence", Reload=>true)
installPackage("MultiplicitySequence", RemakeAllDocumentation => true)
uninstallPackage "MultiplicitySequence"
check "MultiplicitySequence"
needsPackage "MinimalPrimes"
installMinprimes()
debugLevel = 2

elapsedTime multiplicitySequence I
elapsedTime multiplicitySequence(codim I, I)
elapsedTime multiplicitySequence(codim I+1, I)
elapsedTime multiplicitySequence(analyticSpread I, I)
elapsedTime multiplicitySequence I
multiplicitySequence(I, Strategy => "grGr") === multiplicitySequence(I, Strategy => "genElts")

R = QQ[x,y]
I = ideal "x2y,xy2"
monjMult I
jmult I -- jmult 3

-- Monomial ideal, not generated in single degree
R = QQ[x,y,z]
I = ideal(x^2*y^2, y*z^2, x*z^2, z^3) -- Weird minimal presentation with grGr I
getGenElts(I, l, minTerms => 3)

-- Aug 21, 2020
x = symbol x
R = ZZ/31[x_1..x_10]; M = genericMatrix(R,5,2)
R = QQ[x_1..x_9]; M = genericMatrix(R,3,3);
I = minors(2, M)

-- Ferrers ideals
(m,n)=(6,6)
R = QQ[x_0..x_(n-1),y_0..y_(m-1)]
I = ideal flatten table(n,m,(i,j)->x_i*y_j)
J1 = ideal apply(m,k-> sum(min(m-k,n),i->x_i*y_(k+i)));
J2 = ideal apply(1..(n-1),k-> sum(min(n-k,m),i->x_(k+i)*y_i));
J= J1+J2
elapsedTime isReduction (I,J)
elapsedTime grGr I;
elapsedTime cSubi(codim I, I)
elapsedTime multiplicitySequence I
 
--
R = QQ[x,y,z]
I = ideal"xyz2"*ideal(z^3, y*z^2, x*z^2, x^2*y^2)
I = ideal(z^3,  y*z^2, x*z^2)
I = ideal(x*y^3*z^3, x^3*y)
I = ideal"xyz3, x2y2z, xy2z2, xy2z4x"
I = ideal" x4y2,  x2yz3"
I = ideal "x4z, y3z"
I = ideal "xz, yz"

I = ideal "x,y,z"

(monAnalyticSpread I, analyticSpread I)

S = R/I
J = ideal z
multiplicitySequence(1, J)
