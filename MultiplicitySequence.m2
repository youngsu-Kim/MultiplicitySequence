newPackage(
    "MultiplicitySequence",
    Version => "0.8.1", 
    Date => "Oct 9, 2023",
    Authors => {
        {Name => "Justin Chen", 
            Email => "jchen646@gatech.edu"
        },
        {Name => "Youngsu Kim", 
            Email => "youngsu.kim@csusb.edu"
        },
        {Name => "Jonathan Montaño", 
            Email => "montano@asu.edu"
        }
    },
    Headline => "computing the multiplicity sequence of an ideal",
    Keywords => {"Commutative Algebra"},
    AuxiliaryFiles => false,
    Configuration => {
        "AlignCenter" => true
    },
    DebuggingMode => false,
    PackageImports => {
        "ReesAlgebra",
        "OldPolyhedra"
    }
)

export {
    "tangentNormalCone",
    "PrimaryGradingIdeal",
    "multiplicitySequence",
    "HilbertSequence",
    "hilbertSequence",
    -- "getGeneralElements",
    "MinTerms",
    "NumCandidates",
    "DoSaturate",
    "jMultiplicity",
    "monomialReduction",
    "newtonPolyhedron",
    "grGr",
    "jMult",
    "NP",
    "monReduction"
 }

-- Imported functions
importFrom("TangentCone", {"tangentCone"});
importFrom("MinimalPrimes", {"minimalPrimes"})
importFrom("K3Carpets", {"irrelevantIdeal"});

randomSubset = method()
randomSubset (VisibleList, ZZ) := List => (L, k) -> (
    if k <= 0 or k > #L then return {};    
    K := random(L); 
    K_{0..(k-1)}
)

getGeneralElements = method(Options => {symbol MinTerms => -1, symbol NumCandidates => 3})
getGeneralElements (Ideal, ZZ) := List => opts -> (I, n) -> (
    G := flatten entries mingens I; -- I_*;
    R := ring I;
    J := ideal(0_R);
    result := new MutableHashTable;
    for i from 1 to n do (
        foundNext := false;
        t := if opts.MinTerms < 0 then #G else opts.MinTerms;
        while not foundNext and t <= #G do (
            if debugLevel > 0 then print("Trying" | (if t > 1 then " sums of " | toString(t) else "") | " generators of I");
            cands := unique apply(opts.NumCandidates, j -> (matrix{randomSubset(G, t)} *random(R^t, R^1))_(0,0));
            for c in cands do (
                if codim(saturate(J, I) + ideal c) == i then (
                    result#(i-1) = c;
                    if member(c, G) then G = delete(c, G);
                    foundNext = true;
                    break;
                );
            );
            t = t+1;
        );
        if foundNext then J = ideal values result else error "Could not find general element. Consider running this function again, e.g. with a higher value of NumCandidates";
    );
    apply(n, i -> result#i)
)

-- computes the bigraded associated graded algebra with respect to m and I
tangentNormalCone = method(Options => {Variables => {"u", "v"}, PrimaryGradingIdeal => null})
tangentNormalCone Ideal := Ring => opts -> I -> (
    if any(gens ring I, v -> instance(baseName v, IndexedVariable) and member(toString first baseName v, opts.Variables)) then error "Variable name conflict - please choose Variables distinct from any variable name in the ring";
    Q := if opts.PrimaryGradingIdeal === null then ideal gens ring I else opts.PrimaryGradingIdeal;
    if minimalPrimes Q != {ideal gens ring I} then error "Expected PrimaryGradingIdeal to be primary to the maximal ideal";
    if I.cache#?{"Gr_QGr_I",Q} then I.cache#{"Gr_QGr_I",Q} else I.cache#{"Gr_QGr_I",Q} = (
        G1 := normalCone(I, Variable => opts.Variables#1);
        G2 := minimalPresentation normalCone(sub(Q, G1), Variable => opts.Variables#0);
        newVars := apply(opts.Variables, name -> select(gens G2, g -> instance(baseName g, IndexedVariable) and toString first baseName g == name));
        newRing(G2, Degrees => splice({#newVars#0 : {1,0}} | {#newVars#1 : {0,1}} | {#gens G2 - #flatten newVars : {0,0}}))
    )
)

HilbertSequence = new Type of HashTable
HilbertSequence.synonym = "Hilbert sequence"

globalAssignment HilbertSequence
net HilbertSequence := H -> (
    if #first keys H =!= 2 then return net hashTable pairs H;
    d := max(keys H /sum);
    A := matrix table(d+1, d+1, (i, j) -> if H#?{d-(i+j), j} then H#{d-(i+j), j} else 0);
    if not (options MultiplicitySequence).Configuration#"AlignCenter" then A = matrix table(d+1, d+1, (i, j) -> if i > j then 0 else (A_(j-i))_i);
    A = matrix{{0..d}} || A;
    N := net A;
    s0 := replace("\\|", " ", first unstack N);
    s := "+" | fold(apply(length s0 - 2, i -> "-"), (a,b) -> a | b);
    c := stack apply(d+3, i -> (if i < 2 then "" else toString (d-(i-2))) | " ");
    c | stack({s0, s} | apply(drop(unstack N, 1), t -> replace(" 0", " .", substring(0, #t-1, t))))
)

hilbertSequence = method(Options => {symbol DoSaturate => false})
hilbertSequence Module := HilbertSequence => opts -> M -> (
    if opts.DoSaturate then M = M/saturate(0*M, irrelevantIdeal ring M);
    HS := hilbertSeries(M, Reduce => true);
    q := value numerator HS;
    coordChange := map(ring q, ring q, matrix{{#gens ring q:1}} - vars ring q);
    s := first exponents coordChange value denominator HS;
    b := select(listForm coordChange q, p -> all(#s, i -> p#0#i <= s#i));
    new HilbertSequence from hashTable apply(b, p -> (s - p#0, p#1))
)
hilbertSequence Ring := HilbertSequence => opts -> R -> hilbertSequence(R^1, opts)
hilbertSequence Ideal := HilbertSequence => opts -> I -> hilbertSequence(comodule I, opts)

-- hilbertPolynomial = method(Options => {Projective => false}) -- should be a hook?
-- hilbertPolynomial Module := RingElement => o -> M -> ( -- TODO: fix
    -- if not isHomogeneous M then error "expected a (multi-)homogeneous module";
    -- R := ring M;
    -- n := degreeLength R;
    -- if n > 1 then (
        -- i := getSymbol "i";
        -- S := QQ(monoid[i_1..i_n]);
        -- b := hilbertSequence M;
        -- sum(pairs b, p -> p#1*product(#gens S, j -> binomial(S_j+p#0#j, p#0#j)))
    -- ) else Core$hilbertPolynomial(M, o)
-- )
-- hilbertPolynomial Ideal := RingElement => o -> I -> hilbertPolynomial(comodule I, o)
-- hilbertPolynomial Ring := RingElement => o -> R -> hilbertPolynomial(R^1, o)

-- This is the main method. It computes the multiplicity sequence of an ideal using one of two strategies: either bivariate Hilbert series (default), or general elements.
multiplicitySequence = method(Options => options getGeneralElements ++ options hilbertSequence ++ {Strategy => "tangentNormalCone"})
multiplicitySequence Ideal := HashTable => opts -> I -> (
    hashTable if opts.Strategy =!= "generalElements" then (
        H := hilbertSequence(tangentNormalCone I, DoSaturate => opts.DoSaturate);
        d := max(keys H /sum);
        apply(select(keys H, k -> sum k == d), k -> last k => H#k)
    ) else toList apply(codim I..analyticSpread I, j -> {j, multiplicitySequence(j, I, opts)})
)
multiplicitySequence (ZZ, Ideal) := ZZ => opts -> (j, I) -> (
    (c, l) := (codim I, analyticSpread I);
    if j < c then ( print "Requested index is less than codimension"; return 0; );
    if j > l then ( print "Requested index is greater than analytic spread"; return 0; );
    if opts.Strategy == "generalElements" then (
        if not I.cache#?"colonIdeals" then I.cache#"colonIdeals" = new MutableHashTable;
        idealIn21 := if I.cache#"colonIdeals"#?j then I.cache#"colonIdeals"#j else (
            if not I.cache#?"generalElements" or #I.cache#"generalElements" < j then I.cache#"generalElements" = (
                if debugLevel > 0 then print "Finding general elements...";
                getGeneralElements(I, j, MinTerms => opts.MinTerms)
            );
            G := I.cache#"generalElements";
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
    ) else (multiplicitySequence I)#j
)

--------------------------------------------------------------------------------------------
-- Monomial functions
--------------------------------------------------------------------------------------------

---- extract the exponents of a monomial ideal
mon2Exp := I -> (
    if I != monomialIdeal I then error "Expected a monomial ideal";
    transpose matrix flatten apply(I_*, exponents)
)

---- computes the minimal monomial reduction of a monomial ideal
monomialReduction = method()
monomialReduction Ideal := MonomialIdeal => I -> (
    if I != monomialIdeal I then error "Expected a monomial ideal";
    sum(entries transpose sub(vertices newtonPolyhedron I, ZZ), e -> monomialIdeal((ring I)_e))
)

--- from a matrix M extract the rows where all the entries are not zero
isBddFacet := (n, M) -> (
    s := rank source M; --- # of columns
    mutableM := mutableIdentity (ZZ,s); --- row as a vector
    for i from 0 to (s - 1) do (mutableM_(i,i) = M_(n,i));
    det mutableM != 0 --- No if 0, Yes otherwise
)

--adds a column with zero entries to a given matrix
pyrF := M -> M | transpose map(ZZ^1, rank target M, 0)

---- gives a matrix of the from where all the entries are zero except one spot i,i
box := (i,n) -> (
    M := mutableIdentity (ZZ,n);
    for r from 0 to (n-1) do if r != i-1 then M_(r,r) = 0;
    matrix M
)

-- Computes the Newton polyhedron of a monomial ideal
newtonPolyhedron = method()
newtonPolyhedron Ideal := Polyhedron => I -> (
    if I != monomialIdeal I then error "Expected a monomial ideal";
    convexHull(mon2Exp I) + posHull(id_(ZZ^(dim ring I)))
)

-- Computes the analytic spread of a monomial ideal
analyticSpread MonomialIdeal := ZZ => o -> I -> (
    -- if I != monomialIdeal I then error "Expected a monomial ideal";
    d := dim ring I;
    P := newtonPolyhedron(I);
    M := halfspaces P;
    Mm := M_0;
    Mv := M_1;
    r := rank target Mm;  --- # of rows
    1 + max apply(r, p -> dim convexHull vertices intersection (Mm, Mv, Mm^{p}, Mv^{p}))
    -- monAS := 0;
    -- for p from 0 to r-1 do (
        -- face := intersection (Mm, Mv, Mm^{p}, Mv^{p});
        -- monAS = max(monAS,dim convexHull vertices face);      
    -- );
    -- 1 + monAS
)

--------------------------------------------------------------------------------------------
-- j-multiplicity
--------------------------------------------------------------------------------------------

-- Computes the j-multiplicity of an ideal
jMultiplicity = method()
jMultiplicity Ideal := ZZ => I -> (
    R := ring I;
    r := rank source vars R;
    G := gens I;
    g := rank source G;
    M := random(R^r,R^g)*transpose G;
    J := ideal(submatrix(M,{0..r-2},));
    UI := saturate(J,I) + ideal(submatrix(M,{r-1..r-1},));
    N := monoid[Variables=>r, MonomialOrder=>{Weights=>{-1,-1},RevLex},Global=>false];
    -- L := leadTerm gb UI;
    L := tangentCone UI;
    S := (QQ) N;
    f := map(S,R,vars S);
    C := S/f(L);
    -- dim (R/ ideal(submatrix(M,{0..r-1},)))
    if dim C == 0 then length(C^1) else (
        print "analytic spread not maximal";
        0
    )
)
-- monomial j-multiplicity
-- Dependences: loadPackage "Polyhedra", pryF, isBddFacet, mon2Exp, newtonPolyhedron
jMultiplicity MonomialIdeal := ZZ => I -> (
    d := dim ring I;
    P := newtonPolyhedron(I);
    M := halfspaces P;
    Mm := M_0;
    Mv := M_1;
    r := rank target Mm;  --- # of rows
    monj := 0;
    for p from 0 to r-1 do (
    if isBddFacet(p, Mm) then (
        face := intersection (Mm, Mv, Mm^{p}, Mv^{p});
        monj = monj + (d!)*(volume convexHull pyrF(vertices face));
        );
    );
    sub(monj, ZZ)
)

-- Synonyms (pre- v0.8.0)
grGr = tangentNormalCone
jMult = jMultiplicity
monReduction = monomialReduction
NP = newtonPolyhedron
-- getGenElts = getGeneralElements
-- monAnalyticSpread = monomialAnalyticSpread
-- monjMult = monomialjMultiplicity

--------------------------------------------------------------------------------------------
-- Documentation
--------------------------------------------------------------------------------------------

beginDocumentation()

doc ///
    Key
        MultiplicitySequence
    Headline
        multiplicity sequence of ideals
    Description
        Text
            The goal of this package is to compute the 
            @TO2{multiplicitySequence, "multiplicity sequence"}@ of 
            an ideal $I$ in a standard graded equidimensional ring over a field 
            $(R,\mathfrak{m},k)$, where $\mathfrak{m} = R_+$. The multiplicity sequence is a
            generalization of the Hilbert-Samuel multiplicity for ideals that 
            are not necessarily $\mathfrak{m}$-primary. This sequence is obtained as the
            leading terms of the second sum transform of the bivariate Hilbert
            polynomial of $G$, where 
            $G = \operatorname{gr}(\mathfrak{m} \operatorname{gr}(I))$
            is the associated graded ring of the extension of $\mathfrak{m}$ in the
            associated graded ring of $I$ (see @TO tangentNormalCone@).

            The multiplicity sequence was defined by Achiles and Manaresi in
            intersection theory [AM97]. Its importance comes from applications to
            problems in singularity theory (Segre numbers [AR01]) and commutative
            algebra (numerical  characterization of integral dependence 
            [PTUV20, SH06]). Indeed, in [PTUV20] the authors show that in a
            equidimensional and universally catenary Noetherian local ring, two
            ideals $J\subseteq I$ have the same integral closure if and only if
            they have the same multiplicity sequence.

            This package includes two different ways of computing the
            multiplicity sequence of an ideal. The first one uses the definition
            in terms of Hilbert polynomials, while the second uses a general
            element approach based on [AM97] (see also [PTUV20]). The package
            also contains a method that computes all of the coefficients of the
            Hilbert polynomial of a multi-graded module. These numbers can be
            seen as the generalizations of Hilbert coefficients for ideals that
            are not necessarily $\mathfrak{m}$-primary.
	    
        Text
            One of the terms of the multiplicity sequence is the j-multiplicity,
            another important invariant of an ideal in multiplicity theory.
            This package also contains a method @TO jMultiplicity@ which 
            computes the j-multiplicity of an ideal using Theorem 3.6 in [NU10],
            based on code written by H. Schenck and J. Validashti, or via
            polyhedral volume computations if the ideal is monomial, using a
            result of [JM13].
            The package also includes several functions related to integral
            dependence of monomial ideals, such as Newton polyhedron, analytic
            spread, and monomial reductions.
        Text
            The second author thanks D. Eisenbud, D. Grayson, and M. Stillman for
            organizing a Macaulay2 day during the special year in commutative 
            algebra 2012-2013 at MSRI where he learned how to write a package.
    	Text
            {\bf References}:
        Code
            UL {
                "[AM97] Achilles-Manaresi, Multiplicities of a bigraded ring and intersection theory. Math. Ann. 309, 573–591 (1997).",
                "[AR01] Achilles-Rams, Intersection numbers, Segre numbers and generalized Samuel multiplicities. Arch. Math. (Basel) 77, 391–398 (2001)",
                "[JM13] Jeffries-Montaño, The j-multiplicity of monomial ideals, Math. Res. Lett. 20 (2013), no. 4, 729–744.",
                "[NU10] Nishida-Ulrich, Computing j-multiplicities, J. Pure Appl. Algebra, 214(12) (2010), 2101–2110.",
                "[PTUV20] Polini-Trung-Ulrich-Validashti, Multiplicity sequence and integral dependence. Math. Ann. 378 (2020), no. 3-4, 951–969.",
    	    	"[SH06] Swanson-Huneke, Integral Closure of Ideals, Rings, and Modules, London Mathematical Society Lecture Note Series, vol. 336. Cambridge University Press, Cambridge (2006)."
            }
    Subnodes
        tangentNormalCone
        hilbertSequence
        multiplicitySequence
        jMultiplicity
        monomialReduction
        newtonPolyhedron
        (analyticSpread, MonomialIdeal)
///

doc ///
    Key
        tangentNormalCone
        "grGr"
        (tangentNormalCone, Ideal)
        PrimaryGradingIdeal
        [tangentNormalCone, Variables]
        [tangentNormalCone, PrimaryGradingIdeal]
    Headline
        the bigraded ring $\operatorname{gr}(\mathfrak{m} \operatorname{gr}(I))$
    Usage
        tangentNormalCone(I)
    Inputs
        I:Ideal
    Outputs
        :Ring
            the bigraded ring $\operatorname{gr}(\mathfrak{m} \operatorname{gr}(I))$
    Description
        Text
            Given a (graded) ideal $I$ in a (graded-)local ring $(R,\mathfrak{m})$, 
            this function computes the bi-graded ring 
            $G = \operatorname{gr}(\mathfrak{m} \operatorname{gr}(I))$, 
            presented as a quotient of a bigraded polynomial ring.
            After being computed once, this ring is stored in the cache 
            of $I$. This function is based on the method @TO normalCone@.
        Example
            R = QQ[x,y]
            I = ideal"x2,xy"
            A = tangentNormalCone I
            describe A
            hilbertSeries A
        Text
            The variable names may be specified with the option 
            @TT "Variables"@, which should be a list of two strings, with 
            default value {"u","v"}.
        Example
            J = (ideal gens R)^2
            tangentNormalCone(J, Variables => {"s", "t"})
        Text
            The user may also specify a $\mathfrak{m}$-primary ideal $Q$
            instead of $\mathfrak{m}$, via the option 
            @TT "PrimaryGradingIdeal"@, to compute 
            $\operatorname{gr}(Q \operatorname{gr}(I))$.
            Note that for general $\mathfrak{m}$-primary $Q$, one is 
            generally more interested in lengths over $R/Q$, instead of 
            $R/\mathfrak{m}$-vector space dimensions (as in the
            Hilbert series).
        Example
            tangentNormalCone(I, PrimaryGradingIdeal => J)
    SeeAlso
    	normalCone
///

doc ///
    Key
        multiplicitySequence
        (multiplicitySequence, Ideal)
        (multiplicitySequence, ZZ, Ideal)
        MinTerms
        DoSaturate
        [multiplicitySequence, DoSaturate]
        [multiplicitySequence, MinTerms]
        NumCandidates
        [multiplicitySequence, NumCandidates]
        [multiplicitySequence, Strategy]
    Headline
        the multiplicity sequence of an ideal
    Usage
        multiplicitySequence I
        multiplicitySequence(i, I)
    Inputs
        I:Ideal
        i:ZZ
    Outputs
        :HashTable
	    the multiplicity sequence of I
    Description
        Text 
            Given a (graded) ideal $I$, this function computes 
            the multiplicity sequence as defined in [0].
            Specifying {\tt Strategy => "generalElements"} will use the general element
            method as in [4].
        Example
            R = QQ[x,y,z]
            I = ideal"xy2,yz3,zx4"
            multiplicitySequence I
        Text 
            The @TO2{jMultiplicity, "j-multiplicity"}@ of $I$ is the $\ell$-th number,
            where $\ell$ is the @TO2{analyticSpread, "analytic spread"}@ of $I$.	
        Example
            analyticSpread I, jMultiplicity I
        Text
            Note that this function does not require the ambient ring to be a 
            polynomial ring.
        Example
            S = QQ[a..d]
            J = ideal (a*d - b*c, c^2-b*d)
            R = S/J
            I = ideal(R_0^2,R_0*R_1,R_1^3)
            multiplicitySequence I
        Text
            One can specify a particular element in the multiplicity sequence:
        Example
            multiplicitySequence_1 I
        Text
            One can tweak the behavior of the general elements strategy via
            the options @TT "MinTerms"@ and @TT "NumCandidates"@.
            @TT "MinTerms"@ controls the minimal number of summands in each 
            candidate general element (expressed as a linear combination of
            generators of $I$ - thus a lower value may result in "simpler"
            elements and quicker computations), and @TT "NumCandidates"@
            controls the number of attempts to find a general element in each
            codimension.
        CannedExample
            i11 : R = ZZ/2[x_1..x_9];
            
            i12 : I = minors(2, genericMatrix(R, 3, 3));
            
            i13 : multiplicitySequence (6, I, Strategy => "generalElements", MinTerms => 1)
            
            o13 = 12
            
            i15 : I.cache#"generalElements"

            o15 = {x x  + x x , x x  + x x , x x  + x x , x x  + x x , x x  + x x  + x x 
                    5 7    4 8   3 5    2 6   2 7    1 8   6 7    4 9   2 4    3 4    1 5
                   + x x  + x x  + x x , x x  + x x  + x x  + x x  + x x  + x x }
                      1 6    3 8    2 9   3 4    1 6    3 7    6 8    1 9    5 9
            
            i16 : I = ideal I_*; -- clears cache
            
            i17 : multiplicitySequence (6, I, Strategy => "generalElements")
            
            o17 = 12
            
            i18 : I.cache#"generalElements"
            
            o18 = {x x  + x x  + x x  + x x  + x x  + x x  + x x  + x x , x x  + x x  +
                    3 5    2 6    3 7    6 7    3 8    1 9    2 9    4 9   3 7    6 8
                   x x  + x x , x x  + x x  + x x  + x x  + x x  + x x  + x x  + x x  +
                    1 9    5 9   2 4    1 5    3 5    2 6    2 7    3 7    1 8    3 8
                   x x  + x x , x x  + x x  + x x  + x x , x x  + x x  + x x  + x x  +
                    1 9    2 9   3 4    1 6    3 7    1 9   2 4    3 4    1 5    1 6
                   x x  + x x  + x x  + x x  + x x  + x x , x x  + x x  + x x  + x x  +
                    3 7    6 7    3 8    1 9    2 9    4 9   2 4    3 4    1 5    3 5
                   x x  + x x  + x x  + x x  + x x  + x x  + x x  + x x }
                    1 6    2 6    2 7    5 7    1 8    4 8    6 8    5 9
            
            i19 : multiplicitySequence (9, I, Strategy => "generalElements", NumCandidates => 1)
            stdio:72:1:(3): error: Could not find general element. Consider running this function again, e.g. with a higher value of NumCandidates
            
            i20 : multiplicitySequence (9, I, Strategy => "generalElements", NumCandidates => 2)
            
            o20 = 2
    Caveat
    	There are two conventions in use about the order of the sequence. 
        The current function follows that of [4] and in this setting 
        the j-multiplicity of $I$ appears at the $\ell$-th spot, 
        where $\ell$ is the analytic spread of $I$.
        -- TODO: other convention?
        If the ideal $I$ is not graded, this function may produce incorrect 
        results.
    SeeAlso
    	jMultiplicity
        hilbertSequence
        tangentNormalCone
///

doc ///
    Key
        hilbertSequence
        HilbertSequence
        (net, HilbertSequence)
        (hilbertSequence, Module)
        (hilbertSequence, Ring)
        (hilbertSequence, Ideal)
        [hilbertSequence, DoSaturate]
    Headline
        the Hilbert sequence of a multi-graded module
    Usage
        hilbertSequence M
    Inputs
        M:Module
            or @TO ideal@
    Outputs
        :HilbertSequence
            of M
    Description
        Text
            Given an $\NN^p$-graded module $M$, this function computes 
            the coefficients of the pth sum transform of the $\NN^p$-graded 
            Hilbert function of $M$ in its Macaulay expansion. If the input 
            is an ideal $I$, then the Hilbert sequence of @TO comodule@ $I$ is 
            returned.
            --TODO is the Macaulay expansion defined?
            The output is a @TO HilbertSequence@, which is a type of 
            @TO HashTable@.
        Example
            R = QQ[a..e, DegreeRank => 5]
            I = monomialIdeal "de,abe,ace,abcd"
            hilbertSequence I
        Text
            For singly-graded modules, one can read off the Hilbert 
            polynomial from the Hilbert sequence.
        Example
            R = QQ[a..e]
            I = monomialIdeal "de,abe,ace,abcd"
            hilbertSequence I
            hilbertPolynomial I
        Text
            In the case of a bigraded module (e.g. @TO tangentNormalCone@ $I$ 
            for an ideal $I$), the result is displayed as a 2-dimensional table,
            whose alignment (either center or right) is controlled by the 
            package-wide Configuration option @TT "AlignCenter"@ 
            (default value true).
            This is particularly convenient in relation to the 
            @TO2{multiplicitySequence, "multiplicity sequence"}@: namely,
            the multiplicity sequence of $I$ appears as the top row of the table
            for the Hilbert sequence of 
            $\operatorname{gr}(\mathfrak{m} \operatorname{gr}(I))$.
        Example
            R = QQ[x_1..x_9]
            I = minors(2, genericMatrix(R, 3, 3))
            multiplicitySequence I
            hilbertSequence tangentNormalCone I
    Caveat
        In general, to retain a connection to the Hilbert polynomial (as 
        opposed to the pth sum transform) it is necessary to saturate with 
        respect to the irrelevant ideal, cf. page 235 of Conca-De Negri-Gorla, 
        "Cartwright–Sturmfels ideals associated to graphs and linear spaces", 
        2018. This is handled by the optional argument @TT "DoSaturate"@.
    SeeAlso
    	hilbertPolynomial
        multiplicitySequence
///

doc ///
    Key
        jMultiplicity
        "jMult"
        (jMultiplicity, Ideal)
        (jMultiplicity, MonomialIdeal)
    Headline
        the j-multiplicity of an ideal
    Usage
        jMultiplicity(I)
    Inputs
        I:Ideal
    Outputs
        :ZZ
            the j-multiplicity of I
    Description
        Text
            Given an ideal $I$, this function computes the j-multiplicity of $I$
            following the method of Nishida-Ulrich.
        Example
            R = QQ[x,y,z]
            I = ideal"xy,yz,zx"
            J = minimalReduction I
            jMultiplicity J
            jMultiplicity I
            multiplicitySequence I
        Text
            If the ideal $I$ is a monomial ideal, this function computes the 
            j-multiplicity of $I$ following the method of Jeffries-Montaño.
        Example
            R = QQ[x,y]
            I = (monomialIdeal "xy5,x2y3,x3y2")^4
            elapsedTime jMultiplicity I
            elapsedTime jMultiplicity ideal I
    SeeAlso
        multiplicitySequence
///

doc ///
    Key
        newtonPolyhedron
        "NP"
        (newtonPolyhedron, Ideal)
    Headline
        the Newton polyhedron of a monomial ideal
    Usage
        newtonPolyhedron(I)
    Inputs
        I:Ideal
    Outputs
        :Polyhedron
            the Newton polyhedron of the monomial ideal I
    Description
        Text
            Given a monomial ideal $I$ in $k[x_1,\dots,x_d]$, the convex hull 
            in $\mathbb{R}^d$ of the set of exponents of all monomials in $I$ 
            is called the Newton polyhedron of $I$. 
        Example
            R = QQ[x,y,z]
            I = ideal"x2,y3,yz"
            P = newtonPolyhedron I
        Text
            Note that a monomial is in the integral closure of $I$ 
            if and only if its exponent vector is in newtonPolyhedron(I).
        Example
            J = integralClosure(I,1)
    	    P == newtonPolyhedron J
    SeeAlso
        monomialReduction
///

doc ///
    Key
        monomialReduction
        "monReduction"
        (monomialReduction, Ideal)
    Headline
        the minimal monomial reduction of a monomial ideal
    Usage
        monomialReduction(I)
    Inputs
        I:MonomialIdeal
    Outputs
        :MonomialIdeal
            the minimal monomial reduction of I
    Description
        Text
            Given a monomial ideal $I$, this function computes a monomial 
            reduction of $I$ (i.e. a reduction of I which is a monomial ideal), 
            which is inclusion-wise minimal among all monomial reductions of $I$.
        Example
            R = QQ[x,y]
            I = monomialIdeal"x2,xy,y3"
            J = monomialReduction I
            J == I
            K = minimalReduction I
            degree J, degree K
        Text
            This function works by finding the extremal rays of 
            newtonPolyhedron(I), which correspond to the minimal generators of
            the monomial reduction of $I$.
    Caveat
        As seen above, a monomial minimal reduction need not be a minimal
        reduction.
    SeeAlso
        newtonPolyhedron
///

doc ///
    Key
        (analyticSpread, MonomialIdeal)
    Headline
        the analytic spread of a monomial ideal
    Usage
        analyticSpread(I)
    Inputs
        I:MonomialIdeal
    Outputs
        :ZZ
            the analytic spread of I
    Description
        Text
            Given a monomial ideal $I$, this function computes the analytic spread
            of $I$ as one more than the maximal dimension of a bounded facet of 
            its Newton polyhedron.
        Example
            R = QQ[x,y]
            I = monomialIdeal"x2,xy,y3"
            elapsedTime analyticSpread I
    SeeAlso
        newtonPolyhedron
///
 
--------------------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------------------

TEST /// -- Monomial ideals
R = QQ[x,y,z]
I = ideal "x4z, y3z"
K = ideal tangentNormalCone I;
S = QQ[a..e]
J = ideal(a*b^3, b^3*e, a*c^4)
assert(K == (map(ring K, S, gens ring K)) J)
assert(multiplicitySequence I === hashTable {(1, 1), (2, 15)})
assert(multiplicitySequence(I, Strategy => "tangentNormalCone") === multiplicitySequence(I, Strategy => "generalElements"))

R = QQ[x,y,z,t]
I = ideal "x3,y4,z5" * ideal "t"
assert(multiplicitySequence I === hashTable {(1, 1), (2, 3), (3, 72)})
assert(multiplicitySequence(I, Strategy => "tangentNormalCone") === multiplicitySequence(I, Strategy => "generalElements", MinTerms => 3))
///

TEST /// -- Determinantal ideals
R = QQ[x_1..x_8]
M = genericMatrix(R,4,2)
I = minors(2, M)
assert(multiplicitySequence I === hashTable {(3, 4), (4, 6), (5, 4)})

R = QQ[x_1..x_9]
M = genericMatrix(R,3,3)
I = minors(2, M)
assert(multiplicitySequence I === hashTable {(4, 6), (5, 12), (6, 12), (7, 6), (8, 3), (9, 2)})
///

TEST /// -- Ferrers ideals
(m,n)=(3,3)
R = QQ[x_0..x_(n-1),y_0..y_(m-1)]
I = ideal flatten table(n,m,(i,j)->x_i*y_j)
J1 = ideal apply(m,k-> sum(min(m-k,n),i->x_i*y_(k+i)));
J2 = ideal apply(1..(n-1),k-> sum(min(n-k,m),i->x_(k+i)*y_i));
J= J1+J2
assert(isReduction (I,J) and multiplicitySequence J === multiplicitySequence I)
assert((hilbertSequence tangentNormalCone I)#{0,3} == -1 and (hilbertSequence tangentNormalCone J)#{0,3} == -2)
///

TEST /// -- monomial functions
R = QQ[x,y]
I = monomialIdeal"x2,xy,y3"
assert(I == monomialReduction I)
assert not(I == minimalReduction I)
assert(analyticSpread I == analyticSpread ideal I)
assert(jMultiplicity I == 5)
assert(multiplicitySequence(analyticSpread I, I) == jMultiplicity I)
P = newtonPolyhedron I
importFrom("OldPolyhedra", {"fVector"})
assert(fVector P == {3,4,1})
///

TEST /// -- degenerate cases
R = QQ[x,y]
m = ideal "x,y"
I = ideal "x-1,y"
assert(pairs multiplicitySequence m == {(2,1)})
assert(pairs multiplicitySequence ideal "x,y2" == {(2,2)})
assert(pairs multiplicitySequence (m*I) == {(2,1)})
assert(multiplicitySequence(m^2*I, DoSaturate => true) === hashTable {})
assert(multiplicitySequence(m^2*I, DoSaturate => false) === hashTable {2 => 4})
///

end--

--------------------------------------------------------------------------------------------
-- Old code
--------------------------------------------------------------------------------------------

-- tangentNormalCone = I -> (
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
    -- minimalPresentation T
    -- hilbertSeries oo
-- )

-- cSubi = method() -- auxiliary method that computes the multiplicity sequence via Hilbert functions
-- cSubi (ZZ, Ideal) := ZZ => (i,I) -> (
    -- G := tangentNormalCone I;
    -- if not G.cache#?"hilbertSeries" then G.cache#"hilbertSeries" = hilbertSeries(G, Reduce => true);
    -- hS := G.cache#"hilbertSeries"; -- hilbertS := reduceHilbert hilbertSeries G;
    -- poinP := numerator hS;
    -- dPoinP := denominator hS;
    -- A := ring poinP;
    -- B := newRing (A, Degrees => {{1,0}, {0,1}}); -- B := newRing (A, Degrees => {{1,0}, {0,1},{0,0}});
    -- use B;
    -- topP := sub (poinP, B);
    -- botP := value toString dPoinP;
    -- firVar := (ultimate (flatten, entries (vars B)_{0}))_0;
    -- secVar := (ultimate (flatten, entries (vars B)_{1}))_0;
    -- powerFirVar := (degree botP)_0;     
    -- powerSecVar := (degree botP)_1;     
    -- d := dim ring I;
    -- a := powerFirVar - (d - i);
    -- b := powerSecVar - i;
    -- c := topP;
    -- for i from 1 to a do (c = diff( firVar, c));
    -- c = sub (c, firVar => 1);
    -- for i from 1 to b do (c = diff (secVar, c));
    -- c = sub (c, secVar => 1); 
    -- c = c*(-1)^(a+b);
    -- if (c <= 0 or a < 0 or b < 0) then 0 else (sub(c,ZZ) // (a! * b!))
-- )

-- etangentNormalCone = method()
-- etangentNormalCone Ideal := ZZ => I -> (
   -- A := tangentNormalCone I;
   -- B := newRing (A, Degrees => splice{ (#gens A) : 1});
   -- degree B
-- )

-- hilbertSamuelMultiplicity := I -> ( -- computes e(m, R/I) (need to fix)
   -- R := (ring I)/I;
   -- k := coefficientRing ring I;
   -- maxR := ideal vars R;
   -- if (dim R == 0) then return (degree comodule primaryComponent (I, maxR)); -- finite colength case; 
   -- genLinComMat := (gens maxR) * random (k^(numgens maxR), k^(dim R));
   -- colInGenLinComMat := numcols genLinComMat;
   -- genRedIdeal := ideal (0_R);
   -- if (dim R == 1) then genRedIdeal = saturate (ideal (0_R), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    -- the case of dim R/I >= 2
       -- else genRedIdeal = saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat;     
    -- if (codim genRedIdeal != dim R) then return "Elements chosen are not general. Try again."; 
    -- use ring I;
    -- the length method doesn't handle the non-graded case, but the degree function does.
   -- degree comodule primaryComponent (genRedIdeal,maxR) -- alternatively normalCone?
-- )

-- gHilb = method()
-- gHilb (ZZ, MonomialIdeal) := Module => (n, I) -> (
   -- R := ring I;
   -- Inp1 := sub((intclMonIdeal trim I^(n+1))_0 , R );
   -- In := sub((intclMonIdeal trim I^n)_0, R  );
   -- HH^0( (In / Inp1) )
-- )
-- gHilb (ZZ, Ideal) := Module => (n, I) -> ( 
   -- J := monomialIdeal I;
   -- if J != I then error "Expected a monomial ideal";
   -- gHilb (n, J)
-- )

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

--------------------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------------------

R = QQ[x,y]
I = ideal "x2y,xy2"
monomialjMultiplicity I
jMultiplicity I -- jMultiplicity 3

-- Monomial ideal, not generated in single degree
R = QQ[x,y,z]
I = ideal(x^2*y^2, y*z^2, x*z^2, z^3) -- Weird minimal presentation with tangentNormalCone I
getGeneralElements(I, l, MinTerms => 3)

-- Aug 21, 2020
x = symbol x
R = ZZ/31[x_1..x_10]; M = genericMatrix(R,5,2)
R = QQ[x_1..x_9]; M = genericMatrix(R,3,3);
I = minors(2, M)
 
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

(monomialAnalyticSpread I, analyticSpread I)

S = R/I
J = ideal z
multiplicitySequence(1, J)

R = QQ[a..e]
R = QQ[a..e,DegreeRank => 5]
I = monomialIdeal "de,abe,ace,abcd" -- Ex. 1.14 in Miller-Sturmfels
hilbertPolynomial I
hilbertPolynomial(I, Projective => false)

R = QQ[x_1..x_3, DegreeRank => 3]
I = monomialIdeal(x_1^2, x_1*x_2, x_2^3, x_1*x_3^3) -- Ex. 2.4 in Miller-Sturmfels
hilbertSeries I -- Ex 2.13 in Miller-Sturmfels


needsPackage "CorrespondenceScrolls"
P = productOfProjectiveSpaces{1,2}
M1 = comodule ideal(random({1,2},P),random({2,3},P),random({5,2},P));
elapsedTime multiHilbertPolynomial M1 -- == 44, ~1.4 seconds
hilbertSequence M1
-- Note: this has a key {0,3}, while value for key {1,1} is 44

R = QQ[x,y,z]
m = ideal(x^2+1, y^3+y+1, z)
I = m^2
G1 = normalCone(I, Variable => "v")
G2 = minPres normalCone(sub(m, G1), Variable => "u")
n1 = #select(gens G2, g -> (bN := baseName g; instance(bN, IndexedVariable) and toString bN#0 == "u"))
n2 = #select(gens G2, g -> (bN := baseName g; instance(bN, IndexedVariable) and toString bN#0 == "v"))
G = newRing(G2, Degrees => splice({n1 : {1,0}} | {n2 : {0,1}} | {#gens G2 - n1 - n2 : {0,0}})) -- Heft => {0, 1}, 
hilbertSeries G -- error: hilbertSeries: ring has no heft vector

----------

restart
needsPackage "MultiplicitySequence"
loadPackage("MultiplicitySequence", Reload => true)
loadPackage("MultiplicitySequence", Reload => true, Configuration => {"AlignCenter" => false})
installPackage("MultiplicitySequence", RerunExamples => true, RemakeAllDocumentation => true)
uninstallPackage "MultiplicitySequence"
check "MultiplicitySequence"
viewHelp "MultiplicitySequence"
needsPackage "MinimalPrimes"
installMinprimes()
debugLevel = 2

elapsedTime multiplicitySequence I
elapsedTime multiplicitySequence(codim I, I)
elapsedTime multiplicitySequence(analyticSpread I, I)
