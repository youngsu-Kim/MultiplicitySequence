
hilbertSamuelMultiplicity := (I)-> ( -- computes e(m, R/I)
    R := (ring I)/I;
    maxR := ideal vars R;
    if (dim R == 0) then return (degree comodule primaryComponent (I, maxR)); -- finite colength case; 
    genLinComMat := (gens maxR) * random (ZZ^(numgens maxR), ZZ^(dim R));
    colInGenLinComMat := numcols genLinComMat;
    genRedIdeal = ideal (0_R);
    if (dim R == 1) then genRedIdeal = saturate (ideal (0_R), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    -- the case of dim R/I >= 2
        else genRedIdeal = saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat;     
    -- if (codim genRedIdeal != dim R) then return "Elements chosen are not general. Try again."; 
    -- use ring I;
    -- the length method doesn't handle the non-graded case, but the degree function does.
    degree comodule primaryComponent (genRedIdeal,maxR) 
)

getGenElts = method(Options => {symbol minTerms => 1, symbol numCandidates => 20})
getGenElts (Ideal, ZZ) := List => opts -> (I, n) -> (
    G := flatten entries mingens I; -- I_*;
    R := ring I;
    J := ideal(0_R);
    result := {};
    for i from 1 to n do (
        foundNext := false;
        t := if i == n then 1 else opts.minTerms;
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
    c := codim I; -- dim R - dim I;
    l := analyticSpread I;
    if j < c then ( print "Requested index is less than codimension"; return; );
    if j > l then ( print "Requested index is greater than analytic spread"; return; );
    if not I.cache#?"colonIdeals" then (
        (G, numTries) := ({}, 0);
        if debugLevel > 0 then print "Finding general elements...";
        while #G < l and numTries < 10 do (
            try ( G = getGenElts(I, l, minTerms => opts.minTerms + numTries//3); );
            numTries = numTries + 1;
        );
        if #G < l then error "Could not find general elements. Consider running this function again, possibly with a higher value of minTerms (e.g. minTerms => 3)";
        if debugLevel > 0 then print "Finding colon ideals...";
        candidates := apply(toList(c..l), i -> (i, saturate(ideal(G_{0..i-2}), I) + ideal(G#(i-1))));
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

randomSubset = method()
randomSubset (List, ZZ) := List => (L, k) -> (
    i := random(#L);
    if k == 1 then {L#i} else {L#i} | randomSubset(L_(delete(i, toList(0..<#L))), k-1)
)

end--

load "default.m2"
needsPackage "MinimalPrimes"
installMinprimes()
debugLevel = 1

elapsedTime multiplicitySequence(codim I, I)
elapsedTime multiplicitySequence(codim I, I, minTerms => 3)
elapsedTime multiplicitySequence I
elapsedTime multiplicitySequence(I, Strategy => "FullColon")
elapsedTime multiplicitySequence(analyticSpread I, I, minTerms => numgens I - 1)

l = analyticSpread I
tally apply(100, i -> (remove(I.cache, "colonIdeals"); elapsedTime multiplicitySequence(l, I, minTerms => numgens I)))

-- Monomial ideal, not generated in single degree
R = QQ[x,y,z]
I = ideal(x^2*y^2, y*z^2, x*z^2, z^3)
getGenElts(I, l, minTerms => 3)

-- Aug 21, 2020
R = QQ[x_1..x_8]
M = genericMatrix(R,4,2)
I = minors(2, M)

R = ZZ/31[x_1..x_10]; M = genericMatrix(R,5,2)
R = QQ[x_1..x_9]; M = genericMatrix(R,3,3)

 L = {3,3,3,3}
 randomMonomialIdeal (L, R)
 ideal(x^2*y,x^2*z,z^3,x^2*w) -- codim I = 2, l(I) = 4 check c_3.
-- non m-primary component

-- Old code

maxR = ideal vars R
I = minors(2,M)
dMinusI = dim R - dim (R/I), l = analyticSpread I

-- general elements
genEleMat = (gens I) * random(ZZ^(numgens I), ZZ^l); -- here l is the analytic spread of I, change QQ to the ring R

dMinusI >= 2 -- add ``if''
    colonIdeals = for i from dMinusI to l list time {i,(saturate(ideal submatrix(genEleMat,{0..(i-2)}),I) + ideal submatrix(genEleMat,{i-1}) )}; -- x_1..x_(i-1):I^infty + (x_i)
    time apply(colonIdeals, i -> codim i_1) == for i from dMinusI to l list i -- this checks if x_1..x_(i-1):I^infty + (x_i) is of codim i.
    minPrimesOfColonIdeals = for i from 0 to (#colonIdeals-1) list time {(colonIdeals_(i))_0, minimalPrimes (I+(colonIdeals_(i))_1 ) };


-- for loop
j = 3
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1; 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1;
    time for i from 0 to (#primesIn21 -1) list hilbertSamuelMultiplicity primaryComponent(idealIn21, primesIn21_i)
    {j,sum oo}
    
j = 4
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1;
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1;
    for i from 0 to (#primesIn21 -1) list time hilbertSamuelMultiplicity localize(idealIn21, primesIn21_i);
    for i from 0 to (#primesIn21 -1) list time hilbertSamuelMultiplicity primaryComponent(idealIn21, primesIn21_i) -- localize is faster than primaryComponent
    {j,sum oo}
---- The case of homogeneous ideals
---- Method 1
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1; 
    time primesIn21 = minimalPrimes idealIn21;
    time primesIn21NotConI = select (primesIn21, i-> not isSubset(I,i));
    time intPrimesIn21NotConI = primesIn21NotConI // intersect;
    time saturate(idealIn21, intPrimesIn21NotConI);
    time if isHomogeneous oo then degree oo     
---- Method 2 
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1;
    time primesIn21 = minimalPrimes (idealIn21+I);
    time primesIn21 // intersect;
    time saturate(idealIn21, saturate(idealIn21,oo)); -- possible to have embedded components, need to check if inner saturated ideal is unit ideal (e.g. j = 7 with I_2(5x2 generic))
    time if isHomogeneous oo then degree oo


(m,n) = (6,6)    
R = QQ[x_0..x_(n-1),y_0..y_(m-1)]
I = ideal flatten table(n,m,(i,j)->x_i*y_j)
J1 = ideal apply(m,k-> sum(min(m-k,n),i->x_i*y_(k+i)));
J2 = ideal apply(1..(n-1),k-> sum(min(n-k,m),i->x_(k+i)*y_i));
J= J1+J2
