-- Aug 14, 2020
-- The code below will compute the multiplicity sequence for the ideal generated by the 2x2 minors of a generic 4 by 2 matrix.
-- I avoided using the localRing method as computation of computing the local length an ideal was much slower than I expected.
-- There is a hidden formula which recovers the local length using the associativity formula (you should verify this).
-- The assumption that the ``ideals'' have the expected codimension needs to be discussed. (This is my, Youngu's, question.) 

-- To test the code for fun, run it up to the line right above j = 6. 
-- For each block starting with j = 3,4, or 5, the last line produces {j,c_j}. 
-- The remaining ones were created to test the case R = ZZ/31[x_1..x_10], M = genericMatrix(R,5,2), 
-- but I don't think our algorithm is efficient enough to handle this. (So, moding out by a general elements might be the way.)

-- I can explain each line in detail tomorrow.

R = QQ[x_1..x_8]
M = genericMatrix(R,4,2)
R = ZZ/31[x_1..x_9], M = genericMatrix(R,3,3)
maxR = ideal vars R
I = minors(2,M)
time dMinusI = dim R - dim (R/I), l = analyticSpread I

-- general elements
genEleMat = (gens I) * random(ZZ^(numgens I), ZZ^l) -- here l is the analytic spread of I

dMinusI >= 2 -- add ``if''
    time colonIdeals = for i from dMinusI to l list {i,(saturate(ideal submatrix(genEleMat,{0..(i-2)}),I) + ideal submatrix(genEleMat,{i-1}) )} -- x_1..x_(i-1):I^infty + (x_i)
    time apply(colonIdeals, i -> codim i_1) == for i from dMinusI to l list i -- this checks if x_1..x_(i-1):I^infty + (x_i) is of codim i.
needsPackage "MinimalPrimes" -- Justin's suggestion 
installMinprimes()
    time minPrimesOfColonIdeals = for i from 0 to (#colonIdeals-1) list {(colonIdeals_(i))_0, minimalPrimes (I+(colonIdeals_(i))_1 ) }

--needsPackage"LocalRings"
    -- for loop
j = 3
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
--    for i from 0 to (#primesIn21 -1) list length comodule sub (idealIn21, localRing (ring idealIn21, primesIn21_i))
--    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/primesIn21_i)
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i)) -- alternative way to compute the colength using the associative formula
    {j,sum oo}
    
j = 4
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i))
    {j,sum oo}
    
j = 5
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 -- 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i))
    {j,sum oo}

j = 6
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 -- 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i))
    {j,sum oo}

j = 7
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 -- 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i))
    {j,sum oo}

j = 8
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 -- 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i))
    {j,sum oo}

j = 9
    idealIn21 = ((select (colonIdeals, i-> i_0 == j))_0)_1 -- 
    primesIn21 = ((select (minPrimesOfColonIdeals, i-> i_0 == j))_0)_1
    time for i from 0 to (#primesIn21 -1) list multiplicity sub(maxR, R/localize(idealIn21, primesIn21_i))
    {j,sum oo}

-- non m-primary component






























