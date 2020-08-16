

-- length -> degree
-- localize (I,P) -> primaryComponent (I,P)

multiplicityG := (I)-> {
    RRR := (ring I)/I;
    maxR := ideal vars RRR;
    if (dim RRR == 0) then return (degree comodule primaryComponent (I, maxR)); -- finite colength case; 
    genLinComMat := (gens maxR) * random (ZZ^(numgens maxR), ZZ^(dim RRR));
    colInGenLinComMat := numcols genLinComMat;
    genRedIdeal = ideal (0_RRR);
    if (dim RRR == 1) then genRedIdeal = saturate (ideal (0_RRR), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    -- the case of dim R/I >= 2
        else genRedIdeal = saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat;     
    -- if (codim genRedIdeal != dim RRR) then return "Elements chosen are not general. Try again."; 
    -- blank line
    use ring I;
    -- return length comodule primaryComponent (genRedIdeal,maxR) 
    -- the length method doesn't handle the non-graded case, but the degree function does.
    return degree comodule primaryComponent (genRedIdeal,maxR) 
    }

-- Examples
R = QQ[x,y,z]
I = ideal "xy2,yz3,zx4"
J = ideal "x2+y3"
K = ideal (x^2,y^3,z^4)

-- expect 24
multiplicityG K 
multiplicity sub(ideal vars R, R/K)

-- expect 9
time multiplicityG I -- this example is sensitive to the ring which coefficients lies in (ZZ or QQ) 
-- for i to 10 do print multiplicityG I
multiplicity sub(ideal vars R, R/I)

-- expect 2
multiplicity sub(ideal vars R, R/J)
multiplicityG J
