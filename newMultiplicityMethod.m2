-- length -> degree
-- localize (I,P) -> primaryComponent (I,P)

multiplicityG := (I)-> {
    RRR := (ring I)/I;
    maxR := ideal vars RRR;
    if (dim RRR == 0) then return (degree comodule primaryComponent (I, maxR)); -- finite colength case; 
    genLinComMat := (gens maxR) * random (ZZ^(numgens maxR), ZZ^(dim RRR));
    colInGenLinComMat := numcols genLinComMat;
    if (dim RRR == 1) then redIdeal := saturate (ideal (0_RRR), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    else redIdeal := saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat;     
    -- the case of dim R/I >= 2
    if (codim redIdeal != dim RRR) then return "Elements chosen are not general. Try again."; 
    -- blank line
    use ring I;
    -- return length comodule primaryComponent (redIdeal,maxR) 
    -- the length method doesn't handle the non-graded case, but the degree function does.
    return degree comodule primaryComponent (redIdeal,maxR) 
    }

-- Examples
R = QQ[x,y,z]
I = ideal "xy2,yz3,zx4"
J = ideal "x2+y3"

-- expect 9
multiplicityG I
multiplicity sub(ideal vars R, R/I)
multiplicityG sub(I,R)

-- expect 2
multiplicity sub(ideal vars R, R/J)
multiplicityG sub(J,R) 
