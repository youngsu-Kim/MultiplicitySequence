R = QQ[x,y,z,w]
I = ideal "xy2,yz3,zx4"
J = ideal "x2+y3"


multiplicityG = method()
multiplicityG := (I)-> {
    -- we may want to put a code to check equidimentionality of I
    RRR := (ring I)/I;
    maxR := ideal vars RRR;
    if (dim RRR == 0) then return (length comodule I); -- finite colength case; the code of picking up the maxR-primary component is missing
    genLinComMat := (gens maxR) * random (ZZ^(numgens maxR), ZZ^(dim RRR));
    colInGenLinComMat := numcols genLinComMat;
    if (dim RRR == 1) then redIdeal := saturate (ideal (0_RRR), maxR) + ideal genLinComMat  -- the case of dim R/I = 1
    else redIdeal := saturate (ideal submatrix (genLinComMat, {0..(colInGenLinComMat - 2)}), maxR) + ideal genLinComMat; -- the case of dim R/I >= 2
    if (codim redIdeal != dim RRR) then return "Elements chosen are not general. Try again."; 
    --
    return length comodule redIdeal --  the code of picking up the maxR-primary component is missing, for (x^2+y^3) there is another component
}

-- expect 9
multiplicity sub(ideal vars R, R/I)
multiplicityG I

multiplicity sub(ideal vars R, R/J)
multiplicityG J -- it doesn't work