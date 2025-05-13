load "ExternalActivityComplexes.m2"

-- Given two an r1-by-n matrix A1 and an r2-by-n matrix A2, return the fixed points of the matroid
-- Schubert variety of the pair (A1, A2) as a list of zero dimensional ideals 
SchubertfixedPts = method(    
    Options => {
	CoefficientRing => QQ
	})
SchubertfixedPts(Matrix, Matrix) := o -> (A1,A2) -> (
    if (numcols A1 != numcols A2) then error("A1 and A2 should have the same number of columns.");
    n = numcols A1;
    I = affineSchubertVariety(A1,A2);
    S = ring I;
    Ifixed := ideal((1..n)/(i->(((gens S)_{i-1}_0)*((gens S)_{n+i-1}_0))));
    I2 := I+Ifixed;
    I2rad := radical I2;
    primaryDecomposition I2rad 
);

-- turns an ht-0 ideal {x_i: i in I} + {y_i: i not in I} back into the zero coordinates I
idealToCoords = method()
idealToCoords(Ideal) := P -> ( 
    toList select(1..n, i -> isMember(x_i, flatten entries gens P))
);


-- Given two an r1-by-n matrix A1 and an r2-by-n matrix A2, return the fixed points of the matroid
-- Schubert variety of the pair (A1, A2) as a list of *zero coordinates* 
fixedPtCoordList =  method()
fixedPtCoordList(Matrix, Matrix) := (A1,A2) -> (
    fixedPts := SchubertfixedPts(A1, A2);
    for P in fixedPts list idealToCoords(P)
);

-- Returns the Bialynicki-Birula basin of attraction with y_i -> 0 for i not in S. For example, the
-- whole ground set is the biggest stratum 

BBStratum = method()
BBStratum(Ideal, List) := (I, S) ->  (
    n = dim ring I // 2; 
    Zs = product for i from 1 to n list ideal(x_i, y_i); -- irrelevant ideal
    Wall = ideal flatten apply(select(1..n, j -> not member(j, S)), i -> y_i);
    saturate(radical I+Wall, Zs)
)

-- Given two an r1-by-n matrix A1 and an r2-by-n matrix A2, return the Bialynicki-Birula
-- stratification of the matroid Schubert variety of the pair (A1, A2).
-- Atrata given in the form (zero coordinates, equation for stratum closure)

BBStrataFromA1 = method()
BBStrataFromA1(Matrix, Matrix) := (A1,A2) -> (
    Coords := fixedPtsList(A1,A2);
    I = affineSchubertVariety(A1,A2);
    for c in Coords list {c,BBStratum(I,c)}
)

-- main --
A1 = matrix{
    {1,0,0,1,0,1},
    {0,1,0,0,1,1},
    {0,0,1,1,1,0}
    }

A2 = matrix{
    {1,1,1,1,1,1},
    {0,1,2,3,4,5}
} 

BBStrataFromA1(A1,A2)

fixedpts = SchubertfixedPts(A1, A2);

length fixedPts -- number of fixed pts 
netList fixedPts -- fixed pts list


