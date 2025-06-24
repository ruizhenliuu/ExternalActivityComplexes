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

-- Precondition: a list of generators, return support of x, y and combined 
-- Postcondition: a hashTable. "x" => support set for x, "y" => support set for y, "d" =>
-- generator-wise union of support of x and y. 
SupportSets = method()
SupportSets(List) := (lst) -> (
    n = dim ring lst#0 // 2; 
    xSupp = {};
    ySupp = {};
    dilworthSupp = {};
    for eq in lst do (
       allsupp = apply(flatten entries monomials eq, support);
       for m in allsupp do (
            i2 = set apply(select(m, v -> match("x_",toString v)), 
            m -> index(m)+1 );
            i1 = set apply(select(m, v -> match("y_",toString v)), 
            m -> index(m)-n + 1);
            xSupp = append(xSupp, i2);
            ySupp = append(ySupp, i1);
            dilworthSupp = append(dilworthSupp, i1+i2);
       );
    );
    hashTable {"x" => set xSupp, "y" => set ySupp, "d"=>set dilworthSupp}
)

SupportSetsC = method()
SupportSetsC(List,List) := (lst,Coords) -> (
    n = dim ring lst#0 // 2; 
    xSupp = {};
    ySupp = {};
    dilworthSupp = {};
    for eq in lst do (
       allsupp = apply(flatten entries monomials eq, support);
       for m in allsupp do (
            i2 = set apply(select(m, v -> match("x_",toString v)), 
            m -> index(m)+1 );
            i1 = set apply(select(m, v -> match("y_",toString v)), 
            m -> index(m)-n + 1);
            xSupp = append(xSupp, i2);
            ySupp = append(ySupp, i1);
            dilworthSupp = append(dilworthSupp, i1+i2);
       );
    );
    coordset = set Coords;
    xSupp = select(xSupp, I -> isSubset(I, coordset));
    ySupp = select(ySupp, I -> isSubset(I, coordset));
    dilworthSupp = select(dilworthSupp, I -> isSubset(I, coordset));
    hashTable {"x" => set xSupp, "y" => set ySupp, "d"=>set dilworthSupp}
)


-- Precondition: two an r1-by-n matrix A1 and an r2-by-n matrix A2,
-- Postcondition: the Bialynicki-Birula
-- stratification of the matroid Schubert variety of the pair (A1, A2).
-- Atrata given in the form (zero coordinates, equation at A^I)
-- given as a hash map, key by the zero set 

BBCells = method()
BBCells(Matrix, Matrix) := (A1,A2) -> (
    Coords := fixedPtCoordList(A1,A2);
    I = affineSchubertVariety(A1,A2);
    n = dim ring I // 2;
    for c in Coords list (
        J = sub(I, toList (
        ((1..n)/(i->(x_i => if isMember(i,c) then x_i else 1))) |
        ((1..n)/(i->(y_i => if isMember(i,c) then 1 else 0)))
        )
    );
    c => J
    )
)

-- Precondition: two an r1-by-n matrix A1 and an r2-by-n matrix A2, 
-- Postcondition: hash map of Bialynicki-Birula 
-- stratification of the matroid Schubert variety of the pair (A1, A2).
-- Atrata given in the form (zero coordinates, equation for stratum closure)
-- given as a hash map, key by the zero set 

BBStrataFromA1 = method()
BBStrataFromA1(Matrix, Matrix) := (A1,A2) -> (
    Coords := fixedPtCoordList(A1,A2);
    I = affineSchubertVariety(A1,A2);
    for c in Coords list (
    strat =  BBStratum(I,c);
    stratGens = flatten entries gens strat;
    supp = SupportSetsC(stratGens, c);
    {c, stratGens, supp#"y", supp#"x", supp#"d", primaryDecomposition strat}
    )
)

BBStrataAlt = method()
BBStrataAlt(Matrix, Matrix) := (A1,A2) -> (
    Coords := fixedPtCoordList(A1,A2);
    I = affineSchubertVariety(A1,A2);
    M1 = matroid A1;
    M2 = matroid A2;
    E = groundSet M1;
    for c in Coords list (
        strat =  BBStratum(I,c);
        stratGens = flatten entries gens strat;
        supp = SupportSetsC(stratGens, c);
        M3 = M1 | set c;
        M4 = M2 / (E - set c);
        D = diagonalDilworthTruncation(M3,M4);
        {c, stratGens, supp#"y", supp#"x", supp#"d", rank M3, rank M4, rank D,rank(D) == rank M3 +
        rank M4 - 1}
    )
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

bbstrata = BBStrataFromA1(A1,A2)

bbcells = BBCells(A1,A2)

"example1cell.txt" << netList bbcells << close

"example1strata.txt" << netList bbstrata << close

-- Write to excel
fn = "output7.csv";

fn << "IndexingSet,Generators,I1,I2,C,primaryDecomposition\n";

for entry in bbstrata do (
  fn << "\"" | toString entry#0 | "\"" | "," | 
        "\"" | toString entry#1 | "\"" | "," |
        "\"" | toString entry#2 | "\"" | "," |
        "\"" | toString entry#3 | "\"" | "," |
        "\"" | toString entry#4 | "\"" | "," |
        -- "\"" | toString entry#5 | "\"" | "," |
        -- "\"" | toString entry#6 | "\"" | "," |
        "\"" | toString entry#5 | "\"" | "\n";
);

fn << close;

fixedpts = SchubertfixedPts(A1, A2);

length fixedpts -- number of fixed pts 
netList fixedpts -- fixed pts list

---

A3 = transpose matrix {{1,0},{1,5},{1,4},{1,1},{1,2},{1,3}}

A4 = transpose matrix {{1,1},{1,6},{1,5},{1,2},{1,3},{1,9}}

bbstrata = BBStrataFromA1(A3,A4)

-- 

A2 = matrix{
    {1,0,0,1,0,1,1},
    {0,1,0,0,1,1,1},
    {0,0,1,1,1,0,1}
}

A1 =  matrix{
    {1,1,1,1,1,1,1},
    -- {0,1,0,1,2,2,2},
    {0,1,1,1,1,1,1}
}

bbstrata = BBStrataFromA1(A1,A2)

M1 = matroid A1;

M2 = matroid A2;

D = diagonalDilworthTruncation(M1,M2)


