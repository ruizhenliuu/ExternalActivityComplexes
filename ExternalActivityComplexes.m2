newPackage(
    "ExternalActivityComplexes",
    AuxiliaryFiles => false,
    Version => "0.1", 
    Date => "",
    Authors => {
        {Name => "Ayah Almousa", 
            Email => "aalmousa@sc.edu", 
            HomePage => "http://sites.google.com/view/ayah-almousa"}
    },
    Headline => "functions for investigating affine Schubert varieties of a pair of linear spaces",
    PackageExports => {
        "Posets",
	"Matroids"
    },
    DebuggingMode => true
)

export{
    "diagonalDilworthTruncation",	  --documented, has tests
    "kempfCollapsing",			  --no doc, no tests
    "affineSchubertVariety",		  --no doc, no tests
    "kempfCollapsingBeta"		  --no doc, no tests
}
    
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **CODE** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------

diagonalDilworthTruncation = method()

--maybe cache I1 and I2 in a hash table for each C?
diagonalDilworthTruncation(Matroid, Matroid) := Matroid => (M1,M2) -> (
    G := groundSet M1; --assuming they have the same G for now
    possibleCircuits := drop(subsets G,1); --drop empty set
    circuitList := new MutableList;
    for C in possibleCircuits do(
	if (rank(M1,C) + rank(M2,C) == #C) then circuitList#(#circuitList) = C;
	);
    circuitsFinal := apply(toList circuitList, i-> toList i);
    matroid(toList G, circuitsFinal, EntryMode => "circuits")
    )

kempfCollapsing = method(
    Options => {
	CoefficientRing => QQ
	}
    )

kempfCollapsing(Matrix, Matrix) := o -> (A1,A2) -> (
    if (numcols A1 != numcols A2) then error("A1 and A2 should have the same number of columns.");
    kk := o.CoefficientRing;
    n := numcols A1;
    m1 := numrows A1;
    m2 := numrows A2;
    (t,u,v,x,y) := (getSymbol "t", getSymbol "u", getSymbol "v",getSymbol "x", getSymbol "y");
    R := kk[u_1..u_m1,v_1..v_m2,t_1..t_n];
    S := kk[x_1..x_n,y_1..y_n];
    use R;
    T := diagonalMatrix((gens R)_{numgens R-n..numgens R-1});
    tInvVars := apply(1..n, i-> product select((gens R)_{numgens R-n..numgens R-1}, j-> last baseName j != i));
    Tinv := diagonalMatrix(toList tInvVars);
    L1 := matrix{(gens R)_{0..m1-1}}*A1*T;
    L2 := matrix{(gens R)_{m1..m1+m2-1}}*A2*Tinv;
    phi := map(R,S,L1|L2);
    kernel phi
    );


affineSchubertVariety = method(
    Options => {
	CoefficientRing => QQ
	}
    )

affineSchubertVariety(Matrix, Matrix) := o -> (A1,A2) -> (
    if (numcols A1 != numcols A2) then error("A1 and A2 should have the same number of columns.");
    kk := o.CoefficientRing;
    n := numcols A1;
    m1 := numrows A1;
    m2 := numrows A2;
    (t,u,v,x,y) := (getSymbol "t", getSymbol "u", getSymbol "v", getSymbol "x", getSymbol "y");
    R := kk[u_1..u_m1,v_1..v_m2,t_1..t_n];
    S := kk[x_1..x_n,y_1..y_n];
    use R;
    T := diagonalMatrix((gens R)_{numgens R-n..numgens R-1});
    L1 := matrix{(gens R)_{0..m1-1}}*A1*T;
    L2 := matrix{(gens R)_{m1..m1+m2-1}}*A2*T;
    phi := map(R,S,L1|L2);
    kernel phi
    );


kempfCollapsingBeta = method(
    Options => {
	CoefficientRing => QQ
	}
    )

kempfCollapsingBeta(Matrix, Matrix) := o -> (A1,A2) -> (
    if (numcols A1 != numcols A2) then error("A1 and A2 should have the same number of columns.");
    kk := o.CoefficientRing;
    n := numcols A1;
    m1 := numrows A1;
    m2 := numrows A2;
    (t,u,v,x,y,z) := (getSymbol "t", getSymbol "u", getSymbol "v",getSymbol "x", getSymbol "y", getSymbol "z");
    R := kk[u_1..u_m1,v_1..v_m2,t_1..t_n];
    S := QQ[x_1..x_n,y_1..y_n,z_1..z_n];
    use R;
    T := diagonalMatrix((gens R)_{numgens R-n..numgens R-1});
    tInvVars := apply(1..n, i-> product select((gens R)_{numgens R-n..numgens R-1}, j-> last baseName j != i));
    Tinv := diagonalMatrix(toList tInvVars);
    L1 := matrix{(gens R)_{0..m1-1}}*A1*T;
    L2 := matrix{(gens R)_{m1..m1+m2-1}}*A2*Tinv;
    C := matrix {(gens R)_{numgens R-n..numgens R-1}};
    phi := map(R,S,L1|L2|C);
    kernel phi
    );

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **DOCUMENTATION** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------
beginDocumentation ()    

doc ///
    Key
        ExternalActivityComplexes
    Headline
        a package for investigating affine Schubert varieties of a pair of linear spaces.
    Description
        Text
            This package provides functions for constructing and investigating coordinate rings of
	    affine Schubert varieties associated to a pair of linear spaces and several combinatorial objects
	    associated to them, including their initial ideals and their external activity complexes.
        Text
            @UL {
	    {"[BF24] Andy Berget and Alex Fink, ",
	    HREF("https://arxiv.org/abs/2412.11759", EM "The external activity complex of a pair of matroids"),
	    ", arXiv 2412.11759"},
            }@  
///

doc ///
    Key
        diagonalDilworthTruncation
        (diagonalDilworthTruncation, Matroid, Matroid)
    Headline
        compute diagonal Dilworth truncation of a pair of matroids
    Usage
        diagonalDilworthTruncation(M1,M2)
    Inputs
        M1:Matroid
	M2:Matroid
    Outputs
	:Matroid
    Description
        Text
            Given a pair of matroids, computes their diagonal Dilworth truncation as
	    defined in [BF24]. By example 4.8 in [BF24], the diagonal Dilworth truncation
	    of the fano matroid and the nonfano matroid is the uniform matroid of rank 5
	    on 7 elements.
        Example
	    F = specificMatroid "fano"
	    F' = specificMatroid "nonfano"
	    diagonalDilworthTruncation(F,F') == uniformMatroid(5,7)	    
///

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **TESTS** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------


TEST ///
--diagonal Dilworth of any M with U(1,n) should yield M
U35 = uniformMatroid(3,5);
U15 = uniformMatroid(1,5);
D = diagonalDilworthTruncation(U35,U15)
assert(diagonalDilworthTruncation(U35,U15) == U35)
///

TEST ///
--BF24 Example 4.8: Fano matroid and non-Fano matroid give U(5,7)
F7 = specificMatroid "fano"
F7' = specificMatroid "nonfano"
assert(diagonalDilworthTruncation(F7,F7') == uniformMatroid(5,7))
///

end---------------------------------------------------------------------------     

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- **SCRATCH SPACE** --
------------------------------------------------------------------------------
------------------------------------------------------------------------------

    G = groundSet M1; --assuming they have the same G for now
    possibleCircuits = drop(subsets G,1); --drop empty set
    circuitList = new MutableList;
    circuitDecomps = new MutableHashTable;
    for C in possibleCircuits do(
	if (rank(M1,C) + rank(M2,C) == #C) then (
	    circuitList#(#circuitList) = C
	    (M1C, M2C) = (M1|C, M2|C)
	    basesM1C = apply(bases M1C, i-> M1C_(toList i))
	    basesM2C = apply(bases M2C, i-> M2C_(toList i))
	    for i in basesM1C do(
	        Cdiff = sort toList((set C)-(set i))
		if any(basesM2C, i-> i == Cdiff) then (
		    circuitDecomps#C = (i,Cdiff);
		    break;
		    );
		);
	    );
	);
    circuitsFinal = apply(toList circuitList, i-> toList i);
    D = matroid(toList G, circuitsFinal, EntryMode => "circuits");
    D.cache.circuitDecomposition = circuitDecomps;
    D


    diagonalDilworthTruncation = method()

--maybe cache I1 and I2 in a hash table for each C?
diagonalDilworthTruncation(Matroid, Matroid) := Matroid => (M1,M2) -> (
    G := groundSet M1; --assuming they have the same G for now
    possibleCircuits := drop(subsets G,1); --drop empty set
    circuitList := new MutableList;
    circuitDecomps := new MutableHashTable;
    for C in possibleCircuits do(
	if (rank(M1,C) + rank(M2,C) == #C) then (
	    circuitList#(#circuitList) = C;
	    (M1C, M2C) := (M1|C, M2|C);
	    basesM1C := apply(bases M1C, i-> M1C_(toList i));
	    basesM2C := apply(bases M2C, i-> M2C_(toList i));
	    for i in basesM1C do(
	        Cdiff := sort toList((set C)-(set i));
		if any(basesM2C, i-> i == Cdiff) then (
		    circuitDecomps#C = (i,Cdiff);
		    break;
		    );
		);
	    );
	);
    circuitsFinal := apply(toList circuitList, i-> toList i);
    D := matroid(toList G, circuitsFinal, EntryMode => "circuits");
    D.cache.circuitDecomposition = circuitDecomps;
    D
    )
*-
---------------------
--Ayah's sandbox
---------------------

A23 = random(QQ^2,QQ^3);
A13 = random(QQ^1,QQ^3);

---

I = affineSchubertVariety(A23,A13)
inI = monomialIdeal leadTerm I
dual inI

----

L = matrix{{1,1,1,1},{0,1,2,3}};
I = kempfCollapsingBeta(L,L)
mingens I                                                    
inI = ideal leadTerm I
M = matroid L
flats M

mingens I
J = ideal (gens I)_{0..3,6..12}
decompose J


needsPackage "gfanInterface"
--gfan I --too slow

------------------

L = matrix{{1,1,1,1},{0,1,2,3}}
symL = symmetricPower(2,L)
loadPackage "SchurFunctors"
schur({2},L)

I = ideal mingens kempfCollapsingBeta(L,L)
gfan I



----

L3 = matrix{{1,0,1,1,1},{0,1,1,1,-1},{0,0,1,0,0}};
I = kempfCollapsingBeta(L3,L3)
transpose mingens I
M = matroid L3
flats M

------------
U23 = random(QQ^2,QQ^3);
I = kempfCollapsingBeta(U23,U23);
mingens I

----
--4 coplanar points
L = matrix{{1,0,0,1,0,0},{0,1,0,1,0,0},{0,0,1,1,0,1},{0,0,0,0,1,1}};
I = kempfCollapsingBeta(L,L);
transpose mingens I

----
--crazy example
L = matrix{
    {1,0,0,0,0,0,0},
    {0,1,0,1,0,0,1},
    {0,0,1,1,0,1,1},
    {0,0,0,0,1,1,1}
    }
I = kempfCollapsingBeta(L,L);
transpose mingens I
flatten entries mingens I
netList oo

----
U = matrix{{1,1,1,1,1},{0,1,2,3,4}};
J = kempfCollapsing(U,U)
gfan J
netList oo
transpose mingens J


M = matroid L;
flats M
------------------------------------
--Development Section
------------------------------------

restart
uninstallPackage "ExternalActivityComplexes"
restart
installPackage "ExternalActivityComplexes"
restart
needsPackage "ExternalActivityComplexes"
elapsedTime check "ExternalActivityComplexes"
viewHelp "ExternalActivityComplexes"
