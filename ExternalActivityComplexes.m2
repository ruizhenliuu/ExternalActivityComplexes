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
    "diagonalDilworthTruncation"	  --not documented, has tests
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

---------------------
--Ayah's sandbox
---------------------
--M1 = uniformMatroid(3,5)
--M2 = uniformMatroid(1,5)
M1 = specificMatroid "fano"
M2 = specificMatroid "nonfano"
G = groundSet M1
possibleCircuits = drop(subsets G,1) 
circuitList = new MutableList
circuitHash = new MutableHashTable
for C in possibleCircuits do(
    if (rank(M1,C) + rank(M2,C) == #C) then (
	circuitList#(#circuitList) = C;
	);
    );
circuitsFinal = apply(toList circuitList, i-> toList i)
C = circuitsFinal_2
D = matroid(toList G, circuitsFinal, EntryMode => "circuits")

circuitDecomp = new MutableHashTable
for C in circuitsFinal do(
    M1C = restriction(M1,C)
    M2C = restriction(M2,C)
    
    

circuits M1
circuits M2

bases M1
bases M2

--want to keep track of I1 and I2 for each circuit...
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
