load "ExternalActivityComplexes.m2"

L1 = matrix {
    {1,1,1,1,1,1},
    {1,2,3,4,5,6}
    }

-- L1 = matrix {
--     {1,1,1,1,1,1},
--     {1,2,3,4,5,6},
--     {1,4,9,16,25,36}
--     }

-- L1 = matrix{
--     {1,0,0,1,1,1},
--     {0,1,0,1,2,2},
--     {0,0,1,1,2,3}
--     }

L1perp = transpose gens ker L1

I1perp = kempfCollapsingBeta(L1,L1perp)

n = numcols L1
kk = QQ
r = numrows L1

-- tracking the multigrading
S = kk[x_1..x_n,y_1..y_n,z_1..z_n, Degrees => flatten {toList (n:{1,0,0}), toList (n:{0,1,0}), toList (n:{0,0,1})}];

Tm = tuttePolynomial matroid L1

A = QQ[T_0..T_3,MonomialOrder=>GLex];

BESTtutte = (A_1+A_2)^(r) * (A_0+A_3)^(n-r) * sub(Tm, {x=>(A_0+A_1)/(A_1+A_2), y => (A_0+A_1)/(A_0+A_3)}) / (A_0+A_1);

segreTutte = A_2^(n-1) * A_1^(r) * A_0^(n-r) * BESTtutte(0,1/A_2,1/A_1,1/A_0)

multidegree sub(I1perp, S)

