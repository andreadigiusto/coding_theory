//code is written to operate with n <= m

//given a subspace C of a matrix vector space, computes the minimum rank by brute force listing
function MinRank(C)
    Cs := Exclude([x : x in C],C!0);
    d,b := Minimum([Rank(x) : x in Cs]);
    return d;
end function;

//computes the dual of a code C using the vectorisation isomorphism
function Dual(C)
    q := #BaseRing(C!0);
    n := NumberOfRows(C!0);
    m := NumberOfColumns(C!0);
    Fnm := KMatrixSpace(GF(q),n,m);
    basis := Basis(C);
    rows := Rows(ParityCheckMatrix(LinearCode(Matrix([Eltseq(basis[i]) : i in [1..#basis]]))));
    return sub<Fnm|[Matrix(n,m,rows[i]) : i in [1..#rows]]>;
end function;