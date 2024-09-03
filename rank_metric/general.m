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

//creates Gabidullin code in matrix form
function Gabidullin_code(n,m,d,q)
    k := n - d + 1;
    K := GF(q);
    Km := GF(q^m);
    Fnm := KMatrixSpace(K,n,m);
    B := Basis(Km,K)[1..n];
    V := VectorSpace(Km,n);
    W := sub< V | [V![B[i]^(q^j) : i in [1..n]] : j in [0..k-1]]>;
    return sub<Fnm | [ Matrix([ Eltseq(w[i]) : i in [1..n]]) : w in W ] >;
end function;