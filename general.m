//given a subspace C of a matrix vector space, computes the minimum rank by brute force listing
function MinRank(C)
    Cs := Exclude([x : x in C],C!0);
    d,b := Minimum([Rank(x) : x in Cs]);
    return d;
end function;