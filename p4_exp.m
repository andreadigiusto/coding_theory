/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//general purpose code
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

function Hamming_Ball(r,n,q)
    U := UniverseCode(GF(q),n);
    return WordsOfBoundedWeight(U,0,r);
end function;

//computes q-ary entropy of x
function H(q,x)
    return x * Log(q,q-1) - x * Log(q,x) - (1-x) * Log(q,1-x);
end function;

//computes the size of the hamming ball of radius r <= n
function Hball_size(r,n,q)
    ball := 1;
    shell := 1;
    for i in [1..r] do
        shell := shell * (q-1) * (n-i+1) / i;
        ball := ball + shell;
    end for;
    return ball;
end function;

//returns the product v * M (component wise on columns)
//v vector, M matrix
function gen_prod(v,M)
    n := #v;
    for i in [1..n] do
        MultiplyColumn(~M,v[i],i);
    end for;
    return M;
end function;

//computes the Schur product of two linear codes by computing the products of the generators and generating the code
function Schur_prod(A,B)
    n := Length(A);
    K := Alphabet(A);
    if Length(B) ne n or K ne Alphabet(B) then
        return "the input codes do not have the same length/alphabet";
    end if;
    GA := GeneratorMatrix(A);
    GB := GeneratorMatrix(B);
    SchurG := Matrix([[K!0 : i in [1..n]]]);
    for i in [1..Dimension(A)] do
        v := [GA[i,j] : j in [1..n]];
        SchurG := VerticalJoin(SchurG,gen_prod(v,GB));
    end for;
    return LinearCode(SchurG);
end function;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// specific purpose code
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//computes the ratio of the size of the error set of the split channel with random errors of weights up to w1,w2 to the ball of radius w=w1+w2
//w2<w1 is assumed; the total length is 2n
function Err_ratio(w1,w2,n,q)
    Err_size := Hball_size(w2,n,q) * (2 * Hball_size(w1,n,q) - Hball_size(w2,n,q));
    return RealField(3)!(Err_size/Hball_size(w1+w2,2*n,q));
end function;

//computes the rate between sizes of the difference sets for the error sets specified for the function Err_ratio above
//w2<w1 is assumed; the total length is 2n
function diffSet_ratio(w1,w2,n,q)
    diffSet_size := Hball_size(2*w2,n,q)^2 + 2 * Hball_size(2*w2,n,q) * (Hball_size(2*w1,n,q) - Hball_size(2*w2,n,q)) + (Hball_size(w1+w2,n,q) - Hball_size(2*w2,n,q))^2;
    return RealField(3)!(diffSet_size/Hball_size(2*(w1+w2),2*n,q));
end function;

//finds a code A to complement B as an error correcting couple for C with (dim(C) ge dim)
function findA(B,t,dim,attempts)
    n := Length(B);
    K := Alphabet(B);
    for i in [1..attempts] do
        A := RandomLinearCode(K,n,t+1);
        C := Dual(Schur_prod(A,B));
        if MinimumDistance(A) + MinimumDistance(C) gt n and Dimension(C) ge dim then
            print("found an error locating pair");
            return A,C;
        end if;
    end for;
    print("did not find a pair");
    return A,C;
end function;

//experiment for augmenting codes
q := 7;
n := 7;
G := [[ 1, 1, 1, 1, 1, 1, 1 ],
      [ 0, 1, 2, 3, 4, 5, 6 ],
      [ 0, 1, 4, 2, 2, 4, 1 ]];
C := LinearCode< GF(q) , n | G >;
CC := LinearCode< GF(q) , 2*n | [G[i] cat G[i] : i in [1..3]] >;
A := GeneratorMatrix(CC); 
B := VerticalJoin(A,Matrix(GF(q),[[0,0,0,0,1,2,3,4,5,0,0,0,0,0],[0,0,0,0,0,1,2,3,4,5,0,0,0,0]]));
CCC := LinearCode(B);
V := AmbientSpace(CCC);
y := Random(CCC) + V![0,0,0,0,0,0,0,1,2,3,0,0,0,0];