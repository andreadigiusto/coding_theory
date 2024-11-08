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

//exponent for asymptotic approximation of Hamming balls
function F(q,x)
    if x le (q-1)/q then
        return H(q,x);
    else return 1;
    end if;
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

//computes the Schur product (component-wise product) of two linear codes by computing the products of the generators and generating the code
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

//computes the size of the error set; a=block length,b=#blocks,c=#err.block,w=errors per block
function split_ratio(q,a,b,c,w)
    RealField(5)!(&+[Binomial(a,j)*(q-1)^j : j in [1..w]]/q^(a*H(q,w/a)));
    exact := &+[ Binomial(b,i) * (&+[Binomial(a,j)*(q-1)^j : j in [1..w]])^i : i in [1..c]];
    appr1 := &+[Binomial(b,i) * (q^(a*H(q,w/a)))^i : i in [1..c]];
    appr2 := q^(a*c*H(q,w/a)+Log(2,q)*b*H(2,c/b));
    return RealField(5)!(exact/appr1),RealField(5)!(exact/appr2),RealField(5)!(appr1/appr2);
end function;

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

//upper bound on size of split difference set (for GV bound): a=block length, b=number of blocks, c=max corrupted blocks, w=max errors per block
function Split_diff_set(q,a,b,c,w)
    return &+[ (Binomial(b,j)*Binomial(b-j,2*(c-j))*(Hball_size(2*w,a,q)^j)*(Hball_size(w,a,q)^(2*(c-j)))) : j in [0..c]];
end function;

//upper bound on difference set split channel
function ub_split_DE(t,w,n,m,q)
    C := &+[Binomial(m,w)*Binomial(m-gamma,2*(w-gamma)) : gamma in [0..w]];
    return (Hball_size(t,n,q)^(2*w))*C;
end function;

//GV_split vs standard Hamming
function beat_Hamming(t,w,n,m,q)
    return (Log(2,Hball_size(t*w,n*m,q))-Log(2,ub_split_DE(t,w,n,m,q)))/(m*n);
end function;

//compare GV A and GV S
function compare_GVs(t,w,n,m,q)
    GVA := 1 - 2 * (w/m) * H(q,t/n);
    GVS := 1 - ((2 * (w/m) - 1) * F(q,2*(t/n)) + 2 * (1 - (w/m)) * F(q,t/n));
    GVA;
    GVS;
    return GVA - GVS;
end function;

//computes the tensor code C1 \otimes C2 (via pcm)
function TensorCode(C1,C2)
    K := Alphabet(C1);
    n := Length(C2) * Length(C1);
    d := MinimumDistance(C2);
    H1 := ParityCheckMatrix(C1);
    H2 := ParityCheckMatrix(C2);
    H := KroneckerProduct(H1,H2);
    C := Dual(LinearCode(H));
    //if Dimension(C) ge Dimension(BDLC(K,n,d)) then
    //    print("this is a good code:");
    //else 
    //    print("dio can");
    //end if;
    Dimension(C);
    //Dimension(BDLC(K,n,d));
    return C;
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

//a test to find an error corr pair for the split channel
function f1(B,A,attempts)
    K := Alphabet(A);
    n := Length(A);
    S := AutomorphismGroup(UniverseCode(K,n));
    t := n - MinimumDistance(A);
    C1 := ZeroCode(K,n);
    d1 := n;
    for i in [1..attempts] do
        x := Random(S);
        Ax := A^x;
        C := Dual(Schur_prod(Ax,B));
        d := MinimumDistance(C);
        if d lt d1 then
            C1 := C;
            d1 := d;
            print("success!");
        end if;
    end for;
    return C1;
end function;

//GTP construction (from Imai,Fujiya)
K<a> := GF(2^4);
H1 := <>;
Append(~H1, Matrix(GF(2) , [[1 : i in [0..14]]]));
Append(~H1, Transpose( Matrix(GF(2) , [ElementToSequence(a^i) : i in [0..14]] ) ));
Append(~H1, Transpose( Matrix(GF(2) , [ElementToSequence(a^(3*i)) : i in [0..14]] ) ));
Append(~H1, Transpose( Matrix(GF(2) , [ElementToSequence(a^(5*i)) : i in [0..14]] ) ));
H2 := <>;
Append(~H2, Matrix(GF(2),[[1,1,0,0,0,0,0,0],[1,0,1,0,0,0,0,0],[1,0,0,1,0,0,0,0],[1,0,0,0,1,0,0,0],[1,0,0,0,0,1,0,0],[1,0,0,0,0,0,1,0],[1,0,0,0,0,0,0,1]]));
Append(~H2, Matrix(GF(2),[[1,1,1,0,1,0,0,0],[0,1,1,1,0,1,0,0],[1,1,0,1,0,0,1,0],[1,1,1,1,1,1,1,1]]));
Append(~H2, Matrix(GF(2),[[1,1,1,1,1,1,1,1]]));
Append(~H2, Matrix(GF(2),[[1,1,1,1,1,1,1,1]]));
H := VerticalJoin(<TensorProduct(H2[i],H1[i]) : i in [1..4]>);
C := Dual(LinearCode(H));



//experiment for augmenting codes
switch := 0;
if switch eq 1 then
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
end if;

//standard construction (from "Wolf, On the codes derivable from the tensor product of check matrices")
//the redundancy of Cin must be equal to the degree of the field extension over which Cout is built
function stand_con(Cin,Cout)
    n := Length(Cin);
    m := Length(Cout);
    kin := Dimension(Cin);
    kout := Dimension(Cout);
    G := GeneratorMatrix(Cin);
    H := ParityCheckMatrix(Cin);
    G1 := G;
    H1 := H;
    for i in [1..m-1] do
        G1 := DiagonalJoin(G1,G);
        H1 := DiagonalJoin(H1,H);
    end for;
    C1 := LinearCode(G1);
    C2 := LinearCode(Matrix([Vector(&cat[Eltseq(c[i]) : i in [1..m]])*H1 : c in Cout]));
    S := C1 + C2;
    print("intersection of the two blocks");
    C1 meet C2;
    print("dimension constructed code");
    Dimension(S);
    print("expected dimension");
    m*kin+(n-kin)*kout;
    print("expected dimension tensor construction");
    m*n-(n-kin)*(m-kout);
    return S;
end function;

function gen_con(Cin,Cout1,Cout2)
    n := Length(Cin);
    m := Length(Cout);
    kin := Dimension(Cin);
    kout1 := Dimension(Cout1);
    kout1 := Dimension(Cout2);
    G := GeneratorMatrix(Cin);
    H := ParityCheckMatrix(Cin);
    G1 := G;
    H1 := H;
    for i in [1..m-1] do
        G1 := DiagonalJoin(G1,G);
        H1 := DiagonalJoin(H1,H);
    end for;
    C1 := LinearCode(Matrix([Vector(&cat[Eltseq(c[i]) : i in [1..m]])*G1 : c in Cout1]));
    C2 := LinearCode(Matrix([Vector(&cat[Eltseq(c[i]) : i in [1..m]])*H1 : c in Cout2]));
    S := C1 + C2;
    print("dimension constructed code");
    Dimension(S);
    print("expected dimension");
    kout1 * (n-kin) + kout2 * kin;
end function;