//support functions

//q-binomials
function binom(u,v,q);
    f:=0;
    if u le -1 or v le -1 then;
    f:=0;
    end if;
    if v eq 0 and u ge 0 then;
    f:=1;
    end if;
    if v ge 1 and u le v-1 then;
    f:=0;
    end if;
    if v ge 1 and u ge v then;
    P:=1;
    Q:=1;
    for i in [0..v-1] do;
    P:=P*(q^(u-i)-1);
    end for;
    for i in [0..v-1] do;
    Q:=Q*(q^(i+1)-1);
    end for;
    f:=P/Q;
    end if;
    return f;
end function;

//comuptes the support of a code
function code_support(C)
    k := Dimension(C);
    G := GeneratorMatrix(C);
    S := {};
    for i in [1..k] do
        S := S join Support(G[i]);
    end for;
    return S;
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

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//parameters

k_U := 7;
k_V := 3;
n := k_U + k_V;
q := 3;

//code

function Wave_GM(q,k_U,k_V)
    n := k_U + k_V;
    F := GF(q);
    U := RandomLinearCode(F,n,k_U);
    V := RandomLinearCode(F,n,k_V);
    GU := GeneratorMatrix(U);
    GV := GeneratorMatrix(V);
    a := [1 : i in [1..n]];
    b := [Random(F) : i in [1..n]];
    c := [Random([1,2]) : i in [1..n]];
    d := [1 + c[i]*b[i] : i in [1..n]];
    GaUcU := HorizontalJoin(GU,gen_prod(c,GU));
    GbVdV := HorizontalJoin(gen_prod(b,GV) , gen_prod(d,GV));
    GW := VerticalJoin( GaUcU , GbVdV );
    return GW,a,b,c,d;         //GaUcU, GbVdV;
end function;

switch1 := 0;
if switch1 eq 1 then
    GW,a,b,c,d := Wave_GM(q,k_U,k_V);
    C := LinearCode(GW);
    R :=RandomLinearCode(GF(q),2*n,n);
    Dimension(Hull(R));
    Dimension(Hull(C));
    GWT := Transpose(GW);
    for i in [1..n] do
        VerticalJoin(~GWT,GWT[n+i]);
    end for;
    GWext := Transpose(GWT);
    Cext := LinearCode(GWext);
    Rext := RandomLinearCode(GF(q),Length(Cext),n);
    Dimension(Hull(Cext));
    Dimension(Hull(Rext));
end if;

//n is half the length of the final code
function Wave_code(q,n,k_U,k_V)
    F := GF(q);
//    switch := 0;
//    while switch eq 0 do
//        U := RandomLinearCode(F,n,k_U);
//        V := RandomLinearCode(F,n,k_V);
//        if #(U meet V) eq 1 then
//            switch := 1;
//        end if;
//    end while;
    U := RandomLinearCode(F,n,k_U);
    V := RandomLinearCode(F,n,k_V);
    GU := GeneratorMatrix(U);
    GV := GeneratorMatrix(V);
    a := [1 : i in [1..n]];
    b := [Random(F) : i in [1..n]];
    c := [Random([1,2]) : i in [1..n]];
    d := [1 + c[i]*b[i] : i in [1..n]];
    GW := VerticalJoin( HorizontalJoin(GU,gen_prod(c,GU)), HorizontalJoin(gen_prod(b,GV),gen_prod(d,GV)) );
    return LinearCode(GW);
end function;

//Wave_code(q,n,k_U,k_V);

//switch := 0;
//attempts := 10000;

//Sebastian attack

//appends m distinct random columns of M to M
function add_cols(m,M)
    n := NumberOfColumns(M);
    A := Transpose(M);
    list := [i : i in [1..n]];
    //added_list := [];
    for i in [1..m] do
        j := Random(list);
        Exclude(~list,j);
        //Append(~added_list,j);
        VerticalJoin(~A,A[j]);
    end for;
    return Transpose(A);
end function;

Wave := 1;        // =1 for Wave, =0 for random
function Hull_distr(q,n,k_U,k_V,attempts,Wave)
    distr := [RealField(5)!0 : i in [1..n]];
    l := RealField(5)!1/attempts;
    if Wave eq 1 then
        for i in [1..attempts] do
            W := Wave_code(q,n,k_U,k_V);
            W_ext := LinearCode(add_cols(n,GeneratorMatrix(W)));
            h := Dimension(Hull(W_ext));
            distr[h+1] := distr[h+1] + l;
        end for;
    elif Wave eq 0 then
        for i in [1..attempts] do
            C := RandomLinearCode(GF(q),2*n,k_U+k_V);
            C_ext := LinearCode(add_cols(n,GeneratorMatrix(C)));
            h := Dimension(Hull(C_ext));
            distr[h+1] := distr[h+1] + l;
        end for;
    end if;
    return distr;
end function;

//Hull_distr(q,n,k_U,k_V,attempts,Wave);

//random v Wave
//average number of 2 dimensional subcodes supported on t columns of an [n,k] random code, t=1..n
function dim2_suppt(n,k,q)
    return [RealField(3)! (Binomial(n,t) * (binom(k,2,q) / binom(n,2,q)) * (((q^2-1)^t-(q-1)^(t+1)) / ((q^2-1)*(q^2-q)))) : t in [1..n]];
end function;

//supports of subcodes of dimension t by random sampling
function supp_dimt_subc(C,t,attempts)
    F := Alphabet(C);
    n := Length(C);
    k := Dimension(C);
    G := GeneratorMatrix(C);
    supports := [0 : j in [1..n]];
    for i in [1..attempts] do
        A := RandomMatrix(F,t,k);
        SubC := LinearCode(RandomMatrix(F,t,k)*GeneratorMatrix(C));
        s := #code_support(SubC);
        supports[s] := supports[s] + 1;
    end for;
    return supports;
end function;

//average difference in the number of info sets between random and Wave
//needs lot of space (does not work on student version)
avg_diff := 0;
att := 100;
for i in [1..att] do
    W:=Wave_code(q,n,k_U,k_V);
    C := RandomLinearCode(GF(q),2*(k_U+k_V),k_U+k_V);
    w:=#AllInformationSets(W);
    c:=#AllInformationSets(C);
    avg_diff:=avg_diff + c-w;
    c-w;
end for;
RealField()!(avg_diff/att);