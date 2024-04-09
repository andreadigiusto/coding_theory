//Euler-Mascheroni constant
EMconst := 0.5772156649;

qary_bin := function(n,k,q)
    card := 1;
    for i in [0..k-1] do
        card := card * ((q^n-q^i)/(q^k-q^i));
    end for;

    return card;
end function;

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

DimPar := function(n,q)

    ExpDim := 0;
    VarDim := 0;
    TotCodes := 0;

    for i in [0..n] do
        q_bin := qary_bin(n,i,q);
        ExpDim := ExpDim + i * q_bin;
        y := (i-n/2)^2 * q_bin;
        VarDim := VarDim + y;
        TotCodes := TotCodes + q_bin;
    end for;

    ExpDim := ExpDim / TotCodes;
    VarDim := RealField()! (VarDim / TotCodes);

    if (n mod 2) eq 0 then
    //    x := (qary_bin(n,n/2,q) / TotCodes);
        Num := 0;
        Den := 0;
        for j in [1..n/2] do
            P := q^(-j^2);
            Num := Num + j^2 * P;
            Den := Den + P;
        end for;
        Limit := RealField()!((2 * Num) / (1 + 2 * Den));
    //    y := (qary_bin(n,(n+2)/2,q) / TotCodes);
    //    z := (qary_bin(n,(n+4)/2,q) / TotCodes);
    else 
        Num := 0;
        Den := 0;
        for j in [0..(n-1)/2] do
            P := q^(-j * (j+1));
            Num := Num + (j + 0.5)^2 * P;
            Den := Den + P;
        end for;
        Limit := RealField()!( Num / Den);
    end if;

    return ExpDim , VarDim, Limit, VarDim-Limit;
end function;

ExpDist := function(n,q,samples)
    d := 0;
    x := 0;
    for i in [1..samples] do
        k := Random([0..n]);
        C := RandomLinearCode(GF(q),n,k);
        sample_dist := MinimumDistance(C);
        d := d + sample_dist;
    end for;
    d := RealField()!(d / samples);
    return d;
end function;

DistDistr := function(n,k,q,samples)
    DVect := [0 : i in [0..n]];
    for i in [1..samples] do
        if k eq 0 then
            DVect[1] := DVect[1] + 1;
        else
            C := RandomLinearCode(GF(q),n,k);
            d := MinimumDistance(C);
            DVect[d+1] := DVect[d+1] + 1;
        end if;
    end for;
//    ExpDVect := [qary_bin(n,k,q) : k in [0..n]];
    return DVect;
end function;

//samples a uniformly random code of length n over F_q
UnifRandomCode := function(n,q)
    V := [];
    W := [];
    S := 0;
    for k in [0..n] do
        qbin := binom(n,k,q);
        S := S + qbin;
        Append(~V,qbin);
        Append(~W,S);
    end for;

    b := Random([1..S]);

    if b eq 1 then
        dim := 0;
    end if;
    
    for k in [1..n] do
        if (W[k] lt b) and (b le W[k+1]) then
            dim := k;
        end if;
    end for;

    C := RandomLinearCode(GF(q),n,dim);
    return C;

end function;


UnifDist := function(n,q,samples)
    D := [0 : i in [0..n]];

    V := [];
    W := [];
    S := 0;
    for k in [0..n] do
        qbin := binom(n,k,q);
        S := S + qbin;
        Append(~V,qbin);
        Append(~W,S);
    end for;

    for i in [1..samples] do
        b := Random([1..S]);
        if b eq 1 then
            dim := 0;
        end if;
        for k in [1..n] do
            if (W[k] lt b) and (b le W[k+1]) then
                dim := k;
            end if;
        end for;

        C := RandomLinearCode(GF(q),n,dim);
        d := MinimumDistance(C);
        D[d+1] := D[d+1] + 1;
    end for;

    Distr := [RealField(3)!D[d]/samples : d in [1..n+1]];
    dist, pos := Maximum(Distr);
    dist := RealField(3)!((pos - 1) / n);

    return dist, Distr;
end function;

function DimDistr(n,q,samples)
    KVect := [0 : i in [0..n]];
    for i in [1..samples] do
        C := UnifRandomCode(n,q);
        k := Dimension(C);
        KVect[k] := KVect[k] + 1;
    end for;

    KVect := [RealField(3)!(KVect[i]/samples) : i in [1..n+1]];

//    if n mod 2 eq 0 then
//        l := n/2;
//        tot := RealField(5)!(1 + 2 * (&+[1/q^(i^2) : i in [1..l]]));
//        Half := [RealField(5)!((1/q^(i^2))/tot) : i in [1..l]];
//        KLim := Reverse(Half) cat [RealField(5)!(1/tot)] cat Half;
//    else
//        l := (n-1) / 2;
//        tot := RealField(5)!(2 + 2 * (&+[1/q^(i^2) : i in [1..l]]));
//        Half := [RealField(5)!((1/q^(i^2))/tot) : i in [0..l]];
//        KLim := Reverse(Half) cat Half;
//    end if;
//
//    DiffList := [KVect[i]-KLim[i] : i in [1..n+1]];

    return KVect;

end function;

function DimLim(n,q)
    BinVect := [binom(n,i,q) : i in [0..n]];
    sum := &+BinVect;
    V1 := [RealField(5)!(BinVect[i]/sum) : i in [1..n+1]];

    if n mod 2 eq 0 then
        l := n/2;
        theta3 := &+[1/(q^(i^2)) : i in [-l..l]];
        V2 := [RealField(5)!1/(theta3*q^((i^2))) : i in [-l..l]];
    else
        l := (n+1)/2;
        theta2 := 2 * &+[1/(q^(i*(i-1))) : i in [1..l]];
        V2 := [RealField(5)!(1/theta2*q^(i*(i-1))) : i in [1..l]];
        V2 := Reverse(V2) cat V2;
    end if;

    return V1, V2;
//    [V1[i]-V2[i] : i in [1..n+1]];
end function;

function DistDistr(n,k,q,samples)
    V := [0 : i in [0..n]];
    F_q := GF(q);
    avg := 0; 
    for i in [1..samples] do
        C := RandomLinearCode(F_q,n,k);
        d := MinimumDistance(C);
        V[d+1] := V[d+1] + 1;
        avg := avg + d;
    end for;
    DDistr := [RealField(3)!(V[i]/samples) : i in [1..#V]];
    //a,b := Maximum(DDistr);
    return DDistr, RealField(3)!avg/samples; //a , RealField(3)!(b/n)
end function;

//computes q-ary entropy of x
function H(q,x)
    return x * Log(q,q-1) - x * Log(q,x) - (1-x) * Log(q,1-x);
end function;

function HammingWeight(list)
    w := 0;
    for i in [1..#list] do
        if list[i] ne 0 then
            w := w+1;
        end if;
    end for;
    return w;
end function;

//samples a number according to a binomial distribution of parameters 0<1-1/q<1 and n
function BinomialDistr(q,n)
    counter := 0;
    for i in [1..n] do
        if Random(q-1) ne 0 then
            counter := counter + 1;
        end if;
    end for;
    return counter;
end function;

//samples (q^k-1)/(q-1) vectors in F_q^n, computes the minimum of their weights
function ugly_Gumbel(n,k,q,samples)
    DDistr := [0 : i in [0..n]];
    for l in [1..samples] do
        min := n;
        for i in [1..(q^k-1)/(q-1)] do
            w := BinomialDistr(q,n);
            if w lt min then
                min := w;
            end if;
        end for;
        DDistr[min+1] := DDistr[min+1] + 1;
    end for;
    return [RealField(3)!DDistr[i]/samples : i in [1..n+1]];
end function;

function Exp_d(n,k,q)
    const := (q^k-1)/((q-1)*q^n);
    v := const;
    i := 0;
    while v le 1 do
        u_n := v;
        d0 := i;
        i := i + 1;
        v := v + const * Binomial(n,i) * (q-1)^i;
    end while;
    return d0, RealField(5)!u_n;
end function;

function Gumbel_dmin(n,q,d0,u_n)
    cdf := [];
    for s in [-d0-1..n] do
        Append(~cdf,RealField(3)!(1-Exp( - u_n * (( (q-1)*(n-d0) ) / (d0))^s)) );
    end for;
    pdf := [cdf[i+1]-cdf[i] : i in [1..#cdf-1]];

    alpha := Log(((q-1)*(n-d0))/d0);  
    avg := d0 - (EMconst/alpha) - (Log(u_n)/alpha);
    return pdf,avg;
end function;

function KD_distr(n,q,samples)
    Table := [[RealField(5)!0 : i in [0..n]] : i in [0..n]];
    p := RealField(5)!1/samples;
    for i in [1..samples] do
        C := UnifRandomCode(n,q);
        Table[Dimension(C)+1,MinimumDistance(C)] := Table[Dimension(C)+1,MinimumDistance(C)] + p;
    end for;
    return Table;
end function;

function KD_cov(n,q,avg_d)
    
end function;

function dist_general(n,q,samples)
    distr := [RealField(3)!0 : i in [0..n]];
    const := 1/samples;
    for i in [1..samples] do
        C := UnifRandomCode(n,q);
        d := MinimumDistance(C);
        distr[d] := distr[d] + const;
    end for;
    return distr;
end function;

function RadiusDistr(n,k,q,samples)
    V := [0 : i in [0..n]];
    F_q := GF(q);
    avg := 0; 
    for i in [1..samples] do
        C := RandomLinearCode(F_q,n,k);
        r := CoveringRadius(C);
        V[r+1] := V[r+1] + 1;
        avg := avg + r;
    end for;
    DDistr := [RealField(3)!(V[i]/samples) : i in [1..#V]];
    //a,b := Maximum(DDistr);
    return DDistr, RealField(3)!avg/samples; //a , RealField(3)!(b/n)
end function;

function rate_density(n,q,e)
    a := Floor(n * e);
    qbin_list := [binom(n,j,q) : j in [0..n]];
    S := &+qbin_list;
    if n mod 2 eq 0 then
        p := &+qbin_list[(n div 2)-a..(n/2)+a];
    else
        p := &+qbin_list[(n+1)/2-a..(n-1)/2+a];
    end if;
    return RealField(5)!p/S;
end function;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//random code
aaaaaaaaaa := 0;
if aaaaaaaaaa eq 1 then
//scarto nel numero di info set per codici random
q := 13;
n := 10;
k := 5;
samples := 100;
function rand_IS(q,n,k,samples)
    avg := 0;
    for i in [1..samples] do
        C := RandomLinearCode(GF(q),n,k);
        avg := avg + RealField(5)!(Binomial(n,k)-#AllInformationSets(C))/Binomial(n,k);
    end for;
    return avg/samples;
end function;


end if;