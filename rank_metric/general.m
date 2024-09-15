//code is written to operate with n <= m, C \subseteq F_q^{n \times m}

//q-binomial
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

//encodes a vector w.r.to a given basis B
function rk_Enc(coeff,B)
    K := BaseRing(B[1]);
    if #coeff lt #B then
        coeff := coeff cat [0 : i in [1..#B-#coeff]];
    end if;
    return &+[K!coeff[i]*B[i] : i in [1..#B]];
end function;

//given a subspace C of a matrix vector space, computes the minimum rank by brute force listing
function MinRank(C)
    Cs := Exclude([x : x in C],C!0);
    d,b := Minimum([Rank(x) : x in Cs]);
    return d;
end function;

//rank weight distribution of C
function rk_WeightDistr(C)
    n := NumberOfRows(C!0);
    distr := [0 : i in [0..n]];
    words_list := [x : x in C];
    for x in words_list do
        distr[Rank(x) + 1] +:= 1;
    end for;
    return distr;
end function;

//rank weight distribution of an MRD code
function MRD_WeightDistr(n,m,d,q)
    nu := (n - d + 1);
    return [1] cat [binom(n,i,q) * &+([0] cat[(-1)^j * q^(Binomial(j,2)) * binom(i,j,q) * (q^(m*(nu-n+i-j))-1) : j in [0..i-d]]) : i in [1..n]];
end function;

//computes the dual of a code C using the vectorisation isomorphism
function rk_Dual(C)
    q := #BaseRing(C!0);
    n := NumberOfRows(C!0);
    m := NumberOfColumns(C!0);
    Fnm := KMatrixSpace(GF(q),n,m);
    basis := Basis(C);
    rows := Rows(ParityCheckMatrix(LinearCode(Matrix([Eltseq(basis[i]) : i in [1..#basis]]))));
    return sub<Fnm|[Matrix(n,m,rows[i]) : i in [1..#rows]]>;
end function;

//computes the covering radius of C
function rk_CovRad(C,ub_input,lb_input)
    q := #BaseRing(C!0);
    n := NumberOfRows(C!0);
    m := NumberOfColumns(C!0);
    Fnm := KMatrixSpace(GF(q),n,m);
    D := rk_Dual(C);
    WD := rk_WeightDistr(D)[2..n+1];
    e := 0;
    for i in [1..#WD] do
        if WD[i] ne 0 then
            e +:= 1;
        end if;
    end for;

    ub_list := ub_input cat [n , n-MinRank(D)+1, e];   //obvious bound, dual distance bound, external distance bound
    lb_list := lb_input cat [Ceiling((MinRank(C) - 1) / 2)];    //packing radius bound
    ub,pos1 := Minimum(ub_list);
    lb,pos2 := Maximum(lb_list);

    case pos1:
        when 1:
        printf "upper bound is n\n";
        when 2:
        printf "upper bound is from dual distance bound\n";
        when 3:
        printf "upper bound is from external distance bound\n";
    end case;

    printf "upper bound: %o\n", ub;
    printf "lower bound: %o\n", lb;

    if ub eq lb then
        printf "upper and lower bound coincide\n";
        return ub;
    end if;

    r := lb;
    space_list := [x : x in Fnm];
    code_list := [x : x in C];

    for x in code_list do
        Exclude(~space_list,x);
    end for;

    while space_list ne [] do
        y := Representative(space_list);
        coset_list := [y+x : x in C];
        minrk_coset, p := Minimum([Rank(z) : z in coset_list]);
        if minrk_coset eq ub then
            return minrk_coset;
        elif minrk_coset gt r then
            r := minrk_coset;
        end if;
        for z in coset_list do
            Exclude(~space_list,z);
        end for;
    end while;

    return r;
end function;

//creates a list of l random subcodes of C of dimension t
function rk_somesubcodes(C,t,l)
    K := BaseRing(C!0);
    k := Dimension(C);
    B := Basis(C);
    if t gt k then
        return "wrong parameters";
    end if;
    code_list := [];
    while #code_list lt l do
        coeff := RandomMatrix(K,t,k);
        if Rank(coeff) eq t then
            subcode := sub< Fnm | [rk_Enc(Eltseq(Rows(coeff)[i]),B) : i in [1..t]] >;
            if subcode notin code_list then
                Append(~code_list,subcode);
            end if;
        end if;
    end while;
    return code_list;
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