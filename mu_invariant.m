//code for computations around the MDS intersection invariant

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//general purpose code
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//gaussian binomial
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

//returns the product v * M (component wise on columns)
//v vector, M matrix
function gen_prod(v,M)
    n := #v;
    for i in [1..n] do
        MultiplyColumn(~M,v[i],i);
    end for;
    return M;
end function;

//applies the permutation specified by list to the columns of the matrix G
//TODO
function gen_perm(p,G)
    for i in [1..#p] do
        SwapColumns(~G,p[1],p[i]);
    end for;
    return G;
end function;

//generate all lists of length n of nonzero elements in GF(q)
function nonzero_list(q,n)
    F := GF(q);
    list1 := [[GF(q)!i] : i in [1..q-1]];
    list2 := [];
    for i in [1..n-1] do
        for j in [1..#list1] do
            for l in [1..q-1] do
                Append(~list2,Append(list1[j],F!l));
            end for;
        end for;
    list1 := list2;
    list2 := [];
    end for;
    return list1;
end function;

//auxiliary function to generate distinct subsequences of [1..n] in a decent way (ascending sequences)
function AllSequences(n)
    if n eq 1 then
        list := [[],[1]];
    else
        list := AllSequences(n-1);
        m := #list;
        for i in [1..m] do
            Append(~list,list[i] cat [n]);
        end for;
    end if;
    return list;
end function;

//brute force samples a random MDS code of params n, k ,q (attempts is the number of tries before spitting the universe code)
function random_MDS(q,n,k,attempts)
    U := UniverseCode(GF(q),n);
    for i in [1..attempts] do
        M := RandomLinearCode(GF(q),n,k);
        if MinimumDistance(M) eq n - Dimension(M) + 1 and M ne U then
            return M;
        end if;
    end for;
    return U;
end function;

//generates an extended RS code of length n = q+1 and dimension k
function ext_RS(q,k)
    n := q+1;
    return LinearCode( HorizontalJoin( Matrix([[(GF(q)!i)^j : i in [0..q-1]] : j in [0..k-1]]) , Transpose(Matrix([[GF(q)!0 : i in [1..k-1]] cat [GF(q)!1]])) ) );
end function;

//builds a code according to the procedure described in "More MDS codes of non-Reed-Solomon type"
//C2 has length n+3, with dimension 3<=k<=n-1
//a = [a1,...,an] and ai,delta,tau,pi in GF(q)
function C2_constr(k,q,a,delta,tau,pi)
    K := GF(q);
    n := #a;
    B1 := Matrix(K,[[a[j]^i : j in [1..n]] : i in [0..k-1]]);
    B2 := Transpose(Matrix(K,[[0 : i in [1..k-1]] cat [1],[0 : i in [1..k-2]] cat [1,delta],[0 : i in [1..k-3]] cat [1,tau,pi]]));
    G := HorizontalJoin(B1,B2);
    C := LinearCode(G);
    return C;
end function;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//specific purpose code
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//check for MDS subcodes of dimension nu of a code C
function subcode_explorer(C,nu)
    q := #Alphabet(C);
    n := Length(C);
    generators := {};
    W := Words(C,n-nu+1);
    while W ne {} do
        x := Representative(W);
        Include(~generators,x);
        for a in [0..q-1] do
            Exclude(~W,a*x);
        end for;
    end while;
    gen_sets := Subsets( generators , nu);
    x := #gen_sets;
    MDSlist := [];
    for i in [1..x] do
        ExtractRep(~gen_sets,~generators);
        C1 := sub<C|generators>;
        if MinimumDistance(C1) eq n-nu+1 and Dimension(C1) eq nu then
            return C1;    //Append(~MDSlist,C1);
        end if;
    end for;
    return ZeroCode(GF(q),n);
end function;

//intersection of the equivalence class of C with some MDS codes in a sequence listM;
//the codes in listM must be listed in ascending order wrto dimension
function equiv_meet2(C,listM)
    n := Length(C);
    k := Dimension(C);
    Fq := Alphabet(C);
    G := GeneratorMatrix(C);
    m := #listM;
    dimM := [Dimension(listM[i]) : i in [1..m]];

    S := SymmetricGroup(n);
    U := UniverseCode(Fq,n);
    witness_codes := [U : i in [0..k]];
    witness_scale :=[[1 : i in [1..n]] : j in [0..k]];
    witness_perm := [S!(1) : i in [0..k]];
    mu := [n : i in [0..k]];
    Perm := [g : g in S];
    num_perm := Factorial(n);
    Scale := nonzero_list(#Fq,n);
    (#Fq-1)^n;
    for i in [1..#Scale] do
        i;
        s := Scale[i];
        G1 := gen_prod(s,G);
        for j in [1..num_perm] do
            p := Perm[j];
            C1 := LinearCode(G1^p);
            for l in [1..m] do
                M := listM[l];
                r := Dimension(C1 meet M);
                if dimM[l] lt mu[r+1] then
//                    witness_codes[r+1] := M;
                    GM := GeneratorMatrix(M);
                    witness_codes[r+1] := LinearCode(gen_prod([s[j]^(-1) : j in [1..n]],GM^(p^(-1))));
                    witness_scale[r+1] := s;
                    witness_perm[r+1] := p;
                    mu[r+1] := dimM[l]; 
                end if;
            end for;
        end for;
    end for;
    return mu, witness_codes, witness_scale, witness_perm;
end function;

//finds random MDS codes of dimension nu and intersection with C of dim = r (code_att = # of MDS codes generated, gen_att is attempts in the function above)
function random_MDS_meet(C,nu,code_att,gen_att)
    n := Length(C);
    k := Dimension(C);
    q := #Alphabet(C);
    G := [g : g in Sym(n)];
    U := UniverseCode(GF(q),n);
    mu_list := [n : i in [1..k]];
    code_list := [U : i in [1..k]];
    for i in [1..code_att] do
        M := random_MDS(q,n,nu,gen_att);
        if M ne U then
            for j in [1..#G] do
                pM := M^G[j];
                r := Dimension(pM meet C);
                if r ne 0 then
                    mu_r := Dimension(pM);
                    if mu_r lt mu_list[r] then
                        mu_list[r] := mu_r;
                        code_list[r] := pM;
                    end if;
                end if;
            end for;
        end if;
    end for;
    return mu_list, code_list;
end function;

//computes 
function random_equiv_meet(C,M,attempts,input_list)
    n := Length(C);
    k := Dimension(C);
    q := #Alphabet(C);
    A := AutomorphismGroup(UniverseCode(GF(q),n));
    AM := AutomorphismGroup(M);
    aut := [];
    for i in [1..attempts] do
        t := Random(A);
        if t notin AM and t notin aut and t notin input_list then
            Append(~aut,t);
        end if;
    end for;
    princt("chek");
    for i in [1..attempts]
    r,witness := Maximum([Dimension(M^t meet C) : t in aut]);
    return r,witness,aut;
end function;

//ranges nu in the function above from 1 to n-1 (code_att and gen_att are the same as above)
//dim_ub (dim_lb) = upper (lower) bound on dimension nu, <=Length(C)-1 (>=1)
function list_MDS_meet(C,code_att,gen_att,dim_lb,dim_ub)
    mu_record := [];
    codes := [];
    for nu in [dim_lb..dim_ub] do     
        nu;                               
        mu_list, code_list := random_MDS_meet(C,nu,code_att,gen_att);
        Append(~mu_record,mu_list);
        Append(~codes,code_list);
        nu;                               
    end for;
    mu_list := [];
    witness_codes := [];
    for r in [1..Dimension(C)] do
        r;
        [mu_record[l][r] : l in [1..#mu_record]];
        mu_r, pos := Minimum([mu_record[l][r] : l in [1..#mu_record]]);
        mu_r;
        Append(~mu_list,mu_r);
        Append(~witness_codes,codes[pos][r]);
    end for;
    return mu_list,witness_codes;
end function;

//C is a code, code_att=# of MDS generations per dimension, gen_att=# of attempts allowed to generate an MDS code
function MDSweight2(C,code_att,gen_att,lb,ub)
    n := Length(C);
    q := #Alphabet(C);
    kC := Dimension(C);
    D := Dual(C);
    kD := n - kC;

    muC := [[i,n-kC+i] : i in [0..kC]];
    muD := [[i,n-kD+i] : i in [0..kD]];

    
end function;
//alternative defs
//computes the weights defined as mu_r(C)=min{s : for every support S of cardinality S, rk(G(C)_S)>=r}
//input is a code (not its gen.matrix)
function MDSweight1(C)
    n := Length(C);
    k := Dimension(C);
    M := GeneratorMatrix(C);
    weights := [{i} : i in [0..k]];
    rows := [i : i in [1..k]];
    cols := Prune(Reverse(AllSequences(n)));    //Prune(Reverse()) is just to take the empty list out
    for j in [1..#cols] do
        s := #cols[j];
        w := Rank(Submatrix(M,rows,cols[j]));
        Include(~weights[w+1],s);
    end for;
    return weights;
end function;

//random extension of codes to find non MDS codes with 2 coinciding weights mu_r (ideally C is a non-nestable MDS code)
function randomext(C,attempts)
    n := Length(C);
    q := #Alphabet(C);
    k := Dimension(C);
    G := GeneratorMatrix(C);
    switch := 0;
    counter := 0;
    att_codes := [];
    Target := ZeroCode(GF(q),n);
    while switch eq 0 and counter lt attempts do
        G1 := VerticalJoin(G,Matrix([[Random(GF(q)) : i in [1..n]]]));
            if Rank(G1) eq k+1 and G1 notin att_codes then
                Append(~att_codes,G1);
                counter := counter + 1;
                Cext := LinearCode(G1);
                D := subcode_explorer(Cext,k-1);
                if D eq ZeroCode(GF(q),n) then
                    Target := Cext;
                    switch := 1;
                end if;
            end if;
    end while;
    return Target;
end function;

//generates t random subcodes of dimension r of C
function somesubcodes(C,r,t)
    K := Alphabet(C);
    k := Dimension(C);
    spaces_list := [];
    G := GeneratorMatrix(C);
    subc_list := [];
    for i in [1..t] do
        S := RandomMatrix(K,r,k);
        RowS := RowSpace(S);
        while Rank(S) ne r or RowS in spaces_list do
            S := RandomMatrix(K,r,k);
            RowS := RowSpace(S);
        end while;
        Append(~subc_list,S);
        Append(~spaces_list,RowS);
    end for;
    return subc_list,[LinearCode(subc_list[i]*G) : i in [1..t]];
end function;

//finds equivalence classes in a list of codes, bruteforce
function equiv_in_list(list)
    codes := [];
    while list ne [] do
        C := Representative(list);
        Append(~codes,C);
        list1 := [];
        for i in [1..#list] do
            if IsEquivalent(C,list[i]) eq false then
                Append(~list1,list[i]);
            end if;
        end for;
        list := list1;
    end while;
    return codes;
end function;

//brute force tries to augment a subcode D of C to an MDS code of target dimension nu using vectors outside C
function extend_to_MDS(D,C)

end function;

//brute force checking for MDS sovracodes

//duality: kperp := Dimension(Dual(C)), mu = [mu_r(C) : r in [1..Dimension(C)]] 
function beta_C(kperp,mu)
    return [ kperp+r-mu[r] : r in [1..#mu] ];
end function;

//computes the sum of corresponding weights of C and Dual(C) under the correspondence given by beta_C
function duality(mu,mu_perp)
    l := beta_C(#mu_perp,mu);
    return [mu[r]+mu_perp[l[r]] : r in [1..#mu]];
end function;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//examples
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//q := 11;
//n := 8;      //for n =q+1, q>=k, all MDS codes are equivalent to an extended RS
//k := 4;

//C := RandomLinearCode(GF(q),n,k);

//random meets
//list_MDS_meet(C,100,1000,1,n-1);

//extended RS invariant
//listM := [ext_RS(q,j) : j in [1..n-1]];
//mu, witness_codes, witness_scale, witness_perm := equiv_meet2(C,listM);
//sanity check
//for i in [1..#witness_codes] do
//    Dimension(C meet witness_codes[i]);
//end for;
