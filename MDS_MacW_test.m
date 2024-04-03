//SetPath("C:\Documents\GitHub\coding_theory");

MacWMatr := function (n,k,q)

    Matr := [];
    for j in [0..n] do

        Row := [];
        for i in [0..n] do
            Coeff := (&+[ Binomial(n-t,j-t)*Binomial(n-i,t)*(-1)^(j-t)*q^t : t in [0..j]]) / q^k;
            Append(~Row,Coeff);
        end for;
        Append(~Matr,Row);
    end for;

    Matr := Matrix(Matr);

    for i in [2..n+1] do
        SwapColumns(~Matr,1,n+3-i);
    end for;

    for i in [2..n+1] do
        SwapRows(~Matr,1,n+3-i);
    end for;

    return Matr;
end function;

MDSMacWLeftMatr := function (n,k,q)

    Matr := [];
    for nu in [0..n] do
        d := n - nu + 1;

        Row := [];
        for i in [0..n] do
            list1 := [ Binomial(i,t)*(-1)^(i-t) : t in [0..d-1]];
            if list1 eq [] then
                list1 := [0];
            end if;

            list2 := [ Binomial(i,t)*(-1)^(i-t)*q^(t-d+1) : t in [d..n]];
            if list2 eq [] then
                list2 := [0];
            end if;

            Coeff := (((&+list1) + (&+list2)) / (q-1)^i) * q^(n-k);

            if Coeff lt 0 then
                print("negative weight at");
                nu,i;
            end if;

            if (i eq q+1) and (nu eq n-q+1) then
                Coeff;
            end if;

            Append(~Row,Coeff);
        end for;
        Append(~Matr,Row);
    end for;
    
    Matr := Matrix(Matr);
    //Matr;

    for i in [2..n+1] do
        SwapColumns(~Matr,1,n+3-i);
    end for;

    return Matr;
end function;

MDSMacWRightMatr := function (n,k,q)

    Matr := [];
    for nu in [0..n] do
        d := nu + 1;

        Row := [];
        for i in [0..n] do
            list1 := [ Binomial(i,t)*(-1)^(i-t) : t in [0..d-1]];
            if list1 eq [] then
                list1 := [0];
            end if;

            list2 := [ Binomial(i,t)*(-1)^(i-t)*q^(t-d+1) : t in [d..n]];
            if list2 eq [] then
                list2 := [0];
            end if;
            
            Coeff := ((&+list1 + &+list2) / (q-1)^i) * q^(nu);

            if (i eq q+1) and (nu eq q-1) then
                Coeff;
            end if;

            Append(~Row,Coeff);
        end for;
        if nu eq (n-k) then
            Row;
        end if;
        Append(~Matr,Row);
    end for;

    Matr := Matrix(Matr);
    //Matr;

    for i in [2..n+1] do
        SwapColumns(~Matr,1,n+3-i);
    end for;

    return Matr;
end function;

WGen := function(n,k,q)

    C := RandomLinearCode(GF(q),n,k);
    Cperp := Dual(C);
    WDistr := WeightDistribution(C);
    WDistr;
//    WeightDistribution(Cperp);
    W := [];

    for i in [0..n] do
        switch := 0;
        for j in [1..#WDistr] do
            if WDistr[j][1] eq i then
                Append(~W,Rationals()!WDistr[j][2]);
                switch := 1;
            end if;
        end for;
        if switch eq 0 then
            Append(~W,Rationals()!0);
        end if;
    end for;

    return (Rotate(W,-1));
end function;

Test := function(n,k,q)
    W := WGen(n,k,q);

    print("Krawtchouk matrix");
    A := MacWMatr(n,k,q);
    A;
    print("left matrix");
    B := MDSMacWLeftMatr(n,k,q);
    B;
    print("left^(-1)");
    B^(-1);
    print("right matrix");
    C := MDSMacWRightMatr(n,k,q);
    C;
    print("right^(-1)");
    C^(-1);
    print("right^(-1) * left");
    D := C^(-1) * B;
    D;
    W := Transpose(Matrix([W]));
    print("dual weight distribution");
    A*W;
    print("equality tests");
    return A*W eq D*W, A eq D;
end function;

//n := 7;
//k := 2;
//q := 3;
//W := [Rationals()!(Binomial(n,i)*(q-1)^i) : i in [0..n]];
//Test(n,k,q);

//computes the i-th weight of an MDS code of dimension k, length
function MDSWeight(i,k,n,q)
    d := n - k + 1;
    
    if i eq 0 then
        weight := 1;
    elif i lt d then
        weight := 0;
    else
        sum := 0;
        for j in [0..i-d] do
            sum := sum + (-1)^j * Binomial(i,j) * (q^(i+1-d-j)-1);
        end for;
        weight := Binomial(n,i) * sum;
    end if; 
    return weight;
end function;

//computes the size of the hamming ball of radius r = n
function Hball_size(r,n,q)
    ball := 1;
    shell := 1;
    for i in [1..r] do
        shell := shell * (q-1) * (n-i+1) / i;
        ball := ball + shell;
    end for;
    return ball;
end function;

function check(n,q)
    for i in [0..n] do
        for a in [0..n] do
            sum := 0;
            for j in [0..n] do
                sum := sum + (MDSWeight(j,n-a,n,q) * Evaluate(KrawchoukPolynomial(GF(q),n,i),j)); // / (Binomial(n,j) * (q-1)^j));
            end for;
            LHS := sum;
            RHS := q^(n-a) * MDSWeight(i,a,n,q); // / (Binomial(n,i)*(q-1)^i);
            LHS eq RHS;
            if LHS ne RHS then
                LHS;
                RHS;
                return 11234567890098765432112345678900987654321123456789009876543211234567890098765432112345678900987654321;
            end if;
        end for;
    end for;
    return 0;
end function;

function check1(a,n,q)
    for i in [0..n] do
        for j in [0..n] do
            lhs := MDSWeight(j,a,n,q) * Evaluate(KrawchoukPolynomial(GF(q),n,i),j);
            rhs := MDSWeight(i,n-a,n,q) * q^a;
            lhs eq rhs;
        end for;
    end for;
    return 0;
end function;

function WeightEnCheck(n,k,q)
    Q<x,y> := PolynomialRing(RationalField(),2);
    pol1 := Q!0;
    pol2 := Q!0;
    pol3 := Q!0;

    for j in [1..n-k] do
        pol1 := pol1 + Binomial(n-1-j,k-1) * x^j * y^(n-k-j);
    end for;
    pol1 := (x-y)^k * pol1;

    for i in [1..k] do
        pol2 := pol2 + Binomial(n-1-i,n-1-k) * (x+(q-1)*y)^i * (x-y)^(k-i);
    end for;
    pol2 := y^(n-k) * pol2;

    pol4 := pol1 + pol2;
    pol4;

    for i in [0..n] do
        pol3 := pol3 + MDSWeight(i,k,n,q) * x^(n-i) * y^i;
    end for;

    pol3;

    return pol4 eq pol3;

end function;

//auxiliary function to generate distinct subsequences of [1..n] in a decent way
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

//computes the weights defined as mu_r(C)=min{s : for every support S of cardinality S, rk(G(C)_S)>=r}
//input is a code (not its gen.matrix)
function MDSweight_1(C)
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

//check condition for nestability of MDS codes
function nest_check(n,q)
    b := 0;
    for t in [1..n-1] do
        b := b + Binomial(n,t) * (q-1)^(t);
        c := (q^t-1) * q;
        b le c;
    end for;
    return 0;
end function;

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
    #generators;
    set_nu := SetToIndexedSet(Subsets( generators , nu));
    x := #set_nu;
    for i in [1..x] do
        C1 := sub<C|set_nu[i]>;
        if MinimumDistance(C1) eq n-nu+1 and Dimension(C1) eq nu then
            return C1;
        end if;
    end for;
    return 0;
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

//returns the product v * M (component wise on columns)
//v vector, M matrix
function gen_prod(v,M)
    n := #v;
    for i in [1..n] do
        MultiplyColumn(~M,v[i],i);
    end for;
    return M;
end function;

//intersection of C with all codes in the monomial equivalence class of M
function equiv_meet1(C,M)
    n := Length(C);
    k := Dimension(C);
    Fq := Alphabet(C);
    check := [0 : i in [0..k]];
    getout := 0;
    U := UniverseCode(Fq,n);
    witness_codes := [U : i in [0..k]];
    Perm := [g : g in SymmetricGroup(n)];
    num_perm := Factorial(n);
    Scale := nonzero_list(#Fq,n);
    #Scale;
    for i in [1..#Scale] do
        G1 := gen_prod(Scale[i],GeneratorMatrix(M));
        i;
        for j in [1..num_perm] do
            M1 := LinearCode(G1^Perm[j]);
            r := Dimension(M1 meet C);
            if check[r+1] eq 0 then
                witness_codes[r+1] := M1;
                check[r+1] := 1;
                getout := getout + 1;
            end if;
            if getout eq k+1 then
                break;
            end if;
        end for;
        if getout eq k+1 then
            break;
        end if;
    end for;
    return witness_codes, [[r,Dimension(witness_codes[r])] : r in [1..k+1]];
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
                    witness_codes[r+1] := M;
                    witness_scale[r+1] := s;
                    witness_perm[r+1] := p;
                    mu[r+1] := dimM[l]; 
                end if;
            end for;
        end for;
    end for;
    return mu, witness_codes, witness_scale, witness_perm;
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

//generates an extended RS code of length n = q+1 and dimension k
function ext_RS(q,k)
    n := q+1;
    return LinearCode( HorizontalJoin( Matrix([[(GF(q)!i)^j : i in [0..q-1]] : j in [0..k-1]]) , Transpose(Matrix([[GF(q)!0 : i in [1..k-1]] cat [GF(q)!1]])) ) );
end function;

//checks the LP bound obtained from our identities vs the standard one
//everything ending in K is related to the standard (Krawchuck) LP bound, everything ending in M is related to the new (MDS-weight) LP bound
function LP_bound_par(n,d,q)

    Q := RationalField();
    vect := [Q!1] cat [Q!0 : i in [1..n]];
    lhs := [Rotate(vect,i) : i in [0..d-1]];
    obj := [[1 : i in [0..n]]];
    
    lhs_K := lhs;
    lhs_M := lhs;

    rhs_K := [[1]] cat [[0] : i in [1..d-1]] cat [[0] : i in [0..n]];
    rhs_M := [[1]] cat [[0] : i in [1..d-1]] cat [[(q^k*((1/(q-1)^k)+q^(1-d)-(q^(1-d)/(q-1)^k)))] : k in [0..n]];

    rel_K := [[0] : i in [1..d]] cat [[1] : i in [0..n]];
    rel_M := [[0] : i in [1..d]] cat [[-1]: i in [0..n]];

    for nu in [0..n] do
        pol_K := KrawchoukPolynomial(GF(q),n,nu);
        Append(~lhs_K,[Evaluate(pol_K,i) : i in [0..n]]);
    end for;

    for nu in [0..n] do
        Append(~lhs_M,[(MDSWeight(i,nu,n,q)/(Binomial(n,i)*(q-1)^i)) : i in [0..n]]);
    end for;

    //Matrix(Q,lhs_M),Matrix(rel_M),Matrix(Q,rhs_M), Matrix(Q,obj);

    //LP_K := MaximalIntegerSolution(Matrix(Q,lhs_K),Matrix(rel_K),Matrix(Q,rhs_K), Matrix(Q,obj));

    //LP_M := MaximalIntegerSolution(Matrix(Q,lhs_M),Matrix(rel_M),Matrix(Q,rhs_M), Matrix(Q,obj));

    return Matrix(Q,lhs_K),Matrix(rel_K),Matrix(Q,rhs_K), Matrix(Q,lhs_M),Matrix(rel_M),Matrix(Q,rhs_M), Matrix(Q,obj);
end function;

//n := 6;
//d := 4;
//q := 7;

//lhs_K, rel_K, rhs_K, lhs_M, rel_M, rhs_M, obj := LP_bound_par(n,d,q);

//LP_K := MaximalIntegerSolution(lhs_K,rel_K,rhs_K,obj);
//LP_K[1];
//LP_M := MaximalIntegerSolution(lhs_M,rel_M,rhs_M,obj);
//LP_M[1];