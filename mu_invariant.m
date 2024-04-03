//code for computations around the MDS intersection invariant

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//general purpose code
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//specific purpose code
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//examples
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//q := 5;
//n := q+1;      //for n =q+1, q>=k, all MDS codes are equivalent to an extended RS
//k := 4;

//C := RandomLinearCode(GF(q),n,k);
//listM := [ext_RS(q,j) : j in [1..n-1]];
//mu, witness_codes, witness_scale, witness_perm := equiv_meet2(C,listM);
//sanity check
//for i in [1..#witness_codes] do
//    Dimension(C meet witness_codes[i]);
//end for;
