//examples MDS weights (to COPYPASTE in magma, do not load or it's a mess)

//general purpose code (can also load "mu_invariant.m" instead)

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

//generates all subcodes of dimension r: only use for SMALL PARAMETERS
function allsubcodes(C,r)
    q := #Alphabet(C);
    n := Length(C);
    k := Dimension(C);
    if k eq r then
        return [C];
    end if;
    generators := {};
    W := WordsOfBoundedWeight(C,1,n);
    while W ne {} do
        x := Representative(W);
        Include(~generators,x);
        for a in [0..q-1] do
            Exclude(~W,a*x);
        end for;
    end while;
    gen_sets := Subsets( generators , r);
    x := #gen_sets;
    subc_list := [];
    for i in [1..x] do
        ExtractRep(~gen_sets,~generators);
        C1 := sub<C|generators>;
        if C1 notin subc_list then
            Append(~subc_list,C1);
        end if;
    end for;
    return subc_list;
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

//generates an extended RS code of length n = q+1 and dimension k
function ext_RS(q,k)
    n := q+1;
    return LinearCode( HorizontalJoin( Matrix([[(GF(q)!i)^j : i in [0..q-1]] : j in [0..k-1]]) , Transpose(Matrix([[GF(q)!0 : i in [1..k-1]] cat [GF(q)!1]])) ) );
end function;

//computes the list of all nonequivalent subcodes of all dimensions (in a somehow smarter way goddammit)
function sub_codim_1(C)
    n := Length(C);
    k := Dimension(C);
    q := #Alphabet(C);
    if k eq 1 then
        return [ZeroCode(GF(q),n)]; 
    end if;
    a,list := somesubcodes(C,k-1,binom(k,k-1,q));
    return equiv_in_list(list);
end function;

function all_sub(C)
    n := Length(C);
    k := Dimension(C);
    q := #Alphabet(C);
    list := [C];
    LIST := [list];
    for i in [2..k] do
        list := equiv_in_list(&cat[sub_codim_1(list[i]) : i in [1..#list]]);
        Append(~LIST,list);
    end for;
    //Append(~LIST,[ZeroCode(GF(q),n)]);
    return Reverse(LIST);
end function;

function list_match(l1,l2)
    n := Length(l1[1]);
    q := #Alphabet(l1[1]);
    for i in [1..#l1] do
        for j in [1..#l2] do
            if IsEquivalent(l1[i],l2[j]) then
                return [l1[i],l2[j]];
            end if;
        end for;
    end for;
    return [ZeroCode(GF(q),n),ZeroCode(GF(q),n)];
end function;

function str_match(listC,listM)
    mu := #listM;
    l := Minimum(#listC,#listM);
    matches := [];
    for i in [1..l] do
        Append(~matches,list_match(listC[i],listM[i]));
    end for;
    return [[Dimension(matches[i,1]),mu] : i in [1..#matches]];
end function;

function mu_lookup(listC,allM)
    k := #listC;
    m := #allM;
    matches := [str_match(listC,allM[i]) : i in [1..m]];
    mu := [0 : i in [1..k]];
    for i in [1..k] do
        for j in [i..m] do
            if matches[j,i,1] ne 0 then
                mu[i] := matches[j,i,2];
                break;
            end if;
        end for;
    end for;
    return mu;
end function;

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//examples
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //example 1: notice muC[3] is still unknown, either 4 or 5
            if false then

q := 7;
K := GF(q);
n := q+1;     //!! every MDS is extended RS
k := 4;
Id_k := GeneratorMatrix(UniverseCode(K,k));
GC := HorizontalJoin( Id_k , Matrix(GF(7),[[0,1,5,5],[5,6,2,5],[3,4,6,3],[6,6,1,3]]) );
C := LinearCode(GC);

M1 := LinearCode( Matrix(GF(7),[[1,2,1,2]])*GC );
M2 := LinearCode(Matrix(GF(7),[[1,0,3,4,5,2,6,5],[0,1,4,4,6,4,2,1]]));
M3 := ext_RS(q,5);
M4 := M3;
muC := [1,2,5,5];
McodesC := [M1,M2,M3,M4];

D := Dual(C);
GD := GeneratorMatrix(D);

N1 := LinearCode(Matrix(GF(7),[[2,2,3,4]])*GD);
N2 := Dual(M4);
N3 := N2;
N4 := Dual(M2);
muD := [1,3,3,6];       //these weights are sure! proving duality would imply muC[3]=5
McodesD := [N1,N2,N3,N4];

//checks

    sub<C|M1>;
    sub<C|M2>;
    subcode_explorer(C,3);      //returns 0 cause there are no MDS subcodes of dimension 3 in C (already takes some seconds: need a more efficient way!)
    sub<M4|C>;       //C is a subcode of codimension 1 of the extended RS of dimension 5

    sub<D|N1>;
    subcode_explorer(D,2);      //returns 0 cause there are no MDS subcodes of dimension 2 in D
    sub<D|N3>;
    sub<N4|D>;

    //brute force checking that there is no 4dimensional MDS code intersecting C in dim 3
    // if such a codes existed, then the intersection would be a subcode of C that is equivalent to a subcode of dimension 3 of ext_RS(q,4)
l1,l2 := somesubcodes(C,3,binom(Dimension(C),3,q));        //generates all the subcodes of C od dimension 3
noneq := equiv_in_list(l2);                     //then only keeps nonequivalent ones

    //to be subcode of an MDS of dimension 4, the minimum distance should be at least 5
ind := [];
for i in [1..#noneq] do
    if MinimumDistance(noneq[i]) ge 5 then
        Append(~ind,i);
    end if;
end for;
cand := [noneq[i] : i in ind];      //sanity check: #cand:=34

//option 2: a code in cand has the desired MDS ext iff it is equivalent to a 3 dimensional subcode of the ext_RS of dimension 4
M := ext_RS(q,4);
m1,m2 := somesubcodes(M,3,binom(k,3,q));        //generates all the subcodes of M od dimension 3
m_noneq := equiv_in_list(m2);                     //then only keeps nonequivalent ones; sanity check: #m_noneq=5
for i in [1..#m_noneq] do
    i;
    for j in [1..#cand] do
        if IsEquivalent(m_noneq[i],cand[j]) then
            W := cand[j];
            subM := m_noneq[i];
            break;
        end if;
    end for;
end for;

//option 2: a code in cand has the desired MDS ext iff its dual has an MDS subcode of codimension 1
for i in [1..#cand] do
    i;
    E := Dual(cand[i]);
    F := subcode_explorer(E,4);
    if F ne ZeroCode(K,n) then
        print("found the witness for mu_3=4");
        W := Dual(F);
        W;
    end if;
end for;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //example 2
    //missing muC[3]
q := 7;
K := GF(q);
n := q+1; 
M4 := ext_RS(q,4);
GM4 := GeneratorMatrix(M4);                         
R := Matrix(GF(7),[[1,0,1,2,3,6,7,8]]);
C := LinearCode(VerticalJoin(GM4,R));    
GC := GeneratorMatrix(C);

M1 := LinearCode( Matrix(GF(7),[[1,1,1,1,2]])*GC );
M2 := subcode_explorer(M4,2);
//M3 :=
//M4 defined above (obs: it is self dual!)
muC := [1,2,0,4,7];

D := Dual(C);
GD := GeneratorMatrix(D);

N1 := LinearCode( Matrix(GF(7),[[1,2,1]])*GD );
N2 := M4;       //checked via subcode_explorer, then equivalent subcode procedure to chek subcodes of dimension 2 of M3
N3 := M4;

M5 := Dual(N1);

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //example 3: sum of two MDS codes
q := 7;
K := GF(q);
n := q+1;
M3 := ext_RS(q,3);
M4 := ext_RS(q,4);
C := M3 + M4;

M1 := LinearCode(Matrix(K,[[1,3,2,6,2,5,2,2]]));
M2 := subcode_explorer(M4,2);
M5 := UniverseCode(K,n);        //because MinimumDistance(C) eq 1;

muC := [1,2,3,4,8];

D := Dual(C);       //obs : muC[5] eq 8 => muD[i] ne i for all i

N1 := D meet M2;
N2 := D meet M3;
N3 := M4;

muD := [2,3,4];

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //example 4: the one showing inequivalence with Elisa's invariant
q := 7;
K := GF(q);
n := q+1;
RS3 := ext_RS(q,3);
RS4 := ext_RS(q,4);
GC := Matrix(K,[[1,0,6,1,2,5,6,4],[0,1,2,3,4,5,6,0]]);
C := LinearCode(GC);
M1 := LinearCode((Vector([1,1])*GC));
M2 := RS4;
McodeC := [M1,M2];
muC := [1,4];
//check that C is not a two dimensional subcode of a 3 dim MDS
m1,m2 := somesubcodes(RS3,2,binom(3,2,q));        //generates all the subcodes of RS3 od dimension 3
m_noneq := equiv_in_list(m2); 
for i in [1..#m_noneq] do
    if IsEquivalent(m_noneq[i],C) then
        i;
        break;
    end if;
end for;

D := Dual(C);

N2 := subcode_explorer(RS4,2);
N3 := RS3;          //not actually RS3, but an equivalent; can be checked by finding that C is a subcode of something equiv to ext_RS(q,5)
                    //M52 := LinearCode(Matrix(K,[[1,0,6,3,2,6,3,2],[0,1,6,3,4,3,4,1]]));
                    //IsEquivalent(C,M52);
N4 := RS4;
N5 := ext_RS(q,6);      //or something equiv; check via subcodes, long but not unfeasible
N6 := Dual(M1);
muD := [1,2,3,4,6,7];

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

        end if;