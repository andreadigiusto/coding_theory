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

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//examples
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //example 1: notice muC[3] is still unknown, either 4 or 5
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
if false then
    sub<C|M1>;
    sub<C|M2>;
    subcode_explorer(C,3);      //returns 0 cause there are no MDS subcodes of dimension 3 in C (already takes some seconds: need a more efficient way!)
    sub<M4|C>;       //C is a subcode of codimension 1 of the extended RS of dimension 5

    sub<D|N1>;
    subcode_explorer(D,2);      //returns 0 cause there are no MDS subcodes of dimension 2 in D
    sub<D|N3>;
    sub<N4|D>;
end if;
    //brute force checking that there is no 4dimensional MDS code intersecting C in dim 3
    // if such a codes existed, then the intersection would be a subcode of C that is equivalent to a subcode of dimension 3 of ext_RS(q,4)
l1,l2 := somesubcodes(C,3,binom(k,3,q));        //generates all the subcodes of C od dimension 3
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
            D := cand[j];
            subM := m_noneq[i];
            break;
        end if;
    end for;
end for;

//option 2: a code in cand has the desired MDS ext iff its dual has an MDS subcode of codimension 1
if false then
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
end if;
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////