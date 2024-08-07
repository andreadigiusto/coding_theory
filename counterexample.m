///////////////////////////////////////////////////////////////////////////////////////////////////
//                                    auxiliary functions                                        //
///////////////////////////////////////////////////////////////////////////////////////////////////

//computes the gaussian binomial (u,v)_q
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

//returns the Reed-Solomon code of length n=q+1 and dimension k
function ext_RS(q,k)
    n := q+1;
    return LinearCode( HorizontalJoin( Matrix([[(GF(q)!i)^j : i in [0..q-1]] : j in [0..k-1]]) , Transpose(Matrix([[GF(q)!0 : i in [1..k-1]] cat [GF(q)!1]])) ) );
end function;

//generates a list of t random distinct subcodes of dimension r of C
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
    return [LinearCode(subc_list[i]*G) : i in [1..t]];
end function;

//finds equivalence classes in a list of codes, bruteforce
function noneq_list(list)
    codes := [];
    while list ne [] do
        C := list[1];
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

//returns a match (2 equivalent codes) between 2 lists of codes of the same nonzero dimensions; if there is no match, returns a couple of zero codes
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

///////////////////////////////////////////////////////////////////////////////////////////////////
//                              sanity checks for list generation                                //
///////////////////////////////////////////////////////////////////////////////////////////////////
switch := 0;
if switch eq 1 then

//sanity check for somesubcodes: generates all binom(4,3,7)=400 distinct 3-dimensional subcodes of a random code C
C := RandomLinearCode(GF(7),8,4);
sub_list := somesubcodes(C,3,binom(4,3,7));
for i in [1..#sub_list-1] do
    for j in [i+1..#sub_list] do
        if sub_list[i] eq sub_list[j] then
            print("found two equal subcodes in the list");
            i;
            j;
            break;
        end if;
    end for;
end for;

//sanity check for noneq_list, using sub_list generated above
L := noneq_list(sub_list);
for i in [1..#L-1] do
    for j in [i+1..#L] do
        if IsEquivalent(L[i],L[j]) then
            print("found two equivalent subcodes");
            i;
            j;
            break;
        end if;
    end for;
end for;

end if;

///////////////////////////////////////////////////////////////////////////////////////////////////
//                          codes and checks for the counterexample                              //
///////////////////////////////////////////////////////////////////////////////////////////////////

C1 := LinearCode<GF(7), 8 |
    [ GF(7) | 1, 0, 0, 1, 0, 4, 6, 4 ],
    [ GF(7) | 0, 1, 0, 4, 0, 2, 3, 6 ],
    [ GF(7) | 0, 0, 1, 3, 0, 6, 0, 4 ],
    [ GF(7) | 0, 0, 0, 0, 1, 3, 6, 0 ] >;
D1 := Dual(C1);

C2 := LinearCode<GF(7), 8 |
    [ GF(7) | 1, 0, 0, 0, 6, 3, 4, 0 ],
    [ GF(7) | 0, 1, 0, 0, 4, 1, 1, 4 ],
    [ GF(7) | 0, 0, 1, 0, 1, 1, 4, 6 ],
    [ GF(7) | 0, 0, 0, 1, 4, 3, 6, 4 ] >;
D2 := Dual(C2);

//mu_1 of all codes: since each of them contains a word of weight 8, mu_1 = 1
print("mu_1");
#WordsOfBoundedWeight(C1,8,8) ne 0;
#WordsOfBoundedWeight(D1,8,8) ne 0;
#WordsOfBoundedWeight(C2,8,8) ne 0;
#WordsOfBoundedWeight(D2,8,8) ne 0;

//mu_2 of all codes: M always indicates a 2-dimensional MDS subcode
print("mu_2");
M := LinearCode<GF(7), 8 |
    [ GF(7) | 1, 0, 1, 4, 2, 2, 4, 1 ],
    [ GF(7) | 0, 1, 3, 6, 2, 5, 1, 4 ] >;
8 + 1 eq Dimension(M) + MinimumDistance(M);
sub<C1|M>;

M := LinearCode<GF(7), 8 |
    [ GF(7) | 1, 0, 4, 1, 3, 4, 1, 1 ],
    [ GF(7) | 0, 1, 3, 3, 6, 4, 4, 5 ] >;
8 + 1 eq Dimension(M) + MinimumDistance(M);
sub<D1|M>;

M := LinearCode<GF(7), 8 |
    [ GF(7) | 1, 0, 4, 4, 5, 5, 2, 5 ],
    [ GF(7) | 0, 1, 5, 6, 5, 3, 1, 2 ] >;
8 + 1 eq Dimension(M) + MinimumDistance(M);
sub<C2|M>;

M := LinearCode<GF(7), 8 |
    [ GF(7) | 1, 0, 6, 2, 5, 3, 4, 2 ],
    [ GF(7) | 0, 1, 2, 6, 3, 5, 4, 5 ] >;
8 + 1 eq Dimension(M) + MinimumDistance(M);
sub<D2|M>;

//mu_3 of C1 and C2: M is a 3 dimensional MDS subcode of both C1 and C2
print("mu_3");
M := C1 meet C2;
8 + 1 eq Dimension(M) + MinimumDistance(M);

//mu_3 of D1 and D2 
    //computations of the lists of nonequivalent 3-dimensional subcodes of D1, D2 and the extended RS code of dimension 4
M4 := ext_RS(7,4);
t := binom(4,3,7);
list_D1 := noneq_list(somesubcodes(D1,3,t));
list_D2 := noneq_list(somesubcodes(D2,3,t));
list_M4 := noneq_list(somesubcodes(M4,3,t));
    //neither D1 or D2 contains a 3-dimensional MDS subcode: this in particular implies mu_4(C1)=mu_4(C2)=6
Maximum([MinimumDistance(list_D1[i]) : i in [1..#list_D1]]) lt 6;
Maximum([MinimumDistance(list_D2[i]) : i in [1..#list_D2]]) lt 6;
    //mu_3(D2) = 4
M := D2 meet M4;
Dimension(M) eq 3;
    //mu_3(D1) > 4: there is no match between the lists of 3 dimensional subcodes of M4 and D1
list_match(list_D1,list_M4) eq [ZeroCode(GF(7),8),ZeroCode(GF(7),8)];