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

//
function sorted_seq(n)
    list := AllSequences(n);
    sort := [[] : i in [0..n]];
    for i in [1..#list] do
        Append(~sort[#list[i]+1],list[i]);
    end for;
    return sort;
end function;

//computes the shortening generalised weights
function mu(C,M)
    n := Length(C);
    d := n - Dimension(M) + 1;
    supp := sorted_seq(n);
    profile := [ [ Maximum( [Dimension(ShortenCode(C,supp[i,j]))]  : j in [1..#supp[i]]) , i-d ] : i in [d+1..n+1] ];
    return profile;
end function;