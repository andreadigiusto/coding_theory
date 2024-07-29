//one-time commands

readfile := function(N)
    s := Read(N);
    OB := eval s;
    return OB;
end function;

load "mu_examples.m";
Mlist := readfile("sub_lists_7.m");

//iterable commands

data := readfile("examples_[8,4]7.m");
codes := data[1];
G := RandomMatrix(GF(7),4,8);
C := LinearCode(G);
D := Dual(C);
for i in [1..#data[1]] do
    if IsEquivalent(C,data[1,i]) or IsEquivalent(D,data[1,i]) then
        i;
        break;
    end if;
end for;
Clist := all_sub(C);
Dlist := all_sub(D);
mu_lookup(Clist,Mlist);
mu_lookup(Dlist,Mlist);
Append(~data[1],C);

//PrintFileMagma("namefile.m" , print_obj : Overwrite:=true); prints file WITH overwrite