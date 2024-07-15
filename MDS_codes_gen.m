//various families/interpretations of MDS codes

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Reed Solomon codes

//the built-in functions ReedSolomonCode generate codes of length n=q-1

//codes from "Jin-Construction of MDS Codes With Complementary Duals-2017"
//generate GRS codes GRS(a,P(x),v)

q := 7;
K<x> := PolynomialRing(GF(q));
P := RandomIrreduciblePolynomial(GF(q),3);
a := [GF(q)!i : i in [0..q-1]];
v := [GF(q)!1 : i in [0..q-1]];
function GRS_P(a,P,v)
    n := #a;
    k := Degree(P);     //the dimension of the code is the degree of P
    z := [Evaluate(P,a[i]) : i in [1..n]];
    for i in [1..n] do
        if z[i] eq 0 then
            print("invalid sequence a/ polynomial P");
            return 0;
        end if;
    end for;
    u := [v[i]/z[i] : i in [1..n]];
    return GRSCode(a,u,k);
end function;
