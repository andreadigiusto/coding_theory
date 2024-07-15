//MDS codes construction

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    //codes over GF(7)

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //the [6,3,4]_7 codes coming from nonequivalent arcs (see Hirschfeld, Complete arcs and references)
q := 7;
//type 1: complete
H1 := Matrix(GF(q),[[-1,1,1,-1,0,0],[1,1,-1,-1,2,3],[1,1,1,1,1,1]]);
M1 := Dual(LinearCode(H1));
//type 2: complete
H2 := Matrix(GF(q),[[-1,1,1,-1,0,0],[1,1,-1,-1,2,-3],[1,1,1,1,1,1]]);
M2 := Dual(LinearCode(H2));

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    //codes over GF(9)

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    //the classical and non classical 10-arcs in PG(4,9) (nonequivalent [10,5,6]_9 MDS codes), from Glynn, the non-classical 10-arc of PG(4,9)
G<x>:=PolynomialRing(GF(3));
K<s> := ext<GF(3)|x^2-x-1>;
P<x>:= PolynomialRing(K);
        //classical arc (extended Reed Solomon code)
aff_points:=[i : i in K];
G_1 := Matrix(K,[[Evaluate(x^i,j) : j in aff_points] : i in [0..4]]);
G_C := HorizontalJoin(G_1,Transpose(Matrix(K,[[0,0,0,0,1]])));
A_C := LinearCode(G_C);
        //non-classical arc
G_nC := Matrix(K,[[1,0,0,0,0,1,1,1,1,1],[0,1,0,0,0,1,s^5,s^4,s,s^2],[0,0,1,0,0,1,s^4,s,s^3,s^5],[0,0,0,1,0,1,s,s^7,s^6,s^4],[0,0,0,0,1,1,s^3,s^6,s^4,s]]);
A_nC := LinearCode(G_nC);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //2 nonequivalent [6,3,4]_9 codes from Jurrius PhD thesis (have same cov radius)
G<x>:=PolynomialRing(GF(3));
K<s> := ext<GF(3)|x^2-x-1>;
G1 := Matrix(K,[[1,1,1,1,1,1],[0,1,0,1,s^5,s^6],[0,0,1,s^3,s,s^3]]);
C1 := LinearCode(G1);
G2 := Matrix(K,[[1,1,1,1,1,1],[0,1,0,s^7,s^4,s^6],[0,0,1,s^5,s,1]]);  
C2 := LinearCode(G2);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //codes over GF(11)

////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    //a [6,3,4]_11 Roth-Lempel code
G := Matrix(GF(11),[[1,1,1,1,0,0],[1,2,3,4,0,1],[1,4,9,5,1,0]]);
C := LinearCode(G);