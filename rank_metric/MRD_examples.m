// examples of nonequivalent/notable MRD codes in F_q^(nxm)


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// q=2
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
q := 2;
K := GF(q);
    //n = m = 4
n := 4;
m := 4;
Fnm := KMatrixSpace(K,n,m);
    //the 3 nonequivalent MRD codes with d = 4, from Aman, Enumerating semifields, 2013, and references
V := VectorSpace(K,n);
e1 := V![1,0,0,0];  //=1
e2 := V![0,1,0,0];  //=2
e3 := V![0,0,1,0];  //=4
e4 := V![0,0,0,1];  //=8
    //GF(16)
c1 := Matrix([e1,e2,e3,e4]);
c2 := Matrix([e2,e1+e2,e4,e3+e4]);
c3 := Matrix([e3,e4,e2+e3,e1+e2+e4]);
c4 := Matrix([e4,e3+e4,e1+e2+e4,e1+e3+e4]);
gen := [c1,c2,c3,c4];
M1 := sub<Fnm|gen>;
    //T(35), should be the one equivalent to Alberto's example on cov rad/maximality degree
c1 := Matrix([e1,e2,e3,e4]);
c2 := Matrix([e2,e1+e2,e3+e4,e3]);
c3 := Matrix([e3,e4,e2,e1+e2]);
c4 := Matrix([e4,e3+e4,e1,e2]);
gen := [c1,c2,c3,c4];
M2 := sub<Fnm|gen>;
    //V(12)
c1 := Matrix([e1,e2,e3,e4]);
c2 := Matrix([e2,e3,e2+e4,e1+e4]);
c3 := Matrix([e3,e4,e1+e3+e4,e2+e4]);
c4 := Matrix([e4,e1+e3,e2,e3+e4]);
gen := [c1,c2,c3,c4];
M3 := sub<Fnm|gen>;
