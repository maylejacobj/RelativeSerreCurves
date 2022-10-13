/////////////////////////////////////////////////
// Below we load the code of Zywina, Sutherland,
// and Rouse--Zureick-Brown. The file
// "2adicimage.txt" is modified to wrap the
// relevant code in a function TwoAdic(E).
/////////////////////////////////////////////////
ChangeDirectory("/Users/.../SurjectivityOfGalois");
load "SurjectivityOfGalois.m";
ChangeDirectory("/Users/.../galrep");
load "algorithms.m";
ChangeDirectory("/Users/.../2adic");
load "2adicimage.txt";

/////////////////////////////////////////////////
// Given a positive integer n, output GL(2,Z/nZ).
/////////////////////////////////////////////////
Gl := function(n)
	return GL(2,Integers(n));
end function;

/////////////////////////////////////////////////
// Given integers m,n >= 2 with n dividing m,
// output the reduction homomorphism 
// pi_{m,n} : GL_2(Z/mZ) --> GL_2(Z/nZ).
/////////////////////////////////////////////////
Red := function(m,n)
	Gm := Gl(m);
	Gn := Gl(n);
	return hom<Gm -> Gn | [<g,Gn ! g> : g in Generators(Gm)]>;
end function;

/////////////////////////////////////////////////
// Give a subgroup G of GL(2,Z/nZ) for some n,
// output the subgroup det(G) of (Z/nZ)^*.
/////////////////////////////////////////////////
Det := function(G)
	H,phi := UnitGroup(BaseRing(G));
	Gens := Generators(G);
	L := {Determinant(g) @@ phi : g in Gens};
	return sub< H | L>;
end function;

/////////////////////////////////////////////////
// Given a positive even integer n, output the
// preimage of 2Cn in GL(2,Z/nZ).
/////////////////////////////////////////////////
TwoCn := function(n)
	G := Gl(2);
	H := Subgroups(G)[3]`subgroup;
	return H @@ Red(n,2);
end function;

/////////////////////////////////////////////////
// Given a positive even integer n, output the
// preimage of 2B in GL(2,Z/nZ).
/////////////////////////////////////////////////
TwoB := function(n)
	G := Gl(2);
	H := Subgroups(G)[2]`subgroup;
	return H @@ Red(n,2);
end function;

/////////////////////////////////////////////////
// Given a positive even integer n, output the
// preimage of 2Cs in GL(2,Z/nZ).
/////////////////////////////////////////////////
TwoCs := function(n)
	G := Gl(2);
	H := Subgroups(G)[1]`subgroup;
	return H @@ Red(n,2);
end function;

/////////////////////////////////////////////////
// Given a subgroup G of GL(2,Z/nZ), output the
// constant m_1, which is the least positive
// divisor of n such that among maximal subgroups 
// K of [G,G], we have that [K(n),K(n)] \ne [G(n),G(n)].
////////////// Used in Lemma 2.5 ////////////////
// > LevelLower1(TwoCn(216));
// 36
// > LevelLower1(TwoB(216));
// 72
// > LevelLower1(TwoCs(216));
// 72
/////////////////////////////////////////////////
LevelLower1 := function(G)
	n := #BaseRing(G);
	Comm := CommutatorSubgroup(G);
	MaxSubs := MaximalSubgroups(Comm);
	for D in Exclude(Divisors(n),1) do
		Flg := true;
		CommD := Red(n,D)(Comm);
		for K in MaxSubs do
			KD := Red(n,D)(K`subgroup);
			if #KD eq #CommD then
				Flg := false;
			end if;
		end for;
		if Flg then
			return D;
		end if;
	end for;
end function;

/////////////////////////////////////////////////
// Given a subgroup G of GL(2,Z/nZ), output the
// constant m_2, which is the least positive
// divisor of n such that among subgroups K of G:
// [K(n),K(n)] = [G(n),G(n)] implies [K,K] = [G,G].
//////////////  Used in Lemma 2.5 ///////////////
// > LevelLower1(TwoB(72));
// 36	// warning: this computation takes several hours
/////////////////////////////////////////////////
LevelLower2 := function(G)
	n := #BaseRing(G);
	CommG := CommutatorSubgroup(G);
	Subs := LowIndexSubgroups(G,Integers() ! (#G/#CommG));
	for D in Exclude(Divisors(n),1) do
		Flg := true;
		for K in Subs do
			CommK := CommutatorSubgroup(K);
			CommKD := Red(n,D)(CommK);
			if CommKD eq Red(n,D)(CommG) and CommK ne CommG then
				Flg := false;
			end if;
		end for;
		if Flg then
			return D;
		end if;
	end for;
end function;

/////////////////////////////////////////////////
// Given a subgroup G of GL(2,Z/nZ) for some n,
// output the set M(G) of all subgroups H of G
// such that det(H) = det(G) and [H,H]=[G,G].
////////////// Used in Lemma 2.7 ////////////////
// FullCommDet(GL(2,Integers(9)));
// > FullCommDet(TwoCn(4)) eq {TwoCn(4),K1};
// true
// > FullCommDet(TwoB(4)) eq {TwoB(4)};
// true
// > S := {H`subgroup : H in Subgroups(TwoCs(8)) | #Det(H`subgroup) eq EulerPhi(8) and Red(8,4)(H`subgroup) in {TwoCs(4),K2,K3}};
// > T := {};
// > for H in S do
// > 	Flg := true;
// > 	for K in T do
// > 		if IsConjugate(Gl(8),H,K) then
// > 			Flg := false;
// > 		end if;
// > 	end for;
// > 	if Flg then
// > 		Include(~T,H);
// > 	end if;
// > end for;
// > #FullCommDet(TwoCs(8)) eq #T;
// true
// > FlgAll := true;
// > for H in FullCommDet(TwoCs(8)) do
// > 	Flg := false;
// > 	for K in T do
// > 		if IsConjugate(Gl(8),H,K) then
// > 			Flg := true;
// > 		end if;
// > 	end for;
// > 	FlgAll := FlgAll and Flg;
// > end for;
// > FlgAll;
// true
/////////////////////////////////////////////////
FullCommDet := function(G);
	GLn := Gl(#BaseRing(G));
	CommG := CommutatorSubgroup(G);
	Subs := LowIndexSubgroups(G,Integers() ! (#G / #CommG));
	FCDSubs := {};
	for H in Subs do
		if #Det(H) eq #Det(G) and CommutatorSubgroup(H) eq CommutatorSubgroup(G) then
			Flg := true;
			for K in FCDSubs do
				if IsConjugate(GLn,H,K) then
					Flg := false;
				end if;
			end for;
			if Flg then
				Include(~FCDSubs,H);
			end if;
		end if;
	end for;
	return FCDSubs;
end function;

/////////////////////////////////////////////////
// Constructs the subgroups K1, K2, K3 of 
// GL(2,Z/4Z). These are defined on p. 4.
/////////////////////////////////////////////////
m11 := Matrix(Integers(4),[[3,0],[0,1]]);
m12 := Matrix(Integers(4),[[1,1],[1,0]]);
K1 := sub<Gl(4)|[m11,m12]>;
m21 := Matrix(Integers(4),[[3,0],[0,1]]);
m22 := Matrix(Integers(4),[[3,0],[2,3]]);
m23 := Matrix(Integers(4),[[1,2],[0,1]]);
K2 := sub<Gl(4)|[m21,m22,m23]>;
m31 := Matrix(Integers(4),[[3,0],[0,1]]);
m32 := Matrix(Integers(4),[[3,0],[2,3]]);
m33 := Matrix(Integers(4),[[1,2],[0,3]]);
K3 := sub<Gl(4)|[m31,m32,m33]>;

/////////////////////////////////////////////////
// Given finite groups G and H, output all
// isomorphism classes of quotient groups in
// common to both G and H. 
////////////// Used in Lemma 2.8 ////////////////
// > for H in FullCommDet(TwoCn(4)) do
// >  	QuoIntersection(Gl(9),H);
// > end for;
// { <6, 2>, <1, 1>, <3, 1>, <2, 1> }
// { <6, 2>, <1, 1>, <3, 1>, <2, 1> }
// > for H in FullCommDet(TwoB(4)) do
// > 	QuoIntersection(Gl(9),H);
// > end for;
// { <1, 1>, <2, 1> }
// > for H in FullCommDet(TwoCs(8)) do
// > 	QuoIntersection(Gl(9),H);
// > end for;
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
// { <1, 1>, <2, 1> }
/////////////////////////////////////////////////
QuoIntersection := function(G,H)
	QuoG := {IdentifyGroup(G/(N`subgroup)) : N in NormalSubgroups(G) | #H mod Integers() ! (#G/#(N`subgroup)) eq 0};
	QuoH := {IdentifyGroup(H/(N`subgroup)) : N in NormalSubgroups(H) | #G mod Integers() ! (#H/#(N`subgroup)) eq 0};
	return QuoG meet QuoH;
end function;

/////////////////////////////////////////////////
// Given a subgroup G of GL(2,Z/nZ) for some m,
// output the index of the commutator subgroup
// [G,G] in SL(2,Z/nZ).
////////////// Used in Lemma 2.12 ////////////////
// > CommIndx(TwoCn(4));
// 12
// > CommIndx(TwoB(4));
// 12
// > CommIndx(TwoCs(4));
// 48
/////////////////////////////////////////////////
CommIndx := function(G)
	return Integers() ! (#SL(2,Integers(#BaseRing(G))) / #CommutatorSubgroup(G));
end function;

/////////////////////////////////////////////////
// Below we initiate the sets S_{2Cs}, S_{2B},
// and S_{2Cn} defined in the introduction. 
// See also Lemma 2.11.
/////////////////////////////////////////////////
S2Cs := {"H8","H8a","H8b","H8c","H8d","H38","H38a","H38b","H38c","H38d","H46","H46a","H46b","H46c","H46d"};
S2B := {"H6","H14","H15","H16","H17","H18","H19"};
S2Cn := {"H2","H2a","H2b"};

/////////////////////////////////////////////////
// Given G = TwoCs(8), TwoB(4), or TwoCn(4),
// output the set S_{2Cs}, S_{2B}, and S_{2Cn}, 
// respectively, as described in Lemma 2.11.
////////////// Used in Lemma 2.11 ///////////////
// > ConstructSG(TwoCs(8)) eq S2Cs;
// true
// > ConstructSG(TwoB(4)) eq S2B;
// true
// > ConstructSG(TwoCn(4)) eq S2Cn;
// true
/////////////////////////////////////////////////
ConstructSG := function(G:GpOut:=false)
	SG := [];
	GpList := [];
	m := #BaseRing(G);
	for H in FullCommDet(G) do
		for S in finesublist do
			gp := S[4];
			lbl := "H" cat Substring(S[5],2,#S[5]);
			n := #BaseRing(gp);
			if n le m then
				gp := gp @@ Red(m,n);
				n := #BaseRing(gp);
			end if;
			if IsConjugate(Gl(m), Red(n, m)(gp), H) then
				Include(~SG,lbl);
				Include(~GpList,gp);
			end if;
		end for;
		for i in [1..#newsublist] do
    		gp := newsublist[i][3];
    		lbl := "H" cat IntegerToString(i);
    		n := #BaseRing(gp);
    		if n le m then
    			gp := gp @@ Red(m,n);
    			n := #BaseRing(gp);
    		end if;
    		if IsConjugate(Gl(m), Red(n, m)(gp), H) then
    			Include(~SG,lbl);
    			Include(~GpList,gp);
    		end if;
    	end for;
	end for;
	if GpOut then
    	return [<SG[i],GpList[i]> : i in [1..#SG]];
    end if;
    return SG;
end function;

/////////////////////////////////////////////////
// Given G = TwoCs(8), TwoB(4), or TwoCn(4),
// print the number of index two subgroups of H(4),
// for each subgroup H contained in the set S_G.
////////////// Used in Sec. 3 ///////////////////
// > NumIdxTwoSubs(TwoCs(8));
// H8 15
// H8c 15
// H38 15
// H46 15
// H8a 15
// H8d 7
// H8b 7
// H46d 7
// H38a 7
// H46a 7
// H46b 7
// H38b 7
// H38c 7
// H46c 7
// H38d 7
// > NumIdxTwoSubs(TwoB(4));
// H6 7
// H14 7
// H15 7
// H16 7
// H17 7
// H18 7
// H19 7
// > NumIdxTwoSubs(TwoCn(4));
// H2a 1
// H2b 3
// H2 3
/////////////////////////////////////////////////
NumIdxTwoSubs := function(G)
    L := ConstructSG(G:GpOut:=true);
    for HH in L do
        H := Red(#BaseRing(HH[2]),4)(HH[2]);
        HH[1], #LowIndexSubgroups(H,2) - 1;
    end for;
    return "";
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q, output the set of
// prime numbers ell such that the mod ell Galois
// representation of E is non-surjective by
// calling scripts of Zywina and Sutherland.
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("66c3");
// > NonsurjPrimes(E);
// [ 2, 5 ]
/////////////////////////////////////////////////
NonsurjPrimes := function(E)
	L1 := [ell : ell in ExceptionalSet(E)];
	L2 := PossiblyNonsurjectivePrimes(E,L1,1000);
	L3 := [];
	for ell in L2 do
		if not "G" in GaloisImages(E,[ell],1000)[1] then
			Append(~L3,ell);
		end if;
	end for;
	return L3;
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q, output the image
// of the 2-adic Galois representation of E by
// calling a script of Rouse--Zureick-Brown.
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("66c3");
// > TwoAdicGroup(E);
// H15
/////////////////////////////////////////////////
TwoAdicGroup := function(E)
	Curve := TwoAdic(E)[2];
	return "H" cat Substring(Curve,2,#Curve);
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q, output whether
// the 3-adic Galois representation of E is 
// surjective by implementing a result of Elkies.
// It is sufficient to check surjectivity mod 9.
//////////////////// EXAMPLES ///////////////////
// > E := EllipticCurve("14a1"); // The mod 3 representation is nonsurjective
// > ThreeAdicIsSurjective(E);
// false
// > E := EllipticCurve("62208j1"); // The mod 3 representation is surjective, but the mod 9 is nonsurjective
// > ThreeAdicIsSurjective(E);
// false 
// > E := EllipticCurve("1944c1"); // The mod 3 representation is surjective, but the mod 9 is nonsurjective
// > ThreeAdicIsSurjective(E);
// false
// > E := EllipticCurve("11a1"); // The 3-adic representation is surjective since the mod 9 is surjective 
// > ThreeAdicIsSurjective(E);
// true
/////////////////////////////////////////////////
ThreeAdicIsSurjective := function(E)
    if not GaloisImages(E,[3],1000)[1] eq "3G" then
        return false; // The mod 3 representation is nonsurjective
    end if;
    jinv := jInvariant(E);
    if jinv eq 4374 then
        return false; // The mod 3 representation is surjective, but the mod 9 is nonsurjective
    end if;
    S<t> := PolynomialRing(Rationals());
    NumF := S ! 3^7*(t^2 -1)^3*(t^6 +3*t^5 +6*t^4 +t^3 -3*t^2 +12*t+16)^3*(2*t^3 +3*t^2 -3*t-5);
    DenF := S ! (t^3-3*t-1)^9;
    Numj := S ! Numerator(jinv);
    Denj := S ! Denominator(jinv);
    f := NumF*Denj - DenF*Numj;
    R := Roots(f);
    if #R gt 0 then
        return false; // The mod 3 representation is surjective, but the mod 9 is nonsurjective
    end if;
    return true; // The 3-adic representation is surjective since the mod 9 is surjective
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q, output <True,G> 
// if E is a G-Serre curve for a proper subgroup
// G <= GL(2,Z/2Z), and output false otherwise. 
// This function is associated with Theorem 1.1.
/////////////////////////////////////////////////
// > E := EllipticCurve("3136e2");
// > IsRelSerreCurve(E);
// <true, "2Cs">
// > E := EllipticCurve("69a1");
// > IsRelSerreCurve(E);
// <true, "2B">
// > E := EllipticCurve("392c1");
// > IsRelSerreCurve(E);
// <true, "2Cn">
// > E := EllipticCurve("15a1");
// > IsRelSerreCurve(E);
// false
// > E := EllipticCurve("338d2");
// > IsRelSerreCurve(E);
// false
/////////////////////////////////////////////////
IsRelSerreCurve := function(E)
    if not HasComplexMultiplication(E) and #Exclude(NonsurjPrimes(E),2) eq 0 and ThreeAdicIsSurjective(E) then
        Img := TwoAdicGroup(E);
        if Img in S2Cs then
            return <true,"2Cs">;
        end if;
        if Img in S2B then
            return <true,"2B">;
        end if;
        if Img in S2Cn then
            return <true,"2Cn">;
        end if;
    end if;
    return false;
end function;

/////////////////////////////////////////////////
// Given a set S an a positive integer n, output
// n minimal elements of S with respect to
// divisibility that are not 1 or 2.
//////////////////// EXAMPLE ////////////////////
// > S := { 3, 5, 7, 15, 21, 35, 105 };
// > MinWrtDiv(S,3);
// { 3, 5, 7 }
/////////////////////////////////////////////////
MinWrtDiv := function(S,n)
	T := {};
	Exclude(~S,1);
	Exclude(~S,2);
	for k in [1..n] do
		m := Minimum(S);
		Include(~T,m);
		for s in S do
			if s mod m eq 0 then
				Exclude(~S,s);
			end if;
		end for;
	end for;
	return T;
end function;

/////////////////////////////////////////////////
// Given a squarefree integer N, output N' as
// in equation (3.10) of Section 3.
//////////////////// EXAMPLE ////////////////////
// > NPrime(30);
// -15
/////////////////////////////////////////////////
NPrime := function(N)
	if N mod 4 eq 1 then
		return N;
	end if;
	if N mod 4 eq 3 then
		return -N;
	end if;
	if N mod 8 eq 2 then
		return Integers() ! (1/2 * N);
	end if;
	if N mod 8 eq 6 then
		return Integers() ! (-1/2 * N);
	end if;	
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q that is a 2Cs-
// Serre Curve, output the image conductor of E. 
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("198a2");
// > ImgCondCs(E);
// 264
/////////////////////////////////////////////////

ImgCondCs := function(E)
	E := WeierstrassModel(E);
	C := Coefficients(Polynomial(E));
	R<x> := PolynomialRing(Rationals());
	f := x^3 - C[3]*x + C[4];
	R := Roots(f);
	a := R[1][1];
	b := R[2][1];
	c := R[3][1];
	A := Integers() ! (a - b);
	B := Integers() ! (a - c);
	C := Integers() ! (b - c);
	Asf := AbsoluteValue(Squarefree(A));
	Bsf := AbsoluteValue(Squarefree(B));
	Csf := AbsoluteValue(Squarefree(C));
	ABsf := AbsoluteValue(Squarefree(A*B));
	ACsf := AbsoluteValue(Squarefree(A*C));
	BCsf := AbsoluteValue(Squarefree(B*C));
	ABCsf := AbsoluteValue(Squarefree(A*B*C));
	S := {Asf,Bsf,Csf,ABsf,ACsf,BCsf,ABCsf};
	if TwoAdicGroup(E) in ["H8"] then
		L := [x : x in MinWrtDiv(S,3)];
		N1 := L[1];
		N2 := L[2];
		N3 := L[3];
		N1Prime := NPrime(N1);
		N2Prime := NPrime(N2);
		N3Prime := NPrime(N3);
		if (N1*N2*N3) mod 2 ne 0 then
			return LCM([4,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2)),AbsoluteValue(NPrime(N3))]);
		else;
			return LCM([8,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2)),AbsoluteValue(NPrime(N3))]);
		end if;
	end if;
	if TwoAdicGroup(E) in ["H8a","H8b","H8c","H8d","H38","H46"] then
		L := [x : x in MinWrtDiv(S,2)];
		N1 := L[1];
		N2 := L[2];
		N1Prime := NPrime(N1);
		N2Prime := NPrime(N2);
		if (N1*N2) mod 2 eq 0 or TwoAdicGroup(E) in ["H8a","H8c","H38","H46"] then
			return LCM([8,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2))]);
		else
			return LCM([4,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2))]);
		end if;
	end if;
	if TwoAdicGroup(E) in ["H38a","H38b","H38c","H38d","H46a","H46b","H46c","H46d"] then
		L := [x : x in MinWrtDiv(S,1)];
		N1 := L[1];
		N1Prime := NPrime(N1);
		return LCM([8,AbsoluteValue(NPrime(N1))]);
	end if;
end function;


/////////////////////////////////////////////////
// Given an elliptic curve E/Q that is a 2B-
// Serre Curve, output the image conductor of E. 
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("46a2");
// > ImgCondB(E);
// 184
/////////////////////////////////////////////////
ImgCondB := function(E)
	E := WeierstrassModel(E);
	C := Coefficients(Polynomial(E));
	R<x> := PolynomialRing(Rationals());
	f := x^3 - C[3]*x + C[4];
	F := Factorization(f);
	if Degree(F[1][1]) eq 1 then
		a := Coefficients(F[2][1])[2];
		b := Coefficients(F[2][1])[1];
		c := Coefficients(F[1][1])[1];
	else
		a := Coefficients(F[1][1])[2];
		a := Coefficients(F[1][1])[1];
		c := Coefficients(F[2][1])[1];
	end if;
	X := Integers() ! (a^2 - 4*b);
	Y := Integers() ! (a*c - c^2 - b);
	Xsf := AbsoluteValue(Squarefree(X));
	Ysf := AbsoluteValue(Squarefree(Y));
	XYsf := AbsoluteValue(Squarefree(X*Y));
	S := {Xsf,Ysf,XYsf}; 
	if TwoAdicGroup(E) eq "H6" then
		L := [x : x in MinWrtDiv(S,2)];
		N1 := L[1];
		N2 := L[2];
		N1Prime := NPrime(N1);
		N2Prime := NPrime(N2);
		if (N1*N2) mod 2 ne 0 then
			return LCM([4,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2))]);
		else;
			return LCM([8,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2))]);
		end if;
	else
		L := [x : x in MinWrtDiv(S,1)];
		N1 := L[1];
		N1Prime := NPrime(N1);
		return LCM([8,AbsoluteValue(NPrime(N1))]);
	end if;
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q that is a 2Cn-
// Serre Curve, output the image conductor of E. 
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("3136c1");
// > ImgCondCn(E);
// 56
/////////////////////////////////////////////////
ImgCondCn := function(E)
	E := WeierstrassModel(E);
	C := Coefficients(Polynomial(E));
	K<a> := NumberField(DivisionPolynomial(E,2));
	SDK := Integers() ! SquareRoot(Discriminant(RingOfIntegers(K)));
	SDE := AbsoluteValue(Squarefree(Integers() ! SquareRoot(Discriminant(E))));
	if TwoAdicGroup(E) eq "H2" then
		
		if SDE mod 2 eq 0 then
			return LCM([8,SDK,AbsoluteValue(NPrime(SDE))]);
		end if;
		if SDE mod 2 eq 1 then
			return LCM([4,SDK,AbsoluteValue(NPrime(SDE))]);
		end if;
	end if;
	if TwoAdicGroup(E) eq "H2a" then
		return LCM(4,SDK);
	end if;
	if TwoAdicGroup(E) eq "H2b" then
		return LCM(8,SDK);
	end if;
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q that is a 2B-
// Serre Curve, output the cyclicity correction 
// factor associated with E. 
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("102a1");
// > CyclicityCorrectionFactorB(E);
// 78337/78336
/////////////////////////////////////////////////
CyclicityCorrectionFactorB := function(E)
    Dsf := Squarefree(Integers() ! Discriminant(E));
    if Dsf mod 4 ne 1 then
        return 1;
    end if;
    P := [-1/((ell^2-1)*(ell^2-ell)) : ell in Exclude(Divisors(AbsoluteValue(Dsf)),1)];
    N := 1;
    for p in P do
        N := N * p;
    end for;
    return 1 - N;
end function;

/////////////////////////////////////////////////
// Given an elliptic curve E/Q that is a 2Cn-
// Serre Curve, output the cyclicity correction 
// factor associated with E. 
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("392f1");
// > CyclicityCorrectionFactorCn(E);
// 2017/2016
/////////////////////////////////////////////////
CyclicityCorrectionFactorCn := function(E)
    f := DivisionPolynomial(E,2);
    K<a> := SplittingField(f);
    D := Integers() ! SquareRoot(Discriminant(RingOfIntegers(K)));
    if not IsSquarefree(D) then
        return 1;
    end if;
    P := [-1/((ell^2-1)*(ell^2-ell)) : ell in Exclude(Divisors(AbsoluteValue(D)),1)];
    N := 1;
    for p in P do
        N := N * p;
    end for;
    return 1 - N;
end function;

/////////////////////////////////////////////////
// Generate data for the table in the appendix 
////////////// Used for Appendix ////////////////
// > GenerateTable();
// <"2Cs", "H8", "315b2", [ 1, -1, 1, -68, 182 ], 420, "-">
// <"2Cs", "H8a", "1800h2", [ 0, 0, 0, -3675, 35750 ], 120, "-">
// <"2Cs", "H8b", "1089g2", [ 1, -1, 0, -12546, 173047 ], 132, "-">
// <"2Cs", "H8c", "120b2", [ 0, 1, 0, -16, -16 ], 120, "-">
// <"2Cs", "H8d", "33a1", [ 1, 1, 0, -11, 0 ], 132, "-">
// <"2Cs", "H38", "350a2", [ 1, -1, 0, -442, -2784 ], 280, "-">
// <"2Cs", "H38a", "392a2", [ 0, 0, 0, -931, -10290 ], 56, "-">
// <"2Cs", "H38b", "3136s2", [ 0, 0, 0, -3724, 82320 ], 56, "-">
// <"2Cs", "H38c", "112b2", [ 0, 0, 0, -19, -30 ], 56, "-">
// <"2Cs", "H38d", "56a2", [ 0, 0, 0, -19, 30 ], 56, "-">
// <"2Cs", "H46", "198a2", [ 1, -1, 0, -198, 1120 ], 264, "-">
// <"2Cs", "H46a", "288b1", [ 0, 0, 0, -21, -20 ], 24, "-">
// <"2Cs", "H46b", "576c2", [ 0, 0, 0, -84, -160 ], 24, "-">
// <"2Cs", "H46c", "96a1", [ 0, 1, 0, -2, 0 ], 24, "-">
// <"2Cs", "H46d", "66b2", [ 1, 1, 1, -22, -49 ], 264, "-">
// <"2B", "H6", "69a2", [ 1, 0, 1, -16, -25 ], 276, 1>
// <"2B", "H14", "1152o2", [ 0, 0, 0, -216, -864 ], 24, 1>
// <"2B", "H15", "102a1", [ 1, 1, 0, -2, 0 ], 136, 78337/78336>
// <"2B", "H16", "46a1", [ 1, -1, 0, -10, -12 ], 184, 267169/267168>
// <"2B", "H17", "46a2", [ 1, -1, 0, -170, -812 ], 184, 1>
// <"2B", "H18", "490g2", [ 1, 0, 0, -1191, 15721 ], 56, 1>
// <"2B", "H19", "102a2", [ 1, 1, 0, 8, 10 ], 136, 1>
// <"2Cn", "H2", "392f1", [ 0, 0, 0, -7, 7 ], 28, 2017/2016>
// <"2Cn", "H2a", "392c1", [ 0, -1, 0, -16, 29 ], 28, 2017/2016>
// <"2Cn", "H2b", "3136c1", [ 0, 0, 0, -1372, -19208 ], 56, 2017/2016>
/////////////////////////////////////////////////
GenerateTable := function()
    L := [
    EllipticCurve("315b2"),
    EllipticCurve("1800h2"),
    EllipticCurve("1089g2"),
    EllipticCurve("120b2"),
    EllipticCurve("33a1"),
    EllipticCurve("350a2"),
    EllipticCurve("392a2"),
    EllipticCurve("3136s2"),
    EllipticCurve("112b2"),
    EllipticCurve("56a2"),
    EllipticCurve("198a2"),
    EllipticCurve("288b1"),
    EllipticCurve("576c2"),
    EllipticCurve("96a1"),
    EllipticCurve("66b2"),
    EllipticCurve("69a2"),
    EllipticCurve("1152o2"),
    EllipticCurve("102a1"),
    EllipticCurve("46a1"),
    EllipticCurve("46a2"),
    EllipticCurve("490g2"),
    EllipticCurve("102a2"),
    EllipticCurve("392f1"),
    EllipticCurve("392c1"),
    EllipticCurve("3136c1")];
    for E in L do
        GpTup := IsRelSerreCurve(E);
        if GpTup[2] eq "2Cs" then
            Out := <GpTup[2], TwoAdicGroup(E), CremonaReference(E), Coefficients(E), ImgCondCs(E), "-">;
        end if;
        if GpTup[2] eq "2B" then
            Out := <GpTup[2], TwoAdicGroup(E), CremonaReference(E), Coefficients(E), ImgCondB(E), CyclicityCorrectionFactorB(E)>;
        end if;
        if GpTup[2] eq "2Cn" then
            Out := <GpTup[2], TwoAdicGroup(E), CremonaReference(E), Coefficients(E), ImgCondCn(E), CyclicityCorrectionFactorCn(E)>;
        end if;
        Out;
    end for;
    return "";
end function;