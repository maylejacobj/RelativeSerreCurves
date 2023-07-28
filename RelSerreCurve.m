/////////////////////////////////////////////////
// All of our code was run on a machine with the
// following specifications.
// CPU: 2.9 GHz 6-Core Intel Core i9
// Memory: 32 GB 2400 MHz DDR4
// OS: macOS Montery Version 12.5.1
// Magma Version: V2.27-3
/////////////////////////////////////////////////

/////////////////////////////////////////////////
// Below we load "ell-adic-galois-images" by 
// Rouse--Sutherland--Zureick-Brown, which is
// available online at 
// https://github.com/AndrewVSutherland/ell-adic-galois-images.
/////////////////////////////////////////////////
ChangeDirectory("/Users/.../ell-adic-galois-images-main");
Attach("groups/gl2.m");
load "groups/gl2data.m";
RSZB := GL2Load(0);

/////////////////////////////////////////////////
// Below we load "galrep" by Sutherland, which is
// available at https://math.mit.edu/~drew/galrep
/////////////////////////////////////////////////
ChangeDirectory("/Users/.../galrep");
load "galrep.m";

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
// > LevelLower2(TwoB(72));
// 36	// Warning: This computation is slow. It
//      // took us about 2 hours to complete on
//      // the machine specified above.
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
S2Cs := {"2.6.0.1","8.12.0.2","4.12.0.2","8.12.0.1","4.12.0.1","8.12.0.3","8.24.0.5","8.24.0.7","8.24.0.2","8.24.0.1","8.12.0.4","8.24.0.6","8.24.0.8","8.24.0.3","8.24.0.4"};
S2B := {"2.3.0.1","8.6.0.2","8.6.0.4","8.6.0.1","8.6.0.6","8.6.0.3","8.6.0.5"};
S2Cn := {"2.2.0.1","4.4.0.2","8.4.0.1"};

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
	AllGps := [x : x in RSZB | Characteristic(BaseRing(x`subgroup)) ne 0 and Characteristic(BaseRing(x`subgroup)) mod 2 eq 0];
	GpsLbls := {};
	Lbls := {};
	m := Characteristic(BaseRing(G));
	for H in FullCommDet(G) do
		for i in [1..#AllGps] do 
			gp := AllGps[i]`subgroup;
			n := Characteristic(BaseRing(gp));
			if n le m then
				gp := gp @@ Red(m,n);
				n := #BaseRing(gp);
			end if;
			if IsConjugate(Gl(m), Red(n, m)(gp), H) then
				Include(~GpsLbls,<AllGps[i]`label,gp>);
				Include(~Lbls,AllGps[i]`label);
			end if;		
		end for;
	end for;
	if GpOut then
		return GpsLbls;
	end if;
	return Lbls;
end function;

/////////////////////////////////////////////////
// Given G = TwoCs(8), TwoB(4), or TwoCn(4),
// print the number of index two subgroups of H(4),
// for each subgroup H contained in the set S_G.
////////////// Used in Sec. 3 ///////////////////
// > NumIdxTwoSubs(TwoCs(8));
// 8.24.0.5 7
// 8.12.0.4 15
// 8.24.0.7 7
// 8.24.0.2 7
// 8.12.0.3 15
// 8.24.0.3 7
// 8.12.0.1 15
// 4.12.0.2 7
// 8.24.0.1 7
// 8.24.0.8 7
// 8.24.0.6 7
// 8.12.0.2 15
// 8.24.0.4 7
// 4.12.0.1 7
// 2.6.0.1 15
// > NumIdxTwoSubs(TwoB(4));
// 8.6.0.5 7
// 8.6.0.2 7
// 8.6.0.6 7
// 8.6.0.1 7
// 2.3.0.1 7
// 8.6.0.3 7
// 8.6.0.4 7
// > NumIdxTwoSubs(TwoCn(4));
// 2.2.0.1 3
// 8.4.0.1 3
// 4.4.0.2 1
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
// prime numbers ell such that the ell-adic Galois
// representation of E is non-surjective.
//////////////////// EXAMPLE ////////////////////
// > E := EllipticCurve("66c3");
// > NonsurjPrimes(E,GL2EllAdicImages(E,RSZB));
// { 2, 5 }
/////////////////////////////////////////////////
NonsurjPrimes := function(E,EllAdicImages)
	Lbls := EllAdicImages;
	NS := {};
	for lbl in Lbls do
		n := StringToInteger(Split(lbl,".")[1]);
		Include(~NS,Factorization(n)[1][1]);
	end for;
	return NS;
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
    if not HasComplexMultiplication(E) then
	    EllAdicImages := GL2EllAdicImages(E,RSZB);
    	if NonsurjPrimes(E,EllAdicImages) eq {2} then
			TwoAdicGroup := EllAdicImages[1];
		    if TwoAdicGroup in S2Cs then
	            return <true,"2Cs">;
	        end if;
	        if TwoAdicGroup in S2B then
	            return <true,"2B">;
	        end if;
	        if TwoAdicGroup in S2Cn then
	            return <true,"2Cn">;
	        end if;
		end if;
    end if;
    return false;
end function;

/////////////////////////////////////////////////
// Given a set S and a positive integer n, output
// the n elements of S as described in 
// Example 3.3 and the preceding paragraph. 
//////////////////// EXAMPLE ////////////////////
// > S := { 3, 5, 7, 15, 21, 35, 105 };
// > MinElts(S,3);
// [ 3, 5, 7 ]
// > S := { 15, 33, 55, 57, 95, 209, 3135 };
// > MinElts(S,3);
// [ 15, 33, 57 ]
/////////////////////////////////////////////////
MinElts := function(S,n)
	L := [];
	Exclude(~S,1);
	Exclude(~S,2);
	Include(~L,Minimum(S));
	Exclude(~S,Minimum(S));
	if n ge 2 then
		while Minimum(S) mod L[1] eq 0 do
			Exclude(~S,Minimum(S));
		end while;
		Include(~L,Minimum(S));
		Exclude(~S,Minimum(S));
	end if;
	if n eq 3 then
		while (Minimum(S) mod L[1] eq 0) or (Minimum(S) mod L[2] eq 0) or (Minimum(S) mod Squarefree(L[1] * L[2]) eq 0) do
			Exclude(~S,Minimum(S));
		end while;
		Include(~L,Minimum(S));
	end if;
	return L;
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
	TwoAdicGroup := GL2EllAdicImages(E,RSZB)[1];
	if TwoAdicGroup in ["2.6.0.1"] then
		L := MinElts(S,3);
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
	if TwoAdicGroup in ["8.12.0.2","4.12.0.2","8.12.0.1","4.12.0.1","8.12.0.3","8.12.0.4"] then
		L := MinElts(S,2);
		N1 := L[1];
		N2 := L[2];
		N1Prime := NPrime(N1);
		N2Prime := NPrime(N2);
		if (N1*N2) mod 2 eq 0 or TwoAdicGroup in ["8.12.0.2","8.12.0.1","8.12.0.3","8.12.0.4"] then
			return LCM([8,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2))]);
		else
			return LCM([4,AbsoluteValue(NPrime(N1)),AbsoluteValue(NPrime(N2))]);
		end if;
	end if;
	if TwoAdicGroup in ["8.24.0.5","8.24.0.7","8.24.0.2","8.24.0.1","8.24.0.6","8.24.0.8","8.24.0.3","8.24.0.4"] then
		L := MinElts(S,1);
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
	TwoAdicGroup := GL2EllAdicImages(E,RSZB)[1];
	if TwoAdicGroup eq "2.3.0.1" then
		L := MinElts(S,2);
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
		L := MinElts(S,1);
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
	TwoAdicGroup := GL2EllAdicImages(E,RSZB)[1];
	if TwoAdicGroup eq "2.2.0.1" then
		
		if SDE mod 2 eq 0 then
			return LCM([8,SDK,AbsoluteValue(NPrime(SDE))]);
		end if;
		if SDE mod 2 eq 1 then
			return LCM([4,SDK,AbsoluteValue(NPrime(SDE))]);
		end if;
	end if;
	if TwoAdicGroup eq "4.4.0.2" then
		return LCM(4,SDK);
	end if;
	if TwoAdicGroup eq "8.4.0.1" then
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
// <"2Cs", "2.6.0.1", "315b2", [ 1, -1, 1, -68, 182 ], 420, "-">
// <"2Cs", "8.12.0.2", "1800h2", [ 0, 0, 0, -3675, 35750 ], 120, "-">
// <"2Cs", "4.12.0.2", "1089g2", [ 1, -1, 0, -12546, 173047 ], 132, "-">
// <"2Cs", "8.12.0.1", "120b2", [ 0, 1, 0, -16, -16 ], 120, "-">
// <"2Cs", "4.12.0.1", "33a1", [ 1, 1, 0, -11, 0 ], 132, "-">
// <"2Cs", "8.12.0.3", "350a2", [ 1, -1, 0, -442, -2784 ], 280, "-">
// <"2Cs", "8.24.0.5", "392a2", [ 0, 0, 0, -931, -10290 ], 56, "-">
// <"2Cs", "8.24.0.7", "3136s2", [ 0, 0, 0, -3724, 82320 ], 56, "-">
// <"2Cs", "8.24.0.2", "112b2", [ 0, 0, 0, -19, -30 ], 56, "-">
// <"2Cs", "8.24.0.1", "56a2", [ 0, 0, 0, -19, 30 ], 56, "-">
// <"2Cs", "8.12.0.4", "198a2", [ 1, -1, 0, -198, 1120 ], 264, "-">
// <"2Cs", "8.24.0.6", "288b1", [ 0, 0, 0, -21, -20 ], 24, "-">
// <"2Cs", "8.24.0.8", "576c2", [ 0, 0, 0, -84, -160 ], 24, "-">
// <"2Cs", "8.24.0.3", "96a1", [ 0, 1, 0, -2, 0 ], 24, "-">
// <"2Cs", "8.24.0.4", "66b2", [ 1, 1, 1, -22, -49 ], 264, "-">
// <"2B", "2.3.0.1", "69a2", [ 1, 0, 1, -16, -25 ], 276, 1>
// <"2B", "8.6.0.2", "1152o2", [ 0, 0, 0, -216, -864 ], 24, 1>
// <"2B", "8.6.0.4", "102a1", [ 1, 1, 0, -2, 0 ], 136, 78337/78336>
// <"2B", "8.6.0.1", "46a1", [ 1, -1, 0, -10, -12 ], 184, 267169/267168>
// <"2B", "8.6.0.6", "46a2", [ 1, -1, 0, -170, -812 ], 184, 1>
// <"2B", "8.6.0.3", "490g2", [ 1, 0, 0, -1191, 15721 ], 56, 1>
// <"2B", "8.6.0.5", "102a2", [ 1, 1, 0, 8, 10 ], 136, 1>
// <"2Cn", "2.2.0.1", "392f1", [ 0, 0, 0, -7, 7 ], 28, 2017/2016>
// <"2Cn", "4.4.0.2", "392c1", [ 0, -1, 0, -16, 29 ], 28, 2017/2016>
// <"2Cn", "8.4.0.1", "3136c1", [ 0, 0, 0, -1372, -19208 ], 56, 2017/2016>
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
        TwoAdicGroup := GL2EllAdicImages(E,RSZB)[1];
        if GpTup[2] eq "2Cs" then
            Out := <GpTup[2], TwoAdicGroup, CremonaReference(E), Coefficients(E), ImgCondCs(E), "-">;
        end if;
        if GpTup[2] eq "2B" then
            Out := <GpTup[2], TwoAdicGroup, CremonaReference(E), Coefficients(E), ImgCondB(E), CyclicityCorrectionFactorB(E)>;
        end if;
        if GpTup[2] eq "2Cn" then
            Out := <GpTup[2], TwoAdicGroup, CremonaReference(E), Coefficients(E), ImgCondCn(E), CyclicityCorrectionFactorCn(E)>;
        end if;
        Out;
    end for;
    return "";
end function;

/////////////////////////////////////////////////
// Example 5.1: Computes the adelic Galois image
// of the elliptic curve E with LMFDB label
// 315.a2. The image conductor of of E is 420.
// The function outputs G_E(420). The output
// agrees with Zywina's (available on the LMFDB)
// up to conjugation in GL(2,Z/420Z). Note that
// the generators of the output group are random.
/////////////////////////////////////////////////
// > AdelicImageExample1();
// MatrixGroup(2, IntegerRing(420)) of order 2^15 * 3^4 * 5 * 7
// Generators:
//    [ 69 298]
//    [134   7]
//
//    [113 360]
//    [142 359]
//
//    [261  82]
//    [398  53]
//
//    [355  46]
//    [142 111]
/////////////////////////////////////////////////
AdelicImageExample1 := function();

	R<x> := PolynomialRing(Rationals());
	E := EllipticCurve("315b2");
	E := WeierstrassModel(E);
	B :=TorsionBasis(WeierstrassModel(E),4);
	A:=TorsionPoints(B,4);
	K<alpha> := Parent(B[1][1]);
	G,S,phi:=AutomorphismGroup(K);
	
	L := Subfields(K,2);
	NPrimes := [-3,5,-7];
	QuadFlds := [RationalsAsNumberField(),RationalsAsNumberField(),RationalsAsNumberField()];
	Alphas := [One(K),One(K),One(K)];
	for F in L do
		for i in [1,2,3] do
			if #Roots(x^2-NPrimes[i],F[1]) gt 0 then
				QuadFlds[i] := F[1];
				Alphas[i] := Roots(x^2-NPrimes[i],F[1])[1][1];
			end if;
		end for;
	end for;

	Gs := [[],[],[]];
	for i in [1,2,3] do
		for g in G do
			f := phi(g);
			if f(Alphas[i]) eq Alphas[i] then
				Include(~Gs[i],g);
			end if;
		end for;
	end for;
	Gs := [sub<G|Gs[i]> : i in [1,2,3]]; 

	Hs := [sub<GL(2,Integers(4))|[SigmaMatrix(phi(g),B,A,4): g in Generators(Gs[i])]> : i in [1,2,3]];
	H := sub<GL(2,Integers(4))|[SigmaMatrix(phi(g),B,A,4): g in Generators(G)]>;

	pi4 := Red(420,4);
	pi3 := Red(420,3);
	pi5 := Red(420,5);
	pi7 := Red(420,7);

	Q1, epsilon1 := H/Hs[1];
	Q2, epsilon2 := H/Hs[2];
	Q3, epsilon3 := H/Hs[3];

	T1, chi1 := Gl(3)/LowIndexSubgroups(Gl(3),2)[1];
	T2, chi2 := Gl(5)/LowIndexSubgroups(Gl(5),2)[1];
	T3, chi3 := Gl(7)/LowIndexSubgroups(Gl(7),2)[1];

	G420 := H @@ pi4;
	S := {};
	Snew := {};
	SG := sub<G420|[]>;
	Sz := 0;
	Sznew := 0;
	while true do
		g := Random(G420);
		if epsilon1(pi4(g)) eq chi1(pi3(g)) and epsilon2(pi4(g)) eq chi2(pi5(g)) and epsilon3(pi4(g)) eq chi3(pi7(g)) then
			SGnew := sub<G420|Include(S,g)>;
			Sznew := #SGnew;
			if Sznew gt Sz then
				Include(~S,g);
				SG := SGnew;
				Sz := Sznew;
				if Index(G420,SG) eq 8 then
					return SG;
				end if;
			end if;
		end if;
	end while;
end function;

/////////////////////////////////////////////////
// Example 5.2: Computes the adelic Galois image
// of the elliptic curve E with LMFDB label
// 69.a1. The image conductor of of E is 276.
// The function outputs G_E(276). The output
// agrees with Zywina's (available on the LMFDB)
// up to conjugation in GL(2,Z/276Z). Note that
// the generators of the output group are random.
/////////////////////////////////////////////////
// > AdelicImageExample2();
// MatrixGroup(2, IntegerRing(276)) of order 2^12 * 3^2 * 11^2 * 23
// Generators:
//    [207  64]
//    [166 177]
//
//    [ 63  50]
//    [217 143]
//
//    [ 59 272]
//    [265 225]
/////////////////////////////////////////////////
AdelicImageExample2 := function();

	R<x> := PolynomialRing(Rationals());
	E := EllipticCurve("69a2");
	E := WeierstrassModel(E);
	B :=TorsionBasis(WeierstrassModel(E),4);
	A:=TorsionPoints(B,4);
	K<alpha> := Parent(B[1][1]);
	G,S,phi:=AutomorphismGroup(K);

	L := Subfields(K,2);
	NPrimes := [-23,-3];
	QuadFlds := [RationalsAsNumberField(),RationalsAsNumberField()];
	Alphas := [One(K),One(K)];
	for F in L do
		for i in [1,2] do
			if #Roots(x^2-NPrimes[i],F[1]) gt 0 then
				QuadFlds[i] := F[1];
				Alphas[i] := Roots(x^2-NPrimes[i],F[1])[1][1];
			end if;
		end for;
	end for;
	
	Gs := [[],[]];
	for i in [1,2] do
		for g in G do
			f := phi(g);
			if f(Alphas[i]) eq Alphas[i] then
				Include(~Gs[i],g);
			end if;
		end for;
	end for;
	Gs := [sub<G|Gs[i]> : i in [1,2]]; 

	Hs := [sub<GL(2,Integers(4))|[SigmaMatrix(phi(g),B,A,4): g in Generators(Gs[i])]> : i in [1,2]];
	H := sub<GL(2,Integers(4))|[SigmaMatrix(phi(g),B,A,4): g in Generators(G)]>;

	pi4 := Red(276,4);
	pi23 := Red(276,23);
	pi3 := Red(276,3);

	Q1, epsilon1 := H/Hs[1];
	Q2, epsilon2 := H/Hs[2];

	T1, chi1 := Gl(23)/LowIndexSubgroups(Gl(23),2)[1];
	T2, chi2 := Gl(3)/LowIndexSubgroups(Gl(3),2)[1];

	G276 := H @@ pi4;
	S := {};
	Snew := {};
	SG := sub<G276|[]>;
	Sz := 0;
	Sznew := 0;
	while true do
		g := Random(G276);
		if epsilon1(pi4(g)) eq chi1(pi23(g)) and epsilon2(pi4(g)) eq chi2(pi3(g)) then
			SGnew := sub<G276|Include(S,g)>;
			Sznew := #SGnew;
			if Sznew gt Sz then
				Include(~S,g);
				SG := SGnew;
				Sz := Sznew;
				if Index(G276,SG) eq 4 then
					return SG;
				end if;
			end if;
		end if;
	end while;
end function;

/////////////////////////////////////////////////
// Example 5.3: Computes the adelic Galois image
// of the elliptic curve E with LMFDB label
// 392.a1. The image conductor of of E is 28.
// The function outputs G_E(28). The output
// agrees with Zywina's (available on the LMFDB)
// up to conjugation in GL(2,Z/28Z). Note that
// the generators of the output group are random.
/////////////////////////////////////////////////
// > AdelicImageExample3();
//    MatrixGroup(2, IntegerRing(28)) of order 2^8 * 3^2 * 7
//    Generators:
//        [16 27]
//        [19  9]
//
//        [16 19]
//        [25  9]
/////////////////////////////////////////////////
AdelicImageExample3 := function();

	R<x> := PolynomialRing(Rationals());
	E := EllipticCurve("392f1");
	E := WeierstrassModel(E);
	B :=TorsionBasis(WeierstrassModel(E),4);
	A:=TorsionPoints(B,4);
	K<alpha> := Parent(B[1][1]);
	G,S,phi:=AutomorphismGroup(K);
	
	SDEPrime := -7;
	L := Subfields(K,2);
	for F in L do
		if #Roots(x^2-SDEPrime,F[1]) gt 0 then
			QuadFld := F[1]; 
		end if;
	end for;
	Alpha := Roots(x^2-SDEPrime,QuadFld)[1][1];

	G1 := [];
	for g in G do
		f := phi(g);
		if f(Alpha) eq Alpha then
			Include(~G1,g);
		end if;
	end for;
	G1 := sub<G|G1>;

	H := sub<GL(2,Integers(4))|[SigmaMatrix(phi(g),B,A,4): g in Generators(G)]>;
	H1 := sub<GL(2,Integers(4))|[SigmaMatrix(phi(g),B,A,4): g in Generators(G1)]>;
	H2 := LowIndexSubgroups(H,3)[1]; // Unique index 3 subgroup

	pi4 := Red(28,4);
	pi7 := Red(28,7);

	Q1, epsilon := H/H1;
	Q2, omega := H/H2;

	T1, chi := Gl(7)/LowIndexSubgroups(Gl(7),2)[1]; // Unique index 2 subgroup
	T2, xi := Gl(7)/LowIndexSubgroups(Gl(7),3)[1]; // Unique index 3 subgroup

	G28 := H @@ pi4;
	L := [];
	for i in [1,2] do
		S := {};
		Snew := {};
		SG := sub<G28|[]>;
		Sz := 0;
		Sznew := 0;
		while true do
			g := Random(G28);
			if epsilon(pi4(g)) eq chi(pi7(g)) and omega(pi4(g)) eq xi(pi7(g))^i then
				SGnew := sub<G28|Include(S,g)>;
				Sznew := #SGnew;
				if Sznew gt Sz then
					Include(~S,g);
					SG := SGnew;
					Sz := Sznew;
					if Index(G28,SG) eq 6 then
						Include(~L,SG);
						break;
					end if;
				end if;
			end if;
		end while;
	end for;

	a3 := TraceOfFrobenius(E,3);
	f := x^2 - a3 * x + 3;
	if not f in {CharacteristicPolynomial(g) : g in L[2]} then
		return L[1];
	end if;
	if not f in {CharacteristicPolynomial(g) : g in L[1]} then
		return L[2];
	end if;
end function;
