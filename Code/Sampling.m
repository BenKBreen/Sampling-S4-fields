
//###################  Sampling ############################//


// TODO: 
// Check Isitmaximal
// Remove the degree ne 1 in isittype 

//######## Preliminary intrinsics ##################//


intrinsic lambda(A::AlgMatElt, B::AlgMatElt, i::RngIntElt, j::RngIntElt, k::RngIntElt, l::RngIntElt) -> RngIntElt
	{returns the 2 by 2 minor of a matrix, Used for Isitmaximal}
	return Determinant(Matrix([[A[i][j],B[i][j]],[A[k][l],B[k][l]]]));
end intrinsic;







intrinsic Isitmaximal(A::AlgMatElt, B::AlgMatElt) -> Any
	{Tests if the ring specified by the ternary quadratic form (A,B) is maximal. Returns true/false}
	
	lambda1112 := lambda(A,B,1,1,1,2);
	lambda1113 := lambda(A,B,1,1,1,3);	
	lambda1122 := lambda(A,B,1,1,2,2);
	lambda1123 := lambda(A,B,1,1,2,3);
	lambda1133 := lambda(A,B,1,1,3,3);
	
	lambda1213 := lambda(A,B,1,2,1,3);
	lambda1222 := lambda(A,B,1,2,2,2);
	lambda1223 := lambda(A,B,1,2,2,3);
	lambda1233 := lambda(A,B,1,2,3,3);

	lambda1322 := lambda(A,B,1,3,2,2);
	lambda1323 := lambda(A,B,1,3,2,3);
	lambda1333 := lambda(A,B,1,3,3,3);

	lambda2223 := lambda(A,B,2,2,2,3);	
	lambda2233 := lambda(A,B,2,2,3,3);

	lambda2333 := lambda(A,B,2,3,3,3);

	

	Cod3 := [lambda1112, lambda1113, lambda1122, lambda1123, lambda1133, lambda1213, lambda1222, lambda1223, lambda1233, lambda1322, lambda1323, lambda1333, lambda2223, lambda2233, lambda2333];

	primes := [];
	for i in Cod3 do
		if i ne 0 then
			Fact := Factorization(i);
			for j in Fact do
				if j[1] notin primes then
					Append(~primes, j[1]);
				end if;
			end for;
		end if;
	end for;

	if #primes eq 0 then
		return "false";
	else 
		Counter := 0;
		
		for p in primes do
			Cod1 := [*[*lambda1122,lambda1123, lambda1133,lambda1213*], [*lambda1112,lambda1113 *] *];
			t1 := [i mod p : i in Cod1[1]] cat [i mod p^2 : i in Cod1[2]];
			if Set(t1) eq {0} then
				Counter := 1;
				break;
			else	
				Cod2 := [*[*lambda1113,lambda1123,lambda1213,lambda1223, lambda1322,lambda2223 *], [*lambda1112,lambda1122, lambda1222*] *];
				t2 := [i mod p : i in Cod2[1]] cat [i mod p^2 : i in Cod2[2]];
				if Set(t2) eq {0} then
					Counter := 1;
					break;
				else
					t3 := [i mod p : i in Cod3];
					if Set(t3) eq {0} then
						Counter := 1;
						break;
					end if;
				end if;
			end if;
		end for;

		if Counter eq 0 then
			return "true";
		else
			return "false";
		end if;
	end if;
end intrinsic;








intrinsic Isitreduced(A::AlgMatElt, B::AlgMatElt) -> Any
	{Tests if the form (A,B) is the reduced representative. Returns true/false}
	
	a11 := A[1][1]; 
	a12 := A[1][2];
	a13 := A[1][3];
	a22 := A[2][2];
	a23 := A[2][3];
	a33 := A[3][3];

	b11 := B[1][1];
	b12 := B[1][2];
	b13 := B[1][3];
	b22 := B[2][2];
	b23 := B[2][3];
	b33 := B[3][3];
	
	q11 := (a23)^2*(b11)^2 - a22*a33*(b11)^2 - 2*a13*a23*b11*b12 + 2*a12*a33*b11*b12 + 3*(a13)^2*(b12)^2 -2*a11*a33*(b12)^2 + 2*a13*a22*b11*b13 - 2*a12*a23*b11*b13 - 6*a12*a13*b12*b13 + 4*a11*a23*b12*b13 + 3*(a12)^2*(b13)^2 -2*a11*a22*(b13)^2 - 2*(a13)^2*b11*b22 + a11*a33*b11*b22 + 2*a11*a13*b13*b22 + 4*a12*a13*b11*b23 -2*a11*a23*b11*b23 - 2*a11*a13*b12*b23 - 2*a11*a12*b13*b23 + (a11)^2*(b23)^2 - 2*(a12)^2*b11*b33 + a11*a22*b11*b33 +2*a11*a12*b12*b33 - (a11)^2*b22*b33;
	q12 := (a23)^2*b11*b12 - a22*a33*b11*b12 + a13*a23*(b12)^2 -a13*a22*b12*b13 +a12*a22*(b13)^2 -3*a13*a23*b11*b22 + 2*a12*a33*b11*b22 + (a13)^2*b12*b22 -a11*a33*b12*b22 -a12*a13*b13*b22 + 3*a11*a23*b13*b22 +3*a13*a22*b11*b23 -a12*a23*b11*b23 -a12*a13*b12*b23 - a11*a23*b12*b23 + (a12)^2*b13*b23 - 3*a11*a22*b13*b23 + a11*a12*(b23)^2 -a12*a22*b11*b33 + 2*a11*a22*b12*b33 -a11*a12*b22*b33;
	q13 := a13*a33*(b12)^2 +(a23)^2*b11*b13 -a22*a33*b11*b13-a13*a23*b12*b13 -a12*a33*b12*b13 + a12*a23*(b13)^2 - a13*a33*b11*b22 + 2*a11*a33*b13*b22 - a13*a23*b11*b23 + 3*a12*a33*b11*b23 +(a13)^2*b12*b23 - 3*a11*a33*b12*b23 -a12*a13*b13*b23 -a11*a23*b13*b23 + a11*a13*(b23)^2 + 2*a13*a22*b11*b33 -3*a12*a23*b11*b33 - a12*a13*b12*b33 + 3*a11*a23*b12*b33 + (a12)^2*b13*b33 -a11*a22*b13*b33 -a11*a13*b22*b33;
	q22 := 3*(a23)^2*(b12)^2 - 2*a22*a33*(b12)^2 -2*a22*a23*b12*b13 + (a22)^2*(b13)^2 -2*(a23)^2*b11*b22 +a22*a33*b11*b22 -2*a13*a23*b12*b22 + 2*a12*a33*b12*b22 -2*a13*a22*b13*b22 +4*a12*a23*b13*b22 +(a13)^2*(b22)^2 -a11*a33*(b22)^2 +2*a22*a23*b11*b23 + 4*a13*a22*b12*b23 -6*a12*a23*b12*b23 -2*a12*a22*b13*b23 -2*a12*a13*b22*b23 + 2*a11*a23*b22*b23 +3*(a12)^2*(b23)^2 -2*a11*a22*(b23)^2 -(a22)^2*b11*b33 + 2*a12*a22*b12*b33 -2*(a12)^2*b22*b33 +a11*a22*b22*b33;
	q23 := a23*a33*(b12)^2 +(a23)^2*b12*b13 -3*a22*a33*b12*b13 + a22*a23*(b13)^2 -a23*a33*b11*b22 -a13*a23*b13*b22 + 3*a12*a33*b13*b22 + 2*a22*a33*b11*b23 -a13*a23*b12*b23 -a12*a33*b12*b23 -a13*a22*b13*b23 -a12*a23*b13*b23 +(a13)^2*b22*b23 -a11*a33*b22*b23 -a12*a13*(b23)^2 - a22*a23*b11*b33 +3*a13*a22*b12*b33 -a12*a23*b12*b33 -3*a12*a13*b22*b33 +2*a11*a23*b22*b33 +(a12)^2*b23*b33 -a11*a22*b23*b33;
	q33 := (a33)^2*(b12)^2 -2*a23*a33*b12*b13 + 3*(a23)^2*(b13)^2 -2*a22*a33*(b13)^2 -(a33)^2*b11*b22 +2*a13*a33*b13*b22 + 2*a23*a33*b11*b23 -2*a13*a33*b12*b23 -6*a13*a23*b13*b23 + 4*a12*a33*b13*b23 + 3*(a13)^2*(b23)^2 -2*a11*a33*(b23)^2 -2*(a23)^2*b11*b33 + a22*a33*b11*b33 + 4*a13*a23*b12*b33 - 2*a12*a33*b12*b33 +2*a13*a22*b13*b33 -2*a12*a23*b13*b33 -2*(a13)^2*b22*b33 + a11*a33*b22*b33 -2*a12*a13*b23*b33 + 2*a11*a23*b23*b33 + (a12)^2*(b33)^2 -a11*a22*(b33)^2;

	s := 0;
	if 0 lt q11 and q11 le q22 and q22 le q33 then
		if Abs(q12) le q11 and Abs(q13) le q11 and Abs(q23) le q22 then
			if Abs(q12+q13+q23) le q22 and Abs(q12-q13 +q23) le q22 and Abs(q12+q13-q23) le q22 and Abs(q12-q13-q23) le q22 then
				s :=1;
			end if; 
		end if;
	end if;

	if s eq 1 then
		t := 0;
		Pr<X, Y> := PolynomialRing(Rationals(), 2);
		f := Determinant(A*X-B*Y);

		a := MonomialCoefficient(f, X^3);
		b := MonomialCoefficient(f, X^2*Y);
		c := MonomialCoefficient(f, X*Y^2);
		d := MonomialCoefficient(f, Y^3);

		if Abs(b*c-9*a*d) le (b^2-3*a*c) and (b^2-3*a*c) le (c^2 -3*b*d) then
			return "true";
		else
			return "false";
		end if;
	else
		return "false";
	end if;
end intrinsic;



intrinsic Isittype(K::Any) -> Any
	{Tests if a NumberField is totally real and has Galois Group S4. Returns true/false}
	if IsTotallyReal(K) eq true and Degree(K) ne 1 and Order(GaloisGroup(K)) eq 24 then
		return "true";
	else
		return "false";
	end if;
end intrinsic;




intrinsic Alltests(L::SeqEnum) -> Any
	{Tests if pair (A,B) = [*a11,a12,a13,a22,a23,a33,b11,b12,b13,b22,b23,b33*] cooresponds to a totally real S4 field. Returns field K/false}

	a11 := L[1]; 
	a12 := L[2];
	a13 := L[3];
	a22 := L[4];
	a23 := L[5];
	a33 := L[6];

	b11 := L[7];
	b12 := L[8];
	b13 := L[9];
	b22 := L[10];
	b23 := L[11];
	b33 := L[12];

	Q := Rationals();
	A := Matrix([[a11,a12,a13],[a12,a22,a23],[a13,a23,a33]]);
	B := Matrix([[b11,b12,b13],[b12,b22,b23],[b13,b23,b33]]);

	if Isitmaximal(A,B) eq "true" then
		if Isitreduced(A,B) eq "true" then
		
			PQ<x,y,z> := ProjectivePlane(Rationals());
			C1 := Curve(PQ, a11*x^2 + a12*x*y + a13*x*z + a22*y^2 + a23*y*z + a33*z^2);
			C2 := Curve(PQ, b11*x^2 + b12*x*y + b13*x*z + b22*y^2 + b23*y*z + b33*z^2);
			I := IntersectionNumbers(C1,C2);
			K := Parent(I[1][1][1]);

			if Isittype(K) eq "true" then
				Kpoly := Coefficients(DefiningPolynomial(K));
				return [* "true", Kpoly *];
			else
				return ["false"];
			end if;
		else
			return ["false"];
		end if;
	else
		return ["false"];
	end if;
end intrinsic;











//#########  Here is the actual sampling code  #########

intrinsic SampleFields(X::RngIntElt,n::RngIntElt) -> SeqEnum
	{Input:    X: bound for coefficients of (A,B)   n: # of samples,  Output: List coefficients [a0,a1,a2,a3,1] for defining polynomial x^4 +a3*x^3 + ... a0 } 
	V := [];
	while #V lt n do
		L := [];
		for i in [1..12] do
			re := Random(-X, X);
			Append(~L,re);
		end for;
		if Alltests(L)[1] eq "true" then 	
			Append(~V, Alltests(L)[2]);
		else
			V := V;
		end if;
	end while;
	return V;
end intrinsic;






