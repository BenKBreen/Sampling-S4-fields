
// Code for generating a single field from a pair of ternary quadratic forms (A,B)



#######Field Generator example#####

a11 := 1; 
a12 := 3;
a13 := 5;
a22 := 4;
a23 := 6;
a33 := 7;

b11 := 5;
b12 := 6;
b13 := 9;
b22 := 7;
b23 := 8;
b33 := 5;


PQ<x,y,z> := ProjectivePlane(Rationals());
C1 := Curve(PQ, a11*x^2 + a12*x*y + a13*x*z + a22*y^2 + a23*y*z + a33*z^2);
C2 := Curve(PQ, b11*x^2 + b12*x*y + b13*x*z + b22*y^2 + b23*y*z + b33*z^2);


I := IntersectionNumbers(C1,C2);
K := Parent(I[1][1][1]);


A := Matrix([[a11,a12,a13],[a12,a22,a23],[a13,a23,a33]]);
B := Matrix([[b11,b12,b13],[b12,b22,b23],[b13,b23,b33]]);


lambda := function(A,B,i,j,k,l);
	aij := A[i][j];
	bij := B[i][j];
	akl := A[k][l];
	bkl := B[k][l];
	return Determinant(Matrix([[aij,bij],[akl,bkl]]));
end function;


Isitmaximal := function(A,B);
	primes := [t[1] : t in Factorization(lambda(A,B,1,1,2,2))];
	lambda1122 := lambda(A,B,1,1,2,2);
	lambda1123 := lambda(A,B,1,1,2,3);
	lambda1133 := lambda(A,B,1,1,3,3);
	lambda1112 := lambda(A,B,1,1,1,2);
	lambda1113 := lambda(A,B,1,1,1,3);
	lambda1213 := lambda(A,B,1,2,1,3);
	lambda1222 := lambda(A,B,1,2,2,2);
	lambda1223 := lambda(A,B,1,2,2,3);
	lambda1322 := lambda(A,B,1,2,1,3);
	lambda2223 := lambda(A,B,2,2,2,3);	
	
	Cod1 := [*[*lambda1122,lambda1123, lambda1133,lambda1213*], [*lambda1112,lambda1113 *] *];
	Cod2 := [*[*lambda1113,lambda1123,lambda1213,lambda1223, lambda1322,lambda2223 *], [*lambda1112,lambda1122, lambda1222*] *];
	Cod3 := [lambda(A,B,i,j,k,l) : i in [1..3], j in [1..2], k in [1..3], l in [1..2]];

	s := 0;
	for p in primes do
		t1 := [i mod p : i in Cod1[1]] cat [i mod p^2 : i in Cod1[2]];
		t2 := [i mod p : i in Cod2[1]] cat [i mod p^2 : i in Cod2[2]];
		t3 := [i mod p : i in Cod3];
		if Set(t1) eq {0} or Set(t2) eq {0} or Set(t3) eq {0} then
			s := 1;
		end if;
	end for;
	if s eq 1 then
		return "false";
	else
		return "true";
	end if;
end function;


Isitreduced := function(A,B);
	
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

	t := 0;
	f := Determinant(A*x-B*y);

	a := Coefficients(f)[1];
	b := Coefficients(f)[2];
	c := Coefficients(f)[3];
	d := Coefficients(f)[4];

	if Abs(b*c-9*a*d) le (b^2-3*a*c) and (b^2-3*a*c) le (c^2 -3*b*d) then
		t := 1;
	end if;

	if t eq 1 and s eq 1 then
		return "true";
	else
		return "false";
	end if;
end function;


Isittype := function(K);
	if IsTotallyReal(K) eq true and Order(GaloisGroup(K)) eq 24 then
		return "true";
	else
		return "false";
	end if;
end function;