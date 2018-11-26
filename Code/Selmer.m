
intrinsic Selgens(L::SeqEnum) -> SeqEnum
	{Takes a tuple representing the minimal polynomial for a field and returns the generators of 2-Selmer}
	P<x> := PolynomialRing(Integers());
	F := NumberField(P!L);
	Ok := Integers(F);
 	D := Discriminant(Ok);
 	assert Signature(F) eq Degree(F);
 	r1 := Degree(F);

	twofact := Factorization(2*Ok);
	Sel2, mS := pSelmerGroup(2, {Parent(2*Ok) | });
	Sel2gens := [Sel2.i@@mS : i in [1..#Generators(Sel2)]];
	for i := 1 to #Sel2gens do
		sel2i := Sel2gens[i];
		_, bbi := IsPower(sel2i*Ok,2);
		if Norm(bbi) mod 2 eq 0 then
			bbi2 := &*[pp[1]^pp[2] : pp in Factorization(bbi) | Norm(pp[1]) mod 2 eq 0];
			bbi2_basis := Basis(bbi2^-1);
			z := bbi2_basis[1];
			while Integers ()!(Norm(sel2i*z^2)) mod 2 eq 0 do
				z +:= (-1)^(Random(2))*Random(bbi2_basis);
			end while;
			assert mS(sel2i*z^2) eq mS(sel2i);
			Sel2gens[i] := sel2i*z^2;
		end if;
	end for;
	return Sel2gens;
end intrinsic;



intrinsic Sgnrk(L::RngUPolElt) -> any
{Returns the unit signature rank}
  
  h := function(x);
  	if x eq 1 then return 0; else return 1; end if;
  end function;
  
  F := NumberField(L);
  R := Integers(F);
  D := Discriminant(R);
  assert Signature(F) eq Degree(F);
  r1 := Degree(F);

	twofact := Factorization(2*R);
	ClF := ClassGroup(R);
	ClFplus := RayClassGroup(1*R, [1..Degree(F)]);
	U, m := pFundamentalUnits(R, 2 : Al := "ClassGroup");
	Sel2, mS := pSelmerGroup(2, {Parent(2*R) | });
	Sel2gens := [Sel2.i@@mS : i in [1..#Generators(Sel2)]];
	for i := 1 to #Sel2gens do
		sel2i := Sel2gens[i];
		_, bbi := IsPower(sel2i*R,2);
		if Norm(bbi) mod 2 eq 0 then
			bbi2 := &*[pp[1]^pp[2] : pp in Factorization(bbi) | Norm(pp[1]) mod 2 eq 0];
			bbi2_basis := Basis(bbi2^-1);
			z := bbi2_basis[1];
			while Integers ()!(Norm(sel2i*z^2)) mod 2 eq 0 do
				z +:= (-1)^(Random(2))*Random(bbi2_basis);
			end while;
			assert mS(sel2i*z^2) eq mS(sel2i);
			Sel2gens[i] := sel2i*z^2;
		end if;
	end for;
	R4R, m4R := quo<R | 4*R>;
	U4R, mU4R := UnitGroup(R4R);
	U4Rsq, mU4Rsq := quo<U4R | [2*U4R.i : i in [1..#Generators(U4R)]]>;
	E := Matrix(GF(2),[[h(ux) : ux in RealSigns(m(U.i))] cat Eltseq(mU4Rsq(m4R (m(U.i))@@mU4R)) : i in [1..Degree(F)]]);
	sgnrk := Rank(Submatrix(E,1,1,r1,r1));
								
  	//return [* k, rho, rhoplus, sgnrk, sgnrk2, is_split, AbelianInvariants(ClF), AbelianInvariants(ClFplus), E, M, En *];
  	return sgnrk;
end intrinsic;



/*

Disc := [d : d in [2 .. 1000] | IsSquarefree(d)];
D1 := [];
for d in Disc do
	D3 := [p[1] : p in Factorization(d) | p[1] mod 4 eq 3];
	if #D3 eq 0 then
		Append(~D1, [-d,0,1]);
	end if;
end for;


for l in D1 do
	S := Selgens(l);
	K := Norm(FundamentalUnit(QuadraticField(-l[1])));
	Sn := [Norm(s) : s in S];
	if K eq 1 then
		print -l[1], [p[1] : p in Factorization(-l[1])] , Sn;
	end if;
end for;


*/

/*
h := function(x);
  if x eq 1 then return 0; else return 1; end if;
end function;

			

R<x> := PolynomialRing(Integers());

BunchaSelmerStuff := function(F);
  R := Integers(F);
  D := Discriminant(R);
  assert Signature(F) eq Degree(F);
  r1 := Degree(F);

	twofact := Factorization(2*R);
	ClF := ClassGroup(R);
	ClFplus := RayClassGroup(1*R, [1..Degree(F)]);
	U, m := pFundamentalUnits(R, 2 : Al := "ClassGroup");
	Sel2, mS := pSelmerGroup(2, {Parent(2*R) | });
	Sel2gens := [Sel2.i@@mS : i in [1..#Generators(Sel2)]];
	for i := 1 to #Sel2gens do
		sel2i := Sel2gens[i];
		_, bbi := IsPower(sel2i*R,2);
		if Norm(bbi) mod 2 eq 0 then
			bbi2 := &*[pp[1]^pp[2] : pp in Factorization(bbi) | Norm(pp[1]) mod 2 eq 0];
			bbi2_basis := Basis(bbi2^-1);
			z := bbi2_basis[1];
			while Integers ()!(Norm(sel2i*z^2)) mod 2 eq 0 do
				z +:= (-1)^(Random(2))*Random(bbi2_basis);
			end while;
			assert mS(sel2i*z^2) eq mS(sel2i);
			Sel2gens[i] := sel2i*z^2;
		end if;
	end for;
	R4R, m4R := quo<R | 4*R>;
	U4R, mU4R := UnitGroup(R4R);
	U4Rsq, mU4Rsq := quo<U4R | [2*U4R.i : i in [1..#Generators(U4R)]]>;
	E := Matrix(GF(2),[[h(ux) : ux in RealSigns(m(U.i))] cat Eltseq(mU4Rsq(m4R (m(U.i))@@mU4R)) : i in [1..Degree(F)]]);
	M := Matrix(GF(2),[[h(ux) : ux in RealSigns(s)] cat Eltseq(mU4Rsq(m4R (s)@@mU4R)) : s in Sel2gens]);
	En := Matrix(GF(2),[[h(ux) : ux in RealSigns(F!-1)] cat Eltseq(mU4Rsq(m4R (F!-1)@@mU4R))]);
	k := Dimension(Kernel(Submatrix(M,1,r1+1,Nrows(M),r1))) - Dimension(Kernel(M));
	sgnrk := Rank(Submatrix(E,1,1,r1,r1));
	sgnrk2 := Rank(Submatrix(E,1,5,r1,r1)); 
	rhooo := r1-sgnrk;
	rho := tworank(AbelianInvariants(ClF));
	rhoplus := tworank(AbelianInvariants(ClFplus));
	is_split := (rhoplus eq rho+rhooo);
	
								
  	//return [* k, rho, rhoplus, sgnrk, sgnrk2, is_split, AbelianInvariants(ClF), AbelianInvariants(ClFplus), E, M, En *];
  	return Sel2gens;
end function;


B := BunchaSelmerStuff(K);

*/