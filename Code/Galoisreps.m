////////////   Galoisrepresentation V_2 /////////////////


intrinsic V2rep(L::SeqEnum) -> SeqEnum
	{Takes a field defining a polynomial, returns the F[g] module V2}
	K := MakeField(L);
	Ok := Integers(K);
	n := Degree(K);
	V2, mV2 := quo< Ok | 2*Ok>;
	V2gens := [];
	for i in [1..n] do
		L1 := [];
		for j in [1..n] do
			if j eq i then 
				Append(~L1,1);
			else
				Append(~L1,0);
			end if;
		end for;
		Append(~V2gens,V2!L1);
	end for;
	G, Aut, mG := AutomorphismGroup(K);
	GroupGens := Generators(G);
	M := [];
	for a in GroupGens do
		Mat := Matrix(GF(2), [Eltseq(V2!(mG(a)((g@@mV2)))) : g in V2gens]);
		Append(~M,Mat);
	end for;
	Fg := GModule(G, M);
	return DirectSumDecomposition(Fg);
end intrinsic;






intrinsic Sel2g(L::SeqEnum) -> SeqEnum
	{Takes a field defining a polynomial, returns the F[g] module V2}
	K := MakeField(L);
	assert IsTotallyReal(K);
	Ok := Integers(K);
	n := Degree(K);
	Sel2, mS := pSelmerGroup(2, {Parent(2*Ok) | });
	Sel2gens := [];
	for i in [1..#Generators(Sel2)] do
		L1 := [];
		for j in [1..#Generators(Sel2)] do
			if j eq i then 
				Append(~L1,1);
			else
				Append(~L1,0);
			end if;
		end for;
		Append(~Sel2gens,Sel2!L1);
	end for;
	G, Aut, mG := AutomorphismGroup(K);
	GroupGens := Generators(G);
	M := [];
	for a in GroupGens do
		Mat := Matrix(GF(2), [Eltseq(mS(mG(a)((g@@mS)))) : g in Sel2gens]);
		Append(~M,Mat);
	end for;
	Fg := GModule(G, M);
	return DirectSumDecomposition(Fg);
end intrinsic;






intrinsic Vinftyrep(L::SeqEnum) -> SeqEnum
	{Takes a field defining a polynomial, returns the F[g] module Vinfty}
	K := MakeField(L);
	G, Aut, mG := AutomorphismGroup(K);
	Fg := GModule(G, GF(2));
	return DirectSumDecomposition(Fg);
end intrinsic;



intrinsic F2decomp(n::RngIntElt) -> SeqEnum
	{Takes a field defining a polynomial, All the info}
	G := CyclicGroup(n);
	Fg := GModule(G, GF(2));
	return DirectSumDecomposition(Fg);
end intrinsic;



intrinsic Gstructure(L::SeqEnum) -> SeqEnum
	{Takes a field defining a polynomial, All the info}
	K := MakeField(L);
	Ok := Integers(K);
	Decomp := DecompositionType(Ok,2);
	return Sel2g(L), Vinftyrep(L), V2rep(L), Decomp, IsotropyRank(K);
end intrinsic;






intrinsic Allkernels(L::SeqEnum) -> SeqEnum
	{Takes a field defining a polynomial, returns the kernels}
	F := MakeField(L);
  	R := Integers(F);
  	D := Discriminant(R);
  	assert Signature(F) eq Degree(F);
  	r1 := Degree(F);
	twofact := Factorization(2*R);
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
			while Integers()!(Norm(sel2i*z^2)) mod 2 eq 0 do
				z +:= (-1)^(Random(2))*Random(bbi2_basis);
			end while;
			assert mS(sel2i*z^2) eq mS(sel2i);
			Sel2gens[i] := sel2i*z^2;
		end if;
	end for;
	R4R, m4R := quo<R | 4*R>;
	U4R, mU4R := UnitGroup(R4R);
	U4Rsq, mU4Rsq := quo<U4R | [2*U4R.i : i in [1..#Generators(U4R)]]>;
	
	kerinfty := [];
	ker2 := [];

	for s in Sel2 do
		H := [ (1+ux)/2 : ux in RealSigns(s)];
		O := [0 : ux in RealSigns(s)];
		if H eq O then
			Append(~kerinfty,s);
		end if;
	end for;

	for s in Sel2 do
		H := Eltseq(mU4Rsq(m4R(s)@@mU4R));
		O := [0 : i in [1..r1]];
		if H eq O then
			Append(~ker2,s);
		end if;
	end for;

	/*E := Matrix(GF(2),[[h(ux) : ux in RealSigns(m(U.i))] cat Eltseq(mU4Rsq(m4R(m(U.i))@@mU4R)) : i in [1..Degree(F)]]);
	M := Matrix(GF(2),[[h(ux) : ux in RealSigns(s)] cat Eltseq(mU4Rsq(m4R(s)@@mU4R)) : s in Sel2gens]);
	k := Dimension(Kernel(Submatrix(M,1,r1+1,Nrows(M),r1))) - Dimension(Kernel(M));
	sgnrk := Rank(Submatrix(E,1,1,r1,r1));
	rhooo := r1-sgnrk;
	rho := tworank(AbelianInvariants(ClF));
	rhoplus := tworank(AbelianInvariants(ClFplus));
	is_split := (rhoplus eq rho+rhooo); */
  return [* kerinfty, ker2  *];
end intrinsic;
