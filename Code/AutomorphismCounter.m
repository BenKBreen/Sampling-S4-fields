//###################  Converter ############################//


intrinsic MakeForm(alt::RngIntElt, n::RngIntElt) -> Mtrx
	{Input: 0/1 for alternating or nonalternating, n is the dimension of the form}
	F := FiniteField(2);
	if alt eq 0 then
		assert IsEven(n);
		return PermutationMatrix(F, Reverse([1..n]));
	else
		return IdentityMatrix(F,n);
	end if;
end intrinsic;


intrinsic AutoCount(form::Mtrx) -> RngIntElt
	{Input:    form: Matrix for a form      Output: Number of automorphisms of the form}
	n := #Rows(form);
	F := FiniteField(2);
	G := GL(n,F);
 	counts := 0;
 	for i in G do
 		B := i*form*Transpose(i);
 		if B eq form then
 			counts := counts + 1;
 		end if;
 	end for;
 	return counts;
end intrinsic;


intrinsic AutoCountSub(form::Mtrx, S::SeqEnum ) -> RngIntElt
	{Input:     form: Matrix for a form,      S: Subspace as a tuple   Output: Number of automorphisms of the form that preserve S}
	n := #Rows(form);
	F := FiniteField(2);
	V := VectorSpace(F,n);
	G := GL(n,F);
	U := sub<V | S>;
 	counts := 0;
 	for i in G do
 		B := i*form*Transpose(i);
 		if B eq form then
 			S1 := [(V!j)*i : j in S];
 			U1 := sub<V | S1>;
 			if U eq U1 then 			
 				counts := counts + 1;
 			end if;
 		end if;
 	end for;
 	return counts;
end intrinsic;



