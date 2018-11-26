//###################  Isotropy Rank k ############################//


//This code return the distribution of isotropy ranks 


intrinsic tworank(G::GrpAb) -> RngIntElt
  {Input: Abelian Group     Output: 2-rank of the Group}
  
  Invar := AbelianInvariants(G);
  return #[c : c in Invar | c mod 2 eq 0];

end intrinsic;


intrinsic IsotropyRank(K::FldNum) -> RngIntElt
	{Returns the Isotropy Rank of a Number Field K}
	SetClassGroupBounds("GRH");
	
	Ok := Integers(K);
	ClF := ClassGroup(Ok);
	ClFplus := RayClassGroup(1*Ok, [1..Degree(K)]);
	rho := tworank(ClF);
	rhoplus := tworank(ClFplus);
	Isorank := rhoplus - rho;
	return Isorank;

end intrinsic;




intrinsic IsotropyDistribution(T::SeqEnum) -> SeqEnum
	{Input:   T: List of coefficients for polynomials     Output: Tuple of percentages [k=0, k=1, k=2]}
	
	V0 := 0;
	V1 := 0;
	V2 := 0; 

	SetClassGroupBounds("GRH");
	R<x> := PolynomialRing(Rationals());
	
	if #T eq 0 then
		return ["none"];
	else
		for i in T do
			K := NumberField(R!i);
			k := IsotropyRank(K);
			if k eq 0 then
				V0 := V0 +1;
			elif k eq 1 then
				V1 := V1 +1;
			else
				V2 := V2 +1;
			end if;
		end for;
		return Real(V0/#T), Real(V1/#T), Real(V2/#T);
	end if;
end intrinsic;