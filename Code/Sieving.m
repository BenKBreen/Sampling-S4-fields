//###################  Sieve ############################//


// TODO: 
// Tests


//######## Preliminary intrinsics ##################//

intrinsic PinSel(K::FldNum) -> Any
 	{Tests if the Fields K has p as a vector in the two selmer group}
	D := Discriminant(K);
	OK := Integers(K);
	Dprimes := [p[1] : p in Factorization(D) | p[1] mod 4 eq 3];
	count := 0;
	for p in Dprimes do
		Fact := Factorization(p*OK);
		Ram := Set([i[2] mod 2 : i in Fact]);
		if Ram eq {0} then
			count := 1;
			break;
		end if;
	end for;

	if count eq 0 then
		return "false";
	else 
		return "true";
	end if;
end intrinsic;


intrinsic twoinSel(K::FldNum) -> Any
 	{Tests if the Fields K has p as a vector in the two selmer group}
	OK := Integers(K);
	Fact := Factorization(2*OK);
	Ram := Set([i[2] mod 2 : i in Fact]);
	if Ram eq {0} then
		R<x> := PolynomialRing(Rationals());
		L := ext<K | x^2-2>;
		if IsUnramified(L) then
			return "false";
		else
			return "true";
		end if;
	else
		return "false";
	end if;
end intrinsic;




intrinsic minusoneunram(K::FldNum) -> Any
	{Tests if K(i)/K is unramified at finite places}
	R<x> := PolynomialRing(Rationals());
	L := ext<K | x^2+1>;
	if IsUnramified(L) then
		return "true";
	else
		return "false";
	end if;
end intrinsic;





intrinsic minustwounram(K::FldNum) -> Any
	{Tests if K(-2)/K is unramified at finite places}
	R<x> := PolynomialRing(Rationals());
	L := ext<K | x^2+2>;
	if IsUnramified(L) then
		return "true";
	else
		return "false";
	end if;
end intrinsic;



//###################  Actual sieve ############################//

intrinsic Sel2Sieve(L::SeqEnum) -> SeqEnum
	{Sorts a tuple of Fields into 6 boxes V1,V2,V3,V4,V5,V6 based on the image of Sel2(K)}
	V1 := [];
	V2 := [];
	V3 := [];
	V4 := [];
	V5 := [];
	V6 := [];
	for i in L do
		K := MakeField(i);
		if minusoneunram(K) eq "true" then
			if twoinSel(K) eq "true" then
				Append(~V3,i);
			else
				Append(~V1,i);
			end if;
		else
			if PinSel(K) eq "true" then
				if twoinSel(K) eq "true" then
					if minustwounram(K) eq "true" then
						Append(~V4,i);
					else
						Append(~V6,i);
					end if;
				else
					Append(~V4,i);
				end if;
			else
				if twoinSel(K) eq "true" then
					if minustwounram(K) eq "true" then
						Append(~V4,i);
					else
						Append(~V5,i);
					end if;
				else
					Append(~V2,i);
				end if;
			end if;
		end if;
	end for;

	return [V1,V3,V2,V4,V5,V6];
end intrinsic;
