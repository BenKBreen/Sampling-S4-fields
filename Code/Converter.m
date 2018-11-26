//###################  Converter ############################//


intrinsic Convert(L::List) -> SeqEnum
	{Changes a list of polynomials to a list of tuple of coefficients}
	R<x> := PolynomialRing(Rationals());
	Coeffs := [Coefficients(R!i) : i in L];
	return Coeffs;
end intrinsic;



intrinsic MakeField(L::SeqEnum) -> FldNum
	{Changes tuple of coefficients for a defining polynomial into a NumberField}
	R<x> := PolynomialRing(Rationals());
	K := NumberField(R!L);
	return K;
end intrinsic;


intrinsic LMFDBconvert(L::List) -> SeqEnum
	{Changes a list of polynomials to a list of tuple of coefficients}
	R<x> := PolynomialRing(Rationals());
	Coeffs := [Coefficients(R!i[1]) : i in L];
	return Coeffs;
end intrinsic;
