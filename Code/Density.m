//###################  Density counts ############################//


intrinsic RestrictedPartition(n::RngIntElt, k::RngIntElt) -> RngIntElt
	{Returns q(n,k), the number of partitions of n with length at most k}
	count := 0;
	for i in [1..k] do
		num := #Partitions(n,i);
		count := count + num;
	end for;
	return count;
end intrinsic;



intrinsic WeightedSum(n::RngIntElt, p::RngIntElt) -> RngIntElt
	{Returns sum from i=0 to i = n of q(n,i)/p^i }
	count := 1;
	for i in [1..n-1] do
		num := RestrictedPartition(i,n-i)/p^i;
		count := count + num;
	end for;
	return count;
end intrinsic;




intrinsic Dvalues(n::RngIntElt) -> SeqEnum
	{Returns the values a_n,b_n,c_n,d_n,e_n necassary for density computations}
	P := [i : i in PrimesUpTo(100000000) | i mod 4 eq 3];
	R := RealField(10);
	Z := Integers();
	m := Z!(n/2);

	an := WeightedSum(m,2)/(WeightedSum(n,2)*2^(m));
	bn := R!1;
	for p in P do 
		bn := bn*(1-WeightedSum(m,p)/(WeightedSum(n,p)*p^(m)));
	end for;
	cn := an/2^(m);
	dn := an/2^(n);
	if n mod 4 ne 0 then
		en := 0;
	else
		en := WeightedSum(Z!(n/4),2)/(WeightedSum(n,2)*2^(2*n));
	end if;
	return [R!an, R!bn, R!cn, R!dn, R!en];
end intrinsic;





intrinsic Densities(n::RngIntElt) -> SeqEnum
	{Returns the densities for the computations}
	
	L := Dvalues(n);

	an := L[1];
	bn := L[2];
	cn := L[3];
	dn := L[4];
	en := L[5];

	V0 := en;
	V1 := cn-en;
	V2 := (1-an+dn-en)*bn;
	V3 := (1-an+dn-en)*(1-bn) + (dn-en);
	V4 := (an-cn-2*dn +2*en)*bn;
	V5 := (an-cn-2*dn+ 2*en)*(1-bn);

	return [V0*100,V1*100,V2*100,V3*100,V4*100,V5*100];
end intrinsic;









