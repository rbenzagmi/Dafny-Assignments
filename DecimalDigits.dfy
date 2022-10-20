//Noy Shani - 208279406
//Roni Ben Zagmi - 208799684

method Main()
{
	var a := new nat[3];
	var n, start := 8, 0;
	assert NumberOfDecimalDigits(n, 1);
	ghost var q0 := a[..];
	var len, fits := IntToString(n, a, start);
	assert DecimalDigits(a[start..start+len], n);
	assert fits && len == 1 && a[0] == 8 && a[1..] == q0[1..];
}

predicate IsSingleDecimalDigit(d: nat) { 0 <= d && d <= 9 }

predicate NoLeadingZeros(q: seq<nat>)
	requires |q| != 0
{
	q[0] == 0 ==> |q| == 1
}

predicate IsDecimal(q: seq<nat>)
{
	|q| != 0 && (forall d :: d in q  ==> IsSingleDecimalDigit(d)) && NoLeadingZeros(q)
}

function SeqToNat(q: seq<nat>): nat
	requires IsDecimal(q)
{
	if |q| == 1 then q[0] else SeqToNat(q[..|q|-1])*10+q[|q|-1]
}

predicate DecimalDigits(q: seq<nat>, n: nat)
{
	IsDecimal(q) && SeqToNat(q) == n
}

predicate NumberOfDecimalDigits(n: nat, length: nat)
	decreases length
{
	(length == 1 && IsSingleDecimalDigit(n)) ||
	(length > 1 && !IsSingleDecimalDigit(n) && NumberOfDecimalDigits(n/10, length-1)) 
}

predicate Pre(n: nat, q: seq<nat>, start: nat)
{
	start < |q|
}

predicate Post(n: nat, q: seq<nat>, q0: seq<nat>, start: nat, length: nat, fits: bool)
	requires |q| == |q0|
{
	NumberOfDecimalDigits(n, length) &&
	fits == (start + length <= |q|) &&
	(fits ==> q[..start] == q0[..start] && DecimalDigits(q[start..start+length], n) && q[start+length..] == q0[start+length..]) &&
	(!fits ==> q == q0)
}

// get a natural number and return the number of the digits in the number
method len(n: nat) returns (length: nat) 
	requires n >=  0
	ensures NumberOfDecimalDigits(n, length)
{
	if(0 <= n <= 9) 
	{
		length := 1; // just one digit
	} 
	else
	{
		var a := len(n/10);  	
		length := a + 1; // adding 1 to the recursive call
	}
}

function method ComputeInt(n: int) : seq<int>
{
	if (n < 10) then ([n]) else ComputeInt(n/10) + [n%10] 
}

method recursiveIntToString(n: nat, a: array<nat>, start: nat, endExcluded: int)	
	requires 0 <= start < endExcluded <= a.Length
	requires NumberOfDecimalDigits(n, endExcluded-start)
	ensures a[start..endExcluded] == ComputeInt(n) && IsDecimal(a[start..endExcluded])
	ensures a[..start] == old(a[..start]) && a[endExcluded..] == old(a[endExcluded..])
	ensures SeqToNat(a[start..endExcluded] ) == n
	modifies a
	decreases n
{		
	if (n < 10) 
	{
		a[endExcluded-1] := n; // base case
	} 
	else
	{
		a[endExcluded-1] := n%10;
		recursiveIntToString(n/10,a,start,endExcluded-1);	
		assert IsDecimal(a[start..endExcluded]);
	}				
}

// TODO: provide an implementation; NO NEED to document the proof obligations
method IntToString(n: nat, a: array<nat>, start: nat) returns (length: nat, fits: bool)
	requires Pre(n, a[..], start)
	ensures Post(n, a[..], old(a[..]), start, length, fits)
	modifies a
{
	length := len(n); // calculate the number of the digits in n
	fits := start + length <= a.Length;	// checking if the mission is possible
	if (fits)
	{
		recursiveIntToString(n, a, start, start+length); // put n in the array from index start
	}
}