//Noy Shani - 208279406
//Roni Ben Zagmi - 208799684

method Main() {
	var a, b := new int[3], new int[2];
	a[0],a[1],a[2] := 3,5,8;
	b[0],b[1] := 4,7;
	print "Before merging the following two sorted arrays:\n";
	print a[..];
	print "\n";
	print b[..];
	ghost var AB := multiset(a[..]+b[..]);
	assert Sorted(a[..]) && Sorted(b[..]);
	MergeSortedArrays(a, b, AB);
	assert multiset(a[..]+b[..]) == AB;
	assert Sorted(a[..]+b[..]);
	print "\nAfter merging:\n";
	print a[..]; // [3,4,5]
	print "\n";
	print b[..]; // [7,8]
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

function findMin(a:int, b:int) :int
{
	if a <= b then a else b
}

predicate checkingLastPred(temp:seq<int>, a:seq<int>, b:seq<int>, i:int, j: int, t:int)
	requires 0 <= i <= |a| && 0 <= j <= |b| && t == i+j && 0 <= t <= |temp|
{
	t > 0 ==> (j-1 >= 0 && i < |a| && temp[t-1] == findMin(a[i],b[j-1])) || 
					(i-1 >= 0 && j < |b| && temp[t-1] == findMin(a[i-1],b[j]))
}

// TODO: implement iteratively; NO NEED to document the proof obligations
method MergeSortedArrays(a: array<int>, b: array<int>, ghost AB: multiset<int>)
	requires Sorted(a[..]) && Sorted(b[..])
	requires multiset(a[..]+b[..]) == AB
	requires a != b // added on 1/8 (in its absence, when the same array is sent twice, if it contains at least two different elements, the merge is infeasible!)
	ensures Sorted(a[..]+b[..])
	ensures multiset(a[..]+b[..]) == AB
	modifies a,b
{
	var temp_array := new int[a.Length+b.Length];
	var i := 0;
	var j := 0;
	while(i < a.Length && j < b.Length) // filling temp_array with a+b until one of the arrays (a/b) is over	
		invariant multiset(a[..]+b[..]) == AB										
		invariant Sorted(a[..]) && Sorted(b[..])
		invariant 0 <= i <= a.Length
		invariant 0 <= j <= b.Length
		invariant 0 <= i+j <= temp_array.Length
		invariant i+1 < a.Length ==>  a[i] <=  a[i+1]
		invariant j+1 < b.Length ==>  b[j] <=  b[j+1]	
		invariant checkingLastPred(temp_array[..],a[..],b[..],i,j,i+j)	
		invariant multiset(temp_array[..(i+j)]) == multiset(a[..i]+b[..j])		
		invariant Sorted(temp_array[..(i+j)])
	{
		if(a[i] <= b[j])
		{
			temp_array[i+j] := a[i];				
			i := i+1;
		}
		else
		{
			temp_array[i+j] := b[j];
			j := j+1;
		}
	}
	if(i == a.Length && j < b.Length) // all a array are in temp_array and now we fill temp_array with the rest of b array 
	{
		assert i+j > 0 ==> (i-1 >=0 && j < b.Length && temp_array[(i+j)-1] == findMin(a[i-1],b[j]));
		assert Sorted(temp_array[..(i+j)]);
		assert Sorted(b[..]);
		while(j < b.Length)	
			invariant multiset(a[..]+b[..]) == AB
			invariant 0 <= i+j <= temp_array.Length && 0 <= j <= b.Length
			invariant Sorted(temp_array[..(i+j)])
			invariant multiset(temp_array[..(i+j)]) == multiset(a[..i]+b[..j])
			invariant ((0 < i+j <= temp_array.Length && 0 <= j < b.Length) ==> temp_array[i+j-1] <= b[j])
			invariant Sorted(b[..])
			decreases b.Length - j
		{
			assert ((0 < i+j <= temp_array.Length) ==> temp_array[i+j-1] <= b[j]);
			temp_array[i+j] := b[j];
			assert i+j > 0 ==> temp_array[i+j-1] <= temp_array[i+j];
			assert Sorted(b[..]);
			assert j+1 < b.Length ==> b[j] <= b[j+1];
			j := j+1;
		}
		assert multiset(a[..]+b[..]) == AB;
		assert i == a.Length ==> a[..i] == a[..];
		assert j == b.Length ==> b[..j] == b[..];
		assert i+j == temp_array.Length ==> temp_array[..i+j] == temp_array[..];
		assert multiset(temp_array[..]) == multiset(a[..]+b[..]);
	}
	else // all b array are in temp_array and now we fill temp_array with the rest of a array
	{
		assert i+j > 0 ==> (j-1 >= 0 && i < a.Length && temp_array[i+j-1] == findMin(a[i],b[j-1])) ;
		assert Sorted(temp_array[..(i+j)]);
		assert Sorted(a[..]);
		while(i < a.Length)
			invariant multiset(a[..]+b[..]) == AB
			invariant 0 <= i+j <= temp_array.Length && 0 <= i <= a.Length
			invariant Sorted(temp_array[..(i+j)])
			invariant multiset(temp_array[..(i+j)]) == multiset(a[..i]+b[..j])
			invariant ((0 < i+j <= temp_array.Length && 0 <= i < a.Length) ==> temp_array[i+j-1] <= a[i])
			invariant Sorted(a[..])
			decreases a.Length - i
		{
			assert ((0 < i+j <= temp_array.Length) ==> temp_array[i+j-1] <= a[i]);
			temp_array[i+j] := a[i];
			assert i+j > 0 ==> temp_array[i+j-1] <= temp_array[i+j];
			assert Sorted(a[..]);
			assert i+1 < a.Length ==> a[i] <= a[i+1];
			i := i+1;
		}
		assert multiset(a[..]+b[..]) == AB;
		assert i == a.Length ==> a[..i] == a[..];
		assert j == b.Length ==> b[..j] == b[..];
		assert i+j == temp_array.Length ==> temp_array[..i+j] == temp_array[..];
		assert multiset(temp_array[..]) == multiset(a[..]+b[..]);
	}
	// in this point we get temp_array with all the numbers of a and b - when temp_array is sorted
	var q1 := 0;	
	while (q1 < a.Length) // filling a array with |a.length| numbers from temp_array
		invariant multiset(temp_array[..]) == AB
		invariant Sorted(temp_array[..])
		invariant 0 <= q1 <= a.Length
		invariant 0 < q1 < a.Length ==>  Sorted(a[..q1])
		invariant 0 < q1 <= a.Length ==>  a[..q1] == temp_array[..q1]
	{
		a[q1] := temp_array[q1];
		q1 := q1+1;
	}
	var q2 := 0;
	while (q2 < b.Length) // filling b array with |b.length| numbers from temp_array
		invariant 0 <= q2 <= b.Length
		invariant a.Length <= temp_array.Length
		invariant b.Length <= temp_array.Length
		invariant a.Length + b.Length == temp_array.Length
		invariant multiset(temp_array[..]) == AB
		invariant a[..] == temp_array[..a.Length]
		invariant Sorted(temp_array[..])
		invariant 0 < q2 <= b.Length ==> b[..q2] == temp_array[a.Length..a.Length+q2]
		invariant multiset(a[..]) == multiset(temp_array[..a.Length])
		invariant 0 < q2 <= b.Length ==> multiset(b[..q2]) == multiset(temp_array[a.Length..(a.Length+q2)]) 
	{
		b[q2] := temp_array[a.Length+q2];
		q2 := q2+1;
	}	
	assert multiset(temp_array[..]) == AB;
	assert Sorted(temp_array[..]);
	assert a.Length + b.Length == temp_array.Length;
	assert a[..] == temp_array[..a.Length];	
	assert b.Length !=0 ==> 0 <= a.Length < temp_array.Length;
	assert temp_array[..a.Length] + temp_array[a.Length..] == temp_array[..]; 
	assert a[..]+b[..] == temp_array[..];
	assert Sorted(a[..]+b[..]);
	assert multiset(a[..]+b[..]) ==  AB;
}