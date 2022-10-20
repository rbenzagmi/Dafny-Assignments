//Noy Shani - 208279406
//Roni Ben Zagmi - 208799684

method Main()
{
	var z := IterativeIntExpo(2, 3);
	assert z == 8;
}

function RecursiveIntExpo(x: int, y: nat): int
	decreases y
{
	if y == 0 then 1 else x * RecursiveIntExpo(x, y-1)
}

// TODO: implement iteratively; NO NEED to document the proof obligations
method IterativeIntExpo(x: int, y: nat) returns (z: int)
	ensures z == RecursiveIntExpo(x, y)
{
	var i := 1;
	z := 1;
	if (y != 0) 
	{
		z := x;
		assert z == RecursiveIntExpo(x, i) && 0 <= i <= y;
		while (i < y) 
		invariant z == RecursiveIntExpo(x, i) && 0 <= i <= y;
		{
			z := z*x;
			i := i+1;
		}
		assert z == RecursiveIntExpo(x, y);
	}
}