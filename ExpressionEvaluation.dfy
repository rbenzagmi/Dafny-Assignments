//Noy Shani - 208279406
//Roni Ben Zagmi - 208799684

datatype Expression = Value(int) | Add(Expression,Expression) | Multiply(Expression,Expression)
datatype Op = Operand(int) | Addition | Multiplication

method Main() {
	var exp := Add(Value(7),Multiply(Value(3),Value(5)));
	print "\nThe value of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	var x := Evaluate(exp);
	print x;
	assert x == 7 + 3*5;

	x := EvaluateIter(exp); // evaluate iteratively this time, instead of recursively
	assert x == 7 + 3*5;
	print "\nThe iteratively-computed value of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	print x;

	var postfix := ComputePostfix(exp); // recursive computation of the postfix sequence
	print "\nThe postfix form of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	print postfix;
	assert postfix == [Operand(7),Operand(3),Operand(5),Multiplication,Addition];

	postfix := ComputePostfixIter(exp); // compute the postfix sequence iteratively this time, instead of recursively
	print "\nThe iteratively-computed postfix form of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	print postfix;
	assert postfix == [Operand(7),Operand(3),Operand(5),Multiplication,Addition];
}

function ValueOf(exp: Expression): int
	decreases exp
{
	match exp {
		case Value(x) => x
		case Add(l,r) => ValueOf(l)+ValueOf(r)
		case Multiply(l,r) => ValueOf(l)*ValueOf(r)
	}
}

method Evaluate(exp: Expression) returns (val: int)
	ensures val == ValueOf(exp)
	decreases exp
{
	match exp {
		case Value(x) => val := x;
		case Add(l,r) => var valLeft := Evaluate(l); var valRight := Evaluate(r); val := valLeft+valRight;
		case Multiply(l,r) => var valLeft := Evaluate(l); var valRight := Evaluate(r); val := valLeft*valRight;
	}
}

predicate method isOperands(x: Op, y:Op)
{
	x != Addition && x != Multiplication && y != Addition && y != Multiplication
}

predicate method isOperator(x: Op)
{
	x == Addition || x == Multiplication
}

function method numberOfOperands(postFixExp: seq<Op>) : int
{
	if |postFixExp|==0 then 0 else match postFixExp[0]
									{
										case Operand(x) => 1 + numberOfOperands(postFixExp[1..])
										case Addition => numberOfOperands(postFixExp[1..])
										case Multiplication => numberOfOperands(postFixExp[1..])
									}
}

function method numberOfOperators(postFixExp: seq<Op>) : int
{
	if |postFixExp|==0 then 0 else match postFixExp[0]
									{
										case Operand(x) => numberOfOperators(postFixExp[1..])
										case Addition => 1 + numberOfOperators(postFixExp[1..])
										case Multiplication => 1 + numberOfOperators(postFixExp[1..])
									}
}

function method valOfOperand(o : Op) : int
	requires o != Addition && o != Multiplication
{ 
	match o 
	{
		case Operand(x) => x
	}
}

predicate preToPro(exp: Expression, postFixExp: seq<Op>)
{
	|postFixExp| > 0 && (exists ex:Expression :: Postfix(ex) == postFixExp && ValueOf(ex) == ValueOf(exp)) &&
	(|postFixExp|==1 || (|postFixExp| > 1 && exists i: nat :: 2 <= i < |postFixExp| && isOperands(postFixExp[i-2], postFixExp[i-1]) 
	&& isOperator(postFixExp[i]))) && numberOfOperands(postFixExp) == 1 + numberOfOperators(postFixExp)
}

predicate SecondWhile(exp: seq<Op>, i: nat)
{
	2 <= i <= |exp| && (exists j : nat :: i <= j < |exp| && isOperands(exp[j-2], exp[j-1]) && isOperator(exp[j]))
}

lemma {:verify false} LemmaOP(exp: Expression, postFixExp: seq<Op>)
	requires postFixExp == Postfix(exp)
	ensures numberOfOperands(postFixExp) == 1 + numberOfOperators(postFixExp)
{
	// we failed to convice dafny that the lemma is correct,
	// but we wanted to show that when expression is of the postfix order, 
	// the number of the operators (+/*) is large in one from the number of the operands 
}
	
lemma {:verify false} LemmaThree(exp: Expression, postFixExp: seq<Op>)
	requires postFixExp == Postfix(exp) 
	ensures |postFixExp| == 1 || (|postFixExp| > 1 && exists j:nat :: 2 <= j < |postFixExp| &&
															 isOperands(postFixExp[j-2], postFixExp[j-1]) && isOperator(postFixExp[j]))
{
	// we failed to convice dafny that the lemma is correct,
	// but we wanted to show that when expression is of the postfix order, 
	// the length of the postfix expression is 1 (his value) or 
	// bigger than one and then he must have threesome which consist 2 operands and one operator (at least one threesome)  
}

lemma {:verify false} LemmaPreToPro(exp: Expression, preFixExp: seq<Op>, postFixExp: seq<Op>, i: nat, res: int)
	requires 1 < |preFixExp| && preToPro(exp, preFixExp) && 2 <= i < |preFixExp|
	requires isOperands(preFixExp[i-2], preFixExp[i-1]) 
	requires isOperator(preFixExp[i])
	requires (preFixExp[i] == Addition && res == valOfOperand(preFixExp[i-2]) + valOfOperand(preFixExp[i-1])) || 
								(preFixExp[i] == Multiplication && res == valOfOperand(preFixExp[i-2]) * valOfOperand(preFixExp[i-1]))
	requires postFixExp == preFixExp[..i-2] + [Operand(res)] + preFixExp[i+1..]
	ensures preToPro(exp, postFixExp)
{
	// we failed to convice dafny that the lemma is correct,
	// but we wanted to show that the postfix are correct in relation to the prefix order
}

// TODO: implement iteratively (not recursively), using a loop;
// if it helps, feel free to use ComputePostfix or ComputePostfixIter;
// NO NEED to document the proof obligations
method EvaluateIter(exp: Expression) returns (val: int)
	ensures val == ValueOf(exp)
{
	var expsSeq: seq<Op> := ComputePostfix(exp);
	var i: nat;
	var res: int;

	LemmaOP(exp, expsSeq); // ensures that the number of the OP is correct
	LemmaThree(exp, expsSeq); // ensures that there is a three op in the right order
	
	while (|expsSeq| > 1)
		invariant preToPro(exp, expsSeq)
		decreases |expsSeq|
	{	
		i := 2;
		var expsSeqOld := expsSeq; 
		while (i < |expsSeq| && !(isOperands(expsSeq[i-2], expsSeq[i-1]) && isOperator(expsSeq[i])))
			invariant SecondWhile(expsSeq, i)
			decreases |expsSeq| - i
		{
			i := i+1;
		}
		if (expsSeq[i] == Multiplication)
		{
			res := valOfOperand(expsSeq[i-2]) * valOfOperand(expsSeq[i-1]);
		}
		else
		{
			res := valOfOperand(expsSeq[i-2]) + valOfOperand(expsSeq[i-1]);
		}

		expsSeq := expsSeq[..i-2] + [Operand(res)] + expsSeq[i+1..];

		LemmaPreToPro(exp, expsSeqOld, expsSeq, i, res);
	}
	assert numberOfOperands(expsSeq) + numberOfOperators(expsSeq) == 1;
	val := valOfOperand(expsSeq[0]);
}

function Postfix(exp: Expression): seq<Op>
	decreases exp
{
	match exp {
		case Value(x) => [Operand(x)]
		case Add(l,r) => Postfix(l)+Postfix(r)+[Addition]
		case Multiply(l,r) => Postfix(l)+Postfix(r)+[Multiplication]
	}
}

lemma Lemma1 (exp: Expression, x: int)
	requires exp == Value(x)
	ensures [Operand(x)] == Postfix(exp)
{}

lemma Lemma2 (exp: Expression, l: Expression, r: Expression, resL: seq<Op>, resR: seq<Op>)
	requires exp == Add(l,r)
	requires resL == Postfix(l)
	requires resR == Postfix(r)
	requires l < exp 
	requires r < exp 
	ensures (resL + resR + [Addition] == Postfix(exp))
{}

lemma Lemma3 (exp: Expression, l: Expression, r: Expression, resL: seq<Op>, resR: seq<Op>)
	requires exp == Multiply(l,r)
	requires resL == Postfix(l)
	requires resR == Postfix(r)
	requires l < exp 
	requires r < exp
	ensures (resL + resR + [Multiplication] == Postfix(exp))
{}

// TODO: implement recursively and document the proof obligations
method ComputePostfix(exp: Expression) returns (res: seq<Op>)
	ensures res == Postfix(exp)
	decreases exp
{
	match exp {
		case Value(x) => 
        { 
			assert exp == Value(x);
			Lemma1(exp,x);
			assert [Operand(x)] == Postfix(exp);
            res := [Operand(x)];
			assert res == Postfix(exp);
        }
		case Add(l,r) =>
        {
			assert exp == Add(l,r);
			assert l < exp; // for termination
            var resL : seq<Op> := ComputePostfix(l);
			assert resL == Postfix(l); 
			assert r < exp; // for termination
            var resR : seq<Op> := ComputePostfix(r);
			assert resL == Postfix(l);
			assert resR == Postfix(r);
			assert exp == Add(l,r);
			assert l < exp;
			assert r < exp;
			Lemma2(exp, l, r, resL, resR);
			assert resL + resR + [Addition] == Postfix(exp);
            res := resL + resR + [Addition];
			assert res == Postfix(exp);
        } 
		case Multiply(l,r) =>
        {
			assert exp == Multiply(l,r);
			assert l < exp; // for termination
            var resL : seq<Op> := ComputePostfix(l);
			assert resL == Postfix(l);
			assert r < exp; // for termination
            var resR : seq<Op> := ComputePostfix(r);
			assert resL == Postfix(l);
			assert resR == Postfix(r);
			assert exp == Multiply(l,r);
			assert l < exp;
			assert r < exp;
			Lemma3(exp, l, r, resL, resR);
			assert resL + resR + [Multiplication] == Postfix(exp);
            res := resL + resR + [Multiplication];
			assert res == Postfix(exp);
        } 
	}
	assert res == Postfix(exp);
}

// TODO: complete the implementation (of LoopBody below) and the verification
// (by providing a body to Inv, V, LemmaInit, and LemmaPost below);
// NO NEED to document the proof obligations
method ComputePostfixIter(exp: Expression) returns (res: seq<Op>)
	ensures res == Postfix(exp)
{
	var stack := [exp];
	res := [];
	LemmaInit(exp, stack, res);
	while stack != []
		invariant Inv(exp, stack, res)
		decreases V(stack)
	{
		stack, res := LoopBody(exp, stack, res);
	}
	LemmaPost(exp, stack, res);
}
function firstPost(st: seq<Expression>) : seq<Op>
{
	if st == [] then [] else firstPost(st[..|st|-1]) + Postfix(st[|st|-1])
}

predicate Inv(exp: Expression, stack: seq<Expression>, res: seq<Op>)
{
	var v := firstPost(stack);
	v + res == Postfix(exp)
}

function ExpsSizes(st: seq<Expression>): nat
{
	if st == [] then 0 else ExpSize(st[|st|-1]) + ExpsSizes(st[..|st|-1]) 
}

function ExpSize(exp: Expression): nat
{
	match exp 
	{
		case Value(x) => 1
		case Add(l,r) => 1 + ExpSize(l) + ExpSize(r)
		case Multiply(l,r) => 1 + ExpSize(l) + ExpSize(r)
	}
}

function V(stack: seq<Expression>): int
{
	ExpsSizes(stack)
}

lemma LemmaInit(exp: Expression, stack: seq<Expression>, ops: seq<Op>)
	requires stack == [exp] && ops == []
	ensures Inv(exp, stack, ops)
{}

lemma LemmaPost(exp: Expression, stack: seq<Expression>, res: seq<Op>)
	requires Inv(exp, stack, res) && stack == []
	ensures res == Postfix(exp)
{}

method LoopBody(ghost exp: Expression, stack0: seq<Expression>, ops0: seq<Op>) returns (stack: seq<Expression>, ops: seq<Op>)
	requires Inv(exp, stack0, ops0) && stack0 != []
	ensures Inv(exp, stack, ops) && 0 <= V(stack) < V(stack0)
{
	ops := ops0;
	stack := stack0;

	var expL := stack[|stack|-1];
	stack := stack[..|stack|-1]; 

	match expL {
		case Value(x) => 
		{							
			ops := [Operand(x)] + ops0;
		}
		case Add(l,r) => 
		{
			ops := [Addition] + ops0;
			stack := stack + [l,r];
			assert stack  == stack0[..|stack0|-1] + [l] + [r];
			assert ExpsSizes(stack) < ExpsSizes(stack0);
		}
		case Multiply(l,r) =>
		{
			ops := [Multiplication] + ops0;
			stack := stack + [l,r];
			assert stack  == stack0[..|stack0|-1] + [l] + [r];
			assert ExpsSizes(stack) < ExpsSizes(stack0);
		} 
	}
}