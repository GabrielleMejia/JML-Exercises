---
title: JML Tutorial - Exercises - Verifying Method Calls
---
# Verifying Method Calls Exercises:
## **Question 1**
**Write two functions that perform the following: an function that adds two integer arrays and a function that returns true if the arrays to be added are of the same size. Use the following function headers to help you. Determine the specifications needed to verify your functions.**
```Java
public int[] addArrays(int[] a, int[] b);

public boolean sameSize(int[] a, int[] b);
```
**Asnwer and Explanation:**
We are tasked with writing a program that adds two integer arrays, we will break up this process into two functions. The `addArrays()` will take in two integer arrays `a` and `b` and will add their elements if they are the same size. The `sameSize()` will also take in the arrays `a` and `b` and check if they have the same length. Given this information we can write something like the following program:
```Java
public int[] addArrays(int[] a, int[] b) {
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
        		newArr[i] = a[i] + b[i];
		}	
	}
	return new int[0];
}

public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
The `addArrays()` function calls `sameSize()`, and if `a.length == b.length` a new integer array `newArr` is created of size `a.length`. Note, that it could also be of the size `b.length`, it doesn’t really matter since we have determined at this point they are the same size. After creating `newArr` there is a for-loop that runs for the length of `a` and will store `a[i] + b[i]` at `newArr[i]`. If `a` and `b` are NOT the same size the function will return an empty integer array which is written as `new int[0]`. The `sameSize()` function simply returns the result of checking if `a.length == b.length`, that is to say it will return true if `a` and `b` are the same length, and false otherwise. 
 
Now that we have written the code, what preconditions and postconditions should be included? Well, first let’s write any JML specifications for `sameSize()` as it is a more straightforward function. For `sameSize()` we can ensure that the result will always be equivalent to whether `a.length == b.length` (i.e true or false). So we might write something like the following for `sameSize()`
```Java
public int[] addArrays(int[] a, int[] b) {		
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			newArr[i] = a[i] + b[i];
		}	
	}
	return new int[0];
}
//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}

```
As for the `addArrays()` function let’s think about what preconditions we might want to require; we are adding the elements from `a` and `b` and any time we are dealing with integer arithmetic we want to make sure we remain in the size of type int. So we can use the `forall` clause to check that `a[i] + b[i] <= Integer.MAX_VALUE`. Additionally, since the function will return an empty array if `a` and `b` aren’t the same size we can ensure two things to be true. The `\result` will be an integer array where for all index `j` less than the length of resulting array, `\result[j]` will be equal to `a[j] + b[j]`. Secondly, if `a` and `b` aren;t the same length then `\result` will be null. As we move on you will see better ways of handling exceptions and different method behaviors, but for now we can write something like the following: 
```Java
//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
//@ ensures (\forall int j; 0 <= j < \result.length; \result[j] == a[j]+b[j]) || \result == null;
public int[] addArrays(int[] a, int[] b) {		
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			newArr[i] = a[i] + b[i];
		}	
	}
	return new int[0];
}
	
//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
Now, since we are dealing with a for-loop we also have to include an assume statement so we don’t run into any issues going out-of-bounds. Additionally, since we're adding `a[i] + b[i]` we need to account for potential overflow errors like we did in our precondition, so let's also include an assume statement that handles this. 
```Java
//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
//@ ensures (\forall int j; 0 <= j < \result.length; \result[j] == a[j]+b[j]) || \result == null;
public int[] addArrays(int[] a, int[] b) {		
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			//@ assume 0 <= i < a.length;
			//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
			newArr[i] = a[i] + b[i];
		}	
	}
	return new int[0];
}

//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
 Now that we have included everything from past tutorials, what new specifications do we need after reading "Method Calls?" Recall how a method call is verified; at the call site assert the precondition of the called method, and then assume the callee's postconditions. In our program we only have one preconditions for the caller function `addArrays()` which we’ve already accounted for, and one postcondition for the callee function `sameSize()`. So we can write the following:
```Java
//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
//@ ensures (\forall int j; 0 <= j < \result.length; \result[j] == a[j]+b[j]) || \result == null;
public int[] addArrays(int[] a, int[] b) {	
	if(sameSize(a, b)) {
		//@ assert sameSize(a, b);
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			//@ assume 0 <= i < a.length;
			//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
			newArr[i] = a[i] + b[i];
		}	
	}
	return new int[0];
}

//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```

**Learning Objective:** 
The goal of this exercise is to see if the student understands how to verify method calls. This is a rather simple example, so the student should be able to identify the statements needed to verify functions. The exercise also checks that the student understands and can utilize information from past exercises as well. It also checks if the student can also identify all specifications needed - not just those used for verifying method calls.

## **Resources:**
+ [Verifying Method Calls Exercises](VerifyingMethodCallsEx.md)
+ [Question 1 Java](MethodCallsExample1.java)
