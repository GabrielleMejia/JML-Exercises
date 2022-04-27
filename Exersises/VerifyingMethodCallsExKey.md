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

**Learning Objective:** 

## **Resources:**
+ [Verifying Method Calls Exercises](VerifyingMethodCallsEx.md)
+ [Question 1 Java](MethodCallsExample1.java)
