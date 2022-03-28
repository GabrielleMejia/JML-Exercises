---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Assume Statements Exercises Key:
## **Question 1**
**Write a function that takes in an integer array a and returns an array that is the reversal of a. Determine the specifications needed to verify the function.**

**Asnwer and Explanation:**
We are tasked with creating a function that returns an array that is the reversal of an array passed in. First, we know that one of our preconditions is that the array passed in is not null. Additionally, since the function is simply reversing the array and retuning it, we know that the result should be of the same length as the array passed in. So we can write the following function:
```java
//@ requires a != null;
//@ ensures \result.length == a.length;
public int[] reverseArray(int[] a) {
	int len = a.length;
	int[] b = new int[len];

	for (int i = 0; i < a.length; i++) {
		b[len - 1] = a[i];
		len--;			
	}
	
	return b;
}
```
The function above stores the length of array `a` and creates a new integer array `b`. We then create a for-loop that runs for `i < a.length`, and within the for-loop we set `b[len - 1] = a[i]`. This will set the last index of `b` to the first element in `a`. After we set the value of `b` at `len-1`, we decrement `len` by 1. This will cause a lot of warnings if we do not specify that both `i` and `(len-1)` are in the valid range of zero to `a.length`. So we need to include this as an assumption anytime we have a loop and need to ensure that we are not going out of bounds. Note that there are better ways of handling loops which we will see in the "[Specifying Loops](https://www.openjml.org/tutorial/Loops)" tutorial, but for now we will handle loops using the `assume` clause. After the for-loop we can also assert that the length of `b` is the same as the length of `a`. We can then write the following:
```java
//@ requires a != null;
//@ ensures \result.length == a.length;
public int[] reverseArray(int[] a) {
	int len = a.length;
	int[] b = new int[len];

  for (int i = 0; i < a.length; i++) {
		//@ assume 0 <= i < a.length;
		//@ assume 0 <= len-1 < a.length;
		b[len - 1] = a[i];
		len--;			
	}
	//@ assert b.length == a.length;
	return b;
}
```
**Learning Objective:**
The goal of this exercise is to see if the student understands one way that the assume clause can be used at this point in the students' studies. The tutorial on assume statements goes over this use of assumes well, so it should be easy for the student to determine where the assumption clause should be put to ensure that there are no warnings. This also gives the student a taste of what is to come by using loop invariants which will come later. The questions also requires that the student recall past tutorials. 

## **Question 2**
**Given the function below, what assertions can be concluded?**

**Asnwer and Explanation:**

**Learning Objective:** 

## **Resources:**
+ [Assert Statements Exercises](AssertEx.md)
+ [Question 1 Java](AssertExample1.java)
+ [Question 2 Java](AssertExample2.java)

