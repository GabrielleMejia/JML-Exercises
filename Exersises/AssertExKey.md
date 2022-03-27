---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Precondition Exercises Key:
## **Question 1**
**Given three integers, write a function that finds which is the largest of the three. Determine the specifications needed to verify the function.**

**Asnwer and Explanation:**
To find the largest value of three integers we know we have to compare each integer against the other two. We can write the code below to do this:
```Java
public void max(int a, int b, int c) {
	int max;
	if(a >= b && a >= c) {
		max = a;
	}else if(b >= a && b >= c) {
		max = b;
	}else {
		max = c;
	}
}
```
Note that we say greater than or equal to when comparing since we were not told that each integer would be distinct from the others. Therefore let's determine what assumptions can be made. Remember that `asserts` is used when a condition is expected to "hold at a point within the body of a method." So what can we assert in the function above? We know that since we are checking if the values are greater than or equal to each other, one value will be set to `max` no matter what. Therefore, we can assert the following:
```Java
// @ ensures \result >= a && \result >= b && \result >= c;
// @ ensures \result == a || \result == b || \result == c;
public void max(int a, int b, int c) {
	int max;
	if(a >= b && a >= c) {
		max = a;
	}else if(b >= a && b >= c) {
		max = b;
	}else {
		max = c;
	}
	//@ assert max >= a && max >= b && max >= c;
	//@ assert max == a || max == b || max == c;
}
```
**Learning Objective:**
The goal of this exercise is to see if the student can identify how assert can be used in practice, and how logically it can be written in different ways. In the exercise the student can see that no matter what, the program WILL return whatever it determines to be the max value. But the student can make sure that the program returns a value that makes sense. There are no preconditions for this program, and since the student is not told that the values can't all be the same they can begin to make some assertions after the if statement. We want to see if the student can identify what can be asserted.

## **Question 2**

**Asnwer and Explanation:**

**Learning Objective:**

## **Resources:**
+ [Precondition Exercises](AssertEx.md)
+ [Question 1 Java](AssertExample1.java)
+ [Question 2 Java](AssertExample2.java)
