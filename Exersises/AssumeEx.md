---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Assume Statements Exercises:
## **Question 1**
**Write a function that takes in an integer array a and returns an array that is the reversal of a. Determine the specifications needed to verify the function.**

## **Question 2**
**The following code has an error with finding the max value in an array. Given the array a = {3, 12, 7, 0, 5, 9}, the function is printing that the max value is 9. Determine how assume can be used to find where in the code the error occurs.**
```Java
//@ requires a != null;
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
## **[Key](AssumeExKey.md)**

