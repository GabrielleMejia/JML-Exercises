---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Assert Statements Exercises:
## **Question 1**
**Given three integers, write a function that finds which is the largest of the three. Determine the specifications needed to verify the function.**

## **Question 2**
**Given the function below, what assertions can be concluded?**
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
## **[Key](AssertExKey.md)**
