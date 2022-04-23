---
title: JML Tutorial - Exercises - JML Expressions
---
# JML Expressions Exercises Key:
## **Question 1**
**Take a look at the following function that checks if the number passed is prime. We've seen this code before, but now that you've read about JML Expressions, what can now be ensured about the function?**
```Java
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			flag = false; 
			//@ assert num % i == 0;
			//@ assert flag == false;
			return flag;
		}
	}
		
	flag = true;
	//@ assert flag == true;
	return flag;
}
```
**Asnwer and Explanation:**


**Learning Objective:** 

## **Question 2**
**Write a function that simulates the truth table for the Discrete Mathematical inference rule of Modus Ponens, use the function header given below to construct your function. Determine the specifications needed to verify your function.**
```Java
public boolean modusPonens(boolean p, boolean q);
```
**Asnwer and Explanation:**

**Learning Objective:** 

## **Resources:**
+ [JML Expressions Exercises](JmlExprEx.md)
+ [Question 1 Java](JMLExprExample1.java)
+ [Question 2 Java](JMLExprExample2.java)
