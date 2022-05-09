---
title: JML Tutorial - Exercises - Using Method Calls in Specifications 
---
# Using Method Calls in Specifications Exercises Key:
## **Question 1**
**(a) The program given below is unable to be verified; determine where in the specifications it is failing, and explain why it's failing.**
```Java
public class CallingMethodsExample2 {
	
	//@ spec_public
	final private double FAILINGGRADE = 69.4;
	//@ spec_public
	private int totalFailing = 0;
	public boolean flag;
	
	//@ requires grades != null;
	//@ requires (\forall int i; 0 <= i < grades.length; !Double.isNaN(grades[i]));
	//@ assigns totalFailing;
	public void totalFailing(double[] grades) {
		//int count = 0;
		for(int i = 0; i < grades.length; i++) {
			//@ assume 0 <= i < grades.length;
			if(grades[i] <= FAILINGGRADE) {
				//@ assume 0 <= totalFailing+1 < Integer.MAX_VALUE;
				totalFailing++;
			}
		}
	}
	//@ requires grades != null;
	//@ requires grades.length > 0;
	//@ assigns flag;
	public boolean isClassFailing(double[] grades) {
		int classSize = grades.length;

		if((((double)totalFailing) / ((double)classSize)) >= .5){
			flag = true;
			return flag;
		}else {
			flag = false;
			return flag;
		}
	}
	
	public void testClass() {
		double[] classGrades = {71.6, 31.5, 69.5, 69.3, 98.2, 84.3, 102.0};

		totalFailing(classGrades);
		isClassFailing(classGrades);
		//@ assert isClassFailing(classGrades);
	}
}
```
**Asnwer and Explanation:**
Let's break down what the code above is doing. First, we have three global variables `FAILINGGRADE`, `totalFailing`, and `flag`. The function `totalFailing()` increments the variable `totalFailing` by one every time it finds a grade, from the array `grades[]` passed in, that is less than or equal to `FAILINGGRADE`. Then, the function `isClassFailing()` takes in the class grades array and finds the length, then it will return true if over half the class is failing, and false otherwise. The function `testClass()` calls both these functions and then there is an assert statement that asserts the outcome of `isClassFailing()`. However, OpenJML throws an error when the program above is ran.
 
This is because `totalFailing()` is assigning the global variable `totalFailing` and therefore the function is not `pure` and cannot be used for JML specifications. For a function to be called in a specification it must be `pure`.



**(b) Edit the code so that the original specifications verify the program.**

**Asnwer and Explanation:**

**Learning Objective:** 

## **Resources:**
+ [Using Method Calls in Specifications Exercises](CallingMethodsEx.md)
+ [Question 1 part(a) Java](CallingMethodsExample1.java)
+ [Question 1 part(b) Java](CallingMethodsExample2.java)


