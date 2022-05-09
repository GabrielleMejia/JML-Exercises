---
title: JML Tutorial - Exercises - Arithmetic
---
# Arithmetic Exercises:
## **Question 1**
**Given three integers, write a function that finds which is the largest of the three. Determine the specifications needed to verify the function.**

**Learning Objectives:**
+

## **Question 2**
**(a) The function given below is unable to be verified; determine where in the specifications it is failing, and fix it.**
**(b) How could you edit the code to verify the function with the original specification?**
```Java
//@ spec_public
private int playerHealth;
	
//@ requires dmg <= 0;
//@ requires 0 < playerHealth;
public int updatePlayerHealth(int dmg) {
	if(playerHealth > dmg) {
		return (playerHealth - dmg);
	}else {
		return 0;
	}
}
```
**Learning Objectives:**
+ Gain more experience with handling overflow 
+ Understand how to write specifications that reflect the requirements and outputs wanted  

## **[Answer Key](ArithmeticExKey.md)**
