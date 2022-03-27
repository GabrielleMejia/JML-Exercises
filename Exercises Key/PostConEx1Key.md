---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Postcondition Exercises Key:
## **Question 1**
**(a) The function given below is unable to be verified; determine where in the specifications it is failing, and fix it.**
```Java
//@ requires num > 0;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}
```
**Answer and Explanation:**
The function below takes in an integer number variable `num`, and will multiply this number by 2 and return it. However, OpenJML fails to verify the program with the current specifications. To figure out why the program is failing lets determine what we do know. 

Since the number being passed in is a whole number, we know that the returned result will always be greater than the original number passed in when the number is greater than 0. In other words we can ensure the result will always be greater than num, required that num is greater than zero. However, we also need to take into account the return type is an `int`; therefore, we need to make sure that the number being passed in * 2 does not exceed the range of the type int. 

We can see here that the program fails to verify because we are not specifying the range of `num`. To fix this problem, we simply need to include how big `num` can be.
```Java
//@ requires num > 0;
//@ requires num < Integer.MAX_VALUE;
//@ requires num*2 < Integer.MAX_VALUE;
//@ ensures \result > num;
public int multiplyByTwo(int num) {
	return num*2;
}
```
			
By including the second requirement that `num < Integer.MAX_VALUE` and `num*2 < Integer.MAX_VALUE`, we can now ensure that the result will always be greater than the original number passed in.

**(b) Suppose that the specifications for num were updated so that it only has to be greater than -1.  Determine why this would cause an error, and how you could fix the remaining specifications to verify the function.**

**Answer and Explanation:**
First it is important to understand how `num > -1` affects the code. Saying that `num > -1` now includes zero as a potential input. If `num = 0`, then result would equal zero (0 * 2 = 0). Therefore, we cannot ensure that the result is greater than `num`, because in this case it is equal to `num`. To fix this, we simply have to edit the postcondition to the following:
```Java
//@ requires num > -1;
//@ requires num < Integer.MAX_VALUE;
//@ requires num*2 < Integer.MAX_VALUE;
//@ ensures \result >= num;
public int multiplyByTwo(int num) {
	return num*2;
}
```

**(c) Suppose the code was updated to the following, and num must be a positive number. Determine the specifications needed to verify the function.**
```Java
 public int multiplyByTwo(int num) {
	return num/2;
}
```
**Answer and Explanation:**
First let's start with what we know. We are told that `num` must be positive, therefore, `num > 0` - since zero is neither positive nor negative. Secondly, the code has been updated to `num / 2` from `num * 2`. If `num * 2` ensured a value greater than num, then what is `num / 2` ensuring? Well, we know that whenever we divide a whole positive number by anything, the value gets smaller and smaller. Therefore, the code above ensures that the result will be less than the number passed in when `num` is greater than 0. So we can write:
```Java
//@ requires num > -1;
//@ requires num < Integer.MAX_VALUE;
//@ requires num*2 < Integer.MAX_VALUE;
//@ ensures \result >= num;
public int multiplyByTwo(int num) {
	return num*2;
}
```

## **Question 2**
**Given a rectangle of width w and height h, write a function that finds the area of the rectangle and returns it. Determine the specifications needed to verify the function. (Assume width and height are whole numbers)**

