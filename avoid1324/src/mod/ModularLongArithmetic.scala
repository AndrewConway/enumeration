/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package mod

/**
 * In combinatorics, it is useful to compute everything mod a prime. Then the same thing can be done mod a different prime.
 * 
 * This lets one do modular arithmetic mod primes slightly less than 2^64
 */
object ModularLongArithmetic {

  private val primes = Array(57, 87, 117, 143, 153, 167, 171, 195, 203, 273).map{k=>(1L<<62)-k} // primes slightly smaller than 2^62. See http://primes.utm.edu/lists/2small/0bit.html
  
  private var prime = primes(0)
  
  /** Call this at the start of the program to set the modulo operation. If there are multiple threads, they should all go through a synchronized block after this before using anything */
  def setPrime(index:Int) { synchronized { prime=primes(index) } }

  /** Call this at the start of the program to set the modulo operation. If there are multiple threads, they should all go through a synchronized block after this before using anything */
  def setPrimeExplicitly(newprime:Long) { synchronized { prime=newprime } }

  private val checkAllModular = false
  
  def getPrime : Long = prime

  def check(n:Long) {
    if (n<0) throw new IllegalArgumentException
    if (n>prime) throw new IllegalArgumentException
  }
  
  @inline def add(a:Long,b:Long) : Long = {
    if (checkAllModular) { 
      check(a)
      check(b)
    }
    (a+b)%prime
  }
  
  def mul(a:Long,b:Long) : Long = {
    if (checkAllModular) { 
      check(a)
      check(b)
    }
    var res = 0L
    var aa = a
    var bb = b
    if (b>a) { aa=b; bb=a; } // bb is the smaller of a and b; aa is the other
    // invariant at this point (and after each loop below) : final result = res + aa*bb (mod prime). We will make bb successively smaller until final result = res.
    while (bb>0) {
      if ((bb&1)!=0) { res=(res+aa)%prime}
      bb>>>=1
      aa=(2*aa)%prime
    }
    res
  }
  
  
}