/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package avoid1324

import scala.collection.mutable.StringBuilder
import scala.collection.mutable.ListBuffer
import scala.collection.immutable.VectorBuilder

/**
 * The signature for pattern avoiding permutations. 
 * A signature consists of the following information:
 * A list of integers, with well formed brackets around them like 1(2(3)1)(2)5 with the constraint that there can never be two open or close brackets in a row, and all integers must be separated by brackets, except there may be 
 * at the very start two integers with no brackets between them. All integers must be >0, except for possibly the first integer.
 * 
 * Each integer represents a set of contiguous integers left to go in the enumeration. A bracket around something means that all integers above the bracket must be used before anything in the bracket is used.
 * The number to the left of the lowest integer is the first integer (which may be zero).
 * 
 * Canonicalization rules provide the rules that get rid of multiple consecutive open or close brackets:
 *   A((B)C)D = A(B)(C)D
 *   A(B(C))D = A(B,C)D
 * Integers separated by just a comma can be added except for the first one.
 * Brackets at the end can be removed.
 * 
 * 
 * Signatures are encoded as bitstrings.
 * The first 6 bits represent n, the sum of all the integers in the string. Used for determining where the bitstring finishes.
 * The 7th bit is 1 if there should be a 0 at the start of the string
 * The 8th bit is 1 if there should be a ( starting the string.
 * Then there is repeated cycled:
 *   Integer: 00 means a "1", 01 means a "2", 10bbb means the number bbb+3, and 11bbbbbb means the 6 bit binary number bbbbbb+11
 *   0 means no ), 1 means )
 *   0 means no (, 1 means (
 * This means digits 1 and 2 take up 4 bits per element, 3-9 take 7 bits per element, 10+ take 10 bits.
 * Starting with length 39 permutations, one could conceivably split it into 20 "1"s, taking a total of 80 bits (not counting initial 8 bits). That is one worst case.
 * Alternatively, starting with length 39 one could conceivably split it into 10 "3"s, taking a total of 70 bits (not counting initial 8 bits). That is another potential worst case
 * Alternatively, starting with length 39 one could conceivably split it into 3 "11+"s, taking a total of 30 bits (not counting initial 8 bits). That is another potential worst case (obviously insignificant)
 * 
 * This means that 128 bits is plenty, so it is stored as 2 longs. Often the second element will be empty.
 */
sealed class Signature(val bits1:Long,val bits2:Long) extends OrderableWork {
   /** Get the address'th bit */
   def bit(address:Int) : Boolean = (if (address<64) bits1 & (1L<<address) else bits2 & (1L<<(address-64)))!=0
   
   override def n : Int = bits1.toInt & Signature.nMaskInt
   
   def startsWithComma : Boolean = (bits1 & Signature.startsWithCommaMask) !=0
   def startsWithBracket : Boolean = (bits1 & Signature.startsWithBracketMask) !=0
   
   /** The eight bits starting from the given address */
   def eightBitSlice(address:Int) : Int = {
     if (address<57) (bits1>>address).toInt & 255
     else if (address>=64) (bits2>>(address-64)).toInt & 255
     else ((bits1>>>address).toInt + (bits2.toInt << (64-address)))&255
   } 
   
   /** Get the integer starting at the given address */
   def getInt(address:Int) : Int = {
     val slice = eightBitSlice(address)
     val bit2 = (slice&2)!=0
     if ((slice&1) !=0) {
       if (bit2) (slice>>2)+11 else ((slice>>2)&7)+3 
     } else if (bit2) 2 else 1 
   }
   
   override def hashCode() : Int = bits1.hashCode + 1003*bits2.hashCode
   
   override def equals(other:Any) : Boolean = other match {
     case s:Signature => s.bits1==bits1 && s.bits2==bits2
     case _ => false
   }
   
   def toString(startBracket:Char,endBracket:Char) : String = {
     val res = new StringBuilder
     var left = n
     var address = Signature.bitForStartBody
     if (startsWithBracket) res+=startBracket
     else if (startsWithComma) res+=','
     while (left>0) {
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)
       res++=i.toString
       val endb = bit(address)
       val startb = bit(address+1)
       address+=2
       if (endb) res+=endBracket
       if (startb) res+=startBracket
       if (left>0 && !(endb||startb)) res+=','
     }
     res.toString     
   }
   
   override def toString = toString('(',')')
   def toStringSquare = toString('[',']')
   
  
   def largestBracketedComponent : LargestBracketedComponent = {
     val totalSum = n
     var res : LargestBracketedComponent = new LargestBracketedComponent(-1,-1,totalSum,0,0)
     var runStartAddress : Int = -1; // -1 means none, otherwise the first bracketed index than hasn't had an unbracketed element yet.
     var lhsCumSum = 0 // the total sum of integers to the left of runStartAddress
     var address = Signature.bitForStartBody // what we are about to process
     var left = n // sum of remaining integers
     @inline def finish() {
       if (runStartAddress!= -1) {
         val middleCumSum = totalSum-lhsCumSum-left
         if (res==null || res.bracketedLen<middleCumSum) res = new LargestBracketedComponent(runStartAddress,address,lhsCumSum,middleCumSum,left)
         runStartAddress= -1
       }
     }
     var depth = 0
     if (startsWithBracket) { runStartAddress=address; depth=1;}
     while (left>0) {
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)
       val endb = bit(address)
       val startb = bit(address+1)
       address+=2
       if (endb) depth-=1
       if (startb) { depth+=1; if (runStartAddress== -1) { runStartAddress=address; lhsCumSum=totalSum-left }}
       if (depth==0) { finish(); }
     }
     finish()
     // println("Largest bracketed component of "+this+" is "+res)
     res;
   }

   
   // functions to make a new signature out of the old one
   def setStartsWithBracket : Signature = new Signature(bits1|Signature.startsWithBracketMask,bits2)
   def clearStartsWithBracket : Signature = new Signature(bits1& ~Signature.startsWithBracketMask,bits2)
   def setStartsWithComma : Signature = new Signature(bits1|Signature.startsWithCommaMask,bits2)
   /** Remove the bits between two indices */
   def deleteBits(firstIndexToDelete:Int,lastIndexToDeletePlusOne:Int): Signature = {
     val len = lastIndexToDeletePlusOne-firstIndexToDelete
     if (lastIndexToDeletePlusOne<=64) { // all from bits1
       val mask = (1L<<firstIndexToDelete)-1
       new Signature((bits2<<(64-len))|(bits1 & mask) | ( (bits1 >>> len) & ~ mask) ,bits2>>>len)
     } else if (firstIndexToDelete>=64) { // all from bits2
       val mask = (1L<<(firstIndexToDelete-64))-1       
       new Signature(bits1, (bits2 & mask) | ( (bits2 >>> len) & ~ mask) )
     } else { // straddle the boundary
       val mask = (1L<<firstIndexToDelete)-1
       if (len>=64) new Signature((bits2>>>(len-64))|(bits1 & mask),0L)
       else new Signature(((bits2>>>(lastIndexToDeletePlusOne-64))<<firstIndexToDelete)|(bits1 & mask) ,bits2>>>len)
     }
   }
   
   /** Insert the given bit code of length numBits at the given address, pushing existing stuff out. */
   def insertCode(code:Long,address:Int,numBits:Int) : Signature = {
     if (address>=64) {
       val address2 = address-64;
       val mask = (1L<<address2)-1
       new Signature(bits1,(bits2&mask)|(code<<address2) | ((bits2& ~mask)<<numBits))
     } else if (address+numBits>64) { // straddle the divide
       val mask = (1L<<address)-1
       new Signature((bits1&mask)|(code<<address) ,(bits2<<numBits)|(code>>>(64-address))| ((bits1& ~mask)>>>(64-numBits)))
     } else { // all new bits go in bits1
       val mask = (1L<<address)-1
       new Signature((bits1&mask)|(code<<address) | ((bits1& ~mask)<<numBits) ,(bits2<<numBits)| (bits1>>>(64-numBits)))       
     }
   }
   
   def insertNoBracketsThenInt(intToInsert:Int,address:Int) : Signature = {
     val bitsToInsert = Signature.encodedInt(intToInsert)<<2
     val numBitsToInsert = 2+Signature.bitsUsedForInt(intToInsert)
     insertCode(bitsToInsert,address,numBitsToInsert)
   }
   
   def replaceInt(newInt:Int,startAddress:Int) : Signature = {
     deleteBits(startAddress,startAddress+Signature.bitsUsedForInt(getInt(startAddress))).insertCode(Signature.encodedInt(newInt), startAddress, Signature.bitsUsedForInt(newInt))
   }
      /** Get the address'th bit */
   def setBit(address:Int) : Signature = {
     if (address<64) new Signature(bits1 | (1L<<address),bits2)
     else new Signature(bits1,bits2 | (1L<<(address-64)))
   } 
      /** Clear the address'th bit */
   def clearBit(address:Int) : Signature = {
     if (address<0) throw new IllegalArgumentException("clearBit("+address+")")
     if (address<64) new Signature(bits1 & ~(1L<<address),bits2)
     else new Signature(bits1,bits2 & ~(1L<<(address-64)))
   } 
   
   /** Set there to be a start bracket just before the number starting at the given address */
   def setPriorStartBracket(address:Int) : Signature = if (address==Signature.bitForStartBody) setStartsWithBracket else setBit(address-1)
   /** Clear there to be a start bracket just before the number starting at the given address */
   def clearPriorStartBracket(address:Int) : Signature = if (address==Signature.bitForStartBody) setStartsWithBracket else clearBit(address-1)
   /** Get if there is a start bracket just before the number starting at the given address */
   def hasPriorStartBracket(address:Int) : Boolean = if (address==Signature.bitForStartBody) throw new IllegalArgumentException else bit(address-1)
   /** Set there to be a end bracket just before the number starting at the given address */
   def setPriorEndBracket(address:Int) : Signature = if (address==Signature.bitForStartBody) throw new IllegalArgumentException else setBit(address-2)
   /** Clear there to be a end bracket just before the number starting at the given address */
   def clearPriorEndBracket(address:Int) : Signature = if (address==Signature.bitForStartBody) throw new IllegalArgumentException else clearBit(address-2)
   /** Get if there is a end bracket just before the number starting at the given address */
   def hasPriorEndBracket(address:Int) : Boolean = if (address==Signature.bitForStartBody) throw new IllegalArgumentException else bit(address-2)
   
   /** Set there to be an end bracket just after the number starting at the given address */
   def setPostEndBracket(address:Int) : Signature = setBit(address+Signature.bitsUsedForInt(getInt(address)))

   /** Update the n field with the given value */
   def setN(n:Int) : Signature = new Signature((bits1 & Signature.notNMask)|n,bits2)
   
   /** If ends with a trailing bracket, remove it. */
   def possiblyRemoveTrailingBracket : Signature = {
     var left = n
     var address = Signature.bitForStartBody
     var depth = if (startsWithBracket) 1 else 0
     var addressOfLastOpenBracketAtDepth0 = if (depth==1) Signature.bitForStartsWithBracket else -1
     var addressOfStartOfLastOpenBracketAtDepth0 = -1
     while (left>0) {
       val startAddress=address
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)
       val endb = bit(address)
       val startb = bit(address+1)
       if (endb) depth-=1
       if (startb) depth+=1
       if (left==0 && endb) {
         val res=this.clearBit(address).clearBit(addressOfLastOpenBracketAtDepth0)
         val merged = if (addressOfStartOfLastOpenBracketAtDepth0>0 && (startsWithComma || addressOfStartOfLastOpenBracketAtDepth0>Signature.bitForStartBody)) res.mergeAdjacentInts(addressOfStartOfLastOpenBracketAtDepth0, addressOfLastOpenBracketAtDepth0+1) else res
         if (SignatureCounter.checkInternalValidity) merged.checkValid()
         return merged
       } 
       else if (depth==1 && startb) { addressOfLastOpenBracketAtDepth0=address+1; addressOfStartOfLastOpenBracketAtDepth0=startAddress}
       address+=2
     }
     this
   }
   
   def isEmpty : Boolean = n==0
   def checkValid() {
     var depth = 0
     var left = n
     var address = Signature.bitForStartBody
     var allowComma = !startsWithComma
     if (startsWithBracket) depth+=1
     while (left>0) {
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)
       val endb = bit(address)
       val startb = bit(address+1)
       address+=2
       if (endb) { depth-=1; if (depth<0) throw new IllegalArgumentException("Negative bracket depth in "+this) }
       if (startb) depth+=1
       if (left>0 && !(endb||startb||allowComma)) throw new IllegalArgumentException("Too many commas in "+this)
       allowComma=false
     }
     if (left<0) throw new IllegalArgumentException("Initial n value is too low in "+this)
     if (depth!=0) throw new IllegalArgumentException("Brackets do not match in "+this)
     for (a<-address until 128) if (bit(a)) throw new IllegalArgumentException("extra non-zero bits after end in "+this+" : bit "+a)
     for (a<-Signature.bitForStartsWithBracket+1 until Signature.bitForStartBody) if (bit(a)) throw new IllegalArgumentException("extra non-zero bits before start body in "+this+" : bit "+a)
   }
   
   def convertToOldSig : Sig = {
     val stack = new scala.collection.mutable.Stack[VectorBuilder[SigElem]]
     var current = new VectorBuilder[SigElem]
     var left = n
     var address = Signature.bitForStartBody
     def push() { stack.push(current); current = new VectorBuilder[SigElem]; }
     def pop() { 
       val bracketed = new Bracketed(current.result)
       current=stack.pop
       current+=bracketed
     }
     if (startsWithBracket) push()
     while (left>0) {
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)
       current+=new HoldInt(i)
       val endb = bit(address)
       val startb = bit(address+1)
       address+=2
       if (endb) pop()
       if (startb) push()
     }
     assert (stack.isEmpty)
     new Sig(current.result,startsWithComma)
   }
   
   /** If there is an int before the current address and the current address than can be merged, do so. */
   def mergeAdjacentInts(firstAddress:Int,secondAddress:Int) : Signature = {
     if (hasPriorEndBracket(secondAddress) | hasPriorStartBracket(secondAddress) ) return this; // throw new IllegalArgumentException("Trying to merge integers for "+this+" at "+firstAddress+" and "+secondAddress)
     val i1 = getInt(firstAddress)
     val i2 = getInt(secondAddress)
     deleteBits(secondAddress-2,secondAddress+Signature.bitsUsedForInt(i2)).replaceInt(i1+i2,firstAddress)
   }
   
   /** Clear all bits >= lastIndexExclusive */
   def subset(lastIndexExclusive:Int) : Signature = {
     if (lastIndexExclusive<64) new Signature(bits1& ((1L<<lastIndexExclusive)-1),0)
     else new Signature(bits1,bits2&((1L<<(lastIndexExclusive-64))-1))
   }
   /** Shift whole thing left (bad name - removing bits) count bits (and clear n, startsWithBracket,startsWithComma). */
   def shiftLeft(count:Int) : Signature = {
     if (count==0) new Signature(bits1& ~Signature.headerMask,bits2)
     else if (count<64) {
       new Signature(((bits1>>>count)|(bits2<<(64-count)))& ~Signature.headerMask,bits2>>>count)
     } else new Signature((bits2>>>(count-64))& ~Signature.headerMask,0)
   }
   
   /** Shift whole thing right (bad name - inserting bits) count bits (and clear n, startsWithBracket,startsWithComma). */
   def shiftRight(count:Int) : Signature = {
     val nbits1 = bits1 & ~Signature.headerMask
     if (count==0) new Signature(nbits1,bits2) else
     if (count<64) {
       new Signature(nbits1<<count,(bits2<<count)|(nbits1>>>(64-count)))
     } else new Signature(0,nbits1<<(count-64))
   }
   
   
   /** For a signature of the form (A)B, return ,A and ,B */
   def extractFirstBracket() : (Signature,Signature) = {
     if (!startsWithBracket) throw new IllegalArgumentException
     var depth = 1
     var left = n
     var address = Signature.bitForStartBody
     while (left>0) {
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)
       val endb = bit(address)
       val startb = bit(address+1)
       address+=2
       if (endb) { 
         depth-=1; 
         if (depth==0) {
           val na = n-left
           val nb = left
           val a = subset(address-2).setN(na).setStartsWithComma.clearStartsWithBracket
           val bnobracket = shiftLeft(address-Signature.bitForStartBody).setN(nb).setStartsWithComma
           val b = if (startb) bnobracket.setStartsWithBracket else bnobracket 
           return (a,b)
         }
       }
       if (startb) depth+=1
     }
     throw new IllegalArgumentException("Could not extract first Bracket "+this)     
   }
   
   /** The total number of bits used */
   def length : Int = {

     var left = n
     var address = Signature.bitForStartBody
     while (left>0) {
       val i = getInt(address)
       left-=i
       address+=Signature.bitsUsedForInt(i)+2
     }
     address
   }
   
   
   def append(toGoAfter:Signature) : Signature = {
     var left = n
     if (left==0) toGoAfter else if (toGoAfter.isEmpty) this else {
       var address = Signature.bitForStartBody
       var priorAddress = -1
       while (left>0) {
         priorAddress=address
         val i = getInt(address)
         left-=i
         address+=Signature.bitsUsedForInt(i)+2
       }
       val len = address
       // println("length = "+len)
       val rightn = setN(n+toGoAfter.n)
       val withOpenBracket = if (toGoAfter.startsWithBracket) rightn.setBit(len-1) else rightn
       val afterShifted = toGoAfter.shiftRight(len-Signature.bitForStartBody)
       // println("after shifted "+afterShifted.bits1)
       val unmerged = new Signature(withOpenBracket.bits1|afterShifted.bits1,withOpenBracket.bits2|afterShifted.bits2)
       val res = if (startsWithComma || priorAddress>Signature.bitForStartBody) unmerged.mergeAdjacentInts(priorAddress,len) else unmerged
       if (SignatureCounter.checkInternalValidity) {
         try {
           checkValid()
           toGoAfter.checkValid()
           res.checkValid()
         } catch { case e:Exception => println("Append "+this+" and "+toGoAfter+" producing "+res); throw e}
       }
       res
     }
   }
}

object Signature {
  @inline def bitsUsedForInt(i:Int) : Int = if (i<3) 2 else if (i<11) 5 else 8
  
  def encodedInt(i:Int) : Int = {
    if (i<1) throw new IllegalArgumentException("Trying to encode "+i+"<1")
    else if (i<3) (i-1)<<1
    else if (i<11) ((i-3)<<2)+1
    else ((i-11)<<2)+3
  }
  

  @inline val nBits = 6
  @inline val nMask = (1L<<nBits)-1
  @inline val nMaskInt = (1<<nBits)-1
  @inline val notNMask = ~nMask
  
  def start(n:Int) = new Signature(n+(encodedInt(n).toLong<<bitForStartBody),0)
  val zero = new Signature(0,0)
  
  @inline val bitForStartBody = 8 // bit for first element
  @inline val bitForStartsWithBracket = 7
  @inline val bitForStartsWithComma = 6
  @inline val startsWithCommaMask = 1L<<bitForStartsWithComma
  @inline val startsWithBracketMask = 1L<<bitForStartsWithBracket
  @inline val headerMask = (1L<<bitForStartBody)-1
  
  val empty = new Signature(0,0)
  val emptyStartsWithComma = empty.setStartsWithComma

}