/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package avoid1324

import mod.ModularLongArithmetic

/**
 * A pattern of the form LHS,(X),RHS where X is some expression in brackets can be expressed as Sum_i n_i P_i,X, where P_i is some prefix (no longer than LHS) and n_i are integers. This computes these values.
 * (and caches them)
 */
object SplitCache {
  
  val splitCache = new collection.mutable.HashMap[(Signature,Signature),SignatureSplitResult]

  /**
   * do the work of getting the split
   */
  def enumerateSplit(lhs:Signature,rhs:Signature) : SignatureSplitResult = splitCache.getOrElseUpdate((lhs,rhs),{
    val work = new SplitWork
    work.addNoCache(lhs,rhs,1)
    work.toResult
  })
  
  def testEnumerateSplit(lhs:Signature,rhs:Signature) {
    val res = enumerateSplit(lhs,rhs)
    println(""+lhs+" , (B) , "+rhs+" -> ")
    res.tabulate()
  }
  
  private class SplitWork {
     private val result = new collection.mutable.HashMap[Signature,Long]
     def toResult : SignatureSplitResult = {
       val arrayOfTuples : Array[(Signature,Long)] = result.toArray
       new SignatureSplitResult(arrayOfTuples.map{_._2},arrayOfTuples.map{_._1})
     }
   
     def addPrefix(prefix:Signature,mul:Long) {
       if (prefix==null) throw new IllegalArgumentException
        result.put(prefix,result.get(prefix) match {
          case Some(existing) => ModularLongArithmetic.add(existing,mul)
          case None => mul
        })
     }
     /** Enumerate the given elements (which may contain a trailing bracket) with a mark at the beginning */
     def enumerateMarked(sig:Signature) : Long = if (sig.n==0) 1 else SignatureCounter.count(sig.setStartsWithComma)
     
     def add(lhs:Signature,rhs:Signature,mul:Long) {
       if (SignatureCounter.checkInternalValidity) {
         lhs.checkValid()
         rhs.checkValid()
       }
       val subsplit = enumerateSplit(lhs,rhs)
       //println("add "+lhs+" , "+rhs.mkString(",")+ " *"+mul)
       //subsplit.tabulate()
       for (k<-0 until subsplit.length) addPrefix(subsplit.prefix(k),ModularLongArithmetic.mul(mul,subsplit.n(k)))
     }
     def addNoCache(lhs:Signature,rhs:Signature,mul:Long) {
       if (SignatureCounter.checkInternalValidity) {
         lhs.checkValid()
         rhs.checkValid()
       }
       if (lhs.n==0) addPrefix(Signature.emptyStartsWithComma,ModularLongArithmetic.mul(mul,enumerateMarked(rhs)))
       else if (lhs.startsWithBracket) {
         val (a,b) = lhs.extractFirstBracket
         add(b,rhs,ModularLongArithmetic.mul(mul,enumerateMarked(a)))
       } else if (rhs.n==0) addPrefix(lhs,mul)
       else {
         val workLHS = new EnumerateOverSignatureHelper(lhs,false) { // do the additions corresponding to removing elements of lhs
           override def process(newSig:Signature) {
             add(newSig,rhs,mul)
           }
         }
         workLHS.go()
         val (lhsLeftOfMark,lhsRightOfMark) = if (lhs.startsWithComma) (Signature.emptyStartsWithComma,lhs) else {
           assert (!lhs.startsWithBracket)
           val nlhsFirst = lhs.getInt(Signature.bitForStartBody)
           val pos = Signature.bitsUsedForInt(nlhsFirst)+2
           val left = Signature.start(nlhsFirst)
           val rightP = lhs.shiftLeft(pos).setN(lhs.n-nlhsFirst).setStartsWithComma
           val right = if (lhs.hasPriorStartBracket(Signature.bitForStartBody+pos)) rightP.setStartsWithBracket else rightP
           (left,right)
         } 
         val workRHS = new EnumerateOverSignatureHelper(rhs,true) { // do the additions corresponding to removing elements of rhs
           override def process(newSig:Signature) { }
           override def processElement(span:Int,startAddress:Int,endb:Boolean,startb:Boolean) {
             val beforeElem = rhs.subset(startAddress).setN(rhs.n-left-span)
             if (SignatureCounter.checkInternalValidity) beforeElem.checkValid()
             val afterElem = {
               val t = rhs.shiftLeft(address+2-Signature.bitForStartBody).setN(left).setStartsWithComma
               if (startb) t.setStartsWithBracket else t
             }
             for (j<-0 until span) {
                 val before = j
                 val after = span-j-1;
                 val newRrhs = if (after==0) afterElem else Signature.start(after).setStartsWithComma.append(afterElem)
                 val newLrhs = if (before==0) beforeElem.possiblyRemoveTrailingBracket else beforeElem.append(Signature.start(before).setStartsWithComma)
                 if (lhs.startsWithComma) add(lhs,newLrhs,ModularLongArithmetic.mul(mul,enumerateMarked(newRrhs)))
                 else if (newRrhs.isEmpty) add(lhs,newLrhs,mul)
                 else if (newLrhs.isEmpty&&lhsRightOfMark.isEmpty) add(lhs,newRrhs,mul)
                 else {
                   val subsplit = enumerateSplit(lhsLeftOfMark,newRrhs)
                   for (k<-0 until subsplit.length) {
                     val newprefix = subsplit.prefix(k)
                     add(newprefix.append(lhsRightOfMark),newLrhs,ModularLongArithmetic.mul(mul,subsplit.n(k)))
                   }
                 }
               }
           }
         }
         workRHS.go()
       }
     }
   }

}


/**
 * Result = sum_i n(i) * prefix(i)X
 */
class SignatureSplitResult(val n:Array[Long],val prefix:Array[Signature]) { 
  val length = n.length
  def tabulate() {
    for (i<-0 until length) println("  "+prefix(i)+":  "+n(i))
  }
}

