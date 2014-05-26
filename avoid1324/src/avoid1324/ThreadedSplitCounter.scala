/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package avoid1324

import mod.ModularLongArithmetic
import java.util.concurrent.atomic.AtomicInteger

/**
 * Do the computation of a split
 */
object ThreadedSplitCounter {

  def countSplit(request:SplitRequest) {
    val work = new SplitWork(request)
    work.addNoCache(request.lhs,request.rhs,1)
    work.doneWork()
  }
  
  private class SplitWork(originalRequest:SplitRequest) {
     private val result = new collection.mutable.HashMap[Signature,Long]
     def toResult : SignatureSplitResult = {
       val arrayOfTuples : Array[(Signature,Long)] = synchronized { result.toArray }
       new SignatureSplitResult(arrayOfTuples.map{_._2},arrayOfTuples.map{_._1})
     }
   
     def addPrefix(prefix:Signature,mul:Long) {
       if (prefix==null) throw new IllegalArgumentException
       synchronized {
          result.put(prefix,result.get(prefix) match {
            case Some(existing) => ModularLongArithmetic.add(existing,mul)
            case None => mul
          }) 
       }
     }
     /** Enumerate the given elements (which may contain a trailing bracket) with a mark at the beginning */
     def enumerateMarked(sig:Signature) : Long = if (sig.n==0) 1 else PartialComputations.getCache(sig.setStartsWithComma)

     val togo = new AtomicInteger(1) 
     def addWork(work:UseSplitResult) { togo.incrementAndGet(); PartialComputations.addUses(work) }
     def addWork(work:UseResult) { togo.incrementAndGet(); PartialComputations.addUses(work) }
     def doneWork() { 
       if (togo.decrementAndGet()==0) {
         PartialComputations.finished(originalRequest,toResult,true)
       }
     }

     def add(subsplit:SignatureSplitResult,lhsRightOfMark:Signature,newLrhs:Signature,mul:Long) {
       for (k<-0 until subsplit.length) {
         val newprefix = subsplit.prefix(k)
         add(newprefix.append(lhsRightOfMark),newLrhs,ModularLongArithmetic.mul(mul,subsplit.n(k)))
       }
     }

     def add(subsplit:SignatureSplitResult,mul:Long) {
       //subsplit.tabulate()
       for (k<-0 until subsplit.length) addPrefix(subsplit.prefix(k),ModularLongArithmetic.mul(mul,subsplit.n(k)))
     }
     class UseSplitLaterInAdd(override val signature:SplitRequest,mul:Long) extends UseSplitResult {
        override def gotResult(subsplit:SignatureSplitResult) { add(subsplit,mul); doneWork() }
     }
     class UseSplitLaterInAdd2(override val signature:SplitRequest,subsplit:SignatureSplitResult,lhsRightOfMark:Signature,newLrhs:Signature,mul:Long) extends UseSplitResult {
        override def gotResult(subsplit:SignatureSplitResult) { add(subsplit:SignatureSplitResult,lhsRightOfMark:Signature,newLrhs:Signature,mul:Long); doneWork() }
     }

     def add(lhs:Signature,rhs:Signature,mul:Long) {
       if (SignatureCounter.checkInternalValidity) {
         lhs.checkValid()
         rhs.checkValid()
       }
       val request = new SplitRequest(lhs,rhs)
       val subsplit = PartialComputations.getCache(request)
       if (subsplit!=null) add(subsplit,mul)
       else addWork(new UseSplitLaterInAdd(request,mul))
       //println("add "+lhs+" , "+rhs.mkString(",")+ " *"+mul)
     }
     class UseCountLaterAddPrefix(override val signature:Signature,mul:Long) extends UseResult {
       override def gotResult(result:Long) {addPrefix(Signature.emptyStartsWithComma,ModularLongArithmetic.mul(mul,result)); doneWork()}
     }
     class UseCountLaterAdd(override val signature:Signature,b:Signature,rhs:Signature,mul:Long) extends UseResult {
       override def gotResult(result:Long) {add(b,rhs,ModularLongArithmetic.mul(mul,result)); doneWork()}
     }
     def addNoCache(lhs:Signature,rhs:Signature,mul:Long) {
       if (SignatureCounter.checkInternalValidity) {
         lhs.checkValid()
         rhs.checkValid()
       }
       if (lhs.n==0) {
         val countRHS = enumerateMarked(rhs)
         if (countRHS>0) addPrefix(Signature.emptyStartsWithComma,ModularLongArithmetic.mul(mul,countRHS))
         else addWork(new UseCountLaterAddPrefix(rhs,mul))
       }
       else if (lhs.startsWithBracket) {
         val (a,b) = lhs.extractFirstBracket
         val countA = enumerateMarked(a)
         if (countA>0) add(b,rhs,ModularLongArithmetic.mul(mul,countA))
         else addWork(new UseCountLaterAdd(a,b,rhs,mul))
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
                 if (lhs.startsWithComma) {
                   val countNewRrhs = enumerateMarked(newRrhs)
                   if (countNewRrhs>0) add(lhs,newLrhs,ModularLongArithmetic.mul(mul,countNewRrhs))
                   else addWork(new UseCountLaterAdd(newRrhs,lhs,newLrhs,mul))
                 }
                 else if (newRrhs.isEmpty) add(lhs,newLrhs,mul)
                 else if (newLrhs.isEmpty&&lhsRightOfMark.isEmpty) add(lhs,newRrhs,mul)
                 else {
                   val request = new SplitRequest(lhsLeftOfMark,newRrhs)
                   val subsplit = PartialComputations.getCache(request)
                   if (subsplit!=null) add(subsplit:SignatureSplitResult,lhsRightOfMark:Signature,newLrhs:Signature,mul:Long)
                   else addWork(new UseSplitLaterInAdd2(request,subsplit:SignatureSplitResult,lhsRightOfMark:Signature,newLrhs:Signature,mul))
                 }
               }
           }
         }
         workRHS.go()
       }
     }
   }

}