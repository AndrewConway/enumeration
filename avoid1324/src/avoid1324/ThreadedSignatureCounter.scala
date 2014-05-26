/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package avoid1324

import java.util.HashMap
import gnu.trove.map.hash.TLongLongHashMap
import mod.ModularLongArithmetic

/**
 * Count the number of permutations that can come from a given signature
 */


object ThreadedSignatureCounter {

  val maxenum = 8
  val maxSplitCountLHS = 8
  val maxSplitCountRHS = 20
  
  /*
  def count(sig:Signature) : Long = {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    if (sig.startsWithBracket) {
       val (a,b) = sig.extractFirstBracket
       count(a) * count(b)
    } else countCached(sig)
  }

  def countCached(sig:Signature) : Long = {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    if (sig.bits2==0) {
      // shortcache.getOrElseUpdate(sig.bits1, countWithSplit(sig))
      val res = fastcache.get(sig.bits1)
      if (res==0) {
        val computed = countWithSplit(sig)
        fastcache.put(sig.bits1,computed)
        computed
      } else res
    } else if (useLongFastMap) {
      val map = longFastCache.getOrElseUpdate(sig.bits2, new TLongLongHashMap)
      val res = map.get(sig.bits1)
      if (res==0) {
        val computed = countWithSplit(sig)
        map.put(sig.bits1,computed)
        computed
      } else res      
    } else cache.getOrElseUpdate(sig,countWithSplit(sig))
  }
  
  val checkInternalValidity = true
  val checkSplitLongWay = false
  val useLongFastMap = true
  
  def countWithSplit(sig:Signature) : Long = {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    val splitinfo = sig.largestBracketedComponent
    if (splitinfo.lhsN < maxSplitCountLHS && splitinfo.rhsN < maxSplitCountRHS && splitinfo.bracketedLen>0) {
      val splitLHS = sig.subset(splitinfo.startIndex-2).setN(splitinfo.lhsN)
      val splitRHS = sig.shiftLeft(splitinfo.endIndex-Signature.bitForStartBody).setN(splitinfo.rhsN).setStartsWithComma
      val splitMiddleWithBracket = sig.subset(splitinfo.endIndex).shiftLeft(splitinfo.startIndex-Signature.bitForStartBody).setN(splitinfo.bracketedLen).setStartsWithComma.setStartsWithBracket
      val splitMiddleWithoutBracket = splitMiddleWithBracket.possiblyRemoveTrailingBracket
      val split = SplitCache.enumerateSplit(splitLHS,splitRHS)
      var res = 0L
      for (i<-0 until split.length) {
        val prefix = split.prefix(i)
        val newsig = prefix.append(splitMiddleWithoutBracket)
        if (checkInternalValidity) {
          try {
              newsig.checkValid()              
          } catch {
              case e : IllegalArgumentException => println("Working on "+sig+" divided into "+splitLHS+" then "+splitMiddleWithBracket+" then "+splitRHS+" need to add prefix "+prefix+" to "+splitMiddleWithoutBracket+" producing "+newsig); throw e
          }
        }
        res+=split.n(i)*count(newsig)
      }
      if (checkSplitLongWay) {
        val oldmethod = countClassic(sig)
        if (oldmethod!=res) {
            println("Error in enumerating "+sig+" old method "+oldmethod+" new method "+res)
            println("Working on "+sig+" divided into "+splitLHS+" then "+splitMiddleWithBracket+" then "+splitRHS)
            split.tabulate()
            for (i<-0 until split.length) {
              val prefix = split.prefix(i)
              val newsig = prefix.append(splitMiddleWithoutBracket)
              println("Prefix "+prefix+" produces "+newsig)
            }
            throw new IllegalArgumentException
        }
      }
      res
     } else countClassic(sig)
  }*/
  
  /** Count explicitly. No particular optimizations. Assumes no trailing bracket. */
  def countClassic(sig:Signature) {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    if (sig.startsWithBracket) {
       val res = new PartialComputationBuilder(sig,true)
       var left = sig
       while (left.startsWithBracket) {
         val (a,b) = left.extractFirstBracket
         if (SignatureCounter.checkInternalValidity) { 
           a.checkValid()
           b.checkValid()
           if (a.n+b.n!=left.n) throw new IllegalArgumentException
           if (a.n==0) throw new IllegalArgumentException
           if (b.n==0) throw new IllegalArgumentException
         }
         res.addSimple(a)
         left=b
       }
       res.addSimple(left)
       res.finished()
    } else {
       val splitinfo = sig.largestBracketedComponent
       if (splitinfo.lhsN < SignatureCounter.maxSplitCountLHS && splitinfo.rhsN < SignatureCounter.maxSplitCountRHS && splitinfo.bracketedLen>0) {
         val enumerator = new EnumerateViaSplit(sig,splitinfo)
         val request = new SplitRequest(enumerator.splitLHS,enumerator.splitRHS)
         val split = PartialComputations.getCache(request)
         if (split!=null) enumerator.doSplit(split)
         else PartialComputations.register(new DoSplitLater(request,enumerator))
       } else { // do it the hard way
          //println(" "*(maxenum-sig.n)+sig.toString+" -> "+res);
          //if (res!= OldCounter.enumerate(sig.convertToOldSig)) throw new IllegalArgumentException("Wrong answer for "+sig+" expecting "+OldCounter.enumerate(sig.convertToOldSig)+" got "+res)
          val work = new NormalThreadedEnumerateOverSignatureHelper(sig)
          work.go()
          work.res.finished()
       }
    }
  }
  
}

case class SplitRequest(lhs:Signature,rhs:Signature) extends OrderableWork {
  override def n:Int = lhs.n max rhs.n
}

class DoSplitLater(override val signature:SplitRequest,enumerator:EnumerateViaSplit) extends UseSplitResult {
  override def gotResult(result:SignatureSplitResult) { enumerator.doSplit(result) }
}
  
class EnumerateViaSplit(sig:Signature,splitinfo:LargestBracketedComponent) {
  val splitLHS = sig.subset(splitinfo.startIndex-2).setN(splitinfo.lhsN)
  val splitRHS = sig.shiftLeft(splitinfo.endIndex-Signature.bitForStartBody).setN(splitinfo.rhsN).setStartsWithComma
  val splitMiddleWithBracket = sig.subset(splitinfo.endIndex).shiftLeft(splitinfo.startIndex-Signature.bitForStartBody).setN(splitinfo.bracketedLen).setStartsWithComma.setStartsWithBracket
  val splitMiddleWithoutBracket = splitMiddleWithBracket.possiblyRemoveTrailingBracket
  
  def doSplit(split:SignatureSplitResult) {
      var res = 0L
      var togo : List[UseResult] = Nil
      var partialComputation : PartialComputation = null
      for (i<-0 until split.length) {
        val prefix = split.prefix(i)
        val newsig = prefix.append(splitMiddleWithoutBracket)
        if (SignatureCounter.checkInternalValidity) {
          try {
              newsig.checkValid()              
          } catch {
              case e : IllegalArgumentException => println("Working on "+sig+" divided into "+splitLHS+" then "+splitMiddleWithBracket+" then "+splitRHS+" need to add prefix "+prefix+" to "+splitMiddleWithoutBracket+" producing "+newsig); throw e
          }
        }
        val c = PartialComputations.getCache(newsig)
        if (c!=0) res=ModularLongArithmetic.add(res,ModularLongArithmetic.mul(split.n(i),c)) 
        else {
          if (partialComputation==null) partialComputation=new PartialComputation(sig,false)
          togo=(new AccumulateSplitElement(split.n(i),newsig,partialComputation))::togo
        }
      }
      val len = togo.length
      if (len==0) PartialComputations.finished(sig,res,true)
      else {
        partialComputation.initialize(res,len)
        for (work<-togo) PartialComputations.register(work)
      }
  }
}

class AccumulateSplitElement(n:Long,override val signature:Signature,accumulator:PartialComputation) extends UseResult {
  def gotResult(result:Long) { 
    accumulator.add(ModularLongArithmetic.mul(n, result))
    accumulator.done(this)
  }
}

class NormalThreadedEnumerateOverSignatureHelper(sig:Signature) extends EnumerateOverSignatureHelper(sig:Signature,true) {
  val res = new PartialComputationBuilder(sig,false)
  override def process(newSig:Signature) {
    res.addSimple(newSig)
  }
}

