/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package avoid1324

import java.util.HashMap
import gnu.trove.map.hash.TLongLongHashMap
import mod.ModularLongArithmetic
import gnu.trove.impl.hash.TLongLongHash

object VeryLongCache {
  val hashLoadFactor = 0.75f
  
  def newHash = new TLongLongHashMap(10,hashLoadFactor)

  private implicit class LongLen(map:TLongLongHashMap) {
    def isize : Int = map.synchronized(map.size)
    def lsize : Long = isize.toLong
  }
  
}

/** TLongLongHashMap doesn't deal with with more than a billion or so entries. Solve this by splitting up into sub-caches */
class VeryLongCache(val numSubCaches:Int) {
  import VeryLongCache._
  private val hashes = Array.fill(numSubCaches)(newHash)
  def subCache(key:Long) : TLongLongHashMap = hashes(((key.hashCode%numSubCaches)+numSubCaches)%numSubCaches)
  def length : Long = hashes.map{_.lsize}.sum
  def max : Int = hashes.map{_.isize}.max
}

/**
 * Count the number of permutations that can come from a given signature
 */

object SignatureCounter {

  val maxenum = 8
  val maxSplitCountLHS = -8
  val maxSplitCountRHS = 30
  
  //val cache = new collection.mutable.HashMap[Signature,Long]
  //val shortcache = new collection.mutable.HashMap[Long,Long]

  val numShortCaches = 1003
  val numLongCaches = 103

  val longFastCache = new collection.mutable.HashMap[Long,VeryLongCache]
  val cache0 = new VeryLongCache(numShortCaches)
  
//  val fastcache = new TLongLongHashMap()
//  val shortCaches = Array.fill(numShortCaches)(newHash)
  
  def totalShortCaches = cache0.length // shortCaches.map{_.lsize}.sum
  def maxShortCaches = cache0.max // shortCaches.map{_.isize}.max

  
  def shortCacheSize : String = totalShortCaches.toString+" (max "+maxShortCaches+")" // Long = fastcache.size
  def longCacheSize : Long = longFastCache.values.map(_.length).sum
  def longCacheComplexity : Int = longFastCache.size
  def longestLongCacheLength : Int = if (longFastCache.isEmpty) 0 else longFastCache.values.map(_.max).max
  
  def count(sig:Signature) : Long = {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    if (sig.startsWithBracket) {
       val (a,b) = sig.extractFirstBracket
       ModularLongArithmetic.mul(count(a),count(b))
    } else if (saveSplitComputations) countCached(sig) else countWithSplit(sig)
  }

  var savePortionCum = 0.0;
  
  def countCached(sig:Signature) : Long = if (dontSaveEvenN && ((sig.n&1)==0)) {if (saveSplitComputations) countWithSplit(sig) else countClassic(sig)} else {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    val longcache = if (sig.bits2==0) cache0 else longFastCache.getOrElseUpdate(sig.bits2, new VeryLongCache(numLongCaches))
    val cache = longcache.subCache(sig.bits1) // if (sig.bits2==0) shortCaches(((sig.bits1.hashCode%numShortCaches)+numShortCaches)%numShortCaches) else longFastCache.getOrElseUpdate(sig.bits2, newHash)
    val res = cache.get(sig.bits1)
      if (res==0) {
        val computed = if (saveSplitComputations) countWithSplit(sig) else countClassic(sig)
        savePortionCum+=savePortion
        if (savePortionCum>=1.0) {
          cache.put(sig.bits1,computed)
          savePortionCum-=1.0;
        }
        computed
    } else res
  }
  
  val checkInternalValidity = false
  val checkSplitLongWay = false
  val dontSaveEvenN = false // reduce memory use by only saving elements with N odd.
  val saveSplitComputations = true;
  val savePortion = 1.0; // 0.3; is a reasonable value.
  
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
        res=ModularLongArithmetic.add(res,ModularLongArithmetic.mul(split.n(i),count(newsig)))
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
     } else if (saveSplitComputations) countClassic(sig) else countCached(sig)
  }
  
  /** Count explicitly. No particular optimizations. Assumes no trailing bracket. */
  def countClassic(sig:Signature) : Long = {
    if (SignatureCounter.checkInternalValidity) sig.checkValid()
    if (sig.n==0) return 1
    //println(" "*(maxenum-sig.n)+sig.toString+" -> "+res);
    //if (res!= OldCounter.enumerate(sig.convertToOldSig)) throw new IllegalArgumentException("Wrong answer for "+sig+" expecting "+OldCounter.enumerate(sig.convertToOldSig)+" got "+res)
    val work = new NormalEnumerateOverSignatureHelper(sig)
    work.go()
    //println(work.stringdesc.toString+" & "+work.res+" \\\\")
    work.res
  }
}

class NormalEnumerateOverSignatureHelper(sig:Signature) extends EnumerateOverSignatureHelper(sig:Signature,true) {
  var res = 0L
  val stringdesc = new StringBuffer; stringdesc.append(sig.toStringSquare); stringdesc.append(" & ")
  override def process(newSig:Signature) {
    if (!stringdesc.toString.endsWith(" & ")) stringdesc.append(" + "); 
    stringdesc.append(newSig.toStringSquare); 
    res=ModularLongArithmetic.add(res,SignatureCounter.count(newSig))
  }
}


/** Do the work enumerating over a signature, with a callback to process with a new signature with each possible value removed */
abstract class EnumerateOverSignatureHelper(sig:Signature,removeTrailingBracket:Boolean) {
  var left = sig.n
    // println("Processing "+sig)
  var address = Signature.bitForStartBody
  var depth = if (sig.startsWithBracket) 1 else 0
  var firstMarkAddress = if (sig.startsWithComma && depth==0) address else -1 // the location of the first mark not already inside a bracket, or -1 if none.
  var priorToLastStartLevel1 = -1
  var lastStartLevel1 = if (depth==1) address else -1
   
  if (SignatureCounter.checkInternalValidity) sig.checkValid()
  def process(signature:Signature)
  
  def processElement(span:Int,startAddress:Int,endb:Boolean,startb:Boolean) {
         for (j<-0 until span) { // choose the jth value in the span
            val before = j
            val after = span-j-1;
            // deal with after. If zero, dealt with. if an integer, insert after the current integer. If the next integer doesn't have intervening brackets, merge in.
            val withAfter : Signature = if (after==0) sig else if (endb||startb||left==0) sig.insertNoBracketsThenInt(after,address) else sig.replaceInt(sig.getInt(address+2)+after,address+2)
            //println("withAfter %s %x %x".format(withAfter.toString,withAfter.bits1,withAfter.bits2))
            // deal with before. 
            val withBefore : Signature = if (firstMarkAddress== -1) { // have not yet had a mark. Simple case - don't have to worry about brackets. This must be the first element.
               // new node consists of "before", then "after". If "before" is 0, it vanishes and startsWithComma becomes true. If after is 0, it vanishes. If after is non-zero, it merges in with following sequences.
              if (before==0) { 
                val bracketMoved = if (withAfter.bit(address+1)) withAfter.setPriorStartBracket(startAddress) else withAfter // Can't have an end bracket just after as depth = 0. Could have a start bracket that was deleted. Prior could not have a start bracket (as left is one)
                bracketMoved.deleteBits(startAddress,address+2).setStartsWithComma 
              }
              else withAfter.replaceInt(before,startAddress)
            } else if (firstMarkAddress==startAddress) { // the bracket just goes around this
              if (before==0) {
                val bracketMoved = if (withAfter.bit(address+1)) withAfter.setPriorStartBracket(startAddress) else withAfter // Can't have an end bracket just after as depth = 0. Could have a start bracket that was deleted. Prior could not have a start bracket (as left is one)
                bracketMoved.deleteBits(startAddress,address+2) // just delete it. 
              } else {
                withAfter.replaceInt(before,startAddress).setPriorStartBracket(startAddress).setPostEndBracket(startAddress) // just put a bracket around this number.
              }
            } else { // have had a mark a while ago. Will create a new bracket back to it.
              if (before==0) {
                val bracketMoved = if (withAfter.bit(address+1)) withAfter.setPriorStartBracket(startAddress) else withAfter // Can't have an end bracket just after as depth = 0. Could have a start bracket that was deleted. Prior could not have a start bracket (as left is one)
                val deleted = bracketMoved.deleteBits(startAddress,address+2)
                val withEnd = if (deleted.hasPriorEndBracket(startAddress)) deleted.clearPriorStartBracket(lastStartLevel1).mergeAdjacentInts(priorToLastStartLevel1,lastStartLevel1) else deleted.setPriorEndBracket(startAddress)
                withEnd.setPriorStartBracket(firstMarkAddress)
                //val bracketMoved = if (withAfter.bit(address+1)) withAfter.setPriorStartBracket(startAddress) else withAfter // Can't have an end bracket just after as depth = 0. Could have a start bracket that was deleted. Prior could not have a start bracket (as left is one)
                //bracketMoved.deleteBits(startAddress,address+2) // just delete it. 
              } else {
                val thisNumAndEndBracket = withAfter.replaceInt(before,startAddress).setPostEndBracket(startAddress)
                thisNumAndEndBracket.setPriorStartBracket(firstMarkAddress) // just put a bracket around this number and the first mark. Can't already be one there as firstMarkAddress would otherwise have depth>0.
              }
            }
            val newSig = withBefore.setN(withBefore.n-1)
            //println("newSig %s %x %x".format(newSig.toString,newSig.bits1,newSig.bits2))
            val trailingBracketRemoved = if (left==0 && removeTrailingBracket) newSig.possiblyRemoveTrailingBracket else newSig
            if (SignatureCounter.checkInternalValidity) {
              try {
                newSig.checkValid()              
                trailingBracketRemoved.checkValid()              
              } catch {
                case e : IllegalArgumentException => println("Working on "+sig+" address="+address+" startAddress="+startAddress+" span= "+span+" j="+j+" withAfter="+withAfter+" withBefore="+withBefore+" newSig="+newSig+" trailingBracketRemoved= "+trailingBracketRemoved); throw e
              }
            }
            process(trailingBracketRemoved)            
         }         
    
  }
  def go() {    
    while (left>0) {
       val span = sig.getInt(address)
       left-=span
       val startAddress=address
       address+=Signature.bitsUsedForInt(span)
       val endb = sig.bit(address)
       val startb = sig.bit(address+1)
       if (depth==0) { // not inside a bracket, so can use a value in it.
         processElement(span:Int,startAddress:Int,endb:Boolean,startb:Boolean)
       }
       address+=2
       if (endb) depth-=1
       if (startb) {
         depth+=1
         if (depth==1) { lastStartLevel1=address; priorToLastStartLevel1=startAddress }
       }
       if (firstMarkAddress== -1 && depth==0) firstMarkAddress=address
    }
  }
}
