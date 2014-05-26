/**
 * Copyright 2014 Andrew Conway. All rights reserved
 */
package avoid1324

import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicReference
import gnu.trove.map.hash.TLongLongHashMap
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.immutable.HashMap
import java.util.concurrent.ConcurrentHashMap
import mod.ModularLongArithmetic

/**
 * Use the result of an enumeration somehow
 */
abstract class UseResult {
   def signature : Signature
   def gotResult(result:Long) 
}

abstract class UseSplitResult {
   def signature : SplitRequest
   def gotResult(result:SignatureSplitResult) 
}



// abstract class AccumulateOp extends Function2[Long,Long,Long]

class PartialComputationBuilder(sig:Signature,isProduct:Boolean) {
  private var togo : List[UseResult] = Nil
  private val partialComputation = new PartialComputation(sig,isProduct)
  private var res : Long = if (isProduct) 1 else 0
  def addSimple(derivedSig:Signature) {
    val dres = PartialComputations.getCache(derivedSig)
    if (dres!=0) if (isProduct) res=ModularLongArithmetic.mul(res,dres) else res=ModularLongArithmetic.add(res,dres)
    else togo=(new SimpleAccumulateResult(derivedSig,partialComputation))::togo
  }
  def finished() {
    val len = togo.length
    if (len==0) PartialComputations.finished(sig,res,!isProduct)
    else {
      partialComputation.initialize(res,len)
      for (work<-togo) PartialComputations.register(work)
    }
  }
}



class PartialComputation(val sig:Signature,isProduct:Boolean) {
   
   private val res = new AtomicLong
   private val togoCount = new AtomicInteger

   def initialize(startSum:Long,startTogoCount:Int) { res.set(startSum); togoCount.set(startTogoCount)}
   // private val togoSet = new AtomicReference[Set[UseResult]]
   
   def add(newval:Long) { 
     var done=false;
      while (!done) {
        val current = res.get();
        val next = if (isProduct) ModularLongArithmetic.mul(current,newval) else ModularLongArithmetic.add(current,newval)
        done=res.compareAndSet(current, next)
      }
   }
   /*
   def done(worker:UseResult) {
     var done = false
     var isEmpty = false
     while (!done) {
       val current = togoSet.get()
       val newset = current-worker
       done = togoSet.compareAndSet(current,newset)
       isEmpty = newset.isEmpty
     }
     if (isEmpty) PartialComputations.finished(sig,res.get)
   }*/
   def done(worker:UseResult) {
     val isEmpty = togoCount.decrementAndGet()==0
     if (isEmpty) PartialComputations.finished(sig,res.get,!isProduct)
   }
}

/** Something that can be worked on. Values with lower n are done first. */
trait OrderableWork {
  def n:Int
}

object PartialComputations {
  
  var maxQueue = 0    
  
  val toWorkOn = new java.util.concurrent.PriorityBlockingQueue(1000,new java.util.Comparator[OrderableWork]{override def compare(a:OrderableWork,b:OrderableWork) = {a.n-b.n}})
  
  def getWork() : OrderableWork = {
    toWorkOn.take()
  }
  
  val usesMap = new java.util.concurrent.ConcurrentHashMap[Signature,List[UseResult]]
  val usesSplitMap = new java.util.concurrent.ConcurrentHashMap[SplitRequest,List[UseSplitResult]]
  
  
  
  /** Add the given element to usesMap. Add signature to toWorkOn if it was empty. Threadsafe. */
  def addUses(work:UseResult) {
    //println("AddUses "+work.signature)
    val key = work.signature
    var finished = false
    var wasEmpty = false
    while (!finished) {
      val existing = usesMap.get(key)
      //println("Key "+key+" existing "+existing)
      wasEmpty = existing==null
      finished = if (wasEmpty) {
        val desired = work::Nil
        usesMap.putIfAbsent(key,desired)==null
      } else usesMap.replace(key,existing,work::existing)
    }
    if (wasEmpty) {
     // println("Added "+key+" to toWorkOn")
        toWorkOn.add(key)
        maxQueue=maxQueue max toWorkOn.size
    }
  }
  /** Add the given element to usesSplitMap. Add signature to toWorkOn if it was empty. Threadsafe. */
  def addUses(work:UseSplitResult) {
    //println("AddUses "+work.signature)
    val key = work.signature
    var finished = false
    var wasEmpty = false
    while (!finished) {
      val existing = usesSplitMap.get(key)
      //println("Key "+key+" existing "+existing)
      wasEmpty = existing==null
      finished = if (wasEmpty) {
        val desired = work::Nil
        usesSplitMap.putIfAbsent(key,desired)==null
      } else usesSplitMap.replace(key,existing,work::existing)
    }
    if (wasEmpty) {
     // println("Added "+key+" to toWorkOn")
        toWorkOn.add(key)
        maxQueue=maxQueue max toWorkOn.size
    }
  }
  
  
  def getUses(key:Signature) : List[UseResult] = { usesMap.remove(key)  }
  def getUses(key:SplitRequest) : List[UseSplitResult] = { usesSplitMap.remove(key)  }
  
  def register(work:UseResult) { addUses(work)  }
  def register(work:UseSplitResult) { addUses(work)  }
  
  def finished(signature:Signature,result:Long,storeInCache:Boolean) {  /** thread safe */
    if (storeInCache) putCache(signature,result) 
    val dependencies = getUses(signature)
    //println("Finished "+signature+" uses "+dependencies)
    if (dependencies!=null) for (use<-dependencies) use.gotResult(result)
  }
  
  def finished(signature:SplitRequest,result:SignatureSplitResult,storeInCache:Boolean) {  /** thread safe */
    if (storeInCache) putCache(signature,result) 
    val dependencies = getUses(signature)
    //println("Finished "+signature+" uses "+dependencies)
    if (dependencies!=null) for (use<-dependencies) use.gotResult(result)
  }
  
  
  val longCaches2 = new collection.mutable.HashMap[Long,TLongLongHashMap]
  val numSimpleLongCaches = 2048
  val longCaches1 = Array.fill(numSimpleLongCaches)(new TLongLongHashMap)
  val numShortCaches = 1003
  val shortCaches = Array.fill(numShortCaches)(new TLongLongHashMap)
  
  def getLongCache(key:Long) = {
    if (key>=0 && key<numSimpleLongCaches) longCaches1(key.toInt)
    else longCaches2.synchronized { longCaches2.getOrElseUpdate(key,new TLongLongHashMap) }
  }
  
  val splitCache = new java.util.concurrent.ConcurrentHashMap[SplitRequest,SignatureSplitResult]
  def getCache(signature:SplitRequest) : SignatureSplitResult = { splitCache.get(signature) }
  private def putCache(signature:SplitRequest,result:SignatureSplitResult) { splitCache.put(signature,result) }

  // threadsafe
  private def cache(signature:Signature) = if (signature.bits2==0) shortCaches(((signature.bits1.hashCode%numShortCaches)+numShortCaches)%numShortCaches) else getLongCache(signature.bits2) 
  
  private implicit class LongLen(map:TLongLongHashMap) {
    def isize : Int = map.synchronized(map.size)
    def lsize : Long = isize.toLong
  }
  
  def totalShortCaches = shortCaches.map{_.lsize}.sum
  def maxShortCaches = shortCaches.map{_.isize}.max
  def totalLongCaches = longCaches1.map{_.lsize}.sum + longCaches2.synchronized{ longCaches2.values.map{_.lsize}.sum }
  def maxLongCaches = longCaches2.synchronized{ (if (longCaches2.isEmpty) 0 else longCaches2.values.map{_.isize}.max)} max longCaches1.map{_.isize}.max
  
  private def putCache(signature:Signature,result:Long) {
    val c = cache(signature)
    c.synchronized { c.put(signature.bits1,result) }
  }

  def getCache(signature:Signature) : Long = {
    val c = cache(signature)
    c.synchronized { c.get(signature.bits1) }
    // synchronized { getCacheUnsynchronized(signature) }
  }
  
  putCache(Signature.zero,1)
  putCache(Signature.zero.setStartsWithComma,1)
  
  def printResult(n:Int,isFinal:Boolean) {
    synchronized {
      register(new PrintResult(Signature.start(n),isFinal))
    }
  }
  
  val start = System.currentTimeMillis();
  def time = (System.currentTimeMillis()-start).toString+" ms"
  
  def memuse = {
    val r = Runtime.getRuntime();
    r.gc();
    r.gc();
    val mem = r.totalMemory()-r.freeMemory()
    val meg = mem/(1<<20)
    meg.toString+" MB"
  }

  def stats = {
    val s1 = "time "+time+" memory "+memuse
    val s2 = " short cache "+totalShortCaches+" (max "+maxShortCaches+") long cache "+totalLongCaches+" (max "+maxLongCaches+" )"
    val s2a = " split cache "+splitCache.size()
    val s3 = " max queue "+maxQueue
    s1+s2+s2a+s3
  }
  
}

object WorkThread {
  private var workerThreads : List[WorkThread] = Nil
  def addWorker(w:WorkThread) = synchronized {workerThreads=w::workerThreads}
  def interruptWorkers() = synchronized { for (w<-workerThreads) w.interrupt() }  
}

class WorkThread extends Thread {
  WorkThread.addWorker(this)
  override def run() {
    try {
      while (true) {
        PartialComputations.getWork() match {
          case sig:Signature =>
            val res = PartialComputations.getCache(sig)
            if (res==0) ThreadedSignatureCounter.countClassic(sig)
            else PartialComputations.finished(sig, res,false)
            // println(toString+" processed "+sig)
          case request:SplitRequest =>
            val res = PartialComputations.getCache(request)
            if (res==null) ThreadedSplitCounter.countSplit(request)
            else PartialComputations.finished(request, res,false)
            // println(toString+" processed "+sig)
        }
      }
    } catch { case _ : InterruptedException => }
  }
}

class SimpleAccumulateResult(override val signature:Signature,accumulator:PartialComputation) extends UseResult {
  override def gotResult(result:Long) {
    accumulator.add(result)
    accumulator.done(this)
  }
}


class PrintResult(override val signature:Signature,isFinal:Boolean)  extends UseResult {
  override def gotResult(result:Long) {
    println(signature.toString+" -> "+result+"  "+PartialComputations.stats)
    if (isFinal) WorkThread.interruptWorkers()
  }
}