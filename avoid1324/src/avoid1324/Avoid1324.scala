
package avoid1324


import scala.collection.mutable.HashMap
import scala.collection.immutable.VectorBuilder

abstract class SigElem {
  def n : Int
}
case class HoldInt(num:Int) extends SigElem {
  override def toString = num.toString
  override def n = num
}
case class Bracketed(elems:Vector[SigElem]) extends SigElem {
  override def toString = elems.mkString("(",",",")")
  override val n = elems.map{_.n}.sum
}

case class Sig(elems:Vector[SigElem],markAtStart:Boolean) {
  def firstMark : Int = if (markAtStart) 0 else 1/* {
    for (i<-0 until elems.length) if (elems(i).isInstanceOf[Bracketed]) return i
    elems.length
  }*/
  override def toString=(if (markAtStart) "," else "")+elems.mkString(",")
  def n = elems.map{_.n}.sum
  
}


object Avoid1324 extends App {
  import OldCounter._
  
  for (i<-1 to 2;j<-1 to 2) testEnumerateSplit(Sig(Vector(HoldInt(i)),true),Vector(HoldInt(j)))
  for (i<-1 to 2;j<-1 to 2) testEnumerateSplit(Sig(Vector(HoldInt(i)),false),Vector(HoldInt(j)))
  for (i<-1 to 2;j<-1 to 2) testEnumerateSplit(Sig(Vector(HoldInt(1),HoldInt(i)),false),Vector(HoldInt(j)))
    
  for (i<-1 until 28) {
    val res = enumerate(Sig(Vector(HoldInt(i)),false));
    println(i+"  -> "+res+"   cache "+cache.size+"  time "+time+"  split cache="+splitCache.size+" memory ="+memuse)
    for ((key,_)<-cache) if (Math.random()<0.00001) println(key)
    (new CacheStatistics(cache,sig=>LargestBracketedComponent(sig).notBracketed)).tabulate()
  }
  


}

object OldCounter {


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
  
  val maxUseSplit = 12
  
  val maxenum = 9
  val emptyStartSig = Sig(Vector.empty,true)
  
  
  val cache = new HashMap[Sig,Long]
  val splitCache = new HashMap[(Sig,Vector[SigElem]),SplitResult]

  def merge(startFrom:Int,vs: Vector[SigElem]*) = {
    val b = new VectorBuilder[SigElem]
    var last : SigElem = null;
    var bsize = 0;    
    def add(s:SigElem) {
      if (bsize>startFrom && last.isInstanceOf[HoldInt] && s.isInstanceOf[HoldInt]) {
        last=HoldInt(last.asInstanceOf[HoldInt].n+s.asInstanceOf[HoldInt].n)
      } else {
        bsize+=1;
        if (last!=null) b+=last;
        last=s
      }
    }
    for (v<-vs) for (e<-v) add(e)
    if (last!=null) b+=last;
    b.result
  }

  def enumeratePossiblyFactorize(sig:Sig) : Long = {
    sig.elems.head match {
      case Bracketed(elems) => enumeratePossiblyFactorize(Sig(elems,true))*enumeratePossiblyFactorize(Sig(sig.elems.tail,true))
      case _ => enumerate(sig:Sig)
    }
  }

  def enumerateWithSplit(sig:Sig) : Long = {
        val splitinfo = LargestBracketedComponent(sig)
        if (splitinfo.notBracketed<maxUseSplit && splitinfo.bracketedLen>0) {
          val splitlhs = Sig(sig.elems.slice(0,splitinfo.startIndex),sig.markAtStart)
          val splitrhs = sig.elems.slice(splitinfo.endIndex,sig.elems.length)
          val split = enumerateSplit(splitlhs,splitrhs)
          val middleWithBracket = sig.elems.slice(splitinfo.startIndex,splitinfo.endIndex)
          val middleWithoutBracket = merge(0,middleWithBracket.init,middleWithBracket.last.asInstanceOf[Bracketed].elems)
          var res = 0L
          for (i<-0 until split.length) {
            val prefix = split.prefix(i)
            res+=split.n(i)*enumeratePossiblyFactorize(Sig(merge(if (prefix.markAtStart) 0 else 1,prefix.elems,middleWithoutBracket),prefix.markAtStart))
          }/*
          val oldmethod = enumerate(sig)
          if (oldmethod!=res) {
            println("Error in enumerating "+sig+" old method "+oldmethod+" new method "+res)
            println("Split lhs: "+splitlhs+"   rhs:"+splitrhs.mkString(","))
            split.tabulate()
            throw new IllegalArgumentException
          }*/
          res
        } else enumerateUncached(sig)
  }
  
  def bracketMergingStartBracket(elems:Vector[SigElem]) : Vector[Bracketed] = {  // given { a,b,c } produce { (a,b,c) }. Note that ((a,b),c) is the same as (a,b),(c) and this will do that canonicalization. Do not call with empty arg.
    // println("Merge starting bracket for "+elems.mkString(","))
    elems.head match {
      case e@ Bracketed(_) => e +: bracketMergingStartBracket(elems.tail) // merge opening braces.
      case _ => Vector(Bracketed(elems))
    }
  }
  def bracket(elems1:Vector[SigElem],elems2:Vector[HoldInt]) : Vector[SigElem] = { // put a bracket around the concatenation of elems1 and elems2. Canonicalize by merging brackets at end and start.
    if (elems2.isEmpty) {
      if (elems1.isEmpty || elems1.length==1 && elems1(0).isInstanceOf[Bracketed]) elems1
      else elems1.last match {
        case Bracketed(elems) => bracketMergingStartBracket(merge(0,elems1.init,elems)) // merge closing braces.
        case _ => Vector(Bracketed(elems1))
      }
      // just put a bracket around elems1
    } else if (elems1.isEmpty) Vector(Bracketed(elems2))
    else bracketMergingStartBracket(merge(0,elems1,elems2))
  }
  
  def enumerate(sig:Sig) : Long = {
    cache.getOrElseUpdate(sig,enumerateWithSplit(sig))
  }
  
  def enumerateUncached(sig:Sig) : Long = {  
    var res = 0L;
    for (i<-0 until sig.elems.length) {
      sig.elems(i) match {
        case HoldInt(b) =>
          // val beforeElem = sig.elems.slice(0,i)
          val beforeMark = sig.elems.slice(0,i min sig.firstMark)
          val afterMarkBeforeElem = sig.elems.slice(sig.firstMark,i max sig.firstMark)
          val afterElem = sig.elems.slice(i+1,sig.elems.length)
          for (j<-0 until b) {
            val before = j
            val after = b-j-1;
            val newelem1 = if (before==0) Vector.empty else Vector(HoldInt(before))
            val newelem2 = if (after==0) Vector.empty else Vector(HoldInt(after))
            val bracketed = if (sig.firstMark<=i) { // make a bracket from here back to the first mark.
              bracket(afterMarkBeforeElem,newelem1)
            } else newelem1
            val newMarkStart = sig.markAtStart || (i==0 && j==0)
            val startCommaMerge = if (newMarkStart) 0 else 1
            val newsigelems = merge(startCommaMerge,beforeMark,bracketed,newelem2,afterElem)
            // if ends with bracketed element, remove said brackets.
            if (newsigelems.length==0) res+=1;
            else {
              val notailbracket = newsigelems.last match {
                  case Bracketed(elems) => merge(startCommaMerge,newsigelems.init,elems) 
                  case _ => newsigelems
              }
              val newsig = Sig(notailbracket,newMarkStart)
              res+=enumeratePossiblyFactorize(newsig);          
            }
          }
        case _ =>
      }
      
    }
    // println(" "*(maxenum-sig.n)+sig.toString+" -> "+res);
    res;
  }
  
  
  /**
   * A pattern of the form LHS,(X),RHS where X is some expression in brackets can be expressed as Sum_i n_i P_i,X, where P_i is some prefix (no longer than LHS) and n_i are integers. This computes these values.
   */
  def enumerateSplit(lhs:Sig,rhs:Vector[SigElem]) : SplitResult = splitCache.getOrElseUpdate((lhs,rhs),{
    val work = new SplitWork
    work.addNoCache(lhs,rhs,1)
    work.toResult
  })
  
  def testEnumerateSplit(lhs:Sig,rhs:Vector[SigElem]) {
    val res = enumerateSplit(lhs,rhs)
    println(""+lhs+" , (B) , "+rhs.mkString(",")+" -> ")
    res.tabulate()
  }
  
  class SplitWork {
     private val result = new HashMap[Sig,Long]
     def toResult : SplitResult = {
       val arrayOfTuples : Array[(Sig,Long)] = result.toArray
       new SplitResult(arrayOfTuples.map{_._2},arrayOfTuples.map{_._1})
     }
   
     def addPrefix(prefix:Sig,mul:Long) {
       if (prefix==null) throw new IllegalArgumentException
        result.put(prefix,result.get(prefix) match {
          case Some(existing) => existing+mul
          case None => mul
        })
     }
     def removeTrailingBracket(sig:Vector[SigElem]) : Vector[SigElem] = if (sig.isEmpty) Vector.empty else {
       sig.last match {
          case Bracketed(elems) => merge(0,sig.init,elems) 
          case _ => sig
       }
     }
     /** Enumerate the given elements (which may contain a trailing bracket) with a mark at the beginning */
     def enumerateMarked(elems:Vector[SigElem]) : Long = if (elems.isEmpty) 1 else enumerate(Sig(removeTrailingBracket(elems),true)) 
     def add(lhs:Sig,rhs:Vector[SigElem],mul:Long) {
       val subsplit = enumerateSplit(lhs,rhs)
       //println("add "+lhs+" , "+rhs.mkString(",")+ " *"+mul)
       //subsplit.tabulate()
       for (k<-0 until subsplit.length) addPrefix(subsplit.prefix(k),mul*subsplit.n(k))
     }
     def addNoCache(lhs:Sig,rhs:Vector[SigElem],mul:Long) {
       if (lhs.elems.isEmpty) addPrefix(emptyStartSig,mul*enumerateMarked(rhs))
       else lhs.elems.head match {
         case Bracketed(elems) => add(Sig(lhs.elems.tail,true),rhs,mul*enumerateMarked(elems))
         case _ if rhs.isEmpty => addPrefix(lhs,mul)
         case _ =>
           // do the additions corresponding to removing elements of lhs
           for (i<-0 until lhs.elems.length) lhs.elems(i) match {
             case HoldInt(b) =>
               val startInd = if (lhs.markAtStart) 0 else 1
               val beforeElem = lhs.elems.slice(0,i)
               val beforeMark = if (lhs.markAtStart || beforeElem.isEmpty) Vector.empty else Vector(beforeElem(0))
               val afterMarkBeforeElem = if (lhs.markAtStart || beforeElem.isEmpty) beforeElem else beforeElem.tail
               val afterElem = lhs.elems.slice(i+1,lhs.elems.length)
               for (j<-0 until b) {
                 val before = j
                 val after = b-j-1;
                 val newelem1 = if (before==0) Vector.empty else Vector(HoldInt(before))
                 val newelem2 = if (after==0) Vector.empty else Vector(HoldInt(after))
                 val bracketed= if (lhs.markAtStart || i>0) bracket(afterMarkBeforeElem,newelem1) else newelem1
                 val newlhs = merge(startInd,beforeMark,bracketed,newelem2,afterElem)
                 add(Sig(newlhs,lhs.markAtStart || (i==0 && j==0)),rhs,mul)
               }
             case _ =>
           }
           // do the additions corresponding to removing elements of rhs
           val lhsLeftOfMark : Sig = if (lhs.markAtStart) emptyStartSig else Sig(Vector(lhs.elems.head),false);
           val lhsRightOfMark : Vector[SigElem] = if (lhs.markAtStart) lhs.elems else lhs.elems.slice(1,lhs.elems.length)
           for (i<-0 until rhs.length) rhs(i) match {
             case HoldInt(b) =>
               val beforeElem = rhs.slice(0,i)
               val afterElem = rhs.slice(i+1,rhs.length)
               for (j<-0 until b) {
                 val before = j
                 val after = b-j-1;
                 val newelem1 = if (before==0) Vector.empty else Vector(HoldInt(before))
                 val newelem2 = if (after==0) Vector.empty else Vector(HoldInt(after))
                 val newRrhs = removeTrailingBracket(merge(0,newelem2,afterElem))
                 val newLrhs = removeTrailingBracket(merge(0,beforeElem,newelem1))
                 if (lhs.markAtStart) add(lhs,newLrhs,mul*enumerateMarked(newRrhs))
                 else if (newRrhs.isEmpty) add(lhs,newLrhs,mul)
                 else if (newLrhs.isEmpty&&lhsRightOfMark.isEmpty) add(lhs,newRrhs,mul)
                 else {
                   val subsplit = enumerateSplit(lhsLeftOfMark,newRrhs)
                   for (k<-0 until subsplit.length) {
                     val newprefix = subsplit.prefix(k)
                     add(Sig(newprefix.elems++lhsRightOfMark,newprefix.markAtStart),newLrhs,mul*subsplit.n(k))
                   }
                 }
               }
             case _ =>
           }
       }
     }
   }
}


  



class SplitResult(val n:Array[Long],val prefix:Array[Sig]) { 
  val length = n.length
  def tabulate() {
    for (i<-0 until length) println("  "+prefix(i)+":  "+n(i))
  }
}


class LargestBracketedComponent(val startIndex:Int,val endIndex:Int,val lhsN:Int,val bracketedLen:Int,val rhsN:Int) { 
  def notBracketed : Int = lhsN+rhsN
  override def toString = "indices "+startIndex+","+endIndex+" n="+lhsN+"("+bracketedLen+")"+rhsN
}

object LargestBracketedComponent {
  def apply(sig:Sig) : LargestBracketedComponent = {
    val totalSum = sig.n
    var res : LargestBracketedComponent = new LargestBracketedComponent(-1,-1,totalSum,0,0)
    var run : Option[Int] = None
    var lhsCumSum = 0
    var middleCumSum = 0
    def finish(to:Int) {
        run match {
          case Some(from) =>
            if (res==null || res.bracketedLen<middleCumSum) res = new LargestBracketedComponent(from,to,lhsCumSum,middleCumSum,totalSum-lhsCumSum-middleCumSum)
            run=None
            middleCumSum=0
            lhsCumSum+=middleCumSum
          case None =>
        }      
    }
    for (i<-0 until sig.elems.length) sig.elems(i) match {
      case b @ Bracketed(_) =>
        if (run.isEmpty) {
          run=Some(i)
        }
        middleCumSum+=b.n
      case HoldInt(n) =>
        finish(i)
        lhsCumSum+=n
    }
    finish(sig.elems.length)
    res;
  }
}

class CacheStatistics[Key](cache:HashMap[Sig,Long],f:Sig=>Key) {
  private var store : Map[Key,Int] = Map.empty
  for ((sig,_)<-cache) {
    val key = f(sig)
    store+=key->(store.getOrElse(key,0)+1)
  }
  def values(implicit ord: scala.math.Ordering[Key]): List[(Key,Int)] = store.toList.sortBy{_._1}(ord)
  def tabulate()(implicit ord: scala.math.Ordering[Key]) {
    for ((key,count)<-values) println(key+" -> "+count)
  }
}





