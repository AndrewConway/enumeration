package avoid1324

import mod.ModularLongArithmetic

object DoCount extends App {
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
    
  if (args.length>0) ModularLongArithmetic.setPrime(args(0).toInt)
  val maxCount = if (args.length>1) args(1).toInt else 8
  
  println("mod "+ModularLongArithmetic.getPrime)

  
  //ModularLongArithmetic.setPrimeExplicitly(100)
  
  for (i<-1 to maxCount) {
    val res = SignatureCounter.count(Signature.start(i));
    println(i+"  -> "+res+"   long cache "+SignatureCounter.longCacheSize+" short cache "+SignatureCounter.shortCacheSize++"  time "+time+" long caches "+SignatureCounter.longCacheComplexity+" max len "+SignatureCounter.longestLongCacheLength+" split cache="+SplitCache.splitCache.size+" memory ="+memuse)
    //for ((key,_)<-cache) if (Math.random()<0.00001) println(key)
    //(new CacheStatistics(cache,sig=>LargestBracketedComponent(sig).notBracketed)).tabulate()
  }
  
  // Thread.sleep(10000)
}