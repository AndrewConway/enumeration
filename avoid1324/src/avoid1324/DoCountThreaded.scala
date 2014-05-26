package avoid1324

import mod.ModularLongArithmetic

object DoCountThreaded extends App {
  
  if (args.length>0) ModularLongArithmetic.setPrime(args(0).toInt)
  
  val processors = if (args.length>1) args(1).toInt else 8
  val maxCount = if (args.length>2) args(2).toInt else 20
  
  println("mod "+ModularLongArithmetic.getPrime)
  
  for (i<-1 to maxCount) {
    PartialComputations.printResult(i,i==maxCount)
  }
  
  for (i<-1 to processors) (new WorkThread()).start()
  
}