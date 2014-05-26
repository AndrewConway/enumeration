/**
 * Copyright 2013 Andrew Conway. All rights reserved. 
 */

package avoid1324

import org.junit.Assert._
import org.junit.Test

/**
 * Signature checking code is heavy on the check for crossing the 64 bit boundary as there is a lot of scope for 
 * errors there. All primitives that access it are checked. Code that uses the primitives is not checked here as it
 * is checked by checking that the right values are produced, and liberal use of Signature.checkValid throughout the
 * main counting program.
 */
class ZZZ_Signature {

  def invalid(s:Signature) {
    try {
      s.checkValid()
      assertFalse(true) // should throw and exception
    } catch { case _ : IllegalArgumentException => }
  }
  
  @Test
  def testStart() {
    assertEquals("1",Signature.start(1).toString)
    assertEquals("2",Signature.start(2).toString)
    assertEquals("3",Signature.start(3).toString)
    assertEquals("4",Signature.start(4).toString)
    assertEquals("5",Signature.start(5).toString)
    for (i<-1 until 63) {
      val s = Signature.start(i)
      assertEquals(i,s.n)
      assertEquals(i.toString,s.toString)
      assertFalse(s.startsWithBracket)
      assertFalse(s.startsWithComma)
      val sc = s.setStartsWithComma
      assertEquals(","+i,sc.toString)
      assertTrue(sc.startsWithComma)
      assertFalse(sc.startsWithBracket)
      val sb = sc.setStartsWithBracket
      assertEquals("("+i,sb.toString)
      assertTrue(sb.startsWithComma)
      assertTrue(sb.startsWithBracket)
      s.checkValid()
      sc.checkValid()
      invalid(sb)
    } 
    assertEquals("5,1,1",Signature.start(5).setN(7).toString)
  }
  
  @Test
  def testeightBitSlice() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    assertEquals(0xf0,s.eightBitSlice(0))
    assertEquals(0xef,s.eightBitSlice(4))
    assertEquals(0x12,s.eightBitSlice(56))
    assertEquals(0x11,s.eightBitSlice(60))
    assertEquals(0x42,s.eightBitSlice(63))
    assertEquals(0x21,s.eightBitSlice(64))
    assertEquals(0x32,s.eightBitSlice(68))
  }
  
  @Test
  def deleteBits() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val t = new Signature(0x123456789abcdef0L,0x0fedcba98765432fL)
    val s0to4 = new Signature(0x1123456789abcdefL,0x0fedcba98765432L)
    val s4to8 = new Signature(0x1123456789abcde0L,0x0fedcba98765432L)
    val s5to9 = new Signature(0x1123456789abcdf0L,0x0fedcba98765432L)
    val s60to64 = new Signature(0x123456789abcdef0L,0x0fedcba98765432L)
    val s61to65 = new Signature(0x123456789abcdef0L,0x0fedcba98765432L)
    val s62to66 = new Signature(0x123456789abcdef0L,0x0fedcba98765432L)
    val s63to67 = new Signature(0x123456789abcdef0L,0x0fedcba98765432L)
    val s64to68 = new Signature(0x123456789abcdef0L,0x0fedcba98765432L)
    val s65to69 = new Signature(0x123456789abcdef0L,0x0fedcba98765433L)
    val t60to64 = new Signature(0xf23456789abcdef0L,0x0fedcba98765432L)
    val t61to65 = new Signature(0xf23456789abcdef0L,0x0fedcba98765432L)
    val t62to66 = new Signature(0xd23456789abcdef0L,0x0fedcba98765432L)
    val t63to67 = new Signature(0x923456789abcdef0L,0x0fedcba98765432L)
    val t64to68 = new Signature(0x123456789abcdef0L,0x0fedcba98765432L)
    val t65to69 = new Signature(0x123456789abcdef0L,0x0fedcba98765433L)
    assertEquals(s0to4,s.deleteBits(0,4))
    assertEquals(s4to8,s.deleteBits(4,8))
    assertEquals(s5to9,s.deleteBits(5,9))
    assertEquals(s60to64,s.deleteBits(60,64))
    assertEquals(s61to65,s.deleteBits(61,65))
    assertEquals(s62to66,s.deleteBits(62,66))
    assertEquals(s63to67,s.deleteBits(63,67))
    assertEquals(s64to68,s.deleteBits(64,68))
    assertEquals(s65to69,s.deleteBits(65,69))
    assertEquals(t60to64,t.deleteBits(60,64))
    assertEquals(t61to65,t.deleteBits(61,65))
    //val tda = t.deleteBits(63,67)
    //System.out.println("%x".format(tda.bits1))
    //System.out.println("%x".format(tda.bits2))
    assertEquals(t62to66,t.deleteBits(62,66))
    assertEquals(t63to67,t.deleteBits(63,67))
    assertEquals(t64to68,t.deleteBits(64,68))
    assertEquals(t65to69,t.deleteBits(65,69))
  }
  
  @Test
  def insertCode() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val s0 = new Signature(0x23456789abcdef05L,0x0fedcba9876543211L)
    val s4 = new Signature(0x23456789abcdef50L,0x0fedcba9876543211L)
    val s60 = new Signature(0x523456789abcdef0L,0x0fedcba9876543211L)
    val s61 = new Signature(0xb23456789abcdef0L,0x0fedcba9876543210L)
    val s62 = new Signature(0x523456789abcdef0L,0x0fedcba9876543211L)
    val s63 = new Signature(0x923456789abcdef0L,0x0fedcba9876543212L)
    val s64 = new Signature(0x123456789abcdef0L,0x0fedcba9876543215L)
    val s65 = new Signature(0x123456789abcdef0L,0x0fedcba987654320bL)
    assertEquals(s0,s.insertCode(0x5, 0,4))
    assertEquals(s4,s.insertCode(0x5, 4,4))
    assertEquals(s60,s.insertCode(0x5, 60,4))
    assertEquals(s61,s.insertCode(0x5, 61,4))
    assertEquals(s62,s.insertCode(0x5, 62,4))
    assertEquals(s63,s.insertCode(0x5, 63,4))
    assertEquals(s64,s.insertCode(0x5, 64,4))
    assertEquals(s65,s.insertCode(0x5, 65,4))
  }
  
  @Test
  def setClearBit() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val set0 = new Signature(0x123456789abcdef1L,0x0fedcba987654321L)
    val clear0 = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val set4 = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val clear4 = new Signature(0x123456789abcdee0L,0x0fedcba987654321L)
    val set63 = new Signature(0x923456789abcdef0L,0x0fedcba987654321L)
    val clear63 = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val set64 = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val clear64 = new Signature(0x123456789abcdef0L,0x0fedcba987654320L)
    val set65 = new Signature(0x123456789abcdef0L,0x0fedcba987654323L)
    val clear65 = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    assertEquals(set0,s.setBit(0))
    assertEquals(clear0,s.clearBit(0))
    assertEquals(set4,s.setBit(4))
    assertEquals(clear4,s.clearBit(4))
    assertEquals(set63,s.setBit(63))
    assertEquals(clear63,s.clearBit(63))
    assertEquals(set64,s.setBit(64))
    assertEquals(clear64,s.clearBit(64))
    assertEquals(set65,s.setBit(65))
    assertEquals(clear65,s.clearBit(65))
  }
  
  @Test
  def mergeAdjacentInts() {
    
  }
  
  @Test
  def subset() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val s0 = new Signature(0,0)
    val s8 = new Signature(0xf0L,0)
    val s60 = new Signature(0x023456789abcdef0L,0x0)
    val s61 = new Signature(0x123456789abcdef0L,0x0)
    val s64 = new Signature(0x123456789abcdef0L,0x0)
    val s65 = new Signature(0x123456789abcdef0L,0x1)
    val s66 = new Signature(0x123456789abcdef0L,0x1)
    assertEquals(s0,s.subset(0))
    assertEquals(s8,s.subset(8))
    assertEquals(s60,s.subset(60))
    assertEquals(s61,s.subset(61))
    assertEquals(s64,s.subset(64))
    assertEquals(s65,s.subset(65))
    assertEquals(s66,s.subset(66))
  }
  
  @Test
  def shiftLeft() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val s0 = new Signature(s.bits1 & ~Signature.headerMask,s.bits2)
    val s4 = new Signature(0x1123456789abcdefL & (~Signature.headerMask),0xfedcba98765432L)
    assertEquals(s0,s.shiftLeft(0)) // doesn't work for 0 - but should never do.
    assertEquals(s4,s.shiftLeft(4))    
  }
  
  @Test
  def shiftRight() {
    val s = new Signature(0x123456789abcdef0L,0x0fedcba987654321L)
    val s0 = new Signature(s.bits1 & ~Signature.headerMask,s.bits2)
    val s4 = new Signature(0x23456789abcdef00L & (~Signature.headerMask<<4),0xfedcba9876543211L)
    assertEquals(s0,s.shiftRight(0))
    assertEquals(s4,s.shiftRight(4))
  }
  
}
