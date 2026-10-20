module
public import VerifiedGarbage.Impl.Bignum.Arm.Setup


/-! # Build the three CRT workspaces and their public address links

r0 is the main workspace, r7 is the shared word count and r3 is zero.
The main header holds p, q, product, comparison and padded-modulus pointers
at 224..240. Each factor header links back to the main header at 216.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def linkStride : List Instr :=
  [.ldr .r7 .r0 48, .mov .r1 (.shifted .r7 .lsl 7), .dp .add .r1 .r1 (.imm 512), .mov .r2 (.reg .r0)]
def productStride : List Instr := [.mov .r1 (.shifted .r7 .lsl 4), .dp .add .r1 .r1 (.imm 8)]
def advanceLink (d : Nat) : List Instr := [.dp .add .r2 .r2 (.reg .r1), .str .r2 .r0 d]
def linksTail : Prog isa :=
  .seq (.block (advanceLink 224))
    (.seq (.block (advanceLink 228)) (.seq (.block (advanceLink 232))
      (.seq (.block productStride) (.seq (.block (advanceLink 236)) (.block (advanceLink 240))))))
def links : Prog isa := .seq (.block linkStride) linksTail

def primeArgs (slot : Nat) : List Instr := [.ldr .r7 .r0 48, .ldr .r2 .r0 slot]
def primeEnter : List Instr := [.str .r0 .r2 216, .mov .r0 (.reg .r2), .mov .r3 (.imm 0)]
def enterPrime (slot : Nat) : Prog isa := .seq (.block (primeArgs slot)) (.block primeEnter)
def leavePrime : List Instr := [.ldr .r0 .r0 216]
def setupMain : Prog isa := .seq setup links
def setupPrime (slot : Nat) : Prog isa := .seq (enterPrime slot) setup

def setupAll : Prog isa :=
  .seq setupMain (.seq (setupPrime 224)
    (.seq (.block leavePrime) (.seq (setupPrime 228) (.block leavePrime))))

end VG.Impl.Bignum.Arm.Crt
