module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse
public import VerifiedGarbage.Proof.Aes.Slices
public import VerifiedGarbage.Proof.Framework.X86_64.LinearX
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Aes.InvSboxSpec

/-! # The layers of bitsliced AES in SSE2, by evaluation -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes.Slices

/-- The slots of the scratch buffer the layers use. -/
def cfg : Cfg := { base := .r9, slots := 92 }

def ins (r : Nat → XReg) : List (XReg × Nat) := (List.range 8).map fun j => (r j, j)

def outs (r : Nat → XReg) (g : Nat → Nat → List Nat) : List (XReg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (r j, g j)

/-- The masks, in their slots. -/
def maskVals : List (Nat × BitVec 64) :=
  ((List.range 6).map fun i => (maskSlot i, idxMask i)) ++ [(sr2Slot, sr2Mask)]

/-- Input words in registers, and the masks in their slots. -/
def env (r : Nat → XReg) : Env (Nat × Nat) :=
  { reg := fun x => ((ins r).find? (·.1 == x)).map fun i => inWord i.2
    slot := fun k => (maskVals.find? (·.1 == k)).map fun m => (m.2.toNat, 0) }

def keepsMasks (e : Env (Nat × Nat)) : Bool :=
  maskVals.all fun m => e.slot m.1 == some (m.2.toNat, 0)

def post (r : Nat → XReg) (g : Nat → Nat → List Nat) (e : Env (Nat × Nat)) : Bool :=
  linPost 9 (outs r g) e && keepsMasks e

theorem toBs_check : check (lanes 64 9) cfg toBs (env q) (post q toBsG) = true := by decide +kernel
theorem fromBs_check : check (lanes 64 9) cfg fromBs (env q) (post q fromBsG) = true := by decide +kernel
theorem mc0_check : check (lanes 64 9) cfg (mixColumns false) (env p) (post q (mcG false)) = true := by decide +kernel
theorem mc1_check : check (lanes 64 9) cfg (mixColumns true) (env p) (post q (mcG true)) = true := by decide +kernel
theorem sr2_check : check (lanes 64 9) cfg (sr2 p .xmm0 .xmm1) (env p) (post p sr2G) = true := by decide +kernel
theorem sr2q_check : check (lanes 64 9) cfg (sr2 q .xmm8 .xmm9) (env q) (post q sr2G) = true := by decide +kernel

/-- The S-box's 256 inputs. -/
def inT (j : Nat) : Nat := tableOf (fun c => c.testBit j) 256
def sEnv : Env Nat :=
  { reg := fun x => ((ins q).find? (·.1 == x)).map fun i => inT i.2
    slot := fun _ => none }
def sPost (T : List Nat) (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (p j) == some (T.getD j 0)
/-- The constant's bits, as tables. -/
def c63 : List Nat := (List.range 8).map fun j => if (0x63).testBit j then ONES else 0
def sT : List Nat := xorT (sboxT ((List.range 8).map inT)) c63
def iT : List Nat := invSboxT (xorT ((List.range 8).map inT) c63)
theorem sbox_check : check (table 64 256) cfg subBytes sEnv (sPost sT) = true := by decide +kernel
theorem invSbox_check : check (table 64 256) cfg invSubBytes sEnv (sPost iT) = true := by decide +kernel

end VG.Proof.Aes.X86_64.Sse
