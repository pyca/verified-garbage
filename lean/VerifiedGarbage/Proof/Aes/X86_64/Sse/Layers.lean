module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.X86_64.LinearX

/-! # The layers of bitsliced AES in SSE2, by evaluation -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes

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

/-- Pairs as bit numbers. -/
def atoms (T : Nat → Nat → List (Nat × Nat)) (j p : Nat) : List Nat := (T j p).map fun t => 64 * t.1 + t.2

/-- `toBs`: from words `k + 4 c`, half `c` (columns `2 c`, `2 c + 1`) of block `k`. -/
def toBsT (j p : Nat) : List (Nat × Nat) :=
  [(p % 4 + 4 * (byteAt 4 false p / 8), 8 * (byteAt 4 false p % 8) + j)]

/-- `fromBs`: to those words. -/
def fromBsT (w t : Nat) : List (Nat × Nat) := [(t % 8, at_ 4 false (8 * (w / 4) + t / 8) (w % 4))]

theorem toBs_check : check (lanes 64 9) cfg toBs (env q) (post q (atoms toBsT)) = true := by decide +kernel
theorem fromBs_check : check (lanes 64 9) cfg fromBs (env q) (post q (atoms fromBsT)) = true := by decide +kernel
theorem mc0_check : check (lanes 64 9) cfg (mixColumns false) (env p)
    (post q (atoms (mixT mcCoeffs 4 false))) = true := by decide +kernel
theorem mc1_check : check (lanes 64 9) cfg (mixColumns true) (env p)
    (post q (atoms (mixT mcCoeffs 4 true))) = true := by decide +kernel
theorem sr2p_check : check (lanes 64 9) cfg (sr2 p .xmm0 .xmm1) (env p) (post p (atoms (sr2T 4))) = true := by
  decide +kernel
theorem sr2q_check : check (lanes 64 9) cfg (sr2 q .xmm8 .xmm9) (env q) (post q (atoms (sr2T 4))) = true := by
  decide +kernel

def sEnv : Env Nat :=
  { reg := fun x => ((ins q).find? (·.1 == x)).map fun i => sbIn i.2
    slot := fun _ => none }
def sPost (T : List Nat) (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (p j) == some (T.getD j 0)
theorem sbox_check : check (table 64 256) cfg subBytes sEnv (sPost sbox0T) = true := by decide +kernel
theorem invSbox_check : check (table 64 256) cfg invSubBytes sEnv (sPost invSbox0T) = true := by decide +kernel

end VG.Proof.Aes.X86_64.Sse
