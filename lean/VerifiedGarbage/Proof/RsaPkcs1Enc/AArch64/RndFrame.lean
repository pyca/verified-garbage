module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the frames

The precondition by name (`RPre`), with `P` bytes of stack for the callee's
callee (the stack is the two frames and the callee's `P + 1088`), the
frames' base `Q s = sp - 1104` (`frameBytes` and the 16 bytes holding
`x30`), and the state in which the inner frame's body starts (`entered`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- The stack, for `P` bytes of the callee's callee's stack. -/
def rndStack (P : Nat) : Nat := P + 2192

/-! ## The regions -/

def outR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def tapeR (s : State) : Region := ⟨s.gpr .x2, 16⟩
def nR (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
def eR (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
def msgR (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
def randR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
def preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩
def stkR (P : Nat) (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 (rndStack P), rndStack P⟩

/-- The contract's precondition, by name. -/
structure RPre (P : Nat) (s : State) : Prop where
  sp1 : rndStack P ≤ s.sp.toNat
  sp2 : s.sp.toNat + 56 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, msgR s, randR s, preR s, argsR s]
  hwr : s.wr = [outR s, tapeR s, scrR s]
  dOt : (outR s).Disjoint (tapeR s)
  dOn : (outR s).Disjoint (nR s)
  dOe : (outR s).Disjoint (eR s)
  dOm : (outR s).Disjoint (msgR s)
  dOr : (outR s).Disjoint (randR s)
  dOs : (outR s).Disjoint (scrR s)
  dOq : (outR s).Disjoint (preR s)
  dOa : (outR s).Disjoint (argsR s)
  dTn : (tapeR s).Disjoint (nR s)
  dTe : (tapeR s).Disjoint (eR s)
  dTm : (tapeR s).Disjoint (msgR s)
  dTr : (tapeR s).Disjoint (randR s)
  dTs : (tapeR s).Disjoint (scrR s)
  dTq : (tapeR s).Disjoint (preR s)
  dTa : (tapeR s).Disjoint (argsR s)
  dNs : (nR s).Disjoint (scrR s)
  dEs : (eR s).Disjoint (scrR s)
  dMs : (msgR s).Disjoint (scrR s)
  dRs : (randR s).Disjoint (scrR s)
  dSq : (scrR s).Disjoint (preR s)
  dSa : (scrR s).Disjoint (argsR s)
  dKo : (stkR P s).Disjoint (outR s)
  dKt : (stkR P s).Disjoint (tapeR s)
  dKn : (stkR P s).Disjoint (nR s)
  dKe : (stkR P s).Disjoint (eR s)
  dKm : (stkR P s).Disjoint (msgR s)
  dKr : (stkR P s).Disjoint (randR s)
  dKs : (stkR P s).Disjoint (scrR s)
  dKq : (stkR P s).Disjoint (preR s)
  dKa : (stkR P s).Disjoint (argsR s)
  wO : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wT : (s.gpr .x2).toNat + 16 ≤ 2 ^ 64
  wN : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  wE : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  wM : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wR : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  wQ : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x4).toNat
  k2 : (s.gpr .x4).toNat ≤ 1024
  hsi : (s.gpr .x1).toNat = (s.gpr .x4).toNat
  L1 : 1 ≤ (s.gpr .x6).toNat
  L2 : (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat
  hml : (stackArg s 0).toNat + 11 ≤ (s.gpr .x4).toNat
  hrl : (stackArg s 2).toNat ≤ Spec.RsaPkcs1Enc.padEntropy ((s.gpr .x4).toNat - (stackArg s 0).toNat - 3)
  hsl : Spec.Rsa.publicScratchWords (s.gpr .x4).toNat ≤ (stackArg s 4).toNat
  hql : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .x4).toNat

theorem stk_eq (P : Nat) (s : State) :
    (⟨s.sp - BitVec.ofNat 64 (P + 2191 + 1), P + 2191 + 1⟩ : Region) = stkR P s := rfl

theorem pre_of {P : Nat} {s : State}
    (h : (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)).pre s) : RPre P s := by
  unfold rndStack at h
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, AArch64.abi,
    AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
    dNs, dEs, dMs, dRs, dSq, dSa, dKo, dKt, dKn, dKe, dKm, dKr, dKs, dKq, dKa,
    wO, wT, wN, wE, wM, wR, wS, wQ, ⟨k1, k2⟩, hsi, L1, L2, hml, hrl, hsl, hql⟩ := h
  rw [stk_eq] at dKo dKt dKn dKe dKm dKr dKs dKq dKa
  exact ⟨sp1, sp2, hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
    dNs, dEs, dMs, dRs, dSq, dSa, dKo, dKt, dKn, dKe, dKm, dKr, dKs, dKq, dKa,
    wO, wT, wN, wE, wM, wR, wS, wQ, k1, k2, hsi, L1, L2, hml, hrl, hsl, hql⟩

/-! ## The values -/

def kOf (s : State) : Nat := (s.gpr .x4).toNat
def psLen (s : State) : Nat := kOf s - (stackArg s 0).toNat - 3
def nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (kOf s)
def eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
def msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
def randB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
def preW (s : State) : List (BitVec 64) := Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

theorem RPre.ps {P : Nat} {s : State} (hp : RPre P s) :
    8 ≤ psLen s ∧ psLen s + (stackArg s 0).toNat + 3 = kOf s ∧ psLen s ≤ 1021 := by
  have := hp.hml; have := hp.k2; unfold psLen kOf; omega

theorem RPre.randLen {P : Nat} {s : State} (hp : RPre P s) : (stackArg s 2).toNat ≤ psLen s + 128 := hp.hrl

/-! ## The frames -/

/-- The frames' base: `sp` in the inner frame. -/
def Q (s : State) : Addr := s.sp - BitVec.ofNat 64 1104

/-- The base of the stack the function uses. -/
def kb (P : Nat) (s : State) : Addr := s.sp - BitVec.ofNat 64 (rndStack P)

theorem stkR_eq (P : Nat) (s : State) : stkR P s = ⟨kb P s, rndStack P⟩ := rfl

/-- `off p d`, `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_toNat {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

theorem Q_kb (P : Nat) (s : State) : Q s = off (kb P s) (P + 1088) := by
  simp only [Q, kb, off, rndStack]
  rw [show P + 2192 = 1104 + (P + 1088) by omega, BitVec.ofNat_add, ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem kb_toNat {P : Nat} {s : State} (hp : RPre P s) :
    (kb P s).toNat + rndStack P = s.sp.toNat := by
  have := hp.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  unfold rndStack at *; omega

theorem Q_toNat {P : Nat} {s : State} (hp : RPre P s) : (Q s).toNat + 1104 = s.sp.toNat ∧
    P + 1088 ≤ (Q s).toNat := by
  have := hp.sp1
  simp only [Q, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  unfold rndStack at *; omega

theorem Q_sp (s : State) : Q s + BitVec.ofNat 64 1104 = s.sp := BitVec.sub_add_cancel _ _

/-- Bytes of the frames are in the stack the function uses. -/
theorem frame_sub {P : Nat} (s : State) {d n : Nat} (h : d + n ≤ 1104) : Region.Sub ⟨off (Q s) d, n⟩ (stkR P s) := by
  rw [Q_kb P, off_off, stkR_eq]
  exact Offset.sub_base _ (by unfold rndStack; omega)

theorem stackArgAddr_Q (s : State) (j : Nat) : stackArgAddr s j = off (Q s) (1104 + 8 * j) := by
  simp only [stackArgAddr, off]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, Q_sp]

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem arg_contains (s : State) {j : Nat} (hj : j < 7) : (argsR s).Contains (stackArgAddr s j) 8 := by
  rw [argsR, stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (s : State) : (entered s).sp = Q s := by
  show s.sp - 16 - BitVec.ofNat 64 1088 = s.sp - BitVec.ofNat 64 1104
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (s : State) : s.sp - 16 = off (Q s) 1088 := by
  simp only [Q, off]
  rw [show (1104 : Nat) = 16 + 1088 from rfl, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rfl

theorem entered_wr (s : State) : (entered s).wr = ⟨Q s, frameBytes⟩ :: ⟨off (Q s) 1088, 16⟩ :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 1088, 1088⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 1088 = Q s from entered_sp s, lr_slot s]
  rfl

theorem entered_mem (s : State) : (entered s).mem = s.mem.writeW (off (Q s) 1088) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot s]
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- A stack argument, in the memory on entry to the frames' body. -/
theorem arg_entered (s : State) {j : Nat} (hj : j < 7) :
    (entered s).mem.readW (off (Q s) (1104 + 8 * j)) 64 = stackArg s j := by
  rw [entered_mem, Mem.readW_writeW_sep (Offset.sep _ (.inr (by omega)) (by omega) (by omega)) (by decide)]
  show _ = s.mem.readW (stackArgAddr s j) 64
  rw [stackArgAddr_Q]

theorem arg_read (s : State) {j : Nat} (hj : j < 7) :
    (entered s).mem.read (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 = stackArg s j := by
  have := arg_entered s hj
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq] at this
  exact this

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
