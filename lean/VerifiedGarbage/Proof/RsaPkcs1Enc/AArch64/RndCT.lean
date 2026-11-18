module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
meta import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `RsaPkcs1Enc.AArch64.RndCTScan`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndContract`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndBody`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndInvoke`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndScan`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndSetup`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndFrame`, which this module and modules that import it used -/

section

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
  have := hp.hml; have := hp.k2; unfold psLen kOf; omega_arith

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
  rw [Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega_using [h]), Nat.mod_eq_of_lt h]

theorem Q_kb (P : Nat) (s : State) : Q s = off (kb P s) (P + 1088) := by
  simp only [Q, kb, off, rndStack]
  rw [show P + 2192 = 1104 + (P + 1088) by omega_using [], BitVec.ofNat_add, ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem kb_toNat {P : Nat} {s : State} (hp : RPre P s) :
    (kb P s).toNat + rndStack P = s.sp.toNat := by
  have := hp.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  unfold rndStack at *; omega_arith

theorem Q_toNat {P : Nat} {s : State} (hp : RPre P s) : (Q s).toNat + 1104 = s.sp.toNat ∧
    P + 1088 ≤ (Q s).toNat := by
  have := hp.sp1
  simp only [Q, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  unfold rndStack at *; omega_arith

theorem Q_sp (s : State) : Q s + BitVec.ofNat 64 1104 = s.sp := BitVec.sub_add_cancel _ _

/-- Bytes of the frames are in the stack the function uses. -/
theorem frame_sub {P : Nat} (s : State) {d n : Nat} (h : d + n ≤ 1104) : Region.Sub ⟨off (Q s) d, n⟩ (stkR P s) := by
  rw [Q_kb P, off_off, stkR_eq]
  exact Offset.sub_base _ (by unfold rndStack; omega_using [h])

theorem stackArgAddr_Q (s : State) (j : Nat) : stackArgAddr s j = off (Q s) (1104 + 8 * j) := by
  simp only [stackArgAddr, off]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, Q_sp]

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem arg_contains (s : State) {j : Nat} (hj : j < 7) : (argsR s).Contains (stackArgAddr s j) 8 := by
  rw [argsR, stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

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
  rw [entered_mem, Mem.readW_writeW_sep (Offset.sep _ (.inr (by omega_using [])) (by omega_using [hj]) (by omega_using [])) (by decide)]
  show _ = s.mem.readW (stackArgAddr s j) 64
  rw [stackArgAddr_Q]

theorem arg_read (s : State) {j : Nat} (hj : j < 7) :
    (entered s).mem.read (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 = stackArg s j := by
  have := arg_entered s hj
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq] at this
  exact this

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the first block

The frames and the scan's registers after `setup` (`Before`, `setup_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- The registers but `rs` are kept. -/
def Keeps (rs : List Reg) (s t : State) : Prop := ∀ r, r ∉ rs → t.gpr r = s.gpr r

theorem Keeps.trans {rs rs' : List Reg} {s t u : State} (h₁ : Keeps rs s t) (h₂ : Keeps rs' t u) :
    Keeps (rs ++ rs') s u := fun r hr => by
  rw [List.mem_append, not_or] at hr
  exact (h₂ r hr.2).trans (h₁ r hr.1)

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : Keeps rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s t := fun r hr => h r fun h' => hr (hs r h')

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := fun _ _ => rfl

/-- In the frames, at a point of the body: what the body keeps. -/
structure InFrame (s t : State) : Prop where
  sp : t.sp = Q s
  rd : t.rd = s.rd
  wr : t.wr = (entered s).wr
  v : t.v = s.v
  fr : Frame [⟨Q s, 1104⟩] s.mem t.mem
  ps : t.mem.readW (off (Q s) oPs) 64 = BitVec.ofNat 64 (psLen s)
  lr : t.mem.readW (off (Q s) 1088) 64 = s.gpr .x30

/-- After `setup`. -/
structure Before (s t : State) : Prop extends InFrame s t where
  x11 : t.gpr .x11 = stackArg s 1
  x12 : t.gpr .x12 = stackArg s 2
  x14 : t.gpr .x14 = off (Q s) oBuf
  x15 : t.gpr .x15 = BitVec.ofNat 64 (psLen s)
  x16 : t.gpr .x16 = BitVec.ofNat 64 (psLen s)
  keep : Keeps [.x9, .x11, .x12, .x14, .x15, .x16] s t

theorem psLen_bv {P : Nat} {s : State} (hp : RPre P s) :
    s.gpr .x4 - stackArg s 0 - BitVec.ofNat 64 3 = BitVec.ofNat 64 (psLen s) := by
  have := hp.hml
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, psLen, kOf]
  omega_using [this]

theorem args_in {P : Nat} {s : State} (hp : RPre P s) {j : Nat} (hj : j < 7) :
    InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 :=
  ⟨argsR s, by rw [entered_rd, hp.hrd]; simp, by show (argsR s).Contains (off (Q s) (1104 + 8 * j)) 8; rw [← stackArgAddr_Q]; exact arg_contains s hj⟩

theorem frame_in {s : State} {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (entered s).wr (Q s + BitVec.ofNat 64 d) n :=
  ⟨⟨Q s, frameBytes⟩, by rw [entered_wr]; simp, Offset.contains_base _ h (by unfold frameBytes at h; omega_using [h])⟩

theorem setup_ok {P : Nat} {s : State} (hp : RPre P s) : WP isa (.block setup) (entered s) (Before s) := by
  have a0 : InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 1104) 8 := args_in hp (j := 0) (by decide)
  have a1 : InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 1112) 8 := args_in hp (j := 1) (by decide)
  have a2 : InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 1120) 8 := args_in hp (j := 2) (by decide)
  have m0 : (entered s).mem.read (Q s + BitVec.ofNat 64 1104) 8 = stackArg s 0 := arg_read s (j := 0) (by decide)
  have m1 : (entered s).mem.read (Q s + BitVec.ofNat 64 1112) 8 = stackArg s 1 := arg_read s (j := 1) (by decide)
  have m2 : (entered s).mem.read (Q s + BitVec.ofNat 64 1120) 8 = stackArg s 2 := arg_read s (j := 2) (by decide)
  have w48 : InRegions (entered s).wr (Q s + BitVec.ofNat 64 48) 8 := frame_in (by decide)
  have hps := psLen_bv hp
  apply WP.of_runBlock
  simp only [setup, arg, frameBytes, oPs, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    State.load, State.store, State.read, Size.bits, BitVec.setWidth_eq, Option.map_some,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, entered_sp,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq,
    ite_false, a0, a1, a2, m0, m1, m2, w48, Option.some.injEq, exists_eq_left']
  have hv : (s.gpr .x4 - stackArg s 0 - 3#64).setWidth 64 = BitVec.ofNat 64 (psLen s) := by
    rw [BitVec.setWidth_eq]; exact hps
  have hQ := Q_toNat hp
  have hlr : (entered s).mem.readW (Q s + BitVec.ofNat 64 1088) 64 = s.gpr .x30 := by
    rw [entered_mem]; exact Mem.readW_writeW_self64 _ _ _
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · show Frame _ s.mem ((entered s).mem.write _ 8 _)
    rw [entered_mem]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base _ (by decide) (by omega_using [])
    · exact Offset.contains_base _ (by decide) (by omega_using [])
  · show ((entered s).mem.write _ 8 _).readW _ 64 = _
    have := Mem.readW_writeW_self (entered s).mem (Q s + BitVec.ofNat 64 48) 8
      ((s.gpr .x4 - stackArg s 0 - 3#64).setWidth 64) (by decide)
    simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at this
    simp only [oPs, off, entered_gpr]
    rw [this, hps]
  · show ((entered s).mem.write _ 8 _).readW _ 64 = _
    rw [Bytes.readW_write_sep (Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide)]
    exact hlr
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, entered_gpr]
    exact hps
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, entered_gpr,
      BitVec.or_self]
    exact hps
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h14, h15, h16⟩ := hr
    simp only [RegUpd.gpr_write, h9, h11, h12, h14, h15, h16, ite_false, entered_gpr]

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the scan

After `i` octets of the tape `randB s`, the scan has kept their nonzero
octets, `kept s i`, at the start of `PS` (`At`); one octet more (`step_ok`);
and the whole scan (`scan_ok`), which ends with `PS` full, the padding string
of `nonzeroPrefix`, or with the tape read.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Enc (nz nz_zero nz_ne nz_length_le)

/-- The kept octets after `i` octets of the tape. -/
abbrev kept (s : State) (i : Nat) : List Byte := nz ((randB s).take i)

theorem randB_getD {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) :
    (randB s).getD i 0 = s.mem (stackArg s 1 + BitVec.ofNat 64 i) := by
  simp [randB, Spec.Rsa.bytesAt, hi]

theorem randB_length (s : State) : (randB s).length = (stackArg s 2).toNat := by
  simp [randB, Spec.Rsa.bytesAt]

theorem take_succ_eq {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) :
    (randB s).take (i + 1) = (randB s).take i ++ [(randB s).getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]

theorem kept_succ {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) :
    kept s (i + 1) = if (randB s).getD i 0 = 0 then kept s i else kept s i ++ [(randB s).getD i 0] := by
  simp only [kept, take_succ_eq hi]
  split
  · rename_i h; rw [h, nz_zero]
  · rename_i h; exact nz_ne h _

theorem kept_zero (s : State) : kept s 0 = [] := by simp [kept, VG.Proof.RsaPkcs1Enc.nz_nil]

theorem getD_append_lt {l : List Byte} {j : Nat} (b : Byte) (h : j < l.length) :
    (l ++ [b]).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_eq (l : List Byte) (b : Byte) : (l ++ [b]).getD l.length 0 = b := by
  simp [List.getD_eq_getElem?_getD]

/-- After `i` octets of the tape, from the state `t₀` after `setup`. -/
structure At (s t₀ : State) (i : Nat) (u : State) : Prop where
  fr : InFrame s u
  keep : Keeps [.x9, .x11, .x12, .x14, .x16, .x17] t₀ u
  buf : ∀ j < (kept s i).length, u.mem (off (Q s) (oBuf + j)) = (kept s i).getD j 0
  x11 : u.gpr .x11 = stackArg s 1 + BitVec.ofNat 64 i
  x12 : u.gpr .x12 = BitVec.ofNat 64 ((stackArg s 2).toNat - i)
  x14 : u.gpr .x14 = off (Q s) (oBuf + (kept s i).length)
  x16 : u.gpr .x16 = BitVec.ofNat 64 (psLen s - (kept s i).length)
  hi : i ≤ (stackArg s 2).toNat
  hc : (kept s i).length ≤ psLen s

theorem zero_byte (b : Byte) : (b.setWidth 64 == 0) = decide (b = 0) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq, Bytes.setWidth64_eq_zero]

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  show eval (.zero .x r) s = _
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- After `load`, from `t`. -/
structure LoadStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  x17 : u.gpr .x17 = (t.mem (t.gpr .x11)).setWidth 64
  x11 : u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1
  x12 : u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x17 → u.gpr r = t.gpr r

theorem load_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block load) t (LoadStep t) := by
  apply WP.of_runBlock
  simp only [load, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.load,
    State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, reduceCtorEq, ite_false, hr,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h11 h12 h17 => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, BitVec.add_zero,
      Bytes.read_one, Bytes.byte64]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h11, h12, h17, ite_false]

/-- After `keep`, from `t`. -/
structure KeepStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr .x14) 1 ((t.gpr .x17).setWidth 8)
  x14 : u.gpr .x14 = t.gpr .x14 + BitVec.ofNat 64 1
  x16 : u.gpr .x16 = t.gpr .x16 - BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x14 → r ≠ .x16 → u.gpr r = t.gpr r

theorem keep_ok {t : State} (hw : InRegions t.wr (t.gpr .x14 + BitVec.ofNat 64 0) 1) :
    WP isa (.block keep) t (KeepStep t) := by
  apply WP.of_runBlock
  simp only [keep, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, reduceCtorEq, ite_false, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h14 h16 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h14, h16, ite_false]

theorem mul_ok (t : State) :
    WP isa (.block [.mul .x .x9 .x12 .x16]) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.v = t.v ∧ u.mem = t.mem ∧ u.gpr .x9 = t.gpr .x12 * t.gpr .x16 ∧ ∀ r, r ≠ .x9 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write,
    RegUpd.v_write, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, fun r h9 => ?_⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h9, ite_false]

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem byte_rt8 (b : Byte) : BitVec.setWidth 8 (b.setWidth 64) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega_using []

theorem mul_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 a * BitVec.ofNat 64 b != 0) = decide (¬ (a = 0 ∨ b = 0)) := by
  have hab : a * b < 2 ^ 64 := by
    calc a * b < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by decide
  have ht : (BitVec.ofNat 64 a * BitVec.ofNat 64 b).toNat = a * b := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_using [ha]),
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt hab]
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_eq, BitVec.toNat_eq, ht, ← Nat.mul_eq_zero]
  rfl

/-- The rand octet `i`, unchanged in `u`. -/
theorem rand_byte' {P : Nat} {s u : State} (hp : RPre P s) (hf : InFrame s u) {i : Nat}
    (hi : i < (stackArg s 2).toNat) : u.mem (stackArg s 1 + BitVec.ofNat 64 i) = (randB s).getD i 0 := by
  rw [randB_getD hi]
  have hd : (randR s).Disjoint ⟨Q s, 1104⟩ := fun x h₁ h₂ =>
    hp.dKr x (frame_sub (P := P) s (d := 0) (n := 1104) (by decide) x (by rw [off, add_zero']; exact h₂)) h₁
  have hw := hp.wR
  have hc : (randR s).Contains (stackArg s 1 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  exact hf.fr _ fun r hr => by rw [List.mem_singleton.mp hr]; exact hd _ hc

theorem keeps_load {u v : State} (hv : LoadStep u v) : Keeps [.x11, .x12, .x17] u v := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hv.other r hr.1 hr.2.1 hr.2.2

theorem keeps_keep {v w : State} (hw : KeepStep v w) : Keeps [.x14, .x16] v w := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hw.other r hr.1 hr.2

/-- The branch on octet `i`, after its load. -/
theorem branch_ok {P : Nat} {s t₀ u v : State} (hp : RPre P s) {i : Nat} (hI : At s t₀ i u)
    (hv : LoadStep u v) (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) :
    WP isa (.ite (.zero .x .x17) (.block []) (.block keep)) v (At s t₀ (i + 1)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hlen := (stackArg s 2).isLt
  have hoB : oBuf = 64 := rfl
  have hoP : oPs = 48 := rfl
  have h17 : v.gpr .x17 = ((randB s).getD i 0).setWidth 64 := by
    rw [hv.x17, hI.x11, rand_byte' hp hI.fr hi]
  have kv := keeps_load hv
  have kuv : Keeps [.x9, .x11, .x12, .x14, .x16, .x17] t₀ v :=
    (hI.keep.trans kv).mono (by simp)
  have hx11 : v.gpr .x11 = stackArg s 1 + BitVec.ofNat 64 (i + 1) := by rw [hv.x11, hI.x11, add_add']
  have hx12 : v.gpr .x12 = BitVec.ofNat 64 ((stackArg s 2).toNat - (i + 1)) := by
    rw [hv.x12, hI.x12, Bytes.counter_step hi hlen]
  have hx14 : v.gpr .x14 = off (Q s) (oBuf + (kept s i).length) :=
    (hv.other _ (by decide) (by decide) (by decide)).trans hI.x14
  have hx16 : v.gpr .x16 = BitVec.ofNat 64 (psLen s - (kept s i).length) :=
    (hv.other _ (by decide) (by decide) (by decide)).trans hI.x16
  have hfv : InFrame s v := ⟨hv.sp.trans hI.fr.sp, hv.rd.trans hI.fr.rd, hv.wr.trans hI.fr.wr,
    hv.v.trans hI.fr.v, by rw [hv.mem]; exact hI.fr.fr, by rw [hv.mem]; exact hI.fr.ps,
    by rw [hv.mem]; exact hI.fr.lr⟩
  by_cases hz : (randB s).getD i 0 = 0
  · have hk : kept s (i + 1) = kept s i := by rw [kept_succ hi, ite_eq_left hz]
    refine WP.ite true (by rw [eval_zero, h17, zero_byte, decide_eq_true hz]) (fun _ => WP.block_nil ?_)
      (fun h => absurd h (by decide))
    refine ⟨hfv, kuv, fun j hj => ?_, hx11, hx12, by rw [hk]; exact hx14, by rw [hk]; exact hx16, by omega_using [hi],
      by rw [hk]; exact hI.hc⟩
    rw [hk] at hj ⊢; rw [hv.mem]; exact hI.buf j hj
  · have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    have hl : (kept s (i + 1)).length = (kept s i).length + 1 := by rw [hk]; simp
    have hw : InRegions v.wr (v.gpr .x14 + BitVec.ofNat 64 0) 1 := by
      rw [add_zero', hx14, hfv.wr]
      exact frame_in (by unfold oBuf frameBytes; omega_using [hc, hP])
    refine WP.ite false (by rw [eval_zero, h17, zero_byte, decide_eq_false hz]) (fun h => absurd h (by decide))
      fun _ => WP.mono (keep_ok hw) fun w hw' => ?_
    have hm : w.mem = v.mem.write (off (Q s) (oBuf + (kept s i).length)) 1 ((randB s).getD i 0) := by
      rw [hw'.mem, hx14, h17, byte_rt8]
    have kw := keeps_keep hw'
    refine ⟨⟨hw'.sp.trans hfv.sp, hw'.rd.trans hfv.rd, hw'.wr.trans hfv.wr, hw'.v.trans hfv.v, ?_, ?_, ?_⟩,
      (kuv.trans kw).mono (by simp), fun j hj => ?_, ?_, ?_, ?_, ?_, by omega_using [hi], by omega_using [hc, hl]⟩
    · rw [hm]
      exact hfv.fr.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold oBuf; omega_using [hc, hP]) (by omega_using [hc, hP, hoB]))
    · rw [hm, Bytes.readW_write_sep (Offset.sep _ (.inl (by unfold oPs oBuf; omega_using [])) (by omega_using [hoP]) (by omega_using [hc, hP, hoB]))
        (by decide)]
      exact hfv.ps
    · rw [hm, Bytes.readW_write_sep (Offset.sep _ (.inr (by unfold oBuf; omega_using [hc, hP])) (by omega_using []) (by omega_using [hc, hP, hoB]))
        (by decide)]
      exact hfv.lr
    · rw [hm, hk]
      rw [hl] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [hc, hP, hoB]) (by omega_using [hj])), getD_append_lt _ hj]
        rw [hv.mem]; exact hI.buf j hj
      · rw [Bytes.write1_self, getD_append_eq]
    · rw [hw'.other _ (by decide) (by decide)]; exact hx11
    · rw [hw'.other _ (by decide) (by decide)]; exact hx12
    · rw [hw'.x14, hx14, hl, off, off, add_add', Nat.add_assoc]
    · rw [hw'.x16, hx16, hl, Bytes.counter_step hc (by omega_using [hP])]

/-- One octet of the scan, with fewer than `psLen` octets kept and octets
left: `At` for `i + 1`, and `x9` zero if `PS` is full or the tape has
ended. -/
theorem step_ok {P : Nat} {s t₀ u : State} (hp : RPre P s) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) :
    WP isa step u fun x => At s t₀ (i + 1) x ∧
      (x.gpr .x9 != 0) = decide (¬ ((kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat)) := by
  have hP := hp.ps
  have hrl := hp.randLen
  have hwR := hp.wR
  have hr : InRegions (u.rd ++ u.wr) (u.gpr .x11 + BitVec.ofNat 64 0) 1 :=
    ⟨randR s, by rw [hI.fr.rd, hp.hrd]; simp, by
      rw [add_zero', hI.x11]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  refine WP.seq (WP.mono (load_ok hr) fun v hv => WP.seq (WP.mono (branch_ok hp hI hv hi hc) fun w hw =>
    WP.mono (mul_ok w) fun x ⟨hrd, hwr, hsp, hvv, hmem, h9, ho⟩ => ?_))
  have k9 : Keeps [.x9] w x := fun r hr => ho r (by simpa using hr)
  refine ⟨⟨⟨hsp.trans hw.fr.sp, hrd.trans hw.fr.rd, hwr.trans hw.fr.wr, hvv.trans hw.fr.v,
    by rw [hmem]; exact hw.fr.fr, by rw [hmem]; exact hw.fr.ps, by rw [hmem]; exact hw.fr.lr⟩,
    (hw.keep.trans k9).mono (by simp), fun j hj => by rw [hmem]; exact hw.buf j hj,
    by rw [ho _ (by decide)]; exact hw.x11, by rw [ho _ (by decide)]; exact hw.x12,
    by rw [ho _ (by decide)]; exact hw.x14, by rw [ho _ (by decide)]; exact hw.x16, hw.hi, hw.hc⟩, ?_⟩
  have := hw.hi
  have := hw.hc
  rw [h9, hw.x12, hw.x16, mul_ne (by omega_using [hP, hrl]) (by omega_using [hP]), decide_eq_decide]
  omega_using [hi, this]

/-- `PS` filled at octet `i`: the padding string of `nonzeroPrefix`. -/
theorem prefix_of_fill {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat)
    (hc : (kept s i).length < psLen s) (hf : (kept s (i + 1)).length = psLen s) :
    Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s (i + 1), i + 1) := by
  have hz : (randB s).getD i 0 ≠ 0 := by
    intro hz; rw [kept_succ hi, ite_eq_left hz] at hf; omega_using [hc, hf]
  have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
  have hl : i < (randB s).length := by rw [randB_length]; exact hi
  have e : randB s = (randB s).take i ++ (randB s).getD i 0 :: (randB s).drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i (randB s)]
    congr 1
    rw [List.drop_eq_getElem_cons hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have hlen : ((randB s).take i).length = i := by rw [List.length_take]; omega_using [hl]
  rw [e, VG.Proof.RsaPkcs1Enc.nonzeroPrefix_last _ hz (by rw [hk] at hf; simpa using hf), hk, hlen]

/-- What the scan leaves: after `i` octets, `PS` full with the padding
string, or the tape read with fewer nonzero octets. -/
def Done (s t₀ : State) (u : State) : Prop :=
  ∃ i, At s t₀ i u ∧ (((kept s i).length = psLen s ∧
      Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) ∨
    (i = (stackArg s 2).toNat ∧ (kept s i).length < psLen s))

/-- The loop's invariant, with the octets left as its measure. -/
def LoopInv (s t₀ : State) (n : Nat) (u : State) : Prop :=
  ∃ i, n = (stackArg s 2).toNat - i ∧ At s t₀ i u ∧ i < (stackArg s 2).toNat ∧ (kept s i).length < psLen s

theorem at_zero {P : Nat} {s t₀ : State} (hp : RPre P s) (hb : Before s t₀) : At s t₀ 0 t₀ := by
  have hP := hp.ps
  refine ⟨hb.toInFrame, Keeps.refl _ _, fun j hj => absurd hj (by simp [kept_zero]), ?_, ?_, ?_, ?_,
    Nat.zero_le _, by rw [kept_zero]; simp⟩
  · rw [hb.x11, add_zero']
  · rw [hb.x12, Nat.sub_zero]; exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  · rw [hb.x14, kept_zero]; rfl
  · rw [hb.x16, kept_zero]; rfl

theorem scan_ok {P : Nat} {s t₀ : State} (hp : RPre P s) (hb : Before s t₀) :
    WP isa scan t₀ (Done s t₀) := by
  have hP := hp.ps
  have h0 := at_zero hp hb
  by_cases hl : stackArg s 2 = 0
  · refine WP.ite false (by rw [Bytes.eval_nonzero, hb.x12, hl]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ?_
    have hl' : (stackArg s 2).toNat = 0 := by rw [hl]; rfl
    exact ⟨0, h0, .inr ⟨hl'.symm, by rw [kept_zero]; simp; omega_using [hP]⟩⟩
  have hl' : 0 < (stackArg s 2).toNat := by
    rcases Nat.eq_zero_or_pos (stackArg s 2).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
    · exact h
  refine WP.ite true (by rw [Bytes.eval_nonzero, hb.x12, bne_iff_ne.mpr hl]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hinit : LoopInv s t₀ ((stackArg s 2).toNat - 0) t₀ := ⟨0, rfl, h0, hl', by rw [kept_zero]; simp; omega_using [hP]⟩
  refine WP.loop (LoopInv s t₀) ?_ _ _ hinit
  rintro n u ⟨i, rfl, hI, hi, hc⟩
  refine WP.mono (step_ok hp hI hi hc) fun u' ⟨hI', hz'⟩ => ?_
  by_cases hstop : (kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat
  · refine .inl ⟨by rw [Bytes.eval_nonzero, hz', decide_eq_false (not_not_intro hstop)], ⟨i + 1, hI', ?_⟩⟩
    by_cases hf : (kept s (i + 1)).length = psLen s
    · exact .inl ⟨hf, prefix_of_fill hi hc hf⟩
    · exact .inr ⟨hstop.resolve_left hf, by have := hI'.hc; omega_using [hf, this]⟩
  · refine .inr ⟨by rw [Bytes.eval_nonzero, hz', decide_eq_true hstop], _, by omega_using [hi], i + 1, rfl, hI', by omega_using [hi, hstop],
      by have := hI'.hc; omega_using [hstop, this]⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the call's arguments

With `PS` full after `i` octets (`Ready`): `tape` is `[i, 0]`, and the
arguments of `vg_rsa_pkcs1_encrypt_precomputed` in registers and at `sp`
(`args_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- `PS` full after `i` octets, its octets `ps`. -/
structure Ready (s u : State) (i : Nat) (pad : List Byte) : Prop extends InFrame s u where
  keep : Keeps [.x9, .x11, .x12, .x14, .x15, .x16, .x17] s u
  x12 : u.gpr .x12 = BitVec.ofNat 64 ((stackArg s 2).toNat - i)
  x15 : u.gpr .x15 = BitVec.ofNat 64 (psLen s)
  len : pad.length = psLen s
  buf : Spec.Rsa.bytesAt u.mem (off (Q s) oBuf) (psLen s) = pad
  used : i ≤ (stackArg s 2).toNat

/-- The callee's stack arguments. -/
def callArg (s : State) : Nat → Addr
  | 0 => off (Q s) oBuf
  | 1 => BitVec.ofNat 64 (psLen s)
  | 2 => stackArg s 3
  | 3 => stackArg s 4
  | 4 => stackArg s 5
  | _ => stackArg s 6

/-- After the call's arguments. -/
structure Args (s w : State) (i : Nat) (pad : List Byte) : Prop where
  sp : w.sp = Q s
  rd : w.rd = s.rd
  wr : w.wr = (entered s).wr
  v : w.v = s.v
  fr : Frame [⟨Q s, 1104⟩, tapeR s] s.mem w.mem
  ps : w.mem.readW (off (Q s) oPs) 64 = BitVec.ofNat 64 (psLen s)
  lr : w.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  args : ∀ j < 6, w.mem.readW (off (Q s) (8 * j)) 64 = callArg s j
  buf : Spec.Rsa.bytesAt w.mem (off (Q s) oBuf) (psLen s) = pad
  len : pad.length = psLen s
  tape0 : w.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i
  tape1 : w.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0
  x0 : w.gpr .x0 = s.gpr .x0
  x1 : w.gpr .x1 = s.gpr .x1
  x2 : w.gpr .x2 = s.gpr .x3
  x3 : w.gpr .x3 = s.gpr .x4
  x4 : w.gpr .x4 = s.gpr .x5
  x5 : w.gpr .x5 = s.gpr .x6
  x6 : w.gpr .x6 = s.gpr .x7
  x7 : w.gpr .x7 = stackArg s 0
  keep : Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s w

/-- A stack argument, in a frame's memory. -/
theorem arg_u {P : Nat} {s u : State} (hp : RPre P s) (hf : InFrame s u) {j : Nat} (hj : j < 7) :
    u.mem.read (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 = stackArg s j := by
  have hQ := Q_toNat hp
  have h := hf.fr.read (r := ⟨Q s + BitVec.ofNat 64 (1104 + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base (Q s) (d := 1104 + 8 * j) (n := 8) (k := 1104) (by omega_using []) (by omega_using [hj])) (by decide)
  rw [h]
  have := arg_read s hj
  rw [entered_mem] at this
  rw [← this, Mem.writeW, Mem.read_write_sep (Offset.sep _ (.inr (by omega_using [])) (by omega_using [hj]) (by omega_using [])) (by decide)]

/-- The memory after the call's arguments. -/
def argMem (s u : State) : Mem :=
  (((((((u.mem.write (u.gpr .x2 + 0#64) 8 (stackArg s 2 - u.gpr .x12)).write (u.gpr .x2 + 8#64) 8
    (BitVec.setWidth 64 (0 : BitVec 16) <<< 0)).write (Q s + 0#64) 8 (Q s + 64#64)).write (Q s + 8#64) 8
    (u.gpr .x15)).write (Q s + 16#64) 8 (stackArg s 3)).write (Q s + 24#64) 8 (stackArg s 4)).write
    (Q s + 32#64) 8 (stackArg s 5)).write (Q s + 40#64) 8 (stackArg s 6)

theorem rd_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.write a 8 v).readW a 64 = v := by
  have := Mem.readW_writeW_self m a 8 v (by decide)
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at this
  exact this

theorem rd_sep {m : Mem} {a b : Addr} (v : BitVec 64) (h : Mem.Sep a 8 b 8) : (m.write b 8 v).readW a 64 = m.readW a 64 :=
  Bytes.readW_write_sep h (by decide)

theorem rd_q (m : Mem) (q : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.write (q + BitVec.ofNat 64 e) 8 v).readW (q + BitVec.ofNat 64 d) 64 = m.readW (q + BitVec.ofNat 64 d) 64 :=
  rd_sep v (Offset.sep q h hd he)

theorem sub_used {n i : Nat} (hn : n < 2 ^ 64) (hi : i ≤ n) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (n - i) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n - i < 2 ^ 64 by omega_using [hn]), Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hn, hi]),
    show 2 ^ 64 - (n - i) + n = i + 2 ^ 64 by omega_using [hn, hi], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hn, hi])]

/-- What the arguments write: the tape and the callee's stack arguments. -/
theorem argMem_frame {P : Nat} {s u : State} (hp : RPre P s) (hx2 : u.gpr .x2 = s.gpr .x2) :
    Frame [tapeR s, ⟨Q s, 48⟩] u.mem (argMem s u) := by
  have hQ := Q_toNat hp
  have hc : ∀ {d : Nat}, d + 8 ≤ 48 → (⟨Q s, 48⟩ : Region).Contains (Q s + BitVec.ofNat 64 d) 8 :=
    fun hd => Offset.contains_base _ hd (by omega_using [hd])
  have ht : ∀ {d : Nat}, d + 8 ≤ 16 → (tapeR s).Contains (u.gpr .x2 + BitVec.ofNat 64 d) 8 :=
    fun hd => by rw [hx2]; exact Offset.contains_base _ hd (by omega_using [hd])
  have q : (⟨Q s, 48⟩ : Region) ∈ [tapeR s, ⟨Q s, 48⟩] := by simp
  have t : tapeR s ∈ [tapeR s, ⟨Q s, 48⟩] := by simp
  exact ((((((((Frame.refl _ _).write t _ (ht (d := 0) (by decide))).write t _ (ht (d := 8) (by decide))).write q _
    (hc (d := 0) (by decide))).write q _ (hc (d := 8) (by decide))).write q _ (hc (d := 16) (by decide))).write q _
    (hc (d := 24) (by decide))).write q _ (hc (d := 32) (by decide))).write q _ (hc (d := 40) (by decide))

theorem argMem_slot (s u : State) {j : Nat} (hj : j < 6) :
    (argMem s u).readW (off (Q s) (8 * j)) 64 =
      [Q s + 64#64, u.gpr .x15, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6].getD j 0 := by
  match j, hj with
  | 0, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 1, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 2, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 3, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 4, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 5, _ => simp (disch := decide) only [argMem, off, rd_self, Nat.reduceMul]; rfl

theorem argMem_tape {P : Nat} {s u : State} (hp : RPre P s) (hx2 : u.gpr .x2 = s.gpr .x2) :
    (argMem s u).readW (s.gpr .x2) 64 = stackArg s 2 - u.gpr .x12 ∧
      (argMem s u).readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0 := by
  obtain hQ := Q_toNat hp
  have hw := hp.wT
  obtain hd : (tapeR s).Disjoint ⟨Q s, 48⟩ := fun x h₁ h₂ =>
    hp.dKt x (frame_sub (P := P) s (d := 0) (n := 48) (by decide) x (by rw [off, add_zero']; exact h₂)) h₁
  obtain hsep : ∀ {a : Nat}, a + 8 ≤ 16 → ∀ {d : Nat}, d + 8 ≤ 48 →
      Mem.Sep (s.gpr .x2 + BitVec.ofNat 64 a) 8 (Q s + BitVec.ofNat 64 d) 8 := fun ha _ hd' =>
    hd.sep (Offset.contains_base _ ha (by omega_using [ha])) (Offset.contains_base _ hd' (by omega_using [hd']))
  obtain e0 : s.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 0 := (add_zero' _).symm
  constructor
  · rw [e0]
    simp only [argMem, hx2]
    rw [rd_sep _ (hsep (a := 0) (by decide) (d := 40) (by decide)), rd_sep _ (hsep (a := 0) (by decide) (d := 32) (by decide)),
      rd_sep _ (hsep (a := 0) (by decide) (d := 24) (by decide)), rd_sep _ (hsep (a := 0) (by decide) (d := 16) (by decide)),
      rd_sep _ (hsep (a := 0) (by decide) (d := 8) (by decide)), rd_sep _ (hsep (a := 0) (by decide) (d := 0) (by decide)),
      rd_q _ _ _ (.inl (by decide)) (by decide) (by decide), rd_self]
  · simp only [argMem, hx2]
    rw [rd_sep _ (hsep (a := 8) (by decide) (d := 40) (by decide)), rd_sep _ (hsep (a := 8) (by decide) (d := 32) (by decide)),
      rd_sep _ (hsep (a := 8) (by decide) (d := 24) (by decide)), rd_sep _ (hsep (a := 8) (by decide) (d := 16) (by decide)),
      rd_sep _ (hsep (a := 8) (by decide) (d := 8) (by decide)), rd_sep _ (hsep (a := 8) (by decide) (d := 0) (by decide)),
      rd_self]
    rfl

theorem args_ok {P : Nat} {s u : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Ready s u i pad) :
    WP isa (.block callArgs) u (Args s · i pad) := by
  obtain hQ := Q_toNat hp
  have hsp := h.sp
  obtain hin : ∀ {j : Nat}, j < 7 → InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 :=
    fun hj => by rw [h.rd, h.wr, ← entered_rd]; exact args_in hp hj
  obtain a0 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1104) 8 := hin (j := 0) (by decide)
  obtain a2 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1120) 8 := hin (j := 2) (by decide)
  obtain a3 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1128) 8 := hin (j := 3) (by decide)
  obtain a4 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1136) 8 := hin (j := 4) (by decide)
  obtain a5 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1144) 8 := hin (j := 5) (by decide)
  obtain a6 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1152) 8 := hin (j := 6) (by decide)
  obtain m0 : u.mem.read (Q s + BitVec.ofNat 64 1104) 8 = stackArg s 0 := arg_u hp h.toInFrame (j := 0) (by decide)
  obtain m2 : u.mem.read (Q s + BitVec.ofNat 64 1120) 8 = stackArg s 2 := arg_u hp h.toInFrame (j := 2) (by decide)
  obtain m3 : u.mem.read (Q s + BitVec.ofNat 64 1128) 8 = stackArg s 3 := arg_u hp h.toInFrame (j := 3) (by decide)
  obtain m4 : u.mem.read (Q s + BitVec.ofNat 64 1136) 8 = stackArg s 4 := arg_u hp h.toInFrame (j := 4) (by decide)
  obtain m5 : u.mem.read (Q s + BitVec.ofNat 64 1144) 8 = stackArg s 5 := arg_u hp h.toInFrame (j := 5) (by decide)
  obtain m6 : u.mem.read (Q s + BitVec.ofNat 64 1152) 8 = stackArg s 6 := arg_u hp h.toInFrame (j := 6) (by decide)
  obtain hx2 : u.gpr .x2 = s.gpr .x2 := h.keep _ (by decide)
  obtain htw : (tapeR s) ∈ u.wr := by rw [h.wr, entered_wr, hp.hwr]; simp
  obtain t0 : InRegions u.wr (u.gpr .x2 + 0#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  obtain t8 : InRegions u.wr (u.gpr .x2 + 8#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  obtain hfw : ∀ {d : Nat}, d + 8 ≤ frameBytes → InRegions u.wr (Q s + BitVec.ofNat 64 d) 8 :=
    fun hd => by rw [h.wr]; exact frame_in hd
  obtain s0 : InRegions u.wr (Q s + 0#64) 8 := hfw (d := 0) (by decide)
  obtain s8 : InRegions u.wr (Q s + 8#64) 8 := hfw (d := 8) (by decide)
  obtain s16 : InRegions u.wr (Q s + 16#64) 8 := hfw (d := 16) (by decide)
  obtain s24 : InRegions u.wr (Q s + 24#64) 8 := hfw (d := 24) (by decide)
  obtain s32 : InRegions u.wr (Q s + 32#64) 8 := hfw (d := 32) (by decide)
  obtain s40 : InRegions u.wr (Q s + 40#64) 8 := hfw (d := 40) (by decide)
  apply WP.of_runBlock
  simp only [callArgs, Size.bytes, t0, t8, s0, s8, s16, s24, s32, s40, arg, frameBytes, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr,
    State.load, State.store, State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq,
    ite_false, a0, a2, a3, a4, a5, a6, m0, m2, m3, m4, m5, m6, Option.some.injEq, exists_eq_left']
  have hx12 := h.x12
  obtain hl := (stackArg s 2).isLt
  have hu := h.used
  obtain hfa := argMem_frame hp hx2
  have hQ' := hQ
  have hP := hp.ps
  obtain dT : (tapeR s).Disjoint ⟨Q s, 1104⟩ := fun x h₁ h₂ =>
    hp.dKt x (frame_sub (P := P) s (d := 0) (n := 1104) (by decide) x (by rw [off, add_zero']; exact h₂)) h₁
  obtain apart : ∀ {d n : Nat}, 48 ≤ d → d + n ≤ 1104 → ∀ r ∈ [tapeR s, (⟨Q s, 48⟩ : Region)],
      Region.Disjoint ⟨off (Q s) d, n⟩ r := fun h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dT.sub_right (Offset.sub_base _ h2)).symm
    · exact Offset.disjoint_base _ h1 (by omega_using [h2])
  obtain ⟨ht0, ht1⟩ := argMem_tape hp hx2 (u := u)
  have keepS : ∀ r, r ∉ [Reg.x9, .x11, .x12, .x14, .x15, .x16, .x17] → u.gpr r = s.gpr r := h.keep
  refine ⟨rfl, h.rd, h.wr, h.v, ?_, ?_, ?_, fun j hj => ?_, ?_, h.len, ?_, ht1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_⟩
  · exact (h.fr.mono (by simp)).trans (hfa.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨tapeR s, by simp, fun _ h => h⟩
      · exact ⟨⟨Q s, 1104⟩, by simp, by
          have := Offset.sub_base (Q s) (d := 0) (n := 48) (k := 1104) (by decide)
          rwa [add_zero'] at this⟩)
  · show (argMem s u).readW _ 64 = _
    rw [hfa.readW (Region.contains_self _ _) (apart (d := oPs) (n := 8) (by decide) (by decide)) (by decide)]
    exact h.ps
  · show (argMem s u).readW _ 64 = _
    rw [hfa.readW (Region.contains_self _ _) (apart (d := 1088) (n := 8) (by decide) (by decide)) (by decide)]
    exact h.lr
  · show (argMem s u).readW _ 64 = _
    rw [argMem_slot s u hj]
    match j, hj with
    | 0, _ => rfl
    | 1, _ => exact h.x15
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
  · show Spec.Rsa.bytesAt (argMem s u) _ _ = _
    rw [← h.buf]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun j hj => ?_
    exact hfa.bytes (R := ⟨off (Q s) oBuf, psLen s⟩) (apart (by decide) (by unfold oBuf; omega_using [hP]))
      (by show psLen s ≤ 2 ^ 64; omega_using [hP]) (List.mem_range.mp hj)
  · show (argMem s u).readW _ 64 = _
    rw [ht0, hx12, ← sub_used hl hu, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, BitVec.or_self]
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hr
    simp only [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h16, h17, ite_false]
    exact keepS r (by simp [h9, h11, h12, h14, h15, h16, h17])

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the call

The call of `vg_rsa_pkcs1_encrypt_precomputed`, calling the precomputed
public operation `c`, by its contract (`call_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

/-- The callee, `vg_rsa_pkcs1_encrypt_precomputed` calling `c`. -/
def encName (c : PdChecked) : String := "vg_rsa_pkcs1_encrypt_precomputed" ++ c.suffix
def encCode (c : PdChecked) : Prog isa := Impl.RsaPkcs1Enc.AArch64.Precomputed.code c.name c.code

/-- What the callee reads: `n`, `e`, `msg`, `PS`, `pre` and its stack
arguments. -/
def callRd (s : State) : List Region :=
  [nR s, eR s, msgR s, ⟨off (Q s) oBuf, psLen s⟩, preR s, ⟨Q s, 48⟩]

/-- What it writes: `out` and `scratch`. -/
def callWr (s : State) : List Region := [outR s, scrR s]

theorem stackArg_call {s w : State} {i : Nat} {pad : List Byte} (h : Args s w i pad) (rd wr : List Region)
    {j : Nat} (hj : j < 6) : stackArg (w.callEntry.withRegions rd wr) j = callArg s j := by
  show w.mem.readW (w.sp + BitVec.ofNat 64 (8 * j)) 64 = _
  rw [h.sp]; exact h.args j hj

theorem Q_sub (P : Nat) (s : State) : Q s - BitVec.ofNat 64 (P + 1087 + 1) = kb P s := by
  rw [Q_kb P s, off]; exact BitVec.add_sub_cancel _ _

theorem call_pre {P : Nat} {s w : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (P + 1088)).pre
      (w.callEntry.withRegions (callRd s) (callWr s)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hK := kb_toNat hp
  have hbuf : off (Q s) oBuf = off (kb P s) (P + 1088 + oBuf) := by rw [Q_kb P s, off_off]
  have sBuf : Region.Sub ⟨off (Q s) oBuf, psLen s⟩ (stkR P s) := frame_sub s (by unfold oBuf; omega_using [hP])
  have sA : Region.Sub ⟨Q s, 48⟩ (stkR P s) := by
    have := frame_sub (P := P) s (d := 0) (n := 48) (by decide)
    rwa [off, add_zero'] at this
  have sStk : Region.Sub ⟨kb P s, P + 1087 + 1⟩ (stkR P s) := by
    rw [stkR_eq]; exact Region.sub_prefix (by unfold rndStack; omega_using [])
  have wK : (kb P s).toNat + P + 2192 ≤ 2 ^ 64 := by
    have := hp.sp2
    have h' : (kb P s).toNat + P + 2192 = s.sp.toNat := by rw [Nat.add_assoc]; exact hK
    omega_using [h']
  have dSB : (⟨kb P s, P + 1087 + 1⟩ : Region).Disjoint ⟨off (Q s) oBuf, psLen s⟩ := by
    rw [hbuf]; exact Offset.base_disjoint _ (by omega_using []) (by unfold oBuf; omega_using [hP, hQ])
  have dSA : (⟨kb P s, P + 1087 + 1⟩ : Region).Disjoint ⟨Q s, 48⟩ := by
    have := Offset.base_disjoint (kb P s) (e := P + 1088) (n := 48) (k := P + 1087 + 1) (by omega_using [])
      (by omega_using [hQ])
    rwa [show kb P s + BitVec.ofNat 64 (P + 1088) = Q s from (Q_kb P s).symm] at this
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hK := kb_toNat hp
  have hpsN : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have hA : stackArgAddr (w.callEntry.withRegions (callRd s) (callWr s)) 0 = Q s := by
    show w.sp + BitVec.ofNat 64 (8 * 0) = _
    rw [h.sp]; exact add_zero' _
  simp only [h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.sp, hA, Q_sub,
    stackArg_call h _ _ (j := 0) (by decide), stackArg_call h _ _ (j := 1) (by decide),
    stackArg_call h _ _ (j := 2) (by decide), stackArg_call h _ _ (j := 3) (by decide),
    stackArg_call h _ _ (j := 4) (by decide), stackArg_call h _ _ (j := 5) (by decide), callArg, hpsN]
  refine ⟨hQ.2, by have := hp.sp2; omega_arith, rfl, rfl,
    hp.dOn, hp.dOe, hp.dOm, (hp.dKo.sub_left sBuf).symm, hp.dOs, hp.dOq, (hp.dKo.sub_left sA).symm,
    hp.dNs, hp.dEs, hp.dMs, hp.dKs.sub_left sBuf, hp.dSq, (hp.dKs.sub_left sA).symm,
    hp.dKo.sub_left sStk, hp.dKn.sub_left sStk, hp.dKe.sub_left sStk, hp.dKm.sub_left sStk, dSB,
    hp.dKs.sub_left sStk, hp.dKq.sub_left sStk, dSA,
    hp.wO, hp.wN, hp.wE, hp.wM, ?_, hp.wS, hp.wQ,
    ⟨hp.k1, hp.k2⟩, hp.hsi, hp.L1, hp.L2, hp.hml, rfl, hp.hsl, hp.hql⟩
  rw [off_toNat (by unfold oBuf; omega_arith)]
  unfold oBuf; omega_arith

theorem enc_depth (c : PdChecked) : (encCode c).aarch64Depth = c.code.aarch64Depth + 68 := by
  simp only [encCode, Impl.RsaPkcs1Enc.AArch64.Precomputed.code, Impl.RsaPkcs1Enc.AArch64.Precomputed.body,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.psLoop, Impl.RsaPkcs1Enc.AArch64.Encrypt.msgCopy,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.msgLoop,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.maskLoop, Code.aarch64Depth, Instr.frameUnits,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.frameBytes, Nat.zero_max, Nat.max_zero, Nat.reduceDiv, Nat.add_assoc,
    Nat.reduceAdd]

theorem call_covers {P : Nat} {s w : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    Covers (callRd s) (w.rd ++ w.wr) ∧ Covers (callWr s) w.wr := by
  have hP := hp.ps
  have hfr : (⟨Q s, frameBytes⟩ : Region) ∈ w.rd ++ w.wr := by rw [h.wr, entered_wr]; simp
  have cw : Covers (callWr s) w.wr := Covers.of_mem fun r hr => by
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.wr, entered_wr, hp.hwr]
    rcases hr with rfl | rfl <;> simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (add_zero' p).symm
  have cr : Covers (callRd s) (w.rd ++ w.wr) := Covers.of_forall fun r hr => by
    simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨_, hfr, oBuf, rfl, by dsimp only; unfold frameBytes oBuf; omega_using [hP]⟩
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, hfr, 0, z _, by dsimp only; unfold frameBytes; omega_using []⟩
  exact ⟨cr, cw⟩

/-- What the callee reads, as on entry. -/
theorem args_read {P : Nat} {s w : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat = nB s ∧
      Spec.Rsa.bytesAt w.mem (s.gpr .x5) (s.gpr .x6).toNat = eB s ∧
      Spec.Rsa.bytesAt w.mem (s.gpr .x7) (stackArg s 0).toNat = msgB s ∧
      Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s := by
  have dQ : ∀ {R : Region}, (stkR P s).Disjoint R → (tapeR s).Disjoint R →
      ∀ r ∈ [(⟨Q s, 1104⟩ : Region), tapeR s], R.Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := frame_sub (P := P) s (d := 0) (n := 1104) (by decide)
      rw [off, add_zero'] at this
      exact (h₁.sub_left this).symm
    · exact h₂.symm
  have bytes_eq : ∀ {R : Region}, (stkR P s).Disjoint R → (tapeR s).Disjoint R → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt w.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := fun h₁ h₂ hl => by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun j hj => h.fr.bytes (dQ h₁ h₂) hl (List.mem_range.mp hj)
  have nE : Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat = nB s :=
    bytes_eq (R := nR s) hp.dKn hp.dTn (by have := hp.wN; unfold nR; dsimp only; omega_using [])
  have eE : Spec.Rsa.bytesAt w.mem (s.gpr .x5) (s.gpr .x6).toNat = eB s :=
    bytes_eq (R := eR s) hp.dKe hp.dTe (by have := hp.wE; unfold eR; dsimp only; omega_using [])
  have mE : Spec.Rsa.bytesAt w.mem (s.gpr .x7) (stackArg s 0).toNat = msgB s :=
    bytes_eq (R := msgR s) hp.dKm hp.dTm (by have := hp.wM; unfold msgR; dsimp only; omega_using [])
  have qE : Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s := by
    unfold Spec.Rsa.wordsAt preW Spec.Rsa.wordsAt
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have hw := hp.wQ
    exact h.fr.readW (r := preR s) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hw]))
      (dQ hp.dKq hp.dTq) (by decide)
  exact ⟨nE, eE, mE, qE⟩

/-- After the call. -/
structure AfterCall (P : Nat) (s u : State) (i : Nat) (pad : List Byte) : Prop where
  sp : u.sp = Q s
  rd : u.rd = s.rd
  wr : u.wr = (entered s).wr
  cs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem u.mem
  ps : u.mem.readW (off (Q s) oPs) 64 = BitVec.ofNat 64 (psLen s)
  lr : u.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  tape0 : u.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i
  tape1 : u.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0
  res : Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
    Spec.Rsa.written u.mem (s.gpr .x0) (kOf s) ((u.gpr .x0).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad)

theorem call_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s w : State} (hp : RPre c.stack s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    WP isa (.call (encName c) (encCode c)) w (AfterCall c.stack s · i pad) := by
  have hpre := call_pre hp h
  have hv := (Enc.Pc.code_verified c hsat).1
  have hdp := c.depth
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hd16 : 16 * (encCode c).aarch64Depth ≤ c.stack + 1088 := by rw [enc_depth]; omega_using [hdp]
  obtain ⟨cr, cw⟩ := call_covers hp h
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (add_zero' p).symm
  refine WP.callFV hv hpre (Covers.append_left cr cw.right) cw (fun u hrd hwr hsp hf hcs hvs hpost => ?_)
    (by show 16 * (encCode c).aarch64Depth < 2 ^ 64; have := c.le; omega_using [hQ, hd16])
  sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at hpost
  have hpsN : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hP])
  simp only [h.x0, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7,
    stackArg_call h _ _ (j := 0) (by decide), stackArg_call h _ _ (j := 1) (by decide),
    stackArg_call h _ _ (j := 4) (by decide), stackArg_call h _ _ (j := 5) (by decide), callArg, hpsN,
    h.buf] at hpost
  obtain ⟨nE, eE, mE, qE⟩ := args_read hp h
  rw [nE, eE, mE, qE] at hpost
  -- what the call leaves
  have sB : Region.Sub (below w.sp (16 * (encCode c).aarch64Depth)) (stkR c.stack s) := by
    rw [h.sp]
    have := Offset.sub_below (Q s) (a := 16 * (encCode c).aarch64Depth) (n := 16 * (encCode c).aarch64Depth)
      (b := c.stack + 1087 + 1) (m := c.stack + 1087 + 1) (by omega_using [hd16]) (by omega_using [hd16])
    rw [Q_sub] at this
    rw [stkR_eq]
    exact fun x hx => Region.sub_prefix (by unfold rndStack; omega_using []) x (this x hx)
  have hws : ∀ r ∈ callWr s ++ [below w.sp (16 * (encCode c).aarch64Depth)],
      r = outR s ∨ r = scrR s ∨ Region.Sub r (stkR c.stack s) := fun r hr => by
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr sB)
  have apart : ∀ {R : Region}, R.Disjoint (outR s) → R.Disjoint (scrR s) →
      R.Disjoint (below w.sp (16 * (encCode c).aarch64Depth)) →
      ∀ {a : Addr}, R.Contains a 8 → u.mem.readW a 64 = w.mem.readW a 64 := fun h₁ h₂ h₃ _ ha =>
    hf.readW ha (fun r hr => by
      simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃) (by decide)
  have slot : ∀ (d : Nat), d + 8 ≤ 1104 → u.mem.readW (off (Q s) d) 64 = w.mem.readW (off (Q s) d) 64 :=
    fun d hd => apart (R := ⟨off (Q s) d, 8⟩) (hp.dKo.sub_left (frame_sub s hd))
      (hp.dKs.sub_left (frame_sub s hd)) (by
        rw [h.sp]; exact Offset.disjoint_below _ (by omega_using [hQ, hd16, hd])) (Region.contains_self _ _)
  have tB : (tapeR s).Disjoint (below w.sp (16 * (encCode c).aarch64Depth)) := hp.dKt.symm.sub_right sB
  have hpk : ∀ r ∈ preserved, r ≠ .x30 →
      r ∉ [Reg.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] := by
    decide
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun r hr h30 => (hcs r hr h30).trans (h.keep r (hpk r hr h30)),
    fun r hr => by rw [hvs r hr, h.v], ?_, (slot _ (by decide)).trans h.ps, (slot _ (by decide)).trans h.lr,
    (apart hp.dOt.symm hp.dTs tB (by
      rw [z (s.gpr .x2)]; exact Offset.contains_base _ (by decide) (by decide))).trans h.tape0,
    (apart hp.dOt.symm hp.dTs tB (Offset.contains_base _ (by decide) (by decide))).trans h.tape1,
    fun hq => hpost hq⟩
  refine (h.fr.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨stkR c.stack s, by simp, ?_⟩
      have := frame_sub (P := c.stack) s (d := 0) (n := 1104) (by decide)
      rwa [off, add_zero'] at this
    · exact ⟨tapeR s, by simp, fun _ h => h⟩
  · rcases hws r hr with rfl | rfl | hs
    · exact ⟨outR s, by simp, fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨stkR c.stack s, by simp, hs⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-! ### `RsaPkcs1Enc.AArch64.RndReject`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndTail`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the zero loops

The three loops that store zeros, `n` bytes from a pointer register
counting down a counter register (`zloop_ok`): the wipe of `PS`, `out`
zeroed and the octets drawn wiped.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- The body of a zero loop. -/
abbrev zbody (rz rp rc : Reg) : List Instr := [.strb rz rp 0, .addImm .x rp rp 1, .subImm .x rc rc 1]

/-- After one iteration, from `t`. -/
structure ZStep (rz rp rc : Reg) (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr rp) 1 ((t.gpr rz).setWidth 8)
  ptr : u.gpr rp = t.gpr rp + BitVec.ofNat 64 1
  ctr : u.gpr rc = t.gpr rc - BitVec.ofNat 64 1
  other : ∀ r, r ≠ rp → r ≠ rc → u.gpr r = t.gpr r

theorem zbody_ok {rz rp rc : Reg} (hpc : rp ≠ rc) {t : State}
    (hw : InRegions t.wr (t.gpr rp + BitVec.ofNat 64 0) 1) :
    WP isa (.block (zbody rz rp rc)) t (ZStep rz rp rc t) := by
  apply WP.of_runBlock
  simp only [zbody, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h1 h2 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  · simp only [RegUpd.gpr_write, hpc, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, Ne.symm hpc, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h1, h2, ite_false]

/-- After `k` of the `n` iterations of a zero loop from `t`. -/
structure ZInv (rp rc : Reg) (p : Addr) (n : Nat) (t : State) (k : Nat) (u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  keep : Keeps [rp, rc] t u
  ptr : u.gpr rp = p + BitVec.ofNat 64 k
  ctr : u.gpr rc = BitVec.ofNat 64 (n - k)
  fr : Frame [⟨p, n⟩] t.mem u.mem
  zero : ∀ j < k, u.mem (p + BitVec.ofNat 64 j) = 0

theorem zloop_ok {rz rp rc : Reg} (hpc : rp ≠ rc) (hzp : rz ≠ rp) (hzc : rz ≠ rc) {p : Addr} {n : Nat}
    (hn : 0 < n) (hn' : n < 2 ^ 64) {t : State} (hR : ∃ R ∈ t.wr, Region.Sub ⟨p, n⟩ R)
    (hz : t.gpr rz = 0) (hp0 : t.gpr rp = p) (hc0 : t.gpr rc = BitVec.ofNat 64 n) :
    WP isa (.loop (.block (zbody rz rp rc)) (.nonzero .x rc)) t (ZInv rp rc p n t n) := by
  obtain ⟨R, hRm, hRs⟩ := hR
  refine Bytes.count_loop hn (ZInv rp rc p n t) (fun k hk u hu => ?_)
    ⟨rfl, rfl, rfl, rfl, Keeps.refl _ _, by rw [hp0, add_zero'], by rw [hc0, Nat.sub_zero],
      Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hc : (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hn', hk])
  have hw : InRegions u.wr (u.gpr rp + BitVec.ofNat 64 0) 1 := by
    rw [add_zero', hu.ptr, hu.wr]; exact ⟨R, hRm, hRs _ hc⟩
  refine WP.mono (zbody_ok hpc hw) fun w hw' => ?_
  have hzu : u.gpr rz = 0 := (hu.keep rz (by simp [hzp, hzc])).trans hz
  have hm : w.mem = u.mem.write (p + BitVec.ofNat 64 k) 1 0 := by rw [hw'.mem, hu.ptr, hzu]; rfl
  have hrc : w.gpr rc = BitVec.ofNat 64 (n - (k + 1)) := by rw [hw'.ctr, hu.ctr, Bytes.counter_step hk hn']
  refine ⟨⟨hw'.rd.trans hu.rd, hw'.wr.trans hu.wr, hw'.sp.trans hu.sp, hw'.v.trans hu.v, fun r hr => ?_,
    by rw [hw'.ptr, hu.ptr, add_add'], hrc, by rw [hm]; exact hu.fr.write (List.mem_singleton_self _) _ hc,
    fun j hj => ?_⟩, by rw [hrc, Bytes.counter_ne hk hn']⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hw'.other r hr.1 hr.2]; exact hu.keep r (by simp [hr.1, hr.2])
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [hn', hk]) (by omega_using [hj]))]; exact hu.zero j hj
    · exact Bytes.write1_self _ _ _

/-- The zero loop's bytes. -/
theorem zloop_bytes {rp rc : Reg} {p : Addr} {n : Nat} {t u : State} (h : ZInv rp rc p n t n u) :
    Spec.Rsa.bytesAt u.mem p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro j h₁ _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h.zero j h₁

/-- What every path leaves, at the end of the frames' body. -/
structure Fin (P : Nat) (s x : State) : Prop where
  sp : x.sp = Q s
  rd : x.rd = s.rd
  wr : x.wr = (entered s).wr
  fr : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem x.mem
  lr : x.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  cs : ∀ r ∈ preserved, r ≠ .x30 → x.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (x.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- After `status`, from `u`. -/
structure StatusStep (s u w : State) : Prop where
  rd : w.rd = u.rd
  wr : w.wr = u.wr
  sp : w.sp = u.sp
  vv : w.v = u.v
  mem : w.mem = u.mem
  x0 : (w.gpr .x0).setWidth 32 = 2 - (u.gpr .x0).setWidth 32
  x12 : w.gpr .x12 = BitVec.ofNat 64 1024
  x13 : w.gpr .x13 = off (Q s) oBuf
  x14 : w.gpr .x14 = 0
  keep : Keeps [.x0, .x9, .x12, .x13, .x14] u w

theorem status_ok {P : Nat} {s u : State} {i : Nat} {pad : List Byte} (h : AfterCall P s u i pad) :
    WP isa (.block status) u (StatusStep s u) := by
  have hsp := h.sp
  apply WP.of_runBlock
  simp only [status, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, 
    State.read, Size.bits, BitVec.setWidth_eq, Nat.reduceLT, Nat.reduceMul,
    BitVec.shiftLeft_zero, ite_true, hsp, RegUpd.sp_write, RegUpd.gpr_write,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h9, h12, h13, h14⟩ := hr
    simp only [RegUpd.gpr_write, h0, h9, h12, h13, h14, ite_false]

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun j hj => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hj)

theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) : Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [h1]; rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [h1]; rfl, h2⟩

/-- `PS`'s area in the frame. -/
abbrev psR (s : State) : Region := ⟨off (Q s) oBuf, 1024⟩

theorem psR_sub {P : Nat} (s : State) : Region.Sub (psR s) (stkR P s) :=
  frame_sub s (by unfold oBuf; omega_using [])

/-- The status and the wipe of `PS`, after the call. -/
theorem accTail_ok {P : Nat} {s u : State} (hp : RPre P s) {i : Nat} {pad : List Byte}
    (h : AfterCall P s u i pad) :
    WP isa (.seq (.block status) wipe) u fun x => Fin P s x ∧
      x.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i ∧ x.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0 ∧
      (Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
        Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .x0) (kOf s) ((x.gpr .x0).setWidth 32)
          (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  refine WP.seq (WP.mono (status_ok h) fun w hw => ?_)
  have hR : ∃ R ∈ w.wr, Region.Sub (psR s) R :=
    ⟨⟨Q s, frameBytes⟩, by rw [hw.wr, h.wr, entered_wr]; simp, Offset.sub_base _ (by unfold oBuf frameBytes; omega_using [])⟩
  refine WP.mono (zloop_ok (rz := .x14) (rp := .x13) (rc := .x12) (by decide) (by decide) (by decide)
    (by decide) (by decide) hR hw.x14 hw.x13 hw.x12) fun x hx => ?_
  have hf : Frame [psR s] u.mem x.mem := by rw [← hw.mem]; exact hx.fr
  have dK : ∀ {R : Region}, (stkR P s).Disjoint R → ∀ r ∈ [psR s], R.Disjoint r := fun hd r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_left (psR_sub s)).symm
  have kx : ∀ r, r ∉ [Reg.x0, .x9, .x12, .x13, .x14] → x.gpr r = u.gpr r := fun r hr =>
    (hx.keep r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.2.2.2.1, hr.2.2.1⟩)).trans
      (hw.keep r hr)
  refine ⟨⟨hx.sp.trans (hw.sp.trans h.sp), hx.rd.trans (hw.rd.trans h.rd), hx.wr.trans (hw.wr.trans h.wr),
    h.fr.trans (hf.sub fun r hr => ⟨stkR P s, by simp, by rw [List.mem_singleton.mp hr]; exact psR_sub s⟩),
    ?_, fun r hr h30 => (kx r ?_).trans (h.cs r hr h30), fun r hr => by rw [hx.v, hw.vv]; exact h.vs r hr⟩,
    ?_, ?_, fun hq => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by unfold oBuf; omega_using [])) (by omega_using []) (by unfold oBuf; omega_using [])) (by decide)]
    exact h.lr
  · revert hr h30; revert r; decide
  · have ht0 : (tapeR s).Contains (s.gpr .x2) 8 := by
      have := Offset.contains_base (s.gpr .x2) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [add_zero'] at this
    rw [hf.readW (w := 64) ht0 (dK hp.dKt) (by decide)]
    exact h.tape0
  · rw [hf.readW (w := 64) (r := tapeR s) (Offset.contains_base _ (by decide) (by decide)) (dK hp.dKt) (by decide)]
    exact h.tape1
  · have e : (⟨s.gpr .x0, kOf s⟩ : Region) = outR s := by rw [outR, kOf, hp.hsi]
    have h0 : (x.gpr .x0).setWidth 32 = 2 - (u.gpr .x0).setWidth 32 := by
      rw [hx.keep .x0 (by decide)]; exact hw.x0
    have hb := bytes_frame (p := s.gpr .x0) (n := kOf s) hf (by rw [e]; exact dK hp.dKo)
      (by have := hp.k2; unfold kOf; omega_using [])
    have hw0 := written_random (h.res hq)
    rw [h0]
    revert hw0
    cases Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad <;>
      simp only [Spec.RsaPkcs1Enc.writtenRandom, hb] <;> exact id

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: no padding string

The tape read with fewer than `psLen` nonzero octets (`reject_ok`): `out`
zeroed, `PS`'s area wiped, and the status and `tape` by the budget, from
each block of `reject` from any state (`zpre_ok`, `wd_ok`, `outcome_ok`).
What each path leaves (`post`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-! ## The blocks -/
/-- The registers but `rs`, and the rest of the state but memory, are
`t`'s. -/
structure Same (rs : List Reg) (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  keep : Keeps rs t u

theorem zpre_ok (t : State) :
    WP isa (.block [.logic .orr .x .x9 .x0 .x0, .logic .orr .x .x10 .x4 .x4, .movz .x .x13 0 0]) t fun u =>
      Same [.x9, .x10, .x13] t u ∧ u.mem = t.mem ∧ u.gpr .x9 = t.gpr .x0 ∧ u.gpr .x10 = t.gpr .x4 ∧
        u.gpr .x13 = 0 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.read, Size.bits, BitVec.setWidth_eq,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, ite_true, 
    RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false,
    BitVec.or_self, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, trivial, trivial, trivial, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem wd_ok (t : State) :
    WP isa (.block [.movz .x .x10 1024 0, .addSp .x9 oBuf]) t fun u =>
      Same [.x9, .x10] t u ∧ u.mem = t.mem ∧ u.gpr .x10 = BitVec.ofNat 64 1024 ∧
        u.gpr .x9 = off t.sp oBuf := by
  apply WP.of_runBlock
  simp only [oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, BitVec.shiftLeft_zero, Nat.reduceLT, ite_true, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, trivial, rfl, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `subs`'s carry: no borrow, `a ≥ b`. -/
theorem carry_sub (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + (true).toNat) = decide (b.toNat ≤ a.toNat) := by
  rw [BitVec.toNat_not]
  have := b.isLt
  simp only [Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega_using [])

theorem outcome_ok {t : State} {rl : BitVec 64}
    (ha : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 1120) 8)
    (hm : t.mem.read (t.sp + BitVec.ofNat 64 1120) 8 = rl)
    (t0 : InRegions t.wr (t.gpr .x2 + 0#64) 8) (t8 : InRegions t.wr (t.gpr .x2 + 8#64) 8) :
    WP isa (.block outcome) t fun u => Same [.x0, .x9, .x10, .x11, .x12, .x13, .x14, .x17] t u ∧
      u.mem = (t.mem.write (t.gpr .x2 + 0#64) 8
          (if (t.gpr .x15 + 128#64).toNat ≤ rl.toNat then rl else 0)).write (t.gpr .x2 + 8#64) 8
        (if (t.gpr .x15 + 128#64).toNat ≤ rl.toNat then 0 else
          if (t.gpr .x15 + rl - (t.gpr .x15 - t.gpr .x16)).toNat ≤ (t.gpr .x15 + 128#64).toNat then
            t.gpr .x15 + rl - (t.gpr .x15 - t.gpr .x16) else t.gpr .x15 + 128#64) ∧
      u.gpr .x0 = if (t.gpr .x15 + 128#64).toNat ≤ rl.toNat then 3 else 0 := by
  apply WP.of_runBlock
  simp only [outcome, arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.load,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, BitVec.shiftLeft_zero, and_self, ite_true, ha, hm,
    CondCode.holds, RegUpd.c_write, RegUpd.c_addWithCarry, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.v_write, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.rd_addWithCarry,
    RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry, RegUpd.mem_addWithCarry, reduceCtorEq, ite_false,
    carry_sub, t0, t8, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h9, h10, h11, h12, h13, h14, h17⟩ := hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, h0, h9, h10, h11, h12, h13, h14, h17, ite_false]
  · by_cases h1 : (t.gpr .x15 + 128#64).toNat ≤ rl.toNat <;>
    by_cases h2 : (t.gpr .x15 + rl - (t.gpr .x15 - t.gpr .x16)).toNat ≤ (t.gpr .x15 + 128#64).toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_true, ite_false] <;> rfl
  · by_cases h1 : (t.gpr .x15 + 128#64).toNat ≤ rl.toNat <;>
    simp only [h1, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, 
      ] <;> rfl

/-! ## The outcome -/

/-- The contract's postcondition, by name. -/
def post (s u : State) : Prop :=
  let res := Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)
  (∃ req, u.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 res.used ∧
    u.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧
    res.Requests (Spec.RsaPkcs1Enc.padEntropy (psLen s)) req) ∧
  match res.outcome with
  | .accepted ps => Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
      Spec.RsaPkcs1Enc.writtenRandom u.mem (s.gpr .x0) (kOf s) ((u.gpr .x0).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)
  | .entropy .. => (u.gpr .x0).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0
  | .exhausted => (u.gpr .x0).setWidth 32 = 3 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0

theorem kept_all (s : State) : kept s (stackArg s 2).toNat = VG.Proof.RsaPkcs1Enc.nz (randB s) := by
  simp only [kept]; rw [← randB_length, List.take_length]

/-- A stack argument, in memory changed only in the frame and `out`. -/
theorem arg_mem {P : Nat} {s : State} (hp : RPre P s) {m : Mem} (hf : Frame [⟨Q s, 1104⟩, outR s] s.mem m)
    {j : Nat} (hj : j < 7) : m.read (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 = stackArg s j := by
  obtain hQ := Q_toNat hp
  obtain hc : (argsR s).Contains (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 := by
    rw [← off, ← stackArgAddr_Q]; exact arg_contains s hj
  obtain h := hf.read (r := ⟨Q s + BitVec.ofNat 64 (1104 + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base (Q s) (d := 1104 + 8 * j) (n := 8) (k := 1104) (by omega_using []) (by omega_using [hj])
      · exact fun x h₁ h₂ => hp.dOa x h₂ (hc.byte (by simp only [Region.Contains] at h₁; omega_using [h₁]))) (by decide)
  rw [h]
  show s.mem.read _ 8 = s.mem.readW (stackArgAddr s j) 64
  rw [stackArgAddr_Q]; rfl

theorem rd_tape0 (m : Mem) (p : Addr) (a b : BitVec 64) :
    ((m.write (p + 0#64) 8 a).write (p + 8#64) 8 b).readW p 64 = a := by
  obtain h1 := rd_q (m.write (p + 0#64) 8 a) p (d := 0) (e := 8) b (.inl (by decide)) (by decide) (by decide)
  rw [rd_self] at h1
  rw [add_zero'] at h1 ⊢
  exact h1

theorem rd_tape1 (m : Mem) (p : Addr) (a b : BitVec 64) :
    ((m.write (p + 0#64) 8 a).write (p + 8#64) 8 b).readW (p + BitVec.ofNat 64 8) 64 = b := rd_self _ _ _

theorem frame_tape {s : State} (m : Mem) (a b : BitVec 64) :
    Frame [tapeR s] m ((m.write (s.gpr .x2 + 0#64) 8 a).write (s.gpr .x2 + 8#64) 8 b) :=
  ((Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).write
    (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem psLen_add {P : Nat} {s : State} (hp : RPre P s) :
    (BitVec.ofNat 64 (psLen s) + BitVec.ofNat 64 128).toNat = psLen s + 128 := by
  have := hp.ps
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show psLen s < 2 ^ 64 by omega_using [this]),
    Nat.mod_eq_of_lt (show 128 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_using [this])]

theorem request_val {n L c : Nat} (hn : n < 2 ^ 32) (hL : L < 2 ^ 32) (hc : c ≤ n) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 L - (BitVec.ofNat 64 n - BitVec.ofNat 64 (n - c)) =
      BitVec.ofNat 64 (n + L - c) := by
  rw [sub_used (by omega_using [hn]) hc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [hn]), Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega_using [hL]),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hn, hc]), Nat.mod_eq_of_lt (show n + L < 2 ^ 64 by omega_using [hn, hL]),
    Nat.mod_eq_of_lt (show n + L - c < 2 ^ 64 by omega_using [hn, hL]),
    show 2 ^ 64 - c + (n + L) = (n + L - c) + 2 ^ 64 by omega_using [hn, hc], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hn, hL])]

theorem reject_ok {P : Nat} {s t₀ u : State} (hp : RPre P s) (hb : Before s t₀)
    (hI : At s t₀ (stackArg s 2).toNat u) (hc : (kept s (stackArg s 2).toNat).length < psLen s) :
    WP isa reject u fun x => Fin P s x ∧ post s x := by
  have hP := hp.ps
  obtain hQ := Q_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hrl := hp.randLen
  obtain hlen := (stackArg s 2).isLt
  have hfu := hI.fr
  obtain keepS : Keeps [.x9, .x11, .x12, .x14, .x15, .x16, .x17] s u :=
    (hb.keep.trans hI.keep).mono (by simp)
  obtain hx15 : u.gpr .x15 = BitVec.ofNat 64 (psLen s) := (hI.keep .x15 (by decide)).trans hb.x15
  -- `out` zeroed
  refine WP.seq (WP.seq (WP.mono (zpre_ok u) fun w₁ ⟨S₁, m₁, h₉, h₁₀, h₁₃⟩ => ?_))
  obtain hR₁ : ∃ R ∈ w₁.wr, Region.Sub ⟨s.gpr .x0, kOf s⟩ R :=
    ⟨outR s, by rw [S₁.wr, hfu.wr, entered_wr, hp.hwr]; simp, by
      rw [outR, kOf, hp.hsi]; exact fun _ h => h⟩
  refine WP.mono (zloop_ok (rz := .x13) (rp := .x9) (rc := .x10) (by decide) (by decide) (by decide)
    (p := s.gpr .x0) (n := kOf s) (by unfold kOf; omega_using [hk1]) (by unfold kOf; omega_using []) hR₁ h₁₃
    (by rw [h₉]; exact keepS _ (by decide))
    (by rw [h₁₀, keepS _ (by decide)]; exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm))
    fun u₁ Z₁ => ?_
  -- `PS`'s area wiped
  have hx16 := hI.x16
  generalize hcdef : (kept s (stackArg s 2).toNat).length = c at hc hx16
  obtain hu₁x : ∀ r, r ∉ [Reg.x9, .x10, .x13] → u₁.gpr r = u.gpr r := fun r hr =>
    (Z₁.keep r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h]))).trans
      (S₁.keep r hr)
  refine WP.seq (WP.seq (WP.mono (wd_ok u₁) fun w₂ ⟨S₂, m₂, h₁₀', h₉'⟩ => ?_))
  obtain hsp₂ : w₂.sp = Q s := S₂.sp.trans (Z₁.sp.trans (S₁.sp.trans hfu.sp))
  obtain hwr₂ : w₂.wr = (entered s).wr := S₂.wr.trans (Z₁.wr.trans (S₁.wr.trans hfu.wr))
  obtain hR₂ : ∃ R ∈ w₂.wr, Region.Sub (psR s) R :=
    ⟨⟨Q s, frameBytes⟩, by rw [hwr₂, entered_wr]; simp, Offset.sub_base _ (by unfold oBuf frameBytes; omega_using [])⟩
  refine WP.mono (zloop_ok (rz := .x13) (rp := .x9) (rc := .x10) (by decide) (by decide) (by decide)
    (p := off (Q s) oBuf) (n := 1024) (by decide) (by decide) hR₂
    (by rw [S₂.keep _ (by decide), Z₁.keep _ (by decide)]; exact h₁₃)
    (by rw [h₉', Z₁.sp, S₁.sp, hfu.sp]) h₁₀') fun u₂ Z₂ => ?_
  obtain S₂' : Same [.x9, .x10] w₂ u₂ := ⟨Z₂.rd, Z₂.wr, Z₂.sp, Z₂.v, Z₂.keep⟩
  have F₂ : Frame [psR s] w₂.mem u₂.mem := Z₂.fr
  obtain hsp₃ : u₂.sp = Q s := S₂'.sp.trans hsp₂
  obtain hwr₃ : u₂.wr = (entered s).wr := S₂'.wr.trans hwr₂
  obtain hrd₃ : u₂.rd = s.rd := S₂'.rd.trans (S₂.rd.trans (Z₁.rd.trans (S₁.rd.trans hfu.rd)))
  obtain hv₃ : u₂.v = s.v := S₂'.v.trans (S₂.v.trans (Z₁.v.trans (S₁.v.trans hfu.v)))
  obtain psS : Region.Sub (psR s) ⟨Q s, 1104⟩ := Offset.sub_base (Q s) (d := oBuf) (n := 1024) (k := 1104)
    (by unfold oBuf; omega_using [])
  obtain oS : Region.Sub ⟨s.gpr .x0, kOf s⟩ (outR s) := by rw [outR, kOf, hp.hsi]; exact fun _ h => h
  -- memory: changed in the frame and `out`
  obtain F₀ : Frame [⟨Q s, 1104⟩, outR s] s.mem u₂.mem := by
    obtain A : Frame [⟨Q s, 1104⟩, outR s] s.mem u.mem := hfu.fr.mono (by simp)
    obtain B : Frame [⟨Q s, 1104⟩, outR s] u.mem u₁.mem := by
      rw [← m₁]; exact Z₁.fr.sub fun r hr => ⟨outR s, by simp, by rw [List.mem_singleton.mp hr]; exact oS⟩
    obtain C : Frame [⟨Q s, 1104⟩, outR s] u₁.mem u₂.mem := by
      rw [← m₂]; exact F₂.sub fun r hr => ⟨⟨Q s, 1104⟩, by simp, by rw [List.mem_singleton.mp hr]; exact psS⟩
    exact A.trans (B.trans C)
  obtain F₁ : Frame [outR s, psR s] u.mem u₂.mem := by
    obtain B : Frame [outR s, psR s] u.mem u₁.mem := by
      rw [← m₁]; exact Z₁.fr.sub fun r hr => ⟨outR s, by simp, by rw [List.mem_singleton.mp hr]; exact oS⟩
    obtain C : Frame [outR s, psR s] u₁.mem u₂.mem := by rw [← m₂]; exact F₂.mono (by simp)
    exact B.trans C
  obtain keep₂ : Keeps [.x9, .x10, .x13] u u₂ :=
    ((S₁.keep.trans (Z₁.keep.trans (S₂.keep.trans S₂'.keep)))).mono (by simp)
  obtain g₂ : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] → u₂.gpr r = s.gpr r :=
    fun r hr => ((keepS.trans keep₂).mono (by decide)) r hr
  obtain hx2 : u₂.gpr .x2 = s.gpr .x2 := g₂ _ (by decide)
  obtain ha : InRegions (u₂.rd ++ u₂.wr) (u₂.sp + BitVec.ofNat 64 1120) 8 := by
    rw [hsp₃, hrd₃, hwr₃, ← entered_rd]; exact args_in hp (j := 2) (by decide)
  obtain hm : u₂.mem.read (u₂.sp + BitVec.ofNat 64 1120) 8 = stackArg s 2 := by
    rw [hsp₃]; exact arg_mem hp F₀ (j := 2) (by decide)
  obtain htw : tapeR s ∈ u₂.wr := by rw [hwr₃, entered_wr, hp.hwr]; simp
  obtain t0 : InRegions u₂.wr (u₂.gpr .x2 + 0#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  obtain t8 : InRegions u₂.wr (u₂.gpr .x2 + 8#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  obtain hx15₂ : u₂.gpr .x15 = BitVec.ofNat 64 (psLen s) := by rw [keep₂ _ (by decide)]; exact hx15
  obtain hx16₂ : u₂.gpr .x16 = BitVec.ofNat 64 (psLen s - c) := by rw [keep₂ _ (by decide)]; exact hx16
  refine WP.mono (outcome_ok ha hm t0 t8) fun x ⟨Sx, mx, hx0⟩ => ?_
  rw [hx15₂, hx16₂, hx2, psLen_add hp] at mx
  rw [hx15₂, psLen_add hp] at hx0
  -- what is common to both outcomes
  obtain hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all, hcdef]; exact hc
  obtain hL : stackArg s 2 = BitVec.ofNat 64 (stackArg s 2).toNat :=
    ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  obtain Fx : Frame [tapeR s] u₂.mem x.mem := by rw [mx]; exact frame_tape _ _ _
  obtain outZ : Spec.Rsa.bytesAt x.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0 := by
    obtain C : Frame [psR s, tapeR s] u₁.mem u₂.mem := by rw [← m₂]; exact F₂.mono (by simp)
    obtain D : Frame [psR s, tapeR s] u₂.mem x.mem := Fx.mono (by simp)
    rw [bytes_frame (C.trans D) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fun y h₁ h₂ => hp.dKo y (psR_sub s y h₂) (oS y h₁)
      · exact (hp.dOt.sub_left oS)) (by unfold kOf; omega_using []), zloop_bytes Z₁]
  obtain fin : Fin P s x := by
    obtain k : Keeps [Reg.x0, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s x :=
      ((show Keeps _ s u₂ from g₂).trans Sx.keep).mono (by decide)
    obtain Fs : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem x.mem := by
      obtain Fx' : Frame [stkR P s, tapeR s, outR s, scrR s] u₂.mem x.mem := Fx.mono (by simp)
      refine (F₀.sub fun r hr => ?_).trans Fx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨stkR P s, by simp, ?_⟩
        have := frame_sub (P := P) s (d := 0) (n := 1104) (by decide)
        rwa [off, add_zero'] at this
      · exact ⟨outR s, by simp, fun _ h => h⟩
    refine ⟨Sx.sp.trans hsp₃, Sx.rd.trans hrd₃, Sx.wr.trans hwr₃, Fs, ?_,
      fun r hr h30 => k r (by revert hr h30; revert r; decide), fun r _ => by rw [Sx.v, hv₃]⟩
    obtain hd : ∀ r ∈ [outR s, psR s], Region.Disjoint ⟨off (Q s) 1088, 8⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frame_sub s (by decide))
      · exact Offset.disjoint _ (.inr (by unfold oBuf; omega_using [])) (by omega_using []) (by unfold oBuf; omega_using [])
    obtain hdt : ∀ r ∈ [tapeR s], Region.Disjoint ⟨off (Q s) 1088, 8⟩ r := fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.dKt.sub_left (frame_sub s (by decide))
    rw [Fx.readW (Region.contains_self _ _) hdt (by decide), F₁.readW (Region.contains_self _ _) hd (by decide)]
    exact hfu.lr
  refine ⟨fin, ?_⟩
  have hcap : Spec.RsaPkcs1Enc.padEntropy (psLen s) = psLen s + 128 := rfl
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  by_cases hge : psLen s + 128 ≤ (stackArg s 2).toNat
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted hnz (by rw [randB_length, hcap]; exact hge)
    rw [ho, hu, randB_length]
    simp only [hge, ite_true] at mx hx0
    refine ⟨⟨0, ?_, ?_, rfl⟩, ?_, outZ⟩
    · rw [mx, rd_tape0]; exact hL
    · rw [mx, rd_tape1]; rfl
    · rw [hx0]; rfl
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length, hcap]; omega_using [hge])
    rw [ho, hu]
    simp only [hge, ite_false] at mx hx0
    obtain hv : BitVec.ofNat 64 (psLen s) + stackArg s 2 - (BitVec.ofNat 64 (psLen s) - BitVec.ofNat 64 (psLen s - c)) =
        BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c) := by
      have := request_val (n := psLen s) (L := (stackArg s 2).toNat) (c := c) (by omega_using [hP]) (by omega_using [hP, hrl]) (by omega_using [hc])
      rw [← hL] at this
      exact this
    obtain h11 : BitVec.ofNat 64 (psLen s) + 128#64 = BitVec.ofNat 64 (psLen s + 128) := by
      apply BitVec.eq_of_toNat_eq; rw [psLen_add hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP])]
    obtain hv' : (BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c)).toNat = psLen s + (stackArg s 2).toNat - c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP, hrl])]
    rw [hv, hv', h11] at mx
    refine ⟨⟨min (psLen s + (stackArg s 2).toNat - c) (psLen s + 128), ?_, ?_, ?_⟩, ?_, outZ⟩
    · rw [mx, rd_tape0]; rfl
    · rw [mx, rd_tape1]
      by_cases hm : psLen s + (stackArg s 2).toNat - c ≤ psLen s + 128
      · simp only [hm, ite_true, Nat.min_eq_left hm]
      · simp only [hm, ite_false, Nat.min_eq_right (show psLen s + 128 ≤ psLen s + (stackArg s 2).toNat - c by omega_using [hm])]
    · rw [randB_length, hcap]
      exact ⟨by simp only [Nat.lt_min]; omega_using [hc, hge], Nat.min_le_right _ _⟩
    · rw [hx0]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: correctness

With `PS` full, the call and its tail (`accept_ok`); the frames' body
(`body_ok`); and the function (`code_ok`): the registers the ABI keeps and
`post`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

/-- `PS` full after `i` octets: the state before the call's arguments. -/
theorem ready_of {P : Nat} {s t₀ u : State} (hp : RPre P s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hf : (kept s i).length = psLen s) : Ready s u i (kept s i) := by
  have hP := hp.ps
  refine ⟨hI.fr, (hb.keep.trans hI.keep).mono (by decide), hI.x12,
    (hI.keep .x15 (by decide)).trans hb.x15, hf, ?_, hI.hi⟩
  rw [← hf]
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range]
  rw [show off (Q s) oBuf + BitVec.ofNat 64 j = off (Q s) (oBuf + j) from off_off _ _ _, hI.buf j h₁]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

theorem accept_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s t₀ u : State} (hp : RPre c.stack s) (hb : Before s t₀) {i : Nat}
    (hI : At s t₀ i u) (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa (accept (encName c) (encCode c)) u fun x => Fin c.stack s x ∧ post s x := by
  have hr := ready_of hp hb hI hf
  refine WP.seq (WP.mono (args_ok hp hr) fun w ha => ?_)
  refine WP.seq (WP.mono (call_ok c hsat hp ha) fun u' hac => ?_)
  refine WP.mono (accTail_ok hp hac) fun x ⟨hfin, ht0, ht1, hres⟩ => ⟨hfin, ?_⟩
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  rw [ho, hu]
  exact ⟨⟨0, ht0, ht1, rfl⟩, hres⟩

theorem body_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s : State} (hp : RPre c.stack s) :
    WP isa (body (encName c) (encCode c)) (entered s) fun x => Fin c.stack s x ∧ post s x := by
  have hP := hp.ps
  refine WP.seq (WP.mono (setup_ok hp) fun t₀ hb => ?_)
  refine WP.seq (WP.mono (scan_ok hp hb) fun u ⟨i, hI, hd⟩ => ?_)
  have hc := hI.hc
  rcases hd with ⟨hf, hpre⟩ | ⟨rfl, hlt⟩
  · refine WP.ite true (by rw [eval_zero, hI.x16, hf, Nat.sub_self]; rfl) (fun _ => accept_ok c hsat hp hb hI hf hpre)
      (fun h => absurd h (by decide))
  · have hne : (BitVec.ofNat 64 (psLen s - (kept s (stackArg s 2).toNat).length) == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP])] at this
      simp at this; omega_using [hlt, this]
    refine WP.ite false (by rw [eval_zero, hI.x16, hne]) (fun h => absurd h (by decide))
      (fun _ => reject_ok hp hb hI hlt)

theorem popped_gpr (s : State) (r : Reg) :
    (popped .x30 s).gpr r = if r = .x30 then s.mem.read s.sp 8 else s.gpr r := by
  show (s.write .x .x30 _).gpr r = _
  rw [RegUpd.gpr_write, BitVec.setWidth_eq]

/-- `post` reads the memory only in the output and the tape's two words. -/
theorem post_congr {s x y : State}
    (hb : Spec.Rsa.bytesAt y.mem (s.gpr .x0) (kOf s) = Spec.Rsa.bytesAt x.mem (s.gpr .x0) (kOf s))
    (ht : y.mem.readW (s.gpr .x2) 64 = x.mem.readW (s.gpr .x2) 64)
    (ht8 : y.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = x.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64)
    (h0 : y.gpr .x0 = x.gpr .x0) (h : post s x) : post s y := by
  simp only [post] at h ⊢
  obtain ⟨⟨req, h1, h2, h3⟩, h4⟩ := h
  refine ⟨⟨req, ht.trans h1, ht8.trans h2, h3⟩, ?_⟩
  revert h4
  generalize (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).outcome = o
  cases o <;> simp only [h0, hb, imp_self]
  intro h4 hp
  have h5 := h4 hp
  revert h5
  generalize Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) _ = C
  cases C <;> simp only [Spec.RsaPkcs1Enc.writtenRandom, hb, imp_self]

theorem popped_mem' (x : State) : (popped .x30 x).mem = x.mem := rfl

theorem freed_mem' (b : Nat) (x : State) : (freed b x).mem = x.mem := rfl

theorem rd8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem code_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s : State} (hp : RPre c.stack s) :
    WP isa (code (encName c) (encCode c)) s fun s' => abiPreserved s s' ∧ post s s' := by
  have hQ := Q_toNat hp
  refine WP.frameAlloc (by omega_using [hQ]) (by decide) ?_ ?_
  · show 1088 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_using [hQ])]
    show 1088 ≤ s.sp.toNat - 16
    omega_using [hQ]
  · show WP isa (body (encName c) (encCode c)) (entered s) _
    refine WP.mono (body_ok c hsat hp) fun x ⟨hx, hpo⟩ mm uu fl => ?_
    have hsp' : (freed frameBytes x).sp = off (Q s) 1088 := by
      show x.sp + BitVec.ofNat 64 1088 = _; rw [hx.sp]
    -- The output and the tape lie apart from the stack, whose frames' bytes are lost.
    obtain hS : Region.Sub (below s.sp (1088 + 16)) (stkR c.stack s) :=
      Offset.sub_below s.sp (a := 1104) (n := 1104) (b := c.stack + 2191 + 1) (m := c.stack + 2191 + 1)
        (by omega_arith) (by omega_arith)
    obtain hT : ∀ R ∈ [below s.sp (1088 + 16)], (tapeR s).Disjoint R := fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact hp.dKt.symm.sub_right hS
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => hx.vs r hr⟩, ?_⟩
    · show (popped .x30 (freed frameBytes x)).gpr r = s.gpr r
      rw [popped_gpr]
      by_cases h30 : r = .x30
      · subst h30
        simp only [ite_true]
        rw [hsp', freed_mem', rd8]
        exact hx.lr
      · simp only [h30, ite_false]; exact hx.cs r hr h30
    · show x.sp + BitVec.ofNat 64 1088 + 16 = s.sp
      rw [hx.sp, BitVec.add_assoc]
      exact Q_sp s
    · refine post_congr (x := x) ?_ ?_ ?_ ?_ hpo
      · exact List.map_congr_left fun i hi => lost_byte (R := outR s) fl (hp.dKo.symm.sub_right hS)
          (show i < (s.gpr .x1).toNat by rw [hp.hsi]; exact List.mem_range.mp hi)
      · exact fl.readW (r := tapeR s)
          (by simp only [tapeR, Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide) hT (by decide)
      · exact fl.readW (r := tapeR s) (Offset.contains_base (s.gpr .x2) (d := 8) (n := 64 / 8) (k := 16)
          (by decide) (by decide)) hT (by decide)
      · show (popped .x30 (freed frameBytes x)).gpr .x0 = _
        rw [popped_gpr, ite_eq_right_of_eq_false _ _ (by decide)]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the contract

`contract` is the shared contract's precondition, `post`, and its public data
by name (`pub`); it implies the shared contract (`implies`), which a state
with an empty message and tape meets (`sat`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64

/-- The trace of drawing `PS`. -/
abbrev trace (s : State) : List Nat := (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).trace

/-- The public data, by name. -/
def pub (a s : State) : Prop :=
  a.sp = s.sp ∧ (∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], a.gpr r = s.gpr r) ∧
    (∀ j < 7, stackArg a j = stackArg s j) ∧ nB a = nB s ∧ eB a = eB s ∧ preW a = preW s ∧ trace a = trace s

def contract (P : Nat) : Contract isa where
  pre := (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)).pre
  post := post
  pub := pub

theorem wordsAt_two (m : Mem) (p : Addr) :
    Spec.Rsa.wordsAt m p 2 = [m.readW p 64, m.readW (p + BitVec.ofNat 64 8) 64] := by
  simp [Spec.Rsa.wordsAt, List.range_succ]

theorem stackArgs_seven (s : State) :
    List.map (stackArg s) (List.range 7) =
      [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-- A state meeting the precondition: a 512-bit key, an empty message and tape. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 64 | .x5 => 0x4000 | .x6 => 1
    | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10009 then 0x60
    else bif Nat.beq a.toNat 0x1001A then 0x02 else bif Nat.beq a.toNat 0x10020 then 0x70
    else bif Nat.beq a.toNat 0x10029 then 0x70 else bif Nat.beq a.toNat 0x10030 then 0x10 else 0
  rd := [⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 128⟩, ⟨0x10000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 16⟩, ⟨0x20000, 896⟩]

/-- It meets the shared contract with 16 bytes of stack for the callee's call. -/
theorem sat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack 16)).pre s := by
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
    AArch64.abi, AArch64.argRegs, stackArgs_seven, List.append_eq, rndStack] [satState, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using satState

theorem implies (P : Nat) (hsat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)).pre s) :
    (contract P).Implies (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)) where
  pre := fun _ h => h
  post := by
    intro s u _ h
    sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      AArch64.abi, AArch64.argRegs, stackArgs_seven, List.append_eq]
    obtain ⟨⟨req, h0, h1, hr⟩, hm⟩ := h
    exact ⟨⟨req, by rw [wordsAt_two, h0, h1]; rfl, hr⟩, hm⟩
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      AArch64.abi, AArch64.argRegs, stackArgs_seven, List.append_eq, List.getD_cons_succ,
      List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6⟩ := h
    have hl' : (List.map BitVec.toNat (nB s₁ ++ eB s₁) ++ List.map BitVec.toNat (preW s₁)) ++ trace s₁ =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂) ++ List.map BitVec.toNat (preW s₂)) ++ trace s₂ := hl
    have hl1 : (List.map BitVec.toNat (nB s₁ ++ eB s₁)).length =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂)).length := by
      simp [nB, eB, kOf, Spec.Rsa.bytesAt, h4, h6]
    have hl2 : (List.map BitVec.toNat (preW s₁)).length = (List.map BitVec.toNat (preW s₂)).length := by
      simp [preW, Spec.Rsa.wordsAt, a6]
    obtain ⟨h12, h3'⟩ := List.append_inj hl' (by simp only [List.length_append, hl1, hl2])
    obtain ⟨h1', h2'⟩ := List.append_inj h12 hl1
    have inj : ∀ {w : Nat} {l₁ l₂ : List (BitVec w)}, l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ :=
      fun h => (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
    have hne := inj h1'
    obtain ⟨hn, he⟩ := List.append_inj hne (by simp [nB, kOf, Spec.Rsa.bytesAt, h4])
    refine ⟨hsp, ?_, fun j hj => ?_, hn, he, inj h2', h3'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> with_reducible assumption
    · match j, hj with
      | 0, _ => exact a0 | 1, _ => exact a1 | 2, _ => exact a2 | 3, _ => exact a3 | 4, _ => exact a4
      | 5, _ => exact a5 | 6, _ => exact a6
  sat := hsat

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the scan in constant time

Two runs from entry states that agree with an anchor `a` on the public data
(`PR`) read the same octets of the tape and keep as many of them: the scan
reads `scanLen` octets of `a`'s tape in both (`N`), each read octet is zero in
one run exactly when it is in the other, and so is each count of kept octets
(`Proof/RsaPkcs1Enc/RandomCT.lean`). So the branch on each octet, the address
of each load and store and the end of the loop are the same in both runs;
the taint analysis checks the rest, with these registers public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.Bignum.AArch64 (Two two_post two_taint two_piece two_ite two_loop)

variable {P : Nat}

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (P : Nat) (a s : State) : Prop := (contract P).pre s ∧ pub a s

theorem PR.pre {a s : State} (h : PR P a s) : RPre P s := pre_of h.1

theorem PR.gprEq {a s : State} (h : PR P a s) {r : Reg}
    (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]) : s.gpr r = a.gpr r := (h.2.2.1 r hr).symm

theorem PR.spEq {a s : State} (h : PR P a s) : s.sp = a.sp := h.2.1.symm

theorem PR.argEq {a s : State} (h : PR P a s) {j : Nat} (hj : j < 7) : stackArg s j = stackArg a j :=
  (h.2.2.2.1 j hj).symm

theorem PR.QEq {a s : State} (h : PR P a s) : Q s = Q a := by
  show s.sp - _ = a.sp - _; rw [h.spEq]

theorem PR.psEq {a s : State} (h : PR P a s) : psLen s = psLen a := by
  unfold psLen kOf; rw [h.gprEq (r := .x4) (by decide), h.argEq (j := 0) (by decide)]

theorem PR.lenEq {a s : State} (h : PR P a s) : (stackArg s 2).toNat = (stackArg a 2).toNat := by
  rw [h.argEq (by decide)]

theorem PR.traceEq {a s : State} (h : PR P a s) :
    (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB s)).trace =
      (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB a)).trace := by
  have := h.2.2.2.2.2.2.2
  simp only [trace, h.psEq] at this
  exact this.symm

/-- The octets the scan reads, the anchor's. -/
abbrev N (a : State) : Nat := VG.Proof.RsaPkcs1Enc.scanLen (psLen a) (randB a)

theorem PR.scanEq {a s : State} (h : PR P a s) :
    VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := by
  rw [h.psEq]; exact VG.Proof.RsaPkcs1Enc.scanLen_eq h.traceEq

theorem PR.keptEq {a s : State} (h : PR P a s) {j : Nat} (hj : j ≤ N a) :
    (kept s j).length = (kept a j).length :=
  VG.Proof.RsaPkcs1Enc.nz_take_length_eq h.traceEq j (by rw [← h.psEq, h.scanEq]; exact hj)

theorem PR.zeroIff {a s : State} (h : PR P a s) {j : Nat} (hj : j < N a) :
    (randB s).getD j 0 = 0 ↔ (randB a).getD j 0 = 0 :=
  VG.Proof.RsaPkcs1Enc.zero_iff h.traceEq (by rw [← h.psEq, h.scanEq]; exact hj)

/-! ## The loop -/

/-- Before octet `j` of the scan. -/
def LoopPt (P : Nat) (a : State) (j : Nat) (u : State) : Prop :=
  ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ j u ∧ j < (stackArg s 2).toNat ∧ (kept s j).length < psLen s

/-- After the load of octet `j`. -/
def LoadPtA (P : Nat) (p : State × Nat) (v : State) : Prop :=
  ∃ s t₀ u, PR P p.1 s ∧ Before s t₀ ∧ At s t₀ p.2 u ∧ LoadStep u v ∧ p.2 < (stackArg s 2).toNat ∧
    (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After octet `j`, before `x9`. -/
def NextPt (P : Nat) (p : State × Nat) (w : State) : Prop :=
  ∃ s t₀, PR P p.1 s ∧ Before s t₀ ∧ At s t₀ (p.2 + 1) w ∧ p.2 < N p.1

theorem x11_eq {a s t₀ u : State} (S : PR P a s) {j : Nat} (I : At s t₀ j u) :
    u.gpr .x11 = stackArg a 1 + BitVec.ofNat 64 j := by
  rw [I.x11, S.argEq (by decide)]

theorem load_two :
    RelCT isa (Two fun (p : State × Nat) s => p.2 < N p.1 ∧ LoopPt P p.1 p.2 s) (.block load) (Two (LoadPtA P)) := by
  refine two_piece [.x11] (fun p u₁ u₂ ⟨_, s₁, t₁, S₁, _, I₁, _⟩ ⟨_, s₂, t₂, S₂, _, I₂, _⟩ r hr => ?_)
    (by taint_decide) fun p u ⟨hN, s, t₀, S, B, I, hi, hc⟩ => ?_
  · rw [List.mem_singleton.mp hr, x11_eq S₁ I₁, x11_eq S₂ I₂]
  · have hwR := S.pre.wR
    have hr : InRegions (u.rd ++ u.wr) (u.gpr .x11 + BitVec.ofNat 64 0) 1 :=
      ⟨randR s, by rw [I.fr.rd, S.pre.hrd]; simp, by
        rw [add_zero', I.x11]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
    exact WP.mono (load_ok hr) fun v h => ⟨s, t₀, u, S, B, I, h, hi, hc, hN⟩

theorem x14_eq {a s t₀ u : State} (S : PR P a s) {j : Nat} (hj : j ≤ N a) (I : At s t₀ j u) :
    u.gpr .x14 = off (Q a) (oBuf + (kept a j).length) := by
  rw [I.x14, S.QEq, S.keptEq hj]

theorem x17_eq {a s t₀ u v : State} (S : PR P a s) {j : Nat} (I : At s t₀ j u) (L : LoadStep u v)
    (hi : j < (stackArg s 2).toNat) : v.gpr .x17 = ((randB s).getD j 0).setWidth 64 := by
  rw [L.x17, I.x11, rand_byte' S.pre I.fr hi]

theorem branch_two :
    RelCT isa (Two (LoadPtA P)) (.ite (.zero .x .x17) (.block []) (.block keep)) (Two (NextPt P)) := by
  refine two_post (two_ite (fun p v₁ v₂ ⟨s₁, t₁, u₁, S₁, _, I₁, L₁, hi₁, _, hN⟩
      ⟨s₂, t₂, u₂, S₂, _, I₂, L₂, hi₂, _, _⟩ => ?_) ?_ ?_) ?_
  · rw [eval_zero, eval_zero, x17_eq S₁ I₁ L₁ hi₁, x17_eq S₂ I₂ L₂ hi₂, zero_byte, zero_byte]
    rw [decide_eq_decide.mpr ((S₁.zeroIff hN).trans (S₂.zeroIff hN).symm)]
  · exact two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  · refine two_taint [.x14] (fun p v₁ v₂ ⟨⟨s₁, t₁, u₁, S₁, _, I₁, L₁, _, _, hN⟩, _⟩
        ⟨⟨s₂, t₂, u₂, S₂, _, I₂, L₂, _, _, _⟩, _⟩ r hr => ?_) (by taint_decide)
    rw [List.mem_singleton.mp hr, L₁.other _ (by decide) (by decide) (by decide),
      L₂.other _ (by decide) (by decide) (by decide), x14_eq S₁ (Nat.le_of_lt hN) I₁,
      x14_eq S₂ (Nat.le_of_lt hN) I₂]
  · intro p v ⟨s, t₀, u, S, B, I, L, hi, hc, hN⟩
    exact WP.mono (branch_ok S.pre I L hi hc) fun w h => ⟨s, t₀, S, B, h, hN⟩

theorem mul_two : RelCT isa (Two (NextPt P)) (.block [.mul .x .x9 .x12 .x16]) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

theorem step_two :
    RelCT isa (Two fun (p : State × Nat) s => p.2 < N p.1 ∧ LoopPt P p.1 p.2 s) step fun _ _ => True :=
  RelCT.seq load_two (RelCT.seq branch_two mul_two)

/-- At the end of the scan: all `N a` octets read. -/
def ScanDone (P : Nat) (a u : State) : Prop := ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ (N a) u

theorem loop_two :
    RelCT isa (Two fun a s => 0 < N a ∧ LoopPt P a 0 s) (.loop step (.nonzero .x .x9)) (Two (ScanDone P)) := by
  refine two_loop (Φ := LoopPt P) N step_two ?_
  intro a j u hj ⟨s, t₀, S, B, I, hi, hc⟩
  have hs : VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := S.scanEq
  refine WP.mono (step_ok S.pre I hi hc) fun u' ⟨I', hz⟩ => ?_
  have hst : ((kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 2).toNat) ↔ N a = j + 1 := by
    have := VG.Proof.RsaPkcs1Enc.stop_iff (n := psLen s) (r := randB s) (j := j) (by rw [hs]; exact hj) hc
    rw [randB_length, hs] at this; exact this
  have hk := I'.hc
  refine ⟨?_, fun hlt => ⟨s, t₀, S, B, I', ?_, ?_⟩, fun he => ⟨s, t₀, S, B, he ▸ I'⟩⟩
  · rw [Bytes.eval_nonzero, hz]
    by_cases h : (kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 2).toNat
    · rw [decide_eq_false (not_not_intro h), decide_eq_false (by have := hst.mp h; omega_using [hst, h])]
    · rw [decide_eq_true h, decide_eq_true (by
        have : N a ≠ j + 1 := fun e => h (hst.mpr e)
        omega_using [hj, hst, h])]
  · have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
    rw [randB_length, hs] at this; omega_using [hi, hst, hlt]
  · by_cases hn : (kept s (j + 1)).length = psLen s
    · have := hst.mp (.inl hn); omega_using [hst, hk, hlt]
    · omega_using [hk, hn]

/-- Before the scan. -/
def ScanPt (P : Nat) (a t : State) : Prop := ∃ s, PR P a s ∧ Before s t

theorem scan_two : RelCT isa (Two (ScanPt P)) scan (Two (ScanDone P)) := by
  refine two_ite (fun a t₁ t₂ ⟨s₁, S₁, B₁⟩ ⟨s₂, S₂, B₂⟩ => by
    rw [Bytes.eval_nonzero, Bytes.eval_nonzero, B₁.x12, B₂.x12, S₁.argEq (by decide), S₂.argEq (by decide)])
    ?_ ?_
  · refine loop_two.mono (fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, B₁⟩, e₁⟩, ⟨⟨s₂, S₂, B₂⟩, _⟩, hsp⟩ => ?_) fun _ _ h => h
    have hl : stackArg s₁ 2 ≠ 0 := by
      intro h0; rw [Bytes.eval_nonzero, B₁.x12, h0] at e₁; cases e₁
    have hl' : 0 < (stackArg s₁ 2).toNat := by
      rcases Nat.eq_zero_or_pos (stackArg s₁ 2).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
      · exact h
    have hP₁ := S₁.pre.ps
    have hP₂ := S₂.pre.ps
    have hN : 0 < N a := by
      rw [← S₁.scanEq]
      exact VG.Proof.RsaPkcs1Enc.lt_scanLen (i := 0)
        (show (kept s₁ 0).length < psLen s₁ by rw [kept_zero, List.length_nil]; omega_using [hP₁])
        (by rw [randB_length]; exact hl')
    refine ⟨a, ⟨hN, s₁, t₁, S₁, B₁, at_zero S₁.pre B₁, hl', by rw [kept_zero, List.length_nil]; omega_using [hP₁]⟩,
      ⟨hN, s₂, t₂, S₂, B₂, at_zero S₂.pre B₂, by rw [S₂.lenEq, ← S₁.lenEq]; exact hl',
        by rw [kept_zero, List.length_nil]; omega_using [hP₂]⟩, hsp⟩
  · refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
      fun a t ⟨⟨s, S, B⟩, e⟩ => WP.block_nil ⟨s, t, S, B, ?_⟩
    have h0 : stackArg s 2 = 0 := by
      rw [Bytes.eval_nonzero, B.x12] at e
      by_cases h : stackArg s 2 = 0
      · exact h
      · rw [bne_iff_ne.mpr h] at e; cases e
    have : N a = 0 := by
      rw [← S.scanEq]
      have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
      rw [randB_length, h0] at this
      simpa using this
    rw [this]; exact at_zero S.pre B

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: constant time, and `Verified`

After the scan (`RndCTScan`), both runs have kept as many octets, so they
take the same branch on whether `PS` is full. With `PS` full: the call's
arguments by the taint analysis, with `tape` public; the call of
`vg_rsa_pkcs1_encrypt_precomputed`, constant time for its contract, whose
public data both runs share; and the status and the wipe, whose length is a
constant. Otherwise `reject`, which branches only on `n_len` and constants,
by the taint analysis with `out`, `tape` and `n_len` public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.Bignum.AArch64 (Two two_post two_taint two_piece two_ite)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

variable {P : Nat}

/-- On entry to the frames' body. -/
def AllocPt (P : Nat) (a t : State) : Prop := ∃ s, PR P a s ∧ t = entered s

theorem setup_two : RelCT isa (Two (AllocPt P)) (.block setup) (Two (ScanPt P)) :=
  two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
    fun a t ⟨s, S, e⟩ => by subst e; exact WP.mono (setup_ok S.pre) fun u B => ⟨s, S, B⟩

/-- The registers both runs share, from the entry. -/
theorem keepS {s t₀ u : State} (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u) {r : Reg}
    (hr : r ∉ [Reg.x9, .x11, .x12, .x14, .x15, .x16, .x17]) : u.gpr r = s.gpr r :=
  ((hb.keep.trans hI.keep).mono (by decide)) r hr

/-! ## `PS` full -/

def AccPt (P : Nat) (a u : State) : Prop :=
  ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ (N a) u ∧ (kept s (N a)).length = psLen s

def ArgsPt (P : Nat) (a w : State) : Prop := ∃ s, PR P a s ∧ Args s w (N a) (kept s (N a))

def AfterPt (P : Nat) (a u : State) : Prop := ∃ s, PR P a s ∧ AfterCall P s u (N a) (kept s (N a))

theorem args_two : RelCT isa (Two (AccPt P)) (.block callArgs) (Two (ArgsPt P)) :=
  two_piece [.x2] (fun a u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => by
      rw [List.mem_singleton.mp hr, keepS B₁ I₁ (by decide), keepS B₂ I₂ (by decide),
        S₁.gprEq (by decide), S₂.gprEq (by decide)]) (by taint_decide)
    fun a u ⟨s, t₀, S, B, I, hf⟩ => WP.mono (args_ok S.pre (ready_of S.pre B I hf)) fun w h => ⟨s, S, h⟩

theorem entry_gpr (w : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (w.callEntry.withRegions rd wr).gpr r = w.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem call_ct (c : PdChecked) :
    RelCT isa (Two (ArgsPt c.stack)) (.call (encName c) (encCode c)) fun _ _ => True := by
  refine RelCT.callEx (k := Enc.Pc.contract c.stack)
    (fun _ h => by obtain ⟨t, s', he, hq⟩ := Enc.Pc.code_ok c h; exact ⟨t, s', he, hq⟩)
    (Enc.Pc.code_constantTime c) fun w₁ w₂ ⟨a, ⟨s₁, S₁, A₁⟩, ⟨s₂, S₂, A₂⟩, hsp⟩ => ?_
  obtain ⟨c₁, w₁'⟩ := call_covers S₁.pre A₁
  obtain ⟨c₂, w₂'⟩ := call_covers S₂.pre A₂
  obtain ⟨n₁, e₁, -, q₁⟩ := args_read S₁.pre A₁
  obtain ⟨n₂, e₂, -, q₂⟩ := args_read S₂.pre A₂
  have g₁ : ∀ {r : Reg}, r ∉ linkRegs → _ := fun {r} h => entry_gpr w₁ (callRd s₁) (callWr s₁) (r := r) h
  have g₂ : ∀ {r : Reg}, r ∉ linkRegs → _ := fun {r} h => entry_gpr w₂ (callRd s₂) (callWr s₂) (r := r) h
  have ga : ∀ j < 6, stackArg (w₁.callEntry.withRegions (callRd s₁) (callWr s₁)) j =
      stackArg (w₂.callEntry.withRegions (callRd s₂) (callWr s₂)) j := fun j hj => by
    rw [stackArg_call A₁ _ _ hj, stackArg_call A₂ _ _ hj]
    match j, hj with
    | 0, _ => show off (Q s₁) oBuf = off (Q s₂) oBuf; rw [S₁.QEq, S₂.QEq]
    | 1, _ => show BitVec.ofNat 64 (psLen s₁) = BitVec.ofNat 64 (psLen s₂); rw [S₁.psEq, S₂.psEq]
    | 2, _ => show stackArg s₁ 3 = stackArg s₂ 3; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
    | 3, _ => show stackArg s₁ 4 = stackArg s₂ 4; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
    | 4, _ => show stackArg s₁ 5 = stackArg s₂ 5; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
    | 5, _ => show stackArg s₁ 6 = stackArg s₂ 6; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
  have rg : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s₁.gpr r = s₂.gpr r := fun r hr =>
    (S₁.gprEq hr).trans (S₂.gprEq hr).symm
  have hx' : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], r ∉ linkRegs := by decide
  have hx : ∀ {r : Reg}, r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] → r ∉ linkRegs := fun h => hx' _ h
  refine ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, call_pre S₁.pre A₁, call_pre S₂.pre A₂, ?_, c₁.append_left
    w₁'.right, w₁', c₂.append_left w₂'.right, w₂'⟩
  refine ⟨⟨by simp only [State.withRegions_sp, State.callEntry_sp, A₁.sp, A₂.sp, S₁.QEq, S₂.QEq], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide), ?_, ?_⟩,
    ga 4 (by decide), ga 5 (by decide), ?_⟩
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x0, A₂.x0]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x1, A₂.x1]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x2, A₂.x2]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x3, A₂.x3]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x4, A₂.x4]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x5, A₂.x5]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x6, A₂.x6]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x7, A₂.x7, S₁.argEq (by decide), S₂.argEq (by decide)]
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x2, A₂.x2, A₁.x3, A₂.x3,
      State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem, n₁, n₂,
      S₁.2.2.2.2.1.symm.trans S₂.2.2.2.2.1]
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x4, A₂.x4, A₁.x5, A₂.x5,
      State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem, e₁, e₂,
      S₁.2.2.2.2.2.1.symm.trans S₂.2.2.2.2.2.1]
  · rw [stackArg_call A₁ _ _ (j := 4) (by decide), stackArg_call A₂ _ _ (j := 4) (by decide),
      stackArg_call A₁ _ _ (j := 5) (by decide), stackArg_call A₂ _ _ (j := 5) (by decide),
      State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem]
    show Spec.Rsa.wordsAt w₁.mem (stackArg s₁ 5) (stackArg s₁ 6).toNat = Spec.Rsa.wordsAt w₂.mem (stackArg s₂ 5)
      (stackArg s₂ 6).toNat
    rw [q₁, q₂, S₁.2.2.2.2.2.2.1.symm.trans S₂.2.2.2.2.2.2.1]

theorem call_two (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    RelCT isa (Two (ArgsPt c.stack)) (.call (encName c) (encCode c)) (Two (AfterPt c.stack)) :=
  two_post (call_ct c) fun _ _ ⟨s, S, A⟩ => WP.mono (call_ok c hsat S.pre A) fun _ h => ⟨s, S, h⟩

theorem tail_two : RelCT isa (Two (AfterPt P)) (.seq (.block status) wipe) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

theorem accept_ct (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    RelCT isa (Two (AccPt c.stack)) (accept (encName c) (encCode c)) fun _ _ => True :=
  RelCT.seq args_two (RelCT.seq (call_two c hsat) tail_two)

/-! ## `PS` not full -/

def RejPt (P : Nat) (a u : State) : Prop := ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ (N a) u

theorem reject_ct : RelCT isa (Two (RejPt P)) reject fun _ _ => True :=
  two_taint [.x0, .x2, .x4] (fun a u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁⟩ ⟨s₂, t₂, S₂, B₂, I₂⟩ r hr => by
    rw [keepS B₁ I₁ (by revert hr; revert r; decide), keepS B₂ I₂ (by revert hr; revert r; decide),
      S₁.gprEq (by revert hr; revert r; decide), S₂.gprEq (by revert hr; revert r; decide)]) (by taint_decide)

/-! ## The body -/

theorem x16_eq {a s t₀ u : State} (S : PR P a s) (I : At s t₀ (N a) u) :
    u.gpr .x16 = BitVec.ofNat 64 (psLen a - (kept a (N a)).length) := by
  rw [I.x16, S.psEq, S.keptEq (Nat.le_refl _)]

theorem body_ct (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    RelCT isa (Two (AllocPt c.stack)) (body (encName c) (encCode c)) fun _ _ => True := by
  refine RelCT.seq setup_two (RelCT.seq scan_two (two_ite
    (fun a w₁ w₂ ⟨s₁, t₁, S₁, _, I₁⟩ ⟨s₂, t₂, S₂, _, I₂⟩ => by
      rw [eval_zero, eval_zero, x16_eq S₁ I₁, x16_eq S₂ I₂])
    ((accept_ct c hsat).mono (fun w₁ w₂ ⟨a, ⟨⟨s₁, t₁, S₁, B₁, I₁⟩, e₁⟩, ⟨⟨s₂, t₂, S₂, B₂, I₂⟩, e₂⟩, hsp⟩ => ?_)
      fun _ _ h => h)
    (reject_ct.mono (fun w₁ w₂ ⟨a, ⟨⟨s₁, t₁, S₁, B₁, I₁⟩, _⟩, ⟨⟨s₂, t₂, S₂, B₂, I₂⟩, _⟩, hsp⟩ =>
      ⟨a, ⟨s₁, t₁, S₁, B₁, I₁⟩, ⟨s₂, t₂, S₂, B₂, I₂⟩, hsp⟩) fun _ _ h => h)))
  have full : ∀ {s t₀ w : State}, PR c.stack a s → At s t₀ (N a) w → isa.eval (.zero .x .x16) w = some true →
      (kept s (N a)).length = psLen s := fun {s t₀ w} S I e => by
    rw [eval_zero, I.x16] at e
    have hc := I.hc
    have hP : psLen s < 2 ^ 64 := by have := S.pre.ps; omega_using [this]
    have h0 : BitVec.ofNat 64 (psLen s - (kept s (N a)).length) = 0 := by
      simpa using e
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP])] at this
    simp at this; omega_using [hc, this]
  exact ⟨a, ⟨s₁, t₁, S₁, B₁, I₁, full S₁ I₁ e₁⟩, ⟨s₂, t₂, S₂, B₂, I₂, full S₂ I₂ e₂⟩, hsp⟩

theorem pub_refl (s : State) : pub s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem code_constantTime (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    ConstantTime isa (contract c.stack).pre (contract c.stack).pub (code (encName c) (encCode c)) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True)
    ((body_ct c hsat).mono ?_ fun _ _ h => h)))
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  refine ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hp⟩, rfl⟩, ?_⟩
  show (entered s₁).sp = (entered s₂).sp
  rw [entered_sp, entered_sp]
  show s₁.sp - _ = s₂.sp - _
  rw [hp.1]

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed` with the
precomputed public operation `c`, meets the shared contract with `c.stack + 2192`
bytes of stack. -/
theorem code_verified (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    (hsat' : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack c.stack)).pre s) :
    Verified AArch64.target (code (encName c) (encCode c))
      (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack c.stack)) :=
  Verified.of_correct (k := contract c.stack) (fun _ h => by
    obtain ⟨t, s', he, hq⟩ := code_ok c hsat (pre_of h)
    exact ⟨t, s', he, hq⟩) (code_constantTime c hsat) (implies c.stack hsat')

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
