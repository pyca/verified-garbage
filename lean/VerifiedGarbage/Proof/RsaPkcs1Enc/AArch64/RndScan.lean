module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

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
