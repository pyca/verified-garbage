import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Impl.Blake2.X86.CompressS
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.TCB.X86.Target

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressS.Dword`. -/
section

/-!
# BLAKE2s on x86 (32-bit): what the doubleword lemmas leave out

`movd` stated on the doublewords of its result, a rotation to the right as
two shifts, and the rotation by 16 in both directions (the framework's
`dword_rot16` rotates to the left; BLAKE2s rotates to the right).
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86

theorem dword_movd_0 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 0 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, ite_true]

theorem dword_movd_1 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and, Nat.mul_one, show ¬ 32 + j < 32 by omega, ite_false]
  simp

/-- A rotation to the right as two shifts. -/
theorem shr_or_shl (x : BitVec 32) {k : Nat} (hk : k < 32) :
    x >>> k ||| x <<< (32 - k) = x.rotateRight k := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hk]

theorem rotateLeft_16 (x : BitVec 32) : x.rotateLeft 16 = x.rotateRight 16 := by
  simp only [BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.rotateRight, BitVec.rotateRightAux,
    Nat.reduceMod, Nat.reduceSub]
  exact BitVec.or_comm _ _

end VG.Proof.Blake2.X86.CompressS

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressS.Round`. -/
section

/-!
# BLAKE2s on x86 (32-bit), with SSE2: the rounds

Doubleword `i` of `xmm r` holds word `4 r + i` of the work vector (`Rows`).
`vg_ok` executes `G` on each doubleword of the four rows once, for any
values; `gather_ok` the gathering of four message words, for any words of
the block (`Msg`); `round_ok` and `rounds_ok` compose them into the rounds of
`F`: `G` on each doubleword is the column step, and with the rows rotated
(`diag`), the diagonal step.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86
open VG.Spec.Blake2 (Work Block G sigmaAt)
open VG.Proof.Blake2 (mix G_get)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS

/-- The block `M` is at `K`: word `j` at `[K + 4j]`. -/
def Msg (K : BitVec 32) (M : VG.Spec.Blake2.Block 32) (m : Mem) : Prop :=
  ∀ j : Fin 16, m.readW (VG.X86.addr K (4 * j.val)) 32 = M j

/-- Doubleword `l` of register `r`. -/
abbrev dw (s : State) (r : XReg) (l : Nat) : BitVec 32 := dword (s.xmm r) l

/-! ## `G` on each doubleword -/

theorem rotr12 (x : BitVec 32) : x >>> 12 ||| x <<< 20 = x.rotateRight 12 := VG.Proof.Blake2.X86.CompressS.shr_or_shl x (by decide)
theorem rotr8 (x : BitVec 32) : x >>> 8 ||| x <<< 24 = x.rotateRight 8 := VG.Proof.Blake2.X86.CompressS.shr_or_shl x (by decide)
theorem rotr7 (x : BitVec 32) : x >>> 7 ||| x <<< 25 = x.rotateRight 7 := VG.Proof.Blake2.X86.CompressS.shr_or_shl x (by decide)

theorem psrld_12 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 12)) i = dword x i >>> 12 := dword_psrld x _ (by decide) hi
theorem pslld_20 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 20)) i = dword x i <<< 20 := dword_pslld x _ (by decide) hi
theorem psrld_8 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 8)) i = dword x i >>> 8 := dword_psrld x _ (by decide) hi
theorem pslld_24 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 24)) i = dword x i <<< 24 := dword_pslld x _ (by decide) hi
theorem psrld_7 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 7)) i = dword x i >>> 7 := dword_psrld x _ (by decide) hi
theorem pslld_25 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 25)) i = dword x i <<< 25 := dword_pslld x _ (by decide) hi

theorem vg_eq : vg =
    [xb .paddd .xmm0 .xmm5, xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0,
     .xop (.pshuflw .xmm3 .xmm3 0xb1), .xop (.pshufhw .xmm3 .xmm3 0xb1),
     xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2,
     xb .movdqa .xmm4 .xmm1, .xop (.shift .psrld .xmm1 (BitVec.ofNat 8 12)),
     .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 20)), xb .por .xmm1 .xmm4,
     xb .paddd .xmm0 .xmm6, xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0,
     xb .movdqa .xmm4 .xmm3, .xop (.shift .psrld .xmm3 (BitVec.ofNat 8 8)),
     .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 24)), xb .por .xmm3 .xmm4,
     xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2,
     xb .movdqa .xmm4 .xmm1, .xop (.shift .psrld .xmm1 (BitVec.ofNat 8 7)),
     .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 25)), xb .por .xmm1 .xmm4] := rfl

theorem add_swap (a x b : BitVec 32) : a + x + b = a + b + x := by
  rw [BitVec.add_assoc, BitVec.add_comm x b, ← BitVec.add_assoc]

/-- `G`'s four words of doubleword `l`, from the rows and the message words
in `xmm5` and `xmm6`. -/
abbrev laneMix (s : State) (l : Nat) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  VG.Proof.Blake2.mix Spec.Blake2.s (VG.Proof.Blake2.X86.CompressS.dw s .xmm0 l) (VG.Proof.Blake2.X86.CompressS.dw s .xmm1 l) (VG.Proof.Blake2.X86.CompressS.dw s .xmm2 l) (VG.Proof.Blake2.X86.CompressS.dw s .xmm3 l) (VG.Proof.Blake2.X86.CompressS.dw s .xmm5 l)
    (VG.Proof.Blake2.X86.CompressS.dw s .xmm6 l)

theorem vg_ok (s : State) :
    WP isa (.block vg) s fun s' =>
      (∀ l, l < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm0 l = (VG.Proof.Blake2.X86.CompressS.laneMix s l).1 ∧ VG.Proof.Blake2.X86.CompressS.dw s' .xmm1 l = (VG.Proof.Blake2.X86.CompressS.laneMix s l).2.1 ∧
        VG.Proof.Blake2.X86.CompressS.dw s' .xmm2 l = (VG.Proof.Blake2.X86.CompressS.laneMix s l).2.2.1 ∧ VG.Proof.Blake2.X86.CompressS.dw s' .xmm3 l = (VG.Proof.Blake2.X86.CompressS.laneMix s l).2.2.2) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [VG.Proof.Blake2.X86.CompressS.vg_eq]
  apply WP.of_runBlock
  simp only [xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [VG.Proof.Blake2.X86.CompressS.dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, dword_rot16 _ hl, VG.Proof.Blake2.X86.CompressS.psrld_12 _ hl,
      VG.Proof.Blake2.X86.CompressS.pslld_20 _ hl, VG.Proof.Blake2.X86.CompressS.psrld_8 _ hl, VG.Proof.Blake2.X86.CompressS.pslld_24 _ hl, VG.Proof.Blake2.X86.CompressS.psrld_7 _ hl, VG.Proof.Blake2.X86.CompressS.pslld_25 _ hl, VG.Proof.Blake2.X86.CompressS.rotr12, VG.Proof.Blake2.X86.CompressS.rotr8, VG.Proof.Blake2.X86.CompressS.rotr7,
      VG.Proof.Blake2.X86.CompressS.rotateLeft_16, VG.Proof.Blake2.X86.CompressS.laneMix, VG.Proof.Blake2.mix, Spec.Blake2.s, VG.Proof.Blake2.X86.CompressS.add_swap, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, h3, h4, not_false_eq_true]

/-! ## Gathering message words -/

theorem gather_eq (x : XReg) (f : Nat → Nat) : VG.Impl.Blake2.X86.CompressS.gather x f =
    [.mov .ecx (.mem ⟨.edi, 4 * f 0⟩), .mov .edx (.mem ⟨.edi, 4 * f 1⟩),
     .xop (.movd x .ecx), .xop (.movd .xmm7 .edx), .xop (.bin .punpckldq x .xmm7),
     .mov .ecx (.mem ⟨.edi, 4 * f 2⟩), .mov .edx (.mem ⟨.edi, 4 * f 3⟩),
     .xop (.movd .xmm4 .ecx), .xop (.movd .xmm7 .edx), .xop (.bin .punpckldq .xmm4 .xmm7),
     .xop (.bin .punpcklqdq x .xmm4)] := rfl

theorem gathered (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ a) ((0 : BitVec 96) ++ b))
      (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ c) ((0 : BitVec 96) ++ d)) = ofDwords a b c d := by
  simp only [punpcklqdq_eq, punpckldq_eq, dword_ofDwords_0, dword_ofDwords_1, VG.Proof.Blake2.X86.CompressS.dword_movd_0]

theorem dword_gathered (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    dword (ofDwords (f 0) (f 1) (f 2) (f 3)) i = f i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp only [dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]

theorem xmm_setReg_app (s : State) (r : Reg) (v : BitVec 32) (x : XReg) :
    (s.setReg r v).xmm x = s.xmm x := rfl

theorem gather_ok {K : BitVec 32} {M : VG.Spec.Blake2.Block 32} {s : State} (hk : s.gpr .edi = K)
    (hm : VG.Proof.Blake2.X86.CompressS.Msg K M s.mem) (hrd : ∀ j < 16, InRegions (s.rd ++ s.wr) (VG.X86.addr K (4 * j)) 4)
    {x : XReg} (hx4 : x ≠ .xmm4) (hx7 : x ≠ .xmm7) {f : Nat → Nat} (hf : ∀ i < 4, f i < 16) :
    WP isa (.block (VG.Impl.Blake2.X86.CompressS.gather x f)) s fun s' =>
      (∀ i (hi : i < 4), VG.Proof.Blake2.X86.CompressS.dw s' x i = M ⟨f i, hf i hi⟩) ∧
      (∀ y, y ≠ x → y ≠ .xmm4 → y ≠ .xmm7 → s'.xmm y = s.xmm y) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r0 := hrd _ (hf 0 (by decide))
  have r1 := hrd _ (hf 1 (by decide))
  have r2 := hrd _ (hf 2 (by decide))
  have r3 := hrd _ (hf 3 (by decide))
  rw [VG.Proof.Blake2.X86.CompressS.gather_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, VG.X86.readSrc, ea_mk,
    State.load32, RegUpd.gpr_setReg_self, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setReg_of_ne, hk, r0, r1, r2, r3, reduceCtorEq, not_false_eq_true, ↓reduceIte,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun y h1 h2 h3 => ?_, fun r h1 h2 => ?_, trivial, trivial, trivial⟩
  · simp only [VG.Proof.Blake2.X86.CompressS.dw, VG.Proof.Blake2.X86.CompressS.xmm_setReg_app, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx4, RegUpd.xmm_setXmm_of_ne _ _ hx7,
      RegUpd.xmm_setXmm_of_ne _ _ (show (XReg.xmm4) ≠ .xmm7 by decide), VG.Proof.Blake2.X86.CompressS.gathered]
    rw [VG.Proof.Blake2.X86.CompressS.dword_gathered (fun i => s.mem.readW (VG.X86.addr K (4 * f i)) 32) hi, hm ⟨f i, hf i hi⟩]
  · simp only [VG.Proof.Blake2.X86.CompressS.xmm_setReg_app, RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2]

/-! ## The rows -/

/-- The work vector `v` is in `xmm0, …, xmm3`: word `4 r + i` in doubleword
`i` of `xmm r`. -/
structure Rows (v : Work 32) (s : State) : Prop where
  r0 : ∀ i (hi : i < 4), VG.Proof.Blake2.X86.CompressS.dw s .xmm0 i = v[i]
  r1 : ∀ i (hi : i < 4), VG.Proof.Blake2.X86.CompressS.dw s .xmm1 i = v[4 + i]
  r2 : ∀ i (hi : i < 4), VG.Proof.Blake2.X86.CompressS.dw s .xmm2 i = v[8 + i]
  r3 : ∀ i (hi : i < 4), VG.Proof.Blake2.X86.CompressS.dw s .xmm3 i = v[12 + i]

theorem fin16_val (n : Nat) : ((no_index (OfNat.ofNat n) : Fin 16) : Nat) = n % 16 := rfl

/-- The four `G`s on the columns, with message words `X i` and `Y i`. -/
abbrev colStep (v : Work 32) (X Y : Nat → BitVec 32) : Work 32 :=
  G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s v 0 4 8 12 (X 0) (Y 0))
    1 5 9 13 (X 1) (Y 1)) 2 6 10 14 (X 2) (Y 2)) 3 7 11 15 (X 3) (Y 3)

/-- The four `G`s on the diagonals, with message words `X i` and `Y i`. -/
abbrev diagStep (v : Work 32) (X Y : Nat → BitVec 32) : Work 32 :=
  G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s v 0 5 10 15 (X 0) (Y 0))
    1 6 11 12 (X 1) (Y 1)) 2 7 8 13 (X 2) (Y 2)) 3 4 9 14 (X 3) (Y 3)

/-- Message word `j` of half `k` of round `r`. -/
abbrev msgW (M : VG.Spec.Blake2.Block 32) (r k j : Nat) : BitVec 32 := M (sigmaAt r (8 * k + j))

theorem round_eq (M : VG.Spec.Blake2.Block 32) (v : Work 32) (r : Nat) :
    Spec.Blake2.round Spec.Blake2.s M v r =
      VG.Proof.Blake2.X86.CompressS.diagStep (VG.Proof.Blake2.X86.CompressS.colStep v (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 0 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 0 (2 * i + 1)))
        (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i + 1)) := rfl

/-! Bounds of the indices of the work vector, which `get_elem_tactic` would
prove by `omega` over every hypothesis of a long proof. -/

theorem ix0 {i : Nat} (hi : i < 4) : i < 16 := by omega
theorem ix4 {i : Nat} (hi : i < 4) : 4 + i < 16 := by omega
theorem ix8 {i : Nat} (hi : i < 4) : 8 + i < 16 := by omega
theorem ix12 {i : Nat} (hi : i < 4) : 12 + i < 16 := by omega
theorem dx0 (i : Nat) : (i + 3) % 4 < 16 := by omega
theorem dx4 (i : Nat) : 4 + (i + 1) % 4 < 16 := by omega
theorem dx8 (i : Nat) : 8 + (i + 2) % 4 < 16 := by omega
theorem dx12 (i : Nat) : 12 + (i + 3) % 4 < 16 := by omega

/-- Column `i` after the column step is `G` on column `i`. -/
theorem col_get (v : Work 32) (X Y : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    (VG.Proof.Blake2.X86.CompressS.colStep v X Y)[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + i]'(VG.Proof.Blake2.X86.CompressS.ix4 hi)) (v[8 + i]'(VG.Proof.Blake2.X86.CompressS.ix8 hi)) (v[12 + i]'(VG.Proof.Blake2.X86.CompressS.ix12 hi))
        (X i) (Y i)).1 ∧
    (VG.Proof.Blake2.X86.CompressS.colStep v X Y)[4 + i]'(VG.Proof.Blake2.X86.CompressS.ix4 hi) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + i]'(VG.Proof.Blake2.X86.CompressS.ix4 hi)) (v[8 + i]'(VG.Proof.Blake2.X86.CompressS.ix8 hi)) (v[12 + i]'(VG.Proof.Blake2.X86.CompressS.ix12 hi))
        (X i) (Y i)).2.1 ∧
    (VG.Proof.Blake2.X86.CompressS.colStep v X Y)[8 + i]'(VG.Proof.Blake2.X86.CompressS.ix8 hi) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + i]'(VG.Proof.Blake2.X86.CompressS.ix4 hi)) (v[8 + i]'(VG.Proof.Blake2.X86.CompressS.ix8 hi)) (v[12 + i]'(VG.Proof.Blake2.X86.CompressS.ix12 hi))
        (X i) (Y i)).2.2.1 ∧
    (VG.Proof.Blake2.X86.CompressS.colStep v X Y)[12 + i]'(VG.Proof.Blake2.X86.CompressS.ix12 hi) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + i]'(VG.Proof.Blake2.X86.CompressS.ix4 hi)) (v[8 + i]'(VG.Proof.Blake2.X86.CompressS.ix8 hi)) (v[12 + i]'(VG.Proof.Blake2.X86.CompressS.ix12 hi))
        (X i) (Y i)).2.2.2 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [G_get, Fin.getElem_fin, VG.Proof.Blake2.X86.CompressS.fin16_val, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, and_self]

/-- Diagonal `i` after the diagonal step is `G` on diagonal `i`. -/
theorem diag_get (v : Work 32) (X Y : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    (VG.Proof.Blake2.X86.CompressS.diagStep v X Y)[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + (i + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 i))
      (v[8 + (i + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 i)) (v[12 + (i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 i)) (X i) (Y i)).1 ∧
    (VG.Proof.Blake2.X86.CompressS.diagStep v X Y)[4 + (i + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 i) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + (i + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 i))
      (v[8 + (i + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 i)) (v[12 + (i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 i)) (X i) (Y i)).2.1 ∧
    (VG.Proof.Blake2.X86.CompressS.diagStep v X Y)[8 + (i + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 i) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + (i + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 i))
      (v[8 + (i + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 i)) (v[12 + (i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 i)) (X i) (Y i)).2.2.1 ∧
    (VG.Proof.Blake2.X86.CompressS.diagStep v X Y)[12 + (i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 i) =
      (VG.Proof.Blake2.mix Spec.Blake2.s (v[i]'(VG.Proof.Blake2.X86.CompressS.ix0 hi)) (v[4 + (i + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 i))
      (v[8 + (i + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 i)) (v[12 + (i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 i)) (X i) (Y i)).2.2.2 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [G_get, Fin.getElem_fin, VG.Proof.Blake2.X86.CompressS.fin16_val, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, and_self]

/-! ## Rotating the rows -/

theorem shuf39 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x39) i = dword x ((i + 1) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
theorem shuf4e (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x4e) i = dword x ((i + 2) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
theorem shuf93 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x93) i = dword x ((i + 3) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

/-- `xmm0, xmm2, xmm3` rotated by `a, b, c` doublewords by three `pshufd`. -/
theorem shufs_ok (o₁ o₂ o₃ : BitVec 8) {a b c : Nat}
    (h₁ : ∀ x i, i < 4 → dword (shufDwords x o₁) i = dword x ((i + a) % 4))
    (h₂ : ∀ x i, i < 4 → dword (shufDwords x o₂) i = dword x ((i + b) % 4))
    (h₃ : ∀ x i, i < 4 → dword (shufDwords x o₃) i = dword x ((i + c) % 4)) (s : State) :
    WP isa (.block [.xop (.pshufd .xmm0 .xmm0 o₁), .xop (.pshufd .xmm2 .xmm2 o₂),
      .xop (.pshufd .xmm3 .xmm3 o₃)]) s fun s' =>
      (∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm0 i = VG.Proof.Blake2.X86.CompressS.dw s .xmm0 ((i + a) % 4)) ∧
      (∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm1 i = VG.Proof.Blake2.X86.CompressS.dw s .xmm1 i) ∧
      (∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm2 i = VG.Proof.Blake2.X86.CompressS.dw s .xmm2 ((i + b) % 4)) ∧
      (∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm3 i = VG.Proof.Blake2.X86.CompressS.dw s .xmm3 ((i + c) % 4)) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm2 → r ≠ .xmm3 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun i _ => ?_, fun i hi => ?_, fun i hi => ?_, fun r h1 h2 h3 => ?_, trivial,
    trivial, trivial, trivial⟩ <;>
    simp only [VG.Proof.Blake2.X86.CompressS.dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]
  · exact h₁ _ i hi
  · exact h₂ _ i hi
  · exact h₃ _ i hi
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]

theorem diag_eq : diag = [.xop (.pshufd .xmm0 .xmm0 0x93), .xop (.pshufd .xmm2 .xmm2 0x39),
    .xop (.pshufd .xmm3 .xmm3 0x4e)] := rfl
theorem undiag_eq : undiag = [.xop (.pshufd .xmm0 .xmm0 0x39), .xop (.pshufd .xmm2 .xmm2 0x93),
    .xop (.pshufd .xmm3 .xmm3 0x4e)] := rfl

theorem lane_0 (i : Nat) : lane 0 i = i := rfl
theorem lane_1 (i : Nat) : lane 1 i = (i + 3) % 4 := rfl
theorem lane_lt (k : Nat) {i : Nat} (hi : i < 4) : lane k i < 4 := by
  unfold lane; split <;> omega

/-! ## The rounds -/

/-- During the rounds of a block, from `s₀`: the work vector is `v`, and
only the XMM registers, `ecx` and `edx` (and the flags) have changed. -/
structure RS (s₀ : State) (v : Work 32) (s : State) : Prop where
  rows : VG.Proof.Blake2.X86.CompressS.Rows v s
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {K : BitVec 32} {M : VG.Spec.Blake2.Block 32} {s₀ : State} (hk : s₀.gpr .edi = K) (hm : VG.Proof.Blake2.X86.CompressS.Msg K M s₀.mem)
  (hrd : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (VG.X86.addr K (4 * j)) 4)
include hk hm hrd

/-- The message words of half `k` of round `r` into `xmm5` and `xmm6`. -/
theorem msgs_ok {s : State} (hs : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r)
    (hsm : s.mem = s₀.mem) (hsr : s.rd = s₀.rd) (hsw : s.wr = s₀.wr) (r k : Nat) :
    WP isa (.block (msgs r k)) s fun s' =>
      (∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm5 i = VG.Proof.Blake2.X86.CompressS.msgW M r k (2 * lane k i)) ∧
      (∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s' .xmm6 i = VG.Proof.Blake2.X86.CompressS.msgW M r k (2 * lane k i + 1)) ∧
      (∀ y, y ≠ .xmm4 → y ≠ .xmm5 → y ≠ .xmm6 → y ≠ .xmm7 → s'.xmm y = s.xmm y) ∧
      (∀ g, g ≠ .ecx → g ≠ .edx → s'.gpr g = s₀.gpr g) ∧ s'.mem = s₀.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hk' : s.gpr .edi = K := by rw [hs _ (by decide) (by decide), hk]
  have hm' : VG.Proof.Blake2.X86.CompressS.Msg K M s.mem := by rw [hsm]; exact hm
  have hrd' : ∀ j < 16, InRegions (s.rd ++ s.wr) (VG.X86.addr K (4 * j)) 4 := by rw [hsr, hsw]; exact hrd
  unfold msgs
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.gather_ok hk' hm' hrd' (x := .xmm5) (by decide) (by decide)
    (fun i _ => (sigmaAt r (8 * k + 2 * lane k i)).isLt)) fun s₁ ⟨x₁, o₁, g₁, m₁, r₁, w₁⟩ => ?_
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.gather_ok (M := M) (by rw [g₁ _ (by decide) (by decide), hk']) (by rw [m₁]; exact hm')
    (by rw [r₁, w₁]; exact hrd') (x := .xmm6) (by decide) (by decide)
    (fun i _ => (sigmaAt r (8 * k + 2 * lane k i + 1)).isLt)) fun s₂ ⟨x₂, o₂, g₂, m₂, r₂, w₂⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => x₂ i hi, fun y h4 h5 h6 h7 => ?_, fun g h1 h2 => ?_,
    by rw [m₂, m₁, hsm], by rw [r₂, r₁, hsr], by rw [w₂, w₁, hsw]⟩
  · rw [VG.Proof.Blake2.X86.CompressS.dw, o₂ _ (by decide) (by decide) (by decide)]; exact x₁ i hi
  · rw [o₂ _ h6 h4 h7, o₁ _ h5 h4 h7]
  · rw [g₂ g h1 h2, g₁ g h1 h2, hs g h1 h2]

omit hk hm hrd in
/-- `G` on each doubleword of the rows `v`, with message words `X` and `Y`. -/
theorem vg_rows {v : Work 32} {s : State} (h : VG.Proof.Blake2.X86.CompressS.Rows v s) {X Y : Nat → BitVec 32}
    (hX : ∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s .xmm5 i = X i) (hY : ∀ i, i < 4 → VG.Proof.Blake2.X86.CompressS.dw s .xmm6 i = Y i) :
    WP isa (.block vg) s fun s' => VG.Proof.Blake2.X86.CompressS.Rows (VG.Proof.Blake2.X86.CompressS.colStep v X Y) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (VG.Proof.Blake2.X86.CompressS.vg_ok s) fun _ ⟨q, _, g, m, r, w⟩ => by
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, g, m, r, w⟩ <;>
    obtain ⟨a, b, c, d⟩ := q i hi <;>
    simp only [VG.Proof.Blake2.X86.CompressS.laneMix, h.r0 i hi, h.r1 i hi, h.r2 i hi, h.r3 i hi, hX i hi, hY i hi] at a b c d
    · rw [a, (VG.Proof.Blake2.X86.CompressS.col_get v X Y hi).1]
    · rw [b, (VG.Proof.Blake2.X86.CompressS.col_get v X Y hi).2.1]
    · rw [c, (VG.Proof.Blake2.X86.CompressS.col_get v X Y hi).2.2.1]
    · rw [d, (VG.Proof.Blake2.X86.CompressS.col_get v X Y hi).2.2.2]

theorem round_ok {v : Work 32} {s : State} (h : VG.Proof.Blake2.X86.CompressS.RS s₀ v s) (r : Nat) :
    WP isa (VG.Impl.Blake2.X86.CompressS.round r) s (VG.Proof.Blake2.X86.CompressS.RS s₀ (Spec.Blake2.round Spec.Blake2.s M v r)) := by
  -- The column step.
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.msgs_ok hk hm hrd h.gpr h.mem h.rd h.wr r 0)
    fun s₁ ⟨x₁, y₁, o₁, g₁, m₁, r₁, w₁⟩ => ?_)
  simp only [VG.Proof.Blake2.X86.CompressS.lane_0] at x₁ y₁
  have h₁ : VG.Proof.Blake2.X86.CompressS.Rows v s₁ := by
    have e : ∀ q : XReg, q = .xmm0 ∨ q = .xmm1 ∨ q = .xmm2 ∨ q = .xmm3 → s₁.xmm q = s.xmm q :=
      fun q hq => o₁ q (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
    exact ⟨fun i hi => by rw [VG.Proof.Blake2.X86.CompressS.dw, e _ (by simp)]; exact h.rows.r0 i hi,
      fun i hi => by rw [VG.Proof.Blake2.X86.CompressS.dw, e _ (by simp)]; exact h.rows.r1 i hi,
      fun i hi => by rw [VG.Proof.Blake2.X86.CompressS.dw, e _ (by simp)]; exact h.rows.r2 i hi,
      fun i hi => by rw [VG.Proof.Blake2.X86.CompressS.dw, e _ (by simp)]; exact h.rows.r3 i hi⟩
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.vg_rows h₁ x₁ y₁) fun s₂ ⟨h₂, g₂, m₂, r₂, w₂⟩ => ?_)
  -- The rows rotated.
  refine WP.seq ?_
  rw [VG.Proof.Blake2.X86.CompressS.diag_eq]
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.shufs_ok 0x93 0x39 0x4e (a := 3) (b := 1) (c := 2) (fun x i hi => VG.Proof.Blake2.X86.CompressS.shuf93 x hi)
    (fun x i hi => VG.Proof.Blake2.X86.CompressS.shuf39 x hi) (fun x i hi => VG.Proof.Blake2.X86.CompressS.shuf4e x hi) s₂)
    fun s₃ ⟨d0, d1, d2, d3, _, g₃, m₃, r₃, w₃⟩ => ?_
  obtain ⟨w, hw⟩ : ∃ w, w = VG.Proof.Blake2.X86.CompressS.colStep v (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 0 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 0 (2 * i + 1)) :=
    ⟨_, rfl⟩
  rw [← hw] at h₂
  -- The diagonal step.
  have gs : ∀ g, g ≠ .ecx → g ≠ .edx → s₃.gpr g = s₀.gpr g := fun g h1 h2 => by
    rw [g₃, g₂, g₁ g h1 h2]
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.msgs_ok hk hm hrd gs (by rw [m₃, m₂, m₁]) (by rw [r₃, r₂, r₁])
    (by rw [w₃, w₂, w₁]) r 1) fun s₄ ⟨x₄, y₄, o₄, g₄, m₄, r₄, w₄⟩ => ?_)
  simp only [VG.Proof.Blake2.X86.CompressS.lane_1] at x₄ y₄
  have e₄ : ∀ q : XReg, q = .xmm0 ∨ q = .xmm1 ∨ q = .xmm2 ∨ q = .xmm3 → s₄.xmm q = s₃.xmm q :=
    fun q hq => o₄ q (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
  -- Doubleword `i` holds diagonal `j = i - 1` of `w`.
  have dg : ∀ i (hi : i < 4),
      VG.Proof.Blake2.X86.CompressS.dw s₄ .xmm0 i = w[(i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx0 i) ∧ VG.Proof.Blake2.X86.CompressS.dw s₄ .xmm1 i = w[4 + ((i + 3) % 4 + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 _) ∧
      VG.Proof.Blake2.X86.CompressS.dw s₄ .xmm2 i = w[8 + ((i + 3) % 4 + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 _) ∧
      VG.Proof.Blake2.X86.CompressS.dw s₄ .xmm3 i = w[12 + ((i + 3) % 4 + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 _) :=
    fun i hi => ⟨by rw [VG.Proof.Blake2.X86.CompressS.dw, e₄ _ (by simp)]; exact (d0 i hi).trans (h₂.r0 _ (Nat.mod_lt _ (by decide))),
      by rw [VG.Proof.Blake2.X86.CompressS.dw, e₄ _ (by simp)]; exact (d1 i hi).trans ((h₂.r1 i hi).trans (getElem_congr_idx (by omega))),
      by rw [VG.Proof.Blake2.X86.CompressS.dw, e₄ _ (by simp)]
         exact (d2 i hi).trans ((h₂.r2 _ (Nat.mod_lt _ (by decide))).trans (getElem_congr_idx (by omega))),
      by rw [VG.Proof.Blake2.X86.CompressS.dw, e₄ _ (by simp)]
         exact (d3 i hi).trans ((h₂.r3 _ (Nat.mod_lt _ (by decide))).trans (getElem_congr_idx (by omega)))⟩
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.vg_ok s₄) fun s₅ ⟨q, _, g₅, m₅, r₅, w₅⟩ => ?_)
  rw [VG.Proof.Blake2.X86.CompressS.undiag_eq]
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.shufs_ok 0x39 0x93 0x4e (a := 1) (b := 3) (c := 2) (fun x i hi => VG.Proof.Blake2.X86.CompressS.shuf39 x hi)
    (fun x i hi => VG.Proof.Blake2.X86.CompressS.shuf93 x hi) (fun x i hi => VG.Proof.Blake2.X86.CompressS.shuf4e x hi) s₅)
    fun s₆ ⟨u0, u1, u2, u3, _, g₆, m₆, r₆, w₆⟩ => ?_
  rw [VG.Proof.Blake2.X86.CompressS.round_eq, ← hw]
  have hq : ∀ i (hi : i < 4),
      VG.Proof.Blake2.X86.CompressS.dw s₅ .xmm0 i = (VG.Proof.Blake2.X86.CompressS.diagStep w (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i + 1)))[(i + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx0 i) ∧
      VG.Proof.Blake2.X86.CompressS.dw s₅ .xmm1 i = (VG.Proof.Blake2.X86.CompressS.diagStep w (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i + 1)))[4 + ((i + 3) % 4 + 1) % 4]'(VG.Proof.Blake2.X86.CompressS.dx4 _) ∧
      VG.Proof.Blake2.X86.CompressS.dw s₅ .xmm2 i = (VG.Proof.Blake2.X86.CompressS.diagStep w (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i + 1)))[8 + ((i + 3) % 4 + 2) % 4]'(VG.Proof.Blake2.X86.CompressS.dx8 _) ∧
      VG.Proof.Blake2.X86.CompressS.dw s₅ .xmm3 i = (VG.Proof.Blake2.X86.CompressS.diagStep w (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i + 1)))[12 + ((i + 3) % 4 + 3) % 4]'(VG.Proof.Blake2.X86.CompressS.dx12 _) := fun i hi => by
    obtain ⟨a, b, c, d⟩ := q i hi
    obtain ⟨l0, l1, l2, l3⟩ := dg i hi
    obtain ⟨e0, e1, e2, e3⟩ := VG.Proof.Blake2.X86.CompressS.diag_get w (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i)) (fun i => VG.Proof.Blake2.X86.CompressS.msgW M r 1 (2 * i + 1))
      (Nat.mod_lt (i + 3) (show 0 < 4 by decide))
    simp only [VG.Proof.Blake2.X86.CompressS.laneMix, l0, l1, l2, l3, x₄ i hi, y₄ i hi] at a b c d
    exact ⟨a.trans e0.symm, b.trans e1.symm, c.trans e2.symm, d.trans e3.symm⟩
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩,
    fun g h1 h2 => by rw [g₆, g₅, g₄ g h1 h2], by rw [m₆, m₅, m₄], by rw [r₆, r₅, r₄],
    by rw [w₆, w₅, w₄]⟩
  · rw [u0 i hi, (hq _ (Nat.mod_lt _ (by decide))).1]
    exact getElem_congr_idx (by omega)
  · rw [u1 i hi, (hq i hi).2.1]
    exact getElem_congr_idx (by omega)
  · rw [u2 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.2.1]
    exact getElem_congr_idx (by omega)
  · rw [u3 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.2.2]
    exact getElem_congr_idx (by omega)

theorem rounds_ok {v : Work 32} {s : State} (h : VG.Proof.Blake2.X86.CompressS.RS s₀ v s) (n : Nat) :
    WP isa (VG.Impl.Blake2.X86.CompressS.rounds n) s (VG.Proof.Blake2.X86.CompressS.RS s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.s M) v)) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s' h' => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact VG.Proof.Blake2.X86.CompressS.round_ok hk hm hrd h' n

end

end VG.Proof.Blake2.X86.CompressS

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressS.Body`. -/
section

section

/-!
# BLAKE2s on x86 (32-bit): words of `scratch`

`workR`, the first 64 bytes of `scratch`, which only the code that sets up
the work vector writes, and reading its words after writes.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (readW_writeW_addr)

/-- The first 64 bytes of `scratch`. -/
abbrev workR (B : BitVec 32) : Region := ⟨B.setWidth 64, 64⟩

theorem mem_rd {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem rw_slot {B : BitVec 32} (hfit : B.toNat + 64 ≤ 2 ^ 32) (m : Mem) (x : BitVec 32) {i k : Nat}
    (hi : i < 16) (hk : k < 16) :
    (m.writeW (addr B (vOff i)) x).readW (addr B (vOff k)) 32 =
      if i = k then x else m.readW (addr B (vOff k)) 32 := by
  by_cases h : i = k
  · subst h; simp only [Mem.readW_writeW_self32, ite_true]
  · simp only [h, ite_false]
    exact readW_writeW_addr m x (by simp only [vOff]; omega) (by simp only [vOff]; omega)
      (by simp only [vOff]; omega)

/-- Doubleword `i` of 16 bytes loaded from `[B + d]`. -/
theorem dword_load (m : Mem) {B : BitVec 32} {d i : Nat} (hfit : B.toNat + d + 16 ≤ 2 ^ 32)
    (hi : i < 4) : dword (m.readW (addr B d) 128) i = m.readW (addr B (d + 4 * i)) 32 := by
  rw [addr_eq (by omega), addr_eq (by omega), dword_readW _ _ hi, Offset.add_add]

/-- Doubleword `i` of 16 bytes stored to `[B + d]`, read back. -/
theorem load_write_self (m : Mem) {B : BitVec 32} {d i : Nat} (v : BitVec 128)
    (hfit : B.toNat + d + 16 ≤ 2 ^ 32) (hi : i < 4) :
    (m.writeW (addr B d) v).readW (addr B (d + 4 * i)) 32 = dword v i := by
  rw [show addr B (d + 4 * i) = addr B d + BitVec.ofNat 64 (4 * i) by
    rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add], readW_writeW128 _ _ _ hi]

end VG.Proof.Blake2.X86.CompressS

end

section

/-!
# BLAKE2s on x86 (32-bit): the compression function's precondition

`Pre` unpacks the precondition of `compressX86 Spec.Blake2.s`; its lemmas
locate the words the code reads and writes. Also `V0` and `F_eq`: `F` in the
order of the code.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block HashValue blockBytes stateAt blockAt compressBlocks)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-! ## The compression function, in the order of the code -/

/-- The work vector before the rounds (RFC 7693 §3.2). -/
def V0 (h : VG.Spec.Blake2.HashValue 32) (t : Nat) (f : Bool) : Work 32 :=
  let v : Work 32 := h ++ Spec.Blake2.s.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 32 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 32 (t / 2 ^ 32))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v

theorem F_eq (h : VG.Spec.Blake2.HashValue 32) (m : VG.Spec.Blake2.Block 32) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.s h m t f = Vector.ofFn fun i : Fin 8 =>
      h[i] ^^^ ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (VG.Proof.Blake2.X86.CompressS.V0 h t f))[i] ^^^
        ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (VG.Proof.Blake2.X86.CompressS.V0 h t f))[i.val + 8] := rfl

/-- The final block flag as a word. -/
def flagW (f : Bool) : BitVec 32 := if f then BitVec.allOnes 32 else 0

theorem V0_get (h : VG.Spec.Blake2.HashValue 32) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) : (VG.Proof.Blake2.X86.CompressS.V0 h t f)[k] =
    if hk8 : k < 8 then h[k] else if k = 12 then Spec.Blake2.s.IV[4] ^^^ BitVec.ofNat 32 t
    else if k = 13 then Spec.Blake2.s.IV[5] ^^^ BitVec.ofNat 32 (t / 2 ^ 32)
    else if k = 14 then Spec.Blake2.s.IV[6] ^^^ VG.Proof.Blake2.X86.CompressS.flagW f else Spec.Blake2.s.IV[k - 8]'(by omega) := by
  have base : ((h ++ Spec.Blake2.s.IV : Work 32))[k] =
      if hk8 : k < 8 then h[k] else Spec.Blake2.s.IV[k - 8]'(by omega) := by
    simp only [Vector.getElem_append]
  have e12 : (h ++ Spec.Blake2.s.IV : Work 32)[12] = Spec.Blake2.s.IV[4] := by
    simp only [Vector.getElem_append]; rfl
  have e13 : (h ++ Spec.Blake2.s.IV : Work 32)[13] = Spec.Blake2.s.IV[5] := by
    simp only [Vector.getElem_append]; rfl
  have e14 : (h ++ Spec.Blake2.s.IV : Work 32)[14] = Spec.Blake2.s.IV[6] := by
    simp only [Vector.getElem_append]; rfl
  by_cases k14 : k = 14
  · subst k14; cases f <;> simp [VG.Proof.Blake2.X86.CompressS.V0, VG.Proof.Blake2.X86.CompressS.flagW, e14]
  by_cases k13 : k = 13
  · subst k13; cases f <;> simp [VG.Proof.Blake2.X86.CompressS.V0, e13]
  by_cases k12 : k = 12
  · subst k12; cases f <;> simp [VG.Proof.Blake2.X86.CompressS.V0, e12]
  have n14 : ¬14 = k := Ne.symm k14
  have n13 : ¬13 = k := Ne.symm k13
  have n12 : ¬12 = k := Ne.symm k12
  cases f <;> simp only [VG.Proof.Blake2.X86.CompressS.V0, Vector.getElem_set, n14, n13, n12, k14, k13, k12, ite_false, base,
    Bool.false_eq_true, ite_true]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := VG.X86.arg s₀ 0
abbrev bp : BitVec 32 := VG.X86.arg s₀ 1
abbrev nb : Nat := (VG.X86.arg s₀ 2).toNat
abbrev t₀ : Nat := (VG.X86.arg s₀ 4 ++ VG.X86.arg s₀ 3).toNat
abbrev fl : Bool := VG.X86.arg s₀ 5 != 0
abbrev scr : BitVec 32 := VG.X86.arg s₀ 6
abbrev stR : Region := ⟨(VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64, 32⟩
abbrev blR : Region := ⟨(VG.Proof.Blake2.X86.CompressS.bp s₀).setWidth 64, 64 * VG.Proof.Blake2.X86.CompressS.nb s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.Blake2.X86.CompressS.scr s₀).setWidth 64, 512⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(VG.Proof.Blake2.X86.CompressS.esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : VG.Spec.Blake2.HashValue 32 := VG.Spec.Blake2.stateAt 32 s₀.mem ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Blake2.X86.CompressS.bp s₀ + BitVec.ofNat 32 (64 * i)

/-- Block `i`, as `compressBlocks` reads it. -/
abbrev blk (i : Nat) : VG.Spec.Blake2.Block 32 :=
  VG.Spec.Blake2.blockAt 32 s₀.mem ((VG.Proof.Blake2.X86.CompressS.bp s₀).setWidth 64 + BitVec.ofNat 64 (blockBytes 32 * i))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.X86.CompressS.blR s₀, VG.Proof.Blake2.X86.CompressS.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀]
  st_scr : (VG.Proof.Blake2.X86.CompressS.stR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.scrR s₀)
  blk_st : (VG.Proof.Blake2.X86.CompressS.blR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.stR s₀)
  blk_scr : (VG.Proof.Blake2.X86.CompressS.blR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.scrR s₀)
  arg_st : (VG.Proof.Blake2.X86.CompressS.argR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.stR s₀)
  arg_scr : (VG.Proof.Blake2.X86.CompressS.argR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.scrR s₀)
  ret_st : (VG.Proof.Blake2.X86.CompressS.retR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.stR s₀)
  ret_scr : (VG.Proof.Blake2.X86.CompressS.retR s₀).Disjoint (VG.Proof.Blake2.X86.CompressS.scrR s₀)
  st_fits : (VG.Proof.Blake2.X86.CompressS.st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Blake2.X86.CompressS.bp s₀).toNat + 64 * VG.Proof.Blake2.X86.CompressS.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Blake2.X86.CompressS.scr s₀).toNat + 512 ≤ 2 ^ 32
  esp_fits : (VG.Proof.Blake2.X86.CompressS.esp₀ s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₀) : VG.Proof.Blake2.X86.CompressS.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The callee-saved registers are saved in `scratch`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (VG.Proof.Blake2.X86.CompressS.scr s₀)) s₀.gpr saved

theorem saved_fits : Spill.Fits 92 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 80 ≤ p.2 ∧ p.2 + 4 ≤ 92 := by decide

namespace Pre
variable {s₀ : State} (h : VG.Proof.Blake2.X86.CompressS.Pre s₀)
include h

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions s.wr (addr (VG.Proof.Blake2.X86.CompressS.st s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.CompressS.stR s₀, by simp [hw, h.wr], contains_addr hd (by omega) h.st_fits⟩

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 512) :
    InRegions s.wr (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.CompressS.scrR s₀, by simp [hw, h.wr], contains_addr hd (by omega) h.scr_fits⟩

theorem argAddr_eq {d : Nat} (hd : d < 32) :
    addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) d = (VG.Proof.Blake2.X86.CompressS.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    (VG.Proof.Blake2.X86.CompressS.argR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) d) 4 := by
  show (⟨addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) 4, 28⟩ : Region).Contains _ _
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.CompressS.argR s₀, by simp [hrd, h.rd], h.arg_contains hd hd'⟩

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.Blake2.X86.CompressS.argR s₀) := by
  show Region.Sub ⟨addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) 4, 28⟩
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and `scratch` are written. -/
theorem arg_frame {m : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀] s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressS.nb s₀) : (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i).toNat = (VG.Proof.Blake2.X86.CompressS.bp s₀).toNat + 64 * i := by
  have := h.blk_fits
  simp only [VG.Proof.Blake2.X86.CompressS.blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 64 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_word {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressS.nb s₀) {o : Nat} (ho : o + 4 ≤ 64) :
    addr (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) o = (VG.Proof.Blake2.X86.CompressS.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + o) := by
  rw [show addr (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) o = addr (VG.Proof.Blake2.X86.CompressS.bp s₀) (64 * i + o) by
    simp only [addr, VG.Proof.Blake2.X86.CompressS.blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact addr_eq (by have := h.blk_fits; have : i + 1 ≤ VG.Proof.Blake2.X86.CompressS.nb s₀ := hi; omega)

theorem blk_contains {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressS.nb s₀) {o : Nat} (ho : o + 4 ≤ 64) :
    (VG.Proof.Blake2.X86.CompressS.blR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) o) 4 := by
  rw [h.blk_word hi ho]
  have := h.blk_fits
  exact Offset.contains_base _ (by have : i + 1 ≤ VG.Proof.Blake2.X86.CompressS.nb s₀ := hi; omega) (by omega)

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 512) : (VG.Proof.Blake2.X86.CompressS.scrR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 4 :=
  contains_addr hd (by omega) h.scr_fits

theorem st_contains {d : Nat} (hd : d + 4 ≤ 32) : (VG.Proof.Blake2.X86.CompressS.stR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressS.st s₀) d) 4 :=
  contains_addr hd (by omega) h.st_fits

/-- The words of block `i` are readable. -/
theorem blk_rd {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressS.nb s₀) :
    ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) (4 * j)) 4 :=
  fun _ hj => ⟨VG.Proof.Blake2.X86.CompressS.blR s₀, by simp [h.rd], h.blk_contains hi (by omega)⟩

/-- Block `i`, while only the state and `scratch` are written. -/
theorem msg {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressS.nb s₀) {m : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀] s₀.mem m) :
    VG.Proof.Blake2.X86.CompressS.Msg (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) (VG.Proof.Blake2.X86.CompressS.blk s₀ i) m := by
  intro j
  have hj := j.isLt
  rw [hf.readW (r := VG.Proof.Blake2.X86.CompressS.blR s₀) (h.blk_contains hi (by omega)) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨h.blk_st, h.blk_scr⟩) (by decide),
    h.blk_word hi (by omega)]
  have e := Proof.Blake2.blockAt_word (w := 32) s₀.mem
    ((VG.Proof.Blake2.X86.CompressS.bp s₀).setWidth 64 + BitVec.ofNat 64 (blockBytes 32 * i)) j.1 hj
  rw [show VG.Proof.Blake2.X86.CompressS.blk s₀ i j = VG.Proof.Blake2.X86.CompressS.blk s₀ i ⟨j.1, hj⟩ from rfl, VG.Proof.Blake2.X86.CompressS.blk, e, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rfl

/-- Word `k` of the state. -/
theorem stateAt_get (m : Mem) {k : Nat} (hk : k < 8) :
    (VG.Spec.Blake2.stateAt 32 m ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64))[k] = m.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) 32 := by
  simp only [VG.Spec.Blake2.stateAt, Vector.getElem_ofFn]
  rw [addr_eq (by have := h.st_fits; omega)]

theorem stateAt_ext {m : Mem} {H : VG.Spec.Blake2.HashValue 32}
    (hH : ∀ k (hk : k < 8), m.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) 32 = H[k]) :
    VG.Spec.Blake2.stateAt 32 m ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64) = H := by
  ext k hk
  rw [h.stateAt_get m hk, hH k hk]

/-- `scratch` beyond the work vector is unchanged while only the work vector,
or the state, is written. -/
theorem high_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressS.workR (VG.Proof.Blake2.X86.CompressS.scr s₀)] m m' ∨ Frame [VG.Proof.Blake2.X86.CompressS.stR s₀] m m') {d : Nat}
    (hd : 64 ≤ d) (hd' : d + 4 ≤ 512) :
    m'.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 := by
  have hc : (⟨addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d, 4⟩ : Region).Contains (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := h.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left h.st_scr.symm ?_
    rw [addr_eq (by omega)]
    exact Offset.sub_base _ (by omega)

/-- The state is unchanged while only the work vector is written. -/
theorem st_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressS.workR (VG.Proof.Blake2.X86.CompressS.scr s₀)] m m') {d : Nat} (hd : d + 4 ≤ 32) :
    m'.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Blake2.X86.CompressS.stR s₀) (h.st_contains hd) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The work vector is unchanged while only the state is written. -/
theorem work_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressS.stR s₀] m m') {d : Nat} (hd : d + 4 ≤ 512) :
    m'.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Blake2.X86.CompressS.scrR s₀) (h.scr_contains hd) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact h.st_scr.symm

theorem saved_frame {m m' : Mem} (hs : VG.Proof.Blake2.X86.CompressS.Saved s₀ m)
    (hf : Frame [VG.Proof.Blake2.X86.CompressS.workR (VG.Proof.Blake2.X86.CompressS.scr s₀)] m m' ∨ Frame [VG.Proof.Blake2.X86.CompressS.stR s₀] m m') : VG.Proof.Blake2.X86.CompressS.Saved s₀ m' :=
  hs.of_readW fun p hp => have hb := VG.Proof.Blake2.X86.CompressS.saved_bound p hp; h.high_frame hf (by omega) (by omega)

end Pre

end VG.Proof.Blake2.X86.CompressS

end

/-!
# BLAKE2s on x86 (32-bit): one block

`body_ok`: the loop body compresses block `i` into the state and advances to
the next block, from the loop invariant `LInv`.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block HashValue blockBytes stateAt blockAt compressBlocks)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr addr_sep)

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀
  esp : s.gpr .esp = VG.Proof.Blake2.X86.CompressS.esp₀ s₀
  ebp : s.gpr .ebp = s₀.gpr .ebp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀] s₀.mem s.mem
  state : VG.Spec.Blake2.stateAt 32 s.mem ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64) =
    VG.Spec.Blake2.compressBlocks Spec.Blake2.s (VG.Proof.Blake2.X86.CompressS.H₀ s₀) s₀.mem ((VG.Proof.Blake2.X86.CompressS.bp s₀).setWidth 64) i (VG.Proof.Blake2.X86.CompressS.t₀ s₀) (VG.Proof.Blake2.X86.CompressS.fl s₀)
  saved : VG.Proof.Blake2.X86.CompressS.Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Blake2.X86.CompressS.Common s₀ i s where
  edi : s.gpr .edi = VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i
  tlo : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) tloOff) 32 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressS.t₀ s₀ + i * 64)
  thi : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) thiOff) 32 = BitVec.ofNat 32 ((VG.Proof.Blake2.X86.CompressS.t₀ s₀ + i * 64) / 2 ^ 32)
  flag : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) fOff) 32 = VG.Proof.Blake2.X86.CompressS.flagW (VG.Proof.Blake2.X86.CompressS.fl s₀)
  cnt : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) nOff) 32 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressS.nb s₀ - i)

/-! ## Words of `scratch` -/

section
variable {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32)
include hfit

theorem rw_scr (m : Mem) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr B e) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  readW_writeW_addr m v (by omega) (by omega) h

theorem rw_hi (m : Mem) (v : BitVec 32) {k d : Nat} (hk : k < 16) (hd : 64 ≤ d) (hd' : d + 4 ≤ 512) :
    (m.writeW (addr B (vOff k)) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  readW_writeW_addr m v (by omega) (by simp only [vOff]; omega) (by simp only [vOff]; omega)

end

section
variable {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀)
include hp

/-! ## Setting up the work vector -/

/-- The IV part of the work vector, with the counter and the flag, stored
to `scratch`. -/
def ivs : List Instr :=
  [.mov .ecx (.imm Spec.Blake2.s.IV[0]), .store (at_ .esi (vOff 8)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[1]), .store (at_ .esi (vOff 9)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[2]), .store (at_ .esi (vOff 10)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[3]), .store (at_ .esi (vOff 11)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[4]), .alu .xor .ecx (.mem (at_ .esi tloOff)),
   .store (at_ .esi (vOff 12)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[5]), .alu .xor .ecx (.mem (at_ .esi thiOff)),
   .store (at_ .esi (vOff 13)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[6]), .alu .xor .ecx (.mem (at_ .esi fOff)),
   .store (at_ .esi (vOff 14)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[7]), .store (at_ .esi (vOff 15)) .ecx]

/-- The rows loaded. -/
def loadX : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .eax 16),
   .movdquLoad .xmm2 (at_ .esi (vOff 8)), .movdquLoad .xmm3 (at_ .esi (vOff 12))]

omit hp in
theorem load_eq : load = (.mov .eax (.mem (at_ .esp 4)) :: VG.Proof.Blake2.X86.CompressS.ivs) ++ VG.Proof.Blake2.X86.CompressS.loadX := rfl

/-- The memory after `ivs`. -/
def ivMem (m : Mem) (B : BitVec 32) : Mem :=
  (((((((m.writeW (addr B (vOff 8)) Spec.Blake2.s.IV[0]).writeW (addr B (vOff 9)) Spec.Blake2.s.IV[1]).writeW
    (addr B (vOff 10)) Spec.Blake2.s.IV[2]).writeW (addr B (vOff 11)) Spec.Blake2.s.IV[3]).writeW
    (addr B (vOff 12)) (Spec.Blake2.s.IV[4] ^^^ m.readW (addr B tloOff) 32)).writeW
    (addr B (vOff 13)) (Spec.Blake2.s.IV[5] ^^^ m.readW (addr B thiOff) 32)).writeW
    (addr B (vOff 14)) (Spec.Blake2.s.IV[6] ^^^ m.readW (addr B fOff) 32)).writeW
    (addr B (vOff 15)) Spec.Blake2.s.IV[7]

theorem ivs_ok {s : State} (hesi : s.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block VG.Proof.Blake2.X86.CompressS.ivs) s fun s' =>
      s'.gpr .eax = s.gpr .eax ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.Proof.Blake2.X86.CompressS.ivMem s.mem (VG.Proof.Blake2.X86.CompressS.scr s₀) := by
  have fV := hp.scr_fits
  have hw : ∀ k, 8 ≤ k → k < 16 → InRegions s.wr (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) (vOff k)) 4 := fun k _ hk =>
    hp.in_scr hwr (by simp only [vOff]; omega)
  have w8 := hw 8 (by omega) (by omega)
  have w9 := hw 9 (by omega) (by omega)
  have w10 := hw 10 (by omega) (by omega)
  have w11 := hw 11 (by omega) (by omega)
  have w12 := hw 12 (by omega) (by omega)
  have w13 := hw 13 (by omega) (by omega)
  have w14 := hw 14 (by omega) (by omega)
  have w15 := hw 15 (by omega) (by omega)
  have r64 := VG.Proof.Blake2.X86.CompressS.mem_rd (rd := s.rd) (hp.in_scr (d := tloOff) hwr (by decide))
  have r68 := VG.Proof.Blake2.X86.CompressS.mem_rd (rd := s.rd) (hp.in_scr (d := thiOff) hwr (by decide))
  have r72 := VG.Proof.Blake2.X86.CompressS.mem_rd (rd := s.rd) (hp.in_scr (d := fOff) hwr (by decide))
  have hh : ∀ (m : Mem) (v : BitVec 32) (k d : Nat), k < 16 → 64 ≤ d → d + 4 ≤ 512 →
      (m.writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) (vOff k)) v).readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 :=
    fun m v k d h1 h2 h3 => VG.Proof.Blake2.X86.CompressS.rw_hi fV m v h1 h2 h3
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, VG.Proof.Blake2.X86.CompressS.ivs, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hesi, w8, w9, w10, w11, w12,
    w13, w14, w15, r64, r68, r72, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
  simp (disch := decide) only [hh]
  rfl

theorem in_st16 {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 16 ≤ 32) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressS.st s₀) d) 16 := by
  rw [hrd, hwr]; exact VG.Proof.Blake2.X86.CompressS.mem_rd ⟨VG.Proof.Blake2.X86.CompressS.stR s₀, by simp [hp.wr], contains_addr hd (by omega) hp.st_fits⟩

theorem out_st16 {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 16 ≤ 32) :
    InRegions s.wr (addr (VG.Proof.Blake2.X86.CompressS.st s₀) d) 16 := by
  rw [hwr]; exact ⟨VG.Proof.Blake2.X86.CompressS.stR s₀, by simp [hp.wr], contains_addr hd (by omega) hp.st_fits⟩

theorem in_scr16 {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 16 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 16 := by
  rw [hrd, hwr]; exact VG.Proof.Blake2.X86.CompressS.mem_rd ⟨VG.Proof.Blake2.X86.CompressS.scrR s₀, by simp [hp.wr], contains_addr hd (by omega) hp.scr_fits⟩

theorem loadX_ok {s : State} (heax : s.gpr .eax = VG.Proof.Blake2.X86.CompressS.st s₀) (hesi : s.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block VG.Proof.Blake2.X86.CompressS.loadX) s fun s' =>
      s'.xmm .xmm0 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 0) 128 ∧
      s'.xmm .xmm1 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 16) 128 ∧
      s'.xmm .xmm2 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) 32) 128 ∧
      s'.xmm .xmm3 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) 48) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i0 := VG.Proof.Blake2.X86.CompressS.in_st16 hp hrd hwr (d := 0) (by decide)
  have i16 := VG.Proof.Blake2.X86.CompressS.in_st16 hp hrd hwr (d := 16) (by decide)
  have i32 := VG.Proof.Blake2.X86.CompressS.in_scr16 hp hrd hwr (d := 32) (by decide)
  have i48 := VG.Proof.Blake2.X86.CompressS.in_scr16 hp hrd hwr (d := 48) (by decide)
  apply WP.of_runBlock
  simp only [VG.Proof.Blake2.X86.CompressS.loadX, at_, vOff, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.load128, ea_mk, heax, hesi, i0, i16, i32, i48, ite_true, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial⟩ <;>
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]

/-! ## The output -/

omit hp in
theorem finish_eq : VG.Impl.Blake2.X86.CompressS.finish =
    [.xop (.bin .pxor .xmm0 .xmm2), .xop (.bin .pxor .xmm1 .xmm3),
     .movdquLoad .xmm4 ⟨.eax, 0⟩, .xop (.bin .pxor .xmm0 .xmm4), .movdquStore ⟨.eax, 0⟩ .xmm0,
     .movdquLoad .xmm4 ⟨.eax, 16⟩, .xop (.bin .pxor .xmm1 .xmm4), .movdquStore ⟨.eax, 16⟩ .xmm1] := rfl

theorem finish_ok {v : Work 32} {s : State} (hv : VG.Proof.Blake2.X86.CompressS.Rows v s) (heax : s.gpr .eax = VG.Proof.Blake2.X86.CompressS.st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block VG.Impl.Blake2.X86.CompressS.finish) s fun s' =>
      (∀ k (hk : k < 8), s'.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) 32 =
        v[k] ^^^ v[k + 8] ^^^ s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) 32) ∧
      Frame [VG.Proof.Blake2.X86.CompressS.stR s₀] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have fS := hp.st_fits
  have i0 := VG.Proof.Blake2.X86.CompressS.in_st16 hp hrd hwr (d := 0) (by decide)
  have i16 := VG.Proof.Blake2.X86.CompressS.in_st16 hp hrd hwr (d := 16) (by decide)
  have o0 := VG.Proof.Blake2.X86.CompressS.out_st16 hp hwr (d := 0) (by decide)
  have o16 := VG.Proof.Blake2.X86.CompressS.out_st16 hp hwr (d := 16) (by decide)
  rw [VG.Proof.Blake2.X86.CompressS.finish_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, ea_mk, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, heax, i0, o0, i16, o16, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  -- The 16 bytes at `[st + 16]` are read after the store to `[st]`.
  have sep : ∀ (m : Mem) (x : BitVec 128),
      (m.writeW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 0) x).readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 16) 128 = m.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 16) 128 :=
    fun m x => Mem.readW_writeW_sep (addr_sep (by omega) (by omega) (by omega)) (by decide)
  refine ⟨fun k hk => ?_, ?_, trivial, trivial, trivial⟩
  · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, sep]
    rcases (by omega : k < 4 ∨ 4 ≤ k) with h | h
    · have a : dword (s.xmm .xmm0) k = v[k] := hv.r0 k h
      have c : dword (s.xmm .xmm2) k = v[8 + k] := hv.r2 k h
      rw [Mem.readW_writeW_sep (addr_sep (n := 4) (k := 16) (by omega) (by omega) (by omega)) (by decide),
        show 4 * k = 0 + 4 * k by omega, VG.Proof.Blake2.X86.CompressS.load_write_self _ _ (by omega) h, dword_pxor, dword_pxor,
        VG.Proof.Blake2.X86.CompressS.dword_load _ (by omega) h, a, c]
      simp only [Nat.add_comm 8 k]
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 4 ∧ k = 4 + i := ⟨k - 4, by omega, by omega⟩
      have b : dword (s.xmm .xmm1) i = v[4 + i] := hv.r1 i hi
      have d : dword (s.xmm .xmm3) i = v[12 + i] := hv.r3 i hi
      rw [show 4 * (4 + i) = 16 + 4 * i by omega, VG.Proof.Blake2.X86.CompressS.load_write_self _ _ (by omega) hi, dword_pxor,
        dword_pxor, VG.Proof.Blake2.X86.CompressS.dword_load _ (by omega) hi, b, d]
      simp only [show 4 + i + 8 = 12 + i by omega]
  · have hm := List.mem_singleton_self (VG.Proof.Blake2.X86.CompressS.stR s₀)
    exact ((Frame.refl _ _).writeW hm _ (contains_addr (by decide) (by decide) fS)).writeW hm _
      (contains_addr (by decide) (by decide) fS)

/-! ## Advancing -/

/-- The memory after `advance`. -/
def advMem (m : Mem) (B : BitVec 32) : Mem :=
  ((m.writeW (addr B tloOff) (m.readW (addr B tloOff) 32 + 64)).writeW (addr B thiOff)
    (m.readW (addr B thiOff) 32 + 0 + (BitVec.ofBool
      (decide (2 ^ 32 ≤ (m.readW (addr B tloOff) 32).toNat + (64 : BitVec 32).toNat))).setWidth 32)).writeW
    (addr B nOff) (m.readW (addr B nOff) 32 - 1)

theorem advance_ok {s : State} (hesi : s.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) nOff) 32 - 1 == 0) ∧
      s'.mem = VG.Proof.Blake2.X86.CompressS.advMem s.mem (VG.Proof.Blake2.X86.CompressS.scr s₀) := by
  have fV := hp.scr_fits
  have hr : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 4 := fun d hd =>
    VG.Proof.Blake2.X86.CompressS.mem_rd (hp.in_scr hwr hd)
  have hw : ∀ d, d + 4 ≤ 512 → InRegions s.wr (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 4 := fun d hd => hp.in_scr hwr hd
  have r64 := hr tloOff (by decide)
  have r68 := hr thiOff (by decide)
  have r76 := hr nOff (by decide)
  have w64 := hw tloOff (by decide)
  have w68 := hw thiOff (by decide)
  have w76 := hw nOff (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, advance, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, hesi, r64, r68, r76, w64, w68, w76,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · simp (disch := decide) only [VG.Proof.Blake2.X86.CompressS.rw_scr fV]
  · simp (disch := decide) only [VG.Proof.Blake2.X86.CompressS.rw_scr fV]
    rfl

end

/-- Words 8 to 15 of the work vector, in `scratch` after `ivs`. -/
theorem ivMem_hi {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {m : Mem} {H : VG.Spec.Blake2.HashValue 32} {T : Nat}
    {f : Bool} (hlo : m.readW (addr B tloOff) 32 = BitVec.ofNat 32 T)
    (hhi : m.readW (addr B thiOff) 32 = BitVec.ofNat 32 (T / 2 ^ 32))
    (hf : m.readW (addr B fOff) 32 = VG.Proof.Blake2.X86.CompressS.flagW f) {k : Nat} (hk8 : 8 ≤ k) (hk : k < 16) :
    (VG.Proof.Blake2.X86.CompressS.ivMem m B).readW (addr B (vOff k)) 32 = (VG.Proof.Blake2.X86.CompressS.V0 H T f)[k] := by
  have fV : B.toNat + 64 ≤ 2 ^ 32 := by omega
  rw [VG.Proof.Blake2.X86.CompressS.V0_get _ _ _ k hk]
  simp (disch := omega) only [VG.Proof.Blake2.X86.CompressS.ivMem, VG.Proof.Blake2.X86.CompressS.rw_slot fV]
  rw [hlo, hhi, hf]
  have : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow]
  all_goals rfl

theorem frame_ivMem {B : BitVec 32} (hfit : B.toNat + 64 ≤ 2 ^ 32) (m : Mem) :
    Frame [VG.Proof.Blake2.X86.CompressS.workR B] m (VG.Proof.Blake2.X86.CompressS.ivMem m B) := by
  have ct : ∀ i < 16, (VG.Proof.Blake2.X86.CompressS.workR B).Contains (addr B (vOff i)) (32 / 8) := fun i hi =>
    contains_addr (by simp only [vOff]; omega) (by decide) hfit
  have hm := List.mem_singleton_self (VG.Proof.Blake2.X86.CompressS.workR B)
  simp only [VG.Proof.Blake2.X86.CompressS.ivMem]
  exact (((((((((Frame.refl _ _).writeW hm _ (ct 8 (by omega))).writeW hm _ (ct 9 (by omega))).writeW hm _
    (ct 10 (by omega))).writeW hm _ (ct 11 (by omega))).writeW hm _ (ct 12 (by omega))).writeW hm _
    (ct 13 (by omega))).writeW hm _ (ct 14 (by omega))).writeW hm _ (ct 15 (by omega)))

theorem xor_order (h a b : BitVec 32) : a ^^^ b ^^^ h = h ^^^ a ^^^ b := by
  rw [BitVec.xor_comm _ h, BitVec.xor_assoc]

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressS.nb s₀) {s : State} (hL : VG.Proof.Blake2.X86.CompressS.LInv s₀ i s) :
    WP isa body s fun s' =>
      (VG.X86.eval .ne s' = some false ∧ VG.Proof.Blake2.X86.CompressS.Common s₀ (VG.Proof.Blake2.X86.CompressS.nb s₀) s') ∨
      (VG.X86.eval .ne s' = some true ∧ i + 1 < VG.Proof.Blake2.X86.CompressS.nb s₀ ∧ VG.Proof.Blake2.X86.CompressS.LInv s₀ (i + 1) s') := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have fV64 : (VG.Proof.Blake2.X86.CompressS.scr s₀).toNat + 64 ≤ 2 ^ 32 := by omega
  have a0 : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) 4) 32 = VG.Proof.Blake2.X86.CompressS.st s₀ := hp.arg_frame hL.frame (i := 0) (by decide)
  -- Set up the work vector.
  refine WP.seq ?_
  rw [VG.Proof.Blake2.X86.CompressS.load_eq, WP.block_append_iff]
  refine wp_ldm hL.esp (hp.in_arg hL.rd (by omega) (by omega)) fun s₁ u₁ => ?_
  rw [a0] at u₁
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.ivs_ok hp (by rw [u₁.other _ (by decide), hL.esi]) (by rw [u₁.wr, hL.wr]))
    fun s₃ ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ => ?_
  have f₃ : Frame [VG.Proof.Blake2.X86.CompressS.workR (VG.Proof.Blake2.X86.CompressS.scr s₀)] s.mem s₃.mem := by
    rw [e₇, u₁.mem]; exact VG.Proof.Blake2.X86.CompressS.frame_ivMem fV64 _
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.loadX_ok hp (by rw [e₀, u₁.gpr]) (by rw [e₁, u₁.other _ (by decide), hL.esi])
    (by rw [e₅, u₁.rd, hL.rd]) (by rw [e₆, u₁.wr, hL.wr])) fun s₄ ⟨x0, x1, x2, x3, g₄, m₄, r₄, w₄⟩ => ?_
  have sw : ∀ r ∈ [VG.Proof.Blake2.X86.CompressS.workR (VG.Proof.Blake2.X86.CompressS.scr s₀)], ∃ r' ∈ [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨VG.Proof.Blake2.X86.CompressS.scrR s₀, by simp, by simp at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hrows : VG.Proof.Blake2.X86.CompressS.Rows (VG.Proof.Blake2.X86.CompressS.V0 (VG.Spec.Blake2.stateAt 32 s.mem ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64)) (VG.Proof.Blake2.X86.CompressS.t₀ s₀ + i * 64) (VG.Proof.Blake2.X86.CompressS.fl s₀)) s₄ := by
    have hi8 : ∀ k, 8 ≤ k → (hk : k < 16) → s₃.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) (vOff k)) 32 =
        (VG.Proof.Blake2.X86.CompressS.V0 (VG.Spec.Blake2.stateAt 32 s.mem ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64)) (VG.Proof.Blake2.X86.CompressS.t₀ s₀ + i * 64) (VG.Proof.Blake2.X86.CompressS.fl s₀))[k] := fun k h8 hk => by
      rw [e₇, u₁.mem]
      exact VG.Proof.Blake2.X86.CompressS.ivMem_hi fV hL.tlo hL.thi hL.flag h8 hk
    have hs : s₃.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 0) 128 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 0) 128 ∧
        s₃.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 16) 128 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) 16) 128 := by
      have nd : ∀ d, d + 16 ≤ 32 → ∀ r ∈ [VG.Proof.Blake2.X86.CompressS.workR (VG.Proof.Blake2.X86.CompressS.scr s₀)], Region.Disjoint ⟨addr (VG.Proof.Blake2.X86.CompressS.st s₀) d, 16⟩ r :=
        fun d hd r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          refine (hp.st_scr.sub_left ?_).sub_right (Region.sub_prefix (by omega))
          rw [addr_eq (by omega)]; exact Offset.sub_base _ hd
      exact ⟨f₃.readW (Region.contains_self _ _) (nd 0 (by decide)) (by decide),
        f₃.readW (Region.contains_self _ _) (nd 16 (by decide)) (by decide)⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [VG.Proof.Blake2.X86.CompressS.dw, x0, hs.1, VG.Proof.Blake2.X86.CompressS.dword_load _ (by omega) hk, VG.Proof.Blake2.X86.CompressS.V0_get _ _ _ _ (by omega),
        dite_eq_left (by omega), Nat.zero_add, hp.stateAt_get _ (by omega)]
    · rw [VG.Proof.Blake2.X86.CompressS.dw, x1, hs.2, VG.Proof.Blake2.X86.CompressS.dword_load _ (by omega) hk, VG.Proof.Blake2.X86.CompressS.V0_get _ _ _ _ (by omega),
        dite_eq_left (by omega), hp.stateAt_get _ (by omega), show 4 * (4 + k) = 16 + 4 * k by omega]
    · rw [VG.Proof.Blake2.X86.CompressS.dw, x2, VG.Proof.Blake2.X86.CompressS.dword_load _ (by omega) hk, show 32 + 4 * k = vOff (8 + k) by simp only [vOff]; omega,
        hi8 _ (by omega) (by omega)]
    · rw [VG.Proof.Blake2.X86.CompressS.dw, x3, VG.Proof.Blake2.X86.CompressS.dword_load _ (by omega) hk, show 48 + 4 * k = vOff (12 + k) by simp only [vOff]; omega,
        hi8 _ (by omega) (by omega)]
  -- The rounds.
  have hedi₄ : s₄.gpr .edi = VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i := by rw [g₄, e₂, u₁.other _ (by decide), hL.edi]
  have hmsg₄ : VG.Proof.Blake2.X86.CompressS.Msg (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) (VG.Proof.Blake2.X86.CompressS.blk s₀ i) s₄.mem := hp.msg hi (by rw [m₄]; exact hL.frame.trans (f₃.sub sw))
  have hrd₄ : ∀ j < 16, InRegions (s₄.rd ++ s₄.wr) (addr (VG.Proof.Blake2.X86.CompressS.blkAddr s₀ i) (4 * j)) 4 := by
    rw [r₄, w₄, e₅, e₆, u₁.rd, u₁.wr, hL.rd, hL.wr]; exact hp.blk_rd hi
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.rounds_ok hedi₄ hmsg₄ hrd₄ (s := s₄) ⟨hrows, fun _ _ _ => rfl, rfl, rfl, rfl⟩ 10)
    fun s₅ h₅ => ?_)
  -- The output, and advance.
  have g₅ : ∀ r, r ≠ .ecx → r ≠ .edx → s₅.gpr r = s₃.gpr r := fun r h1 h2 => by rw [h₅.gpr r h1 h2, g₄]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.X86.CompressS.finish_ok hp h₅.rows (by rw [g₅ _ (by decide) (by decide), e₀, u₁.gpr])
    (by rw [h₅.rd, r₄, e₅, u₁.rd, hL.rd]) (by rw [h₅.wr, w₄, e₆, u₁.wr, hL.wr]))
    fun s₆ ⟨o₆, f₆', g₆, r₆, w₆⟩ => ?_
  have hesi₆ : s₆.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀ := by
    rw [g₆, g₅ _ (by decide) (by decide), e₁, u₁.other _ (by decide), hL.esi]
  have hwr₆ : s₆.wr = s₀.wr := by rw [w₆, h₅.wr, w₄, e₆, u₁.wr, hL.wr]
  refine VG.Proof.Blake2.X86.CompressS.advance_ok hp hesi₆ hwr₆ |>.mono fun s₇ ⟨d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈⟩ => ?_
  -- Registers
  have hedi₆ : s₆.gpr .edi = s.gpr .edi := by
    rw [g₆, g₅ _ (by decide) (by decide), e₂, u₁.other _ (by decide)]
  have hesp₆ : s₆.gpr .esp = s.gpr .esp := by
    rw [g₆, g₅ _ (by decide) (by decide), e₃, u₁.other _ (by decide)]
  have hebp₆ : s₆.gpr .ebp = s.gpr .ebp := by
    rw [g₆, g₅ _ (by decide) (by decide), e₄, u₁.other _ (by decide)]
  have hrd : s₇.rd = s₀.rd := by rw [d₅, r₆, h₅.rd, r₄, e₅, u₁.rd, hL.rd]
  have hwr : s₇.wr = s₀.wr := by rw [d₆, hwr₆]
  -- Memory
  have hm₅ : s₅.mem = s₃.mem := by rw [h₅.mem, m₄]
  have f₆ : Frame [VG.Proof.Blake2.X86.CompressS.stR s₀] s₃.mem s₆.mem := by rw [← hm₅]; exact f₆'
  have rA : ∀ d, d + 4 ≤ 512 → d ≠ tloOff → d ≠ thiOff → d ≠ nOff → (d % 4 = 0) →
      s₇.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 = s₆.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 := fun d hd h1 h2 h3 h4 => by
    rw [d₈]; simp only [VG.Proof.Blake2.X86.CompressS.advMem]
    rw [VG.Proof.Blake2.X86.CompressS.rw_scr fV _ _ hd (by decide) (by simp only [nOff] at h3 ⊢; omega),
      VG.Proof.Blake2.X86.CompressS.rw_scr fV _ _ hd (by decide) (by simp only [thiOff] at h2 ⊢; omega),
      VG.Proof.Blake2.X86.CompressS.rw_scr fV _ _ hd (by decide) (by simp only [tloOff] at h1 ⊢; omega)]
  have f₇ : Frame [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀] s₀.mem s₇.mem := by
    rw [d₈]; simp only [VG.Proof.Blake2.X86.CompressS.advMem]
    have hm : VG.Proof.Blake2.X86.CompressS.scrR s₀ ∈ [VG.Proof.Blake2.X86.CompressS.stR s₀, VG.Proof.Blake2.X86.CompressS.scrR s₀] := by simp
    exact (((((hL.frame.trans (f₃.sub sw)).trans (f₆.mono (by simp)))).writeW hm _
      (hp.scr_contains (by decide))).writeW hm _
      (hp.scr_contains (by decide))).writeW hm _ (hp.scr_contains (by decide))
  have hstate : VG.Spec.Blake2.stateAt 32 s₇.mem ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64) =
      Spec.Blake2.F Spec.Blake2.s (VG.Spec.Blake2.stateAt 32 s.mem ((VG.Proof.Blake2.X86.CompressS.st s₀).setWidth 64)) (VG.Proof.Blake2.X86.CompressS.blk s₀ i) (VG.Proof.Blake2.X86.CompressS.t₀ s₀ + i * 64)
        (VG.Proof.Blake2.X86.CompressS.fl s₀) := by
    refine hp.stateAt_ext fun k hk => ?_
    have e7 : s₇.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) 32 = s₆.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) 32 := by
      rw [d₈]; simp only [VG.Proof.Blake2.X86.CompressS.advMem]
      have sep : ∀ d, d + 4 ≤ 512 → Mem.Sep (addr (VG.Proof.Blake2.X86.CompressS.st s₀) (4 * k)) (32 / 8) (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) (32 / 8) :=
        fun d hd => hp.st_scr.sep (hp.st_contains (by omega)) (hp.scr_contains hd)
      rw [Mem.readW_writeW_sep (sep _ (by decide)) (by decide),
        Mem.readW_writeW_sep (sep _ (by decide)) (by decide),
        Mem.readW_writeW_sep (sep _ (by decide)) (by decide)]
    rw [e7, o₆ k hk, hm₅, hp.st_frame f₃ (by omega), ← hp.stateAt_get _ hk, VG.Proof.Blake2.X86.CompressS.F_eq]
    simp only [Vector.getElem_ofFn]
    exact VG.Proof.Blake2.X86.CompressS.xor_order _ _ _
  have hsaved : VG.Proof.Blake2.X86.CompressS.Saved s₀ s₇.mem := by
    have s₆' : VG.Proof.Blake2.X86.CompressS.Saved s₀ s₆.mem :=
      hp.saved_frame (hp.saved_frame hL.saved (.inl f₃)) (.inr f₆)
    exact s₆'.of_readW fun p h => rA _ (by have := VG.Proof.Blake2.X86.CompressS.saved_bound p h; omega) (by revert p h; decide)
      (by revert p h; decide) (by revert p h; decide) (by revert p h; decide)
  have k₆ : ∀ d, 64 ≤ d → d + 4 ≤ 512 → s₆.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 32 :=
    fun d h1 h2 => by
      rw [hp.high_frame (.inr f₆) h1 h2, hp.high_frame (.inl f₃) h1 h2]
  have hcommon : VG.Proof.Blake2.X86.CompressS.Common s₀ (i + 1) s₇ := by
    refine ⟨by rw [d₂, hesi₆], by rw [d₃, hesp₆, hL.esp],
      by rw [d₄, hebp₆, hL.ebp], hrd, hwr, f₇, ?_, hsaved⟩
    rw [hstate, Proof.Blake2.compressBlocks_succ, ← hL.state]
    rfl
  have hnb : VG.Proof.Blake2.X86.CompressS.nb s₀ < 2 ^ 32 := (VG.X86.arg s₀ 2).isLt
  have hc1 : s₆.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) nOff) 32 - 1 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressS.nb s₀ - (i + 1)) := by
    rw [k₆ _ (by decide) (by decide), hL.cnt, ofNat_pred (by omega), Nat.sub_sub]
  have hev : VG.X86.eval .ne s₇ = some (!(BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressS.nb s₀ - (i + 1)) == 0)) := by
    rw [Proof.MdStream.X86.eval_ne, d₇, hc1]; rfl
  by_cases hlast : i + 1 = VG.Proof.Blake2.X86.CompressS.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : VG.Proof.Blake2.X86.CompressS.nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressS.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, ⟨hcommon, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [d₁, hedi₆, hL.edi]
      simp only [VG.Proof.Blake2.X86.CompressS.blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [d₈]; simp only [VG.Proof.Blake2.X86.CompressS.advMem]
      rw [VG.Proof.Blake2.X86.CompressS.rw_scr fV _ _ (by decide) (by decide) (by decide), VG.Proof.Blake2.X86.CompressS.rw_scr fV _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32, k₆ _ (by decide) (by decide), hL.tlo,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
      congr 1; omega
    · rw [d₈]; simp only [VG.Proof.Blake2.X86.CompressS.advMem]
      rw [VG.Proof.Blake2.X86.CompressS.rw_scr fV _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
        k₆ _ (by decide) (by decide), k₆ _ (by decide) (by decide), hL.tlo, hL.thi,
        show ∀ x : BitVec 32, x + 0 = x from fun x => BitVec.add_zero x,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Proof.Blake2.X86.Stream.carry_ofNat _ _ (by decide)]
      congr 2; omega
    · rw [rA _ (by decide) (by decide) (by decide) (by decide) rfl, k₆ _ (by decide) (by decide), hL.flag]
    · rw [d₈]; simp only [VG.Proof.Blake2.X86.CompressS.advMem]
      rw [Mem.readW_writeW_self32, hc1]

end VG.Proof.Blake2.X86.CompressS

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressS.Compress`. -/
section

/-!
# BLAKE2s on x86 (32-bit): the compression function

`correct`: the prologue, the final block flag, the loop over the blocks
(`body_ok`) and the epilogue meet `compressX86 Spec.Blake2.s`; `τ₀`, `agree₀`:
the start of its taint analysis.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (HashValue stateAt compressBlocks)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = .mov .eax (.mem (at_ .esp 28)) :: (Spill.saveCode .eax saved ++
    ([.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)), .mov .eax (.mem (at_ .esp 16)),
      .store (at_ .esi tloOff) .eax, .mov .eax (.mem (at_ .esp 20)), .store (at_ .esi thiOff) .eax,
      .mov .ecx (.imm 0), .mov .eax (.mem (at_ .esp 24)), .alu .test .eax (.reg .eax)] : List Instr)) := rfl

/-- Reading an argument after writing `scratch`. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 512) (he : 4 ≤ e) (he' : e + 4 ≤ 32) :
    (m.writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) v).readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) e) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he') (hp.scr_contains hd)) (by decide)

/-- The memory after the prologue's stores of the registers. -/
abbrev spillMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (VG.Proof.Blake2.X86.CompressS.scr s₀)) s₀.gpr saved

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  ((VG.Proof.Blake2.X86.CompressS.spillMem s₀).writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) tloOff) (VG.X86.arg s₀ 3)).writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) thiOff) (VG.X86.arg s₀ 4)

/-- Reading an argument after saving the registers. -/
theorem spill_arg {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) {e : Nat} (he : 4 ≤ e) (he' : e + 4 ≤ 32) :
    (VG.Proof.Blake2.X86.CompressS.spillMem s₀).readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) e) 32 :=
  Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
    hp.arg_scr.sep (hp.arg_contains he he') (hp.scr_contains (by have := VG.Proof.Blake2.X86.CompressS.saved_bound p h; omega))

theorem save_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀ ∧ s₁.gpr .edi = VG.Proof.Blake2.X86.CompressS.bp s₀ ∧ s₁.gpr .esp = VG.Proof.Blake2.X86.CompressS.esp₀ s₀ ∧
      s₁.gpr .ebp = s₀.gpr .ebp ∧ s₁.gpr .ecx = 0 ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = VG.Proof.Blake2.X86.CompressS.saveMem s₀ ∧ s₁.zf = some (VG.X86.arg s₀ 5 &&& VG.X86.arg s₀ 5 == 0) := by
  have hsa := VG.Proof.Blake2.X86.CompressS.readW_writeW_scr_arg hp
  rw [VG.Proof.Blake2.X86.CompressS.prologue_eq]
  refine wp_ldm rfl (hp.in_arg (s := s₀) rfl (d := 28) (by omega) (by omega)) fun s₁ u₁ => ?_
  refine Spill.save_ok saved (fun p h => by
    rw [u₁.gpr]; exact hp.in_scr u₁.wr (by have := VG.Proof.Blake2.X86.CompressS.saved_bound p h; omega)) fun s₂ u₂ => ?_
  have hm : s₂.mem = VG.Proof.Blake2.X86.CompressS.spillMem s₀ := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have hesp : s₂.gpr .esp = VG.Proof.Blake2.X86.CompressS.esp₀ s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have hrd : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  have hwr : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  refine wp_mov fun s₃ u₃ => ?_
  have hesi : s₃.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀ := by rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl
  refine wp_ldm (by rw [u₃.other _ (by decide), hesp]) (hp.in_arg (by rw [u₃.rd, hrd]) (d := 8) (by omega)
    (by omega)) fun s₄ u₄ => ?_
  refine wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), hesp])
    (hp.in_arg (by rw [u₄.rd, u₃.rd, hrd]) (d := 16) (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_stm (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hesi])
    (hp.in_scr (by rw [u₅.wr, u₄.wr, u₃.wr, hwr]) (by decide)) fun s₆ u₆ => ?_
  refine wp_ldm (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hesp])
    (hp.in_arg (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, hrd]) (d := 20) (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_stm (by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), hesi])
    (hp.in_scr (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, hwr]) (by decide)) fun s₈ u₈ => ?_
  refine wp_movi fun s₉ u₉ => ?_
  have esp₉ : s₉.gpr .esp = VG.Proof.Blake2.X86.CompressS.esp₀ s₀ := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), hesp]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hrd]
  have m₉ : s₉.mem = VG.Proof.Blake2.X86.CompressS.saveMem s₀ := by
    rw [u₉.mem, u₈.mem, u₇.gpr, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.mem, hm,
      hsa _ _ (by decide) (by omega) (by omega), VG.Proof.Blake2.X86.CompressS.spill_arg hp (by omega) (by omega),
      VG.Proof.Blake2.X86.CompressS.spill_arg hp (by omega) (by omega)]; rfl
  refine wp_ldm esp₉ (hp.in_arg rd₉ (d := 24) (by omega) (by omega)) fun s₁₀ u₁₀ =>
    wp_test fun s₁₁ f₁₁ z₁₁ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr,
      u₅.other _ (by decide), u₄.other _ (by decide), hesi]
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr,
      u₅.other _ (by decide), u₄.gpr, u₃.mem, hm, VG.Proof.Blake2.X86.CompressS.spill_arg hp (by omega) (by omega)]; rfl
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), esp₉]
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr]
  · rw [f₁₁.rd, u₁₀.rd, rd₉]
  · rw [f₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, hwr]
  · rw [f₁₁.mem, u₁₀.mem, m₉]
  · rw [z₁₁, u₁₀.gpr, m₉, VG.Proof.Blake2.X86.CompressS.saveMem, hsa _ _ (by decide) (by omega) (by omega),
      hsa _ _ (by decide) (by omega) (by omega), VG.Proof.Blake2.X86.CompressS.spill_arg hp (by omega) (by omega)]; rfl

theorem epilogue_eq : epilogue = Spill.restoreCode .esi ([(.ebx, 80), (.edi, 88)] ++ [(.esi, 84)]) ++ [] := rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) {s : State} (hc : VG.Proof.Blake2.X86.CompressS.Common s₀ (VG.Proof.Blake2.X86.CompressS.nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [VG.Proof.Blake2.X86.CompressS.epilogue_eq]
  refine Spill.restoreBase_ok _ (by decide) (fun p h => by
      rw [hc.esi]; exact VG.Proof.Blake2.X86.CompressS.mem_rd (hp.in_scr hc.wr (by have := VG.Proof.Blake2.X86.CompressS.saved_bound p (by revert p h; decide); omega)))
    (by rw [hc.esi]; exact hc.saved.sub (by decide)) fun s' r' =>
      WP.block_nil ⟨fun r hr => ?_, r'.mem⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact r'.gpr (.ebx, 80) (by decide)
  · exact r'.gpr (.esi, 84) (by decide)
  · exact r'.gpr (.edi, 88) (by decide)
  · rw [r'.other _ (by decide), hc.ebp]
  · rw [r'.other _ (by decide), hc.esp]

/-! ## The final block flag and the count -/

/-- The memory after the flag and the count are stored. -/
def flagMem (s₀ : State) : Mem :=
  ((VG.Proof.Blake2.X86.CompressS.saveMem s₀).writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) fOff) (VG.Proof.Blake2.X86.CompressS.flagW (VG.Proof.Blake2.X86.CompressS.fl s₀))).writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) nOff) (VG.X86.arg s₀ 2)

theorem flag_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) {s : State} (hesi : s.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀)
    (hesp : s.gpr .esp = VG.Proof.Blake2.X86.CompressS.esp₀ s₀) (hecx : s.gpr .ecx = 0) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : s.mem = VG.Proof.Blake2.X86.CompressS.saveMem s₀) (hz : s.zf = some (VG.X86.arg s₀ 5 &&& VG.X86.arg s₀ 5 == 0)) :
    WP isa flag s fun s' =>
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = VG.Proof.Blake2.X86.CompressS.flagMem s₀ ∧
      s'.zf = some (VG.X86.arg s₀ 2 &&& VG.X86.arg s₀ 2 == 0) := by
  have h12 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) 12) 32 = VG.X86.arg s₀ 2 := rfl
  have a12 : (VG.Proof.Blake2.X86.CompressS.saveMem s₀).readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) 12) 32 = VG.X86.arg s₀ 2 := by
    rw [VG.Proof.Blake2.X86.CompressS.saveMem, VG.Proof.Blake2.X86.CompressS.readW_writeW_scr_arg hp _ _ (by decide) (by omega) (by omega),
      VG.Proof.Blake2.X86.CompressS.readW_writeW_scr_arg hp _ _ (by decide) (by omega) (by omega), VG.Proof.Blake2.X86.CompressS.spill_arg hp (by omega) (by omega), h12]
  -- After the flag's `ite`: `ecx` holds it.
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .ecx = VG.Proof.Blake2.X86.CompressS.flagW (VG.Proof.Blake2.X86.CompressS.fl s₀) ∧ s₁.gpr .esi = s.gpr .esi ∧
      s₁.gpr .edi = s.gpr .edi ∧ s₁.gpr .esp = s.gpr .esp ∧ s₁.gpr .ebp = s.gpr .ebp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.mem = s.mem) ?_ fun s₁ ⟨c₁, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ => ?_)
  · refine WP.ite (VG.X86.arg s₀ 5 &&& VG.X86.arg s₀ 5 == 0) (by exact hz) (fun h => ?_)
      (fun h => ?_)
    · refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have h0 : VG.X86.arg s₀ 5 = 0 := by simpa using h
      rw [hecx]; simp [VG.Proof.Blake2.X86.CompressS.flagW, VG.Proof.Blake2.X86.CompressS.fl, h0]
    · refine wp_movi fun s₁ u₁ => WP.block_nil ⟨?_, u₁.other .esi (by decide), u₁.other .edi (by decide),
        u₁.other .esp (by decide), u₁.other .ebp (by decide), u₁.rd, u₁.wr, u₁.mem⟩
      have h0 : VG.X86.arg s₀ 5 ≠ 0 := by simpa using h
      have hf : (VG.X86.arg s₀ 5 != 0) = true := by simpa using h0
      rw [u₁.gpr]; simp only [VG.Proof.Blake2.X86.CompressS.flagW, VG.Proof.Blake2.X86.CompressS.fl, hf, ite_true]; rfl
  · have hin : ∀ d, d + 4 ≤ 512 → InRegions s₁.wr (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) 4 := fun d hd =>
      hp.in_scr (by rw [e₆, hwr]) hd
    refine wp_stm (by rw [e₁, hesi]) (hin fOff (by decide)) fun s₂ u₂ => ?_
    refine wp_ldm (by rw [u₂.gpr, e₃, hesp]) (hp.in_arg (by rw [u₂.rd, e₅, hrd]) (by omega) (by omega))
      fun s₃ u₃ => ?_
    refine wp_stm (by rw [u₃.other _ (by decide), u₂.gpr, e₁, hesi])
      (by rw [u₃.wr, u₂.wr]; exact hin nOff (by decide)) fun s₄ u₄ => ?_
    refine wp_test fun s₅ u₅ hz₅ => WP.block_nil ?_
    have e12 : s₂.mem.readW (addr (VG.Proof.Blake2.X86.CompressS.esp₀ s₀) 12) 32 = VG.X86.arg s₀ 2 := by
      rw [u₂.mem, e₇, hm, VG.Proof.Blake2.X86.CompressS.readW_writeW_scr_arg hp _ _ (by decide) (by omega) (by omega), a12]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₁]
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₂]
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₃]
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₄]
    · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, e₅]
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, e₆]
    · rw [u₅.mem, u₄.mem, u₃.gpr, u₃.mem, e12, u₂.mem, c₁, e₇, hm]; rfl
    · rw [hz₅, u₄.gpr, u₃.gpr, e12]

/-! ## Before the first block -/

theorem flagMem_frame {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) : Frame [VG.Proof.Blake2.X86.CompressS.scrR s₀] s₀.mem (VG.Proof.Blake2.X86.CompressS.flagMem s₀) := by
  have m := List.mem_singleton_self (VG.Proof.Blake2.X86.CompressS.scrR s₀)
  have c : ∀ d, d + 4 ≤ 512 → (VG.Proof.Blake2.X86.CompressS.scrR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) d) (32 / 8) := fun d hd =>
    hp.scr_contains hd
  simp only [VG.Proof.Blake2.X86.CompressS.flagMem, VG.Proof.Blake2.X86.CompressS.saveMem]
  exact ((((Spill.saveMem_frame m _ _ _ _ fun p h => c _ (by have := VG.Proof.Blake2.X86.CompressS.saved_bound p h; omega)).writeW m _
    (c tloOff (by decide))).writeW m _ (c thiOff (by decide))).writeW m _
    (c fOff (by decide))).writeW m _ (c nOff (by decide))

theorem common_zero {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) {s : State} (hesi : s.gpr .esi = VG.Proof.Blake2.X86.CompressS.scr s₀)
    (hesp : s.gpr .esp = VG.Proof.Blake2.X86.CompressS.esp₀ s₀) (hebp : s.gpr .ebp = s₀.gpr .ebp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = VG.Proof.Blake2.X86.CompressS.flagMem s₀) : VG.Proof.Blake2.X86.CompressS.Common s₀ 0 s := by
  have fV := hp.scr_fits
  have hr := VG.Proof.Blake2.X86.CompressS.rw_scr fV
  refine ⟨hesi, hesp, hebp, hrd, hwr, ?_, ?_, ?_⟩
  · rw [hm]; exact (VG.Proof.Blake2.X86.CompressS.flagMem_frame hp).mono (by simp)
  · rw [hm]
    refine hp.stateAt_ext fun k hk => ?_
    rw [(VG.Proof.Blake2.X86.CompressS.flagMem_frame hp).readW (r := VG.Proof.Blake2.X86.CompressS.stR s₀) (hp.st_contains (by omega)) (by
        simp only [List.mem_singleton, forall_eq]; exact hp.st_scr) (by decide),
      ← hp.stateAt_get _ hk]
    rfl
  · have sv := Spill.saveMem_saved_addr (B := VG.Proof.Blake2.X86.CompressS.scr s₀) s₀.mem s₀.gpr VG.Proof.Blake2.X86.CompressS.saved_fits (by omega)
    have w : ∀ {m : Mem} (e : Nat), VG.Proof.Blake2.X86.CompressS.Saved s₀ m → e + 4 ≤ 512 → (∀ p ∈ saved, p.2 + 4 ≤ e ∨ e + 4 ≤ p.2) →
        ∀ v : BitVec 32, VG.Proof.Blake2.X86.CompressS.Saved s₀ (m.writeW (addr (VG.Proof.Blake2.X86.CompressS.scr s₀) e) v) :=
      fun e h he hsep v => h.writeW_addr (w := 32) fV (fun p hp => by have := VG.Proof.Blake2.X86.CompressS.saved_bound p hp; omega) he hsep v
    rw [hm]
    exact w _ (w _ (w _ (w _ sv (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _

theorem linv_zero {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) {s : State} (hc : VG.Proof.Blake2.X86.CompressS.Common s₀ 0 s) (hedi : s.gpr .edi = VG.Proof.Blake2.X86.CompressS.bp s₀)
    (hm : s.mem = VG.Proof.Blake2.X86.CompressS.flagMem s₀) : VG.Proof.Blake2.X86.CompressS.LInv s₀ 0 s := by
  have hr := VG.Proof.Blake2.X86.CompressS.rw_scr hp.scr_fits
  refine ⟨hc, by rw [hedi]; simp [VG.Proof.Blake2.X86.CompressS.blkAddr], ?_, ?_, ?_, ?_⟩ <;> rw [hm] <;>
    simp (disch := decide) only [VG.Proof.Blake2.X86.CompressS.flagMem, VG.Proof.Blake2.X86.CompressS.saveMem, Mem.readW_writeW_self32, hr]
  · simp only [Nat.zero_mul, Nat.add_zero, VG.Proof.Blake2.X86.CompressS.t₀]; exact (Proof.Blake2.X86.Stream.lo_append _ _).symm
  · simp only [Nat.zero_mul, Nat.add_zero, VG.Proof.Blake2.X86.CompressS.t₀]; exact (Proof.Blake2.X86.Stream.hi_append _ _).symm
  · simp [VG.Proof.Blake2.X86.CompressS.nb]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s₀) :
    WP isa VG.Impl.Blake2.X86.CompressS.compress s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Blake2.compressX86 Spec.Blake2.s).post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.save_ok hp) fun s₁ ⟨hesi, hedi, hesp, hebp, hecx, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressS.flag_ok hp hesi hesp hecx hrd hwr hm hz)
    fun s₂ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, hz₂⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.X86.CompressS.Common s₀ (VG.Proof.Blake2.X86.CompressS.nb s₀)) ?_ fun s₃ hc =>
    WP.mono (VG.Proof.Blake2.X86.CompressS.restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show VG.Spec.Blake2.stateAt 32 s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := VG.Proof.Blake2.X86.CompressS.common_zero hp (by rw [e₁, hesi]) (by rw [e₃, hesp]) (by rw [e₄, hebp]) (by rw [e₅, hrd])
    (by rw [e₆, hwr]) e₇
  refine WP.ite (VG.X86.arg s₀ 2 &&& VG.X86.arg s₀ 2 == 0) (by exact hz₂) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Blake2.X86.CompressS.nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [VG.Proof.Blake2.X86.CompressS.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Blake2.X86.CompressS.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Blake2.X86.CompressS.nb s₀ - i ∧ i < VG.Proof.Blake2.X86.CompressS.nb s₀ ∧ VG.Proof.Blake2.X86.CompressS.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (VG.X86.eval .ne s' = some false ∧ VG.Proof.Blake2.X86.CompressS.Common s₀ (VG.Proof.Blake2.X86.CompressS.nb s₀) s') ∨
        (VG.X86.eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Blake2.X86.CompressS.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Blake2.X86.CompressS.nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Blake2.X86.CompressS.nb s₀) s₂
      ⟨0, rfl, hpos, VG.Proof.Blake2.X86.CompressS.linv_zero hp hc₀ (by rw [e₂, hedi]) e₇⟩

/-! ## Constant time -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 512], argLen := 32, argBases := [(4, 0), (28, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.Blake2.X86.CompressS.Pre s) : VG.X86.Taint.Wf VG.Proof.Blake2.X86.CompressS.τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Blake2.X86.CompressS.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Blake2.X86.CompressS.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₁)
    (h₂ : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₂)
    (hpub : (Proof.Blake2.compressX86 Spec.Blake2.s).pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Blake2.X86.CompressS.τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := VG.Proof.Blake2.X86.CompressS.pre_of _ h₁; have hp₂ := VG.Proof.Blake2.X86.CompressS.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Blake2.X86.CompressS.wf₀ hp₁, VG.Proof.Blake2.X86.CompressS.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Blake2.X86.CompressS.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Blake2.X86.CompressS.stR, VG.Proof.Blake2.X86.CompressS.scrR, VG.Proof.Blake2.X86.CompressS.st, VG.Proof.Blake2.X86.CompressS.scr, ha 0 (by omega), ha 6 (by omega)]
  · simp only [VG.Proof.Blake2.X86.CompressS.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

end VG.Proof.Blake2.X86.CompressS

end
