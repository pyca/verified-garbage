module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KTail
public import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KEnd
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Spec.RsaKeyGen
import Mathlib.Algebra.GroupWithZero.Basic
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRound
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-! ### `RsaKeyGen.X86_64.Close`, which only this module used -/

section

/-!
# A candidate on x86-64: too close to `p`

`closeCheck` loads `p` into `aX`, puts `c − p` (with its borrow) in `aAcc`
(`diff_ok`), negates it under the mask of the borrow (`neg_ok`): `|c − p|`;
then compares the bound `2^(64 w − 100)` (`aTmp`, by `setWord`) with it
(`cmpLoop_ok`), and leaves the mask of `|c − p| ≤ 2^(64 w − 100)`, or 0
without `p`, in `rbp` (`closeCheck_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- After `j` words of the negation: the low `j` words negated if `b`, with
the carry in `rbp`. -/
structure NegInv (s₀ : State) (B : Addr) (Z e : Nat) (b : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B e j + 2 ^ (64 * j) * c.toNat =
      if b then 2 ^ (64 * j) - wv s₀.mem B e j else wv s₀.mem B e j

theorem xor_mask_toNat (x : BitVec 64) (b : Bool) :
    (x ^^^ mask b).toNat = if b then 2 ^ 64 - 1 - x.toNat else x.toNat := by
  cases b
  · simp [mask_false]
  · simp only [mask_true, BitVec.xor_allOnes, BitVec.toNat_not, ite_true]

theorem negStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {b : Bool}
    (hsi : s₀.gpr .rsi = off B e) (h15 : s₀.gpr .r15 = mask b) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : NegInv s₀ B Z e b j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .r15), cfFromRbp, .alu .adc .rax (.imm 0),
        .store (ix .rsi .r14) .rax, cfToRbp] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ NegInv s₀ B Z e b (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B e := (hI.keep.gpr (by decide)).trans hsi
  have t15 : t.gpr .r15 = mask b := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (e + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = (word t.mem B (e + 8 * j) ^^^ mask b).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tsi hI.r14, t15, hbp, cf_mask, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj])]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := adc_toNat (word t.mem B (e + 8 * j) ^^^ mask b) (BitVec.signExtend 64 (0 : BitVec 32)) c
    rw [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl, Nat.add_zero] at this
    exact this
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_using [he, hn])) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  rw [hx, xor_mask_toNat] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_using [he, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hj, hn])]
    simp only [wv]
    have hD := wv_lt s₀.mem B e j
    have hxl := (word s₀.mem B (e + 8 * j)).isLt
    have hc1 := Bool.toNat_le c
    have hc1' := Bool.toNat_le c'
    rw [pow64_succ]
    generalize 2 ^ (64 * j) = P at hD hval ⊢
    generalize wv s₀.mem B e j = D at hD hval ⊢
    generalize (word s₀.mem B (e + 8 * j)).toNat = x at hxl hr ⊢
    generalize wv t.mem B e j = V at hval ⊢
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hr hval ⊢
      grind
    · simp only [↓reduceIte] at hr hval ⊢
      have hPx : P * x + P ≤ P * 2 ^ 64 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxl
      have e1 : P * r.toNat + P * 2 ^ 64 * c'.toNat = P * (2 ^ 64 - 1 - x + c.toNat) := by
        rw [Nat.mul_assoc, ← Nat.mul_add, hr]
      have e2 : P * (2 ^ 64 - 1 - x + c.toNat) + P * x + P = P * 2 ^ 64 + P * c.toNat := by
        rw [← Nat.mul_add, ← Nat.mul_succ, ← Nat.mul_add]; congr 1; omega_using [hxl]
      omega_using [hD, hval, e1, e2]

/-- `diffLoop`: `[aAcc] := c − p` (`aN` minus `aX`), its borrow's mask in `rbp`. -/
theorem diff_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (seqs diffLoop) s fun t => ∃ b : Bool, t.gpr .rbp = mask b ∧
      wv t.mem B (slot w aAcc) w + wv s.mem B (slot w aX) w = wv s.mem B (slot w aN) w + 2 ^ (64 * w) * b.toNat ∧
      Outside B (slot w aAcc) (8 * w) s.mem t.mem ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.rax, .rbp, .rsi, .r8, .r10, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  have p1 := slot_sep (w := w) (show aAcc ≠ aN by decide)
  have p2 := slot_sep (w := w) (show aAcc ≠ aX by decide)
  unfold diffLoop
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .r8, .r10, .rsi, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .r10 = off B (slot w aX) ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl (sArr aX) (by decide),
      hl (sArr aAcc) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aX (by decide),
      hg.hdr.harr aAcc (by decide)]) rfl) fun s₁ ⟨⟨h12, h8, h10, hsi, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_using [hw]) hw' (SubInv s₁ B Z (slot w aN) (slot w aX) (slot w aAcc))
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, by rw [k.gpr (by decide)]; exact hbp, by simp [wv]⟩⟩)
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega_using [hw']) (by omega_using [sN]) (by omega_using [sX])
        (by omega_using [sA]) (by omega_using [p1]) (by omega_using [p2]) hj hI))
    fun t hI => ?_
  obtain ⟨b, hb, hv⟩ := hI.val
  rw [hm₁] at hv
  refine ⟨b, hb, hv, by rw [← hm₁]; exact hI.out, (hI.keep.gpr (by decide)).trans h12, (k₁.trans hI.keep).mono (by decide)⟩

/-- `negLoop`: `[aAcc]` negated modulo `2^(64 w)` if `rbp` is the mask of
`true`. -/
theorem neg_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {b : Bool} (hbp : s.gpr .rbp = mask b) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa (seqs negLoop) s fun t =>
      wv t.mem B (slot w aAcc) w = (if b then 2 ^ (64 * w) - wv s.mem B (slot w aAcc) w else wv s.mem B (slot w aAcc) w)
        % 2 ^ (64 * w) ∧
      Outside B (slot w aAcc) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .rsi, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aAcc)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aAcc < 32 by decide); omega_using [hZ, this])
  have sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  unfold negLoop
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .rsi] (Q := fun t => t.gpr .r15 = mask b ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.mem = s.mem) (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hbp, hg.hdr.harr aAcc (by decide)]) rfl)
    fun s₁ ⟨⟨h15, hsi, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_using [hw]) hw' (NegInv s₁ B Z (slot w aAcc) b)
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨b, by rw [k.gpr (by decide), k₁.gpr (by decide)]; exact hbp, by cases b <;> simp [wv]⟩⟩)
    (fun j _ hj t hI => negStep_ok hsi h15 ((k₁.gpr (by decide)).trans h12) (by omega_using [hw']) (by omega_using [sA]) hj hI))
    fun t hI => ?_
  obtain ⟨c, _, hv⟩ := hI.val
  rw [hm₁] at hv
  refine ⟨?_, by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  have hlt := wv_lt t.mem B (slot w aAcc) w
  rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- What `closeCheck` changes: `aX`, `aAcc` and `aTmp`. -/
def closeRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aX, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2))]

/-- `closeRanges`'s ranges, in the header and in the arrays. -/
theorem closeRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w []
    [(1, 1), (2, 1), (3, 1)] (closeRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    closeRanges, Public.aX, Public.aAcc, Public.aTmp, aX, aAcc, aTmp] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩

theorem sxm1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem mask_not (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by cases b <;> decide

/-- The bound: `[aTmp] := 2^(64 w − 100)`, `aTmp`'s word `w − 2` set to `2^28`. -/
theorem bound_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))]) (setWord aTmp .rcx)) s fun t =>
      wv t.mem B (slot w aTmp) w = 2 ^ (64 * w - 100) ∧ Outside B (slot w aTmp) (8 * (w + 2)) s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .r8, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 := hg.scr.ld
      (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.r12, .rcx, .rdx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rcx = BitVec.ofNat 64 (w - 2) ∧ (t.gpr .rdx).toNat = 2 ^ 28 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw, sx2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 : BitVec 64).toNat = 2 from rfl]
    omega_using [hw]) rfl)
    fun s₁ ⟨⟨h12, hcx, hdx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (setWord_ok (hg.scr.congr k₁.2.2) ((k₁.gpr (by decide)).trans hg.rdi) (by rw [hm₁]; exact hg.hdr) hZ h12
    (by omega_using [hw]) hw' (o := aTmp) (by decide) (ri := .rcx) (by decide) (i := w - 2) (by omega_using [hw]) hcx)
    fun t ⟨hv, ho, k⟩ => ⟨?_, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩
  rw [hv, hdx, ← Nat.pow_add]; congr 1; omega_using [hw]

/-- `closeCheck` with `p` (`8 w` octets `pB`): `rbp` the mask of
`|c − p| ≤ 2^(64 w − 100)`. -/
theorem closeInner_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hpl : pB.length = 8 * w) (hsrc : Src s B Z pP pB) :
    WP isa (seqs (([.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr kP)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX)))], loadBE] : List (Prog isa)) ++ diffLoop ++ negLoop ++ ([
      .block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))],
      setWord aTmp .rcx,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aTmp))), .mov .r10 (.mem (hdr (sArr aAcc))),
        .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
      .block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)))) s fun t =>
      t.gpr .rbp = mask (decide (Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) ≤
        2 ^ (64 * w - 100))) ∧
      Good t B Z w minv ∧ Frm B (closeRanges w) s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hw8 : (8 * w + 7) / 8 = w := by omega_using []
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  have sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  have hsl : ∀ r ∈ closeRanges w, r.1 + r.2 ≤ Z := by
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> omega_using [sX, sA, sT]
  have hdisj : ∀ j < 8, j ≠ aX → j ≠ aAcc → j ≠ aTmp → ∀ r ∈ closeRanges w,
      slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj h1 h2 h3 r hr
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_sep h1
    · exact slot_sep h2
    · exact slot_sep h3
  have hhd : ∀ i < 32, ∀ r ∈ closeRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i hi r hr
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Or.inl (hdr_lt_slot w _ hi)
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [negLoop]) ?_
  refine wp_seqs_append (by simp) (by simp [diffLoop]) ?_
  simp only [seqs]
  -- `p` into `aX`.
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rcx, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = pP ∧ t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .rbx = off B (slot w aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl kP (by decide), hl kLen (by decide),
      hl (sArr aX) (by decide), hg.hdr.hw, hP, hK, hg.hdr.harr aX (by decide)]) rfl)
    fun s₁ ⟨⟨h12₁, hsi₁, hcx₁, hbx₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (loadArr_ok (j := aX) hs₁ (by decide) (by rw [hw8]; exact hZ)
    (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hpl (by omega_using [hw]) (by omega_using [hw']) hsi₁ hcx₁
    (by rw [hw8]; exact hbx₁)) fun s₂ ⟨hp₂, ha₂, k₂⟩ => ?_
  rw [hw8] at hp₂ ha₂
  have hf₂ : Frm B (closeRanges w) s.mem s₂.mem := by
    rw [← hm₁]; exact Frm.of_arrays ha₂ fun _ hj => (List.mem_singleton.mp hj) ▸ by simp [closeRanges]
  have hg₂ : Good s₂ B Z w minv := ⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi),
    ha₂.hdr (by rw [hm₁]; exact hg.hdr)⟩
  have hc₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    hf₂.wv_eq (fun r hr => by have := hdisj aN (by decide) (by decide) (by decide) (by decide) r hr; omega_using [this])
        (by omega_using [hn, sN])
  -- `c − p`.
  refine WP.mono (diff_ok hg₂ hZ (by omega_using [hw]) (by omega_using [hw'])) fun s₃ ⟨b, hb₃, hv₃, ho₃, h12₃, k₃⟩ => ?_
  rw [hc₂, hp₂] at hv₃
  have hf₃ : Frm B (closeRanges w) s.mem s₃.mem :=
    hf₂.trans (Frm.of_outside (ho₃.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using []))
        (by simp [closeRanges]))
  have hg₃ : Good s₃ B Z w minv := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.outside hg₂.hdr ho₃ (by unfold slot; omega_using [])⟩
  -- `|c − p|`.
  refine WP.mono (neg_ok hg₃ hZ (by omega_using [hw]) (by omega_using [hw']) hb₃ h12₃) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  have hD := wv_lt s₃.mem B (slot w aAcc) w
  have habs : wv s₄.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) := by
    rw [hv₄, absDiff_of hv₃ hD]
    exact Nat.mod_eq_of_lt (by
      unfold Spec.RsaKeyGen.absDiff
      have := wv_lt s.mem B (slot w aN) w
      have : Spec.Rsa.os2ip pB < 2 ^ (64 * w) := by
        have := os2ip_lt pB; rw [hpl, pow256_eq] at this; rwa [show 8 * (8 * w) = 64 * w by omega_using []] at this
      split <;> omega_arith)
  have hf₄ : Frm B (closeRanges w) s.mem s₄.mem :=
    hf₃.trans (Frm.of_outside (ho₄.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using []))
        (by simp [closeRanges]))
  have hg₄ : Good s₄ B Z w minv := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi,
    Hdr.outside hg₃.hdr ho₄ (by unfold slot; omega_using [])⟩
  -- The bound.
  refine WP.assoc (WP.seq (WP.mono (bound_ok hg₄ hZ hw (by omega_using [hw'])) fun s₅ ⟨hT₅, ho₅, k₅⟩ => ?_))
  have hf₅ : Frm B (closeRanges w) s.mem s₅.mem := hf₄.trans (Frm.of_outside ho₅ (by simp [closeRanges]))
  have hg₅ : Good s₅ B Z w minv := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.outside hg₄.hdr ho₅ (by unfold slot; omega_using [])⟩
  have hA₅ : wv s₅.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) := by
    rw [ho₅.wv (k := w) (by have := slot_sep (w := w) (show aTmp ≠ aAcc by decide); omega_using [this])
        (by omega_using [hn, sA])]; exact habs
  have hl₅ : ∀ i < 32, InRegions (s₅.rd ++ s₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₅.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aTmp) ∧ t.gpr .r10 = off B (slot w aAcc) ∧ t.gpr .rbp = mask false ∧ t.mem = s₅.mem) (by
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hl₅ sW (by decide), hl₅ (sArr aTmp) (by decide), hl₅ (sArr aAcc) (by decide),
      hg₅.hdr.hw, hg₅.hdr.harr aTmp (by decide), hg₅.hdr.harr aAcc (by decide)]) rfl)
    fun s₆ ⟨⟨h12₆, hbx₆, h10₆, hbp₆, hm₆⟩, k₆⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg₅.scr.congr k₆.2.2) hbx₆ h10₆ h12₆ hbp₆ (by omega_using [hw])
      (by omega_using [hw']) (by omega_using [sT])
    (by omega_using [sA])) fun s₇ ⟨hbp₇, hm₇, k₇⟩ => ?_)
  rw [hm₆, hT₅, hA₅] at hbp₇
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!decide (2 ^ (64 * w - 100) <
      Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB))) ∧ t.mem = s₇.mem) (by
    xrun [sxm1, hbp₇, mask_not]) rfl) fun t ⟨⟨hbp, hm⟩, k⟩ => ⟨?_, ⟨hg₅.scr.congr (k.2.2.trans (k₇.2.2.trans k₆.2.2)),
      (k.gpr (by decide)).trans ((k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hg₅.rdi)),
      by rw [hm, hm₇, hm₆]; exact hg₅.hdr⟩, by rw [hm, hm₇, hm₆]; exact hf₅,
      (((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k).mono (by decide)⟩
  rw [hbp, ← decide_not]; simp only [Nat.not_lt]

theorem mask_beq_zero (b : Bool) : (mask b &&& mask b == (0 : BitVec 64)) = !b := by cases b <;> decide

/-- `closeCheck`: ZF set unless the candidate is too close to `p` (none if
`p_len = 0`). -/
theorem closeCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hPl : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length) (hpl : pB.length = 0 ∨ pB.length = 8 * w)
    (hsrc : Src s B Z pP pB) :
    WP isa (seqs closeCheck) s fun t =>
      t.zf = some (!Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w)) ∧
      Good t B Z w minv ∧ Frm B (closeRanges w) s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kPlen)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kPlen < 32 by decide); omega_using [hZ, this])
  have hlen : pB.length < 2 ^ 64 := by omega_using [hw', hpl]
  unfold closeCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.zf = some (decide (pB = [])) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hPl]
    cases pB with
    | nil => rfl
    | cons a l =>
      refine beq_false_of_ne fun h => ?_
      have := congrArg BitVec.toNat h
      rw [BitVec.and_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at this
      exact absurd this (by simp)) rfl)
    fun s₁ ⟨⟨hz₁, hbp₁, hm₁⟩, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w minv := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  have fin : ∀ (t : State) (b : Bool), t.gpr .rbp = mask b →
      b = Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w) →
      Good t B Z w minv → Frm B (closeRanges w) s.mem t.mem →
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
        t'.zf = some (!Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w)) ∧
        Good t' B Z w minv ∧ Frm B (closeRanges w) s.mem t'.mem ∧
        Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t' := by
    intro t b hb hbv hgt hf kt
    refine WP.mono (WP.keep [.rbp] (Q := fun t' => t'.zf = some (!b) ∧ t'.mem = t.mem) (by
      xrun [hb, mask_beq_zero]) rfl)
      fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hbv ▸ hz, ⟨hgt.scr.congr k.2.2, (k.gpr (by decide)).trans hgt.rdi, by rw [hm]; exact hgt.hdr⟩,
        by rw [hm]; exact hf, (kt.trans k).mono (by decide)⟩
  refine WP.seq (WP.ite (!decide (pB = [])) (by simp [eval, hz₁]) (fun he => ?_) (fun he => ?_))
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at he
    have hpl8 : pB.length = 8 * w := hpl.resolve_left (by rw [List.length_eq_zero_iff]; exact he)
    refine WP.mono (closeInner_ok hg₁ hZ hw hw' (by rw [hm₁]; exact hP) (by rw [hm₁]; exact hK) hpl8
      (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁)) fun t ⟨hbp, hgt, hf, kt⟩ =>
      fin t _ hbp ?_ hgt (by rw [hm₁] at hf; exact hf) ((k₁.trans kt).mono (by decide))
    simp only [Spec.RsaKeyGen.otherPrime, he, ↓reduceIte, Spec.RsaKeyGen.tooClose, hm₁]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at he
    refine WP.block_nil (fin s₁ false hbp₁ ?_ hg₁ (by rw [hm₁]; exact Frm.refl _ _ _) (k₁.mono (by decide)))
    simp only [Spec.RsaKeyGen.otherPrime, he, ↓reduceIte, Spec.RsaKeyGen.tooClose]

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.LoadC`, which only this module used -/

section

/-!
# A candidate on x86-64: the candidate

`loadC` sets `w = out_len / 8` and the arrays' bases, loads the first
`out_len` octets of `rand` into `aN`, sets its two top bits and its low bit
(`wv_candidate`), and `used := out_len` (`loadC_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `loadC` changes. -/
def loadCRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (8 * kUsed, 8)]

/-- `loadCRanges`'s ranges, in the header and in the arrays. -/
theorem loadCRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(48, 8), (64, 64), (200, 8)]
    [(0, 1)] (loadCRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    loadCRanges, Public.aN, aN, sFn, sW, sArr, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(0, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)

/-- The head of `loadC`: `w`, the bases, and `rand` and `out_len` into `rsi`
and `rcx`. -/
theorem loadCHead_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot (k / 8) 8 ≤ Z) (hk : k < 2 ^ 31) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k)
    (hR : word s.mem B (8 * kRand) = rp) :
    WP isa (.block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++
      setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) s fun t =>
      t.gpr .rsi = rp ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot (k / 8) aN) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧ (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .r12] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot (k / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := k / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  have hst : InRegions s.wr (off B (8 * sW)) 8 := hs.st (by unfold sW; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r12 = BitVec.ofNat 64 (k / 8) ∧ t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (k / 8))) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl kLen (by decide), hK, hst]
    have : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show k / 8 < 2 ^ 64 by omega_arith)]
    rw [this]; exact ⟨rfl, rfl⟩) rfl) fun t₁ ⟨⟨hcx, h12, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (setBases_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega_arith))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) := by
    rw [ho₂.word (by unfold sW sArr; omega_arith) (by unfold sW; omega_arith), hm₁, word_writeW_self]
  have hR₂ : word t₂.mem B (8 * kRand) = rp := by
    rw [ho₂.word (by unfold kRand sFn sArr; omega_arith) (by unfold kRand sFn; omega_arith), hm₁,
      (writeW_outside s.mem B _ (by unfold sW; omega_arith)).word (by unfold sW kRand sFn; omega_arith) (by unfold kRand sFn; omega_arith), hR]
  have hs₂ := hs.congr (k₂.2.2.trans k₁.2.2)
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = rp ∧ t.gpr .rbx = off B (slot (k / 8) aN) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * kRand) (by unfold kRand sFn; omega_arith),
      hs₂.ld (d := 8 * sArr aN) (by unfold sArr aN; omega_arith), hR₂, hb₂ aN (by decide)]) rfl) fun t ⟨⟨hsi, hbx, hm⟩, k₃⟩ => ?_
  refine ⟨hsi, by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact hcx, hbx, by rw [hm]; exact hW₂,
    fun j hj => by rw [hm]; exact hb₂ j hj, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro x hx
  rw [hm, ho₂ x (hx (8 * sArr 0, 64) (by simp)), hm₁, writeW_outside s.mem B _ (by unfold sW; omega_arith) x (hx (8 * sW, 8) (by simp))]

/-- The candidate's bits, and `used := out_len`. -/
theorem loadCBits_ok {s : State} {B : Addr} {Z w k : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hA : word s.mem B (8 * sArr aN) = off B (slot w aN)) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aN))),
      .movImm64 .rdx (BitVec.ofNat 64 (3 * 2 ^ 62)), .alu .or .rdx (.mem (ix .rbx .r12 (-8))),
      .store (ix .rbx .r12 (-8)) .rdx, .mov .rdx (.mem (at0 .rbx)), .alu .or .rdx (.imm 1), .store (at0 .rbx) .rdx,
      .mov .rax (.mem (hdr kLen)), .store (hdr kUsed) .rax]) s fun t =>
      wv t.mem B (slot w aN) w = Spec.RsaKeyGen.candidate (64 * w) (wv s.mem B (slot w aN) w) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧
      Frm B [(slot w aN, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.rax, .rdx, .rbx, .r12] s t := by
  have hn := hs.nowrap
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hU : 8 * kUsed + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  generalize ht : word s.mem B (slot w aN + 8 * (w - 1)) = top
  generalize hb : word s.mem B (slot w aN) = bot
  have hb₁ : word (s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)) B
      (slot w aN) = bot := by
    rw [← hb]; exact (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)
  have hK₂ : ((s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)).writeW
      (off B (slot w aN)) (bot ||| 1)).readW (off B (8 * kLen)) 64 = BitVec.ofNat 64 k := by
    have hk8 := hdr_lt_slot w aN (show kLen < 32 by decide)
    rw [← hK]
    exact ((writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith))
  refine WP.mono (WP.keep [.rax, .rdx, .rbx, .r12] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)).writeW
        (off B (slot w aN)) (bot ||| 1)).writeW (off B (8 * kUsed)) (BitVec.ofNat 64 k) ∧
      t.gpr .r12 = BitVec.ofNat 64 w) (by
    have e1 := addrm8 (b := off B (slot w aN)) (i := BitVec.ofNat 64 w) rfl rfl (show 1 ≤ w by omega_arith)
    have e2 : off B (slot w aN) + BitVec.ofInt 64 0 = off B (slot w aN) := by
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hW, hA, ix, at0, e1, e2,
      hs.ld (d := slot w aN + 8 * (w - 1)) (by omega_arith), hs.st (d := slot w aN + 8 * (w - 1)) (by omega_arith),
      hs.ld (d := slot w aN) (by omega_arith), hs.st (d := slot w aN) (by omega_arith), ht, hb₁, sx1,
      hl kLen (by decide), hK₂, hs.st (d := 8 * kUsed) (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega_arith)])
    rfl) fun t ⟨⟨hm, h12⟩, k⟩ => ⟨?_, ?_, ?_, h12, k⟩
  · rw [hm, (writeW_outside _ _ _ (by omega_arith)).wv (Or.inr hU) (by omega_arith)]
    refine wv_candidate hw ?_ ?_ ?_
    · rw [word_writeW_self, hb]
    · rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self, ht, BitVec.or_comm]
    · intro j h0 hj
      rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith),
        (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega_arith) x (hx (8 * kUsed, 8) (by simp)),
      writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith)]

/-- `loadC` but its last block: `w`, the bases, and the octets of `c`. -/
theorem loadCFront_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot (k / 8) 8 ≤ Z) (hk1 : 16 ≤ k) (hk : k < 2 ^ 31) (hk8 : k % 8 = 0)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = k) :
    WP isa (.seq (.block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++
      setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) loadBE) s fun t =>
      wv t.mem B (slot (k / 8) aN) (k / 8) = Spec.Rsa.os2ip bs ∧ Scr t B Z ∧ t.gpr .rdi = B ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧ (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      (∀ i, 16 ≤ i → i < 32 → word t.mem B (8 * i) = word s.mem B (8 * i)) ∧
      Frm B (loadCRanges (k / 8)) s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have hw8 : (k + 7) / 8 = k / 8 := by omega_arith
  have sN := Nat.le_trans (slot_le (w := k / 8) (show aN < 8 by decide)) hZ
  have hsl : ∀ r ∈ loadCRanges (k / 8), r.1 + r.2 ≤ Z := by
    have := hdr_lt_slot (k / 8) aN (show kUsed < 32 by decide)
    have := hdr_lt_slot (k / 8) aN (show sW < 32 by decide)
    simp only [loadCRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sArr, sW, kUsed, sFn] at * <;> omega_arith
  refine WP.seq (WP.mono (loadCHead_ok hs hdi hZ hk hK hR) fun t₁ ⟨hsi, hcx, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (loadCRanges (k / 8)) s.mem t₁.mem := hf₁.mono (by simp [loadCRanges])
  refine WP.mono (loadArr_ok (j := aN) hs₁ (by decide) (by rw [hw8]; exact hZ) (hsrc.congrK (InScr.of_frm hf₁' hsl) k₁)
    hbl (by omega_arith) hk hsi hcx (by rw [hw8]; exact hbx)) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_
  rw [hw8] at hv₂ ha₂
  have hf₂ : Frm B (loadCRanges (k / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays ha₂ (fun _ hj => (List.mem_singleton.mp hj) ▸ by simp [loadCRanges]))
  refine ⟨hv₂, hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi),
    by rw [ha₂.hslot (by decide)]; exact hW₁, fun j hj => by rw [ha₂.hslot (by unfold sArr; omega_arith)]; exact hb₁ j hj,
    fun i h1 h2 => ?_, hf₂, (k₁.trans k₂).mono (by decide)⟩
  by_cases h3 : i = kUsed
  · subst h3; rw [ha₂.hslot (by decide)]
    exact hf₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr, kUsed, sFn] <;> omega_arith) (by omega_arith)
  refine hf₂.word_eq (fun r hr => ?_) (by omega_arith)
  have := hdr_lt_slot (k / 8) aN (i := i) (by omega_arith)
  simp only [loadCRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, kUsed, sFn] at * <;> omega_arith

/-- `loadC`: `c` from the first `k` octets of `rand`. -/
theorem loadC_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot (k / 8) 8 ≤ Z) (hk1 : 16 ≤ k) (hk : k < 2 ^ 31) (hk8 : k % 8 = 0)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = k) :
    WP isa (seqs loadC) s fun t =>
      wv t.mem B (slot (k / 8) aN) (k / 8) = Spec.RsaKeyGen.candidate (8 * k) (Spec.Rsa.os2ip bs) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧ word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      Frm B (loadCRanges (k / 8)) s.mem t.mem ∧ t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 (k / 8) ∧
      Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have sN := Nat.le_trans (slot_le (w := k / 8) (show aN < 8 by decide)) hZ
  unfold loadC
  simp only [seqs]
  refine WP.assoc (WP.seq (WP.mono (loadCFront_ok hs hdi hZ hk1 hk hk8 hK hR hsrc hbl)
    fun t₂ ⟨hv₂, hs₂, hdi₂, hW₂, hb₂, hhd, hf₂, k₂⟩ => ?_))
  refine WP.mono (loadCBits_ok (k := k) hs₂ hdi₂ hZ (by omega_arith) (by omega_arith) hW₂ (hb₂ aN (by decide))
    (by rw [hhd kLen (by decide) (by decide)]; exact hK)) fun t ⟨hc, hU, hf, h12, k₃⟩ => ?_
  have hw64 : 64 * (k / 8) = 8 * k := by omega_arith
  refine ⟨by rw [hc, hv₂, hw64], hU, ?_, fun j hj => ?_, hf₂.trans (hf.mono (by simp [loadCRanges])),
    (k₃.gpr (by decide)).trans hdi₂, h12, (k₂.trans k₃).mono (by decide)⟩
  · have h1 := hdr_lt_slot (k / 8) aN (show sW < 32 by decide)
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h1
      · exact Or.inl (by unfold sW kUsed sFn; omega_arith)) (by omega_arith)]; exact hW₂
  · have h1 := hdr_lt_slot (k / 8) aN (show sArr j < 32 by unfold sArr; omega_arith)
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h1
      · exact Or.inl (by unfold sArr kUsed sFn; omega_arith)) (by omega_arith)]; exact hb₂ j hj

end VG.Proof.RsaKeyGen.X86_64

end

end


/-!
# A candidate on x86-64: once `rand` has its octets

`MainCtx`: what `kMainWith` needs from the header and the buffers, and
what its stages keep.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `kMainWith` needs, for the `k` octets of a prime. -/
structure MainCtx (s : State) (B : Addr) (Z k : Nat) (op up eP pP rP : Addr) (eB pB r : List Byte) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot (k / 8) aTab + 2048 ≤ Z
  zx : slot (k / 8) aRm1 + 8 * (k / 8 + 2) ≤ Z
  k1 : 32 ≤ k
  k2 : k ≤ 512
  k8 : k % 8 = 0
  out : word s.mem B (8 * kOut) = op
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 k
  usedP : word s.mem B (8 * kUsedP) = up
  e : word s.mem B (8 * kE) = eP
  elen : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length
  p : word s.mem B (8 * kP) = pP
  plen : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length
  rand : word s.mem B (8 * kRand) = rP
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  esrc : Src s B Z eP eB
  psrc : Src s B Z pP pB
  rsrc : Src s B Z rP r
  el1 : 1 ≤ eB.length
  el8 : eB.length ≤ 8
  pl : pB.length = 0 ∨ pB.length = k
  rl : r.length < 2 ^ 64
  rk : k ≤ r.length
  ou : OutUp s B Z op up k

theorem seg_zero (r : List Byte) (n : Nat) : VG.Proof.RsaKeyGen.seg r 0 n = r.take n := by
  simp [VG.Proof.RsaKeyGen.seg]

/-- A stage past `loadC` keeps the first 26 header words and memory past
the scratch space. -/
theorem stage {B : Addr} {Z : Nat} {m₀ m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (h208 : ∀ r ∈ rs, 208 ≤ r.1) (hrZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (h : (∀ i ≤ 25, word m B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m) :
    (∀ i ≤ 25, word m' B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m' :=
  ⟨fun i hi => (hf.word_eq (fun r hr => Or.inl (by have := h208 r hr; omega_arith)) (by omega_arith)).trans (h.1 i hi),
    h.2.trans (InScr.of_frm hf hrZ)⟩

/-- `finUsed st` ends a candidate. -/
theorem finUsed_end {s sX : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} (hs : Scr sX B Z)
    (hdi : sX.gpr .rdi = B) (h8 : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hu : word sX.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word sX.mem B (8 * kUsedP) = up) (ho : OutUp sX B Z op up k)
    (hlo : ∀ i < 6, word sX.mem B (8 * i) = word s.mem B (8 * i)) (hhi : InScr B Z s.mem sX.mem)
    (kk : Keep mmRegs s sX) :
    WP isa (finUsed st) sX fun t => KEnd s t B Z op up k st u none :=
  WP.mono (finUsed_ok hs hdi h8 hst hu hU ho.upw ho.upZ) fun _ h =>
    (KEnd.of_fin ho h).trans_pre hlo (fun x hx => hhi x hx) kk ho.outZ

/-- What `kMainWith`'s frames need of the ranges `closeCheck` changes. -/
theorem closeRanges_fr (w : Nat) : (∀ r ∈ closeRanges w, 208 ≤ r.1) ∧ (∀ r ∈ closeRanges w, r.1 + r.2 ≤ slot w 8) ∧
    (∀ r ∈ closeRanges w, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) ∧
    (∀ r ∈ closeRanges w, r.1 + r.2 ≤ slot w aTab + 2048) := by
  have hs : VG.Proof.RsaKeyGen.SlotShape w (closeRanges w) [] [aX, aAcc, aTmp] := fun r hr => by
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨_, .head _, rfl⟩, .inr ⟨_, .tail _ (.head _), rfl⟩, .inr ⟨_, .tail _ (.tail _ (.head _)), rfl⟩]
  exact ⟨hs.geD rfl rfl, hs.leD rfl rfl, hs.apartW rfl rfl,
    fun r hr => Nat.le_trans (hs.leD (a := aTab) rfl rfl r hr) (Nat.le_add_right _ _)⟩

/-- The same for the ranges the trial division changes. -/
theorem trialRanges_fr (w : Nat) :
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)], 208 ≤ r.1) ∧
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)], r.1 + r.2 ≤ slot w aTab + 2048) ∧
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) :=
  ⟨by rng_le, by rng_le, by rng_disj⟩

/-- The same for the ranges the gcd check changes. -/
theorem gcdRanges_fr (w : Nat) :
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], 208 ≤ r.1) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], r.1 + r.2 ≤ slot w 8) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], r.1 + r.2 ≤ slot w aTab + 2048) := by
  have hs : VG.Proof.RsaKeyGen.SlotShape w [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] [(8 * kG, 8)] [aX] :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr ⟨_, .head _, rfl⟩, .inl (.head _)]
  exact ⟨hs.geD rfl rfl, hs.leD rfl rfl, hs.apartW rfl rfl,
    fun r hr => Nat.le_trans (hs.leD (a := aTab) rfl rfl r hr) (Nat.le_add_right _ _)⟩

/-- The header words `kMainWith` keeps across `loadC`. -/
theorem loadCRanges_hdr (w : Nat) : ∀ i ∈ [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen],
    ∀ r ∈ loadCRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have h : ∀ i ∈ [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen], 8 * i + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(48, 8), (64, 64), (200, 8)] : List (Nat × Nat)), 8 * i + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * i := by
    decide
  exact fun i hi => VG.Proof.RsaKeyGen.hdr_of_shape (loadCRanges_shape w) (h i hi).1 (h i hi).2

end VG.Proof.RsaKeyGen.X86_64
