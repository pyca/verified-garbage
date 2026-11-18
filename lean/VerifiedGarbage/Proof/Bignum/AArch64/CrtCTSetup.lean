module

import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.CrtKey
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.CrtKey
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFix
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import Mathlib.Algebra.GroupWithZero.Nat
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import Mathlib.Algebra.GroupWithZero.Nat

/-! ### `Bignum.AArch64.CrtCTSetupChk`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtCTSetupFix`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time of a prime's fixes

`primeFix` in a prime's workspace (`primeFix_ct`): the mask's load reads
`n`'s header through the workspace's link, pinned by correctness; the
masking loop runs from the array's base and `w_X`, the low word's fix from
the array's base, and `-X⁻¹` and the number 1 from `x0`. What each piece
keeps and changes (`pf1_ok` to `pf4_ok`) gives `primeFix_frm`, what
`primeFix` changes whatever the mask and the prime.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `minv` changes only its registers, whatever `x3`. -/
theorem minv_keep (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.minv) s fun t => Keep [.x4, .x5, .x6, .x15] s t ∧ t.mem = s.mem :=
  WP.mono (WP.keep [.x4, .x5, .x6, .x15] (Q := fun t => t.mem = s.mem)
    (by brun [VG.Impl.Bignum.AArch64.minv, newton]) (by decide) (by decide) (by decide +kernel))
    fun _ ⟨h, k⟩ => ⟨k, h⟩

/-- The low word's fix: its base, then the fix. -/
def fixA : List Instr :=
  [movi .x4 3, .logic .and .x .x5 .x15 .x4, .logic .eor .x .x5 .x5 .x4, ldh .x16 (sArr Public.aN)]

def fixB : List Instr := [ld .x3 .x16, .logic .orr .x .x3 .x3 .x5, st .x3 .x16]

theorem fixLow_eq : fixLow = fixA ++ fixB := rfl

/-! ## The pieces' correctness -/

theorem pf1_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block fixMask) s fun t => SubCtx t B Z o w wx minv ∧ word t.mem (off B o) (8 * sMaskX) = mask c ∧
      Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem ∧ Keep [.x5] s t := by
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (fixMask_ok hc hM) fun t ⟨hm, k⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * sMaskX) (mask c) (by decide)
  rw [← hm] at o₁
  have f₁ : Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem := Frm.of_outside o₁ (by simp)
  exact ⟨hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMaskX sFn; omega_arith) k.wr
    (k.gpr .x0 (by decide)), by rw [hm]; exact word_writeW_self _ _ _ _, f₁, k⟩

theorem pf2_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hm : word s.mem (off B o) (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr Public.aN)) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  refine WP.mono (maskArr_ok hc.good (Nat.le_refl _) hw hw' (by decide) hm) fun t ⟨_, _, ho, _, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k.wr
    (k.gpr .x0 (by decide)), f, k⟩

theorem pfA_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv) :
    WP isa (.block fixA) s fun t => t.gpr .x16 = off B (o + slot wx Public.aN) ∧ t.mem = s.mem ∧
      Keep [.x4, .x5, .x16] s t :=
  WP.mono (WP.keep [.x4, .x5, .x16] (Q := fun t => t.gpr .x16 = off B (o + slot wx Public.aN) ∧ t.mem = s.mem)
    (by brun [fixA, hc.x0, hdr_enc (sArr_lt (show Public.aN < 8 by decide)),
      hc.ld' (sArr_lt (show Public.aN < 8 by decide)), hc.harr' (show Public.aN < 8 by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, hm⟩, k⟩ => ⟨h16, hm, k⟩

/-- A prime's workspace context after a store of its `-X⁻¹`. -/
theorem SubCtx.setMinv {s t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem.writeW (off (off B o) (8 * sMinv)) v)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx v := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8x := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hh : ∀ k < 32, k ≠ sMinv → word t.mem (off B o) (8 * k) = word s.mem (off B o) (8 * k) := fun k hk hne => by
    rw [hm]; exact hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hne)
  have hb : ∀ k < 32, word t.mem B (8 * k) = word s.mem B (8 * k) := fun k hk => by
    rw [hm, off_off]
    exact (writeW_outside s.mem B (d := o + 8 * sMinv) v (by unfold sMinv; omega_arith)).word
      (Or.inl (by unfold sMinv; omega_arith)) (by omega_arith)
  exact ⟨h.scr.congr hwr, h0.trans h.x0, ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw,
    by rw [hm]; exact word_writeW_self _ _ _ _,
    fun j hj => (hh _ (by unfold sArr; omega_arith) (by unfold sArr sMinv; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), hlo, hi⟩

theorem pf3_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (h16 : s.gpr .x16 = off B (o + slot wx Public.aN)) :
    WP isa (.block (fixB ++ VG.Impl.Bignum.AArch64.minv ++ fixTail)) s fun t =>
      SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) ∧ t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hd : o + slot wx Public.aN + 8 ≤ Z := by omega_arith
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (c := .block fixB) (Q := fun t =>
      ∃ v : BitVec 64, t.mem = s.mem.writeW (off B (o + slot wx Public.aN)) v) (by
    brun [fixB, h16, hc.scr.ld hd, hc.scr.st hd]; exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨v, hm₁⟩, k₁⟩ => ?_
  rw [← off_off] at hm₁
  have o₁ := writeW_outside s.mem (off B o) (d := slot wx Public.aN) v (by omega_arith)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₁.wr
    (k₁.gpr .x0 (by decide))
  refine WP.mono (minv_keep s₁) fun s₂ ⟨k₂, hm₂⟩ => ?_
  have hc₂ := hc₁.mem hm₂ k₂ (by decide)
  have hs₂ := hc₂.good.scr
  have hW : ∀ v : BitVec 64, word (s₂.mem.writeW (off B (o + 8 * sMinv)) v) B (o + 8 * sW) =
      BitVec.ofNat 64 wx := fun v => by
    rw [← off_off, ← word_off, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hc₂.hdr.hw
  refine WP.mono (WP.keep [.x9, .x12, .x13] (c := .block fixTail) (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.mem = s₂.mem.writeW (off (off B o) (8 * sMinv)) (s₂.gpr .x15)) (by
    rw [off_off]
    brun [fixTail, hc₂.x0, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hc₂.st' (show sMinv < 32 by decide), hc₂.ld' (show sW < 32 by decide), hW])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h12, h13, hm₃⟩, k₃⟩ => ?_
  have o₃ := writeW_outside s₂.mem (off B o) (d := 8 * sMinv) (s₂.gpr .x15) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm (off B o) [(8 * sMinv, 8)] s₂.mem t.mem := Frm.of_outside o₃ (by simp)
  have K := (k₁.trans k₂).trans k₃
  refine ⟨hc₂.setMinv (by rw [hm₃, word_writeW_self]) k₃.wr (k₃.gpr .x0 (by decide)), h12, h13, ?_,
    K.mono (by decide)⟩
  rw [hm₂] at f₃
  exact (f₁.append f₃).mono fun r hr => by simpa using hr

theorem pf4_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31) (h12 : s.gpr .x12 = BitVec.ofNat 64 wx)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 0) :
    WP isa (setWord Public.aOne) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem ∧ Keep [.x7, .x8, .x14, .x16] s t := by
  have h0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aOne < 8 by decide)
  refine WP.mono (setWord_ok hc.good.scr hc.x0 hc.hdr (Nat.le_refl _) h12 hw' (o := Public.aOne) (by decide)
    (i := 0) (by omega_arith) h13) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) k.wr
    (k.gpr .x0 (by decide)), f, k⟩

/-- What `primeFix` changes, whatever the mask and the prime. -/
def pfRanges (wx : Nat) : List (Nat × Nat) :=
  [(8 * sMaskX, 8), (slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8), (slot wx Public.aOne, 8 * (wx + 2))]

theorem primeFix_eq' : primeFix = ([.block fixMask] : List (Prog isa)) ++ (maskArr Public.aN ++
    ([.block (fixA ++ (fixB ++ VG.Impl.Bignum.AArch64.minv ++ fixTail)), setWord Public.aOne] : List (Prog isa))) := by
  rw [primeFix_eq, fixLow_eq]; simp only [List.append_assoc]

theorem primeFix_frm {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 31) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      Frm (off B o) (pfRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [primeFix_eq']
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  refine WP.mono (pf1_ok hc hM) fun s₁ ⟨hc₁, hm₁, f₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (pf2_ok hc₁ hw hw' hm₁) fun s₂ ⟨hc₂, f₂, k₂⟩ => ?_
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pfA_ok hc₂) fun s₃ ⟨h16, hm₃, k₃⟩ => ?_
  have hc₃ := hc₂.mem hm₃ k₃ (by decide)
  refine WP.mono (pf3_ok hc₃ h16) fun s₄ ⟨hc₄, h12₄, h13₄, f₄, k₄⟩ => ?_
  refine WP.mono (pf4_ok hc₄ hw hw' h12₄ h13₄) fun t ⟨hc₅, f₅, k₅⟩ => ⟨_, hc₅, ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  rw [hm₃] at f₄
  exact (((f₁.append f₂).append f₄).append f₅).mono fun r hr => by
    simp only [pfRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h]

/-! ## Constant time -/

/-- `primeFix`'s hypotheses: a prime's workspace (some `-X⁻¹`), and the
modulus' mask (some value). -/
def PF (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    word s.mem p.B (8 * Public.sMask) = mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the mask's load. -/
def PF1 (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    word s.mem (off p.B p.o) (8 * sMaskX) = mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the masking. -/
def PF2 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the low word's base. -/
def PFA (p : XPub) (s : State) : Prop := PF2 p s ∧ s.gpr .x16 = off p.B (p.o + slot p.wx Public.aN)

/-- After `-X⁻¹`. -/
def PF3 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ s.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .x13 = BitVec.ofNat 64 0

/-- `setWord`'s registers. -/
def PF4 (p : XPub) (s : State) : Prop :=
  s.gpr .x8 = off p.B (p.o + slot p.wx Public.aOne) ∧ s.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .x13 = BitVec.ofNat 64 0

theorem fixMask_ct : RelCT isa (Two PF) (.block fixMask) fun _ _ => True := by
  unfold fixMask
  refine RelCT.block_append (l₁ := ([ldh .x5 sLink] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => PF p t ∧ t.gpr .x5 = p.B) [.x0]
      (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, _, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide) ?_)
    (two_taint [.x0, .x5] (pins_of (fun (p : XPub) r => if r = .x0 then off p.B p.o else p.B)
      fun p s ⟨⟨_, _, hc, _⟩, h5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.x0
        · exact h5) (by taint_decide)))
  rintro p s ⟨minv, c, hc, hM, h1, h2⟩
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B ∧ t.mem = s.mem)
    (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h5, hm⟩, k⟩ => ⟨⟨minv, c, hc.mem hm k (by decide), hm ▸ hM, h1, h2⟩, h5⟩

/-- `primeFix` is constant time. -/
theorem primeFix_ct : RelCT isa (Two PF) (seqs primeFix) fun _ _ => True := by
  rw [primeFix_eq']
  refine RelCT.seqs_append (by simp) (by simp [maskArr]) (RelCT.seq (two_post (Ψ := PF1) fixMask_ct
    fun p s ⟨minv, c, hc, hM, h1, h2⟩ => WP.mono (pf1_ok hc hM) fun t ⟨hc', hm, _⟩ =>
      ⟨minv, c, hc', hm, h1, h2⟩) ?_)
  refine RelCT.seqs_append (by simp [maskArr]) (by simp) (RelCT.seq (two_post (Ψ := PF2)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (maskArr_ct (by decide) (by taint_decide)))
    fun p s ⟨minv, c, hc, hm, h1, h2⟩ => WP.mono (pf2_ok hc (by omega_arith) h2 hm) fun t ⟨hc', _⟩ =>
      ⟨minv, hc', h1, h2⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := PFA) [.x0]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide)
    fun p s h => by
      obtain ⟨minv, hc, h1, h2⟩ := h
      exact WP.mono (pfA_ok hc) fun t ⟨h16, hm, k⟩ => ⟨⟨minv, hc.mem hm k (by decide), h1, h2⟩, h16⟩)
    (two_piece (Ψ := PF3) [.x0, .x16]
      (pins_of (fun (p : XPub) r => if r = .x0 then off p.B p.o else off p.B (p.o + slot p.wx Public.aN))
        fun p s ⟨⟨_, hc, _⟩, h16⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.x0
          · exact h16) (by taint_decide)
      fun p s ⟨⟨_, hc, _⟩, h16⟩ => WP.mono (pf3_ok hc h16) fun t ⟨hc', h12', h13, _⟩ =>
        ⟨_, hc', h12', h13⟩))) ?_
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := PF4) [.x0]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide) ?_)
    (two_taint [.x8, .x12, .x13] (pins_of (fun (p : XPub) r => if r = .x8 then
      off p.B (p.o + slot p.wx Public.aOne) else if r = .x12 then BitVec.ofNat 64 p.wx else BitVec.ofNat 64 0)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨_, hc, h12, h13⟩
  exact WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.B (p.o + slot p.wx Public.aOne))
    (by brun [hc.x0, hdr_enc (sArr_lt (show Public.aOne < 8 by decide)),
      hc.ld' (sArr_lt (show Public.aOne < 8 by decide)), hc.harr' (show Public.aOne < 8 by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13⟩

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: constant time of the checks' pieces

Between the pieces of `checks`, what they read from the headers (`CK`: the
modulus' header, the primes' workspaces' bases, links, sizes and arrays, and
a mask in `sMask`) is kept by their frames. Each piece is constant time from
`CK` and `x0` (`pq_ct`, `eq_ct`, `qinv_ct`, `fixP_ct`, …).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- What the checks keep. -/
def CK (p : ChecksPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ word t.mem p.B (8 * sWsP) = off p.B p.op ∧
    word t.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsF t.mem p.B p.op p.wp ∧ WsF t.mem p.B p.oq p.wq ∧
    (∃ c, word t.mem p.B (8 * Public.sMask) = mask c) ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wp 8 + wsTab p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w

/-- `CK` with `x0` at `f p`. -/
def CKr (f : ChecksPub → Addr) (p : ChecksPub) (t : State) : Prop := CK p t ∧ t.gpr .x0 = f p

theorem pins_ckr (f : ChecksPub → Addr) : Pins (CKr f) [.x0] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem CK.bounds {p : ChecksPub} {t : State} (h : CK p t) :
    p.B.toNat + p.Z ≤ 2 ^ 64 ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
      p.op + slot p.wp 8 + wsTab p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
      p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w :=
  let ⟨hs, _, _, _, _, _, _, b⟩ := h; ⟨hs.nowrap, b⟩

/-- A change above the modulus' header, keeping the primes' workspaces. -/
theorem CK.frm {p : ChecksPub} {t t' : State} (h : CK p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 256 ≤ r.1) (hP : WsF t'.mem p.B p.op p.wp) (hQ : WsF t'.mem p.B p.oq p.wq) {regs : List Reg}
    (k : Keep regs t t') : CK p t' := by
  obtain ⟨hs, hH, hWP, hWQ, -, -, ⟨c, hM⟩, b⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have hw : ∀ i < 32, word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith)) (by omega_arith)
  exact ⟨hs.congr k.wr, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega_arith)).trans (hH.harr j hj)⟩, (hw _ (by decide)).trans hWP,
    (hw _ (by decide)).trans hWQ, hP, hQ, ⟨c, (hw _ (by decide)).trans hM⟩, b⟩

theorem CK.mem {p : ChecksPub} {t t' : State} (h : CK p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : CK p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (hm ▸ h.2.2.2.2.1) (hm ▸ h.2.2.2.2.2.1) k

/-- A change in the accumulators. -/
theorem CK.acc {p : ChecksPub} {t t' : State} (h : CK p t)
    (ho : Outside p.B (slot p.w Public.aAcc) (8 * (2 * p.w + 2)) t.mem t'.mem) {regs : List Reg}
    (k : Keep regs t t') : CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have hA := accs_le p.w
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h0 := hdr_lt_slot p.w Public.aAcc (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(slot p.w Public.aAcc, 8 * (2 * p.w + 2))]) ho (by simp)
  have hr : ∀ r ∈ [(slot p.w Public.aAcc, 8 * (2 * p.w + 2))], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_arith
  exact h.frm f (fun r hr' => by rw [List.mem_singleton.mp hr']; simp only; omega_arith)
    (h.2.2.2.2.1.frm f (fun r hr' => Or.inr (hr r hr')) (by omega_arith))
    (h.2.2.2.2.2.1.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith)) k

/-- A change of the mask. -/
theorem CK.newMask {p : ChecksPub} {t t' : State} (h : CK p t) (ho : Outside p.B (8 * Public.sMask) 8 t.mem t'.mem)
    (hM : ∃ c, word t'.mem p.B (8 * Public.sMask) = mask c) {regs : List Reg} (k : Keep regs t t') : CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(8 * Public.sMask, 8)]) ho (by simp)
  have hr : ∀ r ∈ [(8 * Public.sMask, 8)], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; unfold Public.sMask sFn; simp only; omega_arith
  obtain ⟨hs, hH, hWP, hWQ, hP, hQ, -, b⟩ := h
  have hw : ∀ i < 32, i ≠ Public.sMask → word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi hne =>
    ho.word (by unfold Public.sMask sFn at hne ⊢; omega_arith) (by omega_arith)
  exact ⟨hs.congr k.wr, ⟨(hw _ (by decide) (by decide)).trans hH.hw, (hw _ (by decide) (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega_arith) (by unfold sArr Public.sMask sFn; omega_arith)).trans (hH.harr j hj)⟩,
    (hw _ (by decide) (by decide)).trans hWP, (hw _ (by decide) (by decide)).trans hWQ,
    hP.frm f (fun r hr' => Or.inr (hr r hr')) (by omega_arith),
    hQ.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith), hM, b⟩

theorem ChecksPre.ck {p : ChecksPub} {s : State} (h : ChecksPre p s) : CKr (·.B) p s := by
  obtain ⟨mp, mq, P, Q, QI, m0, hg, a1, a2, b1, b2, b3, c1, c2, c3, c4, hsP, hsQ, hwsP, hwsQ, -, hM, -⟩ := h
  exact ⟨⟨hg.scr, hg.hdr, hsP, hsQ, ⟨hwsP.link, hwsP.hdr.hw, hwsP.hdr.harr⟩, ⟨hwsQ.link, hwsQ.hdr.hw, hwsQ.hdr.harr⟩,
    ⟨m0, hM⟩, a1, a2, b1, b2, b3, c1, c2, c3, c4⟩, hg.x0⟩

theorem CK.good {p : ChecksPub} {t : State} (h : CK p t) (hdi : t.gpr .x0 = p.B) : Good t p.B p.Z p.w p.minv :=
  ⟨h.1, hdi, h.2.1⟩

theorem CK.slotZ {p : ChecksPub} {t : State} (h : CK p t) : slot p.w 8 ≤ p.Z := by
  obtain ⟨-, -, h28, hlo, hop, hoq, -⟩ := h.bounds; omega_arith

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem CK.move {p : ChecksPub} {s : State} (h : CK p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .x0 = X) (hi : i < 32) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8)
    (hw : word s.mem X (8 * i) = A') :
    WP isa (.block [ldh .x0 i]) s (CKr (fun _ => A') p) :=
  WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = A' ∧ t.mem = s.mem)
    (by brun [hdi, hdr_enc hi, hl, hw]) rfl rfl rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

theorem CK.ldB {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 :=
  h.1.ld (by have := h.slotZ; have := hdr_lt_slot p.w 8 hi; omega_arith)

theorem CK.ldP {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off (off p.B p.op) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact (h.1.sub (o := p.op) (n := slot p.wp 8) (by omega_arith) (by omega_arith)).ld (by omega_arith)

theorem CK.ldP' {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off p.B (p.op + 8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact h.1.ld (by omega_arith)

/-- `p`'s workspace. -/
abbrev ckP (p : ChecksPub) : Addr := off p.B p.op
/-- `q`'s workspace. -/
abbrev ckQ (p : ChecksPub) : Addr := off p.B p.oq

theorem enterP_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterP]) s (CKr ckP p) :=
  h.1.move (X := p.B) (i := sWsP) h.2 (by decide) (h.1.ldB (by decide)) h.1.2.2.1

theorem enterQ_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterQ]) s (CKr ckQ p) :=
  h.1.move (X := p.B) (i := sWsQ) h.2 (by decide) (h.1.ldB (by decide)) h.1.2.2.2.1

theorem leaveP_ck {p : ChecksPub} {s : State} (h : CKr ckP p s) : WP isa (.block [leave]) s (CKr (·.B) p) :=
  h.1.move (X := ckP p) (i := sLink) h.2 (by decide) (h.1.ldP (by decide)) h.1.2.2.2.2.1.1

/-! ## `p q` -/

theorem CKr.rows {p : ChecksPub} {s : State} (h : CKr (·.B) p s) :
    RowsPre Public.aN ⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ s := by
  obtain ⟨⟨hs, hH, hWP, hWQ, hP, hQ, -, -, -, hlo, hop, hoq, -⟩, hdi⟩ := h
  exact ⟨hs, hdi, hH.harr _ (by decide), hWP, hWQ, by rw [← word_off]; exact hP.2.1,
    by rw [← word_off]; exact hQ.2.1, by rw [← word_off, hP.2.2 _ (by decide), off_off],
    by rw [← word_off, hQ.2.2 _ (by decide), off_off], by decide, hlo, by dsimp only; omega_arith, by dsimp only; omega_arith⟩

theorem pq_ct : RelCT isa (Two (CKr (·.B))) (seqs pqProduct) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · rw [pqProduct_eq]
    refine RelCT.seqs_append (by simp [zeroAccs]) (by simp) (RelCT.seq (two_post (Ψ := CKr (·.B))
      (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => ⟨p.minv, h.1.good h.2, h.1.slotZ⟩)
        zeroAccs_ct) fun p s h => ?_) ?_)
    · obtain ⟨hn, -, h28, -⟩ := h.1.bounds
      exact WP.mono (zeroAccs_ok (h.1.good h.2) h.1.slotZ (by omega_arith)) fun t ⟨_, ho, k⟩ =>
        ⟨h.1.acc ho k, (k.gpr .x0 (by decide)).trans h.2⟩
    · exact two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ : RowsPub))
        (fun p s h => h.rows) (rows_ct (by taint_decide))
  · obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, a3, a4⟩ := h.1.bounds
    have hR := h.rows
    exact WP.mono (pqProduct_ok (h.1.good h.2) (by omega_arith) hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1
      hR.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.2.1 hlo hop hoq (show 1 ≤ p.wp by omega_arith) a2 (show 1 ≤ p.wq by omega_arith) a4)
      fun t ⟨_, ho, k⟩ => ⟨h.1.acc ho k, (k.gpr .x0 (by decide)).trans h.2⟩

/-! ## `p q = n` -/

/-- `eqCheck`'s registers. -/
def EQ1 (p : ChecksPub) (t : State) : Prop :=
  t.gpr .x0 = p.B ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x14 = BitVec.ofNat 64 p.w ∧
    t.gpr .x16 = off p.B (slot p.w Public.aAcc) ∧ t.gpr .x17 = off p.B (slot p.w Public.aN)

theorem eq_ct : RelCT isa (Two (CKr (·.B))) (seqs eqCheck) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · unfold eqCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := EQ1) [.x0] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (two_taint [.x0, .x12, .x14, .x16, .x17] (pins_of (fun (p : ChecksPub) r => if r = .x0 then p.B else
        if r = .x12 then BitVec.ofNat 64 p.w else if r = .x14 then BitVec.ofNat 64 p.w else
        if r = .x16 then off p.B (slot p.w Public.aAcc) else off p.B (slot p.w Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1
          · exact h.2.2.2.2) (by taint_decide))
    obtain ⟨hk, hdi⟩ := h
    have hH := hk.2.1
    exact WP.mono (WP.keep [.x9, .x12, .x14, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.w ∧
        t.gpr .x14 = BitVec.ofNat 64 p.w ∧ t.gpr .x16 = off p.B (slot p.w Public.aAcc) ∧
        t.gpr .x17 = off p.B (slot p.w Public.aN))
      (by brun [hdi, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show Public.aAcc < 8 by decide)),
        hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hk.ldB (i := sW) (by decide),
        hk.ldB (i := sArr Public.aAcc) (by decide), hk.ldB (i := sArr Public.aN) (by decide), hH.hw,
        hH.harr Public.aAcc (by decide), hH.harr Public.aN (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨h', k⟩ => ⟨(k.gpr .x0 (by decide)).trans hdi, h'⟩
  · obtain ⟨hn, a1, a2, -⟩ := h.1.bounds
    obtain ⟨c, hM⟩ := h.1.2.2.2.2.2.2.1
    exact WP.mono (eqCheck_ok (h.1.good h.2) h.1.slotZ (by omega_arith) (by omega_arith)) fun t ⟨hM', ho, k⟩ =>
      ⟨h.1.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr .x0 (by decide)).trans h.2⟩

/-! ## `qInv < p` -/

/-- `qinvCheck`'s registers. -/
def QI1 (p : ChecksPub) (t : State) : Prop :=
  CKr ckP p t ∧ t.gpr .x12 = BitVec.ofNat 64 p.wp ∧ t.gpr .x14 = BitVec.ofNat 64 p.wp ∧
    t.gpr .x16 = off p.B (p.op + slot p.wp aChunk) ∧ t.gpr .x17 = off p.B (p.op + slot p.wp Public.aN) ∧
    t.c = true

theorem qinvCheck_eq : qinvCheck = [
    .block [ldh .x12 sW, ldh .x16 (sArr aChunk), ldh .x17 (sArr Public.aN), movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7],
    cmpLoop,
    .block ((borrowMask ++ [ldh .x5 sLink]) ++ ([ldw .x3 .x5 Public.sMask, .logic .and .x .x15 .x15 .x3,
      stw .x15 .x5 Public.sMask] : List Instr))] := rfl

theorem qinv_ct : RelCT isa (Two (CKr ckP)) (seqs qinvCheck) (Two (CKr ckP)) := by
  refine two_post ?_ fun p s h => ?_
  · rw [qinvCheck_eq]
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := QI1) [.x0] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (RelCT.seq (two_post (Ψ := CKr ckP) (two_taint [.x12, .x14, .x16, .x17] (pins_of (fun (p : ChecksPub) r =>
        if r = .x12 then BitVec.ofNat 64 p.wp else if r = .x14 then BitVec.ofNat 64 p.wp else
        if r = .x16 then off p.B (p.op + slot p.wp aChunk) else off p.B (p.op + slot p.wp Public.aN))
        fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1
          · exact h.2.2.2.2.1) (by taint_decide)) fun p s h => ?_)
      (RelCT.block_append (RelCT.seq
        (two_piece (Ψ := fun p t => t.gpr .x5 = p.B) [.x0] (pins_ckr _) (by taint_decide) fun p s h => ?_)
        (two_taint [.x5] (pins_of (fun p _ => p.B) fun p s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)))))
    · obtain ⟨hk, hdi⟩ := h
      have hF := hk.2.2.2.2.1
      have h0 : s.gpr .x0 = off p.B p.op := hdi
      have hw : word s.mem p.B (p.op + 8 * sW) = BitVec.ofNat 64 p.wp := by rw [← word_off]; exact hF.2.1
      have ha : ∀ j < 8, word s.mem p.B (p.op + 8 * sArr j) = off p.B (p.op + slot p.wp j) := fun j hj => by
        rw [← word_off, hF.2.2 j hj, off_off]
      exact WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.wp ∧
          t.gpr .x14 = BitVec.ofNat 64 p.wp ∧ t.gpr .x16 = off p.B (p.op + slot p.wp aChunk) ∧
          t.gpr .x17 = off p.B (p.op + slot p.wp Public.aN) ∧ t.c = true ∧ t.mem = s.mem)
        (by brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aChunk < 8 by decide)),
          hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hk.ldP' (i := sW) (by decide),
          hk.ldP' (i := sArr aChunk) (by decide), hk.ldP' (i := sArr Public.aN) (by decide), hw,
          ha aChunk (by decide), ha Public.aN (by decide)])
        (by decide) (by decide) (by decide +kernel))
        fun t ⟨⟨a, b, c, d, e, hm⟩, k⟩ => ⟨⟨hk.mem hm k, (k.gpr .x0 (by decide)).trans hdi⟩, a, b, c, d, e⟩
    · obtain ⟨⟨hk, hdi⟩, h12, h14, h16, h17, hc⟩ := h
      obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
      have := slot_le (w := p.wp) (show aChunk < 8 by decide)
      have := slot_le (w := p.wp) (show Public.aN < 8 by decide)
      exact WP.mono (cmpLoop_ok hk.1 h16 h17 h14 hc (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
        fun t ⟨_, hm, k⟩ => ⟨hk.mem hm k, (k.gpr .x0 (by decide)).trans hdi⟩
    · obtain ⟨hk, hdi⟩ := h
      have h0 : s.gpr .x0 = off p.B p.op := hdi
      have hL : word s.mem p.B (p.op + 8 * sLink) = p.B := by rw [← word_off]; exact hk.2.2.2.2.1.1
      exact WP.mono (WP.keep [.x4, .x5, .x15] (Q := fun t => t.gpr .x5 = p.B)
        (by brun [borrowMask, h0, hdr_enc (show sLink < 32 by decide), hk.ldP' (i := sLink) (by decide), hL])
        (by decide) (by decide) (by decide +kernel))
        fun t h => h.1
  · obtain ⟨hk, hdi⟩ := h
    obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    obtain ⟨c, hM⟩ := hk.2.2.2.2.2.2.1
    have hF := hk.2.2.2.2.1
    exact WP.mono (qinvCheck_ok hk.1 hdi (hdr_any hF.2.1 hF.2.2) (by omega_arith)
      (by unfold Public.sMask sFn; unfold slot hdrBytes at hlo; omega_arith) (by omega_arith) (by omega_arith) hF.1)
      fun t ⟨hM', ho, k⟩ => ⟨hk.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr .x0 (by decide)).trans hdi⟩

/-! ## The fixes -/

theorem pfRanges_le (wx : Nat) : ∀ r ∈ pfRanges wx, 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  intro r hr
  simp only [pfRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith

theorem CK.sub {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .x0 = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) :
    ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z o p.w wx minv ∧ word s.mem p.B (8 * Public.sMask) = mask c := by
  obtain ⟨hs, hH, -, -, -, -, ⟨c, hM⟩, -⟩ := hk
  exact ⟨_, c, ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hi_of_wsTab hhi⟩, hM⟩

theorem CK.pf {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .x0 = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ p.Z) (h2 : 2 ≤ wx) (hwx : wx ≤ p.w) :
    PF ⟨p.B, p.Z, o, p.w, wx⟩ s := by
  have := hk.bounds
  obtain ⟨m, c, hc, hM⟩ := hk.sub hdi hF hlo hhi
  exact ⟨m, c, hc, hM, h2, by simp only; omega_arith⟩

theorem fixP_ct : RelCT isa (Two (CKr ckP)) (seqs primeFix) (Two (CKr ckP)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.op, p.w, p.wp⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.1 hlo (by omega_arith) a1 a2) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.1 hlo (by omega_arith)
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := pfRanges_le p.wp
  refine WP.mono (primeFix_frm hc hM (by omega_arith) (by omega_arith)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith
  have hr' : ∀ r ∈ shiftRanges p.op (pfRanges p.wp), p.op + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.op + slot p.wp 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega_arith
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega_arith) ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩
    (hk.2.2.2.2.2.1.frm f' (fun r h => Or.inr (by have := hr' r h; omega_arith)) (by omega_arith)) k, hc'.x0⟩

theorem fixQ_ct : RelCT isa (Two (CKr ckQ)) (seqs primeFix) (Two (CKr ckQ)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.oq, p.w, p.wq⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.2.1 (by omega_arith) hoq a3 a4) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.2.1 (by omega_arith) hoq
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := pfRanges_le p.wq
  refine WP.mono (primeFix_frm hc hM (by omega_arith) (by omega_arith)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith
  have hr' : ∀ r ∈ shiftRanges p.oq (pfRanges p.wq), p.oq + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.oq + slot p.wq 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega_arith
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega_arith)
    (hk.2.2.2.2.1.frm f' (fun r h => Or.inl (by have := hr' r h; omega_arith)) (by omega_arith))
    ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩ k, hc'.x0⟩

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: constant time of the setup and the checks

The claims of `CrtCTDefs.lean` for the primes' setup: the loads
(`loadArr_ct_pN`, `loadArr_ct_pI`, `loadArr_ct_qN`, in `CrtCTSetupLoad.lean`),
`primesSetup` (`setup_ct`, in `CrtCTSetupWs.lean`), and `checks`
(`checks_ct`) and `checksGiven` (`checksGiven_ct`), from their pieces
(`CrtCTSetupChk.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem leaveEnterQ_ck : RelCT isa (Two (CKr ckP)) (.block [leave, enterQ]) (Two (CKr ckQ)) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := CKr (·.B)) [.x0] (pins_ckr _) (by taint_decide) fun p s h => leaveP_ck h)
      (two_piece [.x0] (pins_ckr _) (by taint_decide) fun p s h => enterQ_ck h))

/-- `checksGiven`, from the checks' state. -/
theorem checksGiven_ck : RelCT isa (Two (CKr (·.B))) (seqs checksGiven) fun _ _ => True := by
  unfold checksGiven
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq (two_piece [.x0] (pins_ckr _)
    (by taint_decide) fun p s h => enterP_ck h) ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq qinv_ct ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq fixP_ct ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq leaveEnterQ_ck ?_)
  refine RelCT.seqs_append (by decide) (by decide) (RelCT.seq fixQ_ct ?_)
  exact two_taint [.x0] (pins_ckr _) (by taint_decide)

theorem checksGiven_ct : ChecksCTOf checksGiven := two_map id (fun _ _ h => h.ck) checksGiven_ck

theorem checks_ct : ChecksCT := by
  unfold ChecksCT ChecksCTOf checks
  simp only [List.append_assoc]
  refine two_map id (fun _ _ h => h.ck) ?_
  refine RelCT.seqs_append (by decide) (by simp [checksGiven]) (RelCT.seq pq_ct ?_)
  exact RelCT.seqs_append (by decide) (by simp [checksGiven]) (RelCT.seq eq_ct checksGiven_ck)

end VG.Proof.Bignum.AArch64
