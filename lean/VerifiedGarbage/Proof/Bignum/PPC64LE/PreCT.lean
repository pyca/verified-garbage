module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The precomputed values of an RSA modulus on PPC64LE: constant time

`n` is public, but the taint analysis treats memory as secret, so the bytes
of `n` that `check` loads, and its result, are secret to it. Two runs are
related by `Two` (`MontCT.lean`) at each step, both satisfying the same
predicate for the same public data `PD` (which holds `n`'s bytes): after
`check1` it fixes the first byte, which `check2` branches on, and after
`check2` whether `n` is valid, which the final branch tests (`RelCT.ite`).
Each piece is checked by the taint analysis from the registers the
predicate fixes.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute
open VG.Proof.Bignum.PPC64LE

theorem getD_of_lt {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- On entry. -/
def C0 (d : PD) (s : State) : Prop := fnContract.pre s ∧ dataOf s = d

/-- After `loadN`. -/
def C2 (d : PD) (s : State) : Prop :=
  Base d s ∧ Mont.val32 s.mem d.S (slot d.w 0) (2 * d.w) = Spec.Rsa.os2ip d.nb ∧
    (∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.N i) 1) ∧
    ∀ i (h : i < d.nb.length), s.mem (off d.N i) = d.nb[i]

/-- After `check1`. -/
def C3 (d : PD) (s : State) : Prop :=
  Base d s ∧ Mont.val32 s.mem d.S (slot d.w 0) (2 * d.w) = Spec.Rsa.os2ip d.nb ∧
    s.gpr .r15 = BitVec.ofNat 64 (d.nb.getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ (d.nb.getD (d.k - 1) 0).toNat % 2 = 1)

/-- After `check2`. -/
def C4 (d : PD) (s : State) : Prop :=
  Base d s ∧ Mont.val32 s.mem d.S (slot d.w 0) (2 * d.w) = Spec.Rsa.os2ip d.nb ∧
    (s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip d.nb) d.k = true)

/-- After the branch. -/
def C5 (d : PD) (s : State) : Prop := s.gpr .r21 = d.S

theorem base_pins {d : PD} {s₁ s₂ : State} (h₁ : Base d s₁) (h₂ : Base d s₂) :
    ∀ r ∈ baseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r19, h₂.r19]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r5, h₂.r5]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r11, h₂.r11]
  · rw [h₁.r21, h₂.r21]
  · rw [h₁.r6, h₂.r6]
  · rw [h₁.r12, h₂.r12]

theorem pins_C0 : Pins C0 [.r3, .r5, .r6, .r7] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [show s₁.gpr .r3 = d.P from congrArg PD.P h₁, show s₂.gpr .r3 = d.P from congrArg PD.P h₂]
  · rw [show s₁.gpr .r5 = d.N from congrArg PD.N h₁, show s₂.gpr .r5 = d.N from congrArg PD.N h₂]
  · exact BitVec.eq_of_toNat_eq ((congrArg PD.k h₁).trans (congrArg PD.k h₂).symm)
  · rw [show s₁.gpr .r7 = d.S from congrArg PD.S h₁, show s₂.gpr .r7 = d.S from congrArg PD.S h₂]

theorem pins_C1 : Pins C1 baseRegs := fun _ _ _ h₁ h₂ => base_pins h₁.base h₂.base

theorem pins_C2 : Pins C2 baseRegs := fun _ _ _ h₁ h₂ => base_pins h₁.1 h₂.1

theorem pins_C3 : Pins C3 (baseRegs ++ ([.r15, .r18] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact base_pins h₁.1 h₂.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]

theorem pins_C4 {Φ : PD → State → Prop} (h : ∀ d s, Φ d s → C4 d s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => base_pins (h _ _ h₁).1 (h _ _ h₂).1

theorem pins_C5 : Pins C5 [.r21] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂]

/-! ## The steps, by correctness -/

theorem T01 {d : PD} {s : State} (h : C0 d s) : WP isa (.block (Precompute.save ++ setup)) s (C1 d) := by
  obtain ⟨hp, rfl⟩ := h
  exact WP.mono (front_ok hp) fun _ h => h.1

theorem T12 {d : PD} {s : State} (h : C1 d s) : WP isa loadN s (C2 d) := by
  have hb := h.base
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw1 : 8 ≤ d.w := by have := hb.k64; omega
  have e0 : slot d.w 0 = hdrBytes := by simp [slot]
  have e8 : slot d.w 8 = hdrBytes + 8 * (8 * (d.w + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have hZ := hb.hZ
  refine WP.mono (loadN_ok (dA := slot d.w 0) hb.scr hb.r10 (by rw [hb.r12]; simp) hb.r6 hb.r11
    (by have := hb.k64; omega) (by omega) (by have := hb.k1024; omega) (by omega) (by omega) h.rd h.sep)
    fun t ⟨hv, out, k⟩ => ⟨hb.keep k, by rw [hv, h.bytesAt], by rw [k.rd, k.wr]; exact h.rd, fun i hi => ?_⟩
  rw [← h.bytes i hi]
  refine out _ (Or.inr ?_)
  have := h.sep i (by rw [← hb.len]; exact hi) (off d.N i)
  simp only [Mont.ofs, ofs] at this ⊢
  by_contra hc; exact this (by omega) rfl

theorem T23 {d : PD} {s : State} (h : C2 d s) : WP isa (.block check1) s (C3 d) := by
  obtain ⟨hb, hv, hrd, hby⟩ := h
  have hl := hb.len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := d.N) (nb := d.nb) (by rw [hb.r12]; simp) hb.r6 hk hl hrd
    fun i hi => hby i (by omega)) fun t ⟨⟨i0, i15, i18, im⟩, k⟩ =>
    ⟨hb.keep k, by rw [im]; exact hv, by rw [i15, getD_of_lt (by omega)], i18,
      by rw [i0, getD_of_lt (by omega)]⟩

theorem T34 {d : PD} {s : State} (h : C3 d s) : WP isa check2 s (C4 d) := by
  obtain ⟨hb, hv, h15, h18, h0⟩ := h
  have hl := hb.len
  have hk := hb.k64
  refine WP.mono (check2_ok (nb := d.nb) hb.r6 hk hb.k1024 hl (by rw [h0, getD_of_lt (by omega)])
    (by rw [h15, getD_of_lt (by omega)]) h18) fun t ⟨a, m, k⟩ =>
    ⟨hb.keep k, by rw [m]; exact hv, a⟩

theorem TA {d : PD} {s : State} (h : C4 d s ∧ s.gpr .r0 = 0) :
    WP isa (.seq r2 (.seq write (.block [.li .r3 1]))) s (C5 d) := by
  obtain ⟨⟨hb, hv, h0⟩, hz⟩ := h
  have hval := h0.mp hz
  have hf := valid_facts hval hb.k64
  have hnw := hb.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw1 : 8 ≤ d.w := by have := hb.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := hb.k1024; omega
  have e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hZ := hb.hZ
  refine WP.seq (WP.mono (r2_ok hb.scr hb.r8 hb.r9 hb.r10 hb.r5 hb.r11 (by omega) hw' (by omega)
    (by rw [hv]; omega)) fun s₃ ⟨_, _, k₃⟩ => ?_)
  have hb₃ := hb.keep k₃
  refine WP.seq (WP.mono (write_ok (P := d.P) (dN := slot d.w 0) (dX := slot d.w 1) hb₃.scr hb₃.pre
    (by rw [hb₃.r19]; simp) hb₃.r10 hb₃.r5 hb₃.r11 (by omega) hw' (by omega) (by omega) (Nat.le_refl _)
    hb.hPS) fun s₄ ⟨_, k₄⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun _ => True) (by prun; exact ⟨_, rfl⟩) (by decide)) fun t ⟨_, k₅⟩ => ?_
  show t.gpr .r21 = d.S
  rw [k₅.gpr .r21 (by decide), k₄.gpr .r21 (by decide), hb₃.r21]

theorem TB {d : PD} {s : State} (h : C4 d s ∧ s.gpr .r0 ≠ 0) :
    WP isa (.seq zeroPre (.block [.li .r3 0])) s (C5 d) := by
  obtain ⟨⟨hb, -, -⟩, -⟩ := h
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw1 : 8 ≤ d.w := by have := hb.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := hb.k1024; omega
  refine WP.seq (WP.mono (zeroPre_ok hb.pre (by rw [hb.r19]; simp) hb.r11 (by omega) hw' (Nat.le_refl _))
    fun s₃ ⟨_, k₃⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun _ => True) (by prun; exact ⟨_, rfl⟩) (by decide)) fun t ⟨_, k₄⟩ => ?_
  show t.gpr .r21 = d.S
  rw [k₄.gpr .r21 (by decide), k₃.gpr .r21 (by decide), hb.r21]

/-! ## Constant time -/

theorem fn_rel : RelCT isa (Two C0) precompute fun _ _ => True := by
  unfold precompute
  refine RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => T01 h)
    (RelCT.seq ?_ (two_taint _ pins_C5 (by taint_decide)))
  unfold core
  refine RelCT.seq (two_post (two_taint _ pins_C1 (by taint_decide)) fun _ _ h => T12 h)
    (RelCT.seq (R := Two C4) ?_ ?_)
  · unfold check
    exact RelCT.seq (two_post (two_taint _ pins_C2 (by taint_decide)) fun _ _ h => T23 h)
      (two_post (two_taint _ pins_C3 (by taint_decide)) fun _ _ h => T34 h)
  · refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => ?_)
      (RelCT.mono (two_post (Φ := fun d s => C4 d s ∧ s.gpr .r0 = 0)
        (two_taint _ (pins_C4 fun _ _ h => h.1) (by taint_decide)) fun _ _ h => TA h)
        (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun d s => C4 d s ∧ s.gpr .r0 ≠ 0)
        (two_taint _ (pins_C4 fun _ _ h => h.1) (by taint_decide)) fun _ _ h => TB h)
        (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    · rw [eval_zero, eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.2.2, h₂.2.2]
    · rw [eval_zero] at hc
      have h0 : s₁.gpr .r0 = 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, h₂.2.2.mpr (h₁.2.2.mp h0)⟩, hsp⟩
    · rw [eval_zero] at hc
      have h0 : s₁.gpr .r0 ≠ 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.2.2.mpr (h₂.2.2.mp e))⟩, hsp⟩

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub precompute :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, hb, h3, h4, h5, h6, h7, h8⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [(List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp hb, h3, h5, h6, h7, h8]⟩,
      hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.Pre
