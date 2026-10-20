module
public import VerifiedGarbage.Impl.Ffdh.AArch64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Data

import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Live
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Entry

/-! # Zeros at the key-generation controller's outputs (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search

private theorem not_self_disjoint {r : Region} (h : r.Disjoint r) (hl : 0 < r.len) : False :=
  h r.base (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

namespace KeyInput

variable {p : KeyPublic} {original : State}

theorem x_eq (h : KeyInput p original) : inX original = ⟨p.xp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hx1, -, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inX, keyOfState, hx1]

theorem y_eq (h : KeyInput p original) : inY original = ⟨p.yp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hx3, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inY, keyOfState, hx3]

theorem x_mem (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.x_eq]; simp [inWrites]

theorem y_mem (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.y_eq]; simp [inWrites]

theorem x_ne_ctl (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  have d := this.1.2.2.2
  rw [h.x_eq, he] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

theorem y_ne_ctl (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  have d := this.2.1.2.2
  rw [h.y_eq, he] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

theorem xy_disjoint (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.yp, p.len⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.x_eq, ← h.y_eq]
  exact this.1.1

end KeyInput

/-- A zeroing of an output changes memory only there. -/
theorem zero_frame {p : KeyPublic} {original : State} (hinput : KeyInput p original) {m m' : Mem}
    {o : Addr} (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original)
    (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original)
    (hf : ∀ x, (∀ j < p.len, x ≠ o + BitVec.ofNat 64 j) → m' x = m x) :
    Frame (KeyInput.callChanges original) m m' := by
  intro a ha
  apply hf
  intro i hi he
  have hk := hinput.len_lt
  have hin : (⟨o, p.len⟩ : Region) ∈ KeyInput.callChanges original := by
    simp only [inWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [KeyInput.callChanges, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with h' | h' | h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inr (.inr (.inl h')))
    · exact absurd h' hrc
  apply ha _ hin
  rw [he]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])

/-- `zeroOut j`: zeros at the output whose pointer is in word `j`. -/
theorem key_zero_out {p : KeyPublic} {original s : State} {used keys scalars j : Nat} {o : Addr}
    (h : KeyLive p original used keys scalars s) (hj56 : j = 5 ∨ j = 6)
    (hj : (j, o) ∈ p.headers used keys scalars)
    (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original) (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original) :
    WP isa (zeroOut j) s fun t =>
      KeyLive p original used keys scalars t ∧ (∀ i < p.len, t.mem (o + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < p.len, x ≠ o + BitVec.ofNat 64 i) → t.mem x = s.mem x) := by
  have hk := h.input.len_bounds
  have hjl := KeyPublic.headers_index hj
  have scr := h.input.control_scr (t := s) h.wr
  have hv := h.header hj
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv hv2
  have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 (8 * j)) 8 := scr.ld (by omega)
  rcases hj56 with rfl | rfl <;> simp only [Nat.reduceMul] at hv hv2 hl <;>
  · have hl2 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 16) 8 := scr.ld (by decide)
    have hout : ∀ i < p.len, InRegions s.wr (o + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨⟨o, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact hr,
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
    unfold zeroOut
    refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = o + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
      brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl, hl2, hv, hv2]) (by decide) (by decide)
        (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
    refine WP.mono (wp_countdown (N := p.len) (by omega) (by omega) (BInv s₁ o)
      (fun i hi t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
      ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
    have hf : ∀ x, (∀ i < p.len, x ≠ o + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
      fun x hx => by rw [hI.frame x hx, hm₁]
    have kk := k₁.trans hI.keep
    exact ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs
      (zero_frame h.input hr hrc hf), hI.bytes, hf⟩

/-- Zeros at `x` and `y`, which keeps the controller's words. -/
theorem key_zero_outputs {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa zeroOutputs s fun t =>
      KeyLive p original used keys scalars t ∧
      Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have hxw := h.input.x_mem
  have hyw := h.input.y_mem
  have hxc := h.input.x_ne_ctl
  have hyc := h.input.y_ne_ctl
  unfold zeroOutputs
  refine WP.seq (WP.mono (key_zero_out h (j := 5) (.inl rfl) (by simp [KeyPublic.headers]) hxw hxc)
    fun v ⟨hv, hbv, hfv⟩ => ?_)
  refine WP.mono (key_zero_out hv (j := 6) (.inr rfl) (by simp [KeyPublic.headers]) hyw hyc)
    fun t ⟨ht, hbt, hft⟩ => ?_
  have hxy := h.input.xy_disjoint
  have hk64 : p.len < 2 ^ 64 := by omega
  refine ⟨ht, ?_, ?_, ?_⟩
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' := List.mem_range.mp hi
    rw [hft _ (fun j hj he => hxy _ (Offset.contains_base _ (d := i) (n := 1) (by omega) (by omega)) (by
      rw [he]; exact Offset.contains_base _ (d := j) (n := 1) (by omega) (by omega)))]
    exact hbv i hi'
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hbt i (List.mem_range.mp hi)
  · intro j hj
    have hf := (zero_frame h.input hxw hxc hfv).trans (zero_frame h.input hyw hyc hft)
    exact h.input.control_frame hf j hj

end VG.Proof.Ffdh.AArch64.KeyGeneration
