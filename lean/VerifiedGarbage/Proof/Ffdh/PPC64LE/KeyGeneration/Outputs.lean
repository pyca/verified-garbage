module
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Data

import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-! # Zeros at the key-generation controller's outputs (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

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
  have hl2 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 16) 8 := scr.ld (by decide)
  have hno : o.toNat + p.len ≤ 2 ^ 64 := h.input.nowrap (List.mem_append_left _ hr)
  have hout : ∀ i < p.len, InRegions s.wr (off o i) 1 := fun i hi =>
    ⟨⟨o, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact hr,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  simp only [Nat.reduceMul] at hv2
  rcases hj56 with rfl | rfl <;> simp only [Nat.reduceMul] at hv hl <;>
  · unfold zeroOut
    refine WP.seq (WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => t.gpr .r3 = o ∧
        t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
      prun [ldf, h.r31, hl, hl2, hv, hv2]) (by decide)) fun s₁ ⟨⟨h3, h4, h5, hm₁⟩, k₁⟩ => ?_)
    refine WP.mono (Generation.zeroLoop_ok (fun i hi => by rw [k₁.wr]; exact hout i hi) (by omega) (by omega)
      h3 h4 h5) fun t ⟨⟨tb, tout⟩, kt⟩ => ?_
    have hf : ∀ x, (∀ i < p.len, x ≠ o + BitVec.ofNat 64 i) → t.mem x = s.mem x := by
      intro x hx
      rw [tout x (Or.inr ?_), hm₁]
      by_contra hc
      exact hx (x - o).toNat (by simp only [ofs] at hc; omega)
        (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    have kk := k₁.trans kt
    exact ⟨h.restore kk.rd kk.wr kk.sp (fun r hr => kk.gpr r (by revert r hr; decide))
      (zero_frame h.input hr hrc hf), fun i hi => tb i hi, hf⟩

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

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
