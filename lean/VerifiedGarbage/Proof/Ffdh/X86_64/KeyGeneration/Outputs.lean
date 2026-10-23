module
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Layout
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut

/-! # Zeros at the key-generation controller's outputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64.Generation (controller_zero_out)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

private theorem not_self_disjoint {r : Region} (h : r.Disjoint r) (hl : 0 < r.len) : False :=
  h r.base (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

namespace KeyInput

variable {p : KeyPublic} {original : State}

theorem len_lt (h : KeyInput p original) : p.len < 2 ^ 31 := by
  have := h.len_bounds.2; omega

private theorem output (h : KeyInput p original) {s : State} (hw : s.wr = original.wr)
    {r : Region} (hr : r ∈ inWrites original) (hrc : r ≠ inCtl original) {o : Addr}
    (hro : r = ⟨o, p.len⟩) : OutOk s p.control 128 o p.len := by
  have hk := h.len_lt
  have hpw := h.writes_pairwise
  have hd : (inCtl original).Disjoint r := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    simp only [inWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hpw.1.2.2.2.symm
    · exact hpw.2.1.2.2.symm
    · exact hpw.2.2.1.2.symm
    · exact hpw.2.2.2.1.symm
    · exact absurd rfl hrc
  have hc : p.control = (inCtl original).base := by rw [← h.2]; rfl
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [hw, h.1.2.2.2.1]
    exact ⟨r, hr, by rw [hro]; exact contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  · intro i hi
    rw [hc]
    exact out_scr (by rw [hro] at hd; exact hd.symm) (contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk]))

theorem output_x (h : KeyInput p original) {s : State} (hw : s.wr = original.wr) :
    OutOk s p.control 128 p.xp p.len := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, -, -, -, -, -, -⟩ := h.1
  refine h.output hw (r := inX original) (by simp [inWrites]) (fun he => ?_) ?_
  · have := h.writes_pairwise
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at this
    exact not_self_disjoint (r := inCtl original) (by rw [he] at this; exact this.1.2.2.2) (by show 0 < 128; decide)
  · rw [← h.2]; simp only [inX, keyOfState, hrsi]

theorem output_y (h : KeyInput p original) {s : State} (hw : s.wr = original.wr) :
    OutOk s p.control 128 p.yp p.len := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrcx, -, -, -, -, -⟩ := h.1
  refine h.output hw (r := inY original) (by simp [inWrites]) (fun he => ?_) ?_
  · have := h.writes_pairwise
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at this
    exact not_self_disjoint (r := inCtl original) (by rw [he] at this; exact this.2.1.2.2) (by show 0 < 128; decide)
  · rw [← h.2]; simp only [inY, keyOfState, hrcx]

theorem x_mem (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ∈ inWrites original := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, -, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp [inWrites, inX, keyOfState, hrsi]

theorem y_mem (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ∈ inWrites original := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrcx, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp [inWrites, inY, keyOfState, hrcx]

theorem x_ne_ctl (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, -, -, -, -, -, -⟩ := h.1
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  have hx : inX original = ⟨p.xp, p.len⟩ := by rw [← h.2]; simp only [inX, keyOfState, hrsi]
  have d := this.1.2.2.2
  rw [hx, he] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

theorem y_ne_ctl (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrcx, -, -, -, -, -⟩ := h.1
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  have hy : inY original = ⟨p.yp, p.len⟩ := by rw [← h.2]; simp only [inY, keyOfState, hrcx]
  have d := this.2.1.2.2
  rw [hy, he] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

theorem xy_disjoint (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.yp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := h.1
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.2]
  simpa only [inX, inY, keyOfState, hrsi, hrcx] using this.1.1

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
  exact contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk])

/-- A zeroing that keeps the loop state. -/
theorem zero_live {p : KeyPublic} {original s t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {o : Addr} (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original)
    (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original)
    (hf : ∀ x, (∀ j < p.len, x ≠ o + BitVec.ofNat 64 j) → t.mem x = s.mem x)
    (k : Keep [.rsi, .rcx, .rax] s t) : KeyLive p original used keys scalars t :=
  h.restore k.2.1 k.2.2 (fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (zero_frame h.input hr hrc hf)

end VG.Proof.Ffdh.X86_64.KeyGeneration
