module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! # The refillable-tape search's end on x86-64

`finish`: the words written to `used` and `state` for each way the
controller ended (`results`), the parameters or zeros at `out`
(`finishOutput`), and the status returned (`returnStatus`). -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

/-! ## The output and the status -/

theorem returnStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa Impl.Dsa.X86_64.Generation.Refill.returnStatus s fun t =>
      t.gpr .rax = (if W 19 = 2 then 3 else W 19) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  unfold Impl.Dsa.X86_64.Generation.Refill.returnStatus
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = W 19 ∧ t.zf = some (W 19 == 2) ∧
    t.mem = s.mem) ?_ rfl) fun u ⟨⟨ra, zu, mu⟩, ku⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := 152) (by decide), R.slot (d := 152) (k := 19) rfl (by decide) rfl]
    rw [sub_beq_zero]
  by_cases h2 : W 19 = 2
  · refine WP.ite true (by simp only [eval, zu, h2, beq_self_eq_true]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 3 ∧ t.mem = u.mem) (by xrun; rfl) rfl)
      fun t ⟨⟨rt, mt⟩, kt⟩ => ⟨by rw [rt, if_pos h2], mt.trans mu, (ku.trans kt).mono (by decide)⟩
  · refine WP.ite false (by simp only [eval, zu, beq_eq_false_iff_ne.mpr h2]) (fun hh => Bool.noConfusion hh)
      (fun _ => WP.block_nil ⟨by rw [ra, if_neg h2], mu, ku⟩)

/-- `finishOutput` then `returnStatus`, for any status. -/
theorem finishTail_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (expected : Option Spec.Dsa.Params)
    (result : (W 19 ≠ 1 ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)) :
    WP isa (.seq Impl.Dsa.X86_64.Generation.finishOutput Impl.Dsa.X86_64.Generation.Refill.returnStatus) s fun t =>
      t.gpr .rax = (if W 19 = 2 then 3 else W 19) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        (expected.map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen)).getD
          (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame [⟨p.geo.F, frameBytes⟩, ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧
      t.gpr .rsp = s.gpr .rsp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : 0 < p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  obtain ⟨V, R⟩ := h.rep
  apply WP.seq
  unfold Impl.Dsa.X86_64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  have hwu : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ u.wr := by rw [ku.2.2]; exact hw
  rcases result with ⟨h19, he⟩ | ⟨h19, a, he, bytes⟩
  · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr h19])
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    unfold Impl.Dsa.X86_64.Generation.outputZero
    refine WP.seq (WP.mono (zeroArgs_ok mu.layout Ru) fun u₁ ⟨L₁, R₁, f₁, k₁⟩ => ?_)
    refine WP.seq (WP.mono (zeroOut_ok L₁ R₁ (by simp [upd, h6]) (by simpa [upd] using h7) (by omega) (by omega)
      (by rw [k₁.2.2]; exact hwu) o.bound o.apart) fun u₂ ⟨L₂, k₂, R₂, _, bytes₂, f₂⟩ => ?_)
    refine WP.mono (returnStatus_ok L₂ R₂) fun t ⟨rt, mt, kt⟩ => ?_
    refine ⟨by simpa [upd] using rt, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mt, he]; exact bytes₂
    · rw [mt, ← hm]
      exact (f₁.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp)).trans
        (f₂.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp))
    · rw [kt.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), ku.gpr (by decide)]
    · rw [kt.2.1, k₂.2.1, k₁.2.1, ku.2.1]
    · rw [kt.2.2, k₂.2.2, k₁.2.2, ku.2.2]
  · refine WP.ite true (by simp only [eval, hz, h19, beq_self_eq_true])
      (fun _ => ?_) (fun impossible => Bool.noConfusion impossible)
    have bytesu : Spec.Rsa.bytesAt u.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := hm ▸ bytes
    refine WP.seq (WP.mono (output_copy_context mu o hwu _ (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytesu)
      fun u₁ ⟨_, bt, f₁, k₁⟩ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    have R₁ : Rep u₁.mem p.geo.F p.geo.hash Vu W := Ru.apart o.apart f₁
    have L₁ := lay_of_rep mu.layout Ru R₁ rfl (k₁.gpr (by decide)) k₁.2.2
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 1 ∧ t.mem = u₁.mem) (by xrun; rfl) rfl)
      fun u₂ ⟨⟨_, m₂⟩, k₂⟩ => ?_)
    sorry

end VG.Proof.Dsa.X86_64.Generation.Refill
