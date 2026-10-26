module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcCall
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Rsa.PrivCheck

import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckFrame
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckLogic
import VerifiedGarbage.Proof.Rsa.Arm.PrivTailContext
import VerifiedGarbage.Proof.Rsa.Arm.PrivStatusPreserved
import VerifiedGarbage.Proof.Rsa.Arm.PrivPdCall
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! # Re-exponentiate, compare, and release only a checked private result -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem check_ok (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} (s : State)
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (check v.pcName v.pc v.pdName v.pd) s fun t => PrivContext g bs t ∧
      t.gpr .r0 = (Rsa.checkResult ((s.gpr .r0).setWidth 64) (bs 0) (bs 1) (bs 2)
        (Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length)).setWidth 32 ∧
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
        (if Rsa.released ((s.gpr .r0).setWidth 64) (bs 0) (bs 1) (bs 2)
            (Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length)
          then Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length else List.replicate g.length 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr g.temporary) g.length = List.replicate g.length 0 ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r12, .lr] s t := by
  unfold check
  refine WP.seq (WP.mono (pcArgs_ok s h slots) ?_)
  rintro s1 ⟨h1, slots1, args1, status1, frame1, rest1⟩
  refine WP.seq (WP.mono (pc_call v h1 slots1 args1) ?_)
  rintro s2 ⟨h2, slots2, frame2, rest2, pc⟩
  refine WP.seq (WP.mono (pdArgs_ok s2 h2 slots2) ?_)
  rintro s3 ⟨h3, slots3, args3, status3, frame3, rest3⟩
  refine WP.seq (WP.mono (pd_call v h3 slots3 args3) ?_)
  rintro s4 ⟨h4, slots4, frame4, rest4, pd⟩
  have bound := h.valid.maxLength
  have fit : g.length < 2 ^ 64 := by omega
  have tempFit : oM + g.length ≤ frameBytes := by simp only [oM, frameBytes]; omega
  have tempPrefix : ∀ r ∈ pdPrefixWrites g, (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint r := by
    rw [temporary_region h.valid]
    exact innerSlice_pdPrefix (by decide) tempFit
  have tempCall : ∀ r ∈ pdWr g ++ [g.calleeRegion], (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint r := by
    rw [temporary_region h.valid]
    exact innerSlice_pdCall h.valid tempFit
  have m3 : Spec.Rsa.bytesAt s3.mem (State.addr g.temporary) g.length =
      Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length := by
    rw [rsa_bytes_frame frame3 fit tempPrefix, rsa_bytes_frame frame2 fit (temporary_pcCall h.valid),
      rsa_bytes_frame frame1 fit (temporary_pcPrefix h.valid)]
  have m4 := (rsa_bytes_frame frame4 fit tempCall).trans m3
  have r1 : s4.mem.readW (off (State.addr g.stack) oR1) 32 = s.gpr .r0 := by
    rw [status_frame frame4 (innerSlice_pdCall h.valid (by decide : oR1 + 4 ≤ frameBytes)),
      status_frame frame3 (statusR1_pdPrefix g), status_frame frame2 (status_pcCall h.valid (by decide))]
    exact status1
  have r3 : s4.mem.readW (off (State.addr g.stack) oR3) 32 = s2.gpr .r0 := by
    rw [status_frame frame4 (innerSlice_pdCall h.valid (by decide : oR3 + 4 ≤ frameBytes))]
    exact status3
  have pre := wordsAt_frame frame3 (by simp only [Spec.Rsa.modulusWords]; omega)
    (precomputation_pdPrefix h.valid)
  have pcBit : match Spec.Rsa.publicPrecompute (bs 0) with
      | some _ => s2.gpr .r0 = 1 | none => s2.gpr .r0 = 0 := by
    cases hp : Spec.Rsa.publicPrecompute (bs 0) <;> simp only [PcOut, hp] at pc ⊢ <;> exact pc.1
  have pdBit : (Spec.Rsa.publicPrecompute (bs 0)).isSome = true →
      match Spec.Rsa.publicOpChecked (bs 0) (bs 1) (Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length) with
      | some y => s4.gpr .r0 = 1 ∧ Spec.Rsa.bytesAt s4.mem (State.addr g.output) g.length = y
      | none => s4.gpr .r0 = 0 := by
    intro somePre
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp somePre
    have pc := pc
    simp only [PcOut, hws] at pc
    have output := pd (bs 0) (h.sources 0).length (by rw [pre, pc.2]; exact hws)
    rw [m3] at output
    cases hp : Spec.Rsa.publicOpChecked (bs 0) (bs 1) (Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length) <;>
      simp only [hp, Spec.Rsa.written] at output ⊢
    · exact output.1
    · exact output
  have logic := check_logic32 (r1 := s.gpr .r0) (r2 := s4.gpr .r0) (r3 := s2.gpr .r0)
    (xb := bs 2) pcBit pdBit
  have accepted : tailAccepted s4 = decide (successBits (s4.gpr .r0) (s.gpr .r0) (s2.gpr .r0) = 1) := by
    unfold tailAccepted
    rw [h4.sp, r1, r3]
  have equal : tailEqual s4 g.output (g.sources 2) g.length =
      decide (Spec.Rsa.bytesAt s4.mem (State.addr g.output) g.length = bs 2) := by
    unfold tailEqual
    have inp : Spec.Rsa.bytesAt s4.mem (State.addr (g.sources 2)) g.length = bs 2 := (h4.sources 2).bytes
    rw [inp]
  refine WP.mono (tail_ok s4 (h4.tailInput slots4)) ?_
  rintro t ⟨status, output, cleared, frame5, rest5⟩
  have bodyFrame := (frame1.sub pcPrefix_sub).trans
    ((frame2.sub (calleeWrites_sub (pcWrites_sub h.valid))).trans
      ((frame3.sub pdPrefix_sub).trans ((frame4.sub (calleeWrites_sub pdWrites_sub)).trans
        (frame5.sub (tailWrites_sub h.valid)))))
  refine ⟨h4.after (frame5.sub (tailWrites_sub h.valid)) rest5, ?_, ?_, cleared, bodyFrame,
    (rest1.mono (by simp)).trans ((rest2.mono (by simp [callClobbers])).trans
      ((rest3.mono (by simp)).trans ((rest4.mono (by simp [callClobbers])).trans rest5)))⟩
  · rw [status, accepted, equal]; exact logic.1
  · rw [output, accepted, equal, m4]
    simp only [Bool.and_eq_true, decide_eq_true_eq, logic.2]
end VG.Proof.Rsa.Arm
