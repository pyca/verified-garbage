module

public import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepare
import VerifiedGarbage.Proof.Bignum.Arm.InlineMontgomery
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! The public byte count selects normalized setup only where the shaped
candidate guarantees a nonzero highest radix word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm

theorem candidatePrepareChoice_ok (s : State) {base src : BitVec 32} {len k : Nat}
    (h : PrepareInput base src len k s)
    (normalized : k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
    WP isa (.block VG.Impl.Ffdh.Arm.CandidatePrepare.choose) s fun v =>
      PrepareInput base src len k v ∧
      (k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (State.addr src) k)) ∧
      v.z = decide (k % 8 = 1) ∧ v.mem = s.mem ∧ Rest [.r1] s v := by
  simp only [VG.Impl.Ffdh.Arm.CandidatePrepare.choose]
  refine wp_dp (op2_imm (by decide)) fun u hu => ?_
  refine wp_cmp (op2_imm (by decide)) fun v hv zero => WP.block_nil ?_
  have rest : Rest [.r1] s v := (hu.rest (by simp)).trans ((hv.rest []).mono (by simp))
  have memory : v.mem = s.mem := hv.mem.trans hu.mem
  have input : PrepareInput base src len k v := by
    refine ⟨h.workspace.congr rest.wr, ?_, ?_, ?_, h.minLength,h.maxLength,h.space,
      h.sourceFits,?_,h.separate,?_,?_⟩
    · have f : Frame [⟨State.addr base,8*len⟩] s.mem v.mem := by rw [memory];exact Frame.refl _ _
      simpa only [memory,rest.sp] using h.stack.after_workspace f rest
    · rw [rest.gpr .r0 (by simp)];exact h.ptr
    · rw [rest.gpr .r6 (by simp)];exact h.count
    · rw [rest.rd,rest.wr];exact h.readable
    · rw [memory];exact h.large
    · rw [memory];exact h.odd
  have branch : v.z = decide (k % 8 = 1) := by
    rw [zero, hu.gpr, dpVal, h.count]
    have mask : (BitVec.ofNat 32 k &&& (7 : BitVec 32)).toNat = k % 8 := by
      rw [BitVec.toNat_and,BitVec.toNat_ofNat]
      change (k % 2^32) &&& (2^3-1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod]
      omega
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro eq
      have emask : (BitVec.ofNat 32 k &&& (7 : BitVec 32)) = 1 := by
        calc
          _ = ((BitVec.ofNat 32 k &&& (7 : BitVec 32)) - 1) + 1 := (BitVec.sub_add_cancel _ _).symm
          _ = 1 := by rw [eq]; rfl
      have e := congrArg BitVec.toNat emask
      rw [mask] at e
      exact e
    · intro eq
      have emask : (BitVec.ofNat 32 k &&& (7 : BitVec 32)) = 1 :=
        BitVec.eq_of_toNat_eq (by rw [mask]; exact eq)
      rw [emask]; rfl
  exact ⟨input,by rw [memory];exact normalized,branch,memory,rest⟩

theorem candidatePrepare_ok (s : State) {base src : BitVec 32} {len k : Nat}
    (h : PrepareInput base src len k s)
    (normalized : k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
    WP isa VG.Impl.Ffdh.Arm.CandidatePrepare.code s fun t =>
      ArithmeticReady base len (Spec.Rsa.modulusWords k) t ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CandidatePrepare.code, WP.seq_iff]
  refine WP.mono (candidatePrepareChoice_ok s h normalized) ?_
  rintro v ⟨input,_,branch,memory,rest⟩
  have finish (t : State) (ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) t)
      (n : Proof.Rsa.Mont.numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (State.addr src) k))
      (r2 : Proof.Rsa.Mont.numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 = 2^(128*Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (State.addr src) k))
      (frame : Frame [⟨State.addr base,8*len⟩] v.mem t.mem) (rt : Rest roundClobbers v t) :=
    And.intro ready (And.intro (memory ▸ n) (And.intro (memory ▸ r2)
      (And.intro (by simpa only [memory] using frame) ((rest.mono (by simp [roundClobbers])).trans rt))))
  refine WP.ite v.z rfl ?_ ?_
  · intro selected
    refine WP.mono (prepare_ok v input) ?_
    rintro t ⟨ready,n,r2,frame,rt⟩
    exact finish t ready n r2 frame rt
  · intro selected
    have notBoundary : k % 8 ≠ 1 := by
      rw [branch] at selected
      simpa only [decide_eq_false_iff_not] using selected
    have bound := normalized.resolve_left notBoundary
    refine WP.mono (normalizedPrepare_ok v (inlineMontgomery base len (Spec.Rsa.modulusWords k))
      input trivial (by rw [memory];exact bound)) ?_
    rintro t ⟨ready,n,r2,_,frame,rt⟩
    exact finish t ready n r2 frame rt

end VG.Proof.Ffdh.Arm
