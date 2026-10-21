module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueEquals
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose the shared trial reducer with a bounded public residue list. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private theorem residueAny {acc : Nat} {values : List Nat}
    (accBound : acc < 2 ^ 32) (bounds : ∀ v ∈ values, v < 256) :
    values.any (fun v => BitVec.ofNat 32 acc == BitVec.ofNat 32 v) = decide (acc ∈ values) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, equal⟩
    rw [ofNat_beq_eq accBound (by have := bounds v hv; omega), decide_eq_true_eq] at equal
    rwa [equal]
  · intro member
    exact ⟨acc, member, by simp⟩

theorem residuePrime_ok {s : State} {dst : BitVec 32} {n prime : Nat}
    (h : ReadContext dst n s) (primeBound : prime < 2) (first : Nat) (rest : List Nat)
    (bounds : ∀ v ∈ first :: rest, v < 256) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime
      (VG.Impl.RsaKeyGen.tabEntry prime) (first :: rest)) s fun t =>
      ∃ acc, acc < 2 * VG.Impl.RsaKeyGen.tabEntry prime ∧
        acc % VG.Impl.RsaKeyGen.tabEntry prime =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime ∧
        t.z = decide (acc ∈ first :: rest) ∧ t.mem = s.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  have small : VG.Impl.RsaKeyGen.tabEntry prime < 256 := by
    rcases (by omega : prime = 0 ∨ prime = 1) with rfl | rfl
    · rw [trialPrime3]; decide
    · rw [trialPrime5]; decide
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (wp_mov (op2_imm (encodable_byte (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : VG.Impl.RsaKeyGen.tabEntry prime < 2 ^ 32)]
    exact small))) fun u moved => WP.block_nil ?_)
  have ctx := h.after_memory moved.mem (moved.rest (by simp : Reg.r7 ∈ [Reg.r7]))
  refine WP.seq (WP.mono (trialSmall_residue_ok u dst h.positive h.countFits h.bufferFits
    primeBound moved.gpr (ctx.frame.read (by decide)) (ctx.frame.read (by decide)) ctx.out ctx.width ctx.readable) ?_)
  rintro v ⟨acc, bound, value, residue, memory, keep⟩
  refine WP.seq (WP.mono (residueEquals_ok v first rest bounds) ?_)
  rintro t ⟨flag, memT, restT⟩
  refine WP.block_nil ⟨acc, bound, ?_, ?_, memT.trans (memory.trans moved.mem),
    (moved.rest (by simp : Reg.r7 ∈ [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7])).trans
      (keep.trans (restT.mono (by simp)))⟩
  · simpa only [moved.mem] using residue
  · rw [value, residueAny (by omega : acc < 2 ^ 32) bounds] at flag
    exact flag

end VG.Proof.Ffdh.Arm.ParameterCandidate
