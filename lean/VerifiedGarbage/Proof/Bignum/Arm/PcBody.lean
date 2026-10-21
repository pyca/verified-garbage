module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.Arm.PcValid
import VerifiedGarbage.Proof.Bignum.Arm.PcFail
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block

/-! # The RSA precomputation body implements both outcomes of the shared specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem pcBody_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (ws : Workspace s base (8 * len)) (stack : PcStack base dst src len k s)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (space : Spec.Rsa.publicScratchWords k ≤ len)
    (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (srcSep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (dstFit : dst.toNat + 16 * Spec.Rsa.modulusWords k ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) (16 * Spec.Rsa.modulusWords k))
    (dstSep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩)
    (ptr : s.gpr .r0 = base) (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : WP isa (PcFn.bodyWith kernel.code) s fun t =>
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (State.addr src) k) with
      | some words => t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) = words
      | none => t.gpr .r0 = 0 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) =
          List.replicate (2 * Spec.Rsa.modulusWords k) 0) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PcFn.bodyWith, WP.seq_iff]
  refine WP.mono (modulusCheck_ok s hk hk' srcFit read source count) ?_
  rintro u ⟨flag, mem, rest⟩
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem u.mem := by rw [mem]; exact Frame.refl _ _
  have stackU := stack.after_workspace frame rest
  refine WP.ite _ (by change some u.z = some _; rw [flag]) ?_ ?_
  · intro valid
    refine WP.mono (pcValid_ok (kernel := kernel) u (ws.congr rest.wr) stackU hk hk' space srcFit
      (by rw [rest.rd, rest.wr]; exact read) srcSep dstFit (by rw [rest.wr]; exact write) dstSep
      ((rest.gpr .r0 (by simp)).trans ptr) ((rest.gpr .r6 (by simp)).trans count)
      (by rw [mem]; exact valid)) ?_
    rintro t ⟨result, words, frameT, keep⟩
    rw [mem] at words frameT
    rw [publicPrecompute_some (bytesAt_length _ _ _) valid]
    exact ⟨⟨result, words⟩, frameT, (rest.mono (by simp [roundClobbers])).trans keep⟩
  · intro invalid
    refine WP.mono (pcFail_ok u stackU hk hk' dstFit (by rw [rest.wr]; exact write)
      ((rest.gpr .r6 (by simp)).trans count)) ?_
    rintro t ⟨result, words, frameT, keep⟩
    rw [mem] at frameT
    have failed : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (State.addr src) k) = none := by
      simp only [Spec.Rsa.publicPrecompute, bytesAt_length, invalid, Bool.false_eq_true, ite_false]
    rw [failed]
    exact ⟨⟨result, words⟩, frameT.mono (by simp), (rest.mono (by simp [roundClobbers])).trans keep⟩

end VG.Proof.Bignum.Arm
