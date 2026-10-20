module
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution

import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Signature release, success return value and restored registers -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def signRelease : Prog isa := seqs [SignVerify.writeScalar r false, SignVerify.writeScalar s true,
  .block SignVerify.result]

theorem signRelease_ok {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa signRelease s0 fun s2 =>
      s2.gpr .x0 = BitVec.ofNat 64 valid.toNat ∧
      Spec.Rsa.bytesAt s2.mem (L.fields .out) (2 * L.qLen) =
        (if valid then Spec.Rsa.bytesAt s0.mem (off L.base r) L.qLen ++
          Spec.Rsa.bytesAt s0.mem (off L.base s) L.qLen else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) → s2.mem x = s0.mem x) ∧
      Keep coreRegs s0 s2 := by
  unfold signRelease seqs
  apply WP.assoc
  refine WP.seq (WP.mono (writeSignature_ok h0 hm hw hsep) fun s1 ⟨hb1, hf1, hk1⟩ => ?_)
  have hn := h0.scratch.nowrap
  have hword (d : Nat) (hd : d + 8 ≤ usedBytes) : word s1.mem L.base d = word s0.mem L.base d := by
    apply Mem.readW_congr
    intro i hi
    exact hf1 _ (fun j hj => scr_ne_out hsep (by omega) (by omega) j hj)
  have hmask := (hword Field.mask.offset (by decide)).trans hm
  refine WP.mono (result_ok (h0.scratch.congr hk1.wr) ((hk1.gpr .x0 (by decide)).trans h0.parent.x0)
    (by decide) hmask) fun s2 ⟨ha, hmem, hk2⟩ => ?_
  refine ⟨ha, ?_, ?_, (hk1.trans hk2).mono (by decide)⟩
  · rw [hmem]
    exact hb1
  · intro x hx
    rw [hmem]
    exact hf1 x hx

end VG.Proof.Dsa.AArch64
