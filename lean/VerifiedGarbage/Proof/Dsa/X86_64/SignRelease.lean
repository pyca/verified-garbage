module
public import VerifiedGarbage.Proof.Dsa.X86_64.Execution
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify

import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Signature release, success return value and restored registers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def signRelease : Prog isa := seqs [SignVerify.writeScalar r false, SignVerify.writeScalar s true,
  .block SignVerify.result]

theorem signRelease_ok {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa signRelease s0 fun s2 =>
      s2.gpr .rax = BitVec.ofNat 64 valid.toNat ∧
      Spec.Rsa.bytesAt s2.mem (L.fields .out) (2 * L.qLen) =
        (if valid then Spec.Rsa.bytesAt s0.mem (off L.base r) L.qLen ++
          Spec.Rsa.bytesAt s0.mem (off L.base s) L.qLen else List.replicate (2 * L.qLen) 0) ∧
      (∀ i < 6, s2.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      (∀ x, (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) → s2.mem x = s0.mem x) ∧
      Keep mmRegs s0 s2 := by
  unfold signRelease seqs
  apply WP.assoc
  refine WP.seq (WP.mono (writeSignature_ok h0 hm hw hsep) fun s1 ⟨hb1, hf1, hk1⟩ => ?_)
  have hn := h0.scratch.nowrap
  have hword (d : Nat) (hd : d + 8 ≤ usedBytes) : word s1.mem L.base d = word s0.mem L.base d := by
    apply Mem.readW_congr
    intro i hi
    exact hf1 _ (fun j hj => scr_ne_out hsep (by omega) (by omega) j hj)
  have hmask := (hword Field.mask.offset (by decide)).trans hm
  refine WP.mono (result_ok (h0.scratch.congr hk1.2.2) ((hk1.gpr (by decide)).trans h0.parent.rdi)
    (by decide) hmask) fun s2 ⟨ha, hsaved, hmem, hk2⟩ => ?_
  refine ⟨ha, ?_, ?_, ?_, (hk1.trans hk2).mono (by decide)⟩
  · rw [hmem]
    exact hb1
  · intro i hi
    exact (hsaved i hi).trans (hword _ (by change 8 * i + 8 ≤ 15712; omega))
  · intro x hx
    rw [hmem]
    exact hf1 x hx

end VG.Proof.Dsa.X86_64
