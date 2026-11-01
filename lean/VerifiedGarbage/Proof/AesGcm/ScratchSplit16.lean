module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.ScratchSplit
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# AES-GCM `seal_split` with sixteen prepared powers and its working space as an argument

`sealSplitPrepared16ScratchContract`: `sealSplitPreparedScratchContract`
(`ScratchSplit.lean`) with the precondition of `Spec.Gcm.Prepared16`, and
its locality (`sealSplitPrepared16Pre_local`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG.Spec.Gcm Proof.Gcm


/-- `sealSplitPrepared16Contract`, whatever `work` is. -/
def sealSplitPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPrepared16Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag _work =>
      sealSplitPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag)
    (writeArgs := true) (stack := stack)


variable (pb : Nat)

theorem sealSplitPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (sealSplitPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitPreparedSig.words pb) (sealSplitPrepared16Pre pb) vs m₁ →
      Curry.apply (sealSplitPreparedSig.words pb) (sealSplitPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 10
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitPreparedSig, sealSplitPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealSplitPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, sealSplitPrepared16Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, h.2.1, preparedPowers16Repr_congr hc h.2.2⟩

end VG.Proof.AesGcm
