module

public import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Contract
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-! # Prepared-context out-of-place scratch contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm
open VG.Spec.Gcm Proof.Gcm


def streamEncryptToPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPreparedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Proof.Gcm.streamEncryptToPrepared16Pre A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (post := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Proof.Gcm.streamEncryptToPost A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (writeArgs := true) (stack := stack)



def sealGatherPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPrepared16Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Proof.AesGcm.sealGatherRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (writeArgs := true) (stack := stack)

variable (pb : Nat)

theorem streamEncryptToPrepared16Pre_local : ∀ vs m₁ m₂,
    vs.length = (streamEncryptToPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamEncryptToPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamEncryptToPreparedSig.words pb) (streamEncryptToPrepared16Pre pb) vs m₁ →
      Curry.apply (streamEncryptToPreparedSig.words pb) (streamEncryptToPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamEncryptToPreparedSig, streamEncryptToPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (streamEncryptToPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, streamEncryptToPrepared16Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, h.2.1, preparedPowers16Repr_congr hc h.2.2⟩

theorem sealGatherPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (sealGatherPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sealGatherPreparedSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherPreparedSig.words pb) (sealGatherPrepared16Pre pb) vs m₁ →
      Curry.apply (sealGatherPreparedSig.words pb) (sealGatherPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb hl h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨cnt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealGatherPreparedSig, sealGatherPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  simp only [sealGatherPreparedSig, sealGatherPrecomputedSig, Sig.lists, List.append_nil] at hl
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealGatherPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (sealGatherPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, sealGatherPrepared16Pre, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le cnt.toNat (2 ^ pb)
  rw [gatheredLen_congr_le (by rw [BitVec.toNat_setWidth]; exact this) hl]
  exact ⟨h.1, h.2.1, preparedPowers16Repr_congr hc h.2.2⟩


end VG.Proof.AesGcm
