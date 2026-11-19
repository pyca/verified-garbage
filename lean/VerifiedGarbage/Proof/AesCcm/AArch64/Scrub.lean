module

public import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64
public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-CCM on AArch64, without secret residue

The postconditions of `vg_aes_ccm_seal` and `vg_aes_ccm_open` read the memory
on return only within the data and the tag (`ScrubAll.ScrubAllOk`): each
implementation, generic over the CMAC implementation it calls and its counter
mode, returns with every register it may leave secret cleared and its whole
stack zeroed (`ScrubAll.scrubAllOf`). Its frame is sized to what its
callees need (`Frame.lean`: 416 bytes with the Cryptographic Extension, 2592
otherwise), so that the zeroing costs little where the callees need no
working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- The bytes of a buffer on which two memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    {n : Nat} (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => (h _ (Region.contains_ofNat p (by have := List.mem_range.mp hi; omega))).symm

theorem sealOk (stack : Nat) :
    ScrubAllOk (Spec.Ccm.sealContract abi stack) stack (Spec.Ccm.sealSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Ccm.sealSig) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of hb.2.2.2.1 (by simp), bytesAt_of hb.2.2.2.2 (by simp)]

theorem openOk (stack : Nat) :
    ScrubAllOk (Spec.Ccm.openContract abi stack) stack (Spec.Ccm.openSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Ccm.openSig) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of hb.2.2.2.1 (by simp)]
      exact h key hk

/-- The registers `vg_aes_ccm_seal` writes itself: its tail clears them with
those its `vg_aes_ctr32` writes (`Ctr32Impl.clear`). -/
def sealOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- Of `vg_aes_ccm_seal`. -/
theorem sealSide (v : Proof.CmacAes.AArch64.UpdateImpl) (hv : v ∈ Proof.Variants.CmacAesUpdate.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (416 + v.scratch) 2
        (Impl.AesCcm.AArch64.«seal» v.callee v.ctr.callee)) (416 + v.scratch)
      (Spec.Ccm.sealSig.retBits abi.ptrBits) (clearUnion sealOwn v.ctr.clear) [] = true := by
  have e : (Proof.Variants.CmacAesUpdate.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (416 + v.scratch) 2
        (Impl.AesCcm.AArch64.«seal» v.callee v.ctr.callee)) (416 + v.scratch)
        (Spec.Ccm.sealSig.retBits abi.ptrBits) (clearUnion sealOwn v.ctr.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_ccm_open` writes itself: its tail clears them with
those its `vg_aes_ctr32` writes (`Ctr32Impl.clear`). -/
def openOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- Of `vg_aes_ccm_open`. -/
theorem openSide (v : Proof.CmacAes.AArch64.UpdateImpl) (hv : v ∈ Proof.Variants.CmacAesUpdate.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (416 + v.scratch) 2
        (Impl.AesCcm.AArch64.«open» v.callee v.ctr.callee)) (416 + v.scratch)
      (Spec.Ccm.openSig.retBits abi.ptrBits) (clearUnion openOwn v.ctr.clear) [] = true := by
  have e : (Proof.Variants.CmacAesUpdate.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (416 + v.scratch) 2
        (Impl.AesCcm.AArch64.«open» v.callee v.ctr.callee)) (416 + v.scratch)
        (Spec.Ccm.openSig.retBits abi.ptrBits) (clearUnion openOwn v.ctr.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.AesCcm.AArch64.Scrub
