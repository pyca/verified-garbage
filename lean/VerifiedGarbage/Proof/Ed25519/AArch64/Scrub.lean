module

public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.Sha512Compress.AArch64
public import VerifiedGarbage.Proof.Ed25519.AArch64.KeyPair
public import VerifiedGarbage.Impl.Ed25519.AArch64.KeyPair
public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyMessage
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.WholeLocal

/-!
# Ed25519 on AArch64, without secret residue

The postconditions of `vg_ed25519_key_pair` and `vg_ed25519_sign_expanded`
read the memory on return only within their outputs, and that of
`vg_ed25519_verify` not at all (`ScrubAll.ScrubAllOk`): each implementation,
generic over the SHA-512 implementation it calls, returns with every register
it may leave secret cleared and its whole stack zeroed
(`ScrubAll.scrubAllOf`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

theorem keyPairOk : ScrubAllOk (Spec.Ed25519.keyPairContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts) 944)
    944 (Spec.Ed25519.keyPairSig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed25519.keyPairSig) (c₀ := (Impl.Ed25519.AArch64.combSym, Impl.Ed25519.AArch64.combWords))
    (cs := []) (W := 944) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOk : ScrubAllOk
    (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts) 352)
    352 (Spec.Ed25519.signExpandedSig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed25519.signExpandedSig)
    (c₀ := (Impl.Ed25519.AArch64.combSym, Impl.Ed25519.AArch64.combWords))
    (cs := []) (W := 352) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOk : ScrubAllOk (Spec.Ed25519.verifyContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.bConsts) 352)
    352 (Spec.Ed25519.verifySig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed25519.verifySig) (c₀ := (Impl.Ed25519.AArch64.bSym, Impl.Ed25519.AArch64.bWords))
    (cs := []) (W := 352) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h

/-! ## What the tails clear

Each function's tail clears the registers its own code writes with those its
SHA-512 compression function writes (`Compress.clear`); `scrubAllOf` needs
`scrubSide` of each, evaluated here with each compression function. -/

/-- The registers `vg_ed25519_key_pair` writes itself. -/
def keyPairOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v31], []⟩

/-- The registers `vg_ed25519_sign_expanded` writes itself. -/
def signExpandedOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v16, .v17, .v18, .v19, .v20, .v21, .v22], []⟩

/-- The registers `vg_ed25519_verify` writes itself. -/
def verifyOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v31], []⟩

/-- Of `vg_ed25519_key_pair`. -/
theorem keyPairSide (v : Proof.Sha512.AArch64.Compress) (hv : v ∈ Proof.Variants.Sha512Compress.AArch64.variants) :
    scrubSide (Impl.Ed25519.AArch64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ v.suffix)
        (Proof.Ed25519.AArch64.KeyPair.dgCode v) "vg_ed25519_public_key_expanded"
        Impl.Ed25519.AArch64.PublicKey.codeExpanded) 944
      (Spec.Ed25519.keyPairSig.retBits AArch64.abi.ptrBits) (clearUnion keyPairOwn v.clear) [] = true := by
  have e : (Proof.Variants.Sha512Compress.AArch64.variants.all fun v =>
      scrubSide (Impl.Ed25519.AArch64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ v.suffix)
        (Proof.Ed25519.AArch64.KeyPair.dgCode v) "vg_ed25519_public_key_expanded"
        Impl.Ed25519.AArch64.PublicKey.codeExpanded) 944
        (Spec.Ed25519.keyPairSig.retBits AArch64.abi.ptrBits) (clearUnion keyPairOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of `vg_ed25519_sign_expanded`. -/
theorem signExpandedSide (v : Proof.Sha512.AArch64.Compress) (hv : v ∈ Proof.Variants.Sha512Compress.AArch64.variants) :
    scrubSide (Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix) 352
      (Spec.Ed25519.signExpandedSig.retBits AArch64.abi.ptrBits) (clearUnion signExpandedOwn v.clear) [] = true := by
  have e : (Proof.Variants.Sha512Compress.AArch64.variants.all fun v =>
      scrubSide (Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix) 352
        (Spec.Ed25519.signExpandedSig.retBits AArch64.abi.ptrBits) (clearUnion signExpandedOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of `vg_ed25519_verify`. -/
theorem verifySide (v : Proof.Sha512.AArch64.Compress) (hv : v ∈ Proof.Variants.Sha512Compress.AArch64.variants) :
    scrubSide (Impl.Ed25519.AArch64.VerifyMessage.code v.code v.suffix) 352
      (Spec.Ed25519.verifySig.retBits AArch64.abi.ptrBits) (clearUnion verifyOwn v.clear) [] = true := by
  have e : (Proof.Variants.Sha512Compress.AArch64.variants.all fun v =>
      scrubSide (Impl.Ed25519.AArch64.VerifyMessage.code v.code v.suffix) 352
        (Spec.Ed25519.verifySig.retBits AArch64.abi.ptrBits) (clearUnion verifyOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Ed25519.AArch64.Scrub
