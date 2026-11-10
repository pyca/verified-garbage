module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.EcKey.Validate
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Elliptic-curve keys on x86-64: postconditions local to the buffers

For every curve (`Spec.EcKey.Instance`), the postconditions of
`vg_ec_<name>_public_key`, `_compress_public_key`, `_decompress_public_key`
and `_validate_public_key` read the memory on return only within `out`, and
that of `vg_ecdsa_<name>_verify` does not read it (`X86_64.Scrub.PostOut`),
as `X86_64.RScrub.withScrub` needs to scrub their implementations.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.EcKey

/-- The bytes at `p`, of `n`, read the memory only within `⟨p, n⟩`. -/
theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n k : Nat} (hk : n ≤ k)
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) : bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => by
    have hi := List.mem_range.mp hi
    refine (h _ ?_).symm
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    have := Nat.mod_le i (2 ^ 64)
    omega

variable (I : Instance) (stack : Nat)

theorem publicKeyOut : PostOut (I.publicKeyContract X86_64.abi stack) (I.publicKeySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Instance.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := 2 * I.curve.len + 1) (by simp only [Elem.size]; omega) hb.1
    change match publicKey I.curve (Spec.Weierstrass.ofBytes (bytesAt m d I.curve.len)) with
      | some (.affine x y) =>
        r = 1 ∧ bytesAt m₂ out (2 * I.curve.len + 1) = encodePoint (.affine x y)
      | _ => r = 0 ∧ bytesAt m₂ out (2 * I.curve.len + 1) = List.replicate (2 * I.curve.len + 1) 0
    rw [e]
    exact h

theorem compressOut :
    PostOut (I.compressPublicKeyContract X86_64.abi stack) (I.compressPublicKeySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Instance.compressPublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := I.curve.len + 1) (by simp only [Elem.size]; omega) hb.1
    change match compressPublicKey I.curve (bytesAt m pk (2 * I.curve.len + 1)) with
      | some bs => r = 1 ∧ bytesAt m₂ out (I.curve.len + 1) = bs
      | none => r = 0 ∧ bytesAt m₂ out (I.curve.len + 1) = List.replicate (I.curve.len + 1) 0
    rw [e]
    exact h

theorem decompressOut :
    PostOut (I.decompressPublicKeyContract X86_64.abi stack) (I.decompressPublicKeySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Instance.decompressPublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := 2 * I.curve.len + 1) (by simp only [Elem.size]; omega) hb.1
    change (r = 1 ∧ ∃ Q, matchesCompressedPublicKey I.curve (bytesAt m pk (I.curve.len + 1)) Q ∧
        bytesAt m₂ out (2 * I.curve.len + 1) = encodePoint Q) ∨
      (r = 0 ∧ (¬ ∃ Q, matchesCompressedPublicKey I.curve (bytesAt m pk (I.curve.len + 1)) Q) ∧
        bytesAt m₂ out (2 * I.curve.len + 1) = List.replicate (2 * I.curve.len + 1) 0)
    rw [e]
    exact h

theorem validateOut :
    PostOut (I.validatePublicKeyContract X86_64.abi stack) (I.validatePublicKeySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

theorem verifyHashOut (J : Spec.Ecdsa.Instance) :
    PostOut (J.verifyHashContract X86_64.abi stack) (J.verifyHashSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

end VG.Proof.EcKey.X86_64.Scrub
