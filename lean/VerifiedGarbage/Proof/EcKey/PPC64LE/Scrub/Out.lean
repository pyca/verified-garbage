module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the scrubbed registrations of ECDH and ECDSA's verification import it without the public keys' proofs

/-!
# Elliptic-curve postconditions on PPC64LE, for scrubbing

For every curve (`Spec.EcKey.Instance`), the postconditions of
`vg_ec_<name>_public_key`, `_compress_public_key` and `_decompress_public_key`,
and of `vg_ecdh_<name>`, read the memory on return only within `out`, and that
of `vg_ecdsa_<name>_verify` does not read it (`PPC64LE.Scrub.PostOut`), by
RISC-V's proofs (`Proof/EcKey/RISCV64/Scrub.lean`), so that each
implementation may be followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.withScrub`). Each lemma takes the tables of constants `cs`
the code reads, which may be none.
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Spec.EcKey

/-- The bytes at `p`, of `n`, read the memory only within `⟨p, n⟩`. -/
theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n k : Nat} (hk : n ≤ k)
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) : bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => by
    have hi := List.mem_range.mp hi
    refine (h _ ?_).symm
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    have := Nat.mod_le i (2 ^ 64)
    omega_using [hk, hi]

variable (I : Instance) (stack : Nat) (cs : List (String × List (BitVec 64)))

theorem publicKeyOut :
    PostOut (I.publicKeyContract (PPC64LE.abi.withConsts cs) stack) (I.publicKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Instance.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := 2 * I.curve.len + 1) (by simp only [Elem.size]; omega_using []) hb.1
    change match publicKey I.curve (Spec.Weierstrass.ofBytes (bytesAt m d I.curve.len)) with
      | some (.affine x y) =>
        r = 1 ∧ bytesAt m₂ out (2 * I.curve.len + 1) = encodePoint (.affine x y)
      | _ => r = 0 ∧ bytesAt m₂ out (2 * I.curve.len + 1) = List.replicate (2 * I.curve.len + 1) 0
    rw [e]
    exact h

theorem compressOut :
    PostOut (I.compressPublicKeyContract (PPC64LE.abi.withConsts cs) stack) (I.compressPublicKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Instance.compressPublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := I.curve.len + 1) (by simp only [Elem.size]; omega_using []) hb.1
    change match compressPublicKey I.curve (bytesAt m pk (2 * I.curve.len + 1)) with
      | some bs => r = 1 ∧ bytesAt m₂ out (I.curve.len + 1) = bs
      | none => r = 0 ∧ bytesAt m₂ out (I.curve.len + 1) = List.replicate (I.curve.len + 1) 0
    rw [e]
    exact h

theorem decompressOut :
    PostOut (I.decompressPublicKeyContract (PPC64LE.abi.withConsts cs) stack) (I.decompressPublicKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Instance.decompressPublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := 2 * I.curve.len + 1) (by simp only [Elem.size]; omega_using []) hb.1
    change (r = 1 ∧ ∃ Q, matchesCompressedPublicKey I.curve (bytesAt m pk (I.curve.len + 1)) Q ∧
        bytesAt m₂ out (2 * I.curve.len + 1) = encodePoint Q) ∨
      (r = 0 ∧ (¬ ∃ Q, matchesCompressedPublicKey I.curve (bytesAt m pk (I.curve.len + 1)) Q) ∧
        bytesAt m₂ out (2 * I.curve.len + 1) = List.replicate (2 * I.curve.len + 1) 0)
    rw [e]
    exact h

theorem exchangeOut :
    PostOut (Spec.Ecdh.Instance.exchangeContract I (PPC64LE.abi.withConsts cs) stack)
      ((Spec.Ecdh.Instance.exchangeSig I).retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨peer, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Ecdh.Instance.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have e := bytesAt_congr (n := I.curve.len) (by simp only [Elem.size]; omega_using []) hb.1
    change match Spec.Ecdh.exchange I.curve (Spec.Weierstrass.ofBytes (bytesAt m d I.curve.len))
          (bytesAt m peer (2 * I.curve.len + 1)) with
      | some z => r = 1 ∧ bytesAt m₂ out I.curve.len = z
      | none => r = 0 ∧ bytesAt m₂ out I.curve.len = List.replicate I.curve.len 0
    rw [e]
    exact h

theorem verifyHashOut (J : Spec.Ecdsa.Instance) :
    PostOut (J.verifyHashContract (PPC64LE.abi.withConsts cs) stack) (J.verifyHashSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
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

end VG.Proof.EcKey.PPC64LE.Scrub
