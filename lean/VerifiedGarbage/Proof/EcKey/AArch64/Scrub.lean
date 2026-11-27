module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Elliptic-curve keys on AArch64, without secret residue

For every curve (`Spec.EcKey.Instance`), the postconditions of
`vg_ec_<name>_public_key`, `_compress_public_key` and `_decompress_public_key`,
and of `vg_ecdh_<name>`, read the memory on return only within `out`, and that
of `vg_ecdsa_<name>_verify` does not read it (`Scrub.ScrubAllOk`, as
x86-64's `Proof/EcKey/X86_64/Scrub/Out.lean` proves them): each
implementation returns with every register it may leave secret cleared, and
its whole stack zeroed, if it has one (`Scrub.verifiedScrubbedAll`).
-/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub VG.Spec.EcKey

/-- The bytes at `p`, of `n`, read the memory only within `⟨p, n⟩`. -/
theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n k : Nat} (hk : n ≤ k)
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) : bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => by
    have hi := List.mem_range.mp hi
    refine (h _ ?_).symm
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    have := Nat.mod_le i (2 ^ 64)
    omega_using [hk, hi]

variable (I : Instance)

/-- `publicKeyOk` for code that takes tables of constants. -/
theorem publicKeyOk_consts (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) :
    ScrubAllOk (I.publicKeyContract (abi.withConsts (c₀ :: cs)) 0) 0 (I.publicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_consts0 (sig := I.publicKeySig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
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

theorem publicKeyOk :
    ScrubAllOk (I.publicKeyContract abi 0) 0 (I.publicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := I.publicKeySig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
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

theorem compressOk :
    ScrubAllOk (I.compressPublicKeyContract abi 0) 0 (I.compressPublicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := I.compressPublicKeySig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
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

theorem decompressOk :
    ScrubAllOk (I.decompressPublicKeyContract abi 0) 0 (I.decompressPublicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := I.decompressPublicKeySig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
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

theorem exchangeOk :
    ScrubAllOk (Spec.Ecdh.Instance.exchangeContract I abi 0) 0
      ((Spec.Ecdh.Instance.exchangeSig I).retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Ecdh.Instance.exchangeSig I) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
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

/-- `exchangeOk` for code with frames, in its stack of `W` bytes, which it zeroes. -/
theorem exchangeOkW (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.Ecdh.Instance.exchangeContract I abi W) W
      ((Spec.Ecdh.Instance.exchangeSig I).retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Ecdh.Instance.exchangeSig I) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
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

/-- `vg_ecdsa_<name>_verify`, in its frame of 80 bytes. -/
theorem verifyHashOk (J : Spec.Ecdsa.Instance) :
    ScrubAllOk (J.verifyHashContract abi 80) 80 (J.verifyHashSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := J.verifyHashSig) (Nat.le_of_ble_eq_true rfl) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
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

/-- `verifyHashOk` for code that takes tables of constants. -/
theorem verifyHashOk_consts (J : Spec.Ecdsa.Instance)
    (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) :
    ScrubAllOk (J.verifyHashContract (abi.withConsts (c₀ :: cs)) 80) 80 (J.verifyHashSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := J.verifyHashSig) (Nat.le_of_ble_eq_true rfl) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
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

end VG.Proof.EcKey.AArch64.Scrub
