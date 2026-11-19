module

public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
public import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# scrypt on AArch64, without secret residue

The postcondition of `vg_scrypt` reads the memory on return only within
`out` (`ScrubAll.ScrubAllOk`, as x86-64's `scrypt_postOut` in
`Proof/Scrypt/X86_64/Whole/Verified.lean` proves it): each implementation,
generic over the SHA-256 implementation it calls, returns with every register
it may leave secret cleared and its whole stack zeroed
(`ScrubAll.scrubAllOf`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem scryptOk (stack : Nat) :
    ScrubAllOk (Spec.Scrypt.scryptContract abi stack) stack (Spec.Scrypt.scryptSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Scrypt.scryptSig)
    fun vs m m₁ m₂ ret hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 12) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨blen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨vlen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨slen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Scrypt.scryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have hby : Spec.Scrypt.bytesAt m₂ out outLen.toNat = Spec.Scrypt.bytesAt m₁ out outLen.toNat := by
      unfold Spec.Scrypt.bytesAt
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.2.2.2.2.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this])
        (by have := outLen.isLt; omega_arith))).symm
    replace h : Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt m pw pwLen.toNat) (Spec.Scrypt.bytesAt m salt saltLen.toNat)
        (vlen.toNat / r.toNat) r.toNat (blen.toNat / r.toNat) outLen.toNat =
        some (Spec.Scrypt.bytesAt m₁ out outLen.toNat) := h
    show _ = some (Spec.Scrypt.bytesAt m₂ out outLen.toNat)
    rw [hby]; exact h

/-- The registers `vg_scrypt` writes itself: its tail clears them with those
its SHA-256 compression function writes (`Compress.clear`). -/
def scryptOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22], []⟩

/-- What `scrubAllOf` needs of `vg_scrypt` with each compression function:
evaluated here. -/
theorem scryptSide (c : Proof.Sha256.AArch64.Compress) (hc : c ∈ Proof.Variants.Sha256Compress.AArch64.variants) :
    scrubSide (Impl.Scrypt.AArch64.scrypt (Proof.Scrypt.AArch64.Whole.pbkName c) (Proof.Scrypt.AArch64.Whole.pbkOf c))
      96 (Spec.Scrypt.scryptSig.retBits abi.ptrBits) (clearUnion scryptOwn c.clear) [] = true := by
  have e : (Proof.Variants.Sha256Compress.AArch64.variants.all fun c =>
      scrubSide (Impl.Scrypt.AArch64.scrypt (Proof.Scrypt.AArch64.Whole.pbkName c) (Proof.Scrypt.AArch64.Whole.pbkOf c))
        96 (Spec.Scrypt.scryptSig.retBits abi.ptrBits) (clearUnion scryptOwn c.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e c hc

end VG.Proof.Scrypt.AArch64.Scrub
