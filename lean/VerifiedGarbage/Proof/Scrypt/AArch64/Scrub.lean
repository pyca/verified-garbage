module

public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# scrypt on AArch64, without secret residue

The postcondition of `vg_scrypt` reads the memory on return only within
`out` (`Scrub.ScrubAllOk`, as x86-64's `scrypt_postOut` in
`Proof/Scrypt/X86_64/Whole/Verified.lean` proves it): each implementation,
generic over the SHA-256 implementation it calls, returns with every register
it may leave secret cleared and its whole stack zeroed
(`Scrub.verifiedScrubbedAll`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub

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

end VG.Proof.Scrypt.AArch64.Scrub
