module

public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.Scrypt.RISCV64.Fn
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Verified
import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# scrypt on RISC-V, without secret residue

The postcondition of `vg_scrypt` reads the memory on return only within
`out` (`RISCV64.Scrub.PostOut`, as AArch64's `Proof/Scrypt/AArch64/Scrub.lean`
proves it): the function as emitted (`Impl.Scrypt.RISCV64.Fn.scrypt`, with
`vg_pbkdf2_hmac_sha256`'s code), the implementation followed by
`Impl.Scrub.RISCV64.scrubTail`, returns with the caller-saved registers
cleared and the stack its frames used zeroed, and meets its contract in
constant time (`scrypt_scrubbed`, by `RISCV64.Scrub.verifiedScrubbed`), which
is what its registration binds. Its arguments on the stack are in the
caller's frame, among the buffers (`writeArgs`), which the caller owns.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

theorem scryptOut (stack : Nat) :
    PostOut (Spec.Scrypt.scryptContract abi stack) (Spec.Scrypt.scryptSig.retBits abi.ptrBits) :=
  postOut_of_local ScrubAbi.plain (sig := Spec.Scrypt.scryptSig)
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

/-- `vg_scrypt` as emitted (`Impl.Scrypt.RISCV64.Fn.scrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem scrypt_scrubbed :
    VerifiedScrubbed target
      (Impl.Scrypt.RISCV64.Fn.scrypt Proof.Scrypt.RISCV64.Whole.pbkName Proof.Scrypt.RISCV64.Whole.pbkCode)
      (Spec.Scrypt.scryptContract RISCV64.abi 1248) 0 :=
  verifiedScrubbed (api := Spec.Scrypt.scryptApi) (W := 1248)
    { code := _, verified := Proof.Scrypt.RISCV64.Whole.scrypt_verified } (scryptOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Scrypt.RISCV64.Scrub
