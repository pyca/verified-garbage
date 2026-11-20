module

public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Fn
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Scrypt.PPC64LE.Lit

/-!
# scrypt on PPC64LE, without secret residue

`vg_scrypt` as emitted (`Impl/Scrypt/PPC64LE/Fn.lean`), followed by its
cleanup (`Impl.Scrub.PPC64LE.scrub`, `PPC64LE.Scrub.verifiedScrubbed`), which
clears the volatile registers, the vector registers it writes and the 1120
bytes of stack its frames use. Its
postcondition reads the memory on return only within `out`
(`PPC64LE.Scrub.PostOut`), by RISC-V's proof
(`Proof/Scrypt/RISCV64/Scrub.lean`). What the cleanup needs of
the code (`scrubSide`) is proved by the kernel's evaluation of it when this
module is built.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

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

/-! ## The function as emitted -/

/-- `vg_scrypt` as emitted (`Impl.Scrypt.PPC64LE.Fn.scrypt`), calling
PBKDF2-HMAC-SHA256's code, meets its contract in constant time and returns
without secret residue. -/
theorem scrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target
      (Impl.Scrypt.PPC64LE.Fn.scrypt Proof.Scrypt.PPC64LE.Whole.pbkName Proof.Scrypt.PPC64LE.Whole.pbkCode)
      (Spec.Scrypt.scryptContract PPC64LE.abi Proof.Scrypt.PPC64LE.Whole.stackBytes) 0 :=
  verifiedScrubbed (api := Spec.Scrypt.scryptApi) {
      code := Impl.Scrypt.PPC64LE.Whole.scrypt Proof.Scrypt.PPC64LE.Whole.pbkName
        Proof.Scrypt.PPC64LE.Whole.pbkCode
      verified := Proof.Scrypt.PPC64LE.Whole.scrypt_verified }
    1120 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
        .v17, .v18, .v19]⟩
    (scryptOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Scrypt.PPC64LE.Scrub
