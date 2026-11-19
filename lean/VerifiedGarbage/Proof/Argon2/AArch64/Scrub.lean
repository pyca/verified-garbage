module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.Blake2b.AArch64
public import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Argon2 on AArch64, without secret residue

The postcondition of `vg_argon2` reads the memory on return only within
`out` (`ScrubAll.ScrubAllOk`, as x86-64's `Proof/Argon2/X86_64/Scrub.lean`
proves it): each implementation, generic over the BLAKE2b implementation it
calls, returns with every register it may leave secret cleared and its whole
stack zeroed (`ScrubAll.scrubAllOf`).
-/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem deriveOk (stack : Nat) :
    ScrubAllOk (Spec.Argon2.deriveContract abi stack) stack (Spec.Argon2.deriveSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Argon2.deriveSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, out, outLen], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Argon2.deriveSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      have ho := hb.2.2.2.2.2.2
      change _ = _ at h
      change Spec.Blake2.bytesAt m₂ out _ = _
      rw [← h]
      simp only [Spec.Blake2.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      simp only [ArgWord.ofRaw, show abi.ptrBits = 64 from rfl, BitVec.toNat_setWidth] at this
      have := Nat.mod_le outLen.toNat (2 ^ 64)
      exact (ho _ (Offset.contains_base _ (by simp only [Elem.size] at *; omega_arith) (by omega_arith))).symm

/-- The registers `vg_argon2_derive` writes, with every BLAKE2b. -/
def deriveClear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v16],
   []⟩

/-- What `scrubAllOf` needs of `vg_argon2_derive` with each BLAKE2b:
evaluated here. -/
theorem deriveSide (v : Proof.Argon2.AArch64.HPrime.Backend) (hv : v ∈ Proof.Variants.Blake2b.AArch64.variants) :
    scrubSide (Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.suffix) v.hash) 400
      (Spec.Argon2.deriveSig.retBits abi.ptrBits) deriveClear [] = true := by
  have e : (Proof.Variants.Blake2b.AArch64.variants.all fun v =>
      scrubSide (Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.suffix) v.hash) 400
        (Spec.Argon2.deriveSig.retBits abi.ptrBits) deriveClear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Argon2.AArch64.Scrub
