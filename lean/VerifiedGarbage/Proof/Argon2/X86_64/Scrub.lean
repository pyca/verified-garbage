module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Argon2 on x86-64, without secret residue

`vg_argon2`'s postcondition reads the memory on return only within `out`
(`X86_64.Scrub.PostOut`): each implementation returns with its whole stack
wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

theorem deriveOut (stack : Nat) :
    PostOut (Spec.Argon2.deriveContract X86_64.abi stack) (Spec.Argon2.deriveSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
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

end VG.Proof.Argon2.X86_64.Scrub
