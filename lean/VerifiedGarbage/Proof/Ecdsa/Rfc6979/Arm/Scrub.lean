module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: what every curve's signing on 32-bit ARM needs to be scrubbed, not one curve's proof

/-!
# Deterministic ECDSA on 32-bit ARM, without secret residue

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return only
within `out` (`Arm.Scrub.PostOut`), as on RISC-V
(`Proof/Ecdsa/Rfc6979/RISCV64/Scrub.lean`): each implementation, generic over
the HMAC implementations its table holds, which it calls indirectly, is
registered followed by a wipe of the stack its contract reserves and
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Arm.Scrub.scrubRegFT`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm.Scrub

open VG.Arm VG.Arm.Scrub
open VG.Proof.HmacTable.Arm (HVar tables)

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

/-- The postcondition reads the memory on return only within `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List HVar) :
    PostOut (specK T cs vs) (T.signSig.retBits 32) :=
  postOut_of_local ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [out, d, dg, dl, sc, hm], _ =>
      simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons,
        forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := 2 * T.ecdsa.curve.len) (Nat.le_refl _) hb.1
      intro H F h1 h2
      have h' := h H F h1 h2
      revert h'
      split
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm.Scrub
