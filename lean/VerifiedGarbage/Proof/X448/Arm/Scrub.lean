module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.X448.Arm.Exchange
public import VerifiedGarbage.Proof.X448.Arm.Base
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X448.Arm.Lit
import VerifiedGarbage.Proof.X448.Arm.BaseLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.X448.Arm.Exchange
meta import VerifiedGarbage.Proof.X448.Arm.Base
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.X448.Arm.Lit
meta import VerifiedGarbage.Proof.X448.Arm.BaseLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# X448 on ARMv7, without secret residue

`vg_x448_base`, with either multiplication of the field
(`Proof/Variants/Curve448Field/Arm.lean`), has no frames: it is registered
scrubbed (`Arm.Scrub.scrubReg`), followed by instructions that set the
registers a callee may change, and the flags, to constants.
`vg_x448_exchange` calls `vg_x448` from frames of 8 bytes, and its
postcondition reads the memory on return only at `out`
(`Arm.Scrub.PostOut`): it is registered followed by a wipe of those bytes
too (`Arm.Scrub.scrubRegF`).
-/

@[expose] public section

namespace VG.Proof.X448.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, N⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n ≤ N) :
    Spec.X448.bytesAt m₂ o n = Spec.X448.bytesAt m₁ o n := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this, hN]))).symm

theorem x448Base_noFrames (u : Bool) : (Impl.X448.Arm.x448Base u).noFrames = true := by
  cases u <;> lit_decide

theorem exchange_noIcall (u : Bool) : noIcall (Impl.Xdh.Arm.exchange ("vg_x448" ++ Impl.X448.Arm.suffix u) (Impl.X448.Arm.x448 u) 56) = true := by
  cases u <;> lit_decide

theorem exchange_armStack (u : Bool) :
    armStack (Impl.Xdh.Arm.exchange ("vg_x448" ++ Impl.X448.Arm.suffix u) (Impl.X448.Arm.x448 u) 56) ≤ 8 := by
  cases u <;> lit_decide

theorem frameOk_8 : FrameOk 8 := by decide

theorem exchangeOut (stack : Nat) :
    PostOut (Spec.X448.exchangeContract abi stack) (Spec.X448.exchangeSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun
    | [out, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.X448.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (Nat.le_refl 56)]
      exact h

/-- `vg_x448_exchange` with the field's multiplication `u`, as `suffix`. -/
def exchangeReg (u : Bool) (suffix : String) : Registration Spec.X448.exchangeApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.Xdh.Arm.exchange ("vg_x448" ++ Impl.X448.Arm.suffix u) (Impl.X448.Arm.x448 u) 56
      verified := Exchange.exchange_variant u }
    (exchange_armStack u) (exchange_noIcall u) frameOk_8 (exchangeOut _) rfl

/-- `vg_x448_base` with the field's multiplication `u`, as `suffix`, given the reference comb's
agreement with the specification. -/
def x448BaseReg (u : Bool) (suffix : String) (hu : Proof.Ed448.BaseCombUOk) :
    Registration Spec.X448.x448BaseApi target :=
  Arm.Scrub.scrubReg {
      suffix := suffix
      code := Impl.X448.Arm.x448Base u
      verified := Proof.X448.Arm.x448Base_verified hu }
    (x448Base_noFrames u)

end VG.Proof.X448.Arm.Scrub
