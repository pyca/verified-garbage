module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Entry
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Entry
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes

/-!
# DSA verification on PPC64LE: constant time

`verify_ct`: two runs from states that satisfy the contract and agree on its
public data (the arguments' registers, the stack's arguments, the key's
public part and the result) leak the same trace. The entry (`entry_rel`),
the checks of the key (`sizes_rel`, `oddsTail_rel`), the verification
(`body_rel`, one taint segment) and `restore` follow one another; each
branch of the checks depends only on the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

theorem fail_rel {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s) :
    RelCT isa (Two Φ) (.block [.li .r3 0]) (Two End) :=
  rel_end (two_taint [.r21] (fun v s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(h v _ h₁).regs.r21, (h v _ h₂).regs.r21])
    (by taint_decide)) (fun v s hs => (h v s hs).regs.r21) (by decide) (by decide)

theorem body_rel : RelCT isa (Two K9) Verify.body (Two End) :=
  rel_end (two_taint _ (pins_fixL _ _ fun _ => rfl) (by taint_decide)) (fun _ _ h => h.1.regs.r21)
    (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)

theorem checkKey_rel : RelCT isa (Two S0) (checkKey Verify.body (.block [.li .r3 0])) (Two End) :=
  sizes_rel (oddsTail_rel body_rel fun _ h => fail_rel h) fun _ h => fail_rel h

theorem pins_End : Pins End [.r21] := by
  intro v s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [h₁, h₂]

theorem verify_rel : RelCT isa (Two C0) Verify.verify fun _ _ => True := by
  unfold Verify.verify
  exact RelCT.seq entry_rel (RelCT.seq checkKey_rel (two_taint _ pins_End (by taint_decide)))

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

/-- Runs that agree on the contract's public data have the same public data `vdOf`. -/
theorem vdOf_eq {s t : State} (hs : vContract.pre s) (hp : vContract.pub s t) : vdOf s = vdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, -, h9, h10, a0, a1, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h3, ← h4, ← h5, ← h6, Nat.min_eq_right (by omega)] at e
  simp only [vdOf, layOf, ← h3, ← h5, ← h6, ← h7, ← h9, ← h10, ← a0, ← a1, e]

theorem verify_ct : ConstantTime isa vContract.pre vContract.pub Verify.verify :=
  RelCT.constantTime (verify_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdOf s, ⟨hs, rfl⟩, ⟨ht, (vdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
