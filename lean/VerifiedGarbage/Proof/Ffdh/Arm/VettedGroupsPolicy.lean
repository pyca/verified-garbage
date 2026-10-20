module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Spec.Ffdh.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsMath
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState

/-! The machine recognizer returns exactly the reviewed vetted-domain cap. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem vettedGroups_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : VettedGroups.TableAt (s.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym)
      VG.Impl.Ffdh.Arm.VettedGroups.groups s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa VG.Impl.Ffdh.Arm.VettedGroups.code s fun t => Context p slots t ∧
      t.gpr .r11 = BitVec.ofNat 32
        ((Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom)).getD 0) ∧
      t.mem = s.mem ∧ Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  refine WP.mono (VettedGroups.code_ok s h h24 h28 h32 table) ?_
  rintro t ⟨context, cap, mem, rest⟩
  have size : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k := by
    rw [p.domainLength]; split <;> simp
  rw [VettedGroups.recognize_spec (by have := p.minLength; omega) size normalized] at cap
  exact ⟨context, cap, mem, rest⟩

end VG.Proof.Ffdh.Arm
