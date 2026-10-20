module

public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# The ARMv7 PKCS #1 v1.5 functions: pieces correct and constant time at once

The pieces of `VG.Proof.Rsa.Arm.Recover.VP` the functions are made of,
beyond the taint analysis (`VP.taint`): blocks that address only the stack,
through `sp` and `r12 = sp` (`VP.stk`), and calls of verified functions,
which may have frames of their own (`VP.callF`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm
open VG.Proof.Rsa.Arm.Recover (VP Two)

/-- A block of loads, stores and arithmetic relative to the stack pointer
(`r12 = sp`). -/
theorem VP.stk {F G : State → State → Prop} {code : List Instr}
    (keep : code.all (fun i => decide (clobbers i .r12 = false)) = true)
    (leak : code.all VG.Proof.Rsa.Arm.stackInstruction = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (wp : ∀ σ s, F σ s → WP isa (.block (.addSp .r12 0 :: code)) s (G σ)) :
    VP F (.block (.addSp .r12 0 :: code)) G :=
  VP.of_ct (fun _ _ => (VG.Proof.Rsa.Arm.setupChecked_ct code keep leak).mono
    (fun _ _ h => sp _ _ _ _ h.1 h.2) fun _ _ _ => trivial) wp

/-- A call of verified code `c` (with frames of its own, `armStack c ≤ S`)
given the regions `rd` and `wr`, the same in both runs. -/
theorem VP.callF {n : String} {c : Prog isa} {k : Contract isa} (hv : Verified target c k)
    {S : Nat} (hst : FrameStack.armStack c ≤ S) (rd wr : List Region) {F G : State → State → Prop}
    (pre : ∀ σ s, F σ s → k.pre (s.callEntry.withRegions rd wr))
    (cov : ∀ σ s, F σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr)
    (room : ∀ σ s, F σ s → S ≤ s.sp.toNat)
    (pub : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ →
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr))
    (post : ∀ σ s s', F σ s → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [FrameStack.belowA s.sp S]) s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → G σ s') :
    VP F (.call n c) G :=
  VP.of_ct (fun _ _ => RelCT.call hv.1 hv.2.1 rd wr fun _ _ h =>
      ⟨pre _ _ h.1, pre _ _ h.2, pub _ _ _ _ h.1 h.2, (cov _ _ h.1).1, (cov _ _ h.1).2, (cov _ _ h.2).1,
        (cov _ _ h.2).2⟩)
    fun σ s h => FrameStack.WP.callF hv.1 (pre σ s h) (cov σ s h).1 (cov σ s h).2
      (Nat.le_trans hst (room σ s h))
      fun s' r w p f g po => post σ s s' h r w p (FrameStack.Frame.belowA_mono f hst (room σ s h)) g po

/-- A piece whose stage carries a fact `X` along, which the piece keeps. -/
theorem VP.with {F G X : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hX : ∀ σ s, F σ s → X σ s → WP isa c s fun t => G σ t → X σ t) :
    VP (fun σ s => F σ s ∧ X σ s) c (fun σ s => G σ s ∧ X σ s) :=
  VP.of_ct (fun _ _ => h.ct.mono (fun _ _ hh => ⟨_, _, hh.1.1, hh.2.1⟩) fun _ _ _ => trivial)
    fun σ s ⟨hf, hx⟩ => WP.mono (WP.and (h.wp σ s hf) (hX σ s hf hx)) fun _ ⟨g, k⟩ => ⟨g, k g⟩

/-- A piece that is constant time when some of its inputs agree. -/
theorem VP.ct {F G : State → State → Prop} {c : Prog isa} {Pub : State → State → Prop}
    (hct : ConstantTime isa (fun _ => True) Pub c)
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → Pub s₁ s₂) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) :
    VP F c G :=
  VP.of_ct (fun _ _ _ _ _ _ _ _ h e₁ e₂ => ⟨hct _ _ _ _ _ _ trivial trivial (hpub _ _ _ _ h.1 h.2) e₁ e₂, trivial⟩)
    wp

end VG.Proof.RsaPkcs1Sig.Arm
