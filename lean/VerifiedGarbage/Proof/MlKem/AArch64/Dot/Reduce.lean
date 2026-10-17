module

public import VerifiedGarbage.Impl.MlKem.AArch64.Dot
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

/-! Canonical reduction of the fused dot-product accumulators. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Dot

open VG.AArch64 VG.Impl.MlKem.AArch64

theorem reduce_ok {d : VReg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hd : d ≠ .v24) (hd16 : d ≠ .v16) (hd17 : d ≠ .v17)
    (hc : VConsts s) {f : Nat → Nat} (hf : Lanes (s.v d) f)
    (hlt : ∀ e < 4, f e < 2 ^ 31)
    (k : ∀ s', VChg [.v24, d] s s' →
      Lanes (s'.v d) (fun e => f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.Dot.dotReduce d ++ rest)) s Q := by
  change WP isa (.block (.vop (.sqdmulh .v24 d .v17) ::
    .vop (.mls d .v24 .v16) :: vcsub d .v24 ++ rest)) s Q
  refine vbar_ok hd (hc := hc) (hf := hf) (hlt := hlt) (k := fun s₁ h₁ l₁ b₁ => ?_)
  have c₁ := hc.chg h₁ (by simp [hd16.symm]) (by simp [hd17.symm])
  refine vcsub_ok hd c₁.q l₁ (fun e he => (b₁ e he).1) fun s₂ h₂ l₂ => ?_
  exact k s₂ ((h₁.trans h₂).mono (by simp)) (l₂.congr fun e he => (b₁ e he).2)

end VG.Proof.MlKem.AArch64.Dot
