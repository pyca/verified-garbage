module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Dsa.RelCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Small facts about RSA's AArch64 workspaces that DSA's proofs use -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

export VG.Proof.Dsa (RelCT.assoc')

theorem SubCtx.of_keep {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List Reg}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem) (k : Keep rs s t) (hr : Reg.x0 ∉ rs) :
    SubCtx t B Z o w wx minv :=
  h.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k.wr (k.gpr _ hr)

end VG.Proof.Dsa.AArch64

namespace VG.Proof.MlKem.AArch64
open VG VG.AArch64

/-- Composition of two runs that keep the same registers. -/
theorem Keep.trans' {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) :
    Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp, fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

end VG.Proof.MlKem.AArch64
