module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MontgomeryOne
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Framework.Omega

/-! Public-context writes leave the loaded modulus and R² unchanged. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem FieldInitial.after_workspace {p : Parameters} {s t : State} (h : FieldInitial p s)
 (good : Good t p.B p.Z p.w p.mi) (same : ∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) : FieldInitial p t := by
 have inverseWord : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) :=
  workspace_word (by have := h.good.scr.nowrap;omega) same
   (by have := slot_le (w:=p.w) (by decide : 0<8);have := p.room;have := p.positive;omega)
 refine ⟨good,(workspace_array h.good same (by decide)).trans h.modulus,?_,
  (workspace_array h.good same (by decide)).trans h.r2⟩
 rw [inverseWord]
 exact h.inverse

end VG.Proof.Ffdh.AArch64.Cached
