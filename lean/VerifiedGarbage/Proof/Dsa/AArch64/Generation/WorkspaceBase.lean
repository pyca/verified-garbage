module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-! Select the arithmetic workspace using the saved arena base. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64

theorem workspaceBase_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hB : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic = B) :
    WP isa (.block Impl.Dsa.AArch64.Generation.workspaceBase) s fun t =>
      t.gpr .x0 = B ∧ t.mem = s.mem ∧ Keep [.x0, .x3] s t := by
  have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s.mem) (by
    unfold Impl.Dsa.AArch64.Generation.workspaceBase
    brun [exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw]
    exact hB) rfl rfl rfl) fun _ ⟨⟨hb, hm⟩, hk⟩ => ⟨hb, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation
