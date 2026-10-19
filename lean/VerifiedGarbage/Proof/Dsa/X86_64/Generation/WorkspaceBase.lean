module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega

/-! # Select the workspace without retaining a caller-saved register -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64

theorem workspaceBase_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hB : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic = B) :
    WP isa (.block Impl.Dsa.X86_64.Generation.workspaceBase) s fun t =>
      t.gpr .rdi = B ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.workspaceBase, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      sx_ofNat (by decide : Impl.Dsa.Generation.Layout.arithmetic < 2 ^ 31)]
    exact hB) rfl) fun _ ⟨⟨hb, hm⟩, hk⟩ => ⟨hb, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
