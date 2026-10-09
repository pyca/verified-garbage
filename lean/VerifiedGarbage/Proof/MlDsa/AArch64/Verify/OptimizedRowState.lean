import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowReady

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized VG.Proof.MlDsa.Arith.Montgomery

abbrev RowData (p : Params) (σ : State) (A : Nat→Nat→Poly) (c : Poly) (r stage : Nat) (s : State) : Prop :=
  match stage with
  | 0 => W p σ A r s
  | 1 => W p σ A r s ∧ PolyIs s.mem (pa s (tmP p)) (rU p σ r)
  | 2 => W p σ A r s ∧ PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)
  | 3 => W p σ A r s ∧ PolyIs s.mem (pa s (tm2P p))
      (montgomeryMultiplyNTT (ntt c) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))
  | 4 => PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A c r))
  | _ => PolyIs s.mem (pa s (wP p)) (Proof.MlDsa.Verify.wRow p (vPk p σ) (vSig p σ) A (ntt c) r)

abbrev RowI (p : Params) (S r stage : Nat) (σ s : State) : Prop :=
  ∃h A c q,SC p S σ h A c q p.ℓ true r s ∧ RowData p σ A c r stage s

end VG.Proof.MlDsa.AArch64.Verify.Optimized
