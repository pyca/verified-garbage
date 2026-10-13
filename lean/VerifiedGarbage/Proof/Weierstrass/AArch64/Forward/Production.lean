module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256DR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256ED
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Spec.Ecdsa.Generic

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.Production

theorem cases : Fixed.Cases where
  rd := ⟨P256RD.checked,P256Bounds.rd_left,P256Bounds.rd_right,P256Bounds.rd_clob⟩
  dr := ⟨P256DR.checked,P256Bounds.dr_left,P256Bounds.dr_right,P256Bounds.dr_clob⟩
  ed := ⟨P256ED.checked,P256Bounds.ed_left,P256Bounds.ed_right,P256Bounds.ed_clob⟩

end VG.Proof.Weierstrass.AArch64.Forward.Production
