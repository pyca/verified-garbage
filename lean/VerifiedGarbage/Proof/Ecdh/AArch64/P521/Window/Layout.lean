module

import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Inverse
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64.Window
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Double
public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep

/-! # The shortened window retains the existing workspace and field layout -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521.Window

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont
open VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64.P521Window
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Spec.Weierstrass

theorem layout (hc : CfgOk c) : WinLay cfg size := by
  have h := winLayQ hc
  exact ⟨h.lay,h.ro,h.nodup,h.tbl,h.n0,by decide,by decide,by decide +kernel⟩

theorem aligned (hc : CfgOk c) : WinA cfg := by
  have h := winAQ hc
  exact ⟨h.sl,h.mod,by decide,h.call⟩

theorem doubles_ok (hc : CfgOk c) (base : Addr) :
    DblsOk cfg c.C base size (some doubles) :=
  scheduled_doubles (layout hc) (aligned hc) (unitMod_pow_two hc.p_odd _)

theorem inverse_spec (hc : CfgOk c) (base : Addr) :
    InvSpecW cfg c.C base size (Impl.Ecdh.AArch64.Cfg.invJ c) (invJClob c.n) (invJW c) :=
  inverse_for c hc cfg.bits cfg.J (by decide +kernel) (by decide +kernel)

end VG.Proof.Ecdh.AArch64.P521.Window
