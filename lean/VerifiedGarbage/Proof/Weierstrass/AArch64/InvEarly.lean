module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Divstep.Alg
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.InvToM

import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyCheck
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The early finish differs only in its actual batch count and scaling constants. -/
def earlyCfg (P : InvCfg) (B m : Nat) : InvCfg :=
  let c := 2^(5*B)*(2^(64*P.M.n))^3 % m
  {P with B:=B,C:=c,Cn:=m-c}

theorem IInv.of_keeps {P : InvCfg} {base : Addr} {I : Divstep.IState} {s t : State}
    (hI : IInv P base I s) {rs : List Reg} (h : Keeps rs s t) (h1 : .x1∉rs) : IInv P base I t :=
  ⟨by rw [h.gpr _ h1]; exact hI.d, by rw [h.mem]; exact hI.f,
    by rw [h.mem]; exact hI.g, by rw [h.mem]; exact hI.a, by rw [h.mem]; exact hI.b⟩

theorem IInv.of_earlyCfg {P : InvCfg} {B m : Nat} {base : Addr} {I : Divstep.IState} {s : State}
    (h : IInv (earlyCfg P B m) base I s) : IInv P base I s := ⟨h.d,h.f,h.g,h.a,h.b⟩

theorem IInv.earlyCfg {P : InvCfg} {base : Addr} {I : Divstep.IState} {s : State}
    (h : IInv P base I s) (B m : Nat) : IInv (earlyCfg P B m) base I s := ⟨h.d,h.f,h.g,h.a,h.b⟩

theorem InvLay.earlyCfg {P : InvCfg} {size : Nat} (hL : InvLay P size) (B m : Nat) :
    InvLay (earlyCfg P B m) size := by
  exact ⟨hL.n4,hL.n10,hL.acc,hL.base,hL.tbl,hL.acc8,hL.base8,hL.tbl8,hL.mod,
    hL.acc_base,hL.acc_tbl,hL.base_tbl,hL.acc_tmp,hL.tbl_tmp,hL.mo_acc,hL.mo_tbl,hL.mo_tmp,hL.base_mo⟩

end VG.Proof.Weierstrass.AArch64
