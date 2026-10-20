module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Algebra.GroupWithZero.Nat
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The number of tiles and all table addresses depend only on public widths. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx SelP)

def LoopPre (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ s₀ mi X Xc v, LoopInv s₀ (off p.B p.o) p.wx mi X Xc v j s ∧
    8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 32 ∧
    s.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - j)

theorem loopPre_step {p : XPub} {j : Nat} {s : State} (h : LoopPre p j s) : StepPre (p,j) s := by
  obtain ⟨_,mi,X,Xc,v,hI,_⟩ := h
  exact ⟨mi,X,Xc,v,hI.ctx,hI.tab,hI.stride,hI.ptr,hI.digit,hI.one⟩

theorem loop_ct : RelCT isa (Two fun p s => 0 < p.wx / 8 ∧ LoopPre p 0 s)
    (.loop rawStep (.nonzero .x .x13))
    (Two fun (p : XPub) s => s.gpr .x0 = off p.B p.o) := by
  apply two_loop (Φ := LoopPre) (fun p : XPub => p.wx / 8)
    (two_map id (fun _ _ h => loopPre_step h.2) step_ct)
  rintro p j s hj ⟨s₀,mi,X,Xc,v,hI,hw,hw',hv,h13⟩
  refine WP.mono ((rawStep_wp _ _).mpr (loopStep_ok hv (by omega) hI)) fun t ⟨ht,hc⟩ => ?_
  have h13' : t.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - (j + 1)) := by
    rw [hc,h13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hz : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ p.wx / 8 := by
    rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.wx / 8 - (j + 1) < 2 ^ 64 by omega)]
    omega
  exact ⟨eval_nz_count hj hz, fun _ => ⟨s₀,mi,X,Xc,v,ht,hw,hw',hv,h13'⟩,
    fun _ => ht.ctx.good.x0⟩

def BlockPre (p : XPub) (s : State) : Prop := VG.Proof.Bignum.AArch64.WindowFive.SelP p s ∧ 8 ≤ p.wx

theorem setup_ready {p : XPub} {s : State} (h : BlockPre p s) :
    WP isa (.block setup) s fun t => 0 < p.wx / 8 ∧ LoopPre p 0 t := by
  obtain ⟨⟨mi,X,Xc,v,hc,_,hw',hv,ht,hN⟩,hw⟩ := h
  refine WP.mono (setup_ok hc hw' hN) fun u ⟨⟨h6,h13,h17,h22,h24,hm⟩,ku⟩ => ?_
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  refine ⟨by omega, u,mi,X,Xc,v,?_,hw,hw',hv,by simpa using h13⟩
  exact ⟨ctx,by rw [hm]; exact ht,h6,by simpa using h17,h22,h24,
    Outside.refl _ _ _ _,fun _ h => by omega,Keep.refl _ _⟩

theorem blocked_ct : RelCT isa (Two BlockPre)
    (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32) (fun _ _ => True) := by
  rw [blocked_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.wx / 8 ∧ LoopPre p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o)
      (fun _ _ ⟨⟨_,_,_,_,hc,_⟩,_⟩ => hc.good.x0)) (by taint_decide)
    (fun _ _ h => setup_ready h)) ?_
  exact RelCT.seq loop_ct (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by taint_decide))

end VG.Proof.Bignum.AArch64.WindowVector
