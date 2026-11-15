module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The number of tiles and all table addresses depend only on public widths. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)

def LoopPre (n : Nat) (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ s₀ mi X Xc v, LoopInv n s₀ (off p.B p.o) p.wx mi X Xc v j s ∧
    8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < n ∧
    s.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - j)

theorem loopPre_step {n : Nat} {p : XPub} {j : Nat} {s : State} (h : LoopPre n p j s) : StepPre n (p,j) s := by
  obtain ⟨_,mi,X,Xc,v,hI,_⟩ := h
  exact ⟨mi,X,Xc,v,hI.ctx,hI.tab,hI.stride,hI.ptr,hI.digit,hI.one⟩

theorem loop_ct {n : Nat} (hN : n = 16 ∨ n = 32) :
    RelCT isa (Two fun p s => 0 < p.wx / 8 ∧ LoopPre n p 0 s)
    (.loop (rawStep n) (.nonzero .x .x13))
    (Two fun (p : XPub) s => s.gpr .x0 = off p.B p.o) := by
  apply two_loop (Φ := LoopPre n) (fun p : XPub => p.wx / 8)
    (two_map id (fun _ _ h => loopPre_step h.2) (step_ct hN))
  rintro p j s hj ⟨s₀,mi,X,Xc,v,hI,hw,hw',hv,h13⟩
  refine WP.mono ((rawStep_wp _ _ _).mpr (loopStep_ok hN hv (by omega_using [hj]) hI)) fun t ⟨ht,hc⟩ => ?_
  have h13' : t.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - (j + 1)) := by
    rw [hc,h13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hj]
  have hz : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ p.wx / 8 := by
    rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.wx / 8 - (j + 1) < 2 ^ 64 by omega_using [hw'])]
    omega_using [hj]
  exact ⟨eval_nz_count hj hz, fun _ => ⟨s₀,mi,X,Xc,v,ht,hw,hw',hv,h13'⟩,
    fun _ => ht.ctx.good.x0⟩

def BlockPreN (n : Nat) (p : XPub) (s : State) : Prop := SelPn n p s ∧ 8 ≤ p.wx

theorem setup_ready {n : Nat} {p : XPub} {s : State} (h : BlockPreN n p s) :
    WP isa (.block setup) s fun t => 0 < p.wx / 8 ∧ LoopPre n p 0 t := by
  obtain ⟨⟨mi,X,Xc,v,hc,_,hw',hv,ht,hN⟩,hw⟩ := h
  refine WP.mono (setup_ok hc hw' hN) fun u ⟨⟨h6,h13,h17,h22,h24,hm⟩,ku⟩ => ?_
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  refine ⟨by omega_using [hw], u,mi,X,Xc,v,?_,hw,hw',hv,by simpa using h13⟩
  exact ⟨ctx,by rw [hm]; exact ht,h6,by simpa using h17,h22,h24,
    Outside.refl _ _ _ _,fun _ h => by omega,Keep.refl _ _⟩

theorem blockedN_ct {n : Nat} (hN : n = 16 ∨ n = 32) : RelCT isa (Two (BlockPreN n))
    (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked n) (fun _ _ => True) := by
  rw [blocked_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.wx / 8 ∧ LoopPre n p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o)
      (fun _ _ ⟨⟨_,_,_,_,hc,_⟩,_⟩ => hc.good.x0)) (by taint_decide)
    (fun _ _ h => setup_ready h)) ?_
  refine RelCT.seq (loop_ct hN) ?_
  rcases hN with rfl | rfl <;>
  · exact x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by taint_decide)
structure GuardCtx (n : Nat) (p : XPub) (s : State) : Prop where
  sel : SelPn n p s
  width : s.gpr .x3 = BitVec.ofNat 64 (p.wx / 8)
  rem : s.gpr .x4 = BitVec.ofNat 64 (p.wx % 8)

theorem guard_ready {n : Nat} {p : XPub} {s : State} (h : SelPn n p s) :
    WP isa (.block guard) s (GuardCtx n p) := by
  obtain ⟨mi,X,Xc,v,hc,hw,hw',hv,ht,hN⟩ := h
  refine WP.mono (guard_ok hc hw') fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_
  exact ⟨⟨mi,X,Xc,v,hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr
    (ku.gpr .x0 (by decide)),hw,hw',hv,hm ▸ ht,hm ▸ hN⟩,h3,h4⟩

theorem guard_width {n : Nat} {p : XPub} {s : State} (h : GuardCtx n p s)
    (ht : isa.eval (.nonzero .x .x3) s = some true) : 8 ≤ p.wx := by
  obtain ⟨_,_,_,_,_,_,hw',_⟩ := h.sel
  rw [eval_nonzero,h.width,ne_zero_iff,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show p.wx / 8 < 2 ^ 64 by omega_using [hw'])] at ht
  have := of_decide_eq_true (Option.some.inj ht)
  omega_using [this]

/-- The selection leaks the same in runs with the same workspace, as its
`fallback` does. -/
theorem select_ct {n : Nat} (hN : n = 16 ∨ n = 32) {fallback : Prog isa}
    (hf : RelCT isa (Two (SelPn n)) fallback (fun _ _ => True)) :
    RelCT isa (Two (SelPn n)) (VG.Impl.Rsa.AArch64.WindowSelectVector.select n fallback) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowSelectVector.select
  refine RelCT.seq (two_piece (Ψ := GuardCtx n) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨_,_,_,_,hc,_⟩ => hc.good.x0))
    (by taint_decide) (fun _ _ h => guard_ready h)) ?_
  refine two_ite (Φ := GuardCtx n) ?_ ?_ ?_
  · intro p s t hs ht
    rw [eval_nonzero,eval_nonzero,hs.width,ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro p s t hs ht
      rw [eval_zero,eval_zero,hs.1.rem,ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.sel,guard_width h.1.1 h.1.2⟩) (blockedN_ct hN)
    · exact two_map id (fun _ _ h => h.1.1.sel) hf
  · exact two_map id (fun _ _ h => h.1.sel) hf

end VG.Proof.Bignum.AArch64.WindowVector
