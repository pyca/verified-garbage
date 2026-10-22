module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideBody
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import Mathlib.Algebra.GroupWithZero.Nat
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import Mathlib.Algebra.GroupWithZero.Nat
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! A 128-byte tile leaks only public addresses: the digit reaches the
comparison's flags and the mask, and the number of tiles and every address
depend only on the public width. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx SelP)

def WStepPre (q : XPub × Nat) (s : State) : Prop :=
  ∃ mi X Xc, TableCtx s (off q.1.B q.1.o) q.1.wx mi X Xc ∧
    word s.mem (off q.1.B q.1.o) (8 * Crt.sTab) = off (off q.1.B q.1.o) (slot q.1.wx 8) ∧
    s.gpr .x6 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧
    s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT + 128 * q.2)

def WScanPins (q : XPub × Nat) (s : State) : Prop :=
  s.gpr .x16 = off (off q.1.B q.1.o) (slot q.1.wx 8 + 128 * q.2) ∧
  s.gpr .x6 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧
  s.gpr .x14 = BitVec.ofNat 64 32 ∧
  s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT + 128 * q.2)

theorem wstep_pins : Pins WStepPre [.x0,.x17] := by
  intro q s t hs ht r hr
  obtain ⟨_,_,_,cs,_,_,ps⟩ := hs
  obtain ⟨_,_,_,ct,_,_,pt⟩ := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact cs.good.x0.trans ct.good.x0.symm
  · exact ps.trans pt.symm

theorem wscan_pins : Pins WScanPins [.x16,.x6,.x14,.x17] := by
  intro q s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem wstep_ct : RelCT isa (Two WStepPre) rawWide (fun _ _ => True) := by
  unfold rawWide
  refine RelCT.seq (two_piece (Ψ := WScanPins) [.x0,.x17] wstep_pins (by taint_decide) ?_)
    (two_taint [.x16,.x6,.x14,.x17] wscan_pins (by taint_decide))
  rintro q s ⟨mi,X,Xc,hc,ht,h6,h17⟩
  exact WP.mono (startWide_ok (v := 0) hc ht h17) fun u ⟨h14,h0,_,ku⟩ =>
    ⟨by simpa using h0.ptr, (ku.gpr .x6 (by decide)).trans h6, h14,
      (ku.gpr .x17 (by decide)).trans h17⟩

def WLoopPre (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ s₀ mi X Xc v, WLoopInv s₀ (off p.B p.o) p.wx mi X Xc v j s ∧
    16 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 32 ∧
    s.gpr .x13 = BitVec.ofNat 64 (p.wx / 16 - j)

theorem wloopPre_step {p : XPub} {j : Nat} {s : State} (h : WLoopPre p j s) :
    WStepPre (p,j) s := by
  obtain ⟨_,mi,X,Xc,v,hI,_⟩ := h
  exact ⟨mi,X,Xc,hI.ctx,hI.tab,hI.stride,hI.ptr⟩

theorem wloop_ct : RelCT isa (Two fun p s => 0 < p.wx / 16 ∧ WLoopPre p 0 s)
    (.loop rawWide (.nonzero .x .x13))
    (Two fun (p : XPub) s => s.gpr .x0 = off p.B p.o) := by
  apply two_loop (Φ := WLoopPre) (fun p : XPub => p.wx / 16)
    (two_map id (fun _ _ h => wloopPre_step h.2) wstep_ct)
  rintro p j s hj ⟨s₀,mi,X,Xc,v,hI,hw,hw',hv,h13⟩
  refine WP.mono ((rawWide_wp _ _).mpr (wloopStep_ok hv (by omega) hI)) fun t ⟨ht,hc⟩ => ?_
  have h13' : t.gpr .x13 = BitVec.ofNat 64 (p.wx / 16 - (j + 1)) := by
    rw [hc,h13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hz : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ p.wx / 16 := by
    rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.wx / 16 - (j + 1) < 2 ^ 64 by omega)]
    omega
  exact ⟨eval_nz_count hj hz, fun _ => ⟨s₀,mi,X,Xc,v,ht,hw,hw',hv,h13'⟩,
    fun _ => ht.ctx.good.x0⟩

def WidePre (p : XPub) (s : State) : Prop := SelP p s ∧ 16 ≤ p.wx ∧ p.wx % 16 = 0

theorem wsetup_ready {p : XPub} {s : State} (h : WidePre p s) :
    WP isa (.block wsetup) s fun t => 0 < p.wx / 16 ∧ WLoopPre p 0 t := by
  obtain ⟨⟨mi,X,Xc,v,hc,_,hw',hv,ht,hN⟩,hw,_⟩ := h
  refine WP.mono (wsetup_ok hc hw' hv hN) fun u ⟨⟨h6,h13,h17,h5,h7,h8,hm⟩,ku⟩ => ?_
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  refine ⟨by omega, u,mi,X,Xc,v,?_,hw,hw',hv,by simpa using h13⟩
  exact ⟨ctx,by rw [hm]; exact ht,h6,by simpa using h17,h5,h7,h8,
    Outside.refl _ _ _ _,fun _ h => by omega,Keep.refl _ _⟩

theorem wide_ct : RelCT isa (Two WidePre)
    (VG.Impl.Rsa.AArch64.WindowSelectVector.wide 32) (fun _ _ => True) := by
  rw [wide_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.wx / 16 ∧ WLoopPre p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o)
      (fun _ _ ⟨⟨_,_,_,_,hc,_⟩,_⟩ => hc.good.x0)) (by taint_decide)
    (fun _ _ h => wsetup_ready h)) ?_
  exact RelCT.seq wloop_ct (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by taint_decide))

end VG.Proof.Bignum.AArch64.WindowVector
