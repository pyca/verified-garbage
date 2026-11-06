module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Weierstrass.AArch64.ArithmeticTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableState
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
/-! ## `JointPrep` -/

-- Formerly `VerifiedGarbage/Proof/Weierstrass/AArch64/ArithmeticTable.lean`, which only this module imported.

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

def jointPrepRanges : List (Nat×Nat) := [(P256Joint.cfg.gBits,520),(P256Joint.cfg.K.bits,264)]

def jointPrepProgram : Prog isa :=
  .seq (Joint.gPrep P256Joint.cfg (p256.sl U))
    (Impl.Weierstrass.AArch64.FastNaf.prep P256Joint.cfg.K (p256.sl V) 5)

structure JointPrepPost (base : Addr) (g : Reg → BitVec 64) (P : Point p256.C) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jacWinSlots P256Joint.cfg.K)
    (winRo P256Joint.cfg.K) (tmv p256.C 4 base t) t
  peer : NafWindowInput P256Joint.cfg.K p256.C base P (sv p256 base s V) t
  generator : ∀ i<jointGLen P256Joint.cfg,t.mem (off base (P256Joint.cfg.gBits+i))=
    jointGByte P256Joint.cfg (sv p256 base s U) i
  fixed : Fixed p256 base g t.mem
  one : tmv p256.C 4 base t P256Joint.cfg.onep=1
  same : ∀ i<45,sv p256 base t i=sv p256 base s i
  keep : KeepRegs nafPrepClob s t
  unch : Unch base jointPrepRanges s.mem t.mem
  syms : t.syms=s.syms

theorem apart_jointPrep {i : Nat} (hi : i<45) :
    ∀ w∈jointPrepRanges,p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i := by
  intro w hw
  simp only [jointPrepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · apply Or.inl; rw [sl_eq4 p256 (by decide)]; change 64+32*i+32≤2112; omega
  · apply Or.inl; rw [sl_eq4 p256 (by decide)]; change 64+32*i+32≤1824; omega

theorem jointPrepStage_ok (hc : CfgOk p256) (hC : Law p256.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed p256 base g s.mem) {P : Point p256.C}
    (hpx : sv p256 base s PX<p256.C.p) (hpy : sv p256 base s PY<p256.C.p)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa jointPrepProgram s (JointPrepPost base g P s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x,p256.mont x<p256.C.p := fun x => Nat.mod_lt _ (by omega)
  refine WP.mono_syms (Weierstrass.AArch64.jointPrep_ok P256Joint.cfg hs
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr JointLayout.bits_disjoint) (by decide)) fun s₂ ⟨hs₂,bG,bQ,k₂,U₂⟩ sy₂ => ?_
  have F₂ := F.unch h7 hn (W:=jointPrepRanges) (by unfold FixedOk jointPrepRanges; decide) U₂
  have e₂ : ∀ {i},i<45 → sv p256 base s₂ i=sv p256 base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_jointPrep hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv p256.C p256.n base s₂ (p256.sl i) = tmv p256.C p256.n base s (p256.sl i) := fun hi => by
    show toM _ _ (sv p256 base s₂ _) = toM _ _ (sv p256 base s _); rw [e₂ hi]
  have hlt : ∀ x∈winRo (P256Joint.cfg.K),wordsVal s₂.mem base x p256.n<p256.C.p := by
    intro x hx
    simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega)
    · exact lt_of_eq_of_lt (e₂ (i:=PX) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i:=PY) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
  have hI : Inv (P256Joint.cfg.K).M base size p256.C.p (·∈jacWinSlots (P256Joint.cfg.K))
      (winRo (P256Joint.cfg.K)) (tmv p256.C p256.n base s₂) s₂ :=
    ⟨hs₂,hM₂,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),hlt,fun _ _ => rfl⟩
  have one : tmv p256.C p256.n base s₂ (p256.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (p256.sl ONEP) p256.n)=1
    rw [F₂.onep]
    have hm1 := toM_cmont hc.toBaseCfgOk 1
    have ho : Fin.ofNat p256.C.p 1 = (1:Fe p256.C) := by rfl
    simpa only [Cfg.mont,Cfg.R,Nat.one_mul,ho] using hm1
  have hp : Rep p256.C (tmv p256.C p256.n base s₂ (p256.sl PX)) (tmv p256.C p256.n base s₂ (p256.sl PY))
      (tmv p256.C p256.n base s₂ (p256.sl ONEP)) P := by
    rw [tv (by decide),tv (by decide),tv (by decide)]; exact hrep
  have hj : InvJ p256.C (tmv p256.C p256.n base s₂ (p256.sl PX)) (tmv p256.C p256.n base s₂ (p256.sl PY))
      (tmv p256.C p256.n base s₂ (p256.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one,Lean.Grind.Semiring.mul_one] using hh
  exact ⟨hI,⟨F₂.zero,fun i hi => bQ i hi,hj⟩,bG,F₂,one,fun _ hi => e₂ hi,k₂,U₂,sy₂⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

/-- The points stage writes only arithmetic work, public digits, and precomputation. -/
def jointPointRanges : List (Nat×Nat) :=
  [(128,32),(512,544),(1824,808),(2848,1536),(5400,64),(6000,512)]

theorem jointPoint_prep : ∀ w∈jointPrepRanges,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointTable` -/

/-! ## `JointSetup` -/

/-! ## `JointPoints` -/

