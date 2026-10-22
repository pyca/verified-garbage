module

import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Weierstrass.Arm.Rep
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Stages
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder

/-! The verification pipeline can use any verified fixed-base multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.X25519.Arm
open Spec.Weierstrass

def GeneratorWP (c : Cfg) (generator : Prog isa) (s₀ : State) (base : Addr) (k : Nat)
    (Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (symbols : String → BitVec 32) : Prop :=
  ∀ s, Scr s base size → Far s base 8192 → Fixed c base s₀.gpr s.mem →
    (∀ x ∈ ladR c.ladderCfg,wordsVal s.mem base x c.MP'.n<c.C.p) →
    Step c.ladderCfg c.C base s k Q →
    Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) →
    (∀ i<64*c.n,s.mem (off base (bitsAt c.n 0+i))=if k.testBit i then 1 else 0) →
    Rest (.lr::work) s₀ s → Unch base [(0,8192)] s₀.mem s.mem → s.syms=symbols →
    WP isa generator s fun t =>
      Rest powClob s t ∧ Unch base (Point.ladWp c.ladderCfg c.wk) s.mem t.mem ∧
      ModOkW c.MP' size c.C.p t.mem base ∧
      (∀ x∈[c.sl RX,c.sl RY,c.sl RZ],wordsVal t.mem base x c.n<c.C.p) ∧
      Q 0 (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY)) (tmv c.C c.n base t (c.sl RZ))

theorem generatorWP_ladder {c : Cfg} (hc : CfgOk c) {s₀ : State} {base : Addr} {k : Nat}
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {symbols : String → BitVec 32} :
    GeneratorWP c (VG.Impl.Weierstrass.Arm.Point.ladderP c.ladderCfg c.SP) s₀ base k Q symbols := by
  intro s hs hf F hlt hstep hR bits _ _ _
  exact Point.ladderP_ok (ladLay hc) (ladWk hc) hc.fp ladPt (unitMod_pow_two hc.p_odd _)
    (bitsAt_lt hc (j := 0) (by decide)) hs hf (modP_of hc F.mp) hlt hstep hR (fun t ht => bits t (Nat.lt_of_lt_of_le ht (scalarBits_le hc))) (scalarBits_enc hc)

end VG.Proof.Ecdsa.Verify.Arm
