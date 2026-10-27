module

import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Stages
public import VerifiedGarbage.Proof.Ecdsa.Arm.MulFn
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
    sv c base s RX = 0 → sv c base s RY = c.mont 1 → sv c base s RZ = 0 →
    (c.mul = none → ∀ i<64*c.n,s.mem (off base (bitsAt c.n 0+i))=if k.testBit i then 1 else 0) →
    (c.mul.isSome → sv c base s K = k) →
    Rest (.lr::work) s₀ s → Unch base [(0,8192)] s₀.mem s.mem → s.syms=symbols →
    WP isa generator s fun t =>
      Rest powClob s t ∧ Unch base (Point.ladWp c.ladderCfg c.wk ++ genX c) s.mem t.mem ∧
      ModOkW c.MP' size c.C.p t.mem base ∧
      (∀ x∈[c.sl RX,c.sl RY,c.sl RZ],wordsVal t.mem base x c.n<c.C.p) ∧
      Q 0 (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY)) (tmv c.C c.n base t (c.sl RZ))

/-- The ladder inline, for a curve without `vg_<curve>_mul`. -/
theorem generatorWP_ladder {c : Cfg} (hc : CfgOk c) (hn : c.mul = none) {s₀ : State} {base : Addr} {k : Nat}
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {symbols : String → BitVec 32} :
    GeneratorWP c (VG.Impl.Weierstrass.Arm.Point.ladderP c.ladderCfg c.SP) s₀ base k Q symbols := by
  intro s hs hf F hlt hstep hR _ _ _ bits _ _ _ _
  exact WP.mono (Point.ladderP_ok (ladLay hc) (ladWk hc) hc.fp ladPt (unitMod_pow_two hc.p_odd _)
    (bitsAt_lt hc (j := 0) (by decide)) hs hf (modP_of hc F.mp) hlt hstep hR
    (fun t ht => bits hn t (Nat.lt_of_lt_of_le ht (scalarBits_le hc))) (scalarBits_enc hc))
    fun t ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩

/-- `gen`: the call or the ladder, for an invariant that accepts `O`. -/
theorem generatorWP_gen {c : Cfg} (hc : CfgOk c) {s₀ : State} {base : Addr} {k : Nat}
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {symbols : String → BitVec 32} (hO : Q (8 * c.C.len) 0 1 0) :
    GeneratorWP c c.gen s₀ base k Q symbols := by
  intro s hs hf F _ hstep _ hrx hry hrz bits hk _ _ _
  exact qMul_ok hc hs hf F (px := GX) (py := GY) (by decide) (lt_of_eq_of_lt F.gx (Nat.mod_lt _
    (by have := hc.p_ge; omega))) (lt_of_eq_of_lt F.gy (Nat.mod_lt _ (by have := hc.p_ge; omega)))
    hrx hry hrz hstep hO hk bits

end VG.Proof.Ecdsa.Verify.Arm
