module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInit
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopCT

/-! # Start each candidate with zero uniform witnesses and the public tape cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont
open VG.Impl.Dsa.X86.Generation

structure PrimeStartPublic (G : PrimeConfig) where
  tape : List (BitVec 8)
  used : Nat
  usedBound : used ≤ G.tapeLen

structure PrimeStartAt (G : PrimeConfig) (p : PrimeStartPublic G) (s : State) : Prop where
  ready : PrimeReady G s
  used : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 p.used
  tape : Spec.Rsa.bytesAt s.mem (G.tape.setWidth 64) G.tapeLen = p.tape

def primeInitial (G : PrimeConfig) (p : PrimeStartPublic G) : PrimeLoopPublic G :=
  ⟨p.tape, p.used, 0, p.usedBound, by unfold PrimeConfig.checks Spec.Dsa.primeChecks; split <;> decide⟩

theorem primeInit_ct (G : PrimeConfig) : RelCT isa (Two (PrimeStartAt G)) (.block primeInit)
    (Two fun p => PrimeLoopAt G (primeInitial G p)) := by
  refine two_piece [.edi] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.ready.context.scr.edi_toNat.trans ht.ready.context.scr.edi_toNat.symm)
  · intro p s R
    refine WP.mono (primeInit_ok R.ready) fun t ⟨Rt, count, used, F, _⟩ => ?_
    exact ⟨Rt, used.trans R.used, count, F.testFrame.tape.trans R.tape⟩

theorem primeLoop_ct (G : PrimeConfig) : RelCT isa (Two (PrimeStartAt G))
    (primeLoop G.len G.draw G.checks) (fun _ _ => True) :=
  RelCT.seq (primeInit_ct G) (two_map (primeInitial G) (fun _ _ h => h) (primeLoopBody_ct G))
end VG.Proof.Dsa.X86.Generation
