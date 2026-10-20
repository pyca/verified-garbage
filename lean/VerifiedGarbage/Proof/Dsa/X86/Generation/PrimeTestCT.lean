module
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInitCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePrepared
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Prime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputs
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePrepareCT

/-! # Complete primality testing depends only on the public candidate and witness tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont
open VG.Impl.Dsa.X86.Generation

structure PrimeTestAt (G : PrimeConfig) (p : PrimeStartPublic G) (s : State) : Prop where
  inputs : PrimeInputs G s
  used : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 p.used
  tape : Spec.Rsa.bytesAt s.mem (G.tape.setWidth 64) G.tapeLen = p.tape

theorem primePrepared_ct (G : PrimeConfig) : RelCT isa (Two (PrimeTestAt G))
    (primePrepare G.len) (Two (PrimeStartAt G)) := by
  refine two_post (two_map (fun _ => G) (fun _ _ h => ⟨rfl, h.inputs⟩) (primePrepare_ct G.len G.lenMin)) ?_
  intro p s R
  refine WP.mono (primePrepared_ok R.inputs) fun t ⟨Rt, used, O, _⟩ => ?_
  have F := primePrepare_testFrame O (by have := R.inputs.scratch.nowrap; omega)
  exact ⟨Rt, used.trans R.used, F.tape.trans R.tape⟩

theorem primeTest_ct (G : PrimeConfig) : RelCT isa (Two (PrimeTestAt G)) (primeTest G.len) (fun _ _ => True) := by
  have checks : (if G.len ≤ 256 then 64 else 128) = G.checks := by
    unfold PrimeConfig.checks Spec.Dsa.primeChecks
    have h : (G.len ≤ 256) ↔ 8 * G.len ≤ 2048 := by omega
    simp only [h]
  unfold primeTest
  rw [checks]
  exact RelCT.seq (primePrepared_ct G) (primeLoop_ct G)
end VG.Proof.Dsa.X86.Generation
