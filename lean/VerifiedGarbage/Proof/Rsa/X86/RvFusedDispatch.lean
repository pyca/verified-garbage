module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.RvFusedRest
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Rsa.X86.RvRest

/-! Public modulus length selects the recovery schedule. -/
@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys

omit rsaBatchLaw in
theorem recoveryChoice_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.recoveryChoice) s fun t =>
      KS g s0 A live AW liveW V ls t ∧ t.cf=some (decide ((g.args 5).toNat<256)) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.recoveryChoice
  refine wp_movS (h.arg (h.start.2 5 (by decide)).1 (by decide)).readSrc fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_subS rfl fun v D cf => WP.block_nil ⟨hu.of_rest D.keeps (by decide) D.mem,?_⟩
  rw [cf,U.gpr]
  rfl

theorem selectedRest_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0) (len : Lengths g)
    (h : KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [VG.Impl.Rsa.X86.Recover.aN]
      (fun _ => 2*(product g s0.mem/2)) [VG.Impl.Rsa.X86.Recover.wM] (fun _ => 0) [] s)
    (go : GoOn (product g s0.mem)) (bound : inputValue g s0.mem 0<2^(64*g.n))
    (odd : inputValue g s0.mem 0%2=1) (large : 101<inputValue g s0.mem 0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.selectedRest s (RestResult g s0) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.selectedRest
  refine WP.seq (WP.mono (recoveryChoice_ok h) fun u ⟨hu,cu⟩ => ?_)
  refine WP.seq (WP.mono (Q := FinIn g s0) ?_ fun t F => finIn_ok inputs len bound odd large F)
  rw [WP.iteCold_iff]
  refine WP.ite (decide ((g.args 5).toNat<256)) (by exact cu) ?_ ?_
  · intro _
    exact rest_ok inputs hu go bound odd large
  · intro _
    exact fusedRest_ok inputs hu go bound odd large

end VG.Proof.Rsa.X86.Recover
