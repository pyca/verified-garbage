import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized (power2RoundAt)
open VG.Impl.MlDsa.AArch64.Call (Ptr)

theorem p2rAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
    (hc : p2rChk rbs wbs t t1 t0 = true) (hr : Reduced s.mem (pa s t)) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P t t1 t0) s fun s' => PPostB S s s' [(t1, 1024), (t0, 1024)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s t1) ((polyAt s.mem (pa s t)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (pa s t0) ((polyAt s.mem (pa s t)).map fun c => ofInt (power2Round c).2) := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (p2r_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => p2r_pre L hc hr h1) (p2r_cov L hc).1 (p2r_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
