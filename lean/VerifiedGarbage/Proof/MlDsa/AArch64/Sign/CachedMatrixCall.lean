import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedMatrix

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- The concrete sampler always uses at most six SHAKE128 blocks. -/
theorem two_max {s t : State} {tr : List Leak}
    (h : (rejNTT2Contract abi).pre s) (e : Exec isa Two.code s tr t)
    (h1 : (t.gpr .x0).setWidth 32=1) :
    ∀k<2,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (s.gpr .x0) k)).isSome := by
  obtain ⟨_,u,eu,hu⟩ := two_ok (pre_two h)
  obtain ⟨_,rfl⟩ := Exec.det e eu
  have hall : ∀k<2,(prefixRow s k 1008).length=256 := by
    by_contra hn
    rw [hu.status,ite_eq_right hn] at h1
    cases h1
  intro k hk
  have hh := hall k hk
  rw [prefixRow_spec] at hh
  have hs := VG.Proof.MlDsa.Sample.rejNTT_some hh
  have hm := VG.Proof.MlDsa.Sign.rejNTTPoly_mono (show 1008≤maxBounds.rejNTT by decide) hs
  change (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (seedP s) k)).isSome=true
  rw [hm]; rfl

 theorem callee {S : Nat} (hS : S<2^64) : CalleeOk S Two.code (rejNTT2Contract abi S) :=
  CalleeOk.of_verified hS two_verified (Nat.zero_le _) (by
    have hd : Two.code.aarch64Depth=0 := by decide +kernel
    simp only [hd,Nat.mul_zero]; exact Nat.zero_le _)

open VG.Proof.MlDsa.AArch64.KeyGen.Optimized

theorem rej2Call_ok {D : Nat} (hD : D<2^64) {p : Params} {s : State} (L : Lay D (sgR p) (sgW p) s)
    {seed a ss : Ptr} (hc : rej2Chk (sgR p) (sgW p) seed a ss = true) :
    WP isa (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args seed a ss)) s fun t =>
      PPostB D s t [(a,2048),(ss,8192)] ∧ t.gpr .x24 = s.gpr .x24 ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 2,Reduced t.mem (poly4 (pa s a) k)) ∧
      (((t.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 2,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt t.mem (poly4 (pa s a) k))) ∨
        ((t.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 2,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 2,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (pa s seed) k)).isSome) := by
  have hc' := hc
  simp only [rej2Chk,Bool.and_eq_true,and_assoc] at hc'
  obtain ⟨_,_,_,c4,c5,c6,_,_⟩ := hc'
  refine WP.mono (callAt_ok L.s64 ((callee hD).withPost (fun _ _ _ h e => two_max (pre_stack (Nat.zero_le D) hD h) e)) (rej2_args L.ok c4 c5 c6)
    (by simp only [List.map_cons,List.map_nil]; decide) (fun s1 h1 => rej2_pre L hc h1) (rej2_cov L hc).1
    (rej2_cov L hc).2) fun t ⟨hp,s1,h1,hq,hx⟩ => ⟨hp.b,hp.cs .x24 (by decide) (by decide),?_⟩
  sig_post [rejNTT2Contract,rejNTT2Sig,AArch64.abi,AArch64.argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  simp only [State.withRegions_gpr,State.withRegions_mem,State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),Args.r0 h1,Args.mem h1,Arg.val] at hx
  exact ⟨hq.1,hq.2,hx⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
