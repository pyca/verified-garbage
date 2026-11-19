module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCommitmentCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCommitmentCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck
import Mathlib.Tactic.FinCases
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck
meta import Mathlib.Tactic.FinCases
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedConsts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedConsts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedMatrix
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedMatrix
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Top
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
meta import VerifiedGarbage.Spec.MlDsa
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Top
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds

/-! ### `MlDsa.AArch64.Sign.CachedMatrixTiming`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedMatrixRoots`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedMatrixBatch`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedMatrixCall`, which this module and modules that import it used -/

section

@[expose] public section

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
    simp only [hd,Nat.mul_zero]; exact Nat.zero_le _) (by lit_decide)

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

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Proof.MlDsa.Sign

theorem aseeds2_eq {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 2 s) {k : Nat} (hk : k<2) :
    seed4 s.mem (pa s (sc oRS4)) k=seedE p σ (e+k) := by
  unfold seed4
  rw [pa_sc_add]
  exact h.done k hk

def twoChk (p : Params) (e : Nat) : Bool :=
  let a := pS (aBase p+e)
  let ws : List (Ptr × Nat) := [(a,2048),(sc (oR4 p),8192)]
  rej2Chk (sgR p) (sgW p) (sc oRS4) a (sc (oR4 p)) && stChk p ws && stChk p [] &&
    keepB (sgR p) (sgW p) ws (sc oRS) 32 && famChk (sgR p) (sgW p) ws (aBase p) (e)

theorem twoBatch_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : twoChk p e = true) {s : State} (h : AS p D σ (e) 2 s) :
    WP isa (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code
      (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p)))) (.block and24)) s
      (IA p D σ (e+2)) := by
  simp only [twoChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨cr,cst⟩,c0⟩,crs⟩,cfam⟩ := hc
  refine WP.seq (WP.mono (rej2Call_ok hP.s64 h.ia.st.lay cr) fun s1 ⟨hp,h24,hred,hout,hmax⟩ => ?_)
  have S1 := h.ia.st.step hp cst
  refine WP.mono (and24_ok s1) fun t ⟨kt,et⟩ => ?_
  have hpt : PPostB D s1 t [] := postB24 kt _
  have hr : (s1.gpr .x0).setWidth 32 = 1 ∨ (s1.gpr .x0).setWidth 32 = 0 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inl h1,.inr h0]
  have et' : t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s1.gpr .x0).setWidth 32) := by rw [et,h24]
  refine ⟨S1.step hpt c0,by rw [kt.mem,hpt.pa (by decide),h.ia.st.lay.keepBytes hp crs]; exact h.ia.rs,
    ?_,fun ht => ?_,fun ht => ?_⟩
  · rw [et']
    rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] <;> decide
  · have hs : s.gpr .x24 = 1 ∧ (s1.gpr .x0).setWidth 32 = 1 := by
      rw [et'] at ht
      rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] at ht <;>
        first | exact ⟨e0,e1⟩ | exact absurd ht (by decide)
    obtain ⟨ok,fam⟩ := h.ia.ok hs.1
    have fm := Fam.of_eq kt.mem (hpt.bs _ (by decide)) (Fam.keep h.ia.st.lay hp cfam fam)
    refine ⟨fun e' he' => ?_,fun e' he' => ?_⟩
    · by_cases hlt : e' < e
      · exact ok e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega_using [hlt]⟩
        rw [← aseeds2_eq h (by omega_using [he'])]; exact hmax hs.2 k (by omega_using [he'])
    · by_cases hlt : e' < e
      · exact fm e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega_using [hlt]⟩
        have hk : k < 2 := by omega_using [he']
        have hm := hmax hs.2 k hk
        have hv : polyAt s1.mem (poly4 (pa s (pS (aBase p+e))) k) = aVal p σ (e+k) := by
          obtain ⟨_,hb⟩ | ⟨h0,_⟩ := hout
          · have hv := rej_val (.inl ⟨hs.2,hb k hk⟩) hs.2 hm
            rw [aseeds2_eq h hk] at hv
            exact hv
          · rw [hs.2] at h0; cases h0
        show PolyIs t.mem (pa t (pS (aBase p+(e+k)))) (aVal p σ (e+k))
        rw [kt.mem,hpt.pa (by change Reg.x28 ∈ keptRegs; decide),hp.pa (by change Reg.x28 ∈ keptRegs; decide),← Nat.add_assoc,← pa_poly4]
        exact ⟨hred hs.2 k hk,hv⟩
  · rw [et'] at ht
    rcases h.ia.r01 with e0 | e0
    · obtain ⟨e',he',hn⟩ := h.ia.bad e0; exact ⟨e',by omega_using [he'],hn⟩
    · rcases hr with e1 | e1
      · rw [e0,e1] at ht; exact absurd ht (by decide)
      · rcases hout with ⟨h1,_⟩ | ⟨_,k,hk,hn⟩
        · exact absurd (e1.symm.trans h1) (by decide)
        · exact ⟨e+k,by omega_using [hk],by rw [← aseeds2_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

end

/-! ## From `CachedMatrixExpansion.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.Sign

 theorem tail_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {σ s : State}
    (h : IA mlDsa65 D σ 28 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65) s (IA mlDsa65 D σ 30) := by
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
  refine WP.seq (WP.mono (seqR_ok (I:=AS mlDsa65 D σ 28) 2 0
    (fun j _ hj s hs=>WP.mono (slot4_ok (by omega_using [hj])
      (slotChk_ok mlDsa65 (by simp) 28 (by decide) j (by omega_using [hj])) hs) fun _ ht=>ht.1)
    s ⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩) fun t ht=>?_)
  exact twoBatch_ok hP (show twoChk mlDsa65 28=true by decide) (by simpa using ht)

 theorem sampleAll65_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {σ s : State}
    (h : IA mlDsa65 D σ 0 s) :
    WP isa (.seq (seqR (sample4 P mlDsa65) 0 7) (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65))
      s (IA mlDsa65 D σ 30) := by
  refine WP.seq (WP.mono (seqR_ok (I:=fun g=>IA mlDsa65 D σ (4*g)) 7 0
    (fun g _ hg s hs=>sample4_ok hP (batchChk_ok mlDsa65 (by simp) g (by change g<7; omega_using [hg]))
      (fun j hj=>slotChk_ok mlDsa65 (by simp) (4*g) (by change 4*g<30; omega_using [hg]) j hj) hs)
    s h) fun t ht=>?_)
  exact tail_ok hP (by simpa using ht)

 theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) (hc : aChk p=true) {σ s : State} (hs : St p D σ s) (h15 : s.gpr .x24=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) s (IA p D σ (p.k*p.ℓ)) := by
  rcases h3 with rfl|rfl|rfl
  · exact Sign.expandA_ok hP (.inl rfl) hc hs h15
  · have hc' := hc
    simp only [aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc'
    obtain ⟨⟨⟨_,hcp⟩,hst⟩,hsk⟩ := hc'
    change WP isa (.seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS)) _) s _
    refine WP.seq (WP.mono (copyP_ok hs.lay hcp) fun s1 ⟨hP1,hcs1,hb⟩=>?_)
    have S1 := hs.step hP1 hst
    have e15 : s1.gpr .x24=1 := by rw [hcs1.get .x24,h15]
    exact sampleAll65_ok hP ⟨S1,by rw [hP1.pa (by decide),hb,rhoOf,←hs.sk,VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15,fun _=>⟨fun _ h=>absurd h (Nat.not_lt_zero _),fun _ h=>absurd h (Nat.not_lt_zero _)⟩,
      fun h0=>absurd (h0.symm.trans e15) (by decide)⟩
  · exact Sign.expandA_ok hP (.inr (.inr rfl)) hc hs h15

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

/-! ## From `CachedMatrixRoots.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message

 /-- The expansion's frames are within `S` and it never touches PSTATE.DIT
(`DLe`). -/
private theorem expandA_dle {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params) :
    DLe (S/16) (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) := by
  have hr : DLe (S/16) P.rejNTT := ⟨by have := hp.rejNTT.fd; omega_using [this], hp.rejNTT.nd⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hp.rej4.fd; omega_using [this], hp.rej4.nd⟩
  have h2 : DLe (S/16) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := by
    have hd : Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
    exact ⟨by rw [hd]; omega_using [], by lit_decide⟩
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  split
  · unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
    dle_tac
  · unfold Impl.MlDsa.AArch64.Sign.expandA
    dle_tac

theorem expandA_depth {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params) :
    16*(Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p).aarch64Depth≤S := by
  have := (expandA_dle hp p).le
  omega_using [this]

theorem expandA_noDit {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params) :
    (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p).all (fun i => !i.touchesDit) = true :=
  (expandA_dle hp p).nd

 theorem rooted_expandA_ok {P : Prims} {S : Nat} (hp : PrimsOk P S) {p : Params}
    (h3 : Ok3 p) (hc : aChk p=true) {σ s : State} (hs : RootedSt p S σ s)
    (hf : s.gpr .x24=1) : WP isa (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) s
      fun t=>IA p S σ (p.k*p.ℓ) t ∧ StaticRoots S t :=
  hs.2.phase (expandA_depth hp p) hp.s64 (expandA_ok hp h3 hc hs.1 hf)

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

end

end

/-! ## From `CachedMatrixCallTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)

theorem two_ret {S : Nat} (hS : S<2^64) : RetPub (rejNTT2Contract abi S) Two.code :=
  RetPub.of_noDit (by lit_decide) (fun _ d h => pre_withDit d h) <| by
  intro x y tx ty x' y' ⟨hx,hy,hpub⟩ ex ey
  have px := pre_two (pre_stack (Nat.zero_le S) hS hx)
  have py := pre_two (pre_stack (Nat.zero_le S) hS hy)
  have pub : Pub 2 x y := by
    sig_pub [rejNTT2Contract,rejNTT2Sig,abi,argRegs] at hpub
    obtain ⟨hsp,hb,h0,h1,h2⟩ := hpub
    exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
  refine ⟨two_ct _ _ _ _ _ _ px py pub ex ey,?_⟩
  obtain ⟨_,u,eu,hu⟩ := two_ok px
  obtain ⟨_,v,ev,hv⟩ := two_ok py
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  have he : (∀k<2,(prefixRow x k 1008).length=256) ↔ ∀k<2,(prefixRow y k 1008).length=256 := by
    constructor
    · intro h k hk; rw [←pub.prefix hk]; exact h k hk
    · intro h k hk; rw [pub.prefix hk]; exact h k hk
  rw [hu.status,hv.status]
  by_cases h : ∀k<2,(prefixRow x k 1008).length=256
  · simp only [ite_eq_left h,ite_eq_left (he.mp h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hy=>h (he.mpr hy))]

theorem rej2At_trRet {S : Nat} (hS : S<2^64)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej2Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 68 = bytesAt y.mem (pa y seed) 68 ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet (callee hS) (two_ret hS) (rej2_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej2_pre Lx hc h1, ?_, ?_, (rej2_cov Lx hc).1, (rej2_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej2_pre Ly hc h2
  · sig_pub [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

/-! ## From `CachedMatrixBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem seeds2 {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 2 s) :
    bytesAt s.mem (pa s (sc oRS4)) 68=seedE p σ (e+0)++seedE p σ (e+1) := by
  have h0 := aseeds2_eq h (show 0<2 by decide)
  have h1 := aseeds2_eq h (show 1<2 by decide)
  unfold seed4 at h0 h1
  rw [show 68=34+34 from rfl,VG.Proof.MlKem.bytesAt_add]
  simp only [Nat.mul_zero,Nat.mul_one,VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]

theorem twoBatch_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (hc : twoChk p e = true) :
    RelCT isa (RR p D (AS p D · e 2) fun x y => x.gpr .x24 = y.gpr .x24)
      (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p)))) (.block and24))
      (RA p D (e+2)) := by
  have hc' := hc
  simp only [twoChk,Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨cr,_⟩,_⟩,_⟩,_⟩ := hc'
  refine stepRR (F := fun _ _ => True) (fun _ _ _ h => WP.mono (twoBatch_ok hP hc h) fun _ ht => ⟨ht,trivial⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  have calltr : RelCT isa (RR p D (AS p D · e 2) fun x y => x.gpr .x24 = y.gpr .x24)
      (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p))))
      (fun x y => LRel D (sgR p) (sgW p) x y ∧ x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) := by
    refine postDepQ (fun x y t1 t2 x' y' h e1 e2 =>
      rej2At_trRet hP.s64 (h.lrel fun _ _ h => h.ia.st).ok cr ?_ x y t1 t2 x' y' h e1 e2)
      (F := fun s t => PPostB D s t [(pS (aBase p+e),2048),(sc (oR4 p),8192)] ∧ t.gpr .x24 = s.gpr .x24)
      ?_ ?_
    · intro x y h
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨L.lx,L.ly,?_,L.same⟩
      obtain ⟨⟨σ1,σ2,_,_,pub,h1,h2⟩,_⟩ := h
      rw [seeds2 h1,seeds2 h2]
      simp only [seedE,pub_rho pub]
    · intro x y h
      obtain ⟨⟨σ1,σ2,_,_,_,h1,h2⟩,_⟩ := h
      exact ⟨WP.mono (rej2Call_ok hP.s64 h1.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩),
        WP.mono (rej2Call_ok hP.s64 h2.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩)⟩
    · intro x y x' y' h hx hy hr
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨⟨L.lx.post hx.1,L.ly.post hy.1,fun r hr => ?_,?_,L.ok⟩,by rw [hx.2,hy.2,h.2],hr⟩
      · rw [hx.1.bs r (bases_kept r hr),hy.1.bs r (bases_kept r hr)]; exact L.regs r hr
      · rw [hx.1.sp,hy.1.sp]; exact L.sp
  refine RelCT.seq calltr (RelCT.postDep (lrel_tr (fun _ _ h => h.1) (by taint_decide))
    (F := fun s t => t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
    (fun x y _ => ⟨WP.mono (and24_ok x) (fun _ h => h.2),WP.mono (and24_ok y) (fun _ h => h.2)⟩)
    fun x y x' y' h hx hy => by rw [hx,hy,h.2.1,h.2.2])


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

/-! ## From `CachedMatrixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.Sign

theorem tail_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) :
    RelCT isa (RA mlDsa65 D 28) (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65)
      (RA mlDsa65 D 30) := by
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
  rw [show 4*(mlDsa65.k*mlDsa65.ℓ/4)=28 by decide]
  refine RelCT.seq (RelCT.mono (seqR_tr
    (Q:=fun j=>RR mlDsa65 D (AS mlDsa65 D · 28 j) fun x y=>x.gpr .x24=y.gpr .x24) 2 0
    (fun j _ hj=>slot4_tr (by omega_using [hj])
      (slotChk_ok mlDsa65 (by simp) 28 (by decide) j (by omega_using [hj])))) ?_ (fun _ _ h=>by simpa using h))
    (twoBatch_tr hP (show twoChk mlDsa65 28=true by decide))
  exact fun x y h=>h.mono (fun _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩) (fun h=>h)

theorem expandA65_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) (hc : aChk mlDsa65 = true) :
    RelCT isa (RR mlDsa65 D (fun σ s => St mlDsa65 D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P mlDsa65) (RA mlDsa65 D (mlDsa65.k * mlDsa65.ℓ)) := by
  have hp : mlDsa65 ∈ [mlDsa44,mlDsa65,mlDsa87] := by simp
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  rw [ite_eq_left (by decide)]
  refine RelCT.seq (R := RA mlDsa65 D 0) (stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => IA mlDsa65 D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · have hB : RelCT isa (RA mlDsa65 D 0) (seqR (sample4 P mlDsa65) 0 7) (RA mlDsa65 D 28) := by
      simpa only [Nat.zero_add,Nat.mul_zero] using
        (seqR_tr (Q:=fun g=>RA mlDsa65 D (4*g)) 7 0 (fun g _ hg=>
          sample4_tr hP (batchChk_ok mlDsa65 hp g (by change g<7; omega_using [hg]))
            (fun j hj=>slotChk_ok mlDsa65 hp (4*g) (by change 4*g<30; omega_using [hg]) j hj)))
    exact RelCT.seq hB (tail_tr hP)

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) (hc : aChk p=true) :
    RelCT isa (RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) fun _ _=>True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (RA p D (p.k*p.ℓ)) := by
  rcases hp with rfl|rfl|rfl
  · exact Sign.expandA_tr hP (.inl rfl) hc
  · exact expandA65_tr hP hc
  · exact Sign.expandA_tr hP (.inr (.inr rfl)) hc

theorem positiveExpand_tr {P : Prims} {p : Params} {D : Nat} (hP : PrimsOk P D) (hp : Ok3 p) :
    RelCT isa (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (PositiveRA p D) := by
  have ha := aChk_ok hp
  intro x y tx ty x' y' h ex ey
  have old : RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) (fun _ _=>True) x y := h.mono (fun _ _ h=>⟨h.1.1,h.2⟩) (fun _=>trivial)
  obtain ⟨tr,out⟩ := expandA_tr hP hp ha _ _ _ _ _ _ old ex ey
  obtain ⟨⟨σ,τ,_,_,_,hx,hy⟩,re⟩ := h
  obtain ⟨_,u,eu,_,ru⟩ := rooted_expandA_ok hP hp ha hx.1 hx.2
  obtain ⟨_,v,ev,_,rv⟩ := rooted_expandA_ok hP hp ha hy.1 hy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨tr,out,ru,rv,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using re⟩


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

end

end

/-! ### `MlDsa.AArch64.Sign.PairedRootsPrologue`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.PairedRootsEntry`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

/-- The ordinary signer contract gains only its three immutable artifact tables. -/
def pairedSignRootConsts := VG.Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts ++
  VG.Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts ++ VG.Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts

theorem pairedSignRootConsts_eq : pairedSignRootConsts=[
    ("VG_MLDSA_NTT_EXPANDED",VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords),
    ("VG_MLDSA_INV_FOLDED",VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords),
    ("VG_MLDSA_INV_PAIR",VG.Impl.MlDsa.AArch64.Optimized.Paired.expandedWords)] := rfl

theorem pairedRoots_entry {p : Params} {S : Nat} {s : State}
    (hS : 0<S) (h : (signContractT p (abi.withConsts pairedSignRootConsts) S).pre s) :
    (signK p S).pre s ∧ StaticRoots S s ∧ PairedRoots S s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  sig_pre [signContractT,signSig,abi,argRegs,Abi.withConsts,pairedSignRootConsts_eq,
    nttConsts_eq,
    Inverse.inverseConsts_eq,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hsp,hd,hf,hi,hpair,hff,hfw,hfs,hif,hiw,his,hpf,hpw,hps,hfa,hia,hpa,ht,hw,d1,d2,d3,d4,d5,d6,d7,
    k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩ := h
  have hrd : s.rd=[⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩] := by
    rw [← List.take_append_drop (s.rd.length-3) s.rd,ht,hd]
  refine ⟨?_,⟨⟨hf,hff,?_,hfw,hfs,hfa⟩,⟨hi,hif,?_,hiw,his,hia⟩⟩,⟨?_,hpf,?_,hpw,hps,hpa⟩⟩
  · have hsub : [⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩]⊆s.rd := by
      rw [hrd]
      exact List.subset_append_left _ _
    dsimp only [signK,scrLen]
    rw [Nat.mul_comm 8 (scratchWords p)]
    exact ⟨hsub,hw,d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5,hsp⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]
    simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]
    simp

  · exact hpair
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩,?_,Region.contains_self _ _⟩
    rw [hrd]
    simp

end VG.Proof.MlDsa.AArch64.Sign

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem paired_prologue {p : Params} {S : Nat} {σ : State} (hp : Ok3 p) (hS : S<2^64)
    (h : (signK p S).pre σ) (hr : StaticRoots S σ) (rp : PairedRoots S σ) :
    WP isa (.block pro) σ fun s=>(RootedSt p S σ s ∧ s.gpr .x24=1) ∧ PairedRoots S s :=
  WP.pairedRoots (rooted_prologue hp h hr) rp (Nat.zero_le _) hS

end VG.Proof.MlDsa.AArch64.Sign

end

end

/-! ### `MlDsa.AArch64.Sign.CachedLoopConcrete`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedChecksBase`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)

structure Roots (p : Params) (S : Nat) (f : Poly) (s : State) : Prop where
  roots : PairedRoots S s
  cache : PolyIs s.mem (pa s t4P) f

theorem Roots.step_layout {p : Params} {S : Nat} {f : Poly} {s t : State}
    {ws : List (Ptr × Nat)} (h : Roots p S f s) (L : Lay S (sgR p) (sgW p) s)
    (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true)
    (hc : keepB (sgR p) (sgW p) ws t4P 1024=true) : Roots p S f t :=
  ⟨h.roots.step_layout L hp hy hw,L.keepPoly hp hc h.cache⟩

theorem keep_nil {p : Params} (hp : Ok3 p) :
    keepB (sgR p) (sgW p) [] t4P 1024=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem keep_zpair {p : Params} {r : Nat} (hp : Ok3 p) (hr : r+1<p.ℓ) :
    keepB (sgR p) (sgW p) (pairedZWrites p r) t4P 1024=true := by
  have hh : ∀r<p.ℓ, keepB (sgR p) (sgW p) (pairedZWrites p r) t4P 1024=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  exact hh r (by omega_using [hr])

theorem keep_lowpair {p : Params} {i : Nat} (hp : Ok3 p) (hi : i+1<p.k) :
    keepB (sgR p) (sgW p) (pairedLowWrites p i) t4P 1024=true := by
  have hh : ∀i<p.k, keepB (sgR p) (sgW p) (pairedLowWrites p i) t4P 1024=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  exact hh i (by omega_using [hi])

theorem keep_hintpair {p : Params} {i : Nat} (hp : Ok3 p) (hi : i+1<p.k) :
    keepB (sgR p) (sgW p) (pairedHintWrites i) t4P 1024=true := by
  have hh : ∀i<p.k, keepB (sgR p) (sgW p) (pairedHintWrites i) t4P 1024=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  exact hh i (by omega_using [hi])

theorem keep_product {p : Params} (hp : Ok3 p) :
    keepB (sgR p) (sgW p) [(t1P,1024),(sc oPS,1024)] t4P 1024=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem keep_z {p : Params} {r : Nat} (hp : Ok3 p) (hr : r<p.ℓ) :
    keepB (sgR p) (sgW p) [(yP p r,1024)] t4P 1024=true := by
  revert r; rcases hp with rfl|rfl|rfl <;> decide

theorem keep_low {p : Params} {i : Nat} (hp : Ok3 p) (hi : i<p.k) :
    keepB (sgR p) (sgW p) [(wP p i,1024),(hP i,1024)] t4P 1024=true := by
  revert i; rcases hp with rfl|rfl|rfl <;> decide

theorem keep_ones {p : Params} (hp : Ok3 p) :
    keepB (sgR p) (sgW p) [(sc oONES,8)] t4P 1024=true := by
  rcases hp with rfl|rfl|rfl <;> decide

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

end

/-! ### `MlDsa.AArch64.Sign.CachedLoopCorrect`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedChecksBoundary`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.AArch64.Optimized
variable {f : Poly}

theorem both {c : Prog isa} {s : State} {Q R : State → Prop}
    (h : WP isa c s Q) (g : WP isa c s R) : WP isa c s fun u=>Q u ∧ R u := by
  obtain ⟨t,u,e,q⟩ := h
  obtain ⟨t',u',e',r⟩ := g
  obtain ⟨_,rfl⟩ := Exec.det e e'
  exact ⟨t,u,e,q,r⟩

theorem challenge_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : Roots p S f s) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (positiveNttArgs cP)) s fun u=>PositiveChallenge p S σ t u ∧ Roots p S f u := by
  refine both (positiveChallenge_ok hp h h1) ?_
  have hc := positiveChallengeChk_ok hp
  simp only [positiveChallengeChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hr,hw⟩,_⟩,_⟩ := hc
  obtain ⟨hf,_⟩ := h.ok h1
  have ht : ForwardRoots s (pa s cP) :=
    ⟨h.c.masks.l.k.d.roots.nttTableAt (h.c.masks.l.st.lay.inW hw),h.c.masks.l.k.d.roots.forward.readable⟩
  refine WP.mono_syms (positiveNttAt_layout h.c.masks.l.st.lay hr hw ht hf.1)
    fun u ⟨hpu,_,_⟩ hy=>?_
  exact roots.step_layout h.c.masks.l.st.lay hpu hy (by simpa using hw)
    (by rcases hp with rfl|rfl|rfl <;> decide)

theorem init_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveChallenge p S σ t s) :
    WP isa (.block kInit) s fun u=>PositiveIZ p S σ t 0 u ∧ Roots p S f u := by
  refine both (positiveChecksInit_ok hp hc h) ?_
  refine ksChk_spec hc fun _ _ _ c4 c5 _ _ _ _ _ _ _ _ c13 _ _ _ _ _ _ _ _ _ _ _ _ _ _=>?_
  have b : PositiveKB p S σ t s := ⟨h.c.masks.l,h.ct,h.challenge,h.sampled⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms (positiveFlagInit s) fun u ⟨hu,_⟩ hsu=>?_
  have hpu : PPostB S s u [] := postB24 hu []
  have bu := b.step hpu hsu c13 (by simp)
  have ru := roots.step_layout b.l.st.lay hpu hsu (by simp) (keep_nil hp)
  refine WP.mono_syms (setQ_ok bu.l.st.lay (by decide) (by decide) c4 (by decide))
    fun v ⟨hpv,_,_⟩ huv=>?_
  exact ru.step_layout bu.l.st.lay hpv huv
    (by rcases hp with rfl|rfl|rfl <;> decide) (keep_ones hp)

theorem ones_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveIH p S σ t p.k s) :
    WP isa (.block (onesOk p)) s fun u=>PositiveKO p S σ t u ∧ Roots p S f u := by
  refine both (positiveOnesOk_ok hc h) ?_
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ _ _ _ _ _ _ _ _ _ hω _ _ _ _ _=>?_
  refine WP.mono_syms (onesOk_run p hω s (h.1.b.l.st.lay.inR c8))
    fun u ⟨⟨_,hm⟩,k⟩ hy=>?_
  have hpu : PPostB S s u [] := postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _)
  exact roots.step_layout h.1.b.l.st.lay hpu hy (by simp) (keep_nil hp)

theorem branch_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveKO p S σ t s) :
    WP isa (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ Roots p S f u := by
  refine both (positiveKBranch_ok hp hc h) ?_
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 _ _ _ _ _ _ _ _ _ _ hl _ _ _ c23=>?_
  have L := h.b.l.st.lay
  refine ifOkElse_ok (fun _=>?_) fun _=>?_
  · refine WP.mono_syms (setQ_ok L (by decide) (by decide) c9 (by decide)) fun u ⟨hpu,_,_⟩ hy=>?_
    exact roots.step_layout L hpu hy
      (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)
  · refine WP.mono_syms (kapAdd_ok p hl s (L.inW c10) (L.inR c23)) fun u ⟨hm,k⟩ hy=>?_
    have hf : Frame [⟨pa s (sc oKAP),8⟩] s.mem u.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hpu : PPostB S s u [(sc oKAP,8)] := postB_of_keep k (by decide) hf
    exact roots.step_layout L hpu hy
      (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

/-- Early rejection preserves the look-ahead mask just like the final
rejection branch. -/
theorem reject_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveIL p S σ t s)
    (sampled : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome)
    (fail : ¬ PassV p σ (p.ℓ*t)) (flag : s.gpr .x24=0) :
    WP isa (.block (kapAdd p)) s fun u=>PositiveEF p S σ t u ∧ Roots p S f u := by
  refine both (positiveReject_ok hp hc h sampled fail flag) ?_
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ _ c10 _ _ _ _ _ _ _ _ _ _ hl _ _ _ c23=>?_
  have L := h.st.lay
  refine WP.mono_syms (kapAdd_ok p hl s (L.inW c10) (L.inR c23)) fun u ⟨hm,k⟩ hy=>?_
  have hf : Frame [⟨pa s (sc oKAP),8⟩] s.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hpu : PPostB S s u [(sc oKAP,8)] := postB_of_keep k (by decide) hf
  exact roots.step_layout L hpu hy
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

end

/-! ### `MlDsa.AArch64.Sign.CachedChecksZVector`, which only this module used -/

section

/-! ## From `CachedChecksZ.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedZ_pair_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r+1<p.ℓ) (roots : Roots p S f s) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zPair p r) s fun u =>
      PositiveIZ p S σ t (r+2) u ∧ Roots p S f u := by
  have checks := pairedZChk_ok hp r (by omega_using [hr]) hr
  simp only [pairedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hy⟩,hw⟩,hwy⟩,hww⟩,hcy⟩,hcw⟩,hsy⟩,hsw⟩,hyw⟩,hB⟩,hz⟩,hys⟩,he⟩,hye⟩,hws⟩ := checks
  obtain ⟨h,hflag⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (yP p r)) j) (Yv p σ (p.ℓ*t) (r+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.y j (by omega_using [hr, hj])
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s1P p r)) j) (S1v p σ (r+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s1 (r+j) (by omega_using [hr, hj])
  have hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s1P p r)) :=
    ⟨h.b.c.bound,fun j hj => (hsecret j hj).bound⟩
  have hsum : ∀j<2,add (polyAt s.mem (pairPolyPtr (pa s (yP p r)) j))
      (pairedProduct s.mem (pa s cP) (pa s (s1P p r)) j)=Zv p σ (p.ℓ*t) (r+j) := by
    intro j hj
    rw [(hdata j hj).2]
    simp only [pairedProduct,h.b.c.value,(hsecret j hj).value]
    rfl
  have ready := pairedZReady_layout h.b.l.st.lay roots.roots hc hs hy hw hwy hww hcy hcw hsy hsw hyw
    hprod (fun j hj => (hdata j hj).1) hB.1 hB.2
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zPair
  refine WP.seq (WP.mono_syms (pairedZAt_layout (gamma:=p.γ₁) h.b.l.st.lay hc hs hy hw ready)
    fun a ⟨hpa,h24,hfields,hret⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hws (keep_zpair hp hr)
  have hznew : ∀j<2,SignedPl a (yBase p+(r+j)) (Zv p σ (p.ℓ*t) (r+j)) (-(q:Int)+1) ((q:Int)-1) := by
    intro j hj
    have hv := hfields j hj
    rw [hsum j hj,paired_pS_addr] at hv
    change SignedPolyIs a.mem (pa a (pS (yBase p+(r+j)))) _ _ _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc] using hv
  simp only [zfam,Bool.and_eq_true] at hz
  have zold := h.z.keep h.b.l.st.lay hpa hz.1.1.2
  have zall : SignedFam a (yBase p) (r+2) (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1) := by
    have h0 := hznew 0 (by decide)
    have h1 := hznew 1 (by decide)
    simpa only [Nat.add_zero,Nat.add_assoc] using (zold.snoc (by simpa only [Nat.add_zero] using h0)).snoc h1
  have yshift : Fam s (yBase p+(r+2)) (p.ℓ-(r+2)) (fun j => Yv p σ (p.ℓ*t) (r+2+j)) := by
    simpa only [show r+1+1=r+2 by omega_using []] using ((h.y.shift (by omega_using [hr])).shift (by omega_using [hr]))
  have ytail := yshift.keep h.b.l.st.lay hpa hys
  have ha : PositiveIZb p S σ t (r+2) a :=
    ⟨h.b.step hpa hsa hz.1.1.1 hws,zall,ytail,
      h.w.keep h.b.l.st.lay hpa hz.1.2,(h.b.l.st.lay.keepW hpa hz.2).trans h.ones⟩
  have ret : (a.gpr .x0).setWidth 32=if normRq ((List.range 2).map fun j => Zv p σ (p.ℓ*t) (r+j))<p.γ₁-p.β then 1 else 0 := by
    have heq : ((List.range 2).map fun j =>
        add (polyAt s.mem (pairPolyPtr (pa s (yP p r)) j)) (pairedProduct s.mem (pa s cP) (pa s (s1P p r)) j))
        = (List.range 2).map (fun j => Zv p σ (p.ℓ*t) (r+j)) := by
      apply List.map_congr_left
      intro j hj
      exact hsum j (List.mem_range.mp hj)
    rw [heq] at hret
    exact hret
  refine WP.mono_syms (and24_ok a) fun u ⟨hku,hfu⟩ hsu => ?_
  have hpu : PPostB S a u [] := postB24 hku []
  refine ⟨⟨ha.step hpu hsu he hye (by simp),?_⟩,ra.step_layout ha.b.l.st.lay hpu hsu (by simp) (keep_nil hp)⟩
  rw [hfu,bit_and (h24.trans hflag) ret]
  apply bit_congr
  rw [pairedZ_norm (by omega_using [hB] : 0<p.γ₁-p.β)]
  exact pairedZ_prefix

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksZVector.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedZ_rooted_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r<p.ℓ) (roots : Roots p S f s) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) s (fun u => PositiveIZ p S σ t (r+1) u ∧ Roots p S f u) := by
  have hc := optimizedZChk_ok hp r hr
  simp only [optimizedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyr,hcr⟩,hyw⟩,hsep⟩,hb⟩,zp⟩,yp⟩,zz⟩,yz⟩,ze⟩,ye⟩,hwp⟩ := hc
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_z hp r hr) h.b.c (h.b.l.k.d.s1 r hr)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hwp (keep_product hp)
  have ha := h.step hpa hsa zp yp hwp
  have hy : PolyIs a.mem (pa a (yP p r)) (Yv p σ (p.ℓ*t) r) := by
    have hv := ha.y 0 (by omega_using [hr])
    simpa only [Nat.add_zero] using hv
  have hraw : RawPolyIs a.mem (pa a t1P)
      (nttInv (multiplyNTT (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t))) (S1v p σ r))) := by
    rw [hpa.pa (by decide)]; exact hprod
  have ready := addNormReady_layout ha.b.l.st.lay hyr hcr hyw hsep hy.1 hraw.1 hb.1 hb.2
  refine WP.seq (WP.mono_syms (addNormAt_field_layout ha.b.l.st.lay hyr hcr ready hy hraw)
    fun b ⟨hpb,h24b,hz,hret⟩ hsb => ?_)
  have rb := ra.step_layout ha.b.l.st.lay hpb hsb (by
    intro w hw; simp only [List.mem_singleton] at hw; subst w; exact hyw) (keep_z hp hr)
  have hz' : SignedPl b (yBase p+r) (Zv p σ (p.ℓ*t) r) (-(q:Int)+1) ((q:Int)-1) := by
    change SignedPolyIs b.mem (pa b (yP p r)) _ _ _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hyr)]
    exact hz
  simp only [zfam,Bool.and_eq_true] at zz
  have hbstate : PositiveIZb p S σ t (r+1) b :=
    ⟨ha.b.step hpb hsb zz.1.1.1 (by simpa using hyw),
      (ha.z.keep ha.b.l.st.lay hpb zz.1.1.2).snoc hz',
      (ha.y.shift hr).keep ha.b.l.st.lay hpb yz,
      ha.w.keep ha.b.l.st.lay hpb zz.1.2,(ha.b.l.st.lay.keepW hpb zz.2).trans ha.ones⟩
  refine WP.mono_syms (and24_ok b) fun c ⟨hkc,hflagc⟩ hsc => ?_
  have hpc : PPostB S b c [] := postB24 hkc []
  refine ⟨⟨hbstate.step hpc hsc ze ye (by simp),?_⟩,
    rb.step_layout hbstate.b.l.st.lay hpc hsc (by simp) (keep_nil hp)⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr forall_lt_succ

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

end

end

/-! ## From `CachedLoopFrame.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
variable {f : Poly}

/-- Sampling writes only the challenge and SHAKE work buffers, retaining the
next iteration's cached odd mask even when sampling exhausts its bound. -/
theorem ball_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hc : bChk p=true) {σ s : State} {t : Nat}
    (roots : Roots p S f s) (h : PositiveIC p S σ t s) :
    WP isa (ballAt P (cLen p) p.τ cP) s fun u=>PositiveIB p S σ t u ∧ Roots p S f u := by
  refine both (positiveBall_ok hP hp hc h) ?_
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc
  refine WP.mono_syms (ballCall_ok hP h.c.masks.l.st.lay hbp c1)
    fun u ⟨hpu,_,_,_,_⟩ hy=>?_
  exact roots.step_layout h.c.masks.l.st.lay hpu hy (challengeWrites_ok hp)
    (by rcases hp with rfl|rfl|rfl <;> decide)

/-- The bounded-sampling failure path changes only the flag and loop counter. -/
theorem ballFailure_ok {S : Nat} {p : Params} (hp : Ok3 p) (hc : lChk p=true)
    {σ s : State} {t : Nat} (roots : Roots p S f s)
    (h : PositiveIB p S σ t s) (h0 : (s.gpr .x0).setWidth 32=0) :
    WP isa (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1)) s fun u=>
      PositiveEB p S σ t u ∧ Roots p S f u := by
  refine both (positiveBallFailure_ok hp hc h h0) ?_
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,k0⟩,_⟩,_⟩,_⟩ := hc
  have hz : WP isa (.block [.movz .x .x24 0 0]) s fun u=>
      VG.Proof.MlKem.AArch64.Only [.x24] s u ∧ u.gpr .x24=0 := by
    refine VG.Proof.MlKem.AArch64.wp_movz fun u hu hv=>VG.Proof.MlKem.AArch64.wp_nil ⟨hu,hv⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms hz fun u ⟨hu,_⟩ hy=>?_
  have hpu : PPostB S s u [] := postB24 hu []
  have ku := h.c.masks.l.k.step hpu hy k0 (by simp)
  have ru := roots.step_layout h.c.masks.l.st.lay hpu hy (by simp) (keep_nil hp)
  refine WP.mono_syms (setQ_ok ku.d.im.st.lay (by decide) (by decide) w1 (by decide))
    fun v ⟨hpv,_,_⟩ hyv=>?_
  exact ru.step_layout ku.d.im.st.lay hpv hyv
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

/-- Counter decrement retains the cached polynomial on every loop outcome:
accepted, rejected, or bounded-sampling failure. -/
theorem decEnd_ok {S : Nat} {p : Params} (hp : Ok3 p) (hparam : ParamsOk p)
    (hc : lChk p=true) {σ s : State} {t : Nat} (roots : Roots p S f s)
    (h : PositiveEP p S σ t s ∨ PositiveEF p S σ t s ∨ PositiveEB p S σ t s) :
    WP isa (.block cntDec) s fun u=>PositiveLP p S σ t u ∧ Roots p S f u := by
  refine both (positiveDecEnd hp hparam hc h) ?_
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,r1⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := hc
  have hk : PositiveIK p S σ s := by rcases h with h|h|h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono_syms (cntDec_ok s (L.inW w1) (L.inR r1)) fun u ⟨⟨hm,_⟩,k⟩ hy=>?_
  have hf : Frame [⟨pa s (sc oCNT),8⟩] s.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hpu : PPostB S s u [(sc oCNT,8)] := postB_of_keep k (by decide) hf
  exact roots.step_layout L hpu hy
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksLow.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedR0_rooted_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i<p.k) (roots : Roots p S f s) (h : PositiveIR p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0R p i) s (fun u=>PositiveIR p S σ t (i+1) u ∧ Roots p S f u) := by
  have hc := optimizedR0Chk_ok hp i hi
  simp only [optimizedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cl,hgb⟩,rp⟩,wp⟩,rr⟩,wr⟩,re⟩,we⟩,hwp⟩ := hc
  simp only [subLowNormChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwr,hcr⟩,hlr⟩,hww⟩,hwl⟩,hwc⟩,hwo⟩,hco⟩,_⟩ := cl
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_r0 hp i hi) h.b.c (h.b.l.k.d.s2 i hi)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hwp (keep_product hp)
  have ha := h.step hpa hsa rp wp hwp
  have hw : PolyIs a.mem (pa a (wP p i)) (Wv p σ (p.ℓ*t) i) := by
    have hv := ha.w 0 (by omega_using [hi])
    simpa only [Nat.add_zero] using hv
  have hraw : RawPolyIs a.mem (pa a t1P) (nttInv (multiplyNTT
      (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t))) (S2v p σ i))) := by
    rw [hpa.pa (by decide)]; exact hprod
  have ready := subLowNormReady_layout ha.b.l.st.lay hwr hcr hlr hww hwl hwc hwo hco
    hw.1 hraw.1 hgb.1 hgb.2.1 hgb.2.2
  refine WP.seq (WP.mono_syms (subLowNormAt_field_layout ha.b.l.st.lay hwr hcr hlr ready hw hraw)
    fun b ⟨hpb,h24b,hhigh,hlow,hret⟩ hsb => ?_)
  have rb := ra.step_layout ha.b.l.st.lay hpb hsb
    (by simpa using And.intro hww hwl) (keep_low hp hi)
  have high' : NatPl b (wBase p+i) (WHighv p σ (p.ℓ*t) i) := by
    change NatPolyIs b.mem (pa b (wP p i)) _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hwr)]
    exact hhigh
  have low' : SignedPl b (5+i) (R0v p σ (p.ℓ*t) i) (-(p.γ₂:Int)) p.γ₂ := by
    change SignedPolyIs b.mem (pa b (hP i)) _ _ _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hlr)]
    exact hlow
  simp only [positiveRfam,Bool.and_eq_true] at rr
  have hbstate : PositiveIRb p S σ t (i+1) b :=
    ⟨ha.b.step hpb hsb rr.1.1.1.1 (by simpa using And.intro hww hwl),
      ha.z.keep ha.b.l.st.lay hpb rr.1.1.1.2,
      (ha.high.keep ha.b.l.st.lay hpb rr.1.1.2).snoc high',
      (ha.low.keep ha.b.l.st.lay hpb rr.1.2).snoc low',
      (ha.w.shift hi).keep ha.b.l.st.lay hpb wr,(ha.b.l.st.lay.keepW hpb rr.2).trans ha.ones⟩
  refine WP.mono_syms (and24_ok b) fun c ⟨hkc,hflagc⟩ hsc => ?_
  have hpc : PPostB S b c [] := postB24 hkc []
  refine ⟨⟨hbstate.step hpc hsc re we (by simp),?_⟩,
    rb.step_layout hbstate.b.l.st.lay hpc hsc (by simp) (keep_nil hp)⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr ⟨fun ⟨⟨a,b⟩,c⟩=>⟨a,forall_lt_succ.mp ⟨b,c⟩⟩,
    fun ⟨a,b⟩=>⟨⟨a,(forall_lt_succ.mpr b).1⟩,(forall_lt_succ.mpr b).2⟩⟩


theorem optimizedR0_pair_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : Roots p S f s) (h : PositiveIR p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p i) s fun u =>
      PositiveIR p S σ t (i+2) u ∧ Roots p S f u := by
  have checks := pairedR0Chk_ok hp i (by omega_arith) hi
  simp only [pairedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨cl,hgb⟩,rr⟩,wr⟩,re⟩,we⟩,hws⟩ := checks
  simp only [pairedLowChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,ho⟩,hl⟩,hw⟩,hwo⟩,hwl⟩,hww⟩,hco⟩,hcl⟩,hcw⟩,hso⟩,hsl⟩,hsw⟩,hol⟩,how⟩,hlw⟩,_⟩ := cl
  obtain ⟨h,hflag⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (wP p i)) j) (Wv p σ (p.ℓ*t) (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.w j (by omega_arith)
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s2P p i)) j) (S2v p σ (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s2 (i+j) (by omega_arith)
  have hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s2P p i)) :=
    ⟨h.b.c.bound,fun j hj => (hsecret j hj).bound⟩
  have hdiff : ∀j<2,pairedDifference s.mem (pa s cP) (pa s (s2P p i)) (pa s (wP p i)) j=
      W'v p σ (p.ℓ*t) (i+j) := by
    intro j hj
    simp only [pairedDifference,pairedProduct,(hdata j hj).2,h.b.c.value,(hsecret j hj).value]
    rfl
  have hsep : ∀r∈[⟨pa s (wP p i),2048⟩,⟨pa s (hP i),2048⟩,⟨pa s t1P,2176⟩],
      (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact roots.roots.apart_write (h.b.l.st.lay.inW hwo)
    · exact roots.roots.apart_write (h.b.l.st.lay.inW hwl)
    · exact roots.roots.apart_write (h.b.l.st.lay.inW hww)
  have ready := pairedLowReady_layout h.b.l.st.lay hc hs ho hl hw hwo hwl hww
    hco hcl hcw hso hsl hsw hol how hlw roots.roots.held roots.roots.fit hsep roots.roots.readable
    hprod (fun j hj => (hdata j hj).1) hgb.1 hgb.2.1 hgb.2.2 roots.roots.aligned
  unfold Impl.MlDsa.AArch64.Sign.Optimized.r0Pair
  refine WP.seq (WP.mono_syms (pairedLowAt_layout h.b.l.st.lay hc hs ho hl hw ready)
    fun a ⟨hpa,h24,hpost⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hws (keep_lowpair hp hi)
  obtain ⟨fields,ret⟩ := hpost.field (VG.Proof.MlDsa.AArch64.Round.isG_of_mem hgb.1) hdiff
  have hhigh : ∀j<2,NatPl a (wBase p+(i+j)) (WHighv p σ (p.ℓ*t) (i+j)) := by
    intro j hj
    have hv := (fields j hj).1
    rw [paired_pS_addr] at hv
    change NatPolyIs a.mem (pa a (pS (wBase p+(i+j)))) _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc] using hv
  have hlow : ∀j<2,SignedPl a (5+(i+j)) (R0v p σ (p.ℓ*t) (i+j)) (-(p.γ₂:Int)) p.γ₂ := by
    intro j hj
    have hv := (fields j hj).2
    rw [paired_pS_addr] at hv
    change SignedPolyIs a.mem (pa a (pS (5+(i+j)))) _ _ _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc,pairedLowPoly,R0v,VG.Proof.MlDsa.Sign.r0F] using hv
  simp only [positiveRfam,Bool.and_eq_true] at rr
  have highold := h.high.keep h.b.l.st.lay hpa rr.1.1.2
  have lowold := h.low.keep h.b.l.st.lay hpa rr.1.2
  have highall : NatFam a (wBase p) (i+2) (WHighv p σ (p.ℓ*t)) := by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      (highold.snoc (by simpa only [Nat.add_zero] using hhigh 0 (by decide))).snoc (hhigh 1 (by decide))
  have lowall : SignedFam a 5 (i+2) (R0v p σ (p.ℓ*t)) (-(p.γ₂:Int)) p.γ₂ := by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      (lowold.snoc (by simpa only [Nat.add_zero] using hlow 0 (by decide))).snoc (hlow 1 (by decide))
  have wshift : Fam s (wBase p+(i+2)) (p.k-(i+2)) (fun j=>Wv p σ (p.ℓ*t) (i+2+j)) := by
    simpa only [show i+1+1=i+2 by omega_arith] using ((h.w.shift (by omega_arith)).shift (by omega_arith))
  have ha : PositiveIRb p S σ t (i+2) a :=
    ⟨h.b.step hpa hsa rr.1.1.1.1 hws,h.z.keep h.b.l.st.lay hpa rr.1.1.1.2,
      highall,lowall,wshift.keep h.b.l.st.lay hpa wr,(h.b.l.st.lay.keepW hpa rr.2).trans h.ones⟩
  refine WP.mono_syms (and24_ok a) fun u ⟨hku,hfu⟩ hsu => ?_
  have hpu : PPostB S a u [] := postB24 hku []
  refine ⟨⟨ha.step hpu hsu re we (by simp),?_⟩,ra.step_layout ha.b.l.st.lay hpu hsu (by simp) (keep_nil hp)⟩
  rw [hfu,bit_and (h24.trans hflag) ret]
  apply bit_congr
  change ((ZOk p σ (p.ℓ*t) ∧ ∀j<i,normRq [R0v p σ (p.ℓ*t) j]<p.γ₂-p.β) ∧
    normRq ((List.range 2).map fun j=>R0v p σ (p.ℓ*t) (i+j))<p.γ₂-p.β) ↔ _
  rw [pairedZ_norm (by omega : 0<p.γ₂-p.β),and_assoc,pairedZ_prefix]

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksHints.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedHint_pair_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : Roots p S f s) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p i) s fun u =>
      PositiveIH p S σ t (i+2) u ∧ Roots p S f u := by
  have hc := pairedHintChk_ok hp i (by omega_arith) hi
  simp only [pairedHintChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨kr,zr⟩,hr⟩,lr⟩,fr⟩,orr⟩,wr⟩,kf⟩,zf⟩,hf⟩,lf⟩,ff⟩,ir⟩,iw⟩,hg,hgpos,hk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPair
  refine WP.seq (WP.mono_syms (pairedHintRow_ok hp hi roots.roots h) fun a ⟨hpa,h24,hint,hret⟩ hsa => ?_)
  obtain ⟨h,hflag⟩ := h
  have ra := roots.step_layout h.b.l.st.lay hpa hsa wr (keep_hintpair hp hi)
  have ba := h.b.step hpa hsa kr wr
  have za := h.z.keep h.b.l.st.lay hpa zr
  have higha := h.high.keep h.b.l.st.lay hpa hr
  have lowshift : SignedFam s (5+(i+2)) (p.k-(i+2))
      (fun j=>R0v p σ (p.ℓ*t) (i+2+j)) (-(p.γ₂:Int)) p.γ₂ := by
    intro j hj
    show SignedPl s (5+(i+2)+j) (R0v p σ (p.ℓ*t) (i+2+j)) _ _
    rw [show 5+(i+2)+j=5+i+(j+2) by omega_arith,show i+2+j=i+(j+2) by omega_arith]
    exact h.low (j+2) (by omega_arith)
  have lowa := lowshift.keep h.b.l.st.lay hpa lr
  have hints : ∀j<2,HintIs a.mem (pa a (hP (i+j))) 1 [Hv p σ (p.ℓ*t) (i+j)] := by
    intro j hj
    have hv := hintIs_pair hint hj
    rw [paired_pS_addr] at hv
    rw [hpa.pa (pS_bases _)]
    simpa only [Nat.add_assoc] using hv
  have hintsa : HFam a 5 (i+2) (Hv p σ (p.ℓ*t)) := by
    have old := HFam.keep h.b.l.st.lay hpa fr h.h
    have h0 := hints 0 (by decide)
    have h1 := hints 1 (by decide)
    simpa only [Nat.add_zero,Nat.add_assoc] using (old.snoc (by simpa only [Nat.add_zero] using h0)).snoc h1
  have onesa := (h.b.l.st.lay.keepW hpa orr).trans h.ones
  have hbound : onesSum (Hv p σ (p.ℓ*t)) i+hintOnes ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j))<2^32 := by
    rw [onesSum_pair]
    have := onesSum_le (Hv p σ (p.ℓ*t)) (i+2)
    omega_arith
  refine WP.mono_syms (hintFinish_semantic (S:=S) a _ _ _ _ (ba.l.st.lay.inR ir)
    (ba.l.st.lay.inW iw) hbound onesa hret (h24.trans hflag)) fun b ⟨hpb,hmem,hflagb⟩ hsb => ?_
  have rb := ra.step_layout ba.l.st.lay hpb hsb (by simpa using iw) (keep_ones hp)
  refine ⟨⟨⟨ba.step hpb hsb kf (by simpa using iw),za.keep ba.l.st.lay hpb zf,
    higha.keep ba.l.st.lay hpb hf,lowa.keep ba.l.st.lay hpb lf,
    HFam.keep ba.l.st.lay hpb ff hintsa,?_⟩,?_⟩,rb⟩
  · rw [hpb.pa (sc_bases _),hmem,Mem.readW_writeW_self64,onesSum_pair]
  · rw [hflagb]
    apply bit_congr
    rw [pairedZ_norm hgpos]
    constructor
    · rintro ⟨⟨a,b⟩,c⟩; exact ⟨a,pairedZ_prefix.mp ⟨b,c⟩⟩
    · rintro ⟨a,b⟩; exact ⟨⟨a,(pairedZ_prefix.mpr b).1⟩,(pairedZ_prefix.mpr b).2⟩

theorem optimizedHint_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : Roots p S f s) (h : PositiveIH p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector p) s fun u =>
      PositiveIH p S σ t p.k u ∧ Roots p S f u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector
  have he : 2*(p.k/2)=p.k := by rcases hp with rfl|rfl|rfl <;> decide
  simpa only [Nat.zero_add,he] using seqR_ok
    (I:=fun j s=>PositiveIH p S σ t (2*j) s ∧ Roots p S f s) (p.k/2) 0
    (fun j _ hj s hs=>by simpa only [Nat.mul_add,Nat.mul_one] using
      optimizedHint_pair_ok hp (by omega_arith : 2*j+1<p.k) hs.2 hs.1) s ⟨by simpa using h,roots⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached odd mask is retained through every response and hint check.
The frame comes from each callee's actual writes, including its bounded work
area, rather than the overall signer's writable scratch region. -/
theorem checks_ok {p : Params} {S : Nat} {σ s : State} {t : Nat} {f : Poly}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1)
    (cache : PolyIs s.mem (pa s t4P) f) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u ∧
      PolyIs u.mem (pa u t4P) f := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  refine WP.seq (WP.seq (WP.mono (challenge_ok hp ⟨roots,cache⟩ h h1) fun a ha=>?_))
  refine WP.seq (WP.mono (init_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (earlyPairedSeq_ok (I:=fun r u=>PositiveIZ p S σ t r u ∧ Roots p S f u) p.ℓ 0
    (fun r _ hr s h=>optimizedZ_rooted_ok hp (by omega_using [hr]) h.2 h.1)
    (fun r _ hr s h=>optimizedZ_pair_ok hp (by omega_using [hr]) h.2 h.1) b hb) fun c ⟨nz,_,hnz,hz,hdz⟩=>?_
  rw [Nat.zero_add] at hnz hdz
  have zflag:=PositiveIZ.done hnz hz.1 hdz
  refine ifOkElse_ok (fun hzpass=>?_) fun hzfail=>?_
  · have he:nz=p.ℓ:=hdz.resolve_right hzpass
    subst he
    refine WP.seq (WP.mono (earlyPairedSeq_ok (I:=fun r u=>PositiveIR p S σ t r u ∧ Roots p S f u) p.k 0
      (fun r _ hr s h=>optimizedR0_rooted_ok hp (by omega_using [hr]) h.2 h.1)
      (fun r _ hr s h=>optimizedR0_pair_ok hp (by omega_using [hr]) h.2 h.1) c ⟨positiveIR_of_IZ hz.1,hz.2⟩)
      fun d ⟨nr,_,hnr,hr,hdr⟩=>?_)
    rw [Nat.zero_add] at hnr hdr
    have rflag:=PositiveIR.done hnr hr.1 hdr
    refine ifOkElse_ok (fun hrpass=>?_) fun hrfail=>?_
    · have he:nr=p.k:=hdr.resolve_right hrpass
      subst he
      refine WP.seq (WP.mono (optimizedHint_paired_vector_ok hp hr.2 (positiveIH_of_IR hr.1)) fun e he=>?_)
      refine WP.seq (WP.mono (ones_ok hp hc he.2 he.1) fun a ha=>?_)
      exact WP.mono (branch_ok hp hc ha.2 ha.1) fun u hu=>⟨hu.1,hu.2.roots,hu.2.cache⟩
    · have flag : d.gpr .x24=0 := by
        rw [rflag]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←rflag]; exact hrfail))
      have fail : ¬ PassV p σ (p.ℓ*t) := by
        intro hpass
        exact (bit_ne.mpr (show ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t) from ⟨hpass.1,hpass.2.1⟩))
          (by rw [←rflag]; exact hrfail)
      exact WP.mono (reject_ok hp hc hr.2 hr.1.1.b.l hr.1.1.b.sampled fail flag)
        fun _ hu=>⟨.inr hu.1,hu.2.roots,hu.2.cache⟩
  · have flag : c.gpr .x24=0 := by
      rw [zflag]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←zflag]; exact hzfail))
    have fail : ¬ PassV p σ (p.ℓ*t) := by
      intro hpass
      exact (bit_ne.mpr hpass.1) (by rw [←zflag]; exact hzfail)
    exact WP.mono (reject_ok hp hc hz.2 hz.1.1.b.l hz.1.1.b.sampled fail flag)
      fun _ hu=>⟨.inr hu.1,hu.2.roots,hu.2.cache⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedLoopCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached commitment has the ordinary commitment result and prepares
exactly the odd mask of the next attempt. -/
def CommitCorrect (P : Prims) (p : Params) (S : Nat) : Prop :=
  ∀σ s t,PositiveIL p S σ t s → PairedRoots S s → (t=0 ∨ Mask p σ t s) →
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.commit P p) s fun u=>
      PositiveIC p S σ t u ∧ PairedRoots S u ∧ Mask p σ (t+1) u

theorem iter_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) (hcommit : CommitCorrect P p S)
    {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) (roots : PairedRoots S s)
    (cache : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.iter P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveLP p S σ t u ∧ PairedRoots S u ∧ Mask p σ (t+1) u := by
  unfold Impl.MlDsa.AArch64.Sign.Cached.iter
  refine WP.seq (WP.mono (hcommit σ s t h roots cache) fun a ⟨ha,ra,ca⟩=>?_)
  refine WP.seq (WP.mono (CachedChecks.ball_ok hP hp hb ⟨ra,ca⟩ ha) fun b ⟨hball,rb⟩=>?_)
  refine WP.seq (WP.ite (M:=isa) _ (eval_w0 b) (fun he=>?_) fun he=>?_)
  · have h1 : (b.gpr .x0).setWidth 32=1 := by
      rcases hball.r01 with e|e
      · rw [e] at he; exact absurd he (by decide)
      · exact e
    refine WP.mono (CachedChecks.checks_ok hp (ksChk_ok hp) rb.roots hball h1 rb.cache)
      fun u ⟨hu,ru,cu⟩=>?_
    exact WP.mono (CachedChecks.decEnd_ok hp (paramsOk hp) (lChk_ok hp) ⟨ru,cu⟩
      (hu.elim .inl (fun h=>.inr (.inl h)))) fun v hv=>⟨hv.1,hv.2.roots,hv.2.cache⟩
  · refine WP.mono (CachedChecks.ballFailure_ok hp (lChk_ok hp) rb hball (by simpa using he))
      fun u ⟨hu,ru⟩=>?_
    exact WP.mono (CachedChecks.decEnd_ok hp (paramsOk hp) (lChk_ok hp) ru (.inr (.inr hu)))
      fun v hv=>⟨hv.1,hv.2.roots,hv.2.cache⟩

/-- The first attempt samples its own mask. Every later attempt receives the
cached mask preserved through all checks and the counter decrement. -/
theorem signLoop_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) (hcommit : CommitCorrect P p S)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Cached.signLoop
  refine WP.seq (WP.mono (WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    fun a ⟨ha,ra⟩=>?_)
  refine WP.loop (M:=isa)
    (fun n s=>∃t,n=814-t ∧ PositiveIL p S σ t s ∧ PairedRoots S s ∧ (t=0 ∨ Mask p σ t s))
    (fun n s ⟨t,hn,hs,rs,cs⟩=>?_) 814 a ⟨0,rfl,ha,ra,.inl rfl⟩
  refine WP.mono (iter_ok hP hp hb hcommit hs rs cs) fun u ⟨hu,ru,cu⟩=>?_
  rcases hu with ⟨hz,hi⟩|⟨hz,hx⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz,814-(t+1),by have := hs.t_lt; omega_arith,
      t+1,rfl,hi,ru,.inr cu⟩
  · exact .inl ⟨by rw [eval_x9,hz]; rfl,hx,ru⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem commit_correct {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87)
    (hd : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S) :
    CommitCorrect P p S := by
  intro σ s t h roots hm
  exact WP.mono (WP.pairedRoots (commit_ok hP hp h hm) roots hd hP.s64)
    fun u ⟨⟨hu,hm⟩,ru⟩=>⟨hu,ru,hm⟩

theorem signLoop_concrete_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87)
    (hd : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  exact signLoop_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hd) h roots

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

/-! ## From `CachedRestTiming.lean` -/

@[expose] public section

/-! ## From `CachedLoopCache.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem Mask.transfer {p : Params} {S : Nat} {σ τ s : State} {t : Nat}
    (hσ : PositiveIK p S σ s) (hτ : PositiveIK p S τ s) (h : Mask p σ t s) : Mask p τ t s := by
  have hr : rppOf p σ=rppOf p τ := hσ.rpp.symm.trans hτ.rpp
  simpa only [Mask,Yv,hr] using h

/-- A cached mask is independent of the existential initial-state witness:
all witnesses of the current key invariant have the same private mask seed. -/
def CacheHeld (p : Params) (S t : Nat) (s : State) : Prop :=
  ∀σ,PositiveIK p S σ s → Mask p σ t s

theorem cacheHeld_of {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hk : PositiveIK p S σ s) (h : Mask p σ t s) : CacheHeld p S t s :=
  fun _ hτ=>h.transfer hk hτ

theorem PositiveLP.key {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveLP p S σ t s) : PositiveIK p S σ s := by
  rcases h with ⟨_,h⟩|⟨_,h⟩ <;> exact h.k

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedDepth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem cachedCommit_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.commit (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  have hm := DLe.of_fd C.expandMask.fd C.expandMask.nd
  have hm2 := DLe.of_fd C.expandMaskPair.fd C.expandMaskPair.nd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.outNtt := ⟨by decide +kernel, by lit_decide⟩
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp3 with rfl|rfl <;> exact ⟨by decide +kernel, by lit_decide⟩
  have hh : DLe 1 ((Sign.primsWith v.callee).highPack p.γ₂) := by
    rcases hp3 with rfl|rfl <;>
    (dsimp only [Sign.primsWith,Impl.MlDsa.AArch64.Optimized.HighPack.code]; dle_tac)
  have hc : DLe 1 (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*Impl.MlDsa.AArch64.Sign.w1Len p)
      (Impl.MlDsa.AArch64.Sign.cLen p)) := by
    rcases hp3 with rfl|rfl <;> exact ⟨by decide +kernel, by lit_decide⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  dle_tac

theorem cachedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87)
    {checks : Prog isa} (hchecks : DLe 1 checks) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p checks) := by
  have C := Sign.prims_okWith (keccak := v)
  have hc := cachedCommit_dle v hp3
  have hi := pairedInitialization_dle v p
  have hb := pairedBall_dle v p
  have hr := DLe.of_fd C.rejNTT.fd C.rejNTT.nd
  have hr4 := DLe.of_fd C.rej4.fd C.rej4.nd
  have hrtwo : DLe 1 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := ⟨by decide +kernel, by lit_decide⟩
  have hp := DLe.of_fd C.bitPack.fd C.bitPack.nd
  have hh := DLe.of_fd C.hintBitPack.fd C.hintBitPack.nd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.canonicalize := ⟨by decide +kernel, by lit_decide⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  split <;> dle_tac

theorem cachedPairedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) :=
  cachedSignWith_dle v hp (pairedChecks_dle p)

end VG.Proof.MlDsa.AArch64.Message

end

/-! ## From `CachedCorrect.lean` -/

/-! ## From `CachedHashTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (callAt sc)
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

theorem hashCall_tr {p : Params} {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args (hashArgs p) x x1 → Args (hashArgs p) y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.ditFree.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c (hashArgs p)) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args (hashArgs p) x x1 ∧ Args (hashArgs p) y y1)
      (block_nomem_tr (glue_nomem (hashArgs p))) (fun x y _ => ⟨hashGlue_ok p x, hashGlue_ok p y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.ditFree.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.call (k := k.ditFree) C.correct C.ct a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

theorem hashRegions_eq {p : Params} {x y : State} (e : SameB x y) :
    hashReads p x=hashReads p y ∧ hashWrites p x=hashWrites p y := by
  simp only [hashReads,hashWrites]
  rw [e.pa (p:=(.x26,0)) (by decide),e.pa (p:=sc oW1) (by decide),
    e.pa (p:=sc oMS) (by decide),e.pa (p:=sc oCT) (by decide),
    e.pa (p:=t1P) (by decide),e.pa (p:=t4P) (by decide)]
  exact ⟨rfl,rfl⟩

theorem hashReady_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {P : State→State→Prop}
    (hP : ∀x y,P x y→Lay S (sgR p) (sgW p) x ∧ Lay S (sgR p) (sgW p) y ∧ SameB x y) :
    RelCT isa P (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p))
      fun _ _=>True := by
  have C : CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p))
      (commitTailContract abi (p.k*w1Len p) (cLen p) S) := by
    rcases hp with rfl|rfl
    · exact CommitTail.callee65 hS
    · exact CommitTail.callee87 hS
  refine hashCall_tr C fun x y x1 y1 hxy hx hy => ?_
  obtain ⟨Lx,Ly,e⟩ := hP x y hxy
  obtain ⟨hr,hw⟩ := hashRegions_eq (p:=p) e
  refine ⟨hashReads p x,hashWrites p x,hash_pre hp Lx hx,?_,?_,
    (hash_cov hp Lx).1,(hash_cov hp Lx).2,?_,?_⟩
  · rw [hr,hw]; exact hash_pre hp Ly hy
  · sig_pub [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs]
    rw [hx.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
      hx.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
      hx.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
      hx.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
      hx.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
      hx.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),
      hy.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
      hy.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
      hy.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
      hy.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
      hy.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
      hy.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp hx,Args.sp hy]
    exact ⟨e.2,e.pa (by decide),e.pa (by decide),e.pa (by decide),
      e.pa (by decide),e.pa (by decide),e.pa (by decide)⟩
  · rw [hr,hw]; exact (hash_cov hp Ly).1
  · rw [hw]; exact (hash_cov hp Ly).2

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedSignTiming.lean` -/

/-! ## From `CachedHashSetupTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

/-- Loading the nonce does not make its value public; only the scratch
address contributes to this straight-line block's trace. -/
theorem hashSetup_tr {p : Params} {S : Nat} {P : State→State→Prop}
    (hP : ∀x y,P x y→LRel S (sgR p) (sgW p) x y) :
    RelCT isa P (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)])
      fun _ _=>True :=
  lrel_tr (hc:=.block []) hP rfl

/-- The complete commitment-plus-cache call has no data-dependent trace. -/
theorem hash_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) :
    RelCT isa (LRel S (sgR p) (sgW p)) (Impl.MlDsa.AArch64.Sign.Cached.hash p)
      fun _ _=>True := by
  have hp3 : Ok3 p := by rcases hp with rfl|rfl <;> simp [Ok3]
  have hr : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have ht := seqL (p:=p) (D:=S) (I:=fun _=>True) (J:=fun _=>True)
    (hashSetup_tr (fun _ _ h=>h.1))
    (fun s L _=>WP.mono (hashSetup_run hp3 s (L.inR hr)) fun t ⟨hk,_⟩=>
      ⟨⟨[],postB_of_keep hk.keep (by decide) (by rw [hk.mem]; exact Frame.refl _ _)⟩,trivial⟩)
    (hashReady_tr hp hS (fun _ _ h=>⟨h.1.lx,h.1.ly,h.1.regs,h.1.sp⟩))
  exact RelCT.mono ht (fun _ _ h=>⟨h,trivial,trivial⟩) (fun _ _ h=>h)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedConcreteCorrect.lean` -/

/-! ## From `CachedCommitmentTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached digest call preserves the original strict signing relation while
producing both the current commitment and the next attempt's tail mask. -/
theorem hash_root_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {E : State→State→Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveICh p S · t p.k))
      (Impl.MlDsa.AArch64.Sign.Cached.hash p)
      (RootRS p S E fun σ s=>PositiveIC p S σ t s ∧ Mask p σ (t+1) s) := by
  apply liftRootT (fun _ _ h=>⟨h.c.masks.l.st,h.c.masks.l.k.d.roots⟩)
    (fun _ _ _ h=>hash_ok hp hS h)
  exact RelCT.mono (hash_tr hp hS) (fun _ _ h=>h.1) (fun _ _ h=>h)

/-- Cached commitment timing uses only the public attempt index; cached mask and
hash contents remain secret throughout the unchanged signing schedule. -/
theorem commit_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {E : State→State→Prop} {t : Nat} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIL p S σ t s ∧ (t=0 ∨ Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.commit P p)
      (RootRS p S E fun σ s=>PositiveIC p S σ t s ∧ Mask p σ (t+1) s) := by
  have hp3 : Ok3 p := by
    rcases hp with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  exact RelCT.seq (masks_tr hP hp) (RelCT.seq (positiveRows_tr hp3)
    (RelCT.seq (positivePackRows_tr hP hp3) (hash_root_tr hp (by have := hP.sl; omega_using [this]))))

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedLoopTrace.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem iter_trace {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp0 : p=mlDsa65 ∨ p=mlDsa87) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.iter P p checks) (PairedIX p S t) := by
  have hp : Ok3 p := by rcases hp0 with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.iter
  have hct : RelCT isa
      (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.commit P p)
      (PairedRS p S (LeakEq p t) (PositiveIC p S · t)) :=
    RelCT.mono (paired_trace_frame hcommit hP.s64 (commit_tr hP hp0))
      (fun _ _ h=>h) (fun _ _ h=>(PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2).mono (fun _ _ h=>h.1))
  refine RelCT.seq hct (RelCT.seq (pairedBall_step_tr hP hp ht hball) ?_)
  refine RelCT.seq (R:=fun x y=>
      (PairedRS p S (LeakEq p t) (fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) x y ∧ True) ∨
      (PairedRS p S (LeakEq p t) (PositiveEB p S · t) x y ∧ True))
    (RelCT.ite ?_ ?_ ?_)
    (relOr (RelCT.mono (pairedEndPF_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h))
      (RelCT.mono (pairedEndB_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h)))
  · rintro x y ⟨_,he⟩; rw [eval_w0,eval_w0,he]
  · refine RelCT.mono (hchecks t ht) ?_ (fun _ _ h=>.inl ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h1 := x0_one hx.1.r01 hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h1⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h1⟩,hy.2⟩⟩,rs⟩,rp⟩
  · have hf : RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=0)
        (.block (([.movz .x .x24 0 0] : List Instr)++setQ (VG.Impl.MlDsa.AArch64.Call.sc oCNT) 1))
        (PairedRS p S (LeakEq p t) (PositiveEB p S · t)) :=
      RelCT.mono (paired_trace_frame (Nat.zero_le _) hP.s64 (positiveBallFailure_tr hp (lChk_ok hp)))
        (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
    refine RelCT.mono hf ?_ (fun _ _ h=>.inr ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h0 := x0_zero hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h0⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h0⟩,hy.2⟩⟩,rs⟩,rp⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The original leakage relation remains unchanged. Cache correctness is
an invariant of each execution, not additional observable information. -/
theorem iter_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (h16 : 16≤S)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.iter P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (fun x y=>PairedIX p S t x y ∧ CacheHeld p S (t+1) x ∧ CacheHeld p S (t+1) y) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  have hchecks : PairedChecksCT p S (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
    intro t ht
    apply positivePairedChecks_tr hp3 (ksChk_ok hp3) h16 hP.s64
    intro σ τ he hs ht'
    exact leq_prefixAgree (paramsOk hp3) he ht hs ht'
  intro x y tx ty x' y' hr ex ey
  obtain ⟨eq,hi⟩ := iter_trace hP hp hchecks hcommit hball ht _ _ _ _ _ _ hr ex ey
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := hr.1.1
  obtain ⟨_,u,eu,hu,ru,cu⟩ := iter_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hcommit)
    hx.1.1 hx.2 hx.1.2
  obtain ⟨_,v,ev,hv,rv,cv⟩ := iter_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hcommit)
    hy.1.1 hy.2 hy.1.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨eq,hi,cacheHeld_of (PositiveLP.key hu) cu,cacheHeld_of (PositiveLP.key hv) cv⟩

theorem signLoop_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (h16 : 16≤S)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p 0) (PositiveIK p S))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (PositiveOX p S) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.signLoop
  refine RelCT.seq (liftPairedR (J:=fun σ s=>PositiveIL p S σ 0 s)
    (fun _ _ _ h roots=>WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp3) h) roots (Nat.zero_le _) hP.s64)
    (lrel_tr (fun _ _ h=>h.root.1.lrel (fun _ _ h=>h.d.im.st)) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M:=isa)
    (fun n x y=>∃t,n=814-t ∧ PairedRS p S (LeakEq p t)
      (fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s)) x y)
    (fun n=>?_) 814)
    (fun _ _ h=>⟨0,rfl,h.mono (fun _ _ h=>⟨h,.inl rfl⟩)⟩) (fun _ _ h=>h)
  intro x y tx ty x' y' ⟨t,hn,hr⟩ ex ey
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,hx,_⟩ := hr.1.1; exact hx.1.1.t_lt
  obtain ⟨htr,hi,cx,cy⟩ := iter_tr hP hp h16 hcommit hball ht _ _ _ _ _ _ hr ex ey
  refine ⟨htr,by rw [eval_x9,eval_x9,hi.1.1],fun h=>hi.1.2.2 (x9_zero h),fun h=>?_⟩
  have hnxt := hi.next (x9_ne h)
  obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hnxt
  exact ⟨814-(t+1),by omega_using [hn, ht],t+1,rfl,
    ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,.inr (cx σ hx.1.k)⟩,hx.2⟩,
      ⟨⟨hy.1,.inr (cy τ hy.1.k)⟩,hy.2⟩⟩,rs⟩,rp⟩⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedVerified.lean` -/

