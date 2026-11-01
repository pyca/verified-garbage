module
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
public import VerifiedGarbage.Proof.Rsa.X86.PrivLoopTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContext
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigest
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverBlocksTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverZero
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverReleaseArgs
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero

/-! # Digest copying and zero output use only public pointers and counters -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct loopTaint releaseLoop_relCT)
open VG.Proof.RsaPkcs1Sig.X86.Sgn (clearTaint clear_relCT)

structure ReleaseReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.output
  src : s.gpr .esi = g.digest
  count : s.gpr .ecx = BitVec.ofNat 32 g.outputLength

theorem releaseArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block releaseArgs) s (ReleaseReady g bs) := by
  refine WP.mono (releaseArgs_ok h) ?_
  rintro t ⟨ht, _, _, _, _, dst, cnt, src⟩
  exact ⟨ht, dst, src, cnt⟩

theorem releaseReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : ReleaseReady g bs s) (ht : ReleaseReady g bs t) : VG.X86.Taint.Agree loopTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.context.sp.trans ht.context.sp.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.dst.trans ht.dst.symm
  · exact hs.count.trans ht.count.symm

theorem release_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) release (fun _ _ => True) := by
  unfold release
  apply pair_seq_ct (releaseArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => releaseArgs_ready h) (fun _ h => releaseArgs_ready h)
  apply VG.RelCT.seq (releaseLoop_relCT.mono (fun _ _ h => releaseReady_agree h.1 h.2)
    (fun _ _ h => sp_agree (h.rf.1 .esp (by decide))))
  exact return_relCT.mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem zeroOut_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) zeroOut (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  obtain ⟨hs, ht⟩ := H
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (zeroArgs_relCT _ _ _ _ _ _ (sp_agree (hs.sp.trans ht.sp.symm)) E1 F1).1
      obtain ⟨_, _, _, Ss, Cs, _⟩ := wp_result (zeroArgs_ok hs) E1
      obtain ⟨_, _, _, St, Ct, _⟩ := wp_result (zeroArgs_ok ht) F1
      have agree : VG.X86.Taint.Agree clearTaint _ _ := agree_regs (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Ss.trans St.symm
        · exact Cs.trans Ct.symm)
      have T2 := (clear_relCT _ _ _ _ _ _ agree E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
