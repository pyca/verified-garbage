module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixN
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-GCM `seal_split` on x86-64 with a prepared key context: `Verified`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_split_prepared`
takes the path for TLS records (`Fast.sel`) before `splitMid` if the
implementations have `seal`'s short path (`splitMidR`), which needs the CPU
features of the loops on 512-bit registers; it meets the shared contract of
`Spec/Gcm/Prepared.lean` as `Split.sealSplitP_framed` does
(`sealSplitPrepared_framed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)
open VG.Proof.AesGcm.X86_64.Fast (fastCond_mx fastCond_spSafe fastCond_xdepth fastAad_mx fastAad_spSafe
  fastAad_xdepth)

/-- The whole blocks of the path for TLS records: in one pass if `v` takes
them so (`SealSplit.prefixN`), and otherwise by `fTo` (`SealSplit.prefix`). -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitPre (v : GcmImpl) (fTo : Fn) : Prog isa :=
  if v.onePass then SealSplit.prefixN fTo else SealSplit.prefix fTo

/-- `seal_split`'s code after the entry for the implementations `v` and a
prepared key context: the path for TLS records first, from 256 bytes if `v`
has `seal`'s short path, which is faster for less, and otherwise at every
length (`any`). -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitMidR (v : GcmImpl) (c : Callees) (fTo : Fn) : Prog isa :=
  if v.short then Fast.sel c (SealSplit.prefix fTo) Short.finKs v.splitFin (v.splitMid c fTo)
  else Fast.sel c (v.splitPre fTo) Short.finKsA v.splitFin (v.splitMid c fTo) true

theorem fastTail_mx : (Fast.tail Short.finKs : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem fastTail_spSafe : (Fast.tail Short.finKs : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem fastTail_xdepth : (Fast.tail Short.finKs : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem fastTailA_mx : (Fast.tail Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem fastTailA_spSafe : (Fast.tail Short.finKsA : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem fastTailA_xdepth : (Fast.tail Short.finKsA : Prog isa).x86_64Depth = 0 := by decide +kernel

section
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared) (T : BlkToFn CtxMode.prepared)

theorem tail_mx :
    ((.seq (SealSplit.«prefix» T.fn) (SealSplit.body (v.withBlk B) v.splitFin) : Prog isa)).allInstrs
      (fun i => !loadsMxcsr i) = true :=
  ((Bool.and_eq_true _ _).mp (run_mx v B T)).2

theorem tail_spSafe :
    ((.seq (SealSplit.«prefix» T.fn) (SealSplit.body (v.withBlk B) v.splitFin) : Prog isa)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  ((Bool.and_eq_true _ _).mp (run_spSafe v B T)).2

theorem tail_xdepth :
    ((.seq (SealSplit.«prefix» T.fn) (SealSplit.body (v.withBlk B) v.splitFin) : Prog isa)).x86_64Depth ≤ 56 :=
  (Nat.max_le.mp (run_xdepth v B T)).2

omit B in
theorem splitPre_mx (tp : (SealSplit.prefix T.fn).allInstrs (fun i => !loadsMxcsr i) = true) :
    (v.splitPre T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitPre; split
  exacts [prefixN_mx tp, tp]

omit B in
theorem splitPre_spSafe (tp : (SealSplit.prefix T.fn).all (fun i => !X86_64.isa.writesSp i) = true) :
    (v.splitPre T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitPre; split
  exacts [prefixN_spSafe tp, tp]

omit B in
theorem splitPre_xdepth (tp : (SealSplit.prefix T.fn).x86_64Depth ≤ 56) : (v.splitPre T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitPre; split
  exacts [prefixN_xdepth tp, tp]

theorem splitMidR_mx : (v.splitMidR (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitMidR; split
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_mx v B T)
    have o := splitMid_mx v B T
    simp only [Fast.sel, Fast.run, Code.allInstrs] at tp tb o ⊢
    rw [fastCond_mx, fastAad_mx, o, tp, tb, fastTail_mx]; rfl
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_mx v B T)
    replace tp := splitPre_mx v T tp
    have o := splitMid_mx v B T
    simp only [Fast.sel, Fast.run, Code.allInstrs] at tp tb o ⊢
    rw [fastCond_mx, fastAad_mx, o, tp, tb, fastTailA_mx]; rfl

theorem splitMidR_spSafe : (v.splitMidR (v.withBlk B) T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitMidR; split
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_spSafe v B T)
    have o := splitMid_spSafe v B T
    simp only [Fast.sel, Fast.run, Code.all] at tp tb o ⊢
    rw [fastCond_spSafe, fastAad_spSafe, o, tp, tb, fastTail_spSafe]; rfl
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_spSafe v B T)
    replace tp := splitPre_spSafe v T tp
    have o := splitMid_spSafe v B T
    simp only [Fast.sel, Fast.run, Code.all] at tp tb o ⊢
    rw [fastCond_spSafe, fastAad_spSafe, o, tp, tb, fastTailA_spSafe]; rfl

theorem splitMidR_xdepth : (v.splitMidR (v.withBlk B) T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitMidR; split
  · have t := tail_xdepth v B T
    have o := splitMid_xdepth v B T
    simp only [Fast.sel, Fast.run, Code.x86_64Depth, fastCond_xdepth, fastAad_xdepth, fastTail_xdepth,
      Nat.max_le] at t o ⊢
    omega
  · have t := tail_xdepth v B T
    have tp := splitPre_xdepth v T (Nat.max_le.mp t).1
    have o := splitMid_xdepth v B T
    simp only [Fast.sel, Fast.run, Code.x86_64Depth, fastCond_xdepth, fastAad_xdepth, fastTailA_xdepth,
      Nat.max_le] at t tp o ⊢
    omega

theorem splitMidR_ok (hF : ShortFacts) : MidOk CtxMode.prepared (v.splitMidR (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMidR GcmImpl.splitPre; split
  · exact Fast.sel_ok hF v B (prefixOk T) Short.finKs_ksOk (splitFin_ok v hF) (splitMid_ok v B T hF)
  · split
    · exact Fast.sel_ok hF v B (prefixNOk hF.setupFin T) Short.finKsA_ksOk (splitFin_ok v hF)
        (splitMid_ok v B T hF)
    · exact Fast.sel_ok hF v B (prefixOk T) Short.finKsA_ksOk (splitFin_ok v hF) (splitMid_ok v B T hF)

theorem splitMidR_rel (hF : ShortFacts) : MidRel CtxMode.prepared (v.splitMidR (v.withBlk B) T.fn) := by
  have hq : ∀ n sl : Nat, sl ≤ n → 16 * (sl / 16) ≤ n := fun _ _ h => by omega
  have nq : ∀ n sl : Nat, sl ≤ n →
      16 * (if 1 ≤ sl / 256 ∧ sl / 256 < n / 256 then 16 * (n / 256) else sl / 16) ≤ n :=
    fun n sl h => by split <;> omega
  unfold GcmImpl.splitMidR GcmImpl.splitPre; split
  · exact @Fast.sel_rel false v B _ _ (prefixOk T) (prefixRel T) hq hF _ Short.finKs_ksOk Short.finKs_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · split
    · exact @Fast.sel_rel true v B _ _ (prefixNOk hF.setupFin T) (prefixNRel hF.setupFin T) nq hF _
        Short.finKsA_ksOk Short.finKsA_rel _ (splitFin_rel v hF) _ (splitMid_rel v B T hF)
    · exact @Fast.sel_rel true v B _ _ (prefixOk T) (prefixRel T) hq hF _ Short.finKsA_ksOk Short.finKsA_rel _
        (splitFin_rel v hF) _ (splitMid_rel v B T hF)

theorem sealSplitR_mx :
    (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [SealSplit.«seal», Code.allInstrs]
  rw [splitMidR_mx v B T]; rfl

theorem sealSplitR_spSafe :
    (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [SealSplit.«seal», Code.all]
  rw [splitMidR_spSafe v B T]; rfl

theorem sealSplitR_xdepth : (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)).x86_64Depth ≤ 56 := by
  have := splitMidR_xdepth v B T
  simp only [SealSplit.«seal», Code.x86_64Depth, tagOut, Nat.max_le]
  omega

theorem sealSplitR_correct (hF : ShortFacts) (s : State)
    (hs : (Proof.AesGcm.sealSplitX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.sealSplitX86_64M CtxMode.prepared).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealSplitM_wp (splitMidR_ok v B T hF) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealSplitR_mx v B T) he hg, hp⟩

theorem sealSplitPrepared_core (hF : ShortFacts) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPreparedScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.prepared) (sealSplitR_correct v B T hF)
    (sealSplitM_ct (splitMidR_ok v B T hF) (splitMidR_rel v B T hF)) splitPrepared_implies

/-- `vg_aes_gcm_seal_split_prepared`, in its frame. -/
theorem sealSplitPrepared_framed (hF : ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)))
      (Spec.Gcm.sealSplitPreparedContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.sealSplitPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealSplitPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitPrepared_core v B T hF) (by decide) (by decide) (by decide)
    (sealSplitR_spSafe v B T) (sealSplitR_xdepth v B T) (Proof.AesGcm.sealSplitPreparedPre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatPrepared_pre

end

end VG.Proof.AesGcm.X86_64.Split
