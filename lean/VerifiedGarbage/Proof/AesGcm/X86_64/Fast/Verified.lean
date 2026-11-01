module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.OnePassZ
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixSCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixS
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixN

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

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)
open VG.Proof.AesGcm.X86_64.Fast (fastCond_mx fastCond_spSafe fastCond_xdepth fastAad_mx fastAad_spSafe
  fastAad_xdepth)

/-- The one-pass loop named `n`. -/
def _root_.VG.Proof.AesGcm.X86_64.OnePassName.code : OnePassName → Prog isa
  | .r => Impl.Gcm.X86_64.StitchR.encN
  | .z => Impl.Gcm.X86_64.StitchZHTo.encN

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.ok (hF : ShortFacts) :
    ∀ n : OnePassName, (n = .z → np = 24) → EncNOk np hpn n.code
  | .r, _ => encNR_ok (hF.setupFin np hpn)
  | .z, h => by obtain rfl := h rfl; exact encNZ_ok hF.phaseOneZ

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.check :
    ∀ n : OnePassName, ∃ hc, (taint.check (Taint.ofRegs encNRegs) n.code hc).isSome = true
  | .r => encN_check
  | .z => encNZ_check

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.mx :
    ∀ n : OnePassName, n.code.allInstrs (fun i => !loadsMxcsr i) = true
  | .r => encNR_mx
  | .z => encNZ_mx

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.spSafe :
    ∀ n : OnePassName, n.code.all (fun i => !X86_64.isa.writesSp i) = true
  | .r => encNR_spSafe
  | .z => encNZ_spSafe

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.xdepth : ∀ n : OnePassName, n.code.x86_64Depth = 0
  | .r => encNR_xdepth
  | .z => encNZ_xdepth

/-- The whole blocks of the path for TLS records: in one pass if `v` takes
them so (`SealSplit.prefixN`, with its loop; on 256-bit registers, one to
three whole blocks without it, `SealSplit.prefixS`), and otherwise by `fTo`
(`SealSplit.prefix`). -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitPre (v : GcmImpl) (fTo : Fn) : Prog isa :=
  match v.onePass with
  | some .r => SealSplit.prefixS ⟨v.ctr.callee.name, v.ctr.callee.code⟩ fTo OnePassName.r.code
  | some .z => SealSplit.prefixN fTo OnePassName.z.code
  | none => SealSplit.prefix fTo

/-- `seal_split`'s code after the entry for the implementations `v` and a
prepared key context: the path for TLS records first, from 256 bytes if `v`
has `seal`'s short path, which is faster for less, and otherwise at every
length (`any`). -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitMidR (v : GcmImpl) (c : Callees) (fTo : Fn) : Prog isa :=
  if v.short then Fast.sel c (v.splitPre fTo) Short.finKs v.splitFin (v.splitMid c fTo)
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
variable (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) (T : BlkToFn (CtxMode.preparedN np hpn))

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
  exacts [prefixS_mx v.ctr.mxcsr (prefixN_mx (OnePassName.mx _) tp), prefixN_mx (OnePassName.mx _) tp, tp]

omit B in
theorem splitPre_spSafe (tp : (SealSplit.prefix T.fn).all (fun i => !X86_64.isa.writesSp i) = true) :
    (v.splitPre T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitPre; split
  exacts [prefixS_spSafe v.ctr.spSafe (prefixN_spSafe (OnePassName.spSafe _) tp),
    prefixN_spSafe (OnePassName.spSafe _) tp, tp]

omit B in
theorem splitPre_xdepth (tp : (SealSplit.prefix T.fn).x86_64Depth ≤ 56) : (v.splitPre T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitPre; split
  exacts [prefixS_xdepth v.ctr.noStack (by decide) (prefixN_xdepth (OnePassName.xdepth _) tp),
    prefixN_xdepth (OnePassName.xdepth _) tp, tp]

theorem splitMidR_mx : (v.splitMidR (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitMidR; split
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_mx v B T)
    replace tp := splitPre_mx v T tp
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
    replace tp := splitPre_spSafe v T tp
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
    have tp := splitPre_xdepth v T (Nat.max_le.mp t).1
    have o := splitMid_xdepth v B T
    simp only [Fast.sel, Fast.run, Code.x86_64Depth, fastCond_xdepth, fastAad_xdepth, fastTail_xdepth,
      Nat.max_le] at t tp o ⊢
    omega
  · have t := tail_xdepth v B T
    have tp := splitPre_xdepth v T (Nat.max_le.mp t).1
    have o := splitMid_xdepth v B T
    simp only [Fast.sel, Fast.run, Code.x86_64Depth, fastCond_xdepth, fastAad_xdepth, fastTailA_xdepth,
      Nat.max_le] at t tp o ⊢
    omega

theorem splitMidR_ok (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n = .z → np = 24) : MidOk (CtxMode.preparedN np hpn) (v.splitMidR (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMidR GcmImpl.splitPre; split <;> split
  · exact Fast.sel_ok hF v B (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T) Short.finKs_ksOk
      (splitFin_ok v hF) (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T) Short.finKs_ksOk (splitFin_ok v hF)
      (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixOk T) Short.finKs_ksOk (splitFin_ok v hF) (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T) Short.finKsA_ksOk
      (splitFin_ok v hF) (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T) Short.finKsA_ksOk (splitFin_ok v hF)
      (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixOk T) Short.finKsA_ksOk (splitFin_ok v hF) (splitMid_ok v B T hF)

theorem splitMidR_rel (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n = .z → np = 24) : MidRel (CtxMode.preparedN np hpn) (v.splitMidR (v.withBlk B) T.fn) := by
  have hq : ∀ n sl : Nat, sl ≤ n → 16 * (sl / 16) ≤ n := fun _ _ h => by omega
  have nq : ∀ n sl : Nat, sl ≤ n →
      16 * (if 1 ≤ sl / 256 ∧ sl / 256 < n / 256 then 16 * (n / 256) else sl / 16) ≤ n :=
    fun n sl h => by split <;> omega
  unfold GcmImpl.splitMidR GcmImpl.splitPre; split <;> split
  · exact @Fast.sel_rel _ _ false v B _ _ (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T)
      (prefixSRel hF v.ctr rfl (OnePassName.ok hF .r nofun) (OnePassName.check _) T) nq hF _ Short.finKs_ksOk
      Short.finKs_rel _ (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ false v B _ _ (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T)
      (prefixNRel (OnePassName.ok hF _ (hz _ ‹_›)) (OnePassName.check _) T) nq hF _ Short.finKs_ksOk Short.finKs_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ false v B _ _ (prefixOk T) (prefixRel T) hq hF _ Short.finKs_ksOk Short.finKs_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ true v B _ _ (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T)
      (prefixSRel hF v.ctr rfl (OnePassName.ok hF .r nofun) (OnePassName.check _) T) nq hF _ Short.finKsA_ksOk
      Short.finKsA_rel _ (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ true v B _ _ (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T)
      (prefixNRel (OnePassName.ok hF _ (hz _ ‹_›)) (OnePassName.check _) T) nq hF _ Short.finKsA_ksOk Short.finKsA_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ true v B _ _ (prefixOk T) (prefixRel T) hq hF _ Short.finKsA_ksOk Short.finKsA_rel _
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

theorem sealSplitR_correct (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n = .z → np = 24) (s : State)
    (hs : (Proof.AesGcm.sealSplitX86_64M (CtxMode.preparedN np hpn)).pre s) :
    ∃ t s', Exec isa (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.sealSplitX86_64M (CtxMode.preparedN np hpn)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealSplitM_wp (splitMidR_ok v B T hF hz) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealSplitR_mx v B T) he hg, hp⟩

end

section
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared) (T : BlkToFn CtxMode.prepared)

theorem sealSplitPrepared_core (hF : ShortFacts) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPreparedScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.prepared) (sealSplitR_correct v B T hF (fun _ _ _ => rfl))
    (sealSplitM_ct (splitMidR_ok v B T hF (fun _ _ _ => rfl)) (splitMidR_rel v B T hF (fun _ _ _ => rfl)))
    splitPrepared_implies

/-- `vg_aes_gcm_seal_split_prepared`, in its frame. -/
theorem sealSplitPrepared_framed (hF : ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.sealSplitPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPreparedPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitPrepared_core v B T hF) (by decide) (by decide) (by decide)
    (sealSplitR_spSafe v B T) (sealSplitR_xdepth v B T) (Proof.AesGcm.sealSplitPreparedPre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatPrepared_pre

end

end VG.Proof.AesGcm.X86_64.Split
