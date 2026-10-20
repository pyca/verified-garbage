module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResources
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
import VerifiedGarbage.Proof.Dsa.X86.Generation.DispatchGenerate

/-! # Functional correctness of argument setup followed by width dispatch -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem entryBody_ok (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {s t : State} {A : ParameterABI s} {W : Nat → BitVec 32}
    (R : EntryResources A t) (words : FrameWords t.mem A.geometry.frameBase W)
    (write : ∀ i, i < (arg s 1).toNat → InRegions t.wr (off (argumentPointer s 0) i) 1) :
    WP isa (entryBody H.sha1 H.sha256 F.name F.code) t (GenerationResult (A.plan W) t) := by
  have length : (A.plan W).saved 7 = BitVec.ofNat 32 (2 * (A.plan W).geometry.pLen + (A.plan W).geometry.qLen) := by
    change arg s 1 = BitVec.ofNat 32 (2 * (arg s 2).toNat + (arg s 3).toNat)
    rw [← A.outLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have room : ((A.plan W).saved 6).toNat + (2 * (A.plan W).geometry.pLen + (A.plan W).geometry.qLen) ≤ 2 ^ 32 := by
    change (arg s 0).toNat + (2 * (arg s 2).toNat + (arg s 3).toNat) ≤ 2 ^ 32
    rw [← A.outLength]; exact A.outBound
  have apart : ((A.plan W).geometry.part packed (2 * (A.plan W).geometry.pLen + (A.plan W).geometry.qLen)).Disjoint
      ⟨((A.plan W).saved 6).setWidth 64, 2 * (A.plan W).geometry.pLen + (A.plan W).geometry.qLen⟩ := by
    have ar := A.outScratch.symm.sub_left A.arenaSub
    have p := A.geometry.width
    have q := A.geometry.qWidth
    have sub := A.geometry.part_sub (d := packed) (n := 2 * A.geometry.pLen + A.geometry.qLen)
      (by unfold packed usedBytes domainCheck; omega)
    have h := ar.sub_left sub
    change (A.geometry.part packed (2 * A.geometry.pLen + A.geometry.qLen)).Disjoint
      ⟨argumentPointer s 0, 2 * (arg s 2).toNat + (arg s 3).toNat⟩
    rw [← A.outLength]; exact h
  unfold entryBody
  refine WP.seq (WP.mono (entryStorage_ok R words) fun a ⟨Ra, Oa, Ka⟩ => ?_)
  refine WP.mono (dispatchGenerate_ok H F Ra rfl
    (by simpa only [ParameterABI.plan, ParameterABI.seeds, ParameterABI.tape, ParameterABI.geometry,
      Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.seedLength)
    (by simpa only [ParameterABI.plan, ParameterABI.hs, ParameterABI.tape, ParameterABI.geometry,
      Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.hLength)
    length room apart (by
      intro i hi
      change InRegions a.wr (off (argumentPointer s 0) i) 1
      rw [Ka.2.2]
      exact write i (by change i < 2 * (arg s 2).toNat + (arg s 3).toNat at hi; rw [A.outLength]; exact hi)))
    fun u ⟨ax, bytes, O, rd, wr, esp⟩ => ?_
  refine ⟨ax, bytes, ?_, rd.trans Ka.2.1, wr.trans Ka.2.2, esp.trans (Ka.1 _ (by decide))⟩
  apply Frame.trans (Oa.mono ?_) O
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  unfold generationWrites parameterWrites
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
end VG.Proof.Dsa.X86.Generation
