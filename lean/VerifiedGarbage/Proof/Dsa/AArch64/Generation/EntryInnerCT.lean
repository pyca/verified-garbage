module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicContextCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryBodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryLink
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicContextCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryBodyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryLink
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Compose register saves, public-input generation, and register restoration. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

private theorem saves_ct : RelCT isa (fun s t => s.sp = t.sp) (.block entrySave) (fun _ _ => True) := by
  apply (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
  · intro s t h
    exact ⟨(), True.intro, True.intro, h⟩
  · exact fun _ _ _ => True.intro

private theorem restores_ct : RelCT isa (fun s t => s.sp = t.sp) (.block entryRestore) (fun _ _ => True) := by
  apply (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
  · intro s t h
    exact ⟨(), True.intro, True.intro, h⟩
  · exact fun _ _ _ => True.intro

private theorem entryTail_ct (H : GenerationHashes) (M : Mont) (T : PrimeTest) :
    RelCT isa (Two EntryBefore)
      (.seq (.block (entryHeader ++ entryIncoming ++ entryDerived))
        (.seq (dispatch H.sha1 H.sha256 M.mm T.run) (.block entryRestore))) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq (R := fun (s t : State) => s.sp = t.sp) ?_ restores_ct
  intro s t xs ys u v hp es et
  have tr := (entryCore_ct H M T _ _ _ _ _ _ hp es et).1
  obtain ⟨_, _, _, hsp⟩ := hp
  exact ⟨tr, (Exec.rdwr es).2.2.trans (hsp.trans (Exec.rdwr et).2.2.symm)⟩

private theorem saved_state {s t : State} {tr : List Leak}
    (h : Exec isa (.block entrySave) (allocState 448 s) tr t) : t = linkState s := by
  obtain ⟨_, u, e, hu⟩ := entrySave_ok s
  obtain ⟨_, rfl⟩ := Exec.det h e
  exact hu

theorem entryAllocated_ct (H : GenerationHashes) (M : Mont) (T : PrimeTest)
    {s t u v : State} (hs : GenerationABI s) (ht : GenerationABI t) (hp : GenerationPublicAgree s t)
    {xs ys : List Leak}
    (es : Exec isa (entryBody H.sha1 H.sha256 M.mm T.run) (allocState 448 s) xs u)
    (et : Exec isa (entryBody H.sha1 H.sha256 M.mm T.run) (allocState 448 t) ys v) : xs = ys := by
  cases es with
  | seq sa ba =>
    cases et with
    | seq sb bb =>
      have hsaves := (saves_ct _ _ _ _ _ _ (by change s.sp - 448#64 = t.sp - 448#64; rw [hp.sp]) sa sb).1
      have asaved := saved_state sa
      have bsaved := saved_state sb
      subst asaved bsaved
      have ha : EntryBefore (parameterOf hs) (linkState s) := ⟨entryInitial_link hs, rfl⟩
      have hb : EntryBefore (parameterOf ht) (linkState t) := ⟨entryInitial_link ht, rfl⟩
      rw [← hp.parameter (hs := hs) (ht := ht)] at hb
      have hsp : (linkState s).sp = (linkState t).sp := by
        change s.sp - 448#64 = t.sp - 448#64
        rw [hp.sp]
      have tails := (entryTail_ct H M T _ _ _ _ _ _ ⟨parameterOf hs, ha, hb, hsp⟩ ba bb).1
      exact congrArg₂ List.append hsaves tails

end VG.Proof.Dsa.AArch64.Generation
