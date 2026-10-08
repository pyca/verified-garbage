import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 2592 bytes of stack below the stack
pointer that its frame and its call use (`Spec.Gcm.sealGatherContract`),
implies the one the proof is written against (`gatherAArch64`,
`gather_implies`), and so the code, calling an implementation of
`vg_aes_gcm_seal` by its shared contract, is `Verified` against it
(`sealGather_verified`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.SealGather

theorem sealGather_correct (F : SealFn) (s : State) (hs : gatherAArch64.pre s) :
    ∃ t s', Exec isa (sealGather F.fn) s t s' ∧ abiPreserved s s' ∧ gatherAArch64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp F hs
  exact ⟨t, s', he, ha, hp⟩

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl
theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filterMap_cons, ih]
theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filterMap_cons, ih]
theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

set_option linter.unusedSimpArgs false in
theorem gatherPre_of_spec {s : State} (h : (Spec.Gcm.sealGatherContract AArch64.abi 2592).pre s) : gatherPre s := by
  sig_pre [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, tl, ta⟩,
    bk, bn, ba, bd, bt, ⟨bds, bl, barg⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hr, hg⟩ := h
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩,
    dt, da, ta, bk, bn, ba, bds, bl, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hr, hg⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.Gcm.sealGatherContract AArch64.abi 2592).post s s' := by
  sig_post [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPost,
    AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.Gcm.sealGatherContract AArch64.abi 2592).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, q6, q7, a0, a1, a2, hd⟩ := hp
  exact ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, a0, a1, a2, hd⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`: no
slices, no nonce, additional data or text; the tag at `0x5000`. -/
def gatherSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := if a = 0x9011 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.Gcm.sealGatherContract AArch64.abi 2592).pre s := by
  sig_implies_sat [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq] [gatherSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using gatherSat

theorem gather_implies : gatherAArch64.Implies (Spec.Gcm.sealGatherContract AArch64.abi 2592) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified AArch64.target (sealGather F.fn) (Spec.Gcm.sealGatherContract AArch64.abi 2592) :=
  Verified.of_correct (k := gatherAArch64) (sealGather_correct F) (sealGather_ct F) gather_implies

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

open VG.Impl.AesGcm.AArch64 in
/-- The frames of `vg_aes_gcm_seal`, in its frame of 2576 bytes, use at most those. -/
theorem seal_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 («seal» v.callees)).aarch64Depth ≤ 2576 := by
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, «seal», j0, j0hash, oneAad, encBody, fo, textAbs,
    finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.aarch64Depth, Instr.frameUnits,
    depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.key.noFrames, depth_of_noFrames v.gh.noFrames]
  decide

end VG.Proof.AesGcm.AArch64.Gather
