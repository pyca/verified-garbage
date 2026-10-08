import VerifiedGarbage.Proof.AesGcm.Arm.Gather.CT
import VerifiedGarbage.Proof.AesGcm.Arm.Frame

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, ARMv7: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 2640 bytes of stack below the stack
pointer that its frame and its call use (`Spec.Gcm.sealGatherContract`),
implies the one the proof is written against (`gatherArm`,
`gather_implies`), and so the code, calling `vg_aes_gcm_seal` by its shared
contract (`sealFn`), is `Verified` against it (`sealGather_verified`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.Gather

open VG VG.Arm VG.Arm.FrameStack VG.Impl.AesGcm.Arm.SealGather

theorem sealGather_correct (F : SealFn) (s : State) (hs : gatherArm.pre s) :
    ∃ t s', Exec isa (sealGather F.name F.code) s t s' ∧ abiPreserved s s' ∧ gatherArm.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp F hs
  exact ⟨t, s', he, ha, hp⟩

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem gatherPre_of_spec {s : State} (h : (Spec.Gcm.sealGatherContract Arm.abi 2640).pre s) : gatherPre s := by
  sig_pre [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i w₁ w₂ kd bk bn ba bd bt ok on oa od ot hR hrd hwr pw bl fl
  obtain ⟨kt, nd, nt, ad, at_, dt, dds, ⟨dl, darg⟩, tds, ⟨tl, targ⟩, -⟩ := pw
  obtain ⟨bds, bls, barg⟩ := bl
  obtain ⟨ods, ol⟩ := fl
  exact ⟨hrd, hwr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr => ⟨(dl r hr).symm, (tl r hr).symm⟩,
    dt, darg, targ, bk, bn, ba, bds, bls, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hR, h⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.Gcm.sealGatherContract Arm.abi 2640).post s s' := by
  sig_post [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.Gcm.sealGatherContract Arm.abi 2640).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq] at hp
  obtain ⟨qsp, q0, q1, q2, q3, a0, a1, a2, a3, a4, a5, a6, hd⟩ := hp
  refine ⟨q0, q1, q2, q3, qsp, fun i hi => ?_, hd⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4, a5, a6]

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`: no
slices, no nonce, additional data or text; the tag at `0x5000`. -/
def gatherSat : State :=
  { mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
      [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0, 0⟩, ⟨0x5000, 16⟩] with
    mem := fun a => if a = 0x8019 then 0x50 else 0 }

theorem gatherSat_pre : ∃ s, (Spec.Gcm.sealGatherContract Arm.abi 2640).pre s := by
  implies_sat [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [gatherSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using gatherSat

theorem gather_implies : gatherArm.Implies (Spec.Gcm.sealGatherContract Arm.abi 2640) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified Arm.target (sealGather F.name F.code) (Spec.Gcm.sealGatherContract Arm.abi 2640) :=
  Verified.of_correct (k := gatherArm) (sealGather_correct F) (sealGather_ct F) gather_implies

open VG.Impl.AesGcm.Arm in
/-- The frames of `vg_aes_gcm_seal`, with its working space, use at most the
2600 bytes of stack its contract gives it. -/
theorem seal_stack : armStack (Impl.StackScratch.Arm.withStackScratch 2592 5 «seal») ≤ 2600 := by
  decide +kernel

/-- `vg_aes_gcm_seal`, by its shared contract. -/
def sealFn : SealFn :=
  ⟨Spec.Gcm.sealApi.name, Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.«seal», seal_framed, seal_stack⟩

end VG.Proof.AesGcm.Arm.Gather
