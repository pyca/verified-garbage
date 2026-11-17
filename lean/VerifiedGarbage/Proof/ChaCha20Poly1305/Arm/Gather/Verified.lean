module

import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Scrub
public import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm.SealGather
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Fn
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 696 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherArm`, `gather_implies`), and so the code, calling
`vg_chacha20_poly1305_seal` by its shared contract (`sealFn`), is `Verified`
against it (`sealGather_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Arm.FrameStack VG.Impl.ChaCha20Poly1305.Arm.SealGather

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

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i w₁ w₂ kd bk bn ba bd bt ok on oa od ot hgl hrd hwr pw bl fl
  obtain ⟨kt, nd, nt, ad, at_, dt, dds, ⟨dl, darg⟩, tds, ⟨tl, targ⟩, -⟩ := pw
  obtain ⟨bds, bls, barg⟩ := bl
  obtain ⟨ods, ol⟩ := fl
  exact ⟨hrd, hwr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr => ⟨(dl r hr).symm, (tl r hr).symm⟩,
    dt, darg, targ, bk, bn, ba, bds, bls, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, h⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    List.append_eq] at hp
  obtain ⟨qsp, q0, q1, q2, q3, a0, a1, a2, a3, a4, hd⟩ := hp
  refine ⟨q0, q1, q2, q3, qsp, fun i hi => ?_, hd⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; the tag at `0x5000`. -/
def gatherSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := bif Nat.beq a.toNat 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [gatherSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax]
    using gatherSat

theorem gather_implies : gatherArm.Implies (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified Arm.target (sealGather F.name F.code) (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696) :=
  Verified.of_correct (k := gatherArm) (sealGather_correct F) (sealGather_ct F) gather_implies

/-- `vg_chacha20_poly1305_seal`, with either arithmetic of Poly1305, by its
shared contract: the code its registration emits (`Scrub.sealReg`), whose
frames use at most the 664 bytes of stack its contract gives it. -/
def sealFn (umaal : Bool) : SealFn :=
  ⟨sealName umaal, Scrub.sealCode umaal, Scrub.sealCode_verified umaal, Scrub.sealCode_armStack umaal⟩

/-! ## Without secret residue -/

open VG.Arm.Scrub in
/-- `seal_gather`'s postcondition reads the memory on return only within
`dst` and `tag`. -/
theorem sealGatherPost_out (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.ChaCha20Poly1305.sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.ChaCha20Poly1305.sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb) vs m m₁ r →
      Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb)
        vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.ChaCha20Poly1305.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.ChaCha20Poly1305.sealGatherPost, ArgWord.ofRaw] at h ⊢
  intro h₁ h₂
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
  exact h h₁ h₂

theorem gatherOut (stack : Nat) :
    VG.Arm.Scrub.PostOut (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 32) :=
  VG.Arm.Scrub.postOut_of_local VG.Arm.Scrub.ScrubAbi.plain (sealGatherPost_out _)

theorem frameOk_696 : VG.Arm.Scrub.FrameOk 696 := by decide

theorem gather_armStack (umaal : Bool) :
    armStack (sealGather (sealFn umaal).name (sealFn umaal).code) ≤ 696 := by
  cases umaal <;> lit_decide

/-- `seal_gather`, calling `seal` with either arithmetic of Poly1305, followed
by a wipe of the stack its contract reserves, and by instructions that set
the registers a callee may change and the flags to constants. -/
theorem gather_noIcall (umaal : Bool) :
    VG.Arm.noIcall (sealGather (sealFn umaal).name (sealFn umaal).code) = true := by
  cases umaal <;> lit_decide

def gatherReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.sealGatherApi Arm.target :=
  VG.Arm.Scrub.scrubRegF {
      suffix := suffix
      code := sealGather (sealFn umaal).name (sealFn umaal).code
      verified := sealGather_verified (sealFn umaal) }
    (gather_armStack umaal) (gather_noIcall umaal) frameOk_696 (gatherOut _) rfl

end VG.Proof.ChaCha20Poly1305.Arm.Gather
