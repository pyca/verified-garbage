import VerifiedGarbage.Proof.AesGcm.X86.Gather.CT
import VerifiedGarbage.Proof.AesGcm.X86.Frame
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 2684 bytes of stack below the stack
pointer that its frame and its call use (`Spec.Gcm.sealGatherContract`),
implies the one the proof is written against (`gatherX86`,
`gather_implies`), and so the code, calling an instance of
`vg_aes_gcm_seal` by its shared contract (`sealFn`), is `Verified` against
it (`sealGather_verified`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86 VG.Impl.AesGcm.X86.SealGather

theorem sealGather_correct (F : SealFn) (s : State) (hs : gatherX86.pre s) :
    ∃ t s', Exec isa (sealGather F.name F.code) s t s' ∧ abiPreserved s s' ∧ gatherX86.post s s' := by
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

/-- The pairs of the slices, read only, and the arguments, writable. -/
theorem pairFacts_ro_w (l : List Region) (a : Region) :
    Sig.conj (Sig.pairFacts (l.map (fun r => (r, false)) ++ [(a, true)])) ↔ ∀ r ∈ l, r.Disjoint a := by
  induction l with
  | nil => simp [Sig.pairFacts, Sig.conj]
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, Sig.pairFacts, List.filterMap_append, List.filterMap_map,
      Function.comp_def, Bool.false_or, Sig.conj_append, ih, List.forall_mem_cons]
    simp [List.filterMap_cons, Sig.conj, Sig.conj_cons, filterMap_none']

theorem gatherPre_of_spec {s : State} (h : (Spec.Gcm.sealGatherContract X86.abi 2684).pre s) : gatherPre s := by
  sig_pre [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, X86.abi] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append, List.append_nil,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons, Sig.pairFacts, argBytes, argVal, ↓reduceIte, Nat.reduceEqDiff,
    Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64, List.append_eq,
    pairFacts_ro_w] at *
  rename_i w₁ w₂ hrd hwr kd pw ek en ea ed et bl fl ok on oa od ot hR
  obtain ⟨kt, karg, nd, nt, narg, ad, at_, aarg, dt, dds, ⟨dls, darg⟩, tds, ⟨tls, targ⟩, dsarg, lsarg⟩ := pw
  obtain ⟨eds, ⟨els, earg⟩, bk, bn, ba, bd, bt, bds, bls, barg⟩ := bl
  obtain ⟨ods, ol⟩ := ot
  exact ⟨hrd, hwr, kd, kt, karg, nd, nt, narg, ad, at_, aarg, dt, dds, dls, darg, tds, tls, targ, dsarg, lsarg,
    ek, en, ea, ed, et, eds, els, earg, bk, bn, ba, bd, bt, bds, bls, barg, fl, ok, on, oa, od, ods, ol, w₁,
    by omega, hR, h⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.Gcm.sealGatherContract X86.abi 2684).post s s' := by
  sig_post [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPost, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceMul, sw32, toNat_w64]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.Gcm.sealGatherContract X86.abi 2684).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceMul, sw32, toNat_w64] at hp
  obtain ⟨qsp, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hd⟩ := hp
  refine ⟨qsp, fun i hi => ?_, hd⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`: no
slices, no nonce, additional data or text; its eleven argument slots at
`0x8004`. -/
def gatherSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30 else if a = 0x8025 then 0x40
    else if a = 0x802d then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 44⟩]

theorem gatherSat_pre : ∃ s, (Spec.Gcm.sealGatherContract X86.abi 2684).pre s := by
  implies_sat [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [gatherSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using gatherSat

theorem gather_implies : gatherX86.Implies (Spec.Gcm.sealGatherContract X86.abi 2684) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified X86.target (sealGather F.name F.code) (Spec.Gcm.sealGatherContract X86.abi 2684) :=
  Verified.of_correct (k := gatherX86) (sealGather_correct F) (sealGather_ct F) gather_implies

open VG.Impl.AesGcm.X86 VG.Impl.StackScratch.X86 in
/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`, with
its working space in a frame of its own. -/
def sealFn (v : GcmImpl) : SealFn where
  name := Spec.Gcm.sealApi.name ++ v.suffix
  code := withStackScratch 2604 9 («seal» v.callees)
  verified := seal_framed v
  noSp := by
    have hs := NoSp.of_all (seal_noEsp v)
    have ha : NoSp (.block (setArgs 2604 9) : Prog isa) := NoSp.of_all (by decide +kernel)
    intro i hi
    simp only [withStackScratch, instrs, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi | hi) | rfl
    · rfl
    · exact ha i hi
    · exact hs i hi
    · rfl
  depth := by
    have := seal_stackUse v
    simp only [withStackScratch, stackUse, frameBytes, Nat.zero_max]
    exact Nat.le_trans (Nat.add_le_add_right this 2604) (by decide)

/-- No instruction of the code, or of the instance it calls, writes `esp`
but its frames' push and pop. -/
theorem sealGather_spSafe (v : GcmImpl) :
    (sealGather (sealFn v).name (sealFn v).code).all (fun i => !X86.isa.writesSp i) = true := by
  have hc : (sealFn v).code.all (fun i => !X86.isa.writesSp i) = true :=
    withStackScratch_spSafe (bytes := 2604) (n := 9) (by decide) (seal_spSafe v)
  have he : (Code.block entry : Prog isa).all (fun i => !X86.isa.writesSp i) = true := by decide +kernel
  have hg : gather.all (fun i => !X86.isa.writesSp i) = true := by decide +kernel
  have hr : (Code.block restore : Prog isa).all (fun i => !X86.isa.writesSp i) = true := by decide +kernel
  show (!X86.isa.writesSp (.alloc 48) && ((Code.block entry : Prog isa).all (fun i => !X86.isa.writesSp i) &&
      (gather.all (fun i => !X86.isa.writesSp i) && ((sealFn v).code.all (fun i => !X86.isa.writesSp i) &&
        (Code.block restore : Prog isa).all (fun i => !X86.isa.writesSp i)))) &&
      !X86.isa.writesSp (.free 48)) = true
  rw [he, hg, hc, hr]; rfl

end VG.Proof.AesGcm.X86.Gather
