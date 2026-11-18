module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAddresses
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTClassify
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFinish
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBranch
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSatWitness
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.Data.Nat.Bitwise.Basic

/-! ### `Ffdh.Arm.KeySearch.Sat`, which only this module used -/

section

/-! A concrete legal ARMv7 key-search invocation: a structurally valid
512-bit domain without q and an exhausted initialized retry budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

private def keySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else if a = 0x8005 then 0x30 else if a = 0x8008 then 0x80
    else if a = 0x800C then 0x40 else if a = 0x8011 then 0x70 else if a = 0x8019 then 0x90
    else if a = 0x801C then 0x20 else if a = 0x801D then 4 else if a = 0x8021 then 0x40
    else if a = 0x4010 then 0x40 else if a = 0x3000 then 0x80 else if a = 0x303F then 1
    else if a = 0x307F then 2 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x8000, 36⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x4000, 128⟩]

theorem plain_sat : ∃ s, (GenerationPolicy.searchContract .full abi (stackUse .full)).pre s := by
  refine ⟨keySat, ?_⟩
  rw [GenerationPolicy.searchContract_full]
  sig_iff
  sig_reduce [Spec.Ffdh.keySearchContract, keySearchSig, pLenValid, domainLenValid,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel


@[irreducible] private def searchMem (W : List (BitVec 64)) : Mem := fun a =>
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 W a else keySat.mem a

private def searchSat (W : List (BitVec 64)) : State :=
  { keySat with mem := searchMem W, rd := keySat.rd ++ [⟨0x100000, 17744⟩], syms := fun _ => 0x100000 }

private theorem searchMem_held (W : List (BitVec 64)) (length : W.length = 2218) (i : Nat) (hi : i < W.length) :
    (searchMem W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  rw [← constMem_held 0x100000 W (by rw [length]; decide) i hi]
  apply Mem.readW_congr
  intro j hj
  unfold searchMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [length] at hi
  omega_using [hi, hj]

private theorem searchSat_arg (W : List (BitVec 64)) {i : Nat} (hi : i < 9) :
    stackArg (searchSat W) i = stackArg keySat i := by
  apply Mem.readW_congr
  intro j hj
  change searchMem W _ = keySat.mem _
  unfold searchMem
  apply ite_eq_right
  have small : ∀ i < 9, ∀ j < 4,
      ¬ (stackArgAddr keySat i + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small i hi j hj

private theorem searchSat_domain (W : List (BitVec 64)) :
    Spec.Rsa.bytesAt (searchMem W) 0x3000 128 = Spec.Rsa.bytesAt keySat.mem 0x3000 128 := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  unfold searchMem
  apply ite_eq_right
  have small : ∀ i < 128, ¬ ((0x3000 : Addr) + BitVec.ofNat 64 i - 0x100000).toNat < 17744 := by decide
  exact small i (List.mem_range.mp hi)

private theorem searchSat_control (W : List (BitVec 64)) {a : Addr}
    (ha : a ∈ [0x4000, 0x4008, 0x4010]) :
    (searchMem W).readW a 64 = keySat.mem.readW a 64 := by
  apply Mem.readW_congr
  intro j hj
  unfold searchMem
  apply ite_eq_right
  have small : ∀ a : Addr, a ∈ [0x4000, 0x4008, 0x4010] → ∀ j < 8,
      ¬ (a + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small a ha j hj

private theorem vetted_satAux (W : List (BitVec 64)) (length : W.length = 2218) :
    ∃ s, (GenerationPolicy.vetted.searchContract (abi.withConsts [(VG.Impl.Ffdh.Arm.VettedGroups.tableSym, W)]) (stackUse .vetted)).pre s := by
  rw [GenerationPolicy.searchContract_vetted]
  unfold GenerationPolicy.legacySearchContract
  refine ⟨searchSat W, pre_consts.mpr ⟨?_, ?_⟩⟩
  · have args (i : Nat) (hi : i < 9) := searchSat_arg W hi
    sig_pre [GenerationPolicy.legacySearchContract, keySearchSig, pLenValid, domainLenValid,
      abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat),
      stackArg (stripConsts K s) i = stackArg s i by intros; rfl]
    simp only [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide),
      args 4 (by decide), args 5 (by decide), args 6 (by decide), args 7 (by decide), args 8 (by decide)]
    have v0 : stackArg keySat 0 = 0x5000 := by decide
    have v1 : stackArg keySat 1 = 0x3000 := by decide
    have v2 : stackArg keySat 2 = 128 := by decide
    have v3 : stackArg keySat 3 = 64 := by decide
    have v4 : stackArg keySat 4 = 0x7000 := by decide
    have v5 : stackArg keySat 5 = 0 := by decide
    have v6 : stackArg keySat 6 = 0x9000 := by decide
    have v7 : stackArg keySat 7 = 1056 := by decide
    have v8 : stackArg keySat 8 = 0x4000 := by decide
    rw [v0, v1, v2, v3, v4, v5, v6, v7, v8]
    dsimp only [stackArgAddr, stripConsts, State.withRegions, searchSat, keySat]
    repeat' apply And.intro
    -- the last four facts are about the memory: each by its own lemma, not by trying the others' first
    rotate_right 4
    · change domainValid 64 (Spec.Rsa.bytesAt (searchMem W) 0x3000 128) = true
      rw [searchSat_domain W]
      decide +kernel
    · change ((searchMem W).readW 0x4000 64).toNat ≤ 128
      rw [searchSat_control W (by decide)]
      decide +kernel
    · change ((searchMem W).readW 0x4008 64).toNat ≤ 128
      rw [searchSat_control W (by decide)]
      decide +kernel
    · change (searchMem W).readW 0x4010 64 = 64
      rw [searchSat_control W (by decide)]
      decide +kernel
    all_goals first
      | rfl
      | decide +kernel
      | (apply Region.disjoint_of_sep; decide +kernel)
  · refine ⟨?_, ?_, ?_, fun r hr => by
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      dsimp only [symAddr, searchSat]
      decide⟩
    · simp only [searchSat, keySat, constRegs, Abi.constRegions, symAddr, List.map_cons, List.map_nil, length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact searchMem_held W length i hi
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      rw [length]
      dsimp only [symAddr, searchSat]
      refine ⟨by decide, ?_, ?_⟩
      · intro q hq
        change q ∈ ([⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x4000, 128⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        all_goals apply Region.disjoint_of_sep; decide
      · intro q hq
        simp only [abi, stackBelow, stackUse, GenerationPolicy.searchStack, List.mem_singleton] at hq
        subst q
        exact Region.disjoint_of_sep (by decide)

private def cachedSearchBase : State :=
  { keySat with
    mem := fun a => if a=0x8026 then 0x10 else if a=0x8028 then 0x13
      else if a=0x8029 then 1 else keySat.mem a
    rd := [⟨0x3000,128⟩,⟨0x7000,0⟩,⟨0x100000,2200⟩,⟨0x8000,44⟩] }

private def cachedSearchSat : State :=
  {cachedSearchBase with mem := CachedSat.withContext cachedSearchBase.mem}

private theorem cachedSearch_arg (i : Nat) (hi : i<11) :
    stackArg cachedSearchSat i=stackArg cachedSearchBase i := by
  apply CachedSat.readW_outside
  have small : ∀ i<11, (stackArgAddr cachedSearchBase i).toNat+4≤0x100000 := by decide
  exact small i hi

private theorem cachedSearch_domain :
    Spec.Rsa.bytesAt cachedSearchSat.mem 0x3000 128=CachedSat.domain := by
  rw [show cachedSearchSat.mem=CachedSat.withContext cachedSearchBase.mem from rfl,CachedSat.domain_unchanged]
  unfold CachedSat.domain
  decide +kernel

private theorem cachedSearch_control {a : Addr} (ha : a ∈ [0x4000,0x4008,0x4010]) :
    cachedSearchSat.mem.readW a 64=cachedSearchBase.mem.readW a 64 := by
  apply CachedSat.readW_outside
  have small : ∀ a : Addr, a ∈ [0x4000,0x4008,0x4010] → a.toNat+8≤0x100000 := by decide
  exact small a ha

theorem cached_sat : ∃ s, (GenerationPolicy.cached.searchContract abi (stackUse .cached)).pre s := by
  refine ⟨cachedSearchSat,?_⟩
  sig_pre [GenerationPolicy.searchContract,cachedKeySearchContract,cachedKeySearchSig,keySearchSig,
    pLenValid,domainLenValid,abi,argRegs,reduceClassify,Loc.val,State.addr]
  simp only [cachedSearch_arg 0 (by decide),cachedSearch_arg 1 (by decide),cachedSearch_arg 2 (by decide),cachedSearch_arg 3 (by decide),cachedSearch_arg 4 (by decide),cachedSearch_arg 5 (by decide),cachedSearch_arg 6 (by decide),cachedSearch_arg 7 (by decide),cachedSearch_arg 8 (by decide),cachedSearch_arg 9 (by decide),cachedSearch_arg 10 (by decide)]
  have a0 : stackArg cachedSearchBase 0=0x5000 := by decide
  have a1 : stackArg cachedSearchBase 1=0x3000 := by decide
  have a2 : stackArg cachedSearchBase 2=128 := by decide
  have a3 : stackArg cachedSearchBase 3=64 := by decide
  have a4 : stackArg cachedSearchBase 4=0x7000 := by decide
  have a5 : stackArg cachedSearchBase 5=0 := by decide
  have a6 : stackArg cachedSearchBase 6=0x9000 := by decide
  have a7 : stackArg cachedSearchBase 7=1056 := by decide
  have a8 : stackArg cachedSearchBase 8=0x4000 := by decide
  have a9 : stackArg cachedSearchBase 9=0x100000 := by decide
  have a10 : stackArg cachedSearchBase 10=275 := by decide
  rw [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10]
  dsimp only [cachedSearchSat,cachedSearchBase,keySat]
  repeat' apply And.intro
  -- the last six facts are about the memory: each by its own lemma, not by trying the others' first
  rotate_right 6
  · change domainValid 64 (Spec.Rsa.bytesAt cachedSearchSat.mem 0x3000 128)=true
    rw [cachedSearch_domain]; exact CachedSat.domain_valid
  · change (cachedSearchSat.mem.readW 0x4000 64).toNat≤128
    rw [cachedSearch_control (by decide)]; decide +kernel
  · change (cachedSearchSat.mem.readW 0x4008 64).toNat≤128
    rw [cachedSearch_control (by decide)]; decide +kernel
  · change cachedSearchSat.mem.readW 0x4010 64=64
    rw [cachedSearch_control (by decide)]; decide +kernel
  · decide +kernel
  · change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt cachedSearchSat.mem 0x3000 128) =
      some (Spec.Rsa.wordsAt cachedSearchSat.mem 0x100000 275)
    rw [cachedSearch_domain]; exact (CachedSat.canonical _).2
  all_goals first
    | decide +kernel
    | (apply Region.disjoint_of_sep; decide +kernel)

theorem sat : ∃ s, (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre s := by
  cases sampling with
  | full => exact plain_sat
  | vetted => exact vetted_satAux _ VettedGroups.tableWords_length
  | cached => exact cached_sat

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CTLoop`, which only this module used -/

section

/-! The native bounded loop's trace is determined by public descriptor,
retry sampling and disclosed attempt-status sequence. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

theorem iteration_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeyCTL (sampling := sampling))) ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey))
      (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.iterationFor
  refine RelCT.seq (two_piece [.r4] key_ctl_pins (by taint_decide) keys_ready) ?_
  exact RelCT.seq (two_post (branch_ct backend) (branch_ready backend))
    (two_taint [.r4] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_pointer h₁).trans (branch_pointer h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint sampling) (s : State) : Prop :=
  if keyContinues q then isa.eval .eq s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval .eq s = some false

theorem ct_step (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (q : KeyPoint sampling) (s : State) (h : KeyCTL q s) :
    WP isa ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) s (KeyCTStep q) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.iterationFor
  refine WP.seq (WP.mono (keys_ready q s h) fun u ready => ?_)
  refine WP.seq (WP.mono (branch_ready backend q u ready) fun t result => ?_)
  by_cases continues : keyContinues q
  · simp only [KeyBranchResult, continues, ite_true] at result
    obtain ⟨⟨original, live, statuses⟩, word⟩ := result
    rw [← nextKeyPoint_inputs q] at word
    refine WP.mono (live.loop_guard word) ?_
    rintro t ⟨flag, state⟩
    simp only [KeyCTStep, continues, ite_true]
    exact ⟨flag, original, state, statuses⟩
  · simp only [KeyBranchResult, continues, ite_false] at result
    obtain ⟨_, _, finished⟩ := result
    refine WP.mono finished.loop_guard ?_
    rintro t ⟨flag, _⟩
    simp only [KeyCTStep, continues, ite_false]
    exact flag

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : KeyPoint sampling, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (n : Nat) :
    RelCT isa (LoopPair (sampling := sampling) n) ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) fun s t =>
      isa.eval .eq s = isa.eval .eq t ∧ (isa.eval .eq s = some false → True) ∧
        (isa.eval .eq s = some true → ∃ m < n, LoopPair (sampling := sampling) m s t) := by
  have wp (q : KeyPoint sampling) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) s fun t =>
        n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (ct_step backend q s h.2) (fun _ result => ⟨h.1, result⟩)
  have ct := two_post ((iteration_ct backend).mono
    (fun _ _ ⟨q, h₁, h₂, sp⟩ => ⟨q, h₁.2, h₂.2, sp⟩) (fun _ _ h => h)) wp
  refine ct.mono (fun _ _ ⟨q, measure, h₁, h₂, sp⟩ => ⟨q, ⟨measure, h₁⟩, ⟨measure, h₂⟩, sp⟩) ?_
  rintro s t ⟨q, ⟨measure, h₁⟩, ⟨_, h₂⟩, sp⟩
  by_cases continues : keyContinues q
  · simp only [KeyCTStep, continues, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2, sp⟩
    have := nextKeyPoint_measure continues
    omega_using [measure, this]
  · simp only [KeyCTStep, continues, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun again => absurd (again.symm.trans h₁) (by decide)⟩

theorem loop_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeyCTL (sampling := sampling)))
      (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v ⟨q, h₁, h₂, sp⟩ e₁ e₂
  exact RelCT.loop (M := isa)
    (body := (VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) (c := .eq)
    (Q := fun _ _ => True) LoopPair (iteration_pair backend) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, h₁, h₂, sp⟩ e₁ e₂

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.Correct`, which only this module used -/

section

/-! ### `Ffdh.Arm.KeySearch.Loop`, which this module and modules that import it used -/

section

/-! Total correctness of the bounded native FFDH key-search loop, composing
the chosen backend's key-generation attempt. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch

def KeyInvariant (p : KeyPublic sampling) (original : State) (expected : KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand p original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand p original) used keys scalars).used

theorem iteration (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (runAttempt : AttemptRunOk backend)
    {p : KeyPublic sampling} {original s : State} {expected : KeySearchResult} {n : Nat}
    (inv : KeyInvariant p original expected n s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext (.call backend.keyName backend.generateKey)) s fun t =>
      (isa.eval .eq t = some false ∧ KeyDone p original expected t) ∨
      (isa.eval .eq t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, measure, h, outcome, count⟩ := inv
  have length := h.rand_length
  have done : ∀ (result : KeySearchResult) t, KeyDone p original result t →
      result.outcome = (p.tail (keyRand p original) used keys scalars).outcome →
      result.used = (p.tail (keyRand p original) used keys scalars).used →
      WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)]) t fun t =>
        (isa.eval .eq t = some false ∧ KeyDone p original expected t) ∨
        (isa.eval .eq t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
    fun _ _ finished resultOutcome resultUsed => WP.mono finished.loop_guard fun _ ⟨flag, state⟩ =>
      Or.inl ⟨flag, state.congr (resultOutcome.trans outcome.symm) (resultUsed.trans count.symm)⟩
  unfold VG.Impl.Ffdh.Arm.KeySearch.iterationFor VG.Impl.Ffdh.Arm.KeySearch.branchFor
  refine WP.seq (WP.mono h.keys_guard fun u ⟨live1, flag1⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (keys = 0)) (by change some u.z = _; rw [flag1]) ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    refine WP.mono live1.exhausted fun t finished => done _ t finished ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inl zero'), exhaustedResult]
  intro nonzero
  have keysNonzero : keys ≠ 0 := of_decide_eq_false nonzero
  refine WP.seq (WP.mono live1.scalars_guard fun u ⟨live2, flag2⟩ => ?_)
  refine WP.ite (decide (scalars = 0)) (by change some u.z = _; rw [flag2]) ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    refine WP.mono live2.exhausted fun t finished => done _ t finished ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inr zero'), exhaustedResult]
  intro nonzero2
  have scalarsNonzero : scalars ≠ 0 := of_decide_eq_false nonzero2
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptOrRequestFor
  refine WP.seq (WP.mono live2.room_guard fun u ⟨live3, roomFlag⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [roomFlag]) ?_ ?_
  · intro short
    have short' : (keyRand p original).length - used < p.len := by
      rw [length]; exact of_decide_eq_true short
    refine WP.mono live3.request fun t finished => done _ t finished ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short keysNonzero scalarsNonzero short', requestResult]
  intro enough
  have room : used + p.len ≤ p.randLen := by
    have := of_decide_eq_false enough
    have := h.used_le
    omega_arith
  have room' : p.len ≤ (keyRand p original).length - used := by rw [length]; omega_using [room]
  refine WP.seq (WP.mono (runAttempt p original u used keys scalars live3 room) fun t ⟨live, post⟩ => ?_)
  refine WP.mono (classify live room (Nat.pos_of_ne_zero keysNonzero)
    (Nat.pos_of_ne_zero scalarsNonzero) post) fun q classified => ?_
  rcases currentStatus_cases p original used with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at classified
    refine done _ q classified ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_accepted keysNonzero scalarsNonzero room' h1, acceptedResult]
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at classified
    refine WP.mono (classified.1.loop_guard classified.2) fun z ⟨flag, state⟩ =>
      Or.inr ⟨flag, _, ?_, used + p.len, keys, scalars - 1, rfl, state, ?_, ?_⟩
    · omega_using [measure, scalarsNonzero]
    · rw [outcome]; simp only [KeyPublic.tail, keyTail_scalar keysNonzero scalarsNonzero room' h2]
    · rw [count]; simp only [KeyPublic.tail, keyTail_scalar keysNonzero scalarsNonzero room' h2]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at classified
    refine WP.mono (classified.1.loop_guard classified.2) fun z ⟨flag, state⟩ =>
      Or.inr ⟨flag, _, ?_, used + p.len, keys - 1, 128, rfl, state, ?_, ?_⟩
    · omega_using [measure, keysNonzero, scalarsNonzero]
    · rw [outcome]; simp only [KeyPublic.tail, keyTail_public keysNonzero scalarsNonzero room' h3]
    · rw [count]; simp only [KeyPublic.tail, keyTail_public keysNonzero scalarsNonzero room' h3]

theorem loop (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (runAttempt : AttemptRunOk backend)
    {p : KeyPublic sampling} {original s : State} {expected : KeySearchResult} {n : Nat}
    (inv : KeyInvariant p original expected n s) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext (.call backend.keyName backend.generateKey)) .eq)
      s (KeyDone p original expected) :=
  WP.loop (M := isa)
    (body := VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext (.call backend.keyName backend.generateKey)) (c := .eq)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => iteration backend runAttempt h) n s inv

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.Start`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.EntryBlocks`, which only this module used -/

section

/-! Loading the controller pointer and retaining the two output pointers;
finishing the native argument snapshot with a zero consumed-byte count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem entryHead_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0 = p.xp) (y : s.gpr .r2 = p.yp) :
    WP isa (.block [.ldrSp .r4 56, VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6]) s fun t =>
      (t.gpr .r4 = p.control ∧ t.mem = writeLow s.mem p.control [(5, p.xp), (6, p.yp)]) ∧ Rest [.r4] s t := by
  refine withRest_all [.r4] ?_ (by rfl) (by rfl)
  have arg := h.incoming 8 (by have := entryWords_min sampling; omega_using [this])
  have addr56 : State.addr (s.sp + 56#32) = off (State.addr s.sp) 56 :=
    VG.Arm.addr_add (by have := arg.fits; omega_using [this])
  have addr40 : State.addr (p.control + 40#32) = off (State.addr p.control) 40 :=
    VG.Arm.addr_add (by have := space.nowrap; omega_using [this])
  have addr48 : State.addr (p.control + 48#32) = off (State.addr p.control) 48 :=
    VG.Arm.addr_add (by have := space.nowrap; omega_using [this])
  unfold VG.Impl.Ffdh.Arm.KeySearch.stf writeLow
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [addr56, arg.readable, arg.word, incomingValue, addr40, addr48,
    space.write (off := 40) (by decide), space.write (off := 48) (by decide), x, y]

theorem entryZero_ok (s : State) {p : KeyPublic sampling} (h : EntryContext p s) :
    WP isa (.block [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 11]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) 88) (0#32) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.stf
  ffrun [h.controller.addr (by decide : 11 < 16), h.controller.write (by decide : 11 < 16)]
  rfl

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.PushedArguments`, which this module and modules that import it used -/

section

/-! The caller's nine ARM stack arguments are read above the saved search
frame and remain separate from the controller workspace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

theorem KeyInput.pushed_arguments {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    EntryArguments p (searchPushed s) := by
  have fit : stackUse sampling ≤ s.sp.toNat := by have := h.bounds.stackFits; rw [← h.2.1] at this; exact this
  have argsFit : s.sp.toNat + argsBytes sampling ≤ 2 ^ 32 := by have := h.bounds.argsFit; rw [← h.2.1] at this; exact this
  have size := entryWords_bytes sampling
  have bytesBound : argsBytes sampling≤44 := by cases sampling <;> decide
  have positive : 24 ≤ stackUse sampling := by have := stackUse_min sampling; omega_using [this]
  have native (i : Nat) (hi : i < entryWords sampling) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega_using [argsFit, size, hi])
  have start : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have wholeRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) (argsBytes sampling) := by
    refine ⟨inArgs sampling s, List.mem_append_left _ ?_, ?_⟩
    · rw [h.layout.rd]; simp [reads]
    · rw [inArgs, start]; exact Region.contains_self _ _
  have pushedFrame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by omega_using [fit, positive] : 24 ≤ s.sp.toNat)
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have savedSub : (FrameStack.belowA s.sp 24).Sub (FrameStack.belowA p.sp (stackUse sampling)) := by
    rw [rootSp]
    exact FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) fit
  have argsSaved : (inArgs sampling s).Disjoint (FrameStack.belowA s.sp 24) :=
    ((h.stack_separate (r := inArgs sampling s) (List.mem_append_right s.wr (by rw [h.layout.rd]; simp [reads]))).sub_left savedSub).symm
  have argsControl : (inArgs sampling s).Disjoint ⟨State.addr p.control, 128⟩ := by
    rw [← h.2.1]
    exact (h.layout.separate (inControl s) (by simp [writes]) (inArgs sampling s) (by simp [reads])).symm
  have offsetAddress (i : Nat) (hi : i < entryWords sampling) :
      off (State.addr (searchPushed s).sp) (24 + 4 * i) = stackArgAddr s i := by
    have room : (searchPushed s).sp.toNat + (24 + 4 * i) < 2 ^ 32 := by
      change (s.sp - 24#32).toNat + (24 + 4 * i) < 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega_using [fit, positive] : 24 ≤ s.sp.toNat)]
      omega_using [argsFit, size, bytesBound, hi]
    change State.addr (searchPushed s).sp + BitVec.ofNat 64 (24 + 4 * i) = _
    rw [← VG.Arm.addr_add room]
    change State.addr (s.sp - 24#32 + BitVec.ofNat 32 (24 + 4 * i)) = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  refine ⟨?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_, ?_⟩
    · change (s.sp - 24#32).toNat + (24 + 4 * i) + 4 ≤ 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega_using [fit, positive] : 24 ≤ s.sp.toNat)]
      omega_using [argsFit, size, bytesBound, hi]
    · rw [offsetAddress i hi, native i hi]
      obtain ⟨r, hr, contains⟩ := CallLay.inRegions_sub wholeRead (by omega_using [size, hi] : 4 * i + 4 ≤ argsBytes sampling) (by omega_using [argsFit])
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    · rw [offsetAddress i hi]
      have sub : (⟨stackArgAddr s i, 4⟩ : Region).Sub (inArgs sampling s) := by
        rw [native i hi, inArgs, start]
        exact Offset.sub_base _ (by omega_using [size, hi])
      have old := pushedFrame.readW (w := 32) (a := stackArgAddr s i) (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _)
        (by simpa using argsSaved.sub_left sub) (by decide)
      exact old.trans (h.incoming_value hi)
  · intro i hi
    rw [offsetAddress i hi]
    apply argsControl.sub_left
    rw [native i hi, inArgs, start]
    exact Offset.sub_base _ (by omega_using [size, hi])

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.InitialWords`, which only this module used -/

section

/-! Exact native halves of the initialized retry counters and domain width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem KeyInput.initial_words {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.mem.readW (off (State.addr p.control) 0) 64 = BitVec.ofNat 64 p.keys ∧
    s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.scalars ∧
    s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 p.len := by
  have pre := h.1
  cases h.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq, off, BitVec.add_zero]
  · simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · cases sampling <;>
      sig_pre [GenerationPolicy.searchContract,GenerationPolicy.legacySearchContract,
        cachedKeySearchContract,cachedKeySearchSig,keySearchSig,abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
    all_goals simp only [KeyConstants.stackArg_stripConsts,KeyConstants.stackArgAddr_stripConsts] at pre
    all_goals sig_split pre
    all_goals
      have value : s.mem.readW (BitVec.setWidth 64 (stackArg s 8)+(16 : BitVec 64)) 64 = BitVec.ofNat 64 (stackArg s 3).toNat := by assumption
      simpa only [keyOfState,off,State.addr,BitVec.ofNat_toNat,show (16 : BitVec 64)=16#64 from rfl] using value

theorem KeyInput.pushed_word {p : KeyPublic sampling} {s : State} {j : Nat} (h : KeyInput p s) (bound : j < 3) :
    (searchPushed s).mem.readW (off (State.addr p.control) (8 * j)) 64 =
      s.mem.readW (off (State.addr p.control) (8 * j)) 64 := by
  have fit : stackUse sampling ≤ p.sp.toNat := h.bounds.stackFits
  have rootFit : 24 ≤ s.sp.toNat := by rw [← h.2.1] at fit; change stackUse sampling ≤ s.sp.toNat at fit; have := stackUse_min sampling; omega_using [fit, this]
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) rootFit
  have sep : (rControl p).Disjoint (FrameStack.belowA s.sp 24) := by
    have base : p.sp = s.sp := by rw [← h.2.1]; rfl
    rw [← base]
    exact h.saved_control.symm
  exact frame.readW (r := rControl p) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
    (by simpa using sep) (by decide)

theorem KeyInput.pushed_policy {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    lowWord (searchPushed s).mem p.control 0 = BitVec.ofNat 32 p.keys ∧
    lowWord (searchPushed s).mem p.control 1 = BitVec.ofNat 32 p.scalars ∧
    lowWord (searchPushed s).mem p.control 2 = BitVec.ofNat 32 p.len ∧
    (∀ j < 3, (searchPushed s).mem.readW (off (State.addr p.control) (8 * j + 4)) 32 = 0) := by
  have w0 := (h.pushed_word (j := 0) (by decide)).trans h.initial_words.1
  have w1 := (h.pushed_word (j := 1) (by decide)).trans h.initial_words.2.1
  have w2 := (h.pushed_word (j := 2) (by decide)).trans h.initial_words.2.2
  have keys : p.keys < 2 ^ 32 := by have := h.bounds.keys; omega_using [this]
  have scalars : p.scalars < 2 ^ 32 := by have := h.bounds.scalars; omega_using [this]
  have len : p.len < 2 ^ 32 := by have := h.bounds.maxLength; omega_using [this]
  refine ⟨packed_low _ _ _ _ keys w0, packed_low _ _ _ _ scalars w1, packed_low _ _ _ _ len w2, ?_⟩
  intro j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases casesJ with rfl | rfl | rfl
  · exact packed_high _ _ _ _ keys w0
  · exact packed_high _ _ _ _ scalars w1
  · exact packed_high _ _ _ _ len w2

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.Entry`, which only this module used -/

section

/-! Exact argument snapshot made before entering the key-search loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryValues (p : KeyPublic sampling) : List (Nat × BitVec 32) :=
  [(5, p.xp), (6, p.yp), (15, p.up), (7, p.dp), (8, BitVec.ofNat 32 p.dlen),
    (9, p.rp), (10, BitVec.ofNat 32 p.randLen), (12, p.scratch),
    (13, BitVec.ofNat 32 p.capacity), (11, 0)]

theorem entryValues_bound (p : KeyPublic sampling) : ∀ e ∈ entryValues p, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem entry_base_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0 = p.xp) (y : s.gpr .r2 = p.yp) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.entry) s fun t =>
      (EntryContext p t ∧ t.mem = writeLow s.mem p.control (entryValues p)) ∧ Rest [.r3, .r4] s t := by
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  change WP isa (.block ([.ldrSp .r4 56, VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
    VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (entryHead_ok s h space x y) ?_
  rintro u ⟨⟨pointer, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem u.mem := by
    rw [mem]; exact writeLow_frame _ _ _ (by simp)
  have context : EntryContext p u :=
    ⟨h.after rest frame, ⟨space.congr rest.wr, pointer⟩⟩
  refine wp_entryCopy (i := 0) (j := 15) context (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s1 c1 m1 _ => ?_
  refine wp_entryCopy (i := 1) (j := 7) c1 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s2 c2 m2 _ => ?_
  refine wp_entryCopy (i := 2) (j := 8) c2 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s3 c3 m3 _ => ?_
  refine wp_entryCopy (i := 4) (j := 9) c3 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s4 c4 m4 _ => ?_
  refine wp_entryCopy (i := 5) (j := 10) c4 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s5 c5 m5 _ => ?_
  refine wp_entryCopy (i := 6) (j := 12) c5 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s6 c6 m6 _ => ?_
  refine wp_entryCopy (i := 7) (j := 13) c6 (by have := entryWords_min sampling; omega_using [this]) (by decide) fun s7 c7 m7 _ => ?_
  refine WP.mono (entryZero_ok s7 c7) ?_
  rintro t ⟨m8, r8⟩
  have frame8 : Frame [⟨State.addr p.control, 128⟩] s7.mem t.mem := by
    rw [m8]
    exact (Frame.refl _ _).writeW (r := ⟨State.addr p.control, 128⟩) (by simp) (0#32)
      (Offset.contains_base _ (by decide : 88 + 4 ≤ 128) (by decide))
  refine ⟨c7.after r8 (by simp) frame8, ?_⟩
  rw [m8, m7, m6, m5, m4, m3, m2, m1, mem]
  rfl

theorem entry_fields (p : KeyPublic sampling) (m : Mem)
    (keys : lowWord m p.control 0 = BitVec.ofNat 32 p.keys)
    (scalars : lowWord m p.control 1 = BitVec.ofNat 32 p.scalars)
    (width : lowWord m p.control 2 = BitVec.ofNat 32 p.len) :
    Slots (writeLow m p.control (entryValues p)) p.control (p.headers 0 p.keys p.scalars) := by
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (entryValues_bound p) j (headerIndices_bound hj)]
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entryValues, lowValue, KeyPublic.field, keys, scalars, width]

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.EntryCache`, which only this module used -/

section

/-! Retain the appended readonly context pointer and word count in state word four. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryCacheMem (p : KeyPublic sampling) (m : Mem) : Mem :=
  (m.writeW (off (State.addr p.control) 32) p.context).writeW
    (off (State.addr p.control) 36) (BitVec.ofNat 32 p.contextWords)

theorem entryCache_frame (p : KeyPublic sampling) (m : Mem) :
    Frame [⟨State.addr p.control,128⟩] m (entryCacheMem p m) := by
  unfold entryCacheMem
  apply Frame.writeW
  · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide : 32+4≤128) (by decide))
  · exact List.mem_cons_self
  · exact Offset.contains_base _ (by decide : 36+4≤128) (by decide)

theorem entryCache_ok (s : State) {p : KeyPublic sampling} (h : EntryContext p s)
    (cached : sampling.cachedContext=true) :
    WP isa (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) s fun t =>
      (EntryContext p t ∧ t.mem=entryCacheMem p s.mem) ∧ Rest [.r3] s t := by
  have a9 := h.incoming 9 (by simp only [entryWords,cached,ite_true]; decide)
  have a10 := h.incoming 10 (by simp only [entryWords,cached,ite_true]; decide)
  have a60 : State.addr (s.sp+BitVec.ofNat 32 60)=off (State.addr s.sp) 60 := addr_add (by have := a9.fits; omega_using [this])
  have a64 : State.addr (s.sp+BitVec.ofNat 32 64)=off (State.addr s.sp) 64 := addr_add (by have := a10.fits; omega_using [this])
  have d32 : State.addr (p.control+BitVec.ofNat 32 32)=off (State.addr p.control) 32 := addr_add (by have := h.controller.space.nowrap; omega_using [this])
  have d36 : State.addr (p.control+BitVec.ofNat 32 36)=off (State.addr p.control) 36 := addr_add (by have := h.controller.space.nowrap; omega_using [this])
  have raw : WP isa (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) s fun t =>
      t.mem=entryCacheMem p s.mem ∧ Rest [.r3] s t := by
    refine withRest_all [.r3] ?_ (by rfl) rfl
    have kept : s.mem.readW (off (State.addr s.sp) 64) 32 =
        (s.mem.writeW (off (State.addr p.control) 32) p.context).readW (off (State.addr s.sp) 64) 32 := by
      symm
      exact Mem.readW_writeW_sep
        ((h.separate 10 (by rw [entryWords,cached]; decide)).sep
          (Region.contains_self _ _) (Offset.contains_base _ (by decide : 32+4≤128) (by decide))) (by decide)
    unfold entryCacheMem
    ffrun [a60,a64,d32,d36,h.controller.ptr,a9.readable,a9.word,a10.readable,a10.word,
      incomingValue,h.controller.space.write (off:=32) (by decide),
      h.controller.space.write (off:=36) (by decide),←kept]
  refine WP.mono raw ?_
  rintro t ⟨mem,rest⟩
  have frame : Frame [⟨State.addr p.control,128⟩] s.mem t.mem := by rw [mem]; exact entryCache_frame p s.mem
  exact ⟨⟨h.after rest (by simp) frame,mem⟩,rest⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The native entry code establishes the complete key-search loop invariant. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/EntryFor.lean`, which only this module imported.
section

/-! The same entry snapshot optionally retains the two cached-context arguments. -/

section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryMem (p : KeyPublic sampling) (m : Mem) : Mem :=
  if sampling.cachedContext then entryCacheMem p (writeLow m p.control (entryValues p))
  else writeLow m p.control (entryValues p)

theorem entryMem_frame (p : KeyPublic sampling) (m : Mem) :
    Frame [⟨State.addr p.control,128⟩] m (entryMem p m) := by
  unfold entryMem
  split
  · exact (writeLow_frame _ _ _ (entryValues_bound p)).trans (entryCache_frame _ _)
  · exact writeLow_frame _ _ _ (entryValues_bound p)

theorem entry_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0=p.xp) (y : s.gpr .r2=p.yp) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) s fun t =>
      (EntryContext p t ∧ t.mem=entryMem p s.mem) ∧ Rest [.r3,.r4] s t := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.entryFor,WP.block_append_iff]
  refine WP.mono (entry_base_ok s h space x y) ?_
  rintro u ⟨⟨context,mem⟩,rest⟩
  by_cases cached : sampling.cachedContext=true
  · simp only [cached,ite_true]
    refine WP.mono (entryCache_ok u context cached) ?_
    rintro t ⟨⟨ct,memT⟩,restT⟩
    refine ⟨⟨ct,?_⟩,rest.trans (restT.mono (by simp))⟩
    rw [memT,mem,entryMem,ite_eq_left cached]
  · simp only [cached]
    exact WP.block_nil ⟨⟨context,by rw [entryMem,ite_eq_right cached]; exact mem⟩,rest⟩

theorem entryCache_read (p : KeyPublic sampling) (m : Mem) {d : Nat}
    (bound : d+4≤128) (sep : d+4≤32 ∨ 40≤d) :
    (entryCacheMem p m).readW (off (State.addr p.control) d) 32 =
      m.readW (off (State.addr p.control) d) 32 := by
  unfold entryCacheMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

theorem entryMem_fields (p : KeyPublic sampling) (m : Mem)
    (keys : lowWord m p.control 0=BitVec.ofNat 32 p.keys)
    (scalars : lowWord m p.control 1=BitVec.ofNat 32 p.scalars)
    (width : lowWord m p.control 2=BitVec.ofNat 32 p.len) :
    Slots (entryMem p m) p.control (p.headers 0 p.keys p.scalars) := by
  have old := entry_fields p m keys scalars width
  unfold entryMem
  split
  · apply (slots_fields _ _ _ _ _ _).mpr
    intro j hj
    change (entryCacheMem p _).readW _ 32 = _
    rw [entryCache_read _ _ (by have := headerIndices_bound hj; omega) (by
      simp only [headerIndices,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact (slots_fields _ _ _ _ _ _).mp old j hj
  · exact old

theorem entryMem_high (p : KeyPublic sampling) (m : Mem) {j : Nat} (hj : j<3) :
    (entryMem p m).readW (off (State.addr p.control) (8*j+4)) 32 =
      m.readW (off (State.addr p.control) (8*j+4)) 32 := by
  unfold entryMem
  split
  · rw [entryCache_read _ _ (by omega) (by omega)]
    exact highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)
  · exact highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)

theorem entryMem_cached (p : KeyPublic sampling) (m : Mem) : CachedSlots p (entryMem p m) := by
  intro cached
  rw [entryMem,ite_eq_left cached]
  unfold entryCacheMem
  constructor
  · rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact Mem.readW_writeW_self32 _ _ _

end VG.Proof.Ffdh.Arm.KeySearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem KeyInput.pushed_read {p : KeyPublic sampling} {s : State} {r : Region}
    (h : KeyInput p s) (read : r ∈ s.rd) :
    Spec.Rsa.bytesAt (searchPushed s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := by
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have fit : stackUse sampling ≤ s.sp.toNat := by rw [← rootSp]; exact h.bounds.stackFits
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := stackUse_min sampling; omega_using [fit, this])
  have sep : r.Disjoint (FrameStack.belowA s.sp 24) := by
    apply Region.Disjoint.symm
    apply (h.stack_separate (List.mem_append_right _ read)).sub_left
    rw [rootSp]
    exact FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) fit
  apply bytesAt_frame frame (by simpa using sep)
  have nowrap := h.layout.nowrap r (by rw [← h.layout.wr, ← h.layout.rd]; exact List.mem_append_right _ read)
  omega_using [nowrap]

theorem start_ok {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) (searchPushed s) fun t =>
      KeyLive p s 0 p.keys p.scalars t := by
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have fit : 24 ≤ s.sp.toNat := by rw [← rootSp]; have := h.bounds.stackFits; have := stackUse_min sampling; omega_arith
  have space : Workspace (searchPushed s) p.control 128 :=
    h.control_space (fun _ hr => List.mem_cons_of_mem _ hr)
  have x : (searchPushed s).gpr .r0 = p.xp := by rw [← h.2.1]; rfl
  have y : (searchPushed s).gpr .r2 = p.yp := by rw [← h.2.1]; rfl
  refine WP.mono_syms (entry_ok (searchPushed s) h.pushed_arguments space x y) ?_
  rintro t ⟨⟨context, mem⟩, rest⟩ syms
  have frame : Frame [rControl p] (searchPushed s).mem t.mem := by
    rw [mem]; exact entryMem_frame _ _
  have saved : Spill.Saved (searchPushed s).mem (State.addr (p.sp - 24#32)) s.gpr savedSlots := by
    rw [rootSp]; exact push_saved s fit
  refine ⟨h, Nat.zero_le _, h.bounds.keys, h.bounds.scalars, rest.rd, ?_, ?_, context.controller.ptr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr]
    change (⟨State.addr (s.sp - 24#32), 24⟩ :: s.wr) = _
    rw [rootSp]
  · rw [rest.sp]
    change s.sp - 24#32 = p.sp - 24#32
    rw [rootSp]
  · intro r hr
    exact rest.gpr r (by revert r hr; decide)
  · apply saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.saved_control
  · exact (bytesAt_frame (r := rRandom p) frame (by simpa using h.random_control)
      (by change p.randLen ≤ 2 ^ 64; have := h.bounds.randomFits; omega_using [this])).trans
        (h.pushed_read (r := rRandom p) (by rw [h.read_regions]; simp))
  · have original : Spec.Rsa.bytesAt s.mem (State.addr p.dp) p.dlen = p.dom := by rw [← h.2.1]; rfl
    exact (bytesAt_frame (r := rDomain p) frame (by simpa using h.domain_control)
      (by change p.dlen ≤ 2 ^ 64; have := h.bounds.domainFit; omega_using [this])).trans
        ((h.pushed_read (r := rDomain p) (by rw [h.read_regions]; simp)).trans original)
  · rw [mem]
    exact entryMem_fields p _ h.pushed_policy.1 h.pushed_policy.2.1 h.pushed_policy.2.2.1
  · intro j hj
    rw [mem, entryMem_high _ _ hj]
    exact h.pushed_policy.2.2.2 j hj

  · have ptrS : KeyConstants.tablePtr sampling s = p.tablePtr := by rw [← h.2.1]; rfl
    cases sampling <;> simpa only [KeyConstants.tablePtr, syms, searchPushed, pushed] using ptrS
  · have ptrS : KeyConstants.tablePtr sampling s = p.tablePtr := by rw [← h.2.1]; rfl
    have heldS := KeyConstants.held_of_consts h.2.2
    rw [ptrS] at heldS
    have pushedFrame : Frame [FrameStack.belowA p.sp 24] s.mem (searchPushed s).mem := by
      rw [rootSp]
      exact FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) fit
    have heldP := KeyConstants.held_after_frame heldS pushedFrame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact (h.constants_stack table ht).sub_right (FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) h.bounds.stackFits))
    exact KeyConstants.held_after_frame heldP frame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact h.constants_control table ht)

  · have pushedFrame : Frame [FrameStack.belowA p.sp 24] s.mem (searchPushed s).mem := by
      rw [rootSp]
      exact FrameStack.pushed_frameA (rs := [.r4,.r9,.r10,.r11,.r12,.lr]) fit
    have heldP := h.cached_held.after_frame pushedFrame
      (fun cached => by have := h.context_fit cached; omega_using [this]) (by
        intro cached r hr
        have eq := List.mem_singleton.mp hr
        subst r
        have member : rContext p ∈ s.rd := by rw [h.read_regions]; simp [contextRegions,cached]
        exact (h.stack_separate (List.mem_append_right s.wr member)).symm.sub_right
          (FrameStack.belowA_sub (by have := stackUse_min sampling; omega_using [this]) h.bounds.stackFits))
    exact heldP.after_frame frame (fun cached => by have := h.context_fit cached; omega_using [this]) (by
      intro cached r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact h.context_control cached)
  · rw [mem]
    exact entryMem_cached p _

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The full native ARMv7 key search satisfies the shared result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch

def searchResult (p : KeyPublic sampling) (s : State) : KeySearchResult :=
  sampling.search p.a p.len ⟨p.keys, p.scalars⟩ (keyRand p s)

theorem function_ok (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) {p : KeyPublic sampling} {s : State}
    (h : KeyInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey)) s fun t =>
      abiPreserved s t ∧ ResultPost p (searchResult p s) t := by
  have fit : 24 ≤ s.sp.toNat := by
    have fits := h.bounds.stackFits
    rw [← h.2.1] at fits
    change stackUse sampling ≤ s.sp.toNat at fits
    have min := stackUse_min sampling
    omega_using [fits, min]
  unfold VG.Impl.Ffdh.Arm.KeySearch.codeFor
  refine WP.frame (by decide) fit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (start_ok h) ?_
  intro u live
  rw [WP.seq_iff]
  have inv : KeyInvariant p s (searchResult p s) (128 * p.keys + p.scalars + 1) u := by
    refine ⟨0, p.keys, p.scalars, rfl, live, ?_, ?_⟩
    all_goals simp only [searchResult, KeyPublic.tail, keyTail, after, List.drop_zero, Nat.zero_add]
  refine WP.mono (loop backend (attemptRun_ok backend) inv) ?_
  intro t finished
  exact finish_ok finished

theorem correct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (s : State)
    (pre : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey)) s tr t ∧
      abiPreserved s t ∧ (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).post s t := by
  let p := keyOfState sampling s
  have parts := selected_pre.mp pre
  have input : KeyInput p s := ⟨parts.1, rfl, parts.2⟩
  obtain ⟨tr, t, run, abiOk, result⟩ := function_ok backend input
  refine ⟨tr, t, run, abiOk, ?_⟩
  apply selected_post.mpr
  have statusFits : (searchResult p s).status < 2 ^ 32 := by
    cases outcome : (searchResult p s).outcome <;> simp [KeySearchResult.status, outcome]
  cases sampling <;>
    sig_post [GenerationPolicy.searchContract, GenerationPolicy.legacySearchContract,
      cachedKeySearchContract, cachedKeySearchSig, keySearchSig, abi, argRegs,
      reduceClassify, Loc.val, State.addr]
  all_goals
    rw [BitVec.setWidth_append_eq_right]
    change (t.gpr .r0).toNat = (searchResult p s).status ∧
      KeyOutput p (searchResult p s) t.mem ∧
      Spec.Rsa.wordsAt t.mem (State.addr p.control) 4 =
        [BitVec.ofNat 64 (searchResult p s).retries.keys, BitVec.ofNat 64 (searchResult p s).retries.scalars,
          BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if (searchResult p s).status = 0 then p.len else 0)] ∧
      Spec.Rsa.wordsAt t.mem (State.addr p.up) 1 = [BitVec.ofNat 64 (searchResult p s).used]
    refine ⟨?_, result.output, result.policy, result.used⟩
    rw [result.status, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusFits]

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.Public`, which only this module used -/

section

/-! The shared search leakage sampling fixes precisely the public descriptor
and the remaining attempt-status sequence used by the native timing proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

private theorem recover {w : Nat} {a b : List (BitVec w)}
    (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
  have values := congrArg (List.map (BitVec.ofNat w)) h
  simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] using values

private theorem public_inputs_of_args {s t : State}
    (preS : KeyInput (keyOfState sampling s) s)
    (preT : KeyInput (keyOfState sampling t) t)
    (sp : s.sp = t.sp)
    (leak : (keyOfState sampling s).dom.map BitVec.toNat ++
      (Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) 4).map BitVec.toNat ++
      (searchResult (keyOfState sampling s) s).statuses =
      (keyOfState sampling t).dom.map BitVec.toNat ++
      (Spec.Rsa.wordsAt t.mem (State.addr (stackArg t 8)) 4).map BitVec.toNat ++
      (searchResult (keyOfState sampling t) t).statuses)
    (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (p4 : stackArg s 0 = stackArg t 0) (p5 : stackArg s 1 = stackArg t 1)
    (p6 : stackArg s 2 = stackArg t 2) (p7 : stackArg s 3 = stackArg t 3)
    (p8 : stackArg s 4 = stackArg t 4) (p9 : stackArg s 5 = stackArg t 5)
    (p10 : stackArg s 6 = stackArg t 6) (p11 : stackArg s 7 = stackArg t 7)
    (p12 : stackArg s 8 = stackArg t 8)
    (table : KeyConstants.tablePtr sampling s = KeyConstants.tablePtr sampling t)
    (ctx : sampling.cachedContext = true → stackArg s 9 = stackArg t 9 ∧ stackArg s 10 = stackArg t 10) :
    ∃ p : KeyPublic sampling, KeyInput p s ∧ KeyInput p t ∧
      (searchResult p s).statuses = (searchResult p t).statuses ∧ s.sp = t.sp := by
  simp only [List.append_assoc] at leak
  have domainSize : ((keyOfState sampling s).dom.map BitVec.toNat).length = ((keyOfState sampling t).dom.map BitVec.toNat).length := by
    simp only [List.length_map, keyOfState, VG.Proof.Bignum.bytesAt_length]
    rw [p6]
  obtain ⟨domainNat, rest⟩ := List.append_inj leak domainSize
  have policySize : ((Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) 4).map BitVec.toNat).length =
      ((Spec.Rsa.wordsAt t.mem (State.addr (stackArg t 8)) 4).map BitVec.toNat).length := by
    simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range]
  obtain ⟨policyNat, statuses⟩ := List.append_inj rest policySize
  have domain := recover domainNat
  have keys := congrArg (fun xs : List Nat => xs[0]!) policyNat
  have scalars := congrArg (fun xs : List Nat => xs[1]!) policyNat
  have ks : (keyOfState sampling s).keys = (keyOfState sampling t).keys := by
    simpa only [keyOfState, Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.getElem!_cons_zero, Nat.mul_zero, BitVec.add_zero] using keys
  have cs : (keyOfState sampling s).scalars = (keyOfState sampling t).scalars := by
    simpa only [keyOfState, Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.getElem!_cons_succ, List.getElem!_cons_zero] using scalars
  have point : keyOfState sampling s = keyOfState sampling t := by
    unfold keyOfState
    rw [KeyPublic.mk.injEq]
    refine ⟨p0, p2, p4, p5, p8, p10, p12, sp, congrArg BitVec.toNat p7,
      congrArg BitVec.toNat p6, congrArg BitVec.toNat p9, congrArg BitVec.toNat p11, ks, cs, domain, table, ?_, ?_⟩
    · by_cases active : sampling.cachedContext = true
      · simp only [active, ite_true]; exact (ctx active).1
      · simp only [active, Bool.false_eq_true, ite_false]
    · by_cases active : sampling.cachedContext = true
      · simp only [active, ite_true]; exact congrArg BitVec.toNat (ctx active).2
      · simp only [active, Bool.false_eq_true, ite_false]
  refine ⟨keyOfState sampling s, preS, ⟨preT.1, point.symm, preT.2.2⟩, ?_, sp⟩
  simpa only [← point] using statuses


theorem public_inputs {s t : State} (hs : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre s)
    (ht : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre t) (pub : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pub s t) :
    ∃ p : KeyPublic sampling, KeyInput p s ∧ KeyInput p t ∧ (searchResult p s).statuses = (searchResult p t).statuses ∧ s.sp = t.sp := by
  have partsS := selected_pre.mp hs
  have partsT := selected_pre.mp ht
  have preS : KeyInput (keyOfState sampling s) s := ⟨partsS.1, rfl, partsS.2⟩
  have preT : KeyInput (keyOfState sampling t) t := ⟨partsT.1, rfl, partsT.2⟩
  obtain ⟨pub, table⟩ := selected_pub.mp pub
  cases sampling <;>
    sig_pub [GenerationPolicy.searchContract, GenerationPolicy.legacySearchContract,
      cachedKeySearchContract, cachedKeySearchSig, keySearchSig, abi, argRegs,
      reduceClassify, Loc.val, State.addr] at pub
  · obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := pub
    exact public_inputs_of_args preS preT sp leak p0 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 table (by intro h; cases h)
  · obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := pub
    exact public_inputs_of_args preS preT sp leak p0 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 table (by intro h; cases h)
  · obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14⟩ := pub
    exact public_inputs_of_args preS preT sp leak p0 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 table (fun _ => ⟨p13, p14⟩)

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! Complete native ARMv7 key generation, including bounded retries and
entropy refills, satisfies the shared correctness and timing contract. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/CTEntry.lean`, which only this module imported.
section

/-! The native entry has public stack/control addresses, even though it
saves arbitrary incoming register values in the outer frame. -/

section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.GenerationSearch

def KeyStart (a : KeyPublic sampling × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (searchResult a.1 s).statuses = a.2

def PushedStart (a : KeyPublic sampling × List Nat) (s : State) : Prop :=
  ∃ original, KeyStart a original ∧ s = searchPushed original

def EntryPointer (a : KeyPublic sampling × List Nat) (s : State) : Prop := s.gpr .r4 = a.1.control

private theorem entry_pointer (a : KeyPublic sampling × List Nat) (s : State) (h : PushedStart a s) :
    WP isa (.block [.ldrSp .r4 56]) s (EntryPointer a) := by
  obtain ⟨original, ⟨input, _⟩, rfl⟩ := h
  refine wp_load_incoming .r4 (input.pushed_arguments.incoming 8 (by cases sampling <;> decide)) (by decide)
    (fun t value _ _ => WP.block_nil ?_)
  simpa only [EntryPointer, incomingValue] using value

private def entryCopies : List (Nat × Nat) := [(24, 15), (28, 7), (32, 8), (40, 9), (44, 10), (48, 12), (52, 13)]

private theorem copies_ct (copies : List (Nat × Nat)) : RelCT isa ControlAddress
    (.block (copies.flatMap (fun e => [.ldrSp .r3 e.1, VG.Impl.Ffdh.Arm.KeySearch.stf .r3 e.2]))) ControlAddress := by
  induction copies with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons e rest ih => exact RelCT.block_append ((entryCopy_ct e.1 e.2).seq ih)

private theorem entry_tail_ct : RelCT isa ControlAddress
    (.block (VG.Impl.Ffdh.Arm.KeySearch.entry.drop 1)) ControlAddress := by
  have stores : RelCT isa ControlAddress (.block [VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6]) ControlAddress :=
    RelCT.block_append ((controlStore_ct .r0 40).seq (controlStore_ct .r2 48))
  change RelCT isa _ (.block (([VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6] ++
    entryCopies.flatMap (fun e => [.ldrSp .r3 e.1, VG.Impl.Ffdh.Arm.KeySearch.stf .r3 e.2])) ++
      [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 11])) _
  exact RelCT.block_append ((RelCT.block_append (stores.seq (copies_ct entryCopies))).seq entryZero_ct)

private theorem entry_plain_ct : RelCT isa (Two (PushedStart (sampling := sampling))) (.block VG.Impl.Ffdh.Arm.KeySearch.entry) ControlAddress := by
  have load : RelCT isa (Two (PushedStart (sampling := sampling))) (.block [.ldrSp .r4 56]) (fun _ _ => True) :=
    (loadStack_ct .r4 56).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  change RelCT isa _ (.block ([.ldrSp .r4 56] ++ VG.Impl.Ffdh.Arm.KeySearch.entry.drop 1)) _
  refine RelCT.block_append (RelCT.seq (two_post load entry_pointer) ?_)
  exact entry_tail_ct.mono (fun _ _ ⟨_, pointer₁, pointer₂, sp⟩ => ⟨pointer₁.trans pointer₂.symm, sp⟩)
    (fun _ _ h => h)

theorem entry_ct : RelCT isa (Two (PushedStart (sampling := sampling)))
    (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) (fun _ _ => True) := by
  have cached : RelCT isa ControlAddress
      (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) ControlAddress :=
    RelCT.block_append ((RelCT.block_append ((controlLoad_ct .r3 60 (by decide)).seq
      (controlStore_ct .r3 32))).seq (RelCT.block_append ((controlLoad_ct .r3 64 (by decide)).seq
      (controlStore_ct .r3 36))))
  unfold VG.Impl.Ffdh.Arm.KeySearch.entryFor
  cases flag : sampling.cachedContext
  · simpa only [Bool.false_eq_true,ite_false,List.append_nil] using
      (entry_plain_ct (sampling:=sampling)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact (RelCT.block_append ((entry_plain_ct (sampling:=sampling)).seq cached)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

def initialPoint (a : KeyPublic sampling × List Nat) : KeyPoint sampling := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩
def Entered (a : KeyPublic sampling × List Nat) (s : State) : Prop := KeyCTL (initialPoint a) s

theorem entry_ready (a : KeyPublic sampling × List Nat) (s : State) (h : PushedStart a s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) s (Entered a) := by
  obtain ⟨original, ⟨input, statuses⟩, rfl⟩ := h
  refine WP.mono (start_ok input) ?_
  intro t live
  refine ⟨original, live, ?_⟩
  simpa only [initialPoint, KeyPublic.tail, keyTail, after, List.drop_zero, searchResult] using statuses

end VG.Proof.Ffdh.Arm.KeySearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/CTFunction.lean`, which only this module imported.
section

/-! Native entry, bounded key search, result stores, and saved-register
frame compose without timing dependence beyond the disclosed search sampling. -/

section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

private theorem loop_ready (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (a : KeyPublic sampling × List Nat) (s : State)
    (h : Entered a s) :
    WP isa (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq)
      s (KeyCTDone a.1) := by
  obtain ⟨original, live, _⟩ := h
  refine WP.mono (loop backend (attemptRun_ok backend)
    (expected := a.1.tail (keyRand a.1 original) 0 a.1.keys a.1.scalars)
    (n := 128 * a.1.keys + a.1.scalars + 1) ?_) (fun _ result => ⟨original, _, result⟩)
  exact ⟨0, a.1.keys, a.1.scalars, rfl, live, rfl, rfl⟩

theorem body_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : RelCT isa (Two (PushedStart (sampling := sampling)))
    (.seq (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext))
      (.seq (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq)
        (.block VG.Impl.Ffdh.Arm.KeySearch.finish))) (fun _ _ => True) := by
  refine RelCT.seq (two_post entry_ct entry_ready) ?_
  have loopCT : RelCT isa (Two (Entered (sampling := sampling)))
      (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq) (fun _ _ => True) :=
    (loop_ct backend).mono (fun _ _ ⟨a, h₁, h₂, sp⟩ => ⟨initialPoint a, h₁, h₂, sp⟩) (fun _ _ h => h)
  refine RelCT.seq (two_post loopCT (loop_ready backend)) ?_
  exact finish_ct.mono (fun _ _ ⟨a, h₁, h₂, sp⟩ => ⟨a.1, h₁, h₂, sp⟩) (fun _ _ h => h)

private theorem push_search_eq {s t : State}
    (h : isa.push (.push [.r4, .r9, .r10, .r11, .r12, .lr]) s = some t) : t = searchPushed s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem function_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : RelCT isa (Two (KeyStart (sampling := sampling)))
    ((VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.codeFor
  refine RelCT.frame (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (body_ct backend).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨q, h₁, h₂, sp⟩, push₁, push₂⟩
  have first := push_search_eq push₁
  have second := push_search_eq push₂
  subst first second
  refine ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, ?_⟩
  change s.sp - 24#32 = t.sp - 24#32
  rw [sp]

end VG.Proof.Ffdh.Arm.KeySearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

theorem constantTime (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    ConstantTime isa (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pub
      (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey)) := by
  intro s t tr₁ tr₂ u v hs ht pub e₁ e₂
  obtain ⟨p, inputS, inputT, statuses, sp⟩ := public_inputs hs ht pub
  exact (function_ct backend _ _ _ _ _ _
    ⟨(p, (searchResult p s).statuses), ⟨inputS, rfl⟩, ⟨inputT, statuses.symm⟩, sp⟩ e₁ e₂).1

/-- The native controller registered for this attempt backend. -/
def calledCode (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : Prog VG.Arm.isa :=
  VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext
    (.call backend.keyName backend.generateKey)

theorem verified (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    Verified target (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey))
      (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)) :=
  ⟨correct backend, constantTime backend, sat⟩

end VG.Proof.Ffdh.Arm.KeySearch
