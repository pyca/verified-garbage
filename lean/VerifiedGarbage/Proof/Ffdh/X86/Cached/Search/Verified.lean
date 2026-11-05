module

import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.CT
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.ABI
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.CachedSat

/-! # `vg_ffdh_generate_key_search_cached` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86

/-- x, y of 64 bytes, `used`, the domain of 128 (`CachedSat.domain`), an empty tape, a working space of
1056 words, a state with the width 64 and the domain's context, apart. -/
def satBase (a : Addr) : Byte :=
  if a = 0x20005 then 0x10
  else if a = 0x20008 then 64
  else if a = 0x2000d then 0x20
  else if a = 0x20010 then 64
  else if a = 0x20015 then 0x50
  else if a = 0x20019 then 0x30
  else if a = 0x2001c then 128
  else if a = 0x20020 then 64
  else if a = 0x20025 then 0x40
  else if a = 0x2002d then 0x90
  else if a = 0x20030 then 0x20
  else if a = 0x20031 then 4
  else if a = 0x20035 then 0x60
  else if a = 0x2003a then 0x10
  else if a = 0x2003c then 0x13
  else if a = 0x2003d then 1
  else if a = 0x6010 then 64 else CachedSat.domainMem a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := CachedSat.withContext satBase
  rd := [⟨0x3000, 128⟩, ⟨0x4000, 0⟩, ⟨0x100000, 2200⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x6000, 128⟩, ⟨0x20004, 60⟩]

theorem sat_read {a : Addr} {w : Nat} (small : a.toNat + w / 8 ≤ 0x100000) :
    satState.mem.readW a w = Mem.readW satBase a w :=
  CachedSat.readW_outside _ small

theorem sat_arg (i : Nat) (hi : i < 15) : arg satState i = Mem.readW satBase (argAddr satState i) 32 := by
  unfold arg
  refine sat_read ?_
  have small : ∀ i < 15, (argAddr satState i).toNat + 32 / 8 ≤ 0x100000 := by decide
  exact small i hi

theorem sat_domain : Spec.Rsa.bytesAt satState.mem 0x3000 128 = CachedSat.domain := by
  rw [show satState.mem = CachedSat.withContext satBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, satBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem satisfiable : ∃ s, (Spec.Ffdh.cachedKeySearchContract abi stack).pre s := by
  have a0 : arg satState 0 = 0x1000 := by rw [sat_arg 0 (by decide)]; decide
  have a1 : arg satState 1 = 64 := by rw [sat_arg 1 (by decide)]; decide
  have a2 : arg satState 2 = 0x2000 := by rw [sat_arg 2 (by decide)]; decide
  have a3 : arg satState 3 = 64 := by rw [sat_arg 3 (by decide)]; decide
  have a4 : arg satState 4 = 0x5000 := by rw [sat_arg 4 (by decide)]; decide
  have a5 : arg satState 5 = 0x3000 := by rw [sat_arg 5 (by decide)]; decide
  have a6 : arg satState 6 = 128 := by rw [sat_arg 6 (by decide)]; decide
  have a7 : arg satState 7 = 64 := by rw [sat_arg 7 (by decide)]; decide
  have a8 : arg satState 8 = 0x4000 := by rw [sat_arg 8 (by decide)]; decide
  have a9 : arg satState 9 = 0 := by rw [sat_arg 9 (by decide)]; decide
  have a10 : arg satState 10 = 0x9000 := by rw [sat_arg 10 (by decide)]; decide
  have a11 : arg satState 11 = 1056 := by rw [sat_arg 11 (by decide)]; decide
  have a12 : arg satState 12 = 0x6000 := by rw [sat_arg 12 (by decide)]; decide
  have a13 : arg satState 13 = 0x100000 := by rw [sat_arg 13 (by decide)]; decide
  have a14 : arg satState 14 = 275 := by rw [sat_arg 14 (by decide)]; decide
  have e : argAddr satState 0 = 0x20004 := by decide
  refine ⟨satState, ?_⟩
  sig_pre [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots,
    argVal, argBytes, stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, e]
  sig_and_intros
  all_goals first
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt satState.mem 0x3000 128) = true
       rw [sat_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt satState.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt satState.mem 0x100000 275)
       rw [sat_domain]; exact (CachedSat.canonical satBase).2)
    | (rw [CachedSat.readW_outside _ (by decide)]; decide)
    | exact Region.disjoint_of_sep (by decide)
    | rfl
    | decide

theorem verified : Verified target Impl.Ffdh.X86.Cached.Search.code (Spec.Ffdh.cachedKeySearchContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Cached.Search
