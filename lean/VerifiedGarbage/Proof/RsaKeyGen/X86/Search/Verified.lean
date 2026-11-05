module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CT
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateVerified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSafety
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpCode
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStackUse
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig

/-! # The verified prime search (i686)

For any candidate within 152 bytes of stack (`search_verified_of`), and for
the candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/X86/RsaKeyGen.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Impl.RsaKeyGen.X86.Search
open VG.Proof.MillerRabin.X86 (RoundImpl montName montCode compact_noSp compact_stack)

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 32
  | 2 => 0x2000
  | 3 => 0x3000
  | 4 => 1
  | 5 => 0x3100
  | 6 => 0
  | 7 => 0x4000
  | 8 => 0
  | 9 => 0x10000
  | 10 => 544
  | _ => 0x6000

/-- The arguments; a state with no candidates left, the width 32 and the
budget `32769 · 32 = 0x100020`; RSA's table at `0x30000`. -/
def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 48 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else if a = 0x6008 then 0x20
  else if a = 0x6010 then 0x20
  else if a = 0x6012 then 0x10
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 1⟩, ⟨0x3100, 0⟩, ⟨0x4000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩, ⟨0x6000, 32⟩, ⟨0x20004, 48⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 12) : arg satState i = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
  have small : i < 1024 := by simpa only [VG.Proof.RsaKeyGen.X86.Candidate.packed_length] using index
  have ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_)
    held
  intro j bound
  have address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have far : ∀ c : Addr, c.toNat < 0x10000 →
      0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j ≠ c := by
    intro c hc e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  change (if _ then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun inside => by
      change ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 48 at inside
      rw [address] at inside; omega),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6008 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6010 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6012 (by decide)))]

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Spec.RsaKeyGen.primeSearchContract, Spec.RsaKeyGen.primeSearchSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide),
    sat_arguments 9 (by decide), sat_arguments 10 (by decide), sat_arguments 11 (by decide)]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)
    | (unfold Spec.RsaKeyGen.primeLenValid; decide +kernel)
    | decide +kernel
    | rfl

theorem search_verified_of (c : Cand) : Verified target (code c.call) contract :=
  ⟨correct c, constantTime c, satisfiable⟩

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_rsa_keygen_candidate" ++ v.suffix
  code := Impl.RsaKeyGen.X86.Candidate.code montName montCode v.name v.code
  verified := Proof.RsaKeyGen.X86.Candidate.verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack
  noSp := CandidateNoSp.code compact_noSp v.noSp montName v.name
  stack := CandidateStackUse.code compact_stack v.stack montName v.name

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) : Verified target (searchCode v) contract :=
  search_verified_of (Cand.ofRound v)

/-- No instruction of the search, its candidate's included, writes `esp`. -/
theorem search_all (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true := by
  have h := Proof.RsaKeyGen.X86.Candidate.code_sp compact_noSp v.noSp montName v.name
  refine Code.all_of_allInstrs ?_
  simp only [searchCode, Cand.ofRound, Cand.call, code, body, iteration, candidateStep, candidateRun,
    Impl.RsaKeyGen.X86.Search.classify, reject, short, exhausted, zeroOut, Code.allInstrs, h]
  rfl

end VG.Proof.RsaKeyGen.X86.Search
