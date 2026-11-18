module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Start
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.TCB.X86_64.Target

/-! ### `Ffdh.X86_64.Generation.SearchData`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchContract`, which this module and modules that import it used -/

section

/-! # The complete parameter-search controller: layout and observable result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Ffdh.X86_64.ParameterCandidate

def inputRand (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
def inputArgs (s : State) : Region := ⟨stackArgAddr s 0, 32⟩
def inputControl (s : State) : Region := ⟨stackArg s 3, 128⟩
def inputBuffers (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

def candidateState (s : State) : State :=
  s.withRegions [inputRand s, ⟨stackArgAddr s 0, 24⟩] (inputBuffers s)

def searchPre (s : State) : Prop :=
  pcPre (candidateState s) ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
    s.rd = [inputRand s, inputArgs s] ∧
    s.wr = inputBuffers s ++ [inputControl s] ∧
    (stackArg s 3).toNat + 128 ≤ 2 ^ 64 ∧
    (∀ r ∈ inputBuffers s ++ [inputRand s, inputArgs s, ⟨s.gpr .rsp, 8⟩,
      below (s.gpr .rsp) 160], (inputControl s).Disjoint r) ∧
    (∀ r ∈ inputBuffers s, r.Disjoint (inputArgs s)) ∧
    160 ≤ (s.gpr .rsp).toNat ∧
    (∀ r ∈ inputBuffers s ++ [inputRand s, inputControl s],
      (below (s.gpr .rsp) 160).Disjoint r) ∧
    (s.mem.readW (stackArg s 3) 64).toNat ≤ Spec.Ffdh.parameterAttempts (s.gpr .rcx).toNat ∧
    s.mem.readW (stackArg s 3 + 8) 64 = s.gpr .rsi ∧
    s.mem.readW (stackArg s 3 + 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat) ∧
    (stackArg s 0).toNat ≤ Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat

def searchResult (s : State) : Spec.Ffdh.ParameterSearchResult :=
  Spec.Ffdh.sievedParameterSearch (s.gpr .rcx).toNat ((s.gpr .r8).setWidth 32).toNat
    (s.mem.readW (stackArg s 3) 64).toNat (pcRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = (searchResult s).status ∧
    Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      (match searchResult s with
        | .accepted p _ => Spec.Rsa.i2osp p (s.gpr .rsi).toNat
        | _ => List.replicate (s.gpr .rsi).toNat 0) ∧
    Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    ∃ requested, Spec.Rsa.wordsAt t.mem (stackArg s 3) 4 =
      [BitVec.ofNat 64 (searchResult s).remaining, s.gpr .rsi,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat),
        BitVec.ofNat 64 requested] ∧
      (searchResult s).Requests (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat) requested

def searchPub (s t : State) : Prop :=
  pcPub s t ∧ stackArg s 3 = stackArg t 3 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 3) 4 = Spec.Rsa.wordsAt t.mem (stackArg t 3) 4

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Public search inputs and the persistent native loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

structure SearchPublic where
  candidate : CandidateP
  control : Addr
  remaining : Nat

abbrev SearchPublic.c (p : SearchPublic) := p.candidate

def searchOfState (s : State) : SearchPublic :=
  ⟨candidateOfState s, stackArg s 3, (s.mem.readW (stackArg s 3) 64).toNat⟩

def SearchInput (p : SearchPublic) (s : State) : Prop := searchPre s ∧ searchOfState s = p

def SearchPublic.headers (p : SearchPublic) (used remaining : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 remaining), (1, BitVec.ofNat 64 p.c.k),
    (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)),
    (5, p.c.op), (6, BitVec.ofNat 64 p.c.k), (7, p.c.up), (8, BitVec.ofNat 64 p.c.bits),
    (9, BitVec.ofNat 64 p.c.gen), (10, off p.c.rp used),
    (11, BitVec.ofNat 64 (p.c.rand.length - used)), (12, BitVec.ofNat 64 used),
    (13, p.c.B), (15, BitVec.ofNat 64 (p.c.Z / 8))]

/-- The original ABI snapshot is functional-proof data, not public data.
In particular its callee-saved registers may contain secrets. Only the
`SearchPublic` descriptor is shared between constant-time runs. -/
structure SearchLive (p : SearchPublic) (original : State) (used remaining : Nat) (s : State) : Prop where
  input : SearchInput p original
  used_le : used ≤ p.c.rand.length
  remaining_le : remaining ≤ p.remaining
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  rsp : s.gpr .rsp = p.c.sp
  r12 : s.gpr .r12 = p.control
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → s.gpr r = original.gpr r
  savedR12 : word s.mem p.control 32 = original.gpr .r12
  random : Spec.Rsa.bytesAt s.mem p.c.rp p.c.rand.length = p.c.rand
  headers : Slots s.mem p.control (p.headers used remaining)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # The native controller, tape, and candidate workspace are disjoint -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

namespace SearchInput

variable {p : SearchPublic} {original : State}

theorem control_scr (h : SearchInput p original) {s : State} (hw : s.wr = original.wr) :
    Scr s p.control 128 := by
  cases h.2
  obtain ⟨_, _, _, hwr, hroom, _⟩ := h.1
  exact Scr.of_mem (by rw [hw, hwr]; simp [searchOfState, inputControl]) hroom

theorem random_disjoint (h : SearchInput p original) :
    ∀ r ∈ original.wr ++ [below (original.gpr .rsp) 160], (inputRand original).Disjoint r := by
  obtain ⟨hc, _, _, hwr, _, hctrl, _, _, hstack, _⟩ := h.1
  obtain ⟨_, _, _, _, _, dor, _, _, dur, _, _, drs, _, _, _, _, _, _, _, _, _, _⟩ := hc
  intro r hr
  rw [hwr] at hr
  simp only [inputBuffers, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact dor.symm
  · exact dur.symm
  · exact drs
  · exact (hctrl (inputRand original) (by simp)).symm
  · exact (hstack (inputRand original) (by simp)).symm

theorem random_frame (h : SearchInput p original) {m m' : Mem}
    (hf : Frame (original.wr ++ [below (original.gpr .rsp) 160]) m m') :
    Spec.Rsa.bytesAt m' p.c.rp p.c.rand.length = Spec.Rsa.bytesAt m p.c.rp p.c.rand.length := by
  cases h.2
  change Spec.Rsa.bytesAt m' (original.gpr .r9) (pcRand original).length =
    Spec.Rsa.bytesAt m (original.gpr .r9) (pcRand original).length
  have hl : (pcRand original).length = (stackArg original 0).toNat := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [hl]
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (h.random_disjoint) (Nat.le_of_lt (BitVec.isLt _)) (List.mem_range.mp hi)

theorem control_disjoint (h : SearchInput p original) :
    ∀ r ∈ inputBuffers original ++ [below (original.gpr .rsp) 160], (inputControl original).Disjoint r := by
  intro r hr
  obtain ⟨_, _, _, _, _, hd, _⟩ := h.1
  rcases List.mem_append.mp hr with hr | hr
  · exact hd _ (List.mem_append_left _ hr)
  · simp only [List.mem_singleton] at hr; subst r
    exact hd _ (by simp)

theorem control_frame (h : SearchInput p original) {m m' : Mem}
    (hf : Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) m m')
    (j : Nat) (hj : j < 16) : word m' p.control (8 * j) = word m p.control (8 * j) := by
  cases h.2
  exact hf.readW (r := inputControl original)
    (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    h.control_disjoint (by decide)

end SearchInput

end VG.Proof.Ffdh.X86_64.Generation
