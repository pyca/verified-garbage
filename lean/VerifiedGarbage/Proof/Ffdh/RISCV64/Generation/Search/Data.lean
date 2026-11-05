module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Data
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Ffdh.GenerationTape

/-! # The parameter search's contract, public data, loop states and writes (RISC-V)

As on PPC64LE (`Proof/Ffdh/PPC64LE/Generation/Search/`): `searchContract` is
the controller on the machine, for a candidate (`Cand`) verified against
`vg_ffdh_parameter_candidate`'s contract with `S` bytes of stack; `SPub` is
everything two constant-time runs share, the tape included; a loop state
(`SLive`) is at an offset into the tape with attempts left, in the frame
saving `ra`, and the search from there (`SPub.tail`) is what the controller
returns. Then the controller's writes of its own words, its zeros at `out`,
and its tests of its attempts and of the status.

`vg_ffdh_generate_parameters(out = a0, out_len = a1, used = a2, bits = a3,
generator = a4, rand = a5, rand_len = a6, scratch = a7, scratch_len,
state)`: eight arguments in registers and two on the stack. The controller
uses `S + 32` bytes of stack: the frame of 16 bytes saving `ra`, its
candidate's frame of 16 bytes, and the `S` bytes the candidate may use below
its own.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Generation

open VG VG.RISCV64 VG.Spec.Ffdh VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)
open VG.Proof.Ffdh.RISCV64.KeyGeneration (CtlAccess tmpRegs)
open VG.Impl.Ffdh.RISCV64.Generation.Search

/-! ## The contract on the machine -/

/-- The stack the controller uses below the stack pointer, for a candidate
using `S` bytes. -/
abbrev stackUse (S : Nat) : Nat := S + 32

/-- An implementation of `vg_ffdh_parameter_candidate`, as the controller
calls it: its name, its code, the stack it uses, and its proof against the
candidate's contract with that stack. -/
structure Cand where
  name : String
  code : Prog isa
  S : Nat
  pos : 0 < S
  small : S ≤ 2 ^ 16
  stack : sdepth code ≤ S
  verified : Verified target code (Proof.Ffdh.parameterCandidateContract abi S)

/-- The candidate, as the controller calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .a2, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 1, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inRand s, inArgs s]

/-- The width, the bits, the generator, the tape and the attempts on entry. -/
abbrev genLen (s : State) : Nat := (s.gpr .a1).toNat
abbrev genBits (s : State) : Nat := (s.gpr .a3).toNat
abbrev genGen (s : State) : Nat := ((s.gpr .a4).setWidth 32).toNat
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat
abbrev genAttempts (s : State) : Nat := (s.mem.readW (stackArg s 1) 64).toNat

def searchPre (S : Nat) (s : State) : Prop :=
  s.sp.toNat + 8 * 2 ≤ 2 ^ 64 ∧ stackUse S ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp (stackUse S)).Disjoint r) ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0 ∧ (stackArg s 1).toNat % 8 = 0 ∧
    512 ≤ genBits s ∧ genBits s ≤ 8192 ∧ genLen s = (genBits s + 7) / 8 ∧
    (genGen s = 2 ∨ genGen s = 5) ∧
    Spec.Rsa.scratchWords (genLen s) ≤ (stackArg s 0).toNat ∧
    genAttempts s ≤ parameterAttempts (genBits s) ∧
    s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 (genLen s) ∧
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (parameterEntropy (genBits s)) ∧
    (s.gpr .a6).toNat ≤ parameterEntropy (genBits s)

def searchResult (s : State) : ParameterSearchResult :=
  parameterSearch (genBits s) (genGen s) (genAttempts s) (genRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .a0) (genLen s) =
      (match searchResult s with
        | .accepted p _ => i2osp p (genLen s)
        | _ => List.replicate (genLen s) 0) ∧
    wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    wordsAt t.mem (stackArg s 1) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (parameterEntropy (genBits s)),
      BitVec.ofNat 64 (searchResult s).requested]

/-- What timing may depend on: the arguments, the tape and the controller's
public words. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    wordsAt s.mem (stackArg s 1) 4 = wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧
    (s.gpr .a4).setWidth 32 = (t.gpr .a4).setWidth 32 ∧ s.gpr .a5 = t.gpr .a5 ∧ s.gpr .a6 = t.gpr .a6 ∧
    s.gpr .a7 = t.gpr .a7 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1

def searchContract (S : Nat) : Contract isa where
  pre := searchPre S
  post := searchPost
  pub := searchPub

/-! ## The public data -/

structure SPub where
  op : Addr
  up : Addr
  rp : Addr
  B : Addr
  control : Addr
  sp : Addr
  len : Nat
  bits : Nat
  gen : Nat
  randLen : Nat
  Z : Nat
  attempts : Nat
  /-- The stack the candidate uses. -/
  S : Nat
  rand : List Byte

def sOfState (S : Nat) (s : State) : SPub where
  op := s.gpr .a0
  up := s.gpr .a2
  rp := s.gpr .a5
  B := s.gpr .a7
  control := stackArg s 1
  sp := s.sp
  len := genLen s
  bits := genBits s
  gen := genGen s
  randLen := (s.gpr .a6).toNat
  Z := (stackArg s 0).toNat * 8
  attempts := genAttempts s
  S := S
  rand := genRand s

def SInput (p : SPub) (s : State) : Prop := searchPre p.S s ∧ sOfState p.S s = p

/-- Words of memory at a base: word `j` holds `v` for each `(j, v)`. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

/-- The search from octet `used` of the tape, with `k` attempts left. -/
def SPub.tail (p : SPub) (used k : Nat) : ParameterSearchResult :=
  (parameterSearch p.bits p.gen k (p.rand.drop used)).consume used

/-- The controller's words while it searches. -/
def SPub.headers (p : SPub) (used k : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 k), (1, BitVec.ofNat 64 p.len), (2, BitVec.ofNat 64 (parameterEntropy p.bits)),
    (5, p.op), (6, BitVec.ofNat 64 p.len), (7, p.up), (8, BitVec.ofNat 64 p.bits),
    (9, BitVec.ofNat 64 p.gen), (10, p.rp + BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (p.randLen - used)), (12, BitVec.ofNat 64 used), (13, p.B),
    (15, BitVec.ofNat 64 (p.Z / 8))]

theorem SPub.headers_bound (p : SPub) (used k : Nat) : ∀ e ∈ p.headers used k, e.1 < 16 := by
  simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> decide

theorem SPub.headers_index {p : SPub} {used k : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used k) : e.1 < 16 := p.headers_bound used k e he

/-- A state of the loop, in the frame saving `ra`: `used` octets consumed,
`k` attempts left. The entry state is functional-proof data only: its
callee-saved registers may hold secrets. -/
structure SLive (p : SPub) (original : State) (used k : Nat) (s : State) : Prop where
  input : SInput p original
  used_le : used ≤ p.randLen
  k_le : k ≤ p.attempts
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = p.sp - 16
  s0 : s.gpr .s0 = p.control
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  savedS0 : word s.mem p.control 32 = original.gpr .s0
  random : bytesAt s.mem p.rp p.randLen = p.rand
  headers : Slots s.mem p.control (p.headers used k)

/-- The output of a finished search. -/
def SOutput (p : SPub) (result : ParameterSearchResult) (m : Mem) : Prop :=
  bytesAt m p.op p.len =
    match result with
    | .accepted q _ => i2osp q p.len
    | _ => List.replicate p.len 0

/-- The controller's four public words for a finished search. -/
def SPub.policy (p : SPub) (result : ParameterSearchResult) : List (BitVec 64) :=
  [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.len,
    BitVec.ofNat 64 (parameterEntropy p.bits), BitVec.ofNat 64 result.requested]

/-- A finished search, before `finish` stores `used` and restores `s0`. -/
structure SDone (p : SPub) (original : State) (result : ParameterSearchResult) (s : State) : Prop where
  input : SInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  s0 : s.gpr .s0 = p.control
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  savedS0 : word s.mem p.control 32 = original.gpr .s0
  usedPtr : word s.mem p.control 56 = p.up
  used : word s.mem p.control 96 = BitVec.ofNat 64 result.used
  status : word s.mem p.control 112 = BitVec.ofNat 64 result.status
  policy : wordsAt s.mem p.control 4 = p.policy result
  output : SOutput p result s.mem

/-! ## Where the buffers are -/

/-- The regions the controller (and its callee) may write, and its stack. -/
def changes (S : Nat) (s : State) : List Region := inWrites s ++ [below s.sp (stackUse S)]

/-- The writes but the controller's words. -/
def callChanges (S : Nat) (s : State) : List Region :=
  [inOut s, inUsed s, inScr s, below s.sp (stackUse S)]

theorem callChanges_sub (S : Nat) (s : State) : ∀ r ∈ callChanges S s, ∃ q ∈ changes S s, Region.Sub r q := by
  intro r hr
  refine ⟨r, ?_, fun _ hi => hi⟩
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [changes, inWrites]

theorem frame_of_callChanges (S : Nat) (s : State) {m m' : Mem} (hf : Frame (callChanges S s) m m') :
    Frame (changes S s) m m' := hf.sub (callChanges_sub S s)

namespace SInput

variable {p : SPub} {s : State}

theorem rd_eq (h : SInput p s) : s.rd = inReads s := h.1.2.2.2.1

theorem wr_eq (h : SInput p s) : s.wr = inWrites s := h.1.2.2.2.2.1

theorem nowrap (h : SInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : SInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.2.1

theorem write_disjoint (h : SInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : SInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp (stackUse p.S)).Disjoint r :=
  h.1.2.2.2.2.2.2.2.2.1 r hr

theorem sp_eq (h : SInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem sp_room (h : SInput p s) : p.S + 32 ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem sp_al (h : SInput p s) : p.sp.toNat % 16 = 0 := by rw [h.sp_eq]; exact h.1.2.2.1

theorem sp_top (h : SInput p s) : p.sp.toNat + 16 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.1.1

theorem up_al (h : SInput p s) : p.up.toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hu, -⟩ := h.1
  rw [← h.2]; exact hu

theorem B_al (h : SInput p s) : p.B.toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -⟩ := h.1
  rw [← h.2]; exact hb

theorem control_al (h : SInput p s) : p.control.toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := h.1
  rw [← h.2]; exact hc

theorem bits_bounds (h : SInput p s) : 512 ≤ p.bits ∧ p.bits ≤ 8192 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := h.1
  rw [← h.2]; exact ⟨h1, h2⟩

theorem len_eq (h : SInput p s) : p.len = (p.bits + 7) / 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hl, -⟩ := h.1
  rw [← h.2]; exact hl

theorem len_bounds (h : SInput p s) : 64 ≤ p.len ∧ p.len ≤ 1024 := by
  have := h.bits_bounds; have := h.len_eq; omega

theorem gen_eq (h : SInput p s) : p.gen = 2 ∨ p.gen = 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := h.1
  rw [← h.2]; exact hg

theorem scratch_le (h : SInput p s) : Spec.Rsa.scratchWords p.len ≤ p.Z / 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ := h.1
  rw [← h.2]; simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]; exact hs

theorem z8 (h : SInput p s) : p.Z / 8 * 8 = p.Z := by
  rw [← h.2]; simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

theorem attempts_le (h : SInput p s) : p.attempts ≤ parameterAttempts p.bits := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ha, -⟩ := h.1
  rw [← h.2]; exact ha

theorem attempts_lt (h : SInput p s) : p.attempts < 2 ^ 64 := by
  have ha := h.attempts_le
  have hb := h.bits_bounds
  have : parameterAttempts p.bits ≤ 8192 * 8192 * 64 := by
    unfold parameterAttempts
    exact Nat.mul_le_mul (Nat.mul_le_mul hb.2 hb.2) (Nat.le_refl _)
  omega

theorem width_word (h : SInput p s) : s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 (genLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -⟩ := h.1
  exact hw

theorem entropy_word (h : SInput p s) :
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (parameterEntropy (genBits s)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := h.1
  exact he

theorem randLen_le (h : SInput p s) : p.randLen ≤ parameterEntropy p.bits := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hr⟩ := h.1
  rw [← h.2]; exact hr

theorem randLen_lt (h : SInput p s) : p.randLen < 2 ^ 64 := by
  rw [← h.2]; exact BitVec.isLt _

theorem rand_length (h : SInput p s) : p.rand.length = p.randLen := by
  rw [← h.2]; simp only [sOfState, genRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem entropy_lt (h : SInput p s) : parameterEntropy p.bits < 2 ^ 32 := by
  have := h.bits_bounds; unfold parameterEntropy; omega

theorem control_scr (h : SInput p s) {t : State} (hw : t.wr = s.wr) : Scr t p.control 128 := by
  refine Scr.of_mem (by rw [hw, h.wr_eq, ← h.2]; simp [inWrites, inCtl, sOfState]) ?_ h.control_al
  rw [← h.2]
  exact h.nowrap (r := inCtl s) (by simp [inWrites])

theorem read_disjoint (h : SInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes p.S s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem bytes_frame (h : SInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes p.S s) m m') : bytesAt m' r.base r.len = bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega_using [hn]) (List.mem_range.mp hi)

theorem random_frame (h : SInput p s) {m m' : Mem} (hf : Frame (changes p.S s) m m') :
    bytesAt m' p.rp p.randLen = bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

theorem control_frame (h : SInput p s) {m m' : Mem} (hf : Frame (callChanges p.S s) m m')
    (j : Nat) (hj : j < 16) : word m' p.control (8 * j) = word m p.control (8 * j) := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  rw [← h.2]
  refine hf.readW (r := inCtl s) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    (fun r hr => ?_) (by decide)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hpw.1.2.2.symm
  · exact hpw.2.1.2.symm
  · exact hpw.2.2.1.symm
  · exact (h.stack_disjoint (r := inCtl s) (by simp [inWrites])).symm

theorem out_eq (h : SInput p s) : inOut s = ⟨p.op, p.len⟩ := by rw [← h.2]; rfl

theorem used_eq (h : SInput p s) : inUsed s = ⟨p.up, 8⟩ := by rw [← h.2]; rfl

theorem ctl_eq (h : SInput p s) : inCtl s = ⟨p.control, 128⟩ := by rw [← h.2]; rfl

theorem scr_eq (h : SInput p s) : inScr s = ⟨p.B, p.Z⟩ := by rw [← h.2]; rfl

private theorem not_self_disjoint {r : Region} (h : r.Disjoint r) (hl : 0 < r.len) : False :=
  h r.base (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

theorem out_mem (h : SInput p s) : (⟨p.op, p.len⟩ : Region) ∈ inWrites s := by
  rw [← h.out_eq]; simp [inWrites]

theorem out_ctl (h : SInput p s) : (⟨p.op, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.out_eq, ← h.ctl_eq]
  exact this.1.2.2

/-- The word for the octets consumed is apart from `out` and the
controller's words. -/
theorem used_disjoint (h : SInput p s) :
    (⟨p.op, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  refine ⟨?_, ?_⟩
  · rw [← h.out_eq, ← h.used_eq]; exact hpw.1.1
  · rw [← h.ctl_eq, ← h.used_eq]; exact hpw.2.1.2.symm

theorem used_wr (h : SInput p s) {t : State} (hw : t.wr = s.wr) : InRegions t.wr p.up 8 :=
  ⟨⟨p.up, 8⟩, by rw [hw, h.wr_eq, ← h.used_eq]; simp [inWrites], Region.contains_self _ _⟩

end SInput

/-- The controller's word-only writes keep `out`. -/
theorem out_frame {p : SPub} {original : State} (hi : SInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') : bytesAt m' p.op p.len = bytesAt m p.op p.len := by
  have hk := hi.len_bounds
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi' => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.out_ctl)
    (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi')

/-! ## What keeps a loop state -/

/-- The controller's words after writes of `values`. -/
theorem headers_after {p : SPub} {s t : State} (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 16) (hm : t.mem = writeController s.mem p.control values)
    {used k : Nat}
    (hv : ∀ e ∈ p.headers used k, controllerValue values e.1 (word s.mem p.control (8 * e.1)) = e.2) :
    Slots t.mem p.control (p.headers used k) := by
  intro e he
  rw [hm, writeController_word _ _ _ hb e.1 (SPub.headers_index he)]
  exact hv e he

namespace SLive

variable {p : SPub} {original s t : State} {used k : Nat}

theorem access (h : SLive p original used k s) : CtlAccess s p.control :=
  CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)

theorem header (h : SLive p original used k s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used k) : word s.mem p.control (8 * j) = v :=
  h.headers (j, v) hj

theorem rand_length (h : SLive p original used k s) : p.rand.length = p.randLen := h.input.rand_length

/-- Through code that keeps `s0`, the stack pointer, the regions, the
controller's words, and writes only `out`, `used`, the working space and the
stack. -/
theorem restore (h : SLive p original used k s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (callChanges p.S original) s.mem t.mem) :
    SLive p original used k t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges p.S original hf
  refine ⟨h.input, h.used_le, h.k_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .s0 (by decide)).trans h.s0,
    fun r hr h0 => (hg r hr).trans (h.saved r hr h0), ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedS0
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (SPub.headers_index he)).trans (h.headers e he)

theorem keep (h : SLive p original used k s) {rs : List Reg}
    (kp : Keep rs s t) (hsp : t.sp = s.sp) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SLive p original used k t := by
  apply h.restore kp.2.1 kp.2.2 hsp (fun reg hr => kp.gpr (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `s0`. -/
theorem update (h : SLive p original used k s) {u k' : Nat}
    (hu : u ≤ p.randLen) (hk : k' ≤ p.attempts)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep tmpRegs s t) (hsp : t.sp = s.sp)
    (hh : Slots t.mem p.control (p.headers u k')) : SLive p original u k' t := by
  have hf : Frame (changes p.S original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [changes, inWrites], ?_⟩
    rw [h.input.ctl_eq]
    exact fun _ hi => hi
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr (by revert r hr; decide)
  refine ⟨h.input, hu, hk, kp.2.1.trans h.rd, kp.2.2.trans h.wr,
    hsp.trans h.sp, (hg .s0 (by decide)).trans h.s0,
    fun reg hreg h0 => (hg reg hreg).trans (h.saved reg hreg h0), ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedS0
  · exact (h.input.random_frame hf).trans h.random

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : SLive p original used k s) {r : ParameterSearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : wordsAt s.mem p.control 4 = p.policy r)
    (ho : SOutput p r s.mem) : SDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.s0, h.saved, h.savedS0,
    h.header (j := 7) (by simp [SPub.headers]),
    by rw [hu]; exact h.header (j := 12) (by simp [SPub.headers]), hs, hp, ho⟩

/-- A finished search, from a loop state through writes of the controller's
words but the saved `s0` and the pointer to `used`. -/
theorem doneWrites (h : SLive p original used k s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 16) (h4 : ∀ e ∈ values, 4 ≠ e.1) (h7 : ∀ e ∈ values, 7 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values) (kp : Keep tmpRegs s t)
    {r : ParameterSearchResult} (hu : word t.mem p.control 96 = BitVec.ofNat 64 r.used)
    (hs : word t.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : wordsAt t.mem p.control 4 = p.policy r) (ho : SOutput p r s.mem) :
    SDone p original r t := by
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr (by revert r hr; decide)
  have hw (j : Nat) (hj : j < 16) (hn : ∀ e ∈ values, j ≠ e.1) :
      word t.mem p.control (8 * j) = word s.mem p.control (8 * j) := by
    rw [hm, writeController_word _ _ _ hb j hj, controllerValue_unchanged _ _ _ hn]
  refine ⟨h.input, kp.2.1.trans h.rd, kp.2.2.trans h.wr, (hg .s0 (by decide)).trans h.s0,
    fun reg hreg h0 => (hg reg hreg).trans (h.saved reg hreg h0), ?_, ?_, hu, hs, hp, ?_⟩
  · exact (hw 4 (by decide) h4).trans h.savedS0
  · exact (hw 7 (by decide) h7).trans (h.header (j := 7) (by simp [SPub.headers]))
  · unfold SOutput at ho ⊢
    rw [hm, out_frame h.input (writeController_frame s.mem p.control values hb)]
    exact ho

end SLive

theorem SDone.keep {p : SPub} {original s t : State} {result : ParameterSearchResult}
    (h : SDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SDone p original result t := by
  refine ⟨h.input, k.2.1.trans h.rd, k.2.2.trans h.wr, (k.gpr (hregs .s0 (by decide))).trans h.s0,
    fun reg hr h0 => (k.gpr (hregs reg hr)).trans (h.saved reg hr h0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedS0
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

/-! ## Where the search goes from a loop state -/

/-- The candidate at octet `used` of the tape. -/
abbrev SPub.cand (p : SPub) (used : Nat) : Option (Option Nat × List Byte) :=
  parameterCandidate p.bits p.gen (p.rand.drop used)

/-- The octets the candidate at `used` reads. -/
def SPub.read (p : SPub) (used : Nat) : Nat :=
  match p.cand used with
  | some (_, rest) => (p.randLen - used) - rest.length
  | none => 0

theorem SPub.read_le {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    used + p.read used ≤ p.randLen := by
  have hu := h.used_le
  unfold SPub.read
  split <;> omega

theorem SPub.tail_zero (p : SPub) (used : Nat) : p.tail used 0 = .exhausted used := by
  simp only [SPub.tail, parameterSearch, ParameterSearchResult.consume, Nat.add_zero]

theorem SPub.tail_short {p : SPub} {used k : Nat} (hk : k ≠ 0) (hl : p.rand.length = p.randLen)
    (hc : p.cand used = none) :
    p.tail used k = if parameterEntropy p.bits ≤ p.randLen - used then .exhausted used
      else .entropy k (parameterRequest p.bits (p.randLen - used)) used := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [SPub.cand] at hc
  simp only [SPub.tail, parameterSearch, hc, List.length_drop, hl]
  split <;> simp only [ParameterSearchResult.consume, Nat.add_zero]

theorem SPub.tail_accept {p : SPub} {used k q : Nat} {rest : List Byte} (hk : k ≠ 0)
    (hl : p.rand.length = p.randLen) (hc : p.cand used = some (some q, rest)) :
    p.tail used k = .accepted q (used + ((p.randLen - used) - rest.length)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [SPub.cand] at hc
  simp only [SPub.tail, parameterSearch, hc, List.length_drop, hl, ParameterSearchResult.consume]

theorem SPub.tail_reject {p : SPub} {used k : Nat} {rest : List Byte} (hk : k ≠ 0)
    (hl : p.rand.length = p.randLen) (hc : p.cand used = some (none, rest)) :
    p.tail used k = p.tail (used + ((p.randLen - used) - rest.length)) (k - 1) := by
  have := Proof.Ffdh.Generation.search_reject (Nat.pos_of_ne_zero hk) hc
  simp only [List.length_drop, hl] at this
  exact this

theorem result_status_lt (r : ParameterSearchResult) : r.status < 5 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem result_status_ne (r : ParameterSearchResult) : r.status ≠ 4 := by
  unfold ParameterSearchResult.status; split <;> decide

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .s0 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep tmpRegs s t ∧ t.sp = s.sp := by
  rcases hst with rfl | rfl <;>
  refine KeyGeneration.WP.ctl ?_ (by rfl) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [stf, hb, a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide),
      a.al 0 (by decide) (by decide), a.al 24 (by decide) (by decide),
      a.al 112 (by decide) (by decide), fin64_exec_li_zero, fin64_exec_li_lit (show 1 < 2048 by decide),
      fin64_exec_li_lit (show 3 < 2048 by decide)]

/-- A terminal status written over a loop state, with no attempts left. -/
theorem terminal_live {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      SLive p original used 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (terminal_ok h.access h.s0 hst) fun t ⟨hm, k, hsp⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update (u := used) (k' := 0) h.used_le (Nat.zero_le _) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k hsp hh, hm⟩

/-- The words of a terminal status written over a loop state. -/
theorem terminal_words {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat}
    (hm : (j : Nat) → j < 16 → word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j))) :
    word t.mem p.control 112 = BitVec.ofNat 64 status ∧
      wordsAt t.mem p.control 4 = [0, BitVec.ofNat 64 p.len,
        BitVec.ofNat 64 (parameterEntropy p.bits), 0] := by
  refine ⟨?_, ?_⟩
  · rw [show (112 : Nat) = 8 * 14 from rfl, hm 14 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rw [h.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]

/-! ## Zeros at `out` -/

/-- A zeroing of `out` changes memory only there. -/
theorem zero_frame {p : SPub} {original : State} (hi : SInput p original) {m m' : Mem}
    (hf : Mont.Outside p.op 0 p.len m m') : Frame (callChanges p.S original) m m' := by
  intro a ha
  refine hf a (Or.inr ?_)
  have hin : (⟨p.op, p.len⟩ : Region) ∈ callChanges p.S original := by
    rw [← hi.out_eq]; simp [callChanges]
  have := ha _ hin
  simp only [Region.Contains, Mont.ofs] at this ⊢
  omega

theorem search_zero_out {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa zeroOut s fun t =>
      SLive p original used k t ∧ bytesAt t.mem p.op p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have a := h.access
  have hv := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv hv6
  have hno : p.op.toNat + p.len ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inOut original) (by simp [inWrites])
    rw [h.input.out_eq] at this; exact this
  have hout : ∀ i < p.len, InRegions s.wr (off p.op i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by rw [h.wr, h.input.wr_eq]; exact h.input.out_mem,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.t0, .t1, .t2] (Q := fun t => t.gpr .t0 = p.op ∧
      t.gpr .t1 = BitVec.ofNat 64 p.len ∧ t.gpr .t2 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.s0, hv, hv6, a.ld 40 (by decide), a.ld 48 (by decide),
      a.al 40 (by decide) (by decide), a.al 48 (by decide) (by decide), fin64_exec_li_zero]) (by rfl)))
    fun s₁ ⟨⟨⟨h3, h4, h5, hm₁⟩, k₁⟩, _, _, hsp₁⟩ => ?_)
  refine WP.mono (WP.rdwr (KeyGeneration.zeroLoop_ok (by omega) (by omega)
      (fun i hi => by rw [k₁.2.2]; exact hout i hi) h3 h4 h5))
    fun t ⟨⟨⟨tb, tout⟩, kt⟩, _, _, hspt⟩ => ?_
  have kk := k₁.trans kt
  have tout' : Mont.Outside p.op 0 p.len s.mem t.mem := by rw [← hm₁]; exact tout
  have hfr := zero_frame h.input tout'
  refine ⟨h.restore kk.2.1 kk.2.2 (hspt.trans hsp₁) (fun r hr => kk.gpr (by revert r hr; decide)) hfr, ?_,
    fun j hj => h.input.control_frame hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact tb i (List.mem_range.mp hi)

theorem search_exhausted {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa exhausted s (SDone p original (.exhausted used)) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_live h (status := 3) (.inr rfl)) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (search_zero_out ht) fun u ⟨hu, hz, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) : word u.mem p.control (8 * j) =
      controllerValue (terminalValues 3) j (word s.mem p.control (8 * j)) := by
    rw [hc j hj, hm, writeController_word _ _ _ (terminalValues_bound 3) j hj]
  obtain ⟨hs, hp⟩ := terminal_words h hw
  exact hu.done rfl hs hp hz

/-! ## The controller's tests of its attempts and of the status -/

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- The attempts left compared with zero. -/
theorem attempts_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block [ldf .t0 0]) s fun t =>
      SLive p original used k t ∧ isa.eval (.zero .t0) t = some (decide (k = 0)) := by
  have a := h.access
  have hw := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hw
  have hk : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega
  refine WP.mono (KeyGeneration.WP.ctl (Q := fun t =>
    isa.eval (.zero .t0) t = some (decide (k = 0)) ∧ t.mem = s.mem) ?_ (by rfl))
    fun _ ⟨⟨he, hm⟩, kt, hsp⟩ => ⟨h.keep kt hsp hm, he⟩
  brun [ldf, h.s0, hw, a.ld 0 (by decide), a.al 0 (by decide) (by decide), KeyGeneration.eval_zero',
    ofNat_beq_zero hk]

/-- The status word, less 4, compared with zero. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .s0 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) s fun t =>
      (isa.eval (.zero .t0) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep tmpRegs s t ∧ t.sp = s.sp := by
  have h4 : ∀ st < 5, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = decide (st = 4) := by decide
  simp only [Bignum.word] at hs
  refine KeyGeneration.WP.ctl ?_ (by rfl)
  brun [ldf, hb, hs, a.ld 112 (by decide), a.al 112 (by decide) (by decide), KeyGeneration.eval_zero',
    h4 st hst]

theorem done_loop_guard {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) :
    WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) s fun t =>
      isa.eval (.zero .t0) t = some false ∧ SDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.s0 h.status (result_status_lt r)) fun t ⟨⟨he, hm⟩, k, _⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (result_status_ne r)]

theorem live_loop_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) s fun t =>
      isa.eval (.zero .t0) t = some true ∧ SLive p original used k t :=
  WP.mono (status_guard (st := 4) h.access h.s0 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k, hsp⟩ => ⟨he, h.keep k hsp hm⟩

end VG.Proof.Ffdh.RISCV64.Generation
