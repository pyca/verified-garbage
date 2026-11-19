module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Ffdh.SievedBounds
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Contract
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-! ### `Ffdh.AArch64.Generation.Search.Live`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Generation.Search.Data`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Generation.Search.Contract`, which this module and modules that import it used -/

section

/-! # The parameter-search controller's contract in terms of the machine (AArch64)

`vg_ffdh_generate_parameters(out = x0, out_len = x1, used = x2, bits = x3,
generator = w4, rand = x5, rand_len = x6, scratch = x7, scratch_len, state)`:
eight arguments in registers and two on the stack. The controller uses 32
bytes of stack: the frame saving `x30` and its candidate's frame of 16
bytes; the candidate it calls has no frames (`Cand.noFrames`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.AArch64.ParameterCandidate (pcContract pcPre pcPub)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 32

/-- An implementation of `vg_ffdh_parameter_candidate_sieved`, as the controller
calls it: its name, its code, which has no frames, and its proofs. -/
structure Cand where
  name : String
  code : Prog isa
  noFrames : code.noFrames = true
  correct : ∀ s, pcContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pcContract.post s s'
  ct : ConstantTime isa pcPre pcPub code

/-- The candidate, as the controller calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x2, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 1, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inRand s, inArgs s]

/-- The width, the bits, the generator, the tape and the attempts on entry. -/
abbrev genLen (s : State) : Nat := (s.gpr .x1).toNat
abbrev genBits (s : State) : Nat := (s.gpr .x3).toNat
abbrev genGen (s : State) : Nat := ((s.gpr .x4).setWidth 32).toNat
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
abbrev genAttempts (s : State) : Nat := (s.mem.readW (stackArg s 1) 64).toNat

def searchPre (s : State) : Prop :=
  s.sp.toNat + 16 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    512 ≤ genBits s ∧ genBits s ≤ 8192 ∧ genLen s = (genBits s + 7) / 8 ∧
    (genGen s = 2 ∨ genGen s = 5) ∧
    Spec.Rsa.scratchWords (genLen s) ≤ (stackArg s 0).toNat ∧
    genAttempts s ≤ parameterAttempts (genBits s) ∧
    s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 (genLen s) ∧
    s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (parameterEntropy (genBits s)) ∧
    (s.gpr .x6).toNat ≤ parameterEntropy (genBits s)

def searchResult (s : State) : ParameterSearchResult :=
  sievedParameterSearch (genBits s) (genGen s) (genAttempts s) (genRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .x0) (genLen s) =
      (match searchResult s with
        | .accepted p _ => i2osp p (genLen s)
        | _ => List.replicate (genLen s) 0) ∧
    wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    ∃ requested, wordsAt t.mem (stackArg s 1) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (parameterEntropy (genBits s)),
      BitVec.ofNat 64 requested] ∧
      (searchResult s).Requests (parameterEntropy (genBits s)) requested

/-- What timing may depend on: the arguments, the tape and the controller's
public words. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    wordsAt s.mem (stackArg s 1) 4 = wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    (s.gpr .x4).setWidth 32 = (t.gpr .x4).setWidth 32 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.gpr .x7 = t.gpr .x7 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # The parameter search's public data, loop states and buffers (AArch64)

`SPub` is everything two constant-time runs share, the tape included; a
loop state (`SLive`) is at an offset into the tape with attempts left, in
the frame saving `x30`, and the search from there (`SPub.tail`) is what the
controller returns.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.Ffdh.AArch64 (Slots)

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
  rand : List Byte

def sOfState (s : State) : SPub where
  op := s.gpr .x0
  up := s.gpr .x2
  rp := s.gpr .x5
  B := s.gpr .x7
  control := stackArg s 1
  sp := s.sp
  len := genLen s
  bits := genBits s
  gen := genGen s
  randLen := (s.gpr .x6).toNat
  Z := (stackArg s 0).toNat * 8
  attempts := genAttempts s
  rand := genRand s

def SInput (p : SPub) (s : State) : Prop := searchPre s ∧ sOfState s = p

/-- The search from octet `used` of the tape, with `k` attempts left. -/
def SPub.tail (p : SPub) (used k : Nat) : ParameterSearchResult :=
  (sievedParameterSearch p.bits p.gen k (p.rand.drop used)).consume used

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

/-- A state of the loop, in the frame saving `x30`: `used` octets consumed,
`k` attempts left. The entry state is functional-proof data only: its
callee-saved registers may hold secrets. -/
structure SLive (p : SPub) (original : State) (used k : Nat) (s : State) : Prop where
  input : SInput p original
  used_le : used ≤ p.randLen
  k_le : k ≤ p.attempts
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = p.sp - 16
  x19 : s.gpr .x19 = p.control
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.control 32 = original.gpr .x19
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = p.rand
  headers : Slots s.mem p.control (p.headers used k)

/-- The output of a finished search. -/
def SOutput (p : SPub) (result : ParameterSearchResult) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m p.op p.len =
    match result with
    | .accepted q _ => Spec.Rsa.i2osp q p.len
    | _ => List.replicate p.len 0

/-- The controller's four public words for a finished search. -/
def SPub.policy (p : SPub) (result : ParameterSearchResult) : List (BitVec 64) :=
  [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.len,
    BitVec.ofNat 64 (parameterEntropy p.bits), BitVec.ofNat 64 (Proof.Ffdh.requested p.bits result)]

/-- A finished search, before `finish` stores `used` and restores `x19`. -/
structure SDone (p : SPub) (original : State) (result : ParameterSearchResult) (s : State) : Prop where
  input : SInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  x19 : s.gpr .x19 = p.control
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.control 32 = original.gpr .x19
  usedPtr : word s.mem p.control 56 = p.up
  used : word s.mem p.control 96 = BitVec.ofNat 64 result.used
  status : word s.mem p.control 112 = BitVec.ofNat 64 result.status
  policy : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy result
  output : SOutput p result s.mem

/-! ## Where the buffers are -/

namespace SInput

variable {p : SPub} {s : State}

theorem nowrap (h : SInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.1 r hr

theorem write_disjoint (h : SInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : SInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : SInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.1

theorem bits_bounds (h : SInput p s) : 512 ≤ p.bits ∧ p.bits ≤ 8192 := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -⟩ := h.1
  rw [← h.2]; exact ⟨h1, h2⟩

theorem len_eq (h : SInput p s) : p.len = (p.bits + 7) / 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl, -⟩ := h.1
  rw [← h.2]; exact hl

theorem len_bounds (h : SInput p s) : 64 ≤ p.len ∧ p.len ≤ 1024 := by
  have := h.bits_bounds; have := h.len_eq; omega_arith

theorem attempts_le (h : SInput p s) : p.attempts ≤ parameterAttempts p.bits := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ha, -⟩ := h.1
  rw [← h.2]; exact ha

theorem attempts_lt (h : SInput p s) : p.attempts < 2 ^ 64 := by
  have ha := h.attempts_le
  have hb := h.bits_bounds
  have : parameterAttempts p.bits ≤ 8192 * 8192 * 64 := by
    unfold parameterAttempts
    exact Nat.mul_le_mul (Nat.mul_le_mul hb.2 hb.2) (Nat.le_refl _)
  omega_using [ha, this]

theorem randLen_le (h : SInput p s) : p.randLen ≤ parameterEntropy p.bits := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hr⟩ := h.1
  rw [← h.2]; exact hr

theorem randLen_lt (h : SInput p s) : p.randLen < 2 ^ 64 := by
  rw [← h.2]; exact BitVec.isLt _

theorem rand_length (h : SInput p s) : p.rand.length = p.randLen := by
  rw [← h.2]; simp only [sOfState, genRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem sp_eq (h : SInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem sp_room (h : SInput p s) : 32 ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem control_scr (h : SInput p s) {t : State} (hw : t.wr = s.wr) : Scr t p.control 128 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inCtl, sOfState]) ?_
  rw [← h.2]
  exact h.nowrap (r := inCtl s) (by simp [inWrites])

/-- The regions the controller (and its callee) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below s.sp stackUse]

theorem read_disjoint (h : SInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem bytes_frame (h : SInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega_using [hn]) (List.mem_range.mp hi)

theorem random_frame (h : SInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

/-- The writes but the controller's words. -/
def callChanges (s : State) : List Region :=
  [inOut s, inUsed s, inScr s, below s.sp stackUse]

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  refine ⟨r, ?_, fun _ hi => hi⟩
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [changes, inWrites]

theorem control_frame (h : SInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
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

theorem out_eq (h : SInput p s) : inOut s = ⟨p.op, p.len⟩ := by
  rw [← h.2]; rfl

theorem used_eq (h : SInput p s) : inUsed s = ⟨p.up, 8⟩ := by
  rw [← h.2]; rfl

theorem ctl_eq (h : SInput p s) : inCtl s = ⟨p.control, 128⟩ := by
  rw [← h.2]; rfl

end SInput

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (SInput.callChanges s) m m') :
    Frame (SInput.changes s) m m' := hf.sub (SInput.callChanges_sub s)

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # What keeps the parameter search's loop state (AArch64), and where the search goes -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)

/-- The loads and stores of a controller's block, at its words. -/
structure CtlAccess (s : State) (B : Addr) : Prop where
  ld : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  st : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8
  ld0 : InRegions (s.rd ++ s.wr) B 8
  st0 : InRegions s.wr B 8

theorem CtlAccess.of_scr {s : State} {B : Addr} (scr : Scr s B 128) : CtlAccess s B :=
  ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩

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

/-- Through code that keeps `x19`, the stack pointer, the regions, the
controller's words, and writes only the output, `used`, the working space
and the stack. -/
theorem restore (h : SLive p original used k s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame (SInput.callChanges original) s.mem t.mem) :
    SLive p original used k t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.k_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .x19 (by decide) (by decide)).trans h.x19,
    fun r hr h19 h30 => (hg r hr h30).trans (h.saved r hr h19 h30),
    fun r hr => (hv r hr).trans (h.vcs r hr), ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedX19
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (SPub.headers_index he)).trans (h.headers e he)

theorem keep (h : SLive p original used k s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SLive p original used k t := by
  apply h.restore kp.rd kp.wr kp.sp (fun reg hr _ => kp.gpr reg (hregs reg hr)) kp.vcs
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `x19`. -/
theorem update (h : SLive p original used k s) {u k' : Nat}
    (hu : u ≤ p.randLen) (hk : k' ≤ p.attempts)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.x0, .x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s t)
    (hh : Slots t.mem p.control (p.headers u k')) : SLive p original u k' t := by
  have hf : Frame (SInput.changes original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [SInput.changes, inWrites], ?_⟩
    rw [h.input.ctl_eq]
    exact fun _ hi => hi
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  refine ⟨h.input, hu, hk, kp.rd.trans h.rd, kp.wr.trans h.wr,
    kp.sp.trans h.sp, (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedX19
  · exact (h.input.random_frame hf).trans h.random

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : SLive p original used k s) {r : ParameterSearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : SOutput p r s.mem) : SDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.x19, h.saved, h.vcs, h.savedX19,
    h.header (j := 7) (by simp [SPub.headers]),
    by rw [hu]; exact h.header (j := 12) (by simp [SPub.headers]), hs, hp, ho⟩

end SLive

theorem SDone.keep {p : SPub} {original s t : State} {result : ParameterSearchResult}
    (h : SDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ (hregs .x19 (by decide))).trans h.x19,
    fun reg hr h19 h30 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h19 h30),
    fun r hr => (k.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedX19
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

/-! ## Where the search goes from a loop state -/

theorem SPub.tail_zero (p : SPub) (used : Nat) : p.tail used 0 = .exhausted used := by
  simp only [SPub.tail, sievedParameterSearch, ParameterSearchResult.consume, Nat.add_zero]

theorem SPub.tail_short {p : SPub} {used k : Nat} (hk : k ≠ 0) (hl : p.rand.length = p.randLen)
    (hc : sievedParameterCandidate p.bits p.gen (p.rand.drop used) = none) :
    p.tail used k = if parameterEntropy p.bits ≤ p.randLen - used then .exhausted used
      else .entropy k (p.randLen - used) used := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [SPub.tail, sievedParameterSearch, hc, List.length_drop, hl]
  split <;> simp only [ParameterSearchResult.consume, Nat.add_zero]

theorem SPub.tail_accept {p : SPub} {used k q : Nat} {rest : List Byte} (hk : k ≠ 0)
    (hl : p.rand.length = p.randLen)
    (hc : sievedParameterCandidate p.bits p.gen (p.rand.drop used) = some (some q, rest)) :
    p.tail used k = .accepted q (used + ((p.randLen - used) - rest.length)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [SPub.tail, sievedParameterSearch, hc, List.length_drop, hl, ParameterSearchResult.consume]

theorem SPub.tail_reject {p : SPub} {used k : Nat} {rest : List Byte} (hk : k ≠ 0)
    (hl : p.rand.length = p.randLen)
    (hc : sievedParameterCandidate p.bits p.gen (p.rand.drop used) = some (none, rest)) :
    p.tail used k = p.tail (used + ((p.randLen - used) - rest.length)) (k - 1) := by
  have := Proof.Ffdh.SievedGeneration.search_reject (Nat.pos_of_ne_zero hk) hc
  simp only [List.length_drop, hl] at this
  exact this

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! ### `Ffdh.AArch64.Generation.Search.Call`, which the modules that import this one used -/

section

/-! # One candidate of the parameter search (AArch64)

In its frame, the controller passes `vg_ffdh_parameter_candidate_sieved` the rest
of the tape. The candidate's buffers are the controller's (`out`, `used`,
the tape's rest and the working space), and its stack argument is in the
candidate's frame, in the 32 bytes of stack below the controller's stack
pointer on entry, which no buffer overlaps. The candidate keeps the
controller's state, and leaves its status, p or zeros at `out`, and the
octets it read at `used`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.AArch64.ParameterCandidate (pcPre pcPost pcResult pcRand)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-- The stack pointer in the candidate's frame. -/
abbrev callSp (p : SPub) : Addr := p.sp - 16 - BitVec.ofNat 64 16

theorem callSp_eq (p : SPub) : callSp p = p.sp - BitVec.ofNat 64 32 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The candidate's regions: `out`, `used`, the tape's rest, the working
space and its argument. -/
abbrev rO (p : SPub) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SPub) : Region := ⟨p.up, 8⟩
abbrev rR (p : SPub) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SPub) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SPub) : Region := ⟨callSp p, 8⟩

structure CallFacts (p : SPub) (used : Nat) : Prop where
  room : 32 ≤ p.sp.toNat
  ou : (rO p).Disjoint (rU p)
  or : (rO p).Disjoint (rR p used)
  os : (rO p).Disjoint (rS p)
  oa : (rO p).Disjoint (rA p)
  ur : (rU p).Disjoint (rR p used)
  us : (rU p).Disjoint (rS p)
  ua : (rU p).Disjoint (rA p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  no : p.op.toNat + p.len ≤ 2 ^ 64
  nu : p.up.toNat + 8 ≤ 2 ^ 64
  nr : (p.rp + BitVec.ofNat 64 used).toNat + (p.randLen - used) ≤ 2 ^ 64
  ns : p.B.toNat + p.Z ≤ 2 ^ 64
  bits : 512 ≤ p.bits ∧ p.bits ≤ 8192
  len : p.len = (p.bits + 7) / 8
  gen : p.gen = 2 ∨ p.gen = 5
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  randLen : p.randLen < 2 ^ 64

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega_arith
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega_arith
    · omega_arith
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

theorem rA_sub (p : SPub) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, callSp_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem SLive.callFacts {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) : CallFacts p used := by
  have hi := h.input
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega_arith
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hb1, hb2, hl, hg, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨wor, -⟩, ⟨wur, -⟩, ⟨wsr, -⟩, -⟩ := hwr
  obtain ⟨bo, bu, bs, -, br, -⟩ := hstk
  obtain ⟨no, nu, ns, -, nr, -⟩ := hnw
  have hR : Region.Sub (rR (sOfState original) used) (inRand original) :=
    Offset.sub_base _ hroom
  have hA := rA_sub (sOfState original)
  have hsp' : (sOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  refine ⟨by rw [hsp']; exact hsp, pou, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wur.sub_right hR, pus, bu.symm.sub_right hA, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, no, nu, nowrap_tape nr hroom, ns, ⟨hb1, hb2⟩, hl, hg, ?_, ?_, BitVec.isLt _⟩
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [sOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

/-- The output and `used` are apart from the stack the search uses. -/
theorem SInput.outStack {p : SPub} {original : State} (hi : SInput p original) :
    (rO p).Disjoint (below p.sp stackUse) ∧ (rU p).Disjoint (below p.sp stackUse) := by
  obtain ⟨_, _, _, _, _, _, _, hstk, _, _, _, _, _, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append] at hstk
  obtain ⟨bo, bu, -⟩ := hstk
  exact ⟨bo.symm, bu.symm⟩

/-- The candidate's stack argument: `scratch_len`. -/
def callValues (p : SPub) : List (Nat × BitVec 64) := [(0, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SPub) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ rfl; show 0 < 16; decide

/-- The candidate's register arguments. -/
def SArgs (p : SPub) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.op ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.up ∧
  t.gpr .x3 = BitVec.ofNat 64 p.bits ∧ t.gpr .x4 = BitVec.ofNat 64 p.gen ∧
  t.gpr .x5 = p.rp + BitVec.ofNat 64 used ∧ t.gpr .x6 = BitVec.ofNat 64 (p.randLen - used) ∧
  t.gpr .x7 = p.B

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x11]

theorem search_arguments_ok {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block arguments) (allocated 16 s) fun u =>
      (SArgs p used u ∧ u.mem = writeController s.mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 16 s) u := by
  have a := h.access
  have hw0 : InRegions (⟨callSp p, 16⟩ :: s.wr) (callSp p) 8 :=
    ⟨⟨callSp p, 16⟩, List.mem_cons_self .., by
      simpa only [BitVec.add_zero] using Offset.contains_base (callSp p) (d := 0) (n := 8) (k := 16)
        (by decide) (by decide)⟩
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ ⟨callSp p, 16⟩ :: s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv5 := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.bits) (by simp [SPub.headers])
  have hv9 := h.header (j := 9) (v := BitVec.ofNat 64 p.gen) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv13 := h.header (j := 13) (v := p.B) (by simp [SPub.headers])
  have hv15 := h.header (j := 15) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv13 hv15
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold arguments writeController callValues SArgs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, allocated, h.sp, h.x19, exec_addSp (show 0 < 4096 by decide),
    hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide), hl 72 (by decide),
    hl 80 (by decide), hl 88 (by decide), hl 104 (by decide), hl 120 (by decide), hw0,
    hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv13, hv15]
  simp only [off, Nat.mul_zero, BitVec.add_zero]

/-- The regions the candidate reads: the tape's rest and its stack argument;
those it writes: `out`, `used` and the working space. -/
def callRd (p : SPub) (used : Nat) : List Region := [rR p used, rA p]
def callWr (p : SPub) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SPub) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callRd p used) (callWr p)

theorem call_gpr {p : SPub} {used : Nat} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callState p used u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_stackArg (p : SPub) (used : Nat) (u : State) (j : Nat) :
    stackArg (callState p used u) j = stackArg u j := rfl

theorem call_arg {p : SPub} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    stackArg u 0 = BitVec.ofNat 64 (p.Z / 8) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeController_word _ _ _ (callValues_bound p) 0 (by decide)

theorem callSp_toNat {p : SPub} (hf : 32 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 32 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
  simp only [BitVec.toNat_ofNat]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem gen_setWidth {g : Nat} (h : g = 2 ∨ g = 5) : ((BitVec.ofNat 64 g).setWidth 32).toNat = g := by
  rcases h with rfl | rfl <;> decide

theorem call_candidate_pre {p : SPub} {used : Nat} {u : State} {m : Mem} (hf : CallFacts p used)
    (hu : u.sp = callSp p) (ha : SArgs p used u)
    (hm : u.mem = writeController m (callSp p) (callValues p)) :
    pcPre (callState p used u) := by
  have h0 := call_arg hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have hb := hf.bits
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega_arith)
  have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega_arith)
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega_arith)
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 :=
    toNat_ofNat_lt (by have := hf.ns; omega_arith)
  have hsp := callSp_toNat hf.room
  have hlt := p.sp.isLt
  unfold pcPre
  simp only [call_gpr (by decide : Reg.x0 ∉ linkRegs), call_gpr (by decide : Reg.x1 ∉ linkRegs),
    call_gpr (by decide : Reg.x2 ∉ linkRegs), call_gpr (by decide : Reg.x3 ∉ linkRegs),
    call_gpr (by decide : Reg.x4 ∉ linkRegs), call_gpr (by decide : Reg.x5 ∉ linkRegs),
    call_gpr (by decide : Reg.x6 ∉ linkRegs), call_gpr (by decide : Reg.x7 ∉ linkRegs),
    call_stackArg, h0, r0, r1, r2, r3, r4, r5, r6, r7, hlen, hbits, hrl, hzw, hf.z8,
    gen_setWidth hf.gen, State.withRegions_rd, State.withRegions_wr, stackArgAddr, State.withRegions_sp,
    State.callEntry_sp, hu, Nat.mul_zero, BitVec.add_zero]
  exact ⟨by omega_arith, rfl, rfl, hf.ou, hf.or, hf.os, hf.oa, hf.ur, hf.us, hf.ua, hf.rs, hf.sa, hf.no, hf.nu,
    hf.nr, hf.ns, hb.1, hb.2, hf.len, hf.gen, hf.scratch⟩

/-- What the candidate at `used` leaves: its status, p or zeros at `out`,
and the octets it read at `used`. -/
def CandPost (p : SPub) (used : Nat) (t : State) : Prop :=
  let res := sievedParameterCandidate p.bits p.gen (p.rand.drop used)
  ((t.gpr .x0).setWidth 32).toNat = candidateStatus res ∧
    Spec.Rsa.bytesAt t.mem p.op p.len =
      (match res with
        | some (some q, _) => Spec.Rsa.i2osp q p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem p.up 1 =
      [BitVec.ofNat 64 (match res with
        | some (_, rest) => (p.randLen - used) - rest.length
        | none => 0)]

theorem CandPost.frame {p : SPub} {used : Nat} {s t : State} {F : Region}
    (h : CandPost p used s) (hf : Frame [F] s.mem t.mem)
    (ho : (rO p).Disjoint F) (hu : (rU p).Disjoint F)
    (hr : (t.gpr .x0).setWidth 32 = (s.gpr .x0).setWidth 32) : CandPost p used t := by
  have eo : Spec.Rsa.bytesAt t.mem p.op p.len = Spec.Rsa.bytesAt s.mem p.op p.len :=
    List.map_congr_left fun i hi => lost_byte hf ho (List.mem_range.mp hi)
  have eu : Spec.Rsa.wordsAt t.mem p.up 1 = Spec.Rsa.wordsAt s.mem p.up 1 := by
    refine List.map_congr_left fun i hi => ?_
    obtain rfl : i = 0 := by simpa using hi
    exact hf.readW (r := rU p) (Offset.contains_base _ (by decide) (by decide))
      (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact hu) (by decide)
  unfold CandPost at h ⊢
  rw [eo, eu, hr]
  exact h

section

variable {p : SPub} {original s : State} {used k : Nat}

theorem call_covers_writes (h : SLive p original used k s) {u : State}
    (hw : u.wr = (allocated 16 s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.1.2.2.2.1]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show (⟨p.op, p.len⟩ : Region) ∈ _; rw [← h.input.out_eq]; simp [inWrites]
  · show (⟨p.up, 8⟩ : Region) ∈ _; rw [← h.input.used_eq]; simp [inWrites]
  · rw [← h.input.2]; simp [inWrites, inScr, sOfState]

theorem call_covers_reads (h : SLive p original used k s)
    {u : State} (hrd : u.rd = (allocated 16 s).rd) (hw : u.wr = (allocated 16 s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  have hroom : used + (p.randLen - used) ≤ p.randLen := by have := h.used_le; omega_arith
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨⟨callSp p, 16⟩, ?_, 0, ?_, by show 0 + 8 ≤ 16; decide⟩
    · rw [hw]; refine List.mem_append_right _ ?_
      show _ ∈ (⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr)
      rw [h.sp]; exact List.mem_cons_self ..
    · rw [BitVec.add_zero]

/-- What the candidate writes, as the controller sees it. -/
theorem candidate_frame (h : SLive p original used k s) {u t : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p))
    (hf : Frame (callWr p) u.mem t.mem) :
    Frame (SInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  have hsp : p.sp = original.sp := hi.sp_eq
  have h1 : Frame (SInput.callChanges original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p) (size := 8) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl; show 8 * 0 + 8 ≤ 8; decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below original.sp stackUse, by simp [SInput.callChanges], ?_⟩
    rw [← hsp]
    exact rA_sub p
  have h2 : Frame (SInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inOut original, by simp [SInput.callChanges], by rw [hi.out_eq]; exact fun _ h => h⟩
    · exact ⟨inUsed original, by simp [SInput.callChanges], by rw [hi.used_eq]; exact fun _ h => h⟩
    · exact ⟨inScr original, by simp [SInput.callChanges], by rw [← hi.2]; exact fun _ h => h⟩
  exact h1.trans h2

/-- The candidate's view of the tape, at its entry. -/
theorem call_rand (h : SLive p original used k s) {u : State}
    (hm : u.mem = writeController s.mem (callSp p) (callValues p)) (ha : SArgs p used u) :
    pcRand (callState p used u) = p.rand.drop used := by
  have hfr : Frame (SInput.changes original) s.mem u.mem :=
    frame_of_callChanges original (candidate_frame (t := u) h hm (fun _ _ => rfl))
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := h.input.randLen_lt; omega_arith)
  simp only [pcRand, call_gpr (by decide : Reg.x5 ∉ linkRegs), call_gpr (by decide : Reg.x6 ∉ linkRegs),
    ha.2.2.2.2.2.1, ha.2.2.2.2.2.2.1, hrl, State.withRegions_mem, State.callEntry_mem]
  have hr := (h.input.random_frame hfr).trans h.random
  have hl := h.rand_length
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ (show used + (p.randLen - used) ≤ p.randLen by
    have := h.used_le; omega_arith), hr, List.take_of_length_le (by simp only [List.length_drop, hl]; omega_arith)]

theorem search_candidate_run (c : Cand) (h : SLive p original used k s) :
    WP isa (candidateRun c.call) s fun t => SLive p original used k t ∧ CandPost p used t := by
  have hf := h.callFacts
  have hroom' : 16 ≤ s.sp.toNat := by
    have := hf.room
    have h16 : (p.sp - BitVec.ofNat 64 16).toNat = p.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
      simp only [BitVec.toNat_ofNat]
    rw [h.sp, show (p.sp - 16 : Addr) = p.sp - BitVec.ofNat 64 16 from rfl, h16]
    omega_arith
  unfold candidateRun
  refine WP.alloc (by decide) hroom' ?_
  refine WP.seq (WP.mono (search_arguments_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := by rw [k.sp]; show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]
  refine WP.callV (k := ParameterCandidate.pcContract) c.correct (call_candidate_pre hf hu ha hm)
    (call_covers_reads h k.rd k.wr) (call_covers_writes h k.wr) ?_ c.noFrames
  intro t hrd hwr hsp hfr hcs _ hvs hpost m u f
  have hA : Region.Sub ⟨s.sp - BitVec.ofNat 64 16, 16⟩ (below p.sp stackUse) := by
    rw [h.sp, show (p.sp - 16 : Addr) - BitVec.ofNat 64 16 = callSp p from rfl, callSp_eq]
    exact Region.sub_prefix (by decide)
  have hA' : ∀ R ∈ [(⟨s.sp - BitVec.ofNat 64 16, 16⟩ : Region)],
      ∃ R' ∈ SInput.callChanges original, Region.Sub R R' := by
    intro R hR
    obtain rfl := List.mem_singleton.mp hR
    refine ⟨below original.sp stackUse, by simp [SInput.callChanges], ?_⟩
    rw [← h.input.sp_eq]
    exact hA
  refine ⟨?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (t := { freed 16 t with mem := m, unknowns := u }) (show (freed 16 t).rd = s.rd from hrd.trans k.rd)
      (show (freed 16 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.wr]; rfl)
    · change t.sp + BitVec.ofNat 64 16 = s.sp
      rw [hsp, k.sp]
      exact BitVec.sub_add_cancel _ _
    · intro r hr h30
      exact (hcs r hr h30).trans (k.gpr r (by revert r hr; decide))
    · intro r hr
      exact (hvs r hr).trans (k.vcs r hr)
    · exact (candidate_frame h hm hfr).trans (f.sub hA')
  · -- The candidate's status and outputs.
    refine CandPost.frame (s := t) ?_ f ((h.input.outStack).1.sub_right hA) ((h.input.outStack).2.sub_right hA) rfl
    have hrand := call_rand h hm ha
    obtain ⟨r0, r1, r2, r3, r4, -, r6, -⟩ := ha
    have hb := hf.bits
    have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := toNat_ofNat_lt (by have := hf.len; omega_arith)
    have hbits : (BitVec.ofNat 64 p.bits).toNat = p.bits := toNat_ofNat_lt (by omega_arith)
    have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
      toNat_ofNat_lt (by have := hf.randLen; omega_arith)
    have hp := hpost
    simp only [ParameterCandidate.pcContract, pcPost, pcResult, hrand, call_gpr (by decide : Reg.x0 ∉ linkRegs),
      call_gpr (by decide : Reg.x1 ∉ linkRegs), call_gpr (by decide : Reg.x2 ∉ linkRegs),
      call_gpr (by decide : Reg.x3 ∉ linkRegs), call_gpr (by decide : Reg.x4 ∉ linkRegs),
      call_gpr (by decide : Reg.x6 ∉ linkRegs), r0, r1, r2, r3, r4, r6, hlen, hbits, hrl,
      gen_setWidth hf.gen, State.withRegions_gpr, State.withRegions_mem] at hp
    exact hp

end

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # The parameter search's writes of its own words, and zeros at `out` (AArch64)

The terminal statuses and the exit for an exhausted bound
(`search_exhausted`); the zeroing of `out`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.Generation.Search
open VG.Impl.Bignum.AArch64 (movi)

namespace SInput

variable {p : SPub} {original : State}

theorem out_mem (h : SInput p original) : (⟨p.op, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.out_eq]; simp [inWrites]

theorem out_ctl (h : SInput p original) : (⟨p.op, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.out_eq, ← h.ctl_eq]
  exact this.1.2.2

end SInput

/-- The controller's word-only writes keep `out`. -/
theorem out_frame {p : SPub} {original : State} (hi : SInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.op p.len = Spec.Rsa.bytesAt m p.op p.len := by
  have hk := hi.len_bounds
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi' => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.out_ctl)
    (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi')

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.x10, .x11] s t := by
  rcases hst with rfl | rfl <;>
  refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, hb, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
      imm64 (show 3 < 65536 by decide), a.st0, a.st 0 (by decide), a.st 24 (by decide),
      a.st 112 (by decide)]
    rfl

/-- A terminal status written over a loop state, with no attempts left. -/
theorem terminal_live {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      SLive p original used 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (terminal_ok h.access h.x19 hst) fun t ⟨hm, k⟩ => ?_
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
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

/-- The words of a terminal status written over a loop state. -/
theorem terminal_words {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat}
    (hm : (j : Nat) → j < 16 → word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j))) :
    word t.mem p.control 112 = BitVec.ofNat 64 status ∧
      Spec.Rsa.wordsAt t.mem p.control 4 = [0, BitVec.ofNat 64 p.len,
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
theorem zero_frame {p : SPub} {original : State} (hinput : SInput p original) {m m' : Mem}
    (hf : ∀ x, (∀ j < p.len, x ≠ p.op + BitVec.ofNat 64 j) → m' x = m x) :
    Frame (SInput.callChanges original) m m' := by
  intro a ha
  apply hf
  intro i hi he
  have hk := hinput.len_bounds
  have hin : (⟨p.op, p.len⟩ : Region) ∈ SInput.callChanges original := by
    rw [← hinput.out_eq]; simp [SInput.callChanges]
  apply ha _ hin
  rw [he]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])

theorem search_zero_out {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa zeroOut s fun t =>
      SLive p original used k t ∧ Spec.Rsa.bytesAt t.mem p.op p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have scr := h.input.control_scr (t := s) h.wr
  have hv := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv hv6
  have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
  have hl6 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
  have hout : ∀ i < p.len, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact h.input.out_mem,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl, hl6, hv, hv6]) (by decide) (by decide)
      (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := p.len) (by omega_using [hk]) (by omega_using [hk]) (BInv s₁ p.op)
    (fun i hi t hI _ => bStep_ok (by omega_using [hk]) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  have hf : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
    fun x hx => by rw [hI.frame x hx, hm₁]
  have kk := k₁.trans hI.keep
  have hfr := zero_frame h.input hf
  refine ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs hfr, ?_,
    fun j hj => h.input.control_frame hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hI.bytes i (List.mem_range.mp hi)

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

end VG.Proof.Ffdh.AArch64.Generation
