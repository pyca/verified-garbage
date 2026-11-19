module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.SievedBounds
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-! ### `Ffdh.PPC64LE.Generation.Search.Data`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.Generation.Search.Contract`, which this module and modules that import it used -/

section

/-! # The parameter-search controller's contract in terms of the machine (PPC64LE)

`vg_ffdh_generate_parameters(out = r3, out_len = r4, used = r5,
bits = r6, generator = r7, rand = r8, rand_len = r9, scratch = r10,
scratch_len, state)`: eight arguments in registers and two on the stack. The
controller uses 336 bytes of stack: the frame of 48 bytes saving the link
register, its candidate's frame of 112 bytes, and the 176 bytes the
candidate may use below its own (`Cand.stack`).

The candidate reads RSA's table of trial division (`TrialTable32`), so the
controller reads it too: its region is the last it reads (`inTab`), and the
precondition states its entries. The contract under `abi.withConsts` states
the same (`Implies.lean`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (pcContract pcPre pcPub)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 336

/-- An implementation of `vg_ffdh_parameter_candidate_sieved`, as the controller
calls it: its name, its code, the stack it uses, and its proofs. -/
structure Cand where
  name : String
  code : Prog isa
  stack : sdepth code ≤ 176
  correct : ∀ s, pcContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pcContract.post s s'
  ct : ConstantTime isa pcPre pcPub code

/-- The candidate, as the controller calls it. -/
abbrev Cand.call (c : Cand) : Prog isa := .call c.name c.code

def inOut (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .r5, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 1, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩
/-- The table of trial division, where the state names it. -/
def inTab (s : State) : Region := ⟨s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inOut s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inRand s, inArgs s, inTab s]

/-- The width, the bits, the generator, the tape and the attempts on entry. -/
abbrev genLen (s : State) : Nat := (s.gpr .r4).toNat
abbrev genBits (s : State) : Nat := (s.gpr .r6).toNat
abbrev genGen (s : State) : Nat := ((s.gpr .r7).setWidth 32).toNat
abbrev genRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev genAttempts (s : State) : Nat := (s.mem.readW (stackArg s 1) 64).toNat

def searchPre (s : State) : Prop :=
  s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
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
    (s.gpr .r9).toNat ≤ parameterEntropy (genBits s) ∧
    VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) s.mem

def searchResult (s : State) : ParameterSearchResult :=
  sievedParameterSearch (genBits s) (genGen s) (genAttempts s) (genRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = (searchResult s).status ∧
    bytesAt t.mem (s.gpr .r3) (genLen s) =
      (match searchResult s with
        | .accepted p _ => i2osp p (genLen s)
        | _ => List.replicate (genLen s) 0) ∧
    wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    ∃ requested, wordsAt t.mem (stackArg s 1) 4 = [BitVec.ofNat 64 (searchResult s).remaining,
      BitVec.ofNat 64 (genLen s), BitVec.ofNat 64 (parameterEntropy (genBits s)),
      BitVec.ofNat 64 requested] ∧
      (searchResult s).Requests (parameterEntropy (genBits s)) requested

/-- What timing may depend on: the arguments, the tape, the controller's
public words and the table's address. -/
def searchPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (genRand s).map (·.toNat) = (genRand t).map (·.toNat) ∧
    wordsAt s.mem (stackArg s 1) 4 = wordsAt t.mem (stackArg t 1) 4 ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧
    (s.gpr .r7).setWidth 32 = (t.gpr .r7).setWidth 32 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 ∧
    s.gpr .r10 = t.gpr .r10 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! # The parameter search's public data, loop states and buffers (PPC64LE)

`SPub` is everything two constant-time runs share, the tape included; a
loop state (`SLive`) is at an offset into the tape with attempts left, in
the frame saving the link register, and the search from there (`SPub.tail`) is what the
controller returns.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh

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
  /-- The table of trial division. -/
  T : Addr

def sOfState (s : State) : SPub where
  op := s.gpr .r3
  up := s.gpr .r5
  rp := s.gpr .r8
  B := s.gpr .r10
  control := stackArg s 1
  sp := s.sp
  len := genLen s
  bits := genBits s
  gen := genGen s
  randLen := (s.gpr .r9).toNat
  Z := (stackArg s 0).toNat * 8
  attempts := genAttempts s
  rand := genRand s
  T := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol

def SInput (p : SPub) (s : State) : Prop := searchPre s ∧ sOfState s = p

/-- Words of memory at a base: word `j` holds `v` for each `(j, v)`. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

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

/-- A state of the loop, in the frame saving the link register: `used`
octets consumed, `k` attempts left. The entry state is functional-proof data
only: its callee-saved registers may hold secrets. -/
structure SLive (p : SPub) (original : State) (used k : Nat) (s : State) : Prop where
  input : SInput p original
  used_le : used ≤ p.randLen
  k_le : k ≤ p.attempts
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = p.sp - 48
  r31 : s.gpr .r31 = p.control
  saved : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = original.gpr r
  savedR31 : word s.mem p.control 32 = original.gpr .r31
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = p.rand
  headers : Slots s.mem p.control (p.headers used k)
  syms : s.syms = original.syms
  table : VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt p.T s.mem

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

/-- A finished search, before `finish` stores `used` and restores `r31`. -/
structure SDone (p : SPub) (original : State) (result : ParameterSearchResult) (s : State) : Prop where
  input : SInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  r31 : s.gpr .r31 = p.control
  saved : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = original.gpr r
  savedR31 : word s.mem p.control 32 = original.gpr .r31
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hr, -⟩ := h.1
  rw [← h.2]; exact hr

theorem randLen_lt (h : SInput p s) : p.randLen < 2 ^ 64 := by
  rw [← h.2]; exact BitVec.isLt _

theorem rand_length (h : SInput p s) : p.rand.length = p.randLen := by
  rw [← h.2]; simp only [sOfState, genRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem sp_eq (h : SInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem sp_room (h : SInput p s) : 336 ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

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

theorem table (h : SInput p s) : VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt p.T s.mem := by
  rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The table's entries survive writes the controller may make. -/
theorem table_frame (h : SInput p s) {m m' : Mem} (hf : Frame (changes s) m m')
    (ht : VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt p.T m) :
    VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt p.T m' := by
  have hn := h.nowrap (r := inTab s) (by simp [inReads])
  have hd := h.read_disjoint (r := inTab s) (by simp [inReads])
  rw [← h.2] at ht ⊢
  intro i hi
  rw [← ht i hi]
  exact hf.readW (r := inTab s) (Offset.contains_base _ (by simp only [inTab] at hn; omega_using [hn, hi])
    (by omega_using [hi])) hd (by decide)

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

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! # What keeps the parameter search's loop state (PPC64LE), and where the search goes -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
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

/-- Through code that keeps `r31`, the stack pointer, the regions, the
controller's words, and writes only the output, `used`, the working space
and the stack. -/
theorem restore (h : SLive p original used k s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (SInput.callChanges original) s.mem t.mem) (hy : t.syms = s.syms) :
    SLive p original used k t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.k_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun r hr h31 => (hg r hr).trans (h.saved r hr h31), ?_, ?_, ?_, hy.trans h.syms,
    h.input.table_frame hf' h.table⟩
  · exact (hc 4 (by decide)).trans h.savedR31
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (SPub.headers_index he)).trans (h.headers e he)

theorem keep (h : SLive p original used k s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hy : t.syms = s.syms)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SLive p original used k t := by
  apply h.restore kp.rd kp.wr kp.sp (fun reg hr => kp.gpr reg (hregs reg hr)) _ hy
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `r31`. -/
theorem update (h : SLive p original used k s) {u k' : Nat}
    (hu : u ≤ p.randLen) (hk : k' ≤ p.attempts)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t)
    (hh : Slots t.mem p.control (p.headers u k')) (hy : t.syms = s.syms) : SLive p original u k' t := by
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
    kp.sp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), ?_, ?_, hh, hy.trans h.syms,
    h.input.table_frame hf h.table⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR31
  · exact (h.input.random_frame hf).trans h.random

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : SLive p original used k s) {r : ParameterSearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : SOutput p r s.mem) : SDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.r31, h.saved, h.savedR31,
    h.header (j := 7) (by simp [SPub.headers]),
    by rw [hu]; exact h.header (j := 12) (by simp [SPub.headers]), hs, hp, ho⟩

end SLive

theorem SDone.keep {p : SPub} {original s t : State} {result : ParameterSearchResult}
    (h : SDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ (hregs .r31 (by decide))).trans h.r31,
    fun reg hr h31 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h31), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedR31
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

end VG.Proof.Ffdh.PPC64LE.Generation
