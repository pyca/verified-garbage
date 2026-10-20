module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore

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
    BitVec.ofNat 64 (parameterEntropy p.bits), BitVec.ofNat 64 result.requested]

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
  have := h.bits_bounds; have := h.len_eq; omega

theorem gen_eq (h : SInput p s) : p.gen = 2 ∨ p.gen = 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := h.1
  rw [← h.2]; exact hg

theorem attempts_le (h : SInput p s) : p.attempts ≤ parameterAttempts p.bits := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ha, -⟩ := h.1
  rw [← h.2]; exact ha

theorem attempts_lt (h : SInput p s) : p.attempts < 2 ^ 64 := by
  have ha := h.attempts_le
  have hb := h.bits_bounds
  have : parameterAttempts p.bits ≤ 8192 * 8192 * 64 := by
    unfold parameterAttempts
    exact Nat.mul_le_mul (Nat.mul_le_mul hb.2 hb.2) (Nat.le_refl _)
  omega

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
