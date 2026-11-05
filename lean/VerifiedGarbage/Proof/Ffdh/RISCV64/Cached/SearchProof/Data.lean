module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptFn
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Data
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.GenerationSearch
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The cached key-generation controller's contract, public data, loop states and writes (RISC-V)

As on PPC64LE (`Proof/Ffdh/PPC64LE/Cached/SearchProof/`): `keyContract` is
the controller on the machine; `KeyPublic` is everything two constant-time
runs share, the context's two arguments among them; a loop state (`KeyLive`)
is at an offset into the tape with budgets left, in the frame saving `ra`,
having written only the controller's buffers and its stack since the entry
(so the context is unchanged), and the search from there (`keyTail`) is what
the controller returns. Then the controller's writes of its own words, its
zeros at the outputs, and its tests of its budgets, its tape and the status.

`vg_ffdh_generate_key_search_cached(x = a0, x_len = a1, y = a2, y_len = a3,
used = a4, domain = a5, domain_len = a6, p_len = a7, rand, rand_len,
scratch, scratch_len, state, ctx, ctx_len)`: eight arguments in registers and
seven on the stack. The controller uses 64 bytes of stack: the frame of 16
bytes saving `ra` and its attempt's frame of 48 bytes; the attempt uses none
below its own (`Attempt.stack`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached.SearchProof

open VG VG.RISCV64 VG.Spec.Ffdh VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.RISCV64.KeyGeneration (tmpRegs CtlAccess zeroLoop_ok WP.ctl ofNat_pred eval_ltu eval_zero'
  ofNat_lt_ofNat)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  writeController_frame_size controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.RISCV64.KeyGeneration.Search

/-! ## The contract on the machine -/

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 64

/-- An implementation of `vg_ffdh_generate_key_cached`, as the controller calls it:
its name, its code, the stack it uses, and its proofs. -/
structure Attempt where
  name : String
  code : Prog isa
  stack : sdepth code = 0
  correct : ∀ s, cgContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ cgContract.post s s'
  ct : ConstantTime isa cgContract.pre cgContract.pub code

/-- The attempt, as the controller calls it. -/
abbrev Attempt.call (a : Attempt) : Prog isa := .call a.name a.code

def inX (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
def inY (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .a4, 8⟩
def inDom (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
def inRand (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 4, 128⟩
def inContext (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inX s, inY s, inUsed s, inScr s, inCtl s]
def inReads (s : State) : List Region := [inDom s, inRand s, inContext s, inArgs s]

/-- The width, the domain and the random octets on entry. -/
abbrev keyLen (s : State) : Nat := (s.gpr .a7).toNat
abbrev keyDom (s : State) : List Byte := bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat
abbrev keyRand (s : State) : List Byte := bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev keyA (s : State) : Parameters := domainOf (keyLen s) (keyDom s)
abbrev keyRetries (s : State) : KeyRetries :=
  ⟨(s.mem.readW (stackArg s 4) 64).toNat, (s.mem.readW (stackArg s 4 + 8) 64).toNat⟩

def keyPre (s : State) : Prop :=
  s.sp.toNat + 8 * 7 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    (s.gpr .a4).toNat % 8 = 0 ∧ (stackArg s 2).toNat % 8 = 0 ∧ (stackArg s 4).toNat % 8 = 0 ∧
    pLenValid (keyLen s) ∧ domainLenValid (keyLen s) (s.gpr .a6).toNat ∧
    (s.gpr .a1).toNat = keyLen s ∧ (s.gpr .a3).toNat = keyLen s ∧
    Spec.Rsa.scratchWords (keyLen s) ≤ (stackArg s 3).toNat ∧
    domainValid (keyLen s) (keyDom s) ∧
    (s.mem.readW (stackArg s 4) 64).toNat ≤ 128 ∧
    (s.mem.readW (stackArg s 4 + 8) 64).toNat ≤ 128 ∧
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) ∧
    (stackArg s 6).toNat = generationPrecomputedWords (keyLen s) ∧
    generationPrecompute (keyLen s) (keyDom s) = some (wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat) ∧
    (stackArg s 5).toNat % 8 = 0

def keyResult (s : State) : KeySearchResult :=
  vettedKeySearch (keyA s) (keyLen s) (keyRetries s) (keyRand s)

def keyPost (s t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = (keyResult s).status ∧
    (match (keyResult s).outcome with
      | .accepted sx sy => bytesAt t.mem (s.gpr .a0) (keyLen s) = i2osp sx (keyLen s) ∧
          bytesAt t.mem (s.gpr .a2) (keyLen s) = i2osp sy (keyLen s)
      | _ => bytesAt t.mem (s.gpr .a0) (keyLen s) = List.replicate (keyLen s) 0 ∧
          bytesAt t.mem (s.gpr .a2) (keyLen s) = List.replicate (keyLen s) 0) ∧
    wordsAt t.mem (stackArg s 4) 4 = [BitVec.ofNat 64 (keyResult s).retries.keys,
      BitVec.ofNat 64 (keyResult s).retries.scalars, BitVec.ofNat 64 (keyLen s),
      BitVec.ofNat 64 (if (keyResult s).status = 0 then keyLen s else 0)] ∧
    wordsAt t.mem (s.gpr .a4) 1 = [BitVec.ofNat 64 (keyResult s).used]

/-- What timing may depend on: the arguments but the random octets, the
domain, the controller's public words and the attempts' statuses. -/
def keyPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (∀ r ∈ argRegs, s.gpr r = t.gpr r) ∧
    (∀ j < 7, stackArg s j = stackArg t j) ∧
    keyDom s = keyDom t ∧ wordsAt s.mem (stackArg s 4) 4 = wordsAt t.mem (stackArg t 4) 4 ∧
    (keyResult s).statuses = (keyResult t).statuses

def keyContract : Contract isa where
  pre := keyPre
  post := keyPost
  pub := keyPub

/-! ## The public data -/

structure KeyPublic where
  xp : Addr
  yp : Addr
  up : Addr
  dp : Addr
  rp : Addr
  B : Addr
  control : Addr
  sp : Addr
  len : Nat
  dlen : Nat
  randLen : Nat
  Z : Nat
  keys : Nat
  scalars : Nat
  dom : List Byte
  ctx : Addr
  ctxLen : Nat

def keyOfState (s : State) : KeyPublic where
  xp := s.gpr .a0
  yp := s.gpr .a2
  up := s.gpr .a4
  dp := s.gpr .a5
  rp := stackArg s 0
  B := stackArg s 2
  control := stackArg s 4
  sp := s.sp
  len := keyLen s
  dlen := (s.gpr .a6).toNat
  randLen := (stackArg s 1).toNat
  Z := (stackArg s 3).toNat * 8
  keys := (keyRetries s).keys
  scalars := (keyRetries s).scalars
  dom := keyDom s
  ctx := stackArg s 5
  ctxLen := (stackArg s 6).toNat

/-- The domain's parameters. -/
abbrev KeyPublic.a (p : KeyPublic) : Parameters := domainOf p.len p.dom

def KeyInput (p : KeyPublic) (s : State) : Prop := keyPre s ∧ keyOfState s = p

/-- The search from octet `used` of `rand`, with `keys` and `scalars` left. -/
abbrev KeyPublic.tail (p : KeyPublic) (rand : List Byte) (used keys scalars : Nat) : KeySearchResult :=
  keyTail .cached p.a p.len rand used keys scalars

/-- Words of memory at a base: word `j` holds `v` for each `(j, v)`. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

/-- The controller's words while it searches. -/
def KeyPublic.headers (p : KeyPublic) (used keys scalars : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 keys), (1, BitVec.ofNat 64 scalars), (2, BitVec.ofNat 64 p.len),
    (5, p.xp), (6, p.yp), (7, p.dp), (8, BitVec.ofNat 64 p.dlen),
    (9, p.rp + BitVec.ofNat 64 used), (10, BitVec.ofNat 64 (p.randLen - used)),
    (11, BitVec.ofNat 64 used), (12, p.B), (13, BitVec.ofNat 64 (p.Z / 8)), (15, p.up)]

theorem KeyPublic.headers_bound (p : KeyPublic) (used keys scalars : Nat) :
    ∀ e ∈ p.headers used keys scalars, e.1 < 16 := by
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> decide

theorem KeyPublic.headers_index {p : KeyPublic} {used keys scalars : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used keys scalars) : e.1 < 16 := p.headers_bound used keys scalars e he

/-- A state of the loop, in the frame saving `ra`: `used` octets consumed,
`keys` and `scalars` left. The entry state is functional-proof data only:
its callee-saved registers may hold secrets, and its tape is secret. -/
structure KeyLive (p : KeyPublic) (original : State) (used keys scalars : Nat) (s : State) : Prop where
  input : KeyInput p original
  used_le : used ≤ p.randLen
  keys_le : keys ≤ 128
  scalars_le : scalars ≤ 128
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = p.sp - 16
  s0 : s.gpr .s0 = p.control
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  savedS0 : word s.mem p.control 32 = original.gpr .s0
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = keyRand original
  domain : Spec.Rsa.bytesAt s.mem p.dp p.dlen = p.dom
  headers : Slots s.mem p.control (p.headers used keys scalars)
  frame : Frame (inWrites original ++ [below original.sp stackUse]) original.mem s.mem

/-- The outputs of a finished search. -/
def KeyOutput (p : KeyPublic) (result : KeySearchResult) (m : Mem) : Prop :=
  match result.outcome with
  | .accepted sx sy => Spec.Rsa.bytesAt m p.xp p.len = Spec.Rsa.i2osp sx p.len ∧
      Spec.Rsa.bytesAt m p.yp p.len = Spec.Rsa.i2osp sy p.len
  | _ => Spec.Rsa.bytesAt m p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt m p.yp p.len = List.replicate p.len 0

/-- The controller's four public words for a finished search. -/
def KeyPublic.policy (p : KeyPublic) (result : KeySearchResult) : List (BitVec 64) :=
  [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
    BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)]

/-- A finished search, before `finish` stores `used` and restores `s0`. -/
structure KeyDone (p : KeyPublic) (original : State) (result : KeySearchResult) (s : State) : Prop where
  input : KeyInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  s0 : s.gpr .s0 = p.control
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  savedS0 : word s.mem p.control 32 = original.gpr .s0
  usedPtr : word s.mem p.control 120 = p.up
  used : word s.mem p.control 88 = BitVec.ofNat 64 result.used
  status : word s.mem p.control 112 = BitVec.ofNat 64 result.status
  policy : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy result
  output : KeyOutput p result s.mem

/-! ## Where the buffers are -/

namespace KeyInput

variable {p : KeyPublic} {s : State}

theorem nowrap (h : KeyInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.2.1 r hr

theorem write_disjoint (h : KeyInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : KeyInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : KeyInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.2.1

theorem rd_eq (h : KeyInput p s) : s.rd = inReads s := h.1.2.2.2.1

theorem wr_eq (h : KeyInput p s) : s.wr = inWrites s := h.1.2.2.2.2.1

theorem len_eq (h : KeyInput p s) : p.len = keyLen s := by rw [← h.2]; rfl

theorem len_bounds (h : KeyInput p s) : 64 ≤ p.len ∧ p.len ≤ 1024 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := h.1
  rw [h.len_eq]; exact hv

theorem len_lt (h : KeyInput p s) : p.len < 2 ^ 31 := by
  have := h.len_bounds.2; omega

theorem sp_eq (h : KeyInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem sp_room (h : KeyInput p s) : 64 ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem sp_al (h : KeyInput p s) : p.sp.toNat % 16 = 0 := by rw [h.sp_eq]; exact h.1.2.2.1

theorem up_al (h : KeyInput p s) : p.up.toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hu, -⟩ := h.1
  rw [← h.2]; exact hu

theorem B_al (h : KeyInput p s) : p.B.toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -⟩ := h.1
  rw [← h.2]; exact hb

theorem control_al (h : KeyInput p s) : p.control.toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := h.1
  rw [← h.2]; exact hc

theorem control_scr (h : KeyInput p s) {t : State} (hw : t.wr = s.wr) : Scr t p.control 128 := by
  refine Scr.of_mem (by rw [hw, h.wr_eq, ← h.2]; simp [inWrites, inCtl, keyOfState]) ?_ h.control_al
  rw [← h.2]
  exact h.nowrap (r := inCtl s) (by simp [inWrites])

/-- The regions the controller (and its callee) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below s.sp stackUse]

theorem read_disjoint (h : KeyInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem bytes_frame (h : KeyInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega_using [hn]) (List.mem_range.mp hi)

theorem random_frame (h : KeyInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

theorem domain_frame (h : KeyInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.dp p.dlen = Spec.Rsa.bytesAt m p.dp p.dlen := by
  rw [← h.2]
  exact h.bytes_frame (r := inDom s) (by simp [inReads]) hf

/-- The writes but the controller's words. -/
def callChanges (s : State) : List Region :=
  [inX s, inY s, inUsed s, inScr s, below s.sp stackUse]

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  refine ⟨r, ?_, fun _ hi => hi⟩
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [changes, inWrites]

theorem control_frame (h : KeyInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 16) : word m' p.control (8 * j) = word m p.control (8 * j) := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  rw [← h.2]
  refine hf.readW (r := inCtl s) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    (fun r hr => ?_) (by decide)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hpw.1.2.2.2.symm
  · exact hpw.2.1.2.2.symm
  · exact hpw.2.2.1.2.symm
  · exact hpw.2.2.2.1.symm
  · exact (h.stack_disjoint (r := inCtl s) (by simp [inWrites])).symm

theorem domain_valid (h : KeyInput p s) : Spec.Ffdh.domainValid p.len p.dom := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := h.1
  rw [← h.2]; exact hv

theorem keys_le (h : KeyInput p s) : p.keys ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h.1
  rw [← h.2]; exact hk

theorem scalars_le (h : KeyInput p s) : p.scalars ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ := h.1
  rw [← h.2]; exact hs

theorem width_word (h : KeyInput p s) :
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -⟩ := h.1
  exact hw

end KeyInput

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (KeyInput.callChanges s) m m') :
    Frame (KeyInput.changes s) m m' := hf.sub (KeyInput.callChanges_sub s)

/-! ## What keeps a loop state -/

namespace KeyLive

variable {p : KeyPublic} {original s t : State} {used keys scalars : Nat}

theorem access (h : KeyLive p original used keys scalars s) : CtlAccess s p.control :=
  CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)

theorem header (h : KeyLive p original used keys scalars s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used keys scalars) : word s.mem p.control (8 * j) = v :=
  h.headers (j, v) hj

theorem rand_length (h : KeyLive p original used keys scalars s) : (keyRand original).length = p.randLen := by
  rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]

/-- Through code that keeps `s0`, the stack pointer, the regions, the
controller's words, and writes only the outputs, `used`, the working space
and the stack. -/
theorem restore (h : KeyLive p original used keys scalars s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (KeyInput.callChanges original) s.mem t.mem) :
    KeyLive p original used keys scalars t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .s0 (by decide)).trans h.s0,
    fun r hr h0 => (hg r hr).trans (h.saved r hr h0), ?_, ?_, ?_, ?_, h.frame.trans hf'⟩
  · exact (hc 4 (by decide)).trans h.savedS0
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.domain_frame hf').trans h.domain
  · intro e he
    exact (hc e.1 (KeyPublic.headers_index he)).trans (h.headers e he)

theorem keep (h : KeyLive p original used keys scalars s) {rs : List Reg}
    (k : Keep rs s t) (hsp : t.sp = s.sp) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    KeyLive p original used keys scalars t := by
  apply h.restore k.2.1 k.2.2 hsp (fun reg hr => k.gpr (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `s0`, to the
counters `u`, `k` and `c`. -/
theorem update (h : KeyLive p original used keys scalars s) {u k c : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ 128) (hc : c ≤ 128)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep tmpRegs s t) (hsp : t.sp = s.sp)
    (hh : Slots t.mem p.control (p.headers u k c)) : KeyLive p original u k c t := by
  have hf : Frame (KeyInput.changes original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [KeyInput.changes, inWrites], ?_⟩
    rw [← h.input.2]
    exact fun _ hi => hi
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr (by revert r hr; decide)
  refine ⟨h.input, hu, hk, hc, kp.2.1.trans h.rd, kp.2.2.trans h.wr,
    hsp.trans h.sp, (hg .s0 (by decide)).trans h.s0,
    fun reg hreg h0 => (hg reg hreg).trans (h.saved reg hreg h0), ?_, ?_, ?_, hh, h.frame.trans hf⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedS0
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.domain_frame hf).trans h.domain

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : KeyLive p original used keys scalars s) {r : KeySearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : KeyOutput p r s.mem) : KeyDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.s0, h.saved, h.savedS0,
    h.header (j := 15) (by simp [KeyPublic.headers]),
    by rw [hu]; exact h.header (j := 11) (by simp [KeyPublic.headers]), hs, hp, ho⟩

end KeyLive

theorem KeyDone.keep {p : KeyPublic} {original s t : State} {result : KeySearchResult}
    (h : KeyDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : KeyDone p original result t := by
  refine ⟨h.input, k.2.1.trans h.rd, k.2.2.trans h.wr, (k.gpr (hregs .s0 (by decide))).trans h.s0,
    fun reg hr h0 => (k.gpr (hregs reg hr)).trans (h.saved reg hr h0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedS0
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

/-- A finished search's state depends on its result's outcome and octets
consumed, not on its statuses. -/
theorem KeyDone.congr {p : KeyPublic} {original s : State} {r r' : KeySearchResult}
    (h : KeyDone p original r s) (ho : r.outcome = r'.outcome) (hu : r.used = r'.used) :
    KeyDone p original r' s := by
  have hs : r.status = r'.status := by unfold KeySearchResult.status; rw [ho]
  have hr : r.retries = r'.retries := by unfold KeySearchResult.retries; rw [ho]
  refine ⟨h.input, h.rd, h.wr, h.s0, h.saved, h.savedS0, h.usedPtr,
    by rw [← hu]; exact h.used, by rw [← hs]; exact h.status, ?_, ?_⟩
  · rw [h.policy]; unfold KeyPublic.policy; rw [hs, hr]
  · have ho' := h.output; unfold KeyOutput at ho' ⊢; rw [← ho]; exact ho'

/-! ## Where the attempt's buffers are

The attempt's buffers are the controller's (`x`, `y`, the domain, a slice
of the tape, the context and the working space), and its stack arguments are at the base
of the attempt's frame, in the 64 bytes of stack below the controller's stack
pointer on entry, which no buffer overlaps. -/

/-- The stack pointer in the attempt's frame. -/
abbrev callSp (p : KeyPublic) : Addr := p.sp - 16 - BitVec.ofNat 64 48

theorem callSp_eq (p : KeyPublic) : callSp p = p.sp - BitVec.ofNat 64 64 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The attempt's regions: its outputs, the domain, the tape's slice, the
working space and its arguments. -/
abbrev rX (p : KeyPublic) : Region := ⟨p.xp, p.len⟩
abbrev rY (p : KeyPublic) : Region := ⟨p.yp, p.len⟩
abbrev rD (p : KeyPublic) : Region := ⟨p.dp, p.dlen⟩
abbrev rR (p : KeyPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.len⟩
abbrev rS (p : KeyPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : KeyPublic) : Region := ⟨callSp p, 40⟩

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  room : 64 ≤ p.sp.toNat
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rD p)
  xr : (rX p).Disjoint (rR p used)
  xs : (rX p).Disjoint (rS p)
  xa : (rX p).Disjoint (rA p)
  yd : (rY p).Disjoint (rD p)
  yr : (rY p).Disjoint (rR p used)
  ys : (rY p).Disjoint (rS p)
  ya : (rY p).Disjoint (rA p)
  ds : (rD p).Disjoint (rS p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  nx : p.xp.toNat + p.len ≤ 2 ^ 64
  ny : p.yp.toNat + p.len ≤ 2 ^ 64
  nd : p.dp.toNat + p.dlen ≤ 2 ^ 64
  nr : (p.rp + BitVec.ofNat 64 used).toNat + p.len ≤ 2 ^ 64
  ns : p.B.toNat + p.Z ≤ 2 ^ 64
  len : Spec.Ffdh.pLenValid p.len
  dlen : Spec.Ffdh.domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  len64 : p.len < 2 ^ 64
  dlen64 : p.dlen < 2 ^ 64
  bal : p.B.toNat % 8 = 0
  spal : (callSp p).toNat % 16 = 0

private theorem sub_tape {r : Addr} {n used len : Nat}
    (hu : used + len ≤ n) : Region.Sub ⟨r + BitVec.ofNat 64 used, len⟩ ⟨r, n⟩ :=
  Offset.sub_base r hu

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega
    · omega
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

theorem rA_sub (p : KeyPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, callSp_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem callSp_toNat {p : KeyPublic} (hf : 64 ≤ p.sp.toNat) : (callSp p).toNat = p.sp.toNat - 64 := by
  rw [callSp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]

theorem KeyLive.callFacts {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    CallFacts p used := by
  have hi := h.input
  have hspal := hi.sp_al
  have hbal := hi.B_al
  obtain ⟨_, hsp, _, _, _, hnw, hpw, hwr, hstk, _, _, _, hlen, hdlen, hx1, hx3, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pxy, pxu, pxs, pxc⟩, ⟨pyu, pys, pyc⟩, ⟨pus, puc⟩, psc⟩ := hpw
  obtain ⟨⟨wxd, wxr, -, wxa⟩, ⟨wyd, wyr, -, wya⟩, -, ⟨wsd, wsr, -, wsa⟩, -⟩ := hwr
  obtain ⟨bx, by', -, bs, -, bd, br, -⟩ := hstk
  obtain ⟨nx, ny, -, ns, -, nd, nr, -⟩ := hnw
  have hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hx1]
  have hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hx3]
  have hD : rD (keyOfState original) = inDom original := rfl
  have hS : rS (keyOfState original) = inScr original := rfl
  have hR : Region.Sub (rR (keyOfState original) used) (inRand original) :=
    sub_tape hroom
  have hA := rA_sub (keyOfState original)
  have hsp' : (keyOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  rw [← hX] at pxy pxs wxd wxr bx nx
  rw [← hY] at pxy pys wyd wyr by' ny
  rw [← hD] at wxd wyd wsd bd nd
  rw [← hS] at pxs pys wsd wsr bs ns
  refine ⟨by rw [hsp']; exact hsp, pxy, wxd, wxr.sub_right hR, pxs, (bx.symm.sub_right hA),
    wyd, wyr.sub_right hR, pys, by'.symm.sub_right hA, wsd.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, nx, ny, nd, nowrap_tape nr hroom, ns, hlen, hdlen, ?_, ?_, ?_, ?_, hbal, ?_⟩
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  · exact BitVec.isLt _
  · exact BitVec.isLt _
  · rw [callSp_toNat (by rw [hsp']; exact hsp)]
    have : 64 ≤ (keyOfState original).sp.toNat := by rw [hsp']; exact hsp
    omega

/-! ## Zeros at the outputs -/

namespace KeyInput

variable {p : KeyPublic} {original : State}

theorem x_eq (h : KeyInput p original) : inX original = ⟨p.xp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hx1, -, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inX, keyOfState, hx1]

theorem y_eq (h : KeyInput p original) : inY original = ⟨p.yp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hx3, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inY, keyOfState, hx3]

theorem x_mem (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.x_eq]; simp [inWrites]

theorem y_mem (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.y_eq]; simp [inWrites]

theorem xy_disjoint (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.yp, p.len⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.x_eq, ← h.y_eq]
  exact this.1.1

theorem x_ctl (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  have := hpw.1.2.2.2
  rwa [h.x_eq, show inCtl original = ⟨p.control, 128⟩ by rw [← h.2]; rfl] at this

theorem y_ctl (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  have := hpw.2.1.2.2
  rwa [h.y_eq, show inCtl original = ⟨p.control, 128⟩ by rw [← h.2]; rfl] at this

theorem x_ne_ctl (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have d := h.x_ctl
  rw [show (⟨p.control, 128⟩ : Region) = inCtl original by rw [← h.2]; rfl, ← he] at d
  have hl := h.len_bounds
  exact d p.xp (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

theorem y_ne_ctl (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have d := h.y_ctl
  rw [show (⟨p.control, 128⟩ : Region) = inCtl original by rw [← h.2]; rfl, ← he] at d
  have hl := h.len_bounds
  exact d p.yp (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

end KeyInput

/-- A zeroing of an output changes memory only there. -/
theorem zero_frame {p : KeyPublic} {original : State} {m m' : Mem}
    {o : Addr} (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original)
    (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original) (hf : Mont.Outside o 0 p.len m m') :
    Frame (KeyInput.callChanges original) m m' := by
  intro a ha
  refine hf a (Or.inr ?_)
  have hin : (⟨o, p.len⟩ : Region) ∈ KeyInput.callChanges original := by
    simp only [inWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [KeyInput.callChanges, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with h' | h' | h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inr (.inr (.inl h')))
    · exact absurd h' hrc
  have := ha _ hin
  simp only [Region.Contains, Mont.ofs] at this ⊢
  omega

/-- `zeroOut j`: zeros at the output whose pointer is in word `j`. -/
theorem key_zero_out {p : KeyPublic} {original s : State} {used keys scalars j : Nat} {o : Addr}
    (h : KeyLive p original used keys scalars s) (hj56 : j = 5 ∨ j = 6)
    (hj : (j, o) ∈ p.headers used keys scalars)
    (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original) (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original) :
    WP isa (zeroOut j) s fun t =>
      KeyLive p original used keys scalars t ∧ (∀ i < p.len, t.mem (off o i) = 0) ∧
      Mont.Outside o 0 p.len s.mem t.mem := by
  have hk := h.input.len_bounds
  have a := h.access
  have hv := h.header hj
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word] at hv hv2
  have hno : o.toNat + p.len ≤ 2 ^ 64 := h.input.nowrap (List.mem_append_left _ hr)
  have hout : ∀ i < p.len, InRegions s.wr (off o i) 1 := fun i hi =>
    ⟨⟨o, p.len⟩, by rw [h.wr, h.input.wr_eq]; exact hr,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  simp only [Nat.reduceMul] at hv2
  rcases hj56 with rfl | rfl <;> simp only [Nat.reduceMul] at hv <;>
  · unfold zeroOut
    refine WP.seq (WP.mono (WP.rdwr (WP.keep [.t0, .t1, .t2] (Q := fun t => t.gpr .t0 = o ∧
        t.gpr .t1 = BitVec.ofNat 64 p.len ∧ t.gpr .t2 = 0 ∧ t.mem = s.mem) (by
      brun [ldf, h.s0, hv, hv2, a.ld 40 (by decide), a.ld 48 (by decide), a.ld 16 (by decide),
        a.al 40 (by decide) (by decide), a.al 48 (by decide) (by decide), a.al 16 (by decide) (by decide),
        fin64_exec_li_zero]) (by rfl)))
      fun s₁ ⟨⟨⟨h3, h4, h5, hm₁⟩, k₁⟩, _, _, hsp₁⟩ => ?_)
    refine WP.mono (WP.rdwr (zeroLoop_ok (by omega) (by omega) (fun i hi => by rw [k₁.2.2]; exact hout i hi)
      h3 h4 h5)) fun t ⟨⟨⟨tb, tout⟩, kt⟩, _, _, hspt⟩ => ?_
    have kk := k₁.trans kt
    have tout' : Mont.Outside o 0 p.len s.mem t.mem := by rw [← hm₁]; exact tout
    exact ⟨h.restore kk.2.1 kk.2.2 (hspt.trans hsp₁) (fun r hr => kk.gpr (by revert r hr; decide))
      (zero_frame hr hrc tout'), tb, tout'⟩

/-- Zeros at `x` and `y`, which keeps the controller's words. -/
theorem key_zero_outputs {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa zeroOutputs s fun t =>
      KeyLive p original used keys scalars t ∧
      Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have hxw := h.input.x_mem
  have hyw := h.input.y_mem
  have hxc := h.input.x_ne_ctl
  have hyc := h.input.y_ne_ctl
  unfold zeroOutputs
  refine WP.seq (WP.mono (key_zero_out h (j := 5) (.inl rfl) (by simp [KeyPublic.headers]) hxw hxc)
    fun v ⟨hv, hbv, hfv⟩ => ?_)
  refine WP.mono (key_zero_out hv (j := 6) (.inr rfl) (by simp [KeyPublic.headers]) hyw hyc)
    fun t ⟨ht, hbt, hft⟩ => ?_
  have hxy := h.input.xy_disjoint
  have hk64 : p.len < 2 ^ 64 := by omega
  refine ⟨ht, ?_, ?_, ?_⟩
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' := List.mem_range.mp hi
    rw [hft _ (Or.inr ?_)]
    · exact hbv i hi'
    · by_contra hc
      exact hxy _ (Offset.contains_base _ (d := i) (n := 1) (by omega) (by omega))
        (by simp only [Region.Contains]; simp only [Mont.ofs] at hc; omega)
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hbt i (List.mem_range.mp hi)
  · intro j hj
    have hf := (zero_frame hxw hxc hfv).trans (zero_frame hyw hyc hft)
    exact h.input.control_frame hf j hj

/-! ## The controller's writes of its own words

The terminal statuses, the request for entropy, the rejections, and the
octets an attempt consumes; the exits without a key (`key_exhausted`,
`key_request`). -/

/-- The controller's words after writes of `values`. -/
theorem headers_after {p : KeyPublic} {s t : State} (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 16) (hm : t.mem = writeController s.mem p.control values)
    {used' keys' scalars' : Nat}
    (hv : ∀ e ∈ p.headers used' keys' scalars',
      controllerValue values e.1 (word s.mem p.control (8 * e.1)) = e.2) :
    Slots t.mem p.control (p.headers used' keys' scalars') := by
  intro e he
  rw [hm, writeController_word _ _ _ hb e.1 (KeyPublic.headers_index he)]
  exact hv e he

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (1, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .s0 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep tmpRegs s t ∧ t.sp = s.sp := by
  rcases hst with rfl | rfl <;>
  refine WP.ctl ?_ (by rfl) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [stf, hb, a.st 0 (by decide), a.st 8 (by decide), a.st 24 (by decide), a.st 112 (by decide),
      a.al 0 (by decide) (by decide), a.al 8 (by decide) (by decide), a.al 24 (by decide) (by decide),
      a.al 112 (by decide) (by decide), fin64_exec_li_zero]

/-- A terminal status written over a loop state, with no budgets left. -/
theorem key_terminal_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      KeyLive p original used 0 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (key_terminal_ok h.access h.s0 hst) fun t ⟨hm, k, hsp⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used 0 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update (u := used) (k := 0) (c := 0) h.used_le (by decide) (by decide) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm k hsp hh, hm⟩

theorem key_exhausted {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa exhausted s (KeyDone p original ⟨.exhausted, used, []⟩) := by
  unfold exhausted
  refine WP.seq (WP.mono (key_terminal_live h (status := 3) (.inr rfl)) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (key_zero_outputs ht) fun u ⟨hu, hx, hy, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) (v : BitVec 64) (hv : controllerValue (terminalValues 3) j
      (word s.mem p.control (8 * j)) = v) : word u.mem p.control (8 * j) = v := by
    rw [hc j hj, hm, writeController_word _ _ _ (terminalValues_bound 3) j hj, hv]
  refine hu.done rfl (hw 14 (by decide) _ (by
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]; rfl)) ?_ ⟨hx, hy⟩
  change [word u.mem p.control (8 * 0), word u.mem p.control (8 * 1), word u.mem p.control (8 * 2),
    word u.mem p.control (8 * 3)] = _
  rw [hw 0 (by decide) 0 (by
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false]),
    hw 1 (by decide) 0 (by
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false]),
    hw 3 (by decide) 0 (by
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false]),
    hc 2 (by decide), hm, writeController_word _ _ _ (terminalValues_bound 3) 2 (by decide)]
  simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_false]
  rw [h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])]
  rfl

def requestValues (p : KeyPublic) : List (Nat × BitVec 64) := [(3, BitVec.ofNat 64 p.len), (14, 0)]

theorem requestValues_bound (p : KeyPublic) : ∀ e ∈ requestValues p, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem key_request_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .t1 2, .li .t2 0, stf .t1 3, stf .t2 14]) s fun t =>
      KeyLive p original used keys scalars t ∧ t.mem = writeController s.mem p.control (requestValues p) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2
  refine WP.mono (WP.ctl (Q := fun t =>
    t.mem = writeController s.mem p.control (requestValues p)) ?_ (by rfl)) fun t ⟨hm, k, hsp⟩ => ?_
  · unfold writeController requestValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.s0, hv2, a.ld 16 (by decide), a.al 16 (by decide) (by decide),
      a.st 24 (by decide), a.st 112 (by decide), a.al 24 (by decide) (by decide),
      a.al 112 (by decide) (by decide), fin64_exec_li_zero]
  have hh : Slots t.mem p.control (p.headers used keys scalars) := by
    refine headers_after _ (requestValues_bound p) hm ?_
    intro e he
    rw [controllerValue_unchanged _ _ _ (by
      intro x hx
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases hx with rfl | rfl <;>
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> decide)]
    exact h.headers e he
  refine ⟨h.update h.used_le h.keys_le h.scalars_le _ (requestValues_bound p) (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k hsp hh, hm⟩

theorem key_request {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa request s (KeyDone p original ⟨.entropy ⟨keys, scalars⟩, used, []⟩) := by
  unfold request
  refine WP.seq (WP.mono (key_request_live h) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (key_zero_outputs ht) fun u ⟨hu, hx, hy, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) : word u.mem p.control (8 * j) =
      controllerValue (requestValues p) j (word s.mem p.control (8 * j)) := by
    rw [hc j hj, hm, writeController_word _ _ _ (requestValues_bound p) j hj]
  refine hu.done rfl (by
    rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]; rfl) ?_ ⟨hx, hy⟩
  change [word u.mem p.control (8 * 0), word u.mem p.control (8 * 1), word u.mem p.control (8 * 2),
    word u.mem p.control (8 * 3)] = _
  rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
  simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]
  rw [h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers]),
    h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers]),
    h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])]
  rfl

def scalarValues (scalars : Nat) : List (Nat × BitVec 64) :=
  [(1, BitVec.ofNat 64 (scalars - 1)), (14, 4)]

def publicValues (keys : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (keys - 1)), (1, 128), (14, 4)]

theorem scalarValues_bound (scalars : Nat) : ∀ e ∈ scalarValues scalars, e.1 < 16 := by
  simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem publicValues_bound (keys : Nat) : ∀ e ∈ publicValues keys, e.1 < 16 := by
  simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_rejected_scalar {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : 0 < scalars) :
    WP isa (.block rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv1
  have e1 := ofNat_pred hs (by have := h.scalars_le; omega)
  refine WP.mono (WP.ctl (Q := fun t =>
    t.mem = writeController s.mem p.control (scalarValues scalars)) ?_ (by rfl)) fun t ⟨hm, k, hsp⟩ => ?_
  · unfold rejectedScalar writeController scalarValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.s0, hv1, e1, a.ld 8 (by decide), a.al 8 (by decide) (by decide),
      a.st 8 (by decide), a.st 112 (by decide), a.al 112 (by decide) (by decide),
      fin64_exec_li_lit (show 4 < 2048 by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used keys (scalars - 1)) := by
    refine headers_after _ (scalarValues_bound scalars) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le h.keys_le (by have := h.scalars_le; omega) _ (scalarValues_bound scalars)
    (by simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k hsp hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (scalarValues_bound scalars) 14 (by decide)]
  simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

theorem key_rejected_public {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hk : 0 < keys) :
    WP isa (.block rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv0
  have e0 := ofNat_pred hk (by have := h.keys_le; omega)
  refine WP.mono (WP.ctl (Q := fun t =>
    t.mem = writeController s.mem p.control (publicValues keys)) ?_ (by rfl)) fun t ⟨hm, k, hsp⟩ => ?_
  · unfold rejectedPublic writeController publicValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.s0, hv0, e0, a.ld 0 (by decide), a.al 0 (by decide) (by decide),
      a.st 0 (by decide), a.st 8 (by decide), a.st 112 (by decide), a.al 8 (by decide) (by decide),
      a.al 112 (by decide) (by decide), fin64_exec_li_lit (show 4 < 2048 by decide),
      fin64_exec_li_lit (show 128 < 2048 by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used (keys - 1) 128) := by
    refine headers_after _ (publicValues_bound keys) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le (by have := h.keys_le; omega) (by decide) _ (publicValues_bound keys)
    (by simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k hsp hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (publicValues_bound keys) 14 (by decide)]
  simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

/-! ## The controller's tests of its budgets, tape and status -/

/-- A budget, at the controller's word `j`, compared with zero. -/
theorem budget_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {j n : Nat} (hj : j = 0 ∨ j = 1)
    (hv : (j, BitVec.ofNat 64 n) ∈ p.headers used keys scalars) (hn : n ≤ 128) :
    WP isa (.block [ldf .t0 j]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .t0) t = some (decide (n = 0)) := by
  have a := h.access
  have hw := h.header hv
  have hb := Steps.ofNat_beq_zero (show n < 2 ^ 64 by omega)
  simp only [Bignum.word] at hw
  rcases hj with rfl | rfl <;> simp only [Nat.reduceMul] at hw <;>
  · refine WP.mono (WP.ctl (Q := fun t =>
      isa.eval (.zero .t0) t = some (decide (n = 0)) ∧ t.mem = s.mem) ?_ (by rfl))
      fun _ ⟨⟨he, hm⟩, k, hsp⟩ => ⟨h.keep k hsp hm, he⟩
    brun [ldf, h.s0, hw, a.ld 0 (by decide), a.ld 8 (by decide), a.al 0 (by decide) (by decide),
      a.al 8 (by decide) (by decide), eval_zero', hb]

theorem keys_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .t0 0]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .t0) t = some (decide (keys = 0)) :=
  budget_guard h (j := 0) (.inl rfl) (by simp [KeyPublic.headers]) h.keys_le

theorem scalars_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .t0 1]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .t0) t = some (decide (scalars = 0)) :=
  budget_guard h (j := 1) (.inr rfl) (by simp [KeyPublic.headers]) h.scalars_le

/-- Whether the tape is short of an attempt: `t0 < t1`. -/
theorem room_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block room) s fun t =>
      KeyLive p original used keys scalars t ∧
        isa.eval (.ltu .t0 .t1) t = some (decide (p.randLen - used < p.len)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv2 hv10
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hk : p.len < 2 ^ 64 := by have := h.input.len_lt; omega
  have hlt := ofNat_lt_ofNat (a := p.randLen - used) (show p.randLen - used < 2 ^ 64 by omega) hk
  refine WP.mono (WP.ctl (Q := fun t =>
    isa.eval (.ltu .t0 .t1) t = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_
    (by rfl)) fun _ ⟨⟨he, hm⟩, k, hsp⟩ => ⟨h.keep k hsp hm, he⟩
  unfold room
  brun [ldf, h.s0, hv2, hv10, a.ld 16 (by decide), a.ld 80 (by decide), a.al 16 (by decide) (by decide),
    a.al 80 (by decide) (by decide), eval_ltu, hlt]

theorem key_status_lt (r : KeySearchResult) : r.status < 5 := by
  unfold KeySearchResult.status; split <;> decide

theorem key_status_ne (r : KeySearchResult) : r.status ≠ 4 := by
  unfold KeySearchResult.status; split <;> decide

/-- The status word, less 4, compared with zero. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .s0 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) s fun t =>
      (isa.eval (.zero .t0) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep tmpRegs s t ∧ t.sp = s.sp := by
  have h4 : ∀ st < 5, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = decide (st = 4) := by decide
  simp only [Bignum.word] at hs
  refine WP.ctl ?_ (by rfl)
  brun [ldf, hb, hs, a.ld 112 (by decide), a.al 112 (by decide) (by decide), eval_zero',
    h4 st hst]

theorem done_loop_guard {p : KeyPublic} {original s : State} {r : KeySearchResult}
    (h : KeyDone p original r s) :
    WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) s fun t =>
      isa.eval (.zero .t0) t = some false ∧ KeyDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.s0 h.status (key_status_lt r)) fun t ⟨⟨he, hm⟩, k, _⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (key_status_ne r)]

theorem live_loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .t0 14, .addi .t0 .t0 (-4)]) s fun t =>
      isa.eval (.zero .t0) t = some true ∧ KeyLive p original used keys scalars t :=
  WP.mono (status_guard (st := 4) h.access h.s0 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k, hsp⟩ => ⟨he, h.keep k hsp hm⟩

/-- The status `t0` minus `k`, compared with zero. -/
theorem test_ok {s : State} {st k : Nat} (h0 : s.gpr .t0 = BitVec.ofNat 64 st) (hst : st < 4)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    WP isa (.block (test k)) s fun t =>
      (isa.eval (.zero .t1) t = some (decide (st = k)) ∧ t.mem = s.mem) ∧ Keep [.t1] s t ∧ t.sp = s.sp := by
  have hb : ∀ st < 4, ∀ k < 4,
      ((BitVec.ofNat 64 st - BitVec.ofNat 64 k) == 0) = decide (st = k) := by decide
  rcases hk with rfl | rfl | rfl <;>
  · refine WP.mono (WP.rdwr (WP.keep [.t1] ?_ (by rfl) rfl)) fun _ ⟨⟨hq, k⟩, _, _, hsp⟩ => ⟨hq, k, hsp⟩
    unfold test
    brun [h0, eval_zero', hb st hst 1 (by decide), hb st hst 2 (by decide), hb st hst 3 (by decide)]

end VG.Proof.Ffdh.RISCV64.Cached.SearchProof
