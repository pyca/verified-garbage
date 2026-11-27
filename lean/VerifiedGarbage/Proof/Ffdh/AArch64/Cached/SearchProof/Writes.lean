module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Ffdh.GenerationSearch
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! ### `Ffdh.AArch64.Cached.SearchProof.Entry`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.Data`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.Contract`, which this module and modules that import it used -/

section

/-! # The key-generation controller's contract in terms of the machine (AArch64)

`vg_ffdh_generate_key_search_cached(x = x0, x_len = x1, y = x2, y_len = x3,
used = x4, domain = x5, domain_len = x6, p_len = x7, rand, rand_len,
scratch, scratch_len, state, ctx, ctx_len)`: eight arguments in registers and seven on the
stack. The controller uses 64 bytes of stack: the frame saving `x30` and
its attempt's frame of 48 bytes; the attempt it calls uses none
(`Attempt.depth`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Spec.Ffdh
open VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod)

/-- The stack the controller uses below the stack pointer. -/
abbrev stackUse : Nat := 64

/-- A stack-free verified cached attempt. -/
structure Attempt where
 M : Mont
 depth : (Impl.Ffdh.AArch64.Cached.Generate.code M.mm).aarch64Depth=0

abbrev Attempt.code (a : Attempt) : Prog isa := Impl.Ffdh.AArch64.Cached.Generate.code a.M.mm
abbrev Attempt.call (a : Attempt) : Prog isa := .call "vg_ffdh_generate_key_cached" a.code

def inX (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inY (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x4, 8⟩
def inDom (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
def inRand (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
def inScr (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
def inCtl (s : State) : Region := ⟨stackArg s 4, 128⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The buffers the controller writes, and those it only reads. -/
def inWrites (s : State) : List Region := [inX s, inY s, inUsed s, inScr s, inCtl s]
def inContext (s : State) : Region := ⟨stackArg s 5,(stackArg s 6).toNat*8⟩
def inReads (s : State) : List Region := [inDom s, inRand s, inContext s,inArgs s]

/-- The width, the domain and the random octets on entry. -/
abbrev keyLen (s : State) : Nat := (s.gpr .x7).toNat
abbrev keyDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
abbrev keyRand (s : State) : List Byte := bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev keyA (s : State) : Parameters := domainOf (keyLen s) (keyDom s)
abbrev keyRetries (s : State) : KeyRetries :=
  ⟨(s.mem.readW (stackArg s 4) 64).toNat, (s.mem.readW (stackArg s 4 + 8) 64).toNat⟩

def keyPre (s : State) : Prop :=
  s.sp.toNat + 56 ≤ 2 ^ 64 ∧ stackUse ≤ s.sp.toNat ∧
    s.rd = inReads s ∧ s.wr = inWrites s ∧
    (∀ r ∈ inWrites s ++ inReads s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (inWrites s).Pairwise Region.Disjoint ∧
    (∀ w ∈ inWrites s, ∀ r ∈ inReads s, w.Disjoint r) ∧
    (∀ r ∈ inWrites s ++ inReads s, (below s.sp stackUse).Disjoint r) ∧
    pLenValid (keyLen s) ∧ domainLenValid (keyLen s) (s.gpr .x6).toNat ∧
    (s.gpr .x1).toNat = keyLen s ∧ (s.gpr .x3).toNat = keyLen s ∧
    Spec.Rsa.scratchWords (keyLen s) ≤ (stackArg s 3).toNat ∧
    domainValid (keyLen s) (keyDom s) ∧
    (s.mem.readW (stackArg s 4) 64).toNat ≤ 128 ∧
    (s.mem.readW (stackArg s 4 + 8) 64).toNat ≤ 128 ∧
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) ∧
    (stackArg s 6).toNat=Spec.Ffdh.generationPrecomputedWords (keyLen s) ∧
    Spec.Ffdh.generationPrecompute (keyLen s) (keyDom s)=some (wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat)

def keyResult (s : State) : KeySearchResult :=
  vettedKeySearch (keyA s) (keyLen s) (keyRetries s) (keyRand s)

def keyPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = (keyResult s).status ∧
    (match (keyResult s).outcome with
      | .accepted sx sy => bytesAt t.mem (s.gpr .x0) (keyLen s) = i2osp sx (keyLen s) ∧
          bytesAt t.mem (s.gpr .x2) (keyLen s) = i2osp sy (keyLen s)
      | _ => bytesAt t.mem (s.gpr .x0) (keyLen s) = List.replicate (keyLen s) 0 ∧
          bytesAt t.mem (s.gpr .x2) (keyLen s) = List.replicate (keyLen s) 0) ∧
    wordsAt t.mem (stackArg s 4) 4 = [BitVec.ofNat 64 (keyResult s).retries.keys,
      BitVec.ofNat 64 (keyResult s).retries.scalars, BitVec.ofNat 64 (keyLen s),
      BitVec.ofNat 64 (if (keyResult s).status = 0 then keyLen s else 0)] ∧
    wordsAt t.mem (s.gpr .x4) 1 = [BitVec.ofNat 64 (keyResult s).used]

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

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # The key-generation controller's public data, loop states and buffers (AArch64)

As on x86-64 (`Proof/Ffdh/X86_64/KeyGeneration/Data.lean`): `KeyPublic` is
everything two constant-time runs share; a loop state (`KeyLive`) is at an
offset into the tape with budgets left, in the frame saving `x30`, and the
search from there (`keyTail`) is what the controller returns.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.AArch64 (Slots)

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
  xp := s.gpr .x0
  yp := s.gpr .x2
  up := s.gpr .x4
  dp := s.gpr .x5
  rp := stackArg s 0
  B := stackArg s 2
  control := stackArg s 4
  sp := s.sp
  len := keyLen s
  dlen := (s.gpr .x6).toNat
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

/-- A state of the loop, in the frame saving `x30`: `used` octets consumed,
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
  x19 : s.gpr .x19 = p.control
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.control 32 = original.gpr .x19
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = keyRand original
  domain : Spec.Rsa.bytesAt s.mem p.dp p.dlen = p.dom
  headers : Slots s.mem p.control (p.headers used keys scalars)
  frame : Frame (inWrites original++[below original.sp stackUse]) original.mem s.mem

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

/-- A finished search, before `finish` stores `used` and restores `x19`. -/
structure KeyDone (p : KeyPublic) (original : State) (result : KeySearchResult) (s : State) : Prop where
  input : KeyInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  x19 : s.gpr .x19 = p.control
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.control 32 = original.gpr .x19
  usedPtr : word s.mem p.control 120 = p.up
  used : word s.mem p.control 88 = BitVec.ofNat 64 result.used
  status : word s.mem p.control 112 = BitVec.ofNat 64 result.status
  policy : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy result
  output : KeyOutput p result s.mem

/-! ## Where the buffers are -/

namespace KeyInput

variable {p : KeyPublic} {s : State}

theorem nowrap (h : KeyInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.1 r hr

theorem write_disjoint (h : KeyInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : KeyInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : KeyInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.1

theorem len_eq (h : KeyInput p s) : p.len = keyLen s := by rw [← h.2]; rfl

theorem len_bounds (h : KeyInput p s) : 64 ≤ p.len ∧ p.len ≤ 1024 := by
  rw [h.len_eq]; exact h.1.2.2.2.2.2.2.2.2.1

theorem sp_eq (h : KeyInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem sp_room (h : KeyInput p s) : 64 ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem control_scr (h : KeyInput p s) {t : State} (hw : t.wr = s.wr) : Scr t p.control 128 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inCtl, keyOfState]) ?_
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, -, -⟩ := h.1
  rw [← h.2]; exact hv

theorem keys_le (h : KeyInput p s) : p.keys ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -, -, -, -⟩ := h.1
  rw [← h.2]; exact hk

theorem scalars_le (h : KeyInput p s) : p.scalars ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -, -, -⟩ := h.1
  rw [← h.2]; exact hs

theorem len_lt (h : KeyInput p s) : p.len < 2 ^ 31 := by
  have := h.len_bounds.2; omega_using [this]

end KeyInput

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.Live`, which the modules that import this one used -/

section

/-! # What keeps the key-generation controller's loop state (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (KeyInput.callChanges s) m m') :
    Frame (KeyInput.changes s) m m' := hf.sub (KeyInput.callChanges_sub s)

namespace KeyLive

variable {p : KeyPublic} {original s t : State} {used keys scalars : Nat}

/-- Through code that keeps `x19`, the stack pointer, the regions, the
controller's words, and writes only the outputs, `used`, the working space
and the stack. -/
theorem restore (h : KeyLive p original used keys scalars s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame (KeyInput.callChanges original) s.mem t.mem) :
    KeyLive p original used keys scalars t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .x19 (by decide) (by decide)).trans h.x19,
    fun r hr h19 h30 => (hg r hr h30).trans (h.saved r hr h19 h30),
    fun r hr => (hv r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_,h.frame.trans hf'⟩
  · exact (hc 4 (by decide)).trans h.savedX19
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.domain_frame hf').trans h.domain
  · intro e he
    exact (hc e.1 (KeyPublic.headers_index he)).trans (h.headers e he)

theorem keep (h : KeyLive p original used keys scalars s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    KeyLive p original used keys scalars t := by
  apply h.restore k.rd k.wr k.sp (fun reg hr _ => k.gpr reg (hregs reg hr)) k.vcs
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `x19`, to the
counters `u`, `k` and `c`. -/
theorem update (h : KeyLive p original used keys scalars s) {u k c : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ 128) (hc : c ≤ 128)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.x0, .x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14] s t)
    (hh : Slots t.mem p.control (p.headers u k c)) : KeyLive p original u k c t := by
  have hf : Frame (KeyInput.changes original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [KeyInput.changes, inWrites], ?_⟩
    rw [← h.input.2]
    exact fun _ hi => hi
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  refine ⟨h.input, hu, hk, hc, kp.rd.trans h.rd, kp.wr.trans h.wr,
    kp.sp.trans h.sp, (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, hh,h.frame.trans hf⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedX19
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.domain_frame hf).trans h.domain

theorem header (h : KeyLive p original used keys scalars s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used keys scalars) : word s.mem p.control (8 * j) = v :=
  h.headers (j, v) hj

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : KeyLive p original used keys scalars s) {r : Spec.Ffdh.KeySearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : KeyOutput p r s.mem) : KeyDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.x19, h.saved, h.vcs, h.savedX19,
    h.header (j := 15) (by simp [KeyPublic.headers]),
    by rw [hu]; exact h.header (j := 11) (by simp [KeyPublic.headers]), hs, hp, ho⟩

end KeyLive

theorem KeyDone.keep {p : KeyPublic} {original s t : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : KeyDone p original result t := by
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

/-- A finished search's state depends on its result's outcome and octets
consumed, not on its statuses. -/
theorem KeyDone.congr {p : KeyPublic} {original s : State} {r r' : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (ho : r.outcome = r'.outcome) (hu : r.used = r'.used) :
    KeyDone p original r' s := by
  have hs : r.status = r'.status := by unfold Spec.Ffdh.KeySearchResult.status; rw [ho]
  have hr : r.retries = r'.retries := by unfold Spec.Ffdh.KeySearchResult.retries; rw [ho]
  refine ⟨h.input, h.rd, h.wr, h.x19, h.saved, h.vcs, h.savedX19, h.usedPtr,
    by rw [← hu]; exact h.used, by rw [← hs]; exact h.status, ?_, ?_⟩
  · rw [h.policy]; unfold KeyPublic.policy; rw [hs, hr]
  · have ho' := h.output; unfold KeyOutput at ho' ⊢; rw [← ho]; exact ho'

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # The key-generation controller's entry (AArch64)

The stack arguments are loaded, the caller's `x19` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving
`x30`, the controller is at the tape's start (`key_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [hn]

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .x19), (5, s.gpr .x0), (6, s.gpr .x2), (7, s.gpr .x5), (8, s.gpr .x6),
    (9, stackArg s 0), (10, stackArg s 1), (11, 0), (12, stackArg s 2), (13, stackArg s 3),
    (15, s.gpr .x4)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) (j : Nat) (hj : j < 7) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .x19 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := input_args h 2 (by decide)
  have ha3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 24) 8 := input_args h 3 (by decide)
  have ha4 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 := input_args h 4 (by decide)
  refine WP.keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] ?_ (by decide) (by decide) (by decide +kernel)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide), hd, ha0,
    ha1, ha2, ha3, ha4, hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 96 (by decide), hs 104 (by decide), hs 120 (by decide)]
  simp only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rfl

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.Outputs`, which this module and modules that import it used -/

section

/-! # Zeros at the key-generation controller's outputs (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

private theorem not_self_disjoint {r : Region} (h : r.Disjoint r) (hl : 0 < r.len) : False :=
  h r.base (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hl])
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hl])

namespace KeyInput

variable {p : KeyPublic} {original : State}

theorem x_eq (h : KeyInput p original) : inX original = ⟨p.xp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hx1, -, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inX, keyOfState, hx1]

theorem y_eq (h : KeyInput p original) : inY original = ⟨p.yp, p.len⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hx3, -, -, -, -, -⟩ := h.1
  rw [← h.2]; simp only [inY, keyOfState, hx3]

theorem x_mem (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.x_eq]; simp [inWrites]

theorem y_mem (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.y_eq]; simp [inWrites]

theorem x_ne_ctl (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  have d := this.1.2.2.2
  rw [h.x_eq, he] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

theorem y_ne_ctl (h : KeyInput p original) : (⟨p.yp, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  have d := this.2.1.2.2
  rw [h.y_eq, he] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

theorem xy_disjoint (h : KeyInput p original) : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.yp, p.len⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.x_eq, ← h.y_eq]
  exact this.1.1

end KeyInput

/-- A zeroing of an output changes memory only there. -/
theorem zero_frame {p : KeyPublic} {original : State} (hinput : KeyInput p original) {m m' : Mem}
    {o : Addr} (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original)
    (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original)
    (hf : ∀ x, (∀ j < p.len, x ≠ o + BitVec.ofNat 64 j) → m' x = m x) :
    Frame (KeyInput.callChanges original) m m' := by
  intro a ha
  apply hf
  intro i hi he
  have hk := hinput.len_lt
  have hin : (⟨o, p.len⟩ : Region) ∈ KeyInput.callChanges original := by
    simp only [inWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [KeyInput.callChanges, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with h' | h' | h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inr (.inr (.inl h')))
    · exact absurd h' hrc
  apply ha _ hin
  rw [he]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])

/-- `zeroOut j`: zeros at the output whose pointer is in word `j`. -/
theorem key_zero_out {p : KeyPublic} {original s : State} {used keys scalars j : Nat} {o : Addr}
    (h : KeyLive p original used keys scalars s) (hj56 : j = 5 ∨ j = 6)
    (hj : (j, o) ∈ p.headers used keys scalars)
    (hr : (⟨o, p.len⟩ : Region) ∈ inWrites original) (hrc : (⟨o, p.len⟩ : Region) ≠ inCtl original) :
    WP isa (zeroOut j) s fun t =>
      KeyLive p original used keys scalars t ∧ (∀ i < p.len, t.mem (o + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < p.len, x ≠ o + BitVec.ofNat 64 i) → t.mem x = s.mem x) := by
  have hk := h.input.len_bounds
  have hjl := KeyPublic.headers_index hj
  have scr := h.input.control_scr (t := s) h.wr
  have hv := h.header hj
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv hv2
  have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 (8 * j)) 8 := scr.ld (by omega_using [hj56])
  rcases hj56 with rfl | rfl <;> simp only [Nat.reduceMul] at hv hv2 hl <;>
  · have hl2 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 16) 8 := scr.ld (by decide)
    have hout : ∀ i < p.len, InRegions s.wr (o + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨⟨o, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact hr,
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
    unfold zeroOut
    refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = o + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
      brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl, hl2, hv, hv2]) (by decide) (by decide)
        (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
    refine WP.mono (wp_countdown (N := p.len) (by omega_using [hk]) (by omega_using [hk]) (BInv s₁ o)
      (fun i hi t hI _ => bStep_ok (by omega_using [hk]) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
      ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
    have hf : ∀ x, (∀ i < p.len, x ≠ o + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
      fun x hx => by rw [hI.frame x hx, hm₁]
    have kk := k₁.trans hI.keep
    exact ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs
      (zero_frame h.input hr hrc hf), hI.bytes, hf⟩

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
  have hk64 : p.len < 2 ^ 64 := by omega_using [hk]
  refine ⟨ht, ?_, ?_, ?_⟩
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' := List.mem_range.mp hi
    rw [hft _ (fun j hj he => hxy _ (Offset.contains_base _ (d := i) (n := 1) (by omega_using [hi']) (by omega_using [hk, hi'])) (by
      rw [he]; exact Offset.contains_base _ (d := j) (n := 1) (by omega_using [hj]) (by omega_using [hk, hj])))]
    exact hbv i hi'
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hbt i (List.mem_range.mp hi)
  · intro j hj
    have hf := (zero_frame h.input hxw hxc hfv).trans (zero_frame h.input hyw hyc hft)
    exact h.input.control_frame hf j hj

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # The key-generation controller's writes of its own words (AArch64)

The terminal statuses, the request for entropy, the rejections, and the
octets an attempt consumes; the exits without a key (`key_exhausted`,
`key_request`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search
open VG.Impl.Bignum.AArch64 (movi)

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

/-- The loads and stores of a controller's block, at its words. -/
structure CtlAccess (s : State) (B : Addr) : Prop where
  ld : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  st : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8
  ld0 : InRegions (s.rd ++ s.wr) B 8
  st0 : InRegions s.wr B 8

theorem KeyLive.access {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : CtlAccess s p.control := by
  have scr := h.input.control_scr (t := s) h.wr
  exact ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (1, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.x10, .x11] s t := by
  rcases hst with rfl | rfl <;>
  refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, hb, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
      imm64 (show 3 < 65536 by decide), a.st0, a.st 0 (by decide), a.st 8 (by decide),
      a.st 24 (by decide), a.st 112 (by decide)]
    rfl

/-- A terminal status written over a loop state, with no budgets left. -/
theorem key_terminal_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      KeyLive p original used 0 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (key_terminal_ok h.access h.x19 hst) fun t ⟨hm, k⟩ => ?_
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
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

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

/-! ## A request for entropy -/

def requestValues (p : KeyPublic) : List (Nat × BitVec 64) := [(3, BitVec.ofNat 64 p.len), (14, 0)]

theorem requestValues_bound (p : KeyPublic) : ∀ e ∈ requestValues p, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem key_request_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .x10 2, movi .x11 0, stf .x10 3, stf .x11 14]) s fun t =>
      KeyLive p original used keys scalars t ∧ t.mem = writeController s.mem p.control (requestValues p) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2
  refine WP.mono (WP.keep [.x10, .x11] (Q := fun t =>
    t.mem = writeController s.mem p.control (requestValues p)) ?_ (by decide) (by decide)
      (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  · unfold writeController requestValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, imm64 (show 0 < 65536 by decide), hv2, a.ld 16 (by decide),
      a.st 24 (by decide), a.st 112 (by decide)]
    rfl
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
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

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

/-! ## Rejections -/

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

theorem ofNat_pred {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt h]; omega_using [h0])]
  simp only [BitVec.toNat_ofNat]
  omega_using [h]

theorem key_rejected_scalar {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : 0 < scalars) :
    WP isa (.block rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv1
  have e1 := ofNat_pred hs (by have := h.scalars_le; omega_using [this])
  refine WP.mono (WP.keep [.x10, .x11] (Q := fun t =>
    t.mem = writeController s.mem p.control (scalarValues scalars)) ?_ (by decide) (by decide)
      (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedScalar writeController scalarValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, imm64 (show 4 < 65536 by decide), hv1, e1, a.ld 8 (by decide),
      a.st 8 (by decide), a.st 112 (by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used keys (scalars - 1)) := by
    refine headers_after _ (scalarValues_bound scalars) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le h.keys_le (by have := h.scalars_le; omega_using [this]) _ (scalarValues_bound scalars)
    (by simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (scalarValues_bound scalars) 14 (by decide)]
  simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

theorem key_rejected_public {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hk : 0 < keys) :
    WP isa (.block rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv0
  have e0 := ofNat_pred hk (by have := h.keys_le; omega_using [this])
  refine WP.mono (WP.keep [.x10, .x11, .x12] (Q := fun t =>
    t.mem = writeController s.mem p.control (publicValues keys)) ?_ (by decide) (by decide)
      (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedPublic writeController publicValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, imm64 (show 4 < 65536 by decide), imm64 (show 128 < 65536 by decide),
      hv0, e0, a.ld0, a.st0, a.ld 0 (by decide), a.st 0 (by decide), a.st 8 (by decide), a.st 112 (by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used (keys - 1) 128) := by
    refine headers_after _ (publicValues_bound keys) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le (by have := h.keys_le; omega_using [this]) (by decide) _ (publicValues_bound keys)
    (by simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (publicValues_bound keys) 14 (by decide)]
  simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
