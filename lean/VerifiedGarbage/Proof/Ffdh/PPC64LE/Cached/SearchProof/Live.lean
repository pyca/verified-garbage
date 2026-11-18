module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Live
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Contract
public import VerifiedGarbage.Proof.Ffdh.GenerationSearch
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Data
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Ffdh.PPC64LE.Cached.SearchProof.Data`, which this module and modules that import it used -/

section

/-! # The cached key-generation controller's public data, loop states and buffers (PPC64LE)

As the uncached controller's (`Proof/Ffdh/PPC64LE/KeyGeneration/Data.lean`),
with the context's two arguments in `KeyPublic`: `KeyPublic` is everything
two constant-time runs share; a loop state (`KeyLive`) is at an offset into
the tape with budgets left, in the frame saving the link register, having
written only the controller's buffers and its stack since the entry (so the
context is unchanged), and the search from there (`keyTail`) is what the
controller returns.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.PPC64LE.Generation (Slots)

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
  xp := s.gpr .r3
  yp := s.gpr .r5
  up := s.gpr .r7
  dp := s.gpr .r8
  rp := stackArg s 0
  B := stackArg s 2
  control := stackArg s 4
  sp := s.sp
  len := keyLen s
  dlen := (s.gpr .r9).toNat
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

/-- A state of the loop, in the frame saving the link register: `used`
octets consumed, `keys` and `scalars` left. The entry state is
functional-proof data only: its callee-saved registers may hold secrets, and
its tape is secret. -/
structure KeyLive (p : KeyPublic) (original : State) (used keys scalars : Nat) (s : State) : Prop where
  input : KeyInput p original
  used_le : used ≤ p.randLen
  keys_le : keys ≤ 128
  scalars_le : scalars ≤ 128
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = p.sp - 48
  r31 : s.gpr .r31 = p.control
  saved : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = original.gpr r
  savedR31 : word s.mem p.control 32 = original.gpr .r31
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

/-- A finished search, before `finish` stores `used` and restores `r31`. -/
structure KeyDone (p : KeyPublic) (original : State) (result : KeySearchResult) (s : State) : Prop where
  input : KeyInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  r31 : s.gpr .r31 = p.control
  saved : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = original.gpr r
  savedR31 : word s.mem p.control 32 = original.gpr .r31
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

theorem sp_room (h : KeyInput p s) : 192 ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

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

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

end

end

/-! # What keeps the key-generation controller's loop state (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.Generation (Slots CtlAccess)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (KeyInput.callChanges s) m m') :
    Frame (KeyInput.changes s) m m' := hf.sub (KeyInput.callChanges_sub s)

namespace KeyLive

variable {p : KeyPublic} {original s t : State} {used keys scalars : Nat}

theorem access (h : KeyLive p original used keys scalars s) : CtlAccess s p.control :=
  CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)

/-- Through code that keeps `r31`, the stack pointer, the regions, the
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
    hsp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun r hr h31 => (hg r hr).trans (h.saved r hr h31), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedR31
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.domain_frame hf').trans h.domain
  · intro e he
    exact (hc e.1 (KeyPublic.headers_index he)).trans (h.headers e he)
  · exact h.frame.trans hf'

theorem keep (h : KeyLive p original used keys scalars s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    KeyLive p original used keys scalars t := by
  apply h.restore k.rd k.wr k.sp (fun reg hr => k.gpr reg (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `r31`, to the
counters `u`, `k` and `c`. -/
theorem update (h : KeyLive p original used keys scalars s) {u k c : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ 128) (hc : c ≤ 128)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t)
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
    kp.sp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), ?_, ?_, ?_, hh, h.frame.trans hf⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR31
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
  ⟨h.input, h.rd, h.wr, h.r31, h.saved, h.savedR31,
    h.header (j := 15) (by simp [KeyPublic.headers]),
    by rw [hu]; exact h.header (j := 11) (by simp [KeyPublic.headers]), hs, hp, ho⟩

end KeyLive

theorem KeyDone.keep {p : KeyPublic} {original s t : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : KeyDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ (hregs .r31 (by decide))).trans h.r31,
    fun reg hr h31 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h31), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedR31
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
  refine ⟨h.input, h.rd, h.wr, h.r31, h.saved, h.savedR31, h.usedPtr,
    by rw [← hu]; exact h.used, by rw [← hs]; exact h.status, ?_, ?_⟩
  · rw [h.policy]; unfold KeyPublic.policy; rw [hs, hr]
  · have ho' := h.output; unfold KeyOutput at ho' ⊢; rw [← ho]; exact ho'

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof
