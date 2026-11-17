module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Search
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

/-! ### `RsaKeyGen.PPC64LE.Search.Data`, which this module and modules that import it used -/

section

/-! # The search's public data and its loop states (PPC64LE)

As on AArch64 (`Proof/RsaKeyGen/AArch64/Search/Entry.lean`): the search keeps
its working state in the 20 words at `sp - 160` (`SearchPublic.F`) of the
frame it allocates, with their base in `r31`; the loop runs below it, in the
frame saving the link register.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

def searchOfState (s : State) : SearchPublic where
  op := s.gpr .r3
  up := s.gpr .r5
  ep := s.gpr .r6
  pp := s.gpr .r8
  rp := s.gpr .r10
  B := stackArg s 1
  stp := stackArg s 3
  sp := s.sp
  len := searchLen s
  elen := (s.gpr .r7).toNat
  plen := (s.gpr .r9).toNat
  randLen := (stackArg s 0).toNat
  Z := (stackArg s 2).toNat * 8
  remaining := searchRemaining s
  eB := searchE s

def SearchInput (p : SearchPublic) (s : State) : Prop := searchPre s ∧ searchOfState s = p

/-- The table of trial division's region. -/
abbrev tabR (s : State) : Region := ⟨s.syms Impl.RsaKeyGen.TrialTable32.symbol, 8 * 1024⟩

/-! ## Where the buffers are -/

namespace SearchInput

variable {p : SearchPublic} {s : State}

theorem base (h : SearchInput p s) : basePre (stripConsts tables s) := h.1.1

theorem consts (h : SearchInput p s) : ConstsOk tables stackUse s := h.1.2

theorem wr_eq (h : SearchInput p s) : s.wr = inWrites s := h.base.2.2.2.1

theorem rd_mem (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) : r ∈ s.rd := by
  have e : (stripConsts tables s).rd = inReads s := h.base.2.2.1
  rw [← e] at hr
  exact List.mem_of_mem_take hr

theorem nowrap (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.base.2.2.2.2.1 r hr

theorem write_disjoint (h : SearchInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.base.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.base.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : SearchInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.base.2.2.2.2.2.1

theorem tab_mem : (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed) ∈ tables :=
  List.mem_singleton_self _

theorem packed_length : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

theorem tables_eq : tables = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

theorem tab_reg (s : State) : tabR s ∈ constRegs tables s := by
  rw [tables_eq, constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length]
  exact List.mem_singleton_self _

theorem tab_rd (h : SearchInput p s) : tabR s ∈ s.rd := by
  have := h.consts.mem_rd tab_mem
  rw [packed_length] at this
  exact this

theorem tab_fit (h : SearchInput p s) : (tabR s).base.toNat + (tabR s).len ≤ 2 ^ 64 := by
  have := h.consts.fit tab_mem
  rw [packed_length] at this
  exact this

theorem tab_wr (h : SearchInput p s) {r : Region} (hr : r ∈ s.wr) : (tabR s).Disjoint r :=
  (h.consts.2.2.1 _ (tab_reg s)).2.1 r hr

theorem tab_stack (h : SearchInput p s) : (tabR s).Disjoint (below s.sp stackUse) :=
  (h.consts.2.2.1 _ (tab_reg s)).2.2 _ (by simp [abi, stackBelow, below])

theorem tab_held (h : SearchInput p s) (i : Nat) (hi : i < 1024) :
    s.mem.readW (s.syms Impl.RsaKeyGen.TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 :=
  h.consts.readW tab_mem (by rw [packed_length]; exact hi)

theorem sp_eq (h : SearchInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem room (h : SearchInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.base.2.1

theorem top (h : SearchInput p s) : p.sp.toNat + 128 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.base.1

theorem F_toNat (h : SearchInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 768 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [SearchPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega_using [this]), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : SearchInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  refine Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) ?_
  have := h.F_toNat
  have : 768 ≤ p.sp.toNat := h.room
  have := h.top
  omega_arith

/-- The regions the search (and its callee) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below s.sp stackUse]

theorem read_disjoint (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem bytes_frame (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega_using [hn]) (List.mem_range.mp hi)

theorem random_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

theorem e_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.ep p.elen = Spec.Rsa.bytesAt m p.ep p.elen := by
  rw [← h.2]
  exact h.bytes_frame (r := inE s) (by simp [inReads]) hf

theorem p_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.pp p.plen = Spec.Rsa.bytesAt m p.pp p.plen := by
  rw [← h.2]
  exact h.bytes_frame (r := inP s) (by simp [inReads]) hf

/-- The table's words, through what the search may write. -/
theorem tab_frame (h : SearchInput p s) {m' : Mem} (hf : Frame (changes s) s.mem m') (i : Nat) (hi : i < 1024) :
    m'.readW (s.syms Impl.RsaKeyGen.TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  rw [← h.tab_held i hi]
  refine hf.readW (r := tabR s) (Offset.contains_base _ (by omega_using [hi]) (by have := h.tab_fit; omega_using [hi]))
    (fun w hw => ?_) (by decide)
  rcases List.mem_append.mp hw with hw | hw
  · exact h.tab_wr (by rw [h.wr_eq]; exact hw)
  · obtain rfl := List.mem_singleton.mp hw
    exact h.tab_stack

/-- The frame is in the stack the search may use. -/
theorem frame_sub (h : SearchInput p s) : Region.Sub p.frame (below s.sp stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

/-- What a candidate call may write: the outputs, the working space, and the
stack below the search's frame. -/
def callChanges (s : State) : List Region :=
  [inOut s, inUsed s, inScr s, ⟨s.sp - BitVec.ofNat 64 stackUse, 576⟩]

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨below s.sp stackUse, by simp [changes], Offset.sub_below _ (by decide) (by decide)⟩

/-- The frame is disjoint from what a candidate call writes. -/
theorem frame_disjoint (h : SearchInput p s) : ∀ r ∈ callChanges s, p.frame.Disjoint r := by
  have hsub := h.frame_sub
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fun x hx hy => (h.stack_disjoint (r := inOut s) (by simp [inWrites])) x (hsub x hx) hy
  · exact fun x hx hy => (h.stack_disjoint (r := inUsed s) (by simp [inWrites])) x (hsub x hx) hy
  · exact fun x hx hy => (h.stack_disjoint (r := inScr s) (by simp [inWrites])) x (hsub x hx) hy
  · rw [← h.sp_eq]
    have hs := Offset.sep_below p.sp 768 (a := 160) (n := 160) (b := 768) (k := 576) (by decide) (by decide)
      (Or.inr (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (by simp only [Region.Contains, SearchPublic.F] at hx; omega_using [hx])
      (by simp only [Region.Contains] at hy; exact hy)

theorem frame_words (h : SearchInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 20) : word m' p.F (8 * j) = word m p.F (8 * j) :=
  hf.readW (r := p.frame) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    (h.frame_disjoint) (by decide)

end SearchInput

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (SearchInput.callChanges s) m m') :
    Frame (SearchInput.changes s) m m' := hf.sub (SearchInput.callChanges_sub s)

/-! ## The loop states -/

/-- A state of the loop, in the frame saving the link register: `used`
octets consumed, `remaining` counted candidates left. The entry state is
functional-proof data only: its callee-saved registers may hold secrets, and
its tape is secret. -/
structure SearchLive (p : SearchPublic) (original : State) (used remaining : Nat) (s : State) : Prop where
  input : SearchInput p original
  used_le : used ≤ p.randLen
  remaining_le : remaining ≤ p.remaining
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  sp : s.sp = p.F - 80
  r31 : s.gpr .r31 = p.F
  saved : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = original.gpr r
  syms : s.syms = original.syms
  savedR31 : word s.mem p.F 32 = original.gpr .r31
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = searchRand original
  e : Spec.Rsa.bytesAt s.mem p.ep p.elen = p.eB
  other : Spec.Rsa.bytesAt s.mem p.pp p.plen = searchP original
  tab : Frame (SearchInput.changes original) original.mem s.mem
  headers : Slots s.mem p.F (p.headers used remaining)

namespace SearchLive

variable {p : SearchPublic} {original s t : State} {used remaining : Nat}

theorem headers_index {e : Nat × BitVec 64} (he : e ∈ p.headers used remaining) : e.1 < 20 :=
  p.headers_bound used remaining e he

/-- Through code that keeps `r31`, the stack pointer, the regions and the
callee-saved registers, and writes only what a candidate call may. -/
theorem restore (h : SearchLive p original used remaining s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (SearchInput.callChanges original) s.mem t.mem) :
    SearchLive p original used remaining t := by
  have hc := h.input.frame_words hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.remaining_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .r31 (by decide)).trans h.r31,
    fun r hr h31 => (hg r hr).trans (h.saved r hr h31), hy.trans h.syms, ?_, ?_, ?_, ?_, h.tab.trans hf', ?_⟩
  · exact (hc 4 (by decide)).trans h.savedR31
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.e_frame hf').trans h.e
  · exact (h.input.p_frame hf').trans h.other
  · intro e he
    exact (hc e.1 (headers_index he)).trans (h.headers e he)

theorem keep (h : SearchLive p original used remaining s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hy : t.syms = s.syms)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SearchLive p original used remaining t := by
  apply h.restore kp.rd kp.wr kp.sp hy (fun reg hr => kp.gpr reg (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- The search's memory moves only within what it may write. -/
theorem frame_of_writeFrame (h : SearchLive p original used remaining s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20) :
    Frame (SearchInput.changes original) s.mem (writeFrame s.mem p.F values) := by
  apply (writeFrame_frame s.mem p.F values hb).sub
  intro region hregion
  obtain rfl := List.mem_singleton.mp hregion
  exact ⟨_, by simp [SearchInput.changes], h.input.frame_sub⟩

/-- Through stores of frame words but the saved `r31`, to the counters `u`
and `k`. -/
theorem update (h : SearchLive p original used remaining s) {u k : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values) (hy : t.syms = s.syms)
    {rs : List Reg} (kp : Keep rs s t) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide)
    (hh : Slots t.mem p.F (p.headers u k)) : SearchLive p original u k t := by
  have hf : Frame (SearchInput.changes original) s.mem t.mem := by
    rw [hm]; exact h.frame_of_writeFrame values hb
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (hregs r hr)
  refine ⟨h.input, hu, hk, kp.rd.trans h.rd, kp.wr.trans h.wr, kp.sp.trans h.sp,
    (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), hy.trans h.syms, ?_, ?_, ?_, ?_,
    h.tab.trans hf, hh⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 4) = _
    rw [writeFrame_word _ _ _ hb 4 (by decide), frameValue_unchanged _ _ _ h4]
    exact h.savedR31
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.e_frame hf).trans h.e
  · exact (h.input.p_frame hf).trans h.other

end SearchLive

end VG.Proof.RsaKeyGen.PPC64LE.Search

end

end

-- separate module: its proofs build in parallel with those of `Call` and `Step`, which `Correct` and `CT` also import

/-! # The search's entry (PPC64LE)

In the frame the search allocates, the caller's `r31` is saved in word 4 and
the register arguments stored (`entrySave_ok`); then the stack arguments and
the state's first word are loaded and the rest of the words stored
(`entryLoad_ok`); then, after `mflr r0`, in the frame saving it, the search
is at the tape's start with its counted candidates (`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Search
open VG.Spec.RsaKeyGen (primeEntropy)

/-- The frame's words the first block stores. -/
def saveValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r31), (5, s.gpr .r3), (6, s.gpr .r4), (7, s.gpr .r5), (8, s.gpr .r6), (9, s.gpr .r7),
    (10, s.gpr .r8), (11, s.gpr .r9), (12, s.gpr .r10)]

/-- The frame's words the second block stores. -/
def loadValues (s : State) : List (Nat × BitVec 64) :=
  [(13, stackArg s 0), (14, stackArg s 1), (15, stackArg s 2), (18, stackArg s 3),
    (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .r4), (2, (s.gpr .r4 <<< 15) + s.gpr .r4), (3, 0), (16, 0)]

/-- The frame's words on entry, in the order the entry stores them. -/
abbrev entryValues (s : State) : List (Nat × BitVec 64) := saveValues s ++ loadValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, saveValues, loadValues, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl) <;> dsimp only <;> decide

theorem add_ofNat_zero (x : Addr) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

/-- The frame's words' base, from the stack pointer the allocation leaves. -/
theorem frame_base (x : Addr) : x - BitVec.ofNat 64 192 + 32 = x - BitVec.ofNat 64 160 :=
  (Offset.sub_ofNat_eq x (by decide : 160 ≤ 192)).symm

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 192 s).wr = p.frame :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 192 + 32, 192 - 32⟩ : Region) :: s.wr = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [frame_base, h.sp_eq]

theorem alloc_sp {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 192 s).sp + BitVec.ofNat 64 32 = p.F := by
  show s.sp - BitVec.ofNat 64 192 + 32 = p.sp - _
  rw [frame_base, h.sp_eq]

theorem alloc_room {s : State} (h : stackUse ≤ s.sp.toNat) : 192 ≤ s.sp.toNat := by
  have : 192 ≤ stackUse := by decide
  omega_using [h, this]

/-- The back chain of the search's frame and the frame's words: below the
stack pointer. -/
theorem entry_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) :
    Frame [below s.sp stackUse] s.mem (writeFrame (allocated 192 s).mem p.F values) := by
  have h₁ : Frame [below s.sp stackUse] s.mem (allocated 192 s).mem :=
    Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_below s.sp (a := 192) (b := stackUse) (by decide) (by decide) (by decide))
  refine h₁.trans ((writeFrame_frame _ p.F values hb).sub fun r hr => ?_)
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, h.frame_sub⟩

/-- The stack arguments' addresses, from the frame's base. -/
theorem arg_addr (sp : Addr) (k : Nat) :
    sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 (256 + 8 * k) = sp + BitVec.ofNat 64 (32 + 8 * (8 + k)) := by
  rw [show 256 + 8 * k = 160 + (32 + 8 * (8 + k)) by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem args_contains (s : State) (k : Nat) (hk : k < 4) :
    (inArgs s).Contains (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + k))) 8 := by
  have e : s.sp + BitVec.ofNat 64 (32 + 8 * (8 + k)) = stackArgAddr s 0 + BitVec.ofNat 64 (8 * k) := by
    unfold stackArgAddr
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega_using []
  rw [e]
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) (k : Nat) (hk : k < 4) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + k))) 8 :=
  ⟨inArgs s, List.mem_append_left _ (h.rd_mem (by simp [inReads])), args_contains s k hk⟩

/-- The registers the first block writes. -/
abbrev saveRegs : List Reg := [.r11, .r31]

theorem entrySave_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entrySave) (allocated 192 s) fun t =>
      (t.gpr .r31 = p.F ∧ t.mem = writeFrame (allocated 192 s).mem p.F (saveValues s)) ∧
      Keep saveRegs (allocated 192 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 192 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ea : ∀ t : State, exec (.addSp .r11 32) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 32)) := by
    intro t; simp [exec]
  have hsp := alloc_sp h
  have hg : ∀ r, (allocated 192 s).gpr r = s.gpr r := fun _ => rfl
  refine WP.keep saveRegs ?_ (by decide)
  unfold entrySave writeFrame saveValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, ea, hsp, hg, add_ofNat_zero, hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 96 (by decide), off]

/-- The registers the second block writes. -/
abbrev loadRegs : List Reg := [.r8, .r9, .r10, .r11, .r12]

theorem entryLoad_ok {p : SearchPublic} {s u : State} (h : SearchInput p s)
    (h31 : u.gpr .r31 = p.F) (hm : u.mem = writeFrame (allocated 192 s).mem p.F (saveValues s))
    (ku : Keep saveRegs (allocated 192 s) u) :
    WP isa (.block entryLoad) u fun t =>
      t.mem = writeFrame u.mem p.F (loadValues s) ∧ Keep loadRegs u t := by
  have hw : u.wr = p.frame :: s.wr := ku.wr.trans (alloc_wr h)
  have scr := h.frame_scr hw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions u.wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hrd : u.rd ++ u.wr = s.rd ++ (p.frame :: s.wr) := by rw [ku.rd, hw]; rfl
  have hF : p.F = s.sp - BitVec.ofNat 64 160 := by show p.sp - _ = _; rw [h.sp_eq]
  have hfr := entry_frame h (saveValues s) (by
    simp only [saveValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  rw [← hm] at hfr
  have ha (k : Nat) (hk : k < 4) : InRegions (u.rd ++ u.wr) (p.F + BitVec.ofNat 64 (256 + 8 * k)) 8 := by
    rw [hrd, hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args h k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (k : Nat) (hk : k < 4) : u.mem.readW (p.F + BitVec.ofNat 64 (256 + 8 * k)) 64 = stackArg s k := by
    rw [hF, arg_addr]
    refine hfr.readW (r := inArgs s) (args_contains s k hk) (fun r hr => ?_) (by decide)
    · obtain rfl := List.mem_singleton.mp hr
      exact (h.stack_disjoint (List.mem_append_right _ (by simp [inReads]))).symm
  have hst : InRegions (u.rd ++ u.wr) (stackArg s 3 + BitVec.ofNat 64 0) 8 := by
    rw [hrd, add_ofNat_zero]
    refine ⟨inState s, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), ?_⟩
    · rw [h.wr_eq]; simp [inWrites]
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
  have hw0 : u.mem.readW (stackArg s 3 + BitVec.ofNat 64 0) 64 = s.mem.readW (stackArg s 3) 64 := by
    rw [add_ofNat_zero]
    refine hfr.readW (r := inState s) ?_ (fun r hr => ?_) (by decide)
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
    · obtain rfl := List.mem_singleton.mp hr
      exact (h.stack_disjoint (List.mem_append_left _ (by simp [inWrites]))).symm
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 v0 v1 v2 v3
  have h4 : u.gpr .r4 = s.gpr .r4 := ku.gpr .r4 (by decide)
  refine WP.keep loadRegs ?_ (by decide)
  unfold entryLoad writeFrame loadValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, h31, h4, a0, a1, a2, a3, v0, v1, v2, v3, hst, hw0, hs 104 (by decide), hs 112 (by decide),
    hs 120 (by decide), hs 144 (by decide), hs 0 (by decide), hs 8 (by decide), hs 16 (by decide),
    hs 24 (by decide), hs 128 (by decide), off]
  rfl

theorem sp_240 (x : Addr) : x - BitVec.ofNat 64 192 - 48 = x - BitVec.ofNat 64 160 - 80 := by
  rw [BitVec.sub_sub, BitVec.sub_sub]; rfl

theorem sp_208 (x : Addr) : x - BitVec.ofNat 64 192 - 48 + 32 = x - BitVec.ofNat 64 208 := by
  rw [BitVec.sub_sub, Offset.sub_ofNat_eq x (show 208 ≤ 240 by decide)]; rfl

/-- The push of the frame saving the link register writes only below the
search's frame. -/
theorem push_frame {s : State} {x : Addr}
    (hx : x = s.sp - BitVec.ofNat 64 192) (m : Mem) (v w : BitVec 64) :
    Frame (SearchInput.callChanges s) m ((m.write (x - 48) 8 v).write (x - 48 + 32) 8 w) := by
  have hr : (⟨s.sp - BitVec.ofNat 64 stackUse, 576⟩ : Region) ∈ SearchInput.callChanges s := by
    simp [SearchInput.callChanges]
  refine Frame.write (Frame.write (Frame.refl _ _) hr _ ?_) hr _ ?_
  · rw [hx, sp_240, BitVec.sub_sub]
    exact Offset.contains_below s.sp (a := 240) (b := stackUse) (by decide) (by decide) (by decide)
  · rw [hx, sp_208]
    exact Offset.contains_below s.sp (a := 208) (b := stackUse) (by decide) (by decide) (by decide)

/-- The registers the entry and `mflr r0` write. -/
abbrev entryRegs : List Reg := saveRegs ++ loadRegs ++ [.r0]

theorem search_start {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .r31 = p.F) (hm : t.mem = writeFrame (allocated 192 s).mem p.F (entryValues s))
    (k : Keep entryRegs (allocated 192 s) t) (hy : t.syms = s.syms) :
    SearchLive p s 0 p.remaining (framed .r0 t) := by
  have hb := entryValues_bound s
  have hf₁ : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    exact (entry_frame h _ hb).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [SearchInput.changes], fun _ hi => hi⟩
  have htsp : t.sp = s.sp - BitVec.ofNat 64 192 := k.sp
  have hp := push_frame htsp t.mem t.sp (t.gpr .r0)
  have hf₂ : Frame (SearchInput.changes s) s.mem (framed .r0 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (framed .r0 t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) : word (framed .r0 t).mem p.F (8 * j) =
      frameValue (entryValues s) j (word (allocated 192 s).mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  have hL : p.len ≤ 512 := by rw [← h.2]; exact h.base.2.2.2.2.2.2.2.2.1.2.1
  have hx4 : s.gpr .r4 = BitVec.ofNat 64 p.len := by
    rw [← h.2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  have hcap : (s.gpr .r4 <<< 15) + s.gpr .r4 = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hx4, SearchInit.shl_ofNat _ _ (by omega_using [hL]), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega_using []
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr.trans (alloc_wr h), ?_, hx, ?_, hy, ?_, ?_, ?_, ?_, hf₂, ?_⟩
  · show t.sp - 48 = p.sp - BitVec.ofNat 64 160 - 80
    rw [htsp, h.sp_eq, sp_240]
  · intro r hr h31
    exact k.gpr r (by revert r hr h31; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hw 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]; rw [← h.2]; rfl
  · rw [h.e_frame hf₂]; rw [← h.2]; rfl
  · rw [h.p_frame hf₂]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (SearchPublic.headers_bound _ _ _ e he)]
    rw [← h.2] at he hcap hx4 ⊢
    simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      simp only [frameValue, entryValues, saveValues, loadValues, List.cons_append, List.nil_append,
        List.foldl_cons, List.foldl_nil, searchOfState, searchRemaining,
        searchLen, BitVec.ofNat_toNat, BitVec.setWidth_eq, hcap, BitVec.add_zero, Nat.sub_zero,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.PPC64LE.Search
