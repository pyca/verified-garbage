module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `RsaKeyGen.AArch64.Search.Data`, which this module and modules that import it used -/

section

/-! # The search's public data and its loop states (AArch64)

As on x86-64 (`Proof/RsaKeyGen/X86_64/Search/Data.lean`): the search keeps its
working state in its frame of 20 words at `sp - 160` (`SearchPublic.F`), with
its base in `x19`; the loop runs below it, in the frame saving `x30`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

def searchOfState (s : State) : SearchPublic where
  op := s.gpr .x0
  up := s.gpr .x2
  ep := s.gpr .x3
  pp := s.gpr .x5
  rp := s.gpr .x7
  B := stackArg s 1
  stp := stackArg s 3
  sp := s.sp
  len := searchLen s
  elen := (s.gpr .x4).toNat
  plen := (s.gpr .x6).toNat
  randLen := (stackArg s 0).toNat
  Z := (stackArg s 2).toNat * 8
  remaining := searchRemaining s
  eB := searchE s

def SearchInput (p : SearchPublic) (s : State) : Prop := searchPre s ∧ searchOfState s = p

/-! ## Where the buffers are -/

namespace SearchInput

variable {p : SearchPublic} {s : State}

theorem nowrap (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.1 r hr

theorem write_disjoint (h : SearchInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : SearchInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.1

theorem sp_eq (h : SearchInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem room (h : SearchInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem top (h : SearchInput p s) : p.sp.toNat + 32 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.1.1

theorem F_toNat (h : SearchInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 208 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [SearchPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega_using [this]), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : SearchInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  refine Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) ?_
  have := h.F_toNat
  have : 208 ≤ p.sp.toNat := h.room
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

/-- The frame is in the stack the search may use. -/
theorem frame_sub (h : SearchInput p s) : Region.Sub p.frame (below s.sp stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

/-- What a candidate call may write: the outputs, the working space, and the
stack arguments below the frame saving `x30`. -/
def callChanges (s : State) : List Region :=
  [inOut s, inUsed s, inScr s, ⟨s.sp - BitVec.ofNat 64 stackUse, 48⟩]

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
    have hs := Offset.sep_below p.sp 208 (a := 160) (n := 160) (b := 208) (k := 48) (by decide) (by decide)
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

/-- A state of the loop: `used` octets consumed, `remaining` counted
candidates left. The entry state is functional-proof data only: its
callee-saved registers may hold secrets, and its tape is secret. -/
structure SearchLive (p : SearchPublic) (original : State) (used remaining : Nat) (s : State) : Prop where
  input : SearchInput p original
  used_le : used ≤ p.randLen
  remaining_le : remaining ≤ p.remaining
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  sp : s.sp = p.F - 16
  x19 : s.gpr .x19 = p.F
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.F 32 = original.gpr .x19
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = searchRand original
  e : Spec.Rsa.bytesAt s.mem p.ep p.elen = p.eB
  other : Spec.Rsa.bytesAt s.mem p.pp p.plen = searchP original
  headers : Slots s.mem p.F (p.headers used remaining)

namespace SearchLive

variable {p : SearchPublic} {original s t : State} {used remaining : Nat}

theorem headers_index {e : Nat × BitVec 64} (he : e ∈ p.headers used remaining) : e.1 < 20 :=
  p.headers_bound used remaining e he

/-- Through code that keeps `x19`, the stack pointer, the regions and the
callee-saved registers, and writes only what a candidate call may. -/
theorem restore (h : SearchLive p original used remaining s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame (SearchInput.callChanges original) s.mem t.mem) :
    SearchLive p original used remaining t := by
  have hc := h.input.frame_words hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.remaining_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .x19 (by decide) (by decide)).trans h.x19,
    fun r hr h19 h30 => (hg r hr h30).trans (h.saved r hr h19 h30),
    fun r hr => (hv r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedX19
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.e_frame hf').trans h.e
  · exact (h.input.p_frame hf').trans h.other
  · intro e he
    exact (hc e.1 (headers_index he)).trans (h.headers e he)

theorem keep (h : SearchLive p original used remaining s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SearchLive p original used remaining t := by
  apply h.restore kp.rd kp.wr kp.sp (fun reg hr _ => kp.gpr reg (hregs reg hr)) kp.vcs
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

/-- Through stores of frame words but the saved `x19`, to the counters `u`
and `k`. -/
theorem update (h : SearchLive p original used remaining s) {u k : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values)
    {rs : List Reg} (kp : Keep rs s t) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide)
    (hh : Slots t.mem p.F (p.headers u k)) : SearchLive p original u k t := by
  have hf : Frame (SearchInput.changes original) s.mem t.mem := by
    rw [hm]; exact h.frame_of_writeFrame values hb
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (hregs r hr)
  refine ⟨h.input, hu, hk, kp.rd.trans h.rd, kp.wr.trans h.wr, kp.sp.trans h.sp,
    (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, hh⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 4) = _
    rw [writeFrame_word _ _ _ hb 4 (by decide), frameValue_unchanged _ _ _ h4]
    exact h.savedX19
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.e_frame hf).trans h.e
  · exact (h.input.p_frame hf).trans h.other

end SearchLive

end VG.Proof.RsaKeyGen.AArch64.Search

end

end

-- separate module: its proofs build in parallel with those of `Call` and `Step`, which `Correct` and `CT` also import

/-! # The search's entry (AArch64)

In the frame the search allocates, the stack arguments and the state's
first word are loaded, the caller's `x19` saved in word 4 and the arguments
and public words stored in the frame (`entry_ok`); then, in the frame saving
`x30`, the search is at the tape's start with its counted candidates
(`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 (ld mov movi)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeEntropy)

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [hn]

/-- The frame's words on entry, in the order the entry stores them. -/
def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .x19), (5, s.gpr .x0), (6, s.gpr .x1), (7, s.gpr .x2), (8, s.gpr .x3), (9, s.gpr .x4),
    (10, s.gpr .x5), (11, s.gpr .x6), (12, s.gpr .x7), (13, stackArg s 0), (14, stackArg s 1),
    (15, stackArg s 2), (18, stackArg s 3), (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .x1),
    (2, (s.gpr .x1 <<< 15) + s.gpr .x1), (3, 0), (16, 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl) <;> dsimp only <;> decide

/-- The stack arguments' addresses, from the frame's base. -/
theorem arg_addr (sp : Addr) (k : Nat) :
    sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 (160 + 8 * k) = sp + BitVec.ofNat 64 (8 * k) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) (j : Nat) (hj : j < 4) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19]

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 160 s).wr = p.frame :: s.wr := by
  show _ = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [h.sp_eq]; rfl

theorem alloc_sp {p : SearchPublic} {s : State} (h : SearchInput p s) : (allocated 160 s).sp = p.F := by
  show _ = p.sp - _
  rw [h.sp_eq]; rfl

theorem entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) (allocated 160 s) fun t =>
      (t.gpr .x19 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s)) ∧
      Keep entryRegs (allocated 160 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 160 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hsp := alloc_sp h
  have hF : p.F = s.sp - BitVec.ofNat 64 160 := by show p.sp - _ = _; rw [h.sp_eq]
  have hrd : (allocated 160 s).rd ++ (allocated 160 s).wr = s.rd ++ (p.frame :: s.wr) := by
    rw [← alloc_wr h]; rfl
  have ha (k : Nat) (hk : k < 4) :
      InRegions ((allocated 160 s).rd ++ (allocated 160 s).wr)
        (p.F + BitVec.ofNat 64 (160 + 8 * k)) 8 := by
    rw [hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args h k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (k : Nat) (hk : k < 4) :
      s.mem.readW (p.F + BitVec.ofNat 64 (160 + 8 * k)) 64 = stackArg s k := by
    rw [hF, arg_addr]; rfl
  have hst : InRegions ((allocated 160 s).rd ++ (allocated 160 s).wr) (stackArg s 3) 8 := by
    refine ⟨inState s, ?_, ?_⟩
    · rw [hrd, h.1.2.2.2.1]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 v0 v1 v2 v3
  have hmem : (allocated 160 s).mem = s.mem := rfl
  refine WP.keep entryRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold entry writeFrame entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide), hsp, hmem,
    a0, a1, a2, a3, v0, v1, v2, v3, hst, BitVec.add_zero,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide), hs 64 (by decide),
    hs 72 (by decide), hs 80 (by decide), hs 88 (by decide), hs 96 (by decide), hs 104 (by decide),
    hs 112 (by decide), hs 120 (by decide), hs 144 (by decide), hs 0 (by decide), hs 8 (by decide),
    hs 16 (by decide), hs 24 (by decide), hs 128 (by decide)]
  rfl

/-- The state the body of the frame saving `x30` starts in (`WP.frameRegKept`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

theorem F_16 (p : SearchPublic) : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by
  rw [SearchPublic.F, BitVec.sub_sub]; rfl

/-- The push of `x30` writes only below the frame. -/
theorem push_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SearchInput.callChanges s) m (m.write (p.F - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 48⟩)
    (by simp [SearchInput.callChanges]) _ ?_
  rw [F_16, h.sp_eq]
  exact Offset.contains_below s.sp (a := 176) (b := 208) (by decide) (by decide) (by decide)

theorem search_start {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocated 160 s) t) :
    SearchLive p s 0 p.remaining (pushedX30 t) := by
  have hb := entryValues_bound s
  have hf₁ : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    apply (writeFrame_frame s.mem p.F _ hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [SearchInput.changes], h.frame_sub⟩
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← htsp] at hp
  have hf₂ : Frame (SearchInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (pushedX30 t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) :
      word (pushedX30 t).mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  have hL : p.len ≤ 512 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.1.2.1
  have hx1 : s.gpr .x1 = BitVec.ofNat 64 p.len := by
    rw [← h.2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  have hcap : (s.gpr .x1 <<< 15) + s.gpr .x1 = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hx1, SearchInit.shl_ofNat _ _ (by omega_using [hL]), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega_using []
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr.trans (alloc_wr h), ?_, hx, ?_, k.vcs, ?_, ?_, ?_,
    ?_, ?_⟩
  · show t.sp - 16 = p.F - 16
    rw [htsp]
  · intro r hr h19 _
    exact k.gpr r (by revert r hr h19; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hw 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]; rw [← h.2]; rfl
  · rw [h.e_frame hf₂]; rw [← h.2]; rfl
  · rw [h.p_frame hf₂]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (SearchPublic.headers_bound _ _ _ e he)]
    rw [← h.2] at he hcap hx1 ⊢
    simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      simp only [frameValue, entryValues, List.foldl_cons, List.foldl_nil, searchOfState, searchRemaining,
        searchLen, BitVec.ofNat_toNat, BitVec.setWidth_eq, hcap, BitVec.add_zero, Nat.sub_zero,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.AArch64.Search
