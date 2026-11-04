module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The RSA prime search's data (AArch64)

The public descriptor of a search (`SPub`: the arguments but the octets of
`p` and the tape, `e` and the counted candidates left), its frame of 20
words at `F = sp − 160`, and the loop's state (`SLive`): the frame's words
for the octets consumed and the counted candidates left, with the caller's
`x19` saved. The entry state is functional-proof data only: its tape and
`p` are secret, and its callee-saved registers may hold secrets.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController controllerValue controllerValue_unchanged
  writeController_frame_size)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

structure SPub where
  op : Addr
  up : Addr
  ep : Addr
  pp : Addr
  rp : Addr
  B : Addr
  stp : Addr
  sp : Addr
  len : Nat
  elen : Nat
  plen : Nat
  randLen : Nat
  Z : Nat
  remaining : Nat
  eB : List Byte

def sOfState (s : State) : SPub where
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

def SInput (p : SPub) (s : State) : Prop := searchPre s ∧ sOfState s = p

/-- The frame's base. -/
abbrev SPub.F (p : SPub) : Addr := p.sp - BitVec.ofNat 64 160

/-- The frame's region. -/
abbrev SPub.frame (p : SPub) : Region := ⟨p.F, 160⟩

/-- The search from octet `used` of `rand`, with `remaining` counted
candidates left. -/
abbrev SPub.tail (p : SPub) (pB rand : List Byte) (used remaining : Nat) : PrimeSearchResult :=
  primeSearch p.len p.eB pB remaining (rand.drop used)

/-- The search from a loop state, for the entry state `original`. -/
abbrev tailOf (p : SPub) (original : State) (used remaining : Nat) : PrimeSearchResult :=
  p.tail (searchP original) (searchRand original) used remaining

/-- The frame's words while the search goes on (but the request and the
status, which only a finished search has). -/
def SPub.headers (p : SPub) (used k : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 k), (1, BitVec.ofNat 64 p.len), (2, BitVec.ofNat 64 (primeEntropy p.len)),
    (5, p.op), (6, BitVec.ofNat 64 p.len), (7, p.up), (8, p.ep), (9, BitVec.ofNat 64 p.elen),
    (10, p.rp + BitVec.ofNat 64 used), (11, BitVec.ofNat 64 (p.randLen - used)),
    (12, BitVec.ofNat 64 used), (13, p.B), (15, BitVec.ofNat 64 (p.Z / 8)), (16, p.pp),
    (17, BitVec.ofNat 64 p.plen), (18, p.stp)]

theorem SPub.headers_bound (p : SPub) (used k : Nat) : ∀ e ∈ p.headers used k, e.1 < 20 := by
  simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> decide

theorem SPub.headers_index {p : SPub} {used k : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used k) : e.1 < 20 := p.headers_bound used k e he

/-! ## The frame's words -/

theorem frame_store_word (m : Mem) (B : Addr) (v : BitVec 64) {i j : Nat} (hi : i < 20) (hj : j < 20) :
    word (m.writeW (off B (8 * i)) v) B (8 * j) = if j = i then v else word m B (8 * j) := by
  by_cases he : j = i
  · subst he
    rw [ite_eq_left rfl]
    exact word_writeW_self _ _ _ _
  · rw [ite_eq_right he]
    exact hdrStore_hdr _ _ _ (by omega) (by omega) (Ne.symm he)

theorem frame_word (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 20) (j : Nat) (hj : j < 20) :
    word (writeController m B values) B (8 * j) = controllerValue values j (word m B (8 * j)) := by
  induction values generalizing m with
  | nil => rfl
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    change word (writeController (m.writeW (off B (8 * e.1)) e.2) B values) B (8 * j) = _
    rw [ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)), frame_store_word _ _ _ he hj]
    rfl

theorem frame_frame (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 20) :
    Frame [⟨B, 160⟩] m (writeController m B values) :=
  writeController_frame_size m B values (by decide) fun e he => by
    have := hvalues e he; omega_using [this]

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

theorem sp_eq (h : SInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem room (h : SInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem top (h : SInput p s) : p.sp.toNat + 32 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.1.1

theorem F_toNat (h : SInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 208 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [SPub.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : SInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  refine Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) ?_
  have := h.F_toNat
  have : 208 ≤ p.sp.toNat := h.room
  have := h.top
  omega

/-- The regions the search (and its callee) may write, and its stack. -/
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
  exact hf.bytes (h.read_disjoint hr) (by omega) (List.mem_range.mp hi)

theorem random_frame (h : SInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

theorem e_frame (h : SInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.ep p.elen = Spec.Rsa.bytesAt m p.ep p.elen := by
  rw [← h.2]
  exact h.bytes_frame (r := inE s) (by simp [inReads]) hf

theorem p_frame (h : SInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.pp p.plen = Spec.Rsa.bytesAt m p.pp p.plen := by
  rw [← h.2]
  exact h.bytes_frame (r := inP s) (by simp [inReads]) hf

/-- The frame is in the stack the search may use. -/
theorem frame_sub (h : SInput p s) : Region.Sub p.frame (below s.sp stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

/-- What a candidate call may write: the outputs, the working space, and the
stack below the frame. -/
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
theorem frame_disjoint (h : SInput p s) : ∀ r ∈ callChanges s, p.frame.Disjoint r := by
  have hsub := h.frame_sub
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fun x hx hy => h.stack_disjoint (r := inOut s) (by simp [inWrites]) x (hsub x hx) hy
  · exact fun x hx hy => h.stack_disjoint (r := inUsed s) (by simp [inWrites]) x (hsub x hx) hy
  · exact fun x hx hy => h.stack_disjoint (r := inScr s) (by simp [inWrites]) x (hsub x hx) hy
  · rw [← h.sp_eq]
    have hs := Offset.sep_below p.sp 208 (a := 160) (n := 160) (b := 208) (k := 48) (by decide) (by decide)
      (Or.inr (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (by simp only [Region.Contains, SPub.F] at hx; omega)
      (by simp only [Region.Contains] at hy; exact hy)

theorem frame_words (h : SInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 20) : word m' p.F (8 * j) = word m p.F (8 * j) :=
  hf.readW (r := p.frame) (Offset.contains_base _ (by omega) (by omega))
    (h.frame_disjoint) (by decide)

theorem out_eq (h : SInput p s) : inOut s = ⟨p.op, p.len⟩ := by rw [← h.2]; rfl
theorem used_eq (h : SInput p s) : inUsed s = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
theorem state_eq (h : SInput p s) : inState s = ⟨p.stp, 32⟩ := by rw [← h.2]; rfl

end SInput

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (SInput.callChanges s) m m') :
    Frame (SInput.changes s) m m' := hf.sub (SInput.callChanges_sub s)

/-! ## The loop states -/

/-- A state of the loop, in the frame saving `x30`: `used` octets consumed,
`k` counted candidates left. -/
structure SLive (p : SPub) (original : State) (used k : Nat) (s : State) : Prop where
  input : SInput p original
  used_le : used ≤ p.randLen
  k_le : k ≤ p.remaining
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
  headers : Slots s.mem p.F (p.headers used k)

/-- A finished search, before `finish` stores its results. -/
structure SDone (p : SPub) (original : State) (result : PrimeSearchResult) (s : State) : Prop where
  input : SInput p original
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  x19 : s.gpr .x19 = p.F
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.F 32 = original.gpr .x19
  usedPtr : word s.mem p.F (8 * 7) = p.up
  stp : word s.mem p.F (8 * 18) = p.stp
  len : word s.mem p.F (8 * 1) = BitVec.ofNat 64 p.len
  cap : word s.mem p.F (8 * 2) = BitVec.ofNat 64 (primeEntropy p.len)
  remaining : word s.mem p.F (8 * 0) = BitVec.ofNat 64 result.remaining
  request : word s.mem p.F (8 * 3) = BitVec.ofNat 64 result.requested
  used : word s.mem p.F (8 * 12) = BitVec.ofNat 64 result.used
  status : word s.mem p.F (8 * 14) = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt s.mem p.op p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0

/-- The loads and stores of the frame's words. -/
structure CtlAccess (s : State) (B : Addr) : Prop where
  ld : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  st : ∀ d, d + 8 ≤ 160 → InRegions s.wr (B + BitVec.ofNat 64 d) 8
  ld0 : InRegions (s.rd ++ s.wr) B 8
  st0 : InRegions s.wr B 8

theorem CtlAccess.of_scr {s : State} {B : Addr} (scr : Scr s B 160) : CtlAccess s B :=
  ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩

/-- The frame's words after writes of `values`. -/
theorem headers_after {p : SPub} {s t : State} (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) (hm : t.mem = writeController s.mem p.F values)
    {used k : Nat}
    (hv : ∀ e ∈ p.headers used k, controllerValue values e.1 (word s.mem p.F (8 * e.1)) = e.2) :
    Slots t.mem p.F (p.headers used k) := by
  intro e he
  rw [hm, frame_word _ _ _ hb e.1 (SPub.headers_index he)]
  exact hv e he

namespace SLive

variable {p : SPub} {original s t : State} {used k : Nat}

theorem access (h : SLive p original used k s) : CtlAccess s p.F :=
  CtlAccess.of_scr (h.input.frame_scr h.wr)

theorem header (h : SLive p original used k s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used k) : word s.mem p.F (8 * j) = v :=
  h.headers (j, v) hj

theorem rand_length (h : SLive p original used k s) : (searchRand original).length = p.randLen := by
  rw [← h.input.2]; simp only [sOfState, searchRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]

/-- Through code that keeps `x19`, the stack pointer, the regions, the
frame's words, and writes only the output, `used`, the working space and the
stack below the frame. -/
theorem restore (h : SLive p original used k s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame (SInput.callChanges original) s.mem t.mem) :
    SLive p original used k t := by
  have hc := h.input.frame_words hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.k_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .x19 (by decide) (by decide)).trans h.x19,
    fun r hr h19 h30 => (hg r hr h30).trans (h.saved r hr h19 h30),
    fun r hr => (hv r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedX19
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.e_frame hf').trans h.e
  · exact (h.input.p_frame hf').trans h.other
  · intro e he
    exact (hc e.1 (SPub.headers_index he)).trans (h.headers e he)

theorem keep (h : SLive p original used k s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SLive p original used k t := by
  apply h.restore kp.rd kp.wr kp.sp (fun reg hr _ => kp.gpr reg (hregs reg hr)) kp.vcs
  rw [hm]
  exact Frame.refl _ _

/-- The search's memory moves only within what it may write. -/
theorem frame_of_writes (h : SLive p original used k s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20) :
    Frame (SInput.changes original) s.mem (writeController s.mem p.F values) := by
  apply (frame_frame s.mem p.F values hb).sub
  intro region hregion
  obtain rfl := List.mem_singleton.mp hregion
  exact ⟨_, by simp [SInput.changes], h.input.frame_sub⟩

/-- Through writes of the frame's words but the saved `x19`. -/
theorem update (h : SLive p original used k s) {u k' : Nat}
    (hu : u ≤ p.randLen) (hk : k' ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.F values)
    (kp : Keep [.x0, .x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s t)
    (hh : Slots t.mem p.F (p.headers u k')) : SLive p original u k' t := by
  have hf : Frame (SInput.changes original) s.mem t.mem := by
    rw [hm]; exact h.frame_of_writes values hb
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  refine ⟨h.input, hu, hk, kp.rd.trans h.rd, kp.wr.trans h.wr,
    kp.sp.trans h.sp, (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.F values) p.F (8 * 4) = _
    rw [frame_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedX19
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.e_frame hf).trans h.e
  · exact (h.input.p_frame hf).trans h.other

end SLive

theorem SDone.keep {p : SPub} {original s t : State} {result : PrimeSearchResult}
    (h : SDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ (hregs .x19 (by decide))).trans h.x19,
    fun reg hr h19 h30 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h19 h30),
    fun r hr => (k.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedX19, h.usedPtr, h.stp, h.len, h.cap, h.remaining, h.request, h.used, h.status, h.output]

end VG.Proof.RsaKeyGen.AArch64.Search
