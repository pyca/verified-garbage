module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Search
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

/-! ### `RsaKeyGen.RISCV64.Search.Data`, which this module and modules that import it used -/

section

/-! # The search's public data and its loop states (RISCV64)

As on AArch64 (`Proof/RsaKeyGen/AArch64/Search/Entry.lean`): the search keeps
its working state in the 20 words at `sp - 160` (`SearchPublic.F`) of the
frame it allocates, with their base in `s0`; the loop runs below it, in the
16-byte frame saving `ra`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

def searchOfState (s : State) : SearchPublic where
  op := s.gpr .a0
  up := s.gpr .a2
  ep := s.gpr .a3
  pp := s.gpr .a5
  rp := s.gpr .a7
  B := stackArg s 1
  stp := stackArg s 3
  sp := s.sp
  len := searchLen s
  elen := (s.gpr .a4).toNat
  plen := (s.gpr .a6).toNat
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

theorem wr_eq (h : SearchInput p s) : s.wr = inWrites s := h.base.2.2.2.2.1

theorem rd_mem (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) : r ∈ s.rd := by
  have e : (stripConsts tables s).rd = inReads s := h.base.2.2.2.1
  rw [← e] at hr
  exact List.mem_of_mem_take hr

theorem nowrap (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.base.2.2.2.2.2.1 r hr

theorem write_disjoint (h : SearchInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.base.2.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.base.2.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : SearchInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.base.2.2.2.2.2.2.1

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

theorem tab_al (h : SearchInput p s) : (tabR s).base.toNat % 8 = 0 := by
  have := h.consts.aligned tab_mem
  show (s.syms _).toNat % 8 = 0
  omega_using [this]

theorem tab_wr (h : SearchInput p s) {r : Region} (hr : r ∈ s.wr) : (tabR s).Disjoint r :=
  (h.consts.2.2.1 _ (tab_reg s)).2.1 r hr

theorem tab_stack (h : SearchInput p s) : (tabR s).Disjoint (below s.sp stackUse) :=
  (h.consts.2.2.1 _ (tab_reg s)).2.2 _ (by simp [abi, stackBelow, below])

theorem tab_held (h : SearchInput p s) (i : Nat) (hi : i < 1024) :
    s.mem.readW (s.syms Impl.RsaKeyGen.TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 :=
  h.consts.readW tab_mem (by rw [packed_length]; exact hi)

theorem sp_eq (h : SearchInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem used_al (h : SearchInput p s) : (s.gpr .a2).toNat % 8 = 0 := h.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem scratch_al (h : SearchInput p s) : (stackArg s 1).toNat % 8 = 0 :=
  h.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem state_al (h : SearchInput p s) : (stackArg s 3).toNat % 8 = 0 :=
  h.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem sp16 (h : SearchInput p s) : p.sp.toNat % 16 = 0 := by rw [h.sp_eq]; exact h.base.1

theorem room (h : SearchInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.base.2.2.1

theorem top (h : SearchInput p s) : p.sp.toNat + 32 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.base.2.1

theorem F_toNat (h : SearchInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 496 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [SearchPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega_using [this]), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : SearchInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  have := h.F_toNat
  have : 496 ≤ p.sp.toNat := h.room
  have := h.top
  have := h.sp16
  exact Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) (by omega_arith) (by omega_arith)

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
  [inOut s, inUsed s, inScr s, ⟨s.sp - BitVec.ofNat 64 stackUse, 336⟩]

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
    have hs := Offset.sep_below p.sp 496 (a := 160) (n := 160) (b := 496) (k := 336) (by decide) (by decide)
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

/-! ## What straight-line code keeps -/

/-- The registers but `rs`, the permissions and the stack pointer keep their
values. -/
structure KeepS (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace KeepS

theorem refl (rs : List Reg) (s : State) : KeepS rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepS rs s₁ s₂) (h₂ : KeepS rs' s₂ s₃) :
    KeepS (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : KeepS rs s s')
    (hr : ∀ r ∈ rs, r ∈ rs' := by decide) : KeepS rs' s s' :=
  ⟨fun r hn => h.gpr r fun h' => hn (hr r h'), h.rd, h.wr, h.sp⟩

theorem trans' {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepS rs s₁ s₂) (h₂ : KeepS rs s₂ s₃) :
    KeepS rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mem (s : State) (m : Mem) : KeepS [] s { s with mem := m } := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem write (s : State) (r : Reg) (v : BitVec 64) : KeepS [r] s (s.write r v) :=
  ⟨fun r' hr => RegUpd.gpr_write_of_ne s v (by simpa using hr), rfl, rfl, rfl⟩

end KeepS

/-- `WP.keep`, with the stack pointer. -/
theorem WP.keep' {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : callFree c = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ KeepS rs s s' :=
  WP.mono (WP.rdwr (WP.keep rs h hc hn)) fun _ ⟨⟨hq, k⟩, _, _, hsp⟩ => ⟨hq, ⟨fun _ hr => k.gpr hr, k.2.1, k.2.2, hsp⟩⟩

/-- `WP.keep'`, with the addresses of statics kept. -/
theorem WP.keepS {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : callFree c = true := by decide +kernel) :
    WP isa c s fun s' => (Q s' ∧ KeepS rs s s') ∧ s'.syms = s.syms :=
  VG.RISCV64.WP.mono_syms (WP.keep' rs h hc hn) fun _ h hy => ⟨h, hy⟩

/-! ## The loop states -/

/-- A state of the loop, in the frame saving `ra`: `used`
octets consumed, `remaining` counted candidates left. The entry state is
functional-proof data only: its callee-saved registers may hold secrets, and
its tape is secret. -/
structure SearchLive (p : SearchPublic) (original : State) (used remaining : Nat) (s : State) : Prop where
  input : SearchInput p original
  used_le : used ≤ p.randLen
  remaining_le : remaining ≤ p.remaining
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  sp : s.sp = p.F - 16
  s0 : s.gpr .s0 = p.F
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  syms : s.syms = original.syms
  savedS0 : word s.mem p.F 32 = original.gpr .s0
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = searchRand original
  e : Spec.Rsa.bytesAt s.mem p.ep p.elen = p.eB
  other : Spec.Rsa.bytesAt s.mem p.pp p.plen = searchP original
  tab : Frame (SearchInput.changes original) original.mem s.mem
  headers : Slots s.mem p.F (p.headers used remaining)

namespace SearchLive

variable {p : SearchPublic} {original s t : State} {used remaining : Nat}

theorem headers_index {e : Nat × BitVec 64} (he : e ∈ p.headers used remaining) : e.1 < 20 :=
  p.headers_bound used remaining e he

/-- Through code that keeps `s0`, the stack pointer, the regions and the
callee-saved registers, and writes only what a candidate call may. -/
theorem restore (h : SearchLive p original used remaining s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (SearchInput.callChanges original) s.mem t.mem) :
    SearchLive p original used remaining t := by
  have hc := h.input.frame_words hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.remaining_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .s0 (by decide)).trans h.s0,
    fun r hr h31 => (hg r hr).trans (h.saved r hr h31), hy.trans h.syms, ?_, ?_, ?_, ?_, h.tab.trans hf', ?_⟩
  · exact (hc 4 (by decide)).trans h.savedS0
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.e_frame hf').trans h.e
  · exact (h.input.p_frame hf').trans h.other
  · intro e he
    exact (hc e.1 (headers_index he)).trans (h.headers e he)

theorem keep (h : SearchLive p original used remaining s) {rs : List Reg}
    (kp : KeepS rs s t) (hm : t.mem = s.mem) (hy : t.syms = s.syms)
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

/-- Through stores of frame words but the saved `s0`, to the counters `u`
and `k`. -/
theorem update (h : SearchLive p original used remaining s) {u k : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values) (hy : t.syms = s.syms)
    {rs : List Reg} (kp : KeepS rs s t) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide)
    (hh : Slots t.mem p.F (p.headers u k)) : SearchLive p original u k t := by
  have hf : Frame (SearchInput.changes original) s.mem t.mem := by
    rw [hm]; exact h.frame_of_writeFrame values hb
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (hregs r hr)
  refine ⟨h.input, hu, hk, kp.rd.trans h.rd, kp.wr.trans h.wr, kp.sp.trans h.sp,
    (hg .s0 (by decide)).trans h.s0,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), hy.trans h.syms, ?_, ?_, ?_, ?_,
    h.tab.trans hf, hh⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 4) = _
    rw [writeFrame_word _ _ _ hb 4 (by decide), frameValue_unchanged _ _ _ h4]
    exact h.savedS0
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.e_frame hf).trans h.e
  · exact (h.input.p_frame hf).trans h.other

end SearchLive

end VG.Proof.RsaKeyGen.RISCV64.Search

end

end

-- separate module: its proofs build in parallel with those of `Call` and `Step`, which `Correct` and `CT` also import

/-! # The search's entry (RISC-V)

In the frame the search allocates, the stack arguments and the state's
first word are loaded, the caller's `s0` saved in word 4 and the arguments
and public words stored in the frame (`entry_ok`); then, in the frame saving
`ra` (`WP.frameRegAny`, for a body with any frames), the search is at the
tape's start with its counted candidates (`search_start`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Search
open VG.Spec.RsaKeyGen (primeEntropy)

/-- `WP.frameReg` for a body with any frames (`sdepth`), as on PPC64LE
(`Proof/Framework/PPC64LE/CallAny.lean`). -/
theorem WP.frameRegAny {r : Reg} {main : Prog isa} {s₀ : State} {Q : State → Prop}
    (hsp : 16 ≤ s₀.sp.toNat) (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 16, 16⟩ R)
    (hmain : WP isa main (framed r s₀) fun s₂ => Q { s₂.write r (s₀.gpr r) with sp := s₀.sp })
    (hn : sdepth main + 16 < 2 ^ 64) :
    WP isa (.frame (.push r) main (.pop r)) s₀ Q := by
  refine WP.frame hsp (WP.narrowAny (rd := s₀.rd) (wr := s₀.wr) hmain ?_ ?_ ?_ (by omega_using [hn]))
  · intro a n hi
    exact InRegions_append_cons.mpr (.inr hi)
  · intro a n hi
    exact InRegions_append_cons (xs := []).mpr (.inr hi)
  · intro s' hrd hwr hsp' hf hq
    obtain hread : s'.mem.read (s'.sp + 8) 8 = s₀.gpr r := by
      rw [hsp', show (pushed r s₀).sp = s₀.sp - 16 from rfl,
        hf.read (r := ⟨s₀.sp - 16, 16⟩) (frame_contains s₀.sp) (fun R hR => ?_) (by decide)]
      · exact read_write_self _ _ _
      · rcases List.mem_append.mp hR with hR | hR
        · exact hd R hR
        · simp only [List.mem_singleton] at hR; subst hR
          exact frame_not_below s₀.sp hn
    obtain e : popped r s' = { (s'.withRegions s₀.rd s₀.wr).write r (s₀.gpr r) with sp := s₀.sp } := by
      simp only [popped, hread]
      simp only [hsp', hwr, pushed, List.tail_cons, BitVec.sub_add_cancel]
      cases s'
      simp only [pushed] at hrd
      subst hrd
      rfl
    rw [e]; exact hq

/-- The frame's words on entry, in the order the entry stores them. -/
def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .s0), (5, s.gpr .a0), (6, s.gpr .a1), (7, s.gpr .a2), (8, s.gpr .a3), (9, s.gpr .a4),
    (10, s.gpr .a5), (11, s.gpr .a6), (12, s.gpr .a7), (13, stackArg s 0), (14, stackArg s 1),
    (15, stackArg s 2), (18, stackArg s 3), (0, s.mem.readW (stackArg s 3) 64), (1, s.gpr .a1),
    (2, (s.gpr .a1 <<< 15) + s.gpr .a1), (3, 0), (16, 0)]

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
  refine ⟨inArgs s, List.mem_append_left _ (h.rd_mem (by simp [inReads])), ?_⟩
  simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0]

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocd 160 s).wr = p.frame :: s.wr := by
  show _ = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [h.sp_eq]; rfl

theorem alloc_sp {p : SearchPublic} {s : State} (h : SearchInput p s) : (allocd 160 s).sp = p.F := by
  show _ = p.sp - _
  rw [h.sp_eq]; rfl

theorem entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) (allocd 160 s) fun t =>
      ((t.gpr .s0 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s)) ∧
      Keep entryRegs (allocd 160 s) t) ∧ t.sp = p.F := by
  obtain scr := h.frame_scr (alloc_wr h)
  obtain hsp := alloc_sp h
  obtain hF : p.F = s.sp - BitVec.ofNat 64 160 := by show p.sp - _ = _; rw [h.sp_eq]
  obtain hrd : (allocd 160 s).rd ++ (allocd 160 s).wr = s.rd ++ (p.frame :: s.wr) := by
    rw [← alloc_wr h]; rfl
  have ha (k : Nat) (hk : k < 4) :
      InRegions ((allocd 160 s).rd ++ (allocd 160 s).wr) (p.F + BitVec.ofNat 64 (160 + 8 * k)) 8 := by
    rw [hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args h k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (k : Nat) (hk : k < 4) :
      s.mem.readW (p.F + BitVec.ofNat 64 (160 + 8 * k)) 64 = stackArg s k := by
    rw [hF, arg_addr]; rfl
  have hal (k : Nat) (hk : k < 4) : (p.F + BitVec.ofNat 64 (160 + 8 * k)).toNat % 8 = 0 := by
    rw [hF, arg_addr]
    obtain h16 : s.sp.toNat % 16 = 0 := by have := h.sp16; rwa [h.sp_eq] at this
    obtain ht : s.sp.toNat + 32 ≤ 2 ^ 64 := by have := h.top; rwa [h.sp_eq] at this
    obtain e : (s.sp + BitVec.ofNat 64 (8 * k)).toNat = s.sp.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hk, ht]
    rw [e]; omega_using [h16]
  obtain hst : InRegions ((allocd 160 s).rd ++ (allocd 160 s).wr) (stackArg s 3 + BitVec.ofNat 64 0) 8 := by
    rw [hrd, BitVec.add_zero]
    refine ⟨inState s, ?_, ?_⟩
    · rw [h.wr_eq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
    · simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
  obtain hsal : (stackArg s 3 + BitVec.ofNat 64 0).toNat % 8 = 0 := by
    rw [BitVec.add_zero]; exact h.state_al
  obtain a0 := ha 0 (by decide)
  obtain a1 := ha 1 (by decide)
  obtain a2 := ha 2 (by decide)
  obtain a3 := ha 3 (by decide)
  obtain v0 := hv 0 (by decide)
  obtain v1 := hv 1 (by decide)
  obtain v2 := hv 2 (by decide)
  obtain v3 := hv 3 (by decide)
  obtain l0 := hal 0 (by decide)
  obtain l1 := hal 1 (by decide)
  obtain l2 := hal 2 (by decide)
  obtain l3 := hal 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 v0 v1 v2 v3 l0 l1 l2 l3
  have hmem : (allocd 160 s).mem = s.mem := rfl
  refine WP.mono (WP.rdwr (WP.keep entryRegs ?_ (by decide +kernel))) fun t ⟨⟨hq, k⟩, _, _, hsp'⟩ =>
    ⟨⟨hq, k⟩, hsp'.trans hsp⟩
  obtain ea : ∀ t : State, exec (.addSp .t6 0) t = some (t.write .t6 (t.sp + BitVec.ofNat 64 0)) := by
    intro t; simp [exec]
  obtain hz : p.F + BitVec.ofNat 64 0 = p.F := BitVec.add_zero _
  obtain hs0 : InRegions (allocd 160 s).wr p.F 8 := by
    have := scr.st (d := 0) (n := 8) (by decide); simpa only [off, hz] using this
  obtain hl0 : p.F.toNat % 8 = 0 := by
    have := scr.al8 (d := 0) (by decide) (by decide); simpa only [off, hz] using this
  unfold entry writeFrame entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [stf, ea, hsp, hz, hs0, hl0, hmem, exec_li, a0, a1, a2, a3, v0, v1, v2, v3, l0, l1, l2, l3, hst, hsal,
    scr.st (d := 0) (n := 8) (by decide), scr.al8 (d := 0) (by decide) (by decide), scr.st (d := 8) (n := 8) (by decide), scr.al8 (d := 8) (by decide) (by decide), scr.st (d := 16) (n := 8) (by decide), scr.al8 (d := 16) (by decide) (by decide), scr.st (d := 24) (n := 8) (by decide), scr.al8 (d := 24) (by decide) (by decide), scr.st (d := 32) (n := 8) (by decide), scr.al8 (d := 32) (by decide) (by decide), scr.st (d := 40) (n := 8) (by decide), scr.al8 (d := 40) (by decide) (by decide), scr.st (d := 48) (n := 8) (by decide), scr.al8 (d := 48) (by decide) (by decide), scr.st (d := 56) (n := 8) (by decide), scr.al8 (d := 56) (by decide) (by decide), scr.st (d := 64) (n := 8) (by decide), scr.al8 (d := 64) (by decide) (by decide), scr.st (d := 72) (n := 8) (by decide), scr.al8 (d := 72) (by decide) (by decide), scr.st (d := 80) (n := 8) (by decide), scr.al8 (d := 80) (by decide) (by decide), scr.st (d := 88) (n := 8) (by decide), scr.al8 (d := 88) (by decide) (by decide), scr.st (d := 96) (n := 8) (by decide), scr.al8 (d := 96) (by decide) (by decide), scr.st (d := 104) (n := 8) (by decide), scr.al8 (d := 104) (by decide) (by decide), scr.st (d := 112) (n := 8) (by decide), scr.al8 (d := 112) (by decide) (by decide), scr.st (d := 120) (n := 8) (by decide), scr.al8 (d := 120) (by decide) (by decide), scr.st (d := 128) (n := 8) (by decide), scr.al8 (d := 128) (by decide) (by decide), scr.st (d := 144) (n := 8) (by decide), scr.al8 (d := 144) (by decide) (by decide), off]
  simp only [BitVec.add_zero]
  rfl

theorem F_16_8 (p : SearchPublic) : p.F - 16 + 8 = p.sp - BitVec.ofNat 64 168 := by
  rw [SearchPublic.F, BitVec.sub_sub, Offset.sub_ofNat_eq p.sp (show 168 ≤ 176 by decide)]; rfl

/-- The push of `ra` writes only below the frame. -/
theorem push_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SearchInput.callChanges s) m (m.write (p.F - 16 + 8) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 336⟩)
    (by simp [SearchInput.callChanges]) _ ?_
  rw [F_16_8, h.sp_eq]
  exact Offset.contains_below s.sp (a := 168) (b := 496) (by decide) (by decide) (by decide)

theorem search_start {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .s0 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocd 160 s) t) (htsp : t.sp = p.F) (hy : t.syms = s.syms) :
    SearchLive p s 0 p.remaining (framed .ra t) := by
  obtain hb := entryValues_bound s
  obtain hf₁ : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    apply (writeFrame_frame s.mem p.F _ hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [SearchInput.changes], h.frame_sub⟩
  obtain hp := push_frame h t.mem (t.gpr .ra)
  rw [← htsp] at hp
  obtain hf₂ : Frame (SearchInput.changes s) s.mem (framed .ra t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 20) : word (framed .ra t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) :
      word (framed .ra t).mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  obtain hL : p.len ≤ 512 := by rw [← h.2]; exact h.base.2.2.2.2.2.2.2.2.2.1.2.1
  obtain hx1 : s.gpr .a1 = BitVec.ofNat 64 p.len := by
    rw [← h.2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  obtain hcap : (s.gpr .a1 <<< 15) + s.gpr .a1 = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hx1, SearchInit.shl_ofNat _ _ (by omega_using [hL]), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega_using []
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.2.1, k.2.2.trans (alloc_wr h), ?_, hx, ?_, hy, ?_, ?_, ?_, ?_,
    hf₂, ?_⟩
  · show t.sp - 16 = p.F - 16
    rw [htsp]
  · intro r hr h0
    exact k.gpr (by revert r hr h0; decide)
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

end VG.Proof.RsaKeyGen.RISCV64.Search
