module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Generate
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Data
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Step
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Correct
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.Bignum.Layout

/-! # RSA key generation's controller on RISC-V: its public data, frame and loop states -/

@[expose] public section

/-! ## The controller's public data, its frame and its loop states (RISCV64)

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Generate/Classify.lean`): `GenPublic`
is everything two constant-time runs share: the arguments, the primes'
octets, the exponent and the table's address. The controller keeps its
working state in the 14 words at `sp - 112` (`GenPublic.F`) of the frame it
allocates, with their base in `s0`; the loop runs below it, in the 16-byte
frame saving `ra`, as the prime search's does
(`Proof/RsaKeyGen/RISCV64/Search/Data.lean`).
-/

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

structure GenPublic where
  kp : Addr
  up : Addr
  rp : Addr
  B : Addr
  stp : Addr
  sp : Addr
  L : Nat
  randLen : Nat
  Z : Nat
  eB : List Byte
  /-- The table of trial division. -/
  T : Addr

/-- The frame's base. -/
abbrev GenPublic.F (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 112

/-- The frame's region. -/
abbrev GenPublic.frame (p : GenPublic) : Region := ⟨p.F, 112⟩

/-- The frame's words while the search goes on (but the status, and the
region to zero). -/
def GenPublic.headers (p : GenPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, p.kp), (1, BitVec.ofNat 64 p.L), (2, p.up), (3, p.rp), (4, BitVec.ofNat 64 p.randLen), (5, p.B),
    (6, BitVec.ofNat 64 (p.Z / 8)), (7, p.stp), (8, BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (limitOf p.L p.eB))]

theorem GenPublic.headers_bound (p : GenPublic) (used : Nat) : ∀ e ∈ p.headers used, e.1 < 14 := by
  simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

def genOfState (s : State) : GenPublic where
  kp := s.gpr .a0
  up := s.gpr .a2
  rp := s.gpr .a3
  B := s.gpr .a5
  stp := s.gpr .a7
  sp := s.sp
  L := genLen s
  randLen := (s.gpr .a4).toNat
  Z := (s.gpr .a6).toNat * 8
  eB := genE s
  T := s.syms Impl.RsaKeyGen.TrialTable32.symbol

def GenInput (p : GenPublic) (s : State) : Prop := genPre s ∧ genOfState s = p

/-- The phase's word in the state. -/
def phaseWord : KeyPhase → Nat
  | .p => 0
  | .q _ => 1

/-- The key's buffer's slot `j` (`p_len` octets each). -/
abbrev GenPublic.slot (p : GenPublic) (j : Nat) : Addr := p.kp + BitVec.ofNat 64 (j * p.L)

/-- The state's words for the progress `st`, and the exponent. -/
structure StateOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  remaining : word m p.stp 0 = BitVec.ofNat 64 st.remaining
  len : word m p.stp 8 = BitVec.ofNat 64 p.L
  cap : word m p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L)
  phase : word m p.stp 32 = BitVec.ofNat 64 (phaseWord st.phase)
  left : word m p.stp 40 = BitVec.ofNat 64 st.left
  e : Spec.Rsa.bytesAt m (p.stp + 48) 8 = p.eB
  remaining_le : st.remaining ≤ limitOf p.L p.eB
  left_lt : st.left < 2 ^ 64

/-- The key's buffer for the progress `st`: zeros but `p`'s slot, which holds
`p` for `q`'s search. -/
structure KeyOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  low : Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0
  high : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0
  other : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB

/-- The table's region. -/
abbrev tabR (s : State) : Region := ⟨s.syms Impl.RsaKeyGen.TrialTable32.symbol, 8 * 1024⟩

/-! ## Where the buffers are -/

namespace GenInput

variable {p : GenPublic} {s : State}

theorem base (h : GenInput p s) : basePre (stripConsts tables s) := h.1.1

theorem consts (h : GenInput p s) : ConstsOk tables stackUse s := h.1.2

theorem wr_eq (h : GenInput p s) : s.wr = inWrites s := h.base.2.2.2.1

theorem rd_mem (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) : r ∈ s.rd := by
  have e : (stripConsts tables s).rd = inReads s := h.base.2.2.1
  rw [← e] at hr
  exact List.mem_of_mem_take hr

theorem nowrap (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.base.2.2.2.2.1 r hr

theorem write_disjoint (h : GenInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.base.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.base.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : GenInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.base.2.2.2.2.2.1

theorem tab_mem : (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed) ∈ tables :=
  List.mem_singleton_self _

theorem packed_length : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

theorem tables_eq : tables = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

theorem tab_reg (s : State) : tabR s ∈ constRegs tables s := by
  rw [tables_eq, constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length]
  exact List.mem_singleton_self _

theorem tab_rd (h : GenInput p s) : tabR s ∈ s.rd := by
  have := h.consts.mem_rd tab_mem
  rw [packed_length] at this
  exact this

theorem tab_fit (h : GenInput p s) : (tabR s).base.toNat + (tabR s).len ≤ 2 ^ 64 := by
  have := h.consts.fit tab_mem
  rw [packed_length] at this
  exact this

theorem tab_wr (h : GenInput p s) {r : Region} (hr : r ∈ s.wr) : (tabR s).Disjoint r :=
  (h.consts.2.2.1 _ (tab_reg s)).2.1 r hr

theorem tab_stack (h : GenInput p s) : (tabR s).Disjoint (below s.sp stackUse) :=
  (h.consts.2.2.1 _ (tab_reg s)).2.2 _ (by simp [abi, stackBelow, below])

theorem tab_held (h : GenInput p s) (i : Nat) (hi : i < 1024) :
    s.mem.readW (s.syms Impl.RsaKeyGen.TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 :=
  h.consts.readW tab_mem (by rw [packed_length]; exact hi)

theorem sp_eq (h : GenInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem room (h : GenInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.base.2.1

theorem sp16 (h : GenInput p s) : p.sp.toNat % 16 = 0 := by rw [h.sp_eq]; exact h.base.1

theorem used_al (h : GenInput p s) : (s.gpr .a2).toNat % 8 = 0 :=
  h.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem scratch_al (h : GenInput p s) : (s.gpr .a5).toNat % 8 = 0 :=
  h.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem state_al (h : GenInput p s) : (s.gpr .a7).toNat % 8 = 0 :=
  h.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem tab_al (h : GenInput p s) : (tabR s).base.toNat % 8 = 0 := by
  have := h.consts.aligned tab_mem
  show (s.syms _).toNat % 8 = 0
  omega

theorem F_toNat (h : GenInput p s) : p.F.toNat = p.sp.toNat - 112 := by
  have : 656 ≤ p.sp.toNat := h.room
  have h112 : (BitVec.ofNat 64 112).toNat = 112 := rfl
  rw [GenPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h112]; omega), h112]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : GenInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 112 := by
  have := h.F_toNat
  have : 656 ≤ p.sp.toNat := h.room
  have := p.sp.isLt
  have := h.sp16
  exact Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) (by omega) (by omega)

/-- The regions the controller (and its callees) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below s.sp stackUse]

theorem read_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem bytes_frame (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega) (List.mem_range.mp hi)

theorem random_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

/-- The table's words, through what the controller may write. -/
theorem tab_frame (h : GenInput p s) {m' : Mem} (hf : Frame (changes s) s.mem m') (i : Nat) (hi : i < 1024) :
    m'.readW (s.syms Impl.RsaKeyGen.TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  rw [← h.tab_held i hi]
  refine hf.readW (r := tabR s) (Offset.contains_base _ (by omega) (by have := h.tab_fit; omega))
    (fun w hw => ?_) (by decide)
  rcases List.mem_append.mp hw with hw | hw
  · exact h.tab_wr (by rw [h.wr_eq]; exact hw)
  · obtain rfl := List.mem_singleton.mp hw
    exact h.tab_stack

/-- The frame is in the stack the controller may use. -/
theorem frame_sub (h : GenInput p s) : Region.Sub p.frame (below s.sp stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

theorem frame_disjoint_writes (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s) : p.frame.Disjoint r :=
  fun x hx hy => (h.stack_disjoint (List.mem_append_left _ hr)) x (h.frame_sub x hx) hy

/-- What a step may write: the key's buffer, `used`, the working space, the
state's first four words, and the stack below the frame. -/
def callChanges (s : State) : List Region :=
  [inKey s, inUsed s, inScr s, ⟨s.gpr .a7, 32⟩, ⟨s.sp - BitVec.ofNat 64 stackUse, 544⟩]

theorem state32_sub (s : State) : Region.Sub ⟨s.gpr .a7, 32⟩ (inState s) := by
  unfold inState
  exact Region.sub_prefix (by decide)

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], state32_sub s⟩
  · exact ⟨below s.sp stackUse, by simp [changes], Region.sub_prefix (by decide)⟩

/-- The frame is disjoint from what a step writes. -/
theorem frame_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, p.frame.Disjoint r := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact (h.frame_disjoint_writes (r := inState s) (by simp [inWrites])).sub_right (state32_sub s)
  · rw [← h.sp_eq]
    have hs := Offset.sep_below p.sp 656 (a := 112) (n := 112) (b := 656) (k := 544) (by decide) (by decide)
      (Or.inr (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (by simp only [Region.Contains, GenPublic.F] at hx; omega)
      (by simp only [Region.Contains] at hy; exact hy)

theorem frame_words (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 14) : word m' p.F (8 * j) = word m p.F (8 * j) :=
  hf.readW (r := p.frame) (Offset.contains_base _ (by omega) (by omega)) h.frame_disjoint (by decide)

/-- The state's last three words. -/
abbrev stateTail (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 32, 24⟩

theorem tail_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, (stateTail p).Disjoint r := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hstp : s.gpr .a7 = p.stp := by rw [← h.2]; rfl
  have hsub : Region.Sub (stateTail p) (inState s) := by rw [hst]; exact Offset.sub_base _ (by decide)
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hpw.1.2.2.symm).sub_left hsub
  · exact (hpw.2.1.2.symm).sub_left hsub
  · exact (hpw.2.2.1.symm).sub_left hsub
  · rw [hstp]
    exact fun x hx hy => by
      simp only [Region.Contains] at hx hy
      have := Offset.sep p.stp (d := 32) (n := 24) (e := 0) (k := 32) (Or.inr (by decide)) (by decide) (by decide)
      rw [BitVec.add_zero] at this
      exact this x (by omega) (by omega)
  · exact fun x hx hy => (h.stack_disjoint (r := inState s) (by simp [inWrites])) x
      (Region.sub_prefix (base := s.sp - BitVec.ofNat 64 stackUse) (by decide) x hy) (hsub x hx)

theorem tail_word (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m') {d : Nat}
    (hd₁ : 32 ≤ d) (hd₂ : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d := by
  have hc : (stateTail p).Contains (off p.stp d) 8 := by
    rw [show off p.stp d = p.stp + BitVec.ofNat 64 32 + BitVec.ofNat 64 (d - 32) by
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  exact hf.readW hc h.tail_disjoint (by decide)

theorem tail_bytes (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m') :
    Spec.Rsa.bytesAt m' (p.stp + 48) 8 = Spec.Rsa.bytesAt m (p.stp + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hsub : Region.Sub ⟨p.stp + 48, 8⟩ (stateTail p) := by
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 32 + BitVec.ofNat 64 16 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl]
    exact Offset.sub_base _ (by decide)
  exact hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => (h.tail_disjoint r hr).sub_left hsub)
    (by show 8 ≤ 2 ^ 64; decide) hi

end GenInput

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (GenInput.callChanges s) m m') :
    Frame (GenInput.changes s) m m' := hf.sub (GenInput.callChanges_sub s)

/-! ## The loop states -/

/-- A state of the controller in the frame saving `ra`: `used`
octets consumed, the progress `st` in the state. The entry state is
functional-proof data only: its callee-saved registers may hold secrets, and
its tape and key buffer are secret. -/
structure GenFrame (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop where
  input : GenInput p original
  used_le : used ≤ p.randLen
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  sp : s.sp = p.F - 16
  s0 : s.gpr .s0 = p.F
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  syms : s.syms = original.syms
  savedS0 : word s.mem p.F 72 = original.gpr .s0
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = genRand original
  tab : Frame (GenInput.changes original) original.mem s.mem
  headers : Slots s.mem p.F (p.headers used)
  state : StateOk p st s.mem

/-- A state of the loop: the frame's, and the key's buffer for the progress. -/
structure GenLive (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop
    extends GenFrame p original used st s where
  key : KeyOk p st s.mem

/-- The key search from octet `used` of the tape, from the progress `st`. -/
abbrev tailOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : KeySearchResult :=
  keySearch p.L p.eB st ((genRand original).drop used)

/-- A loop state, whose key search from there finishes as `final`. -/
def GenIter (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (s : State) : Prop :=
  GenLive p original used st s ∧ ∃ tr, final = (tailOf p original used st).consume used tr

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through a step that keeps `s0`, the stack pointer, the regions and the
callee-saved registers, and writes only what a step may, with the state's
first three words for the progress `st'`, whose phase and generations are
`st`'s. -/
theorem restore (h : GenFrame p original used st s) {st' : KeyProgress}
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (GenInput.callChanges original) s.mem t.mem)
    (h0 : word t.mem p.stp 0 = BitVec.ofNat 64 st'.remaining)
    (h1 : word t.mem p.stp 8 = BitVec.ofNat 64 p.L)
    (h2 : word t.mem p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L))
    (hph : st'.phase = st.phase ∨ phaseWord st'.phase = phaseWord st.phase) (hl : st'.left = st.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) :
    GenFrame p original used st' t := by
  have hc := h.input.frame_words hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .s0 (by decide)).trans h.s0, fun r hr hn => (hg r hr).trans (h.saved r hr hn), hy.trans h.syms,
    ?_, ?_, h.tab.trans hf', ?_, ⟨h0, h1, h2, ?_, ?_, ?_, hrem, by rw [hl]; exact h.state.left_lt⟩⟩
  · exact (hc 9 (by decide)).trans h.savedS0
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (GenPublic.headers_bound _ _ e he)).trans (h.headers e he)
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.phase]
    rcases hph with hph | hph <;> rw [hph]
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.left, hl]
  · rw [h.input.tail_bytes hf, h.state.e]

end GenFrame

end VG.Proof.RsaKeyGen.RISCV64.Generate

/-! ## The controller's entry (RISC-V)

In the frame the controller allocates, the caller's `s0` is saved in word 9
and the arguments stored (`entryHead_ok`); then the state's width and
exponent are read and the rest of the words stored (`entryWords_ok`); then,
in the frame saving `ra`, the controller is at the tape's start with the
progress in the state (`gen_start`), as the prime search's entry
(`Proof/RsaKeyGen/RISCV64/Search/Entry.lean`).
-/


namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)
open VG.Proof.RsaKeyGen.RISCV64.Search (KeepS WP.keep')

/-! ## Whether the exponent is 3 -/

/-- The exponent's eight octets, most significant first, read as a word, are
`3 · 2^56` exactly when the exponent is 3. -/
theorem word_eq_three (m : Mem) (a : Addr) :
    m.readW a 64 = 0x0300000000000000 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a 8) = 3 := by
  have hb : ∀ j < 8, (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
    intro j hj
    rw [← Mem.extractLsb'_read m a (n := 8) hj]
    rfl
  have hc : ∀ j < 8, (0x0300000000000000 : BitVec 64).extractLsb' (8 * j) 8 = if j = 7 then 3 else 0 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      h | h | h | h | h | h | h | h <;> subst h <;> decide
  rw [show Spec.Rsa.bytesAt m a 8 = Spec.Rsa.bytesAt m a 7 ++ [m (a + BitVec.ofNat 64 7)] from
    SearchInit.bytesAt_succ m a 7, SearchInit.os2ip_eq_three, SearchInit.or_eq_zero,
    SearchInit.orOf_eq_zero]
  have hx : (m (a + BitVec.ofNat 64 7)).setWidth 64 ^^^ 3 = 0 ↔ m (a + BitVec.ofNat 64 7) = 3 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
      rw [BitVec.toNat_setWidth, show (3 : BitVec 64).toNat = 3 from rfl] at this
      apply BitVec.eq_of_toNat_eq
      have hl := (m (a + BitVec.ofNat 64 7)).isLt
      rw [show (3 : BitVec 8).toNat = 3 from rfl]
      omega
    · intro h; rw [h]; decide
  rw [hx]
  constructor
  · intro h
    refine ⟨fun b hm => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      have hj := List.mem_range.mp hj
      have := (hb j (by omega)).symm.trans ((congrArg (fun x : BitVec 64 => x.extractLsb' (8 * j) 8) h).trans
        (hc j (by omega)))
      rw [ite_eq_right (by omega)] at this
      exact this
    · have := (hb 7 (by decide)).symm.trans ((congrArg (fun x : BitVec 64 => x.extractLsb' (8 * 7) 8) h).trans
        (hc 7 (by decide)))
      exact this
  · rintro ⟨h0, h7⟩
    apply Proof.Bignum.ByteDigits.eq_of_bytes
    intro j hj
    rw [hb j hj, hc j hj]
    by_cases h : j = 7
    · subst h; rw [ite_eq_left rfl]; exact h7
    · rw [ite_eq_right h]
      exact h0 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)

/-- 1 exactly when `x` is zero (`sltu x, 1`). -/
theorem zero_bit (x : BitVec 64) :
    (if x < 1#64 then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : ¬ x < 1#64 := by
      intro hl
      apply h
      rw [BitVec.lt_def] at hl
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      exact BitVec.eq_of_toNat_eq (by show x.toNat = 0; omega)
    simp only [this, h, ↓reduceIte]; rfl

/-- The counted candidates of a prime's search, from the primes' octets `w`
and the exponent's word `ew`, as the entry computes them. -/
def limitBV (w ew : BitVec 64) : BitVec 64 :=
  w <<< 3 + w <<< 5 + (w <<< 4 + w <<< 3) * (if ew ^^^ 3#64 <<< 56 < 1#64 then 1 else 0)

theorem limitBV_eq {L : Nat} {ew : BitVec 64} {eB : List Byte} (hL : L ≤ 512)
    (he : ew = 0x0300000000000000 ↔ Spec.Rsa.os2ip eB = 3) :
    limitBV (BitVec.ofNat 64 L) ew = BitVec.ofNat 64 (limitOf L eB) := by
  unfold limitBV limitOf primeLimit
  rw [zero_bit, SearchInit.shl_ofNat _ 3 (by omega), SearchInit.shl_ofNat _ 4 (by omega),
    SearchInit.shl_ofNat _ 5 (by omega), SearchInit.add_ofNat, SearchInit.add_ofNat, ← BitVec.ofNat_mul,
    SearchInit.add_ofNat]
  have hz : (ew ^^^ 3#64 <<< 56 = 0) ↔ ew = 0x0300000000000000 := by
    rw [show (ew ^^^ 3#64 <<< 56 = 0) ↔ (ew ^^^ 3#64 <<< 56 = 0#64) from Iff.rfl, BitVec.xor_eq_zero_iff,
      show (3#64 : BitVec 64) <<< 56 = 0x0300000000000000 from rfl]
  by_cases h : ew = 0x0300000000000000
  · rw [ite_eq_left (hz.mpr h), ite_eq_left (he.mp h)]; congr 1; omega
  · rw [ite_eq_right (fun h' => h (hz.mp h')), ite_eq_right (fun h' => h (he.mpr h'))]; congr 1; omega

/-! ## The entry's stores -/

/-- The frame's words the first block stores. -/
def saveValues (s : State) : List (Nat × BitVec 64) :=
  [(9, s.gpr .s0), (0, s.gpr .a0), (2, s.gpr .a2), (3, s.gpr .a3), (4, s.gpr .a4), (5, s.gpr .a5),
    (6, s.gpr .a6), (7, s.gpr .a7)]

/-- The frame's words the second block stores. -/
def loadValues (s : State) : List (Nat × BitVec 64) :=
  [(1, s.mem.readW (s.gpr .a7 + 8) 64), (8, 0),
    (11, limitBV (s.mem.readW (s.gpr .a7 + 8) 64) (s.mem.readW (s.gpr .a7 + 48) 64))]

/-- The frame's words on entry, in the order the entry stores them. -/
abbrev entryValues (s : State) : List (Nat × BitVec 64) := saveValues s ++ loadValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 14 := by
  simp only [entryValues, saveValues, loadValues, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem add_ofNat_zero (x : Addr) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem alloc_wr {p : GenPublic} {s : State} (h : GenInput p s) :
    (allocd 112 s).wr = p.frame :: s.wr := by
  show _ = (⟨p.sp - _, 112⟩ : Region) :: s.wr
  rw [h.sp_eq]; rfl

theorem alloc_sp {p : GenPublic} {s : State} (h : GenInput p s) : (allocd 112 s).sp = p.F := by
  show _ = p.sp - _
  rw [h.sp_eq]; rfl

theorem writeFrame_frame_size (m : Mem) (B : Addr) (values : List (Nat × BitVec 64)) {size : Nat}
    (hsize : size ≤ 2 ^ 64) (hvalues : ∀ e ∈ values, 8 * e.1 + 8 ≤ size) :
    Frame [⟨B, size⟩] m (writeFrame m B values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    have hstore : Frame [⟨B, size⟩] m (m.writeW (off B (8 * e.1)) e.2) :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ he (by omega))
    exact hstore.trans (ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)))

/-- The frame's words: below the stack pointer. -/
theorem entry_frame {p : GenPublic} {s : State} (h : GenInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 14) :
    Frame [below s.sp stackUse] s.mem (writeFrame s.mem p.F values) := by
  refine (writeFrame_frame_size _ p.F values (size := 112) (by decide) (by
    intro e he; have := hb e he; omega)).sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, h.frame_sub⟩

/-- The registers the first block writes. -/
abbrev saveRegs : List Reg := [.t1, .s0]

theorem entryHead_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block entryHead) (allocd 112 s) fun t =>
      (t.gpr .s0 = p.F ∧ t.mem = writeFrame s.mem p.F (saveValues s)) ∧
      KeepS saveRegs (allocd 112 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have ea : ∀ t : State, exec (.addSp .t1 0) t = some (t.write .t1 (t.sp + BitVec.ofNat 64 0)) := by
    intro t; simp [exec]
  have hsp := alloc_sp h
  have hz : p.F + BitVec.ofNat 64 0 = p.F := BitVec.add_zero _
  have hs0 : InRegions (allocd 112 s).wr p.F 8 := by
    have := scr.st (d := 0) (n := 8) (by decide); simpa only [off, hz] using this
  have hl0 : p.F.toNat % 8 = 0 := by
    have := scr.al8 (d := 0) (by decide) (by decide); simpa only [off, hz] using this
  have hmem : (allocd 112 s).mem = s.mem := rfl
  have hg : ∀ r, (allocd 112 s).gpr r = s.gpr r := fun _ => rfl
  refine WP.keep' saveRegs ?_ (by decide +kernel)
  unfold entryHead writeFrame saveValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [stf, ea, hsp, hz, hs0, hl0, hmem, hg,
    scr.st (d := 16) (n := 8) (by decide), scr.al8 (d := 16) (by decide) (by decide),
    scr.st (d := 24) (n := 8) (by decide), scr.al8 (d := 24) (by decide) (by decide),
    scr.st (d := 32) (n := 8) (by decide), scr.al8 (d := 32) (by decide) (by decide),
    scr.st (d := 40) (n := 8) (by decide), scr.al8 (d := 40) (by decide) (by decide),
    scr.st (d := 48) (n := 8) (by decide), scr.al8 (d := 48) (by decide) (by decide),
    scr.st (d := 56) (n := 8) (by decide), scr.al8 (d := 56) (by decide) (by decide),
    scr.st (d := 72) (n := 8) (by decide), scr.al8 (d := 72) (by decide) (by decide), off]

/-- The registers the second block writes. -/
abbrev wordRegs : List Reg := [.t0, .a1, .a2, .a3, .a4, .a5, .a6]

theorem entryWords_ok {p : GenPublic} {s u : State} (h : GenInput p s)
    (hs0 : u.gpr .s0 = p.F) (hm : u.mem = writeFrame s.mem p.F (saveValues s))
    (ku : KeepS saveRegs (allocd 112 s) u) :
    WP isa (.block entryWords) u fun t =>
      t.mem = writeFrame u.mem p.F (loadValues s) ∧ KeepS wordRegs u t := by
  have hw : u.wr = p.frame :: s.wr := ku.wr.trans (alloc_wr h)
  have scr := h.frame_scr hw
  have hrd : u.rd ++ u.wr = s.rd ++ (p.frame :: s.wr) := by rw [ku.rd, hw]; rfl
  have hfr := entry_frame h (saveValues s) (by
    simp only [saveValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  rw [← hm] at hfr
  have hnS := h.nowrap (r := inState s) (by simp [inWrites])
  simp only [inState] at hnS
  have hst (d : Nat) (hd : d + 8 ≤ 56) : (inState s).Contains (s.gpr .a7 + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ hd (by omega)
  have hsi (d : Nat) (hd : d + 8 ≤ 56) : InRegions (u.rd ++ u.wr) (s.gpr .a7 + BitVec.ofNat 64 d) 8 := by
    rw [hrd]
    refine ⟨inState s, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), hst d hd⟩
    rw [h.wr_eq]; simp [inWrites]
  have hsa (d : Nat) (hd : d + 8 ≤ 56) (h8 : d % 8 = 0) : (s.gpr .a7 + BitVec.ofNat 64 d).toNat % 8 = 0 := by
    have := h.state_al
    have e : (s.gpr .a7 + BitVec.ofNat 64 d).toNat = (s.gpr .a7).toNat + d := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e]; omega
  have hv (d : Nat) (hd : d + 8 ≤ 56) :
      u.mem.readW (s.gpr .a7 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 d) 64 :=
    hfr.readW (r := inState s) (hst d hd) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (h.stack_disjoint (List.mem_append_left _ (by simp [inWrites]))).symm) (by decide)
  have h7 : u.gpr .a7 = s.gpr .a7 := ku.gpr .a7 (by decide)
  have a8 := hsi 8 (by decide)
  have a48 := hsi 48 (by decide)
  have l8 := hsa 8 (by decide) (by decide)
  have l48 := hsa 48 (by decide) (by decide)
  have v8 := hv 8 (by decide)
  have v48 := hv 48 (by decide)
  refine WP.keep' wordRegs ?_ (by decide +kernel)
  unfold entryWords writeFrame loadValues limitBV
  simp only [List.foldl_cons, List.foldl_nil]
  brun [stf, hs0, h7, a8, a48, l8, l48, v8, v48, exec_li,
    scr.st (d := 8) (n := 8) (by decide), scr.al8 (d := 8) (by decide) (by decide),
    scr.st (d := 64) (n := 8) (by decide), scr.al8 (d := 64) (by decide) (by decide),
    scr.st (d := 88) (n := 8) (by decide), scr.al8 (d := 88) (by decide) (by decide), off]
  rfl

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

namespace GenInput

variable {p : GenPublic} {s : State}

theorem state_eq (h : GenInput p s) : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl

theorem state_below (h : GenInput p s) : (below s.sp stackUse).Disjoint ⟨p.stp, 56⟩ := by
  rw [← h.state_eq]; exact h.stack_disjoint (List.mem_append_left _ (by simp [inWrites]))

theorem state_words (h : GenInput p s) {m : Mem} (hf : Frame [below s.sp stackUse] s.mem m) (d : Nat)
    (hd : d + 8 ≤ 56) :
    m.readW (p.stp + BitVec.ofNat 64 d) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 d) 64 := by
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  rw [h.state_eq] at hn
  refine hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd (by simp only at hn; omega))
    (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  exact h.state_below.symm

theorem state_bytes (h : GenInput p s) {m : Mem} (hf : Frame [below s.sp stackUse] s.mem m) :
    Spec.Rsa.bytesAt m (p.stp + 48) 8 = Spec.Rsa.bytesAt s.mem (p.stp + 48) 8 := by
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  rw [h.state_eq] at hn
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
  obtain rfl := List.mem_singleton.mp hq
  exact (h.state_below.sub_right (Offset.sub_base _ (by simp only at hn; omega) (n := 8) (d := 48) (k := 56))).symm

end GenInput

/-- The state's words for the progress on entry. -/
theorem stateOk_entry {p : GenPublic} {s : State} (h : GenInput p s) {m : Mem}
    (hf : Frame [below s.sp stackUse] s.mem m) : StateOk p (genProgress s) m := by
  have hw (d : Nat) (hd : d + 8 ≤ 56) := h.state_words hf d hd
  obtain ⟨-, -, -, -, -, -, -, -, hL, -, -, hrem, hcap, hph, -⟩ := h.base
  have hstp : p.stp = s.gpr .a7 := by rw [← h.2]; rfl
  have hLp : p.L = genLen s := by rw [← h.2]; rfl
  have heB : p.eB = genE s := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, BitVec.isLt _⟩
  · change m.readW (p.stp + BitVec.ofNat 64 0) 64 = _
    rw [hw 0 (by decide), BitVec.add_zero, hstp]; exact (ofNat_toNat64 _).symm
  · change m.readW (p.stp + BitVec.ofNat 64 8) 64 = _
    rw [hw 8 (by decide), hLp, hstp, ofNat_toNat64]; rfl
  · change m.readW (p.stp + BitVec.ofNat 64 16) 64 = _
    rw [hw 16 (by decide), hLp, hstp]; exact hcap
  · change m.readW (p.stp + BitVec.ofNat 64 32) 64 = _
    rw [hw 32 (by decide), hstp]
    simp only [genProgress, keyProgressAt]
    have hph' : (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 32) 64).toNat ≤ 1 := hph
    split
    · rename_i h0
      have h0' : (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      rw [h0']; rfl
    · rename_i h0
      have h0' : ¬(s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      have : (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 32) 64).toNat = 1 := by omega
      rw [this]; rfl
  · change m.readW (p.stp + BitVec.ofNat 64 40) 64 = _
    rw [hw 40 (by decide), hstp]; exact (ofNat_toNat64 _).symm
  · rw [h.state_bytes hf, heB, hstp]
  · rw [hLp, heB]
    exact hrem

theorem F_16_8 (p : GenPublic) : p.F - 16 + 8 = p.sp - BitVec.ofNat 64 120 := by
  rw [GenPublic.F, BitVec.sub_sub, Offset.sub_ofNat_eq p.sp (show 120 ≤ 128 by decide)]; rfl

/-- The push of `ra` writes only below the controller's frame. -/
theorem push_frame {p : GenPublic} {s : State} (h : GenInput p s) (m : Mem) (v : BitVec 64) :
    Frame (GenInput.callChanges s) m (m.write (p.F - 16 + 8) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 544⟩)
    (by simp [GenInput.callChanges]) _ ?_
  rw [F_16_8, h.sp_eq]
  exact Offset.contains_below s.sp (a := 120) (b := 656) (by decide) (by decide) (by decide)

/-- The push's region is below the stack pointer too. -/
theorem push_below {p : GenPublic} {s : State} (h : GenInput p s) (m : Mem) (v : BitVec 64) :
    Frame [below s.sp stackUse] m (m.write (p.F - 16 + 8) 8 v) := by
  refine Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
  rw [F_16_8, h.sp_eq]
  exact Offset.contains_below s.sp (a := 120) (b := stackUse) (by decide) (by decide) (by decide)

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := saveRegs ++ wordRegs

/-- The controller's state on leaving its entry, in the frame saving `ra`,
before it clears the key's buffer: everything it wrote is below the stack
pointer. -/
theorem gen_start {p : GenPublic} {s t : State} (h : GenInput p s)
    (hx : t.gpr .s0 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : KeepS entryRegs (allocd 112 s) t) (hy : t.syms = s.syms) :
    GenFrame p s 0 (genProgress s) (framed .ra t) ∧ Frame [below s.sp stackUse] s.mem (framed .ra t).mem := by
  have hb := entryValues_bound s
  have hfb₁ : Frame [below s.sp stackUse] s.mem t.mem := by rw [hm]; exact entry_frame h _ hb
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hp := push_frame h t.mem (t.gpr .ra)
  rw [← htsp] at hp
  have hpb := push_below h t.mem (t.gpr .ra)
  rw [← htsp] at hpb
  have hfb : Frame [below s.sp stackUse] s.mem (framed .ra t).mem := hfb₁.trans hpb
  have hf₂ : Frame (GenInput.changes s) s.mem (framed .ra t).mem :=
    hfb.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [GenInput.changes], fun _ hi => hi⟩
  have hc (j : Nat) (hj : j < 14) : word (framed .ra t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 14) : word (framed .ra t).mem p.F (8 * j) =
      frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ (fun e he => by have := hb e he; omega) j (by omega)
  have hL : p.L ≤ 512 := by rw [← h.2]; exact h.base.2.2.2.2.2.2.2.2.1.2.1
  refine ⟨⟨h, Nat.zero_le _, k.rd, k.wr.trans (alloc_wr h), ?_, hx, ?_, hy, ?_, ?_, hf₂, ?_,
    stateOk_entry h hfb⟩, hfb⟩
  · show t.sp - 16 = p.F - 16
    rw [htsp]
  · intro r hr h0
    exact k.gpr r (by revert r hr h0; decide)
  · rw [show (72 : Nat) = 8 * 9 from rfl, hw 9 (by decide)]
    rfl
  · rw [h.random_frame hf₂]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (GenPublic.headers_bound _ _ e he)]
    have hLs : genLen s = p.L := by rw [← h.2]; rfl
    have hlim : limitBV (s.mem.readW (s.gpr .a7 + 8) 64) (s.mem.readW (s.gpr .a7 + 48) 64) =
        BitVec.ofNat 64 (limitOf p.L p.eB) := by
      rw [show s.mem.readW (s.gpr .a7 + 8) 64 = BitVec.ofNat 64 p.L by rw [← hLs]; exact (ofNat_toNat64 _).symm]
      exact limitBV_eq hL (by rw [word_eq_three]; rw [← h.2]; rfl)
    rw [← h.2] at he hlim
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [frameValue, entryValues, saveValues, loadValues, List.cons_append, List.nil_append,
        List.foldl_cons, List.foldl_nil, genOfState, genLen, ofNat_toNat64, hlim,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.RISCV64.Generate

/-! # Zeros in the key's buffer (RISC-V)

`clear` writes zeros to the region in frame words 12 and 13, which is in the
key's buffer, with the prime search's loop of `sb` (`zeroLoop_ok`): the
frame, the state and everything else is kept. `clearAround` clears the
key's buffer but `p`'s slot, `clearAll` all of it.
-/

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Generate
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.RISCV64.Search (zeroLoop_ok WP.keepS KeepS)

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

theorem key_region (h : GenFrame p original used st s) : inKey original = ⟨p.kp, 9 * p.L⟩ := by
  have : (original.gpr .a1).toNat = 9 * genLen original := h.input.base.2.2.2.2.2.2.2.2.2.1
  rw [← h.input.2]
  simp only [inKey, genOfState, this]

theorem key_state (h : GenFrame p original used st s) : (inKey original).Disjoint (inState original) := by
  have hpw := h.input.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.1.2.2

/-- Through a step that changes only the key's buffer. -/
theorem restoreKey (h : GenFrame p original used st s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame [inKey original] s.mem t.mem) : GenFrame p original used st t := by
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  have hd := h.key_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d :=
    hf.readW (r := inState original) (by rw [hst]; exact Offset.contains_base _ hd' (by
        have := h.input.nowrap (r := inState original) (by simp [inWrites]); rw [hst] at this; simp only at this
        omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine h.restore hr hw hsp hy hg (hf.sub fun r hr => ?_) ?_ ?_ ?_ (.inl rfl) rfl h.state.remaining_le
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩
  · rw [hword 0 (by decide)]; exact h.state.remaining
  · rw [hword 8 (by decide)]; exact h.state.len
  · rw [hword 16 (by decide)]; exact h.state.cap

theorem frame_st (h : GenFrame p original used st s) :
    ∀ d, d + 8 ≤ 112 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 :=
  fun _ hd => (h.input.frame_scr h.wr).st hd

theorem frame_al (h : GenFrame p original used st s) {d : Nat} (hd : d + 8 ≤ 112) (h8 : d % 8 = 0) :
    (p.F + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  (h.input.frame_scr h.wr).al8 hd h8

theorem frame_ld (h : GenFrame p original used st s) :
    ∀ d, d + 8 ≤ 112 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 :=
  fun d hd => let ⟨r, hr, hc⟩ := h.frame_st d hd; ⟨r, List.mem_append_right _ hr, hc⟩

theorem key_nowrap (h : GenFrame p original used st s) : p.kp.toNat + 9 * p.L ≤ 2 ^ 64 := by
  have := h.input.nowrap (r := inKey original) (by simp [inWrites])
  rw [h.key_region] at this
  exact this

theorem len_valid (h : GenFrame p original used st s) : primeLenValid p.L := by
  rw [← h.input.2]; exact h.input.base.2.2.2.2.2.2.2.2.1

theorem frame_key (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.kp, 9 * p.L⟩ := by
  rw [← h.key_region]; exact h.input.frame_disjoint_writes (by simp [inWrites])

end GenFrame

/-- `clear`: zeros at the region in frame words 12 and 13. -/
theorem clear_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {op : Addr} {len : Nat}
    (h12 : word s.mem p.F (8 * 12) = op) (h13 : word s.mem p.F (8 * 13) = BitVec.ofNat 64 len)
    (hsub : Region.Sub ⟨op, len⟩ (inKey original)) (_hn : op.toNat + len ≤ 2 ^ 64) (h1 : 1 ≤ len)
    (hlt : len < 2 ^ 31) :
    WP isa clear s fun t => GenFrame p original used st t ∧ (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      Frame [⟨op, len⟩] s.mem t.mem ∧ (∀ j < 14, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) ∧
      KeepS [.a1, .a2, .a3] s t := by
  have hin : inKey original ∈ s.wr := by
    rw [h.wr, h.input.wr_eq]; exact List.mem_cons_of_mem _ (by simp [inWrites])
  have hout : ∀ i < len, InRegions s.wr (off op i) 1 := fun i hi =>
    ⟨inKey original, hin, hsub _ (Offset.contains_base _ (by omega) (by omega))⟩
  have hl12 := h.frame_ld 96 (by decide)
  have hl13 := h.frame_ld 104 (by decide)
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13
  unfold clear
  refine WP.seq (WP.mono (WP.keepS [.a1, .a2, .a3] (Q := fun t => t.gpr .a1 = op ∧
      t.gpr .a2 = BitVec.ofNat 64 len ∧ t.gpr .a3 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.s0, hl12, hl13, h.frame_al (d := 96) (by decide) (by decide),
      h.frame_al (d := 104) (by decide) (by decide), h12, h13, exec_li]; try rfl) (by decide +kernel))
    fun s₁ ⟨⟨⟨h3, h4, h5, hm₁⟩, k₁⟩, hy₁⟩ => ?_)
  refine VG.RISCV64.WP.mono_syms (zeroLoop_ok (fun i hi => by rw [k₁.wr]; exact hout i hi) h1
    (by omega) h3 h4 h5) fun t ⟨⟨tb, tout⟩, kt⟩ hyt => ?_
  have hfx : ∀ x, (∀ i < len, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x := by
    intro x hx
    rw [tout x (Or.inr ?_), hm₁]
    by_contra hc
    exact hx (x - op).toNat (by simp only [ofs] at hc; omega)
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
  have hframe : Frame [⟨op, len⟩] s.mem t.mem := by
    intro a ha
    apply hfx
    intro i hi he
    apply ha _ (List.mem_singleton_self _)
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)
  have hkey : Frame [inKey original] s.mem t.mem := hframe.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨inKey original, List.mem_singleton_self _, hsub⟩
  have kk := k₁.trans kt
  refine ⟨h.restoreKey kk.rd kk.wr kk.sp (hyt.trans hy₁) (fun r hr => kk.gpr r (by revert r hr; decide)) hkey,
    fun i hi => by rw [← off]; exact tb i hi, hframe,
    fun j hj => h.input.frame_words (hkey.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩) j hj, kk.mono (by decide)⟩

/-! ## Stores to the frame -/

theorem writeFrame_frame14 (m : Mem) (F : Addr) (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 14) :
    Frame [⟨F, 112⟩] m (writeFrame m F values) :=
  writeFrame_frame_size m F values (by decide) (fun e he => by have := hb e he; omega)

namespace GenInput

variable {p : GenPublic} {s : State}

theorem frame_state (h : GenInput p s) : p.frame.Disjoint ⟨p.stp, 56⟩ := by
  rw [← h.state_eq]; exact h.frame_disjoint_writes (by simp [inWrites])

/-- The state through stores to the frame. -/
theorem stateOk_frame (h : GenInput p s) {m m' : Mem} (hf : Frame [p.frame] m m') {st : KeyProgress}
    (hs : StateOk p st m) : StateOk p st m' := by
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  rw [h.state_eq] at hn
  have hd := h.frame_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d :=
    hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd' (by simp only at hn; omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs.remaining_le, hs.left_lt⟩
  · rw [hword 0 (by decide)]; exact hs.remaining
  · rw [hword 8 (by decide)]; exact hs.len
  · rw [hword 16 (by decide)]; exact hs.cap
  · rw [hword 32 (by decide)]; exact hs.phase
  · rw [hword 40 (by decide)]; exact hs.left
  · rw [← hs.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    refine hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
    obtain rfl := List.mem_singleton.mp hq
    refine (hd.sub_right ?_).symm
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]
    exact Offset.sub_base _ (by simp only at hn; omega)

end GenInput

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through stores to the frame but its saved `s0`, with the words for the
octets consumed `u`. -/
theorem store (h : GenFrame p original used st s) {u : Nat} (hu : u ≤ p.randLen)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 14) (h9 : ∀ e ∈ values, 9 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ reg ∈ preserved, t.gpr reg = s.gpr reg)
    (hh : Slots t.mem p.F (p.headers u)) : GenFrame p original u st t := by
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame14 s.mem p.F values hb
  have hf : Frame (GenInput.changes original) s.mem t.mem := by
    apply hfr.sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩
  refine ⟨h.input, hu, hread.trans h.rd, hwrite.trans h.wr, hsp.trans h.sp,
    (hg .s0 (by decide)).trans h.s0, fun reg hreg hne => (hg reg hreg).trans (h.saved reg hreg hne),
    hy.trans h.syms, ?_, ?_, h.tab.trans hf, hh, h.input.stateOk_frame hfr h.state⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 9) = _
    rw [writeFrame_word _ _ _ (fun e he => by have := hb e he; omega) 9 (by decide),
      frameValue_unchanged _ _ _ h9]
    exact h.savedS0
  · exact (h.input.random_frame hf).trans h.random

/-- The words of the frame's headers, kept through stores of others. -/
theorem slots_kept (h : GenFrame p original used st s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 14) (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F values) p.F (p.headers used) := by
  intro e he
  have hj := GenPublic.headers_bound _ _ e he
  rw [writeFrame_word _ _ _ (fun e he => by have := hb e he; omega) e.1 (by omega),
    frameValue_unchanged _ _ _ ?_]
  · exact h.headers e he
  · intro x hx heq
    have := hnot x hx
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- A loop state's frame words, read. -/
theorem slot (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used) : word s.mem p.F (8 * j) = v := h.headers (j, v) hj

end GenFrame

/-! ## The key's buffer but `p` -/

theorem bytes_zero {m : Mem} {op : Addr} {len : Nat} (h : ∀ i < len, m (op + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m op len = List.replicate len 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)

theorem bytes_kept {m m' : Mem} {R : Region} {a : Addr} {n : Nat} (hf : Frame [R] m m')
    (hd : R.Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨a, n⟩) (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) hn
    (List.mem_range.mp hi)

theorem slot_disjoint (kp : Addr) {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2 ^ 64)
    (he : e + k ≤ 2 ^ 64) : Region.Disjoint ⟨kp + BitVec.ofNat 64 d, n⟩ ⟨kp + BitVec.ofNat 64 e, k⟩ :=
  fun x hx hy => Offset.sep kp h hd he x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

theorem slot_sub (kp : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Region.Sub ⟨kp + BitVec.ofNat 64 d, n⟩ ⟨kp, k⟩ := Offset.sub_base kp h

theorem kp_zero (kp : Addr) : kp = kp + BitVec.ofNat 64 0 := (BitVec.add_zero kp).symm

/-- A read below a store of the frame sees what was there. -/
theorem read_below_store (m : Mem) (B : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep B (d := d) (n := 8) (e := e) (k := 8) (Or.inl h) (by omega) he)
    (by decide)

theorem read_below_store0 (m : Mem) (B : Addr) (v : BitVec 64) {e : Nat} (h : 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW B 64 = m.readW B 64 := by
  have := read_below_store m B v (d := 0) h he
  rwa [BitVec.add_zero] at this

theorem setLow_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [ldf .a0 0, stf .a0 12, ldf .a1 1, .shift .sll .d .a1 .a1 2, stf .a1 13]) s fun t =>
      (t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 2)] ∧ KeepS [.a0, .a1] s t) ∧
        t.syms = s.syms := by
  have hl := h.frame_ld
  have hs := h.frame_st
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hal0 : p.F.toNat % 8 = 0 := by simpa only [BitVec.add_zero] using h.frame_al (d := 0) (by decide) (by decide)
  have h0 := h.slot (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have h1 := h.slot (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keepS [.a0, .a1] ?_ (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hl0, hal0, h.frame_al (d := 0) (by decide) (by decide), h.frame_al (d := 8) (by decide) (by decide),
    h.frame_al (d := 96) (by decide) (by decide), h.frame_al (d := 104) (by decide) (by decide), hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide),
    off, BitVec.add_zero]

theorem setHigh_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [ldf .a1 1, .shift .sll .d .a2 .a1 2, .add .a1 .a1 .a2, ldf .a0 0, .add .a0 .a0 .a1, stf .a0 12,
      ldf .a1 1, .shift .sll .d .a1 .a1 2, stf .a1 13]) s fun t =>
      (t.mem = writeFrame s.mem p.F [(12, p.kp + (BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2)),
        (13, BitVec.ofNat 64 p.L <<< 2)] ∧ KeepS [.a0, .a1, .a2] s t) ∧ t.syms = s.syms := by
  have hl := h.frame_ld
  have hs := h.frame_st
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hal0 : p.F.toNat % 8 = 0 := by simpa only [BitVec.add_zero] using h.frame_al (d := 0) (by decide) (by decide)
  have h0 := h.slot (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have h1 := h.slot (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keepS [.a0, .a1, .a2] ?_ (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hl0, hal0, h.frame_al (d := 0) (by decide) (by decide), h.frame_al (d := 8) (by decide) (by decide),
    h.frame_al (d := 96) (by decide) (by decide), h.frame_al (d := 104) (by decide) (by decide), hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    h0, h1, hs 96 (by decide), hs 104 (by decide), off, BitVec.add_zero]

theorem setAll_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [ldf .a0 0, stf .a0 12, ldf .a1 1, .shift .sll .d .a2 .a1 3, .add .a2 .a2 .a1, stf .a2 13]) s fun t =>
      (t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L)] ∧
        KeepS [.a0, .a1, .a2] s t) ∧ t.syms = s.syms := by
  have hl := h.frame_ld
  have hs := h.frame_st
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hal0 : p.F.toNat % 8 = 0 := by simpa only [BitVec.add_zero] using h.frame_al (d := 0) (by decide) (by decide)
  have h0 := h.slot (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have h1 := h.slot (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keepS [.a0, .a1, .a2] ?_ (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hl0, hal0, h.frame_al (d := 0) (by decide) (by decide), h.frame_al (d := 8) (by decide) (by decide),
    h.frame_al (d := 96) (by decide) (by decide), h.frame_al (d := 104) (by decide) (by decide), hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    h0, h1, hs 96 (by decide), hs 104 (by decide), off, BitVec.add_zero]

theorem store_region {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {a b : BitVec 64}
    (hm : t.mem = writeFrame s.mem p.F [(12, a), (13, b)]) {rs : List Reg} (k : KeepS rs s t)
    (hy : t.syms = s.syms) (hrs : ∀ r ∈ preserved, r ∉ rs) :
    GenFrame p original used st t ∧ word t.mem p.F (8 * 12) = a ∧ word t.mem p.F (8 * 13) = b ∧
      Frame [p.frame] s.mem t.mem := by
  have hb : ∀ e ∈ [(12, a), (13, b)], e.1 < 14 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.store h.used_le _ hb (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide)
    hm k.rd k.wr k.sp hy (fun r hr => k.gpr r (hrs r hr)) (by
      rw [hm]; exact h.slots_kept _ hb (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide)), ?_, ?_, ?_⟩
  · rw [hm, writeFrame_word _ _ _ (fun e he => by have := hb e he; omega) 12 (by decide)]; rfl
  · rw [hm, writeFrame_word _ _ _ (fun e he => by have := hb e he; omega) 13 (by decide)]; rfl
  · rw [hm]; exact writeFrame_frame14 s.mem p.F _ hb

/-- `clearAround`: zeros at the key's buffer but `p`'s slot. -/
theorem clearAround_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s)
    (hp : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    WP isa clearAround s fun t => GenLive p original used st t ∧
      Frame [⟨p.kp, 9 * p.L⟩, p.frame] s.mem t.mem := by
  have hn := h.key_nowrap
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have hkr := h.key_region
  have hfk := h.frame_key
  have h4 : BitVec.ofNat 64 p.L <<< 2 = BitVec.ofNat 64 (4 * p.L) := by
    rw [VG.Proof.RsaKeyGen.SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h5 : p.kp + (BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2) = p.slot 5 := by
    rw [h4, VG.Proof.RsaKeyGen.SearchInit.add_ofNat]; congr 2; omega
  unfold clearAround
  simp only [seqs]
  refine WP.seq (VG.RISCV64.WP.mono_syms (setLow_ok h) fun t1 ⟨⟨hm1, k1⟩, hy1⟩ _ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 hy1 (by decide)
  rw [h4] at w13
  refine WP.seq (WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega))
    (by omega) (by omega) (by omega)) fun t2 ⟨g2, z2, f2, _, _⟩ => ?_)
  refine WP.seq (VG.RISCV64.WP.mono_syms (setHigh_ok g2) fun t3 ⟨⟨hm3, k3⟩, hy3⟩ _ => ?_)
  obtain ⟨g3, w12', w13', f3⟩ := store_region g2 hm3 k3 hy3 (by decide)
  rw [h4] at w13'
  rw [h5] at w12'
  refine WP.mono (clear_ok g3 w12' w13' (by rw [hkr]; exact slot_sub _ (by omega)) (by
      have : (p.slot 5).toNat = p.kp.toNat + 5 * p.L := by
        rw [GenPublic.slot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      omega) (by omega) (by omega)) fun t4 ⟨g4, z4, f4, _, _⟩ => ?_
  have hd0 : Region.Disjoint ⟨p.slot 5, 4 * p.L⟩ ⟨p.kp, 4 * p.L⟩ := by
    have := slot_disjoint p.kp (d := 5 * p.L) (n := 4 * p.L) (e := 0) (k := 4 * p.L) (.inr (by omega))
      (by omega) (by omega)
    rwa [← kp_zero] at this
  have hfs : p.frame.Disjoint ⟨p.slot 4, p.L⟩ := hfk.sub_right (slot_sub _ (by omega))
  have hf0 : p.frame.Disjoint ⟨p.kp, 4 * p.L⟩ := hfk.sub_right (Region.sub_prefix (by omega))
  have hfr : Frame [⟨p.kp, 9 * p.L⟩, p.frame] s.mem t4.mem := by
    have e1 : ∀ r ∈ [p.frame], ∃ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), p.frame], Region.Sub r q := fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩
    have e2 : ∀ {op : Addr} {n : Nat}, Region.Sub ⟨op, n⟩ ⟨p.kp, 9 * p.L⟩ →
        ∀ r ∈ [(⟨op, n⟩ : Region)], ∃ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), p.frame], Region.Sub r q := fun hs r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_cons_self .., hs⟩
    exact ((f1.sub e1).trans (f2.sub (e2 (Region.sub_prefix (by omega))))).trans
      ((f3.sub e1).trans (f4.sub (e2 (slot_sub _ (by omega)))))
  refine ⟨⟨g4, ⟨?_, ?_, ?_⟩⟩, hfr⟩
  · rw [bytes_kept f4 hd0 (by omega), bytes_kept f3 hf0 (by omega)]
    exact bytes_zero z2
  · exact bytes_zero z4
  · intro pB hpB
    rw [bytes_kept f4 (slot_disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega),
      bytes_kept f3 hfs (by omega), bytes_kept f2 ?_ (by omega), bytes_kept f1 hfs (by omega)]
    · exact hp pB hpB
    · have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := 4 * p.L) (k := p.L) (.inl (by omega))
        (by omega) (by omega)
      rwa [← kp_zero] at this

end VG.Proof.RsaKeyGen.RISCV64.Generate

/-! # The controller's call of the prime search (RISC-V)

For the search of the progress' prime: `out` is `p`'s slot for `p`, `q`'s for
`q`; `p` is `p`'s slot, of `p_len` octets for `q` and none for `p`; `e` the
state's last word; the tape after the octets consumed. Its four stack
arguments in the call's frame of 32 bytes, at `sp - 160` for the
controller's stack pointer on entry. The search's regions are the
controller's (its output and the other prime in the key's buffer, `used`, the
working space, the state's first four words, its exponent in the state's
last, the rest of the tape), its stack arguments, and the table of trial
division; it may use the 496 bytes below its call's frame.
-/

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf primeOf)
open VG.Proof.RsaKeyGen.RISCV64.Search (WP.keepS KeepS)

/-- The search's output: `p`'s slot for `p`, `q`'s for `q`. -/
def outOf (p : GenPublic) (st : KeyProgress) : Addr := if phaseWord st.phase = 0 then p.slot 4 else p.slot 5

/-- The other prime's length: none for `p`. -/
def plenOf (p : GenPublic) (st : KeyProgress) : Nat := if phaseWord st.phase = 0 then 0 else p.L

/-- The stack pointer in the search's call frame. -/
abbrev callSp (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 160

theorem callSp_eq (p : GenPublic) : p.F - 16 - BitVec.ofNat 64 32 = callSp p := by
  rw [GenPublic.F, BitVec.sub_sub, BitVec.sub_sub]; rfl

/-- The search's stack arguments, in its frame. -/
def callValues (p : GenPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (p.randLen - used)), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8)), (3, p.stp)]

theorem callValues_bound (p : GenPublic) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 20 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The search's arguments in registers. -/
def SearchRegs (p : GenPublic) (used : Nat) (st : KeyProgress) (s : State) : Prop :=
  s.gpr .a0 = outOf p st ∧ s.gpr .a1 = BitVec.ofNat 64 p.L ∧ s.gpr .a2 = p.up ∧
    s.gpr .a3 = p.stp + BitVec.ofNat 64 48 ∧ s.gpr .a4 = BitVec.ofNat 64 8 ∧ s.gpr .a5 = p.slot 4 ∧
    s.gpr .a6 = BitVec.ofNat 64 (plenOf p st) ∧ s.gpr .a7 = p.rp + BitVec.ofNat 64 used

theorem phaseWord_le (ph : KeyPhase) : phaseWord ph ≤ 1 := by cases ph <;> simp only [phaseWord] <;> omega

/-- The registers the arguments' block writes. -/
abbrev searchArgRegs : List Reg := [.t0, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2]

theorem GenFrame.state_ld {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {t : State} (hw : t.wr = (allocd 32 s).wr) :
    ∀ d, d + 8 ≤ 56 → InRegions (t.rd ++ t.wr) (p.stp + BitVec.ofNat 64 d) 8 := by
  intro d hd
  have hn := h.input.nowrap (r := inState original) (by simp [inWrites])
  rw [h.input.state_eq] at hn
  refine ⟨inState original, List.mem_append_right _ ?_,
    by rw [h.input.state_eq]; exact Offset.contains_base _ hd (by simp only at hn; omega)⟩
  rw [hw]
  exact List.mem_cons_of_mem _ (by rw [h.wr, h.input.wr_eq]; exact List.mem_cons_of_mem _ (by simp [inWrites]))

theorem GenFrame.frame_ldA {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {t : State} {k : Nat} (hw : t.wr = (allocd k s).wr) :
    ∀ d, d + 8 ≤ 112 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  intro d hd
  obtain ⟨r, hr, hc⟩ := h.frame_st d hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

theorem callSp_F (p : GenPublic) : callSp p + BitVec.ofNat 64 48 = p.F := by
  rw [callSp, GenPublic.F, Offset.sub_ofNat_eq p.sp (show 112 ≤ 160 by decide)]

/-! ## The search's arguments -/

/-- The call's frame, its stack arguments stored. -/
abbrev callMem (p : GenPublic) (used : Nat) (s : State) : Mem :=
  writeFrame s.mem (callSp p) (callValues p used)

theorem alloc_call_sp {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : (allocd 32 s).sp = callSp p := by
  show s.sp - _ = _
  rw [h.sp, callSp_eq]

theorem alloc_call_wr {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    (allocd 32 s).wr = ⟨callSp p, 32⟩ :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ : Region) :: s.wr = _
  rw [h.sp, callSp_eq]

theorem alloc_args_frame {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    Frame (GenInput.callChanges original) s.mem (callMem p used s) := by
  have hr : (⟨original.sp - BitVec.ofNat 64 stackUse, 544⟩ : Region) ∈ GenInput.callChanges original := by
    simp [GenInput.callChanges]
  refine (writeFrame_frame_size _ _ (callValues p used) (size := 32)
    (by decide) (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub fun r hr' => ?_
  obtain rfl := List.mem_singleton.mp hr'
  refine ⟨_, hr, ?_⟩
  rw [callSp, ← h.input.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

/-- The frame's words, through what a call may write. -/
theorem GenFrame.call_word {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {m : Mem}
    (hf : Frame (GenInput.callChanges original) s.mem m) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used) : m.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v :=
  (h.input.frame_words hf j (GenPublic.headers_bound _ _ _ hj)).trans (h.headers (j, v) hj)

/-- The registers the stack arguments' block writes. -/
abbrev stackRegs : List Reg := [.a0, .a1, .a2, .a3, .t1, .t2]

theorem search_stack_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block searchStack) (allocd 32 s) fun u =>
      (u.mem = callMem p used s ∧ KeepS stackRegs (allocd 32 s) u) ∧ u.syms = (allocd 32 s).syms := by
  have hl := h.frame_ldA (t := allocd 32 s) (k := 32) rfl
  have hsp := alloc_call_sp h
  have haw := alloc_call_wr h
  have hcs : (callSp p).toNat = p.sp.toNat - 160 := by
    have := h.input.room
    have hsu : stackUse = 656 := rfl
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 160).toNat = 160 from rfl]; omega),
      show (BitVec.ofNat 64 160).toNat = 160 from rfl]
  have hw : ∀ d, d + 8 ≤ 32 → InRegions (allocd 32 s).wr (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 32⟩, by rw [haw]; exact List.mem_cons_self .., Offset.contains_base _ hd (by
      have := p.sp.isLt; have := h.input.room; have hsu : stackUse = 656 := rfl; omega)⟩
  have hwa : ∀ d, d + 8 ≤ 32 → d % 8 = 0 → (callSp p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
    intro d hd h8
    have := h.input.sp16; have := h.input.room; have hsu : stackUse = 656 := rfl
    have e : (callSp p + BitVec.ofNat 64 d).toNat = (callSp p).toNat + d := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.sp.isLt; omega
    rw [e, hcs]; omega
  have hz : callSp p + BitVec.ofNat 64 0 = callSp p := BitVec.add_zero _
  have hw0 : InRegions (allocd 32 s).wr (callSp p) 8 := by simpa only [hz] using hw 0 (by decide)
  have hwa0 : (callSp p).toNat % 8 = 0 := by simpa only [hz] using hwa 0 (by decide) (by decide)
  have hf : Frame (GenInput.callChanges original) s.mem s.mem := Frame.refl _ _
  have hv4 := h.call_word hf (j := 4) (v := BitVec.ofNat 64 p.randLen) (by simp [GenPublic.headers])
  have hv5 := h.call_word hf (j := 5) (v := p.B) (by simp [GenPublic.headers])
  have hv6 := h.call_word hf (j := 6) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := h.call_word hf (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hv8 := h.call_word hf (j := 8) (v := BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul] at hv4 hv5 hv6 hv7 hv8
  have h31 : (allocd 32 s).gpr .s0 = p.F := h.s0
  have hmem : (allocd 32 s).mem = s.mem := rfl
  have hul := h.used_le
  have hrl : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hsub : BitVec.ofNat 64 p.randLen - BitVec.ofNat 64 used = BitVec.ofNat 64 (p.randLen - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl,
      Nat.mod_eq_of_lt (by omega : used < 2 ^ 64)]
    omega
  have ea : ∀ t : State, exec (.addSp .t1 0) t = some (t.write .t1 (t.sp + BitVec.ofNat 64 0)) := by
    intro t; simp [exec]
  have hsp0 : (allocd 32 s).sp + BitVec.ofNat 64 0 = callSp p := by rw [BitVec.add_zero, hsp]
  refine WP.keepS stackRegs ?_ (by decide +kernel)
  unfold searchStack callMem writeFrame callValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, ea, hsp, hsp0, h31, hmem, hl 32 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hl 64 (by decide), h.frame_al (d := 32) (by decide) (by decide), h.frame_al (d := 40) (by decide) (by decide),
    h.frame_al (d := 48) (by decide) (by decide), h.frame_al (d := 56) (by decide) (by decide),
    h.frame_al (d := 64) (by decide) (by decide), hv4, hv5, hv6, hv7, hv8, hsub, hw0, hwa0, hw 0 (by decide),
    hwa 0 (by decide) (by decide),
    hw 8 (by decide), hw 16 (by decide), hw 24 (by decide), hwa 8 (by decide) (by decide),
    hwa 16 (by decide) (by decide), hwa 24 (by decide) (by decide), off]

theorem search_args_ok {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hm : u.mem = callMem p used s)
    (ku : KeepS stackRegs (allocd 32 s) u) :
    WP isa (.block searchArgs) u fun v =>
      ((SearchRegs p used st v ∧ v.mem = u.mem) ∧ KeepS searchArgRegs u v) ∧ v.syms = u.syms := by
  have hl := h.frame_ldA (t := u) (k := 32) ku.wr
  have hsl := h.state_ld (t := u) ku.wr
  have hf := alloc_args_frame h (used := used)
  rw [← hm] at hf
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used) :
      u.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.call_word hf hj
  have hv0 := hv 0 p.kp (by simp [GenPublic.headers])
  have hv1 := hv 1 (BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv2 := hv 2 p.up (by simp [GenPublic.headers])
  have hv3 := hv 3 p.rp (by simp [GenPublic.headers])
  have hv7 := hv 7 p.stp (by simp [GenPublic.headers])
  have hv8 := hv 8 (BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1 hv2 hv3 hv7 hv8
  have hl0 : InRegions (u.rd ++ u.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hph : u.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) := by
    have := h.input.tail_word hf (d := 32) (by decide) (by decide)
    simp only [Bignum.word, off] at this
    rw [this]; exact h.state.phase
  have h31 : u.gpr .s0 = p.F := (ku.gpr .s0 (by decide)).trans h.s0
  have hal0 : p.F.toNat % 8 = 0 := by simpa only [BitVec.add_zero] using h.frame_al (d := 0) (by decide) (by decide)
  have hsa32 : (p.stp + BitVec.ofNat 64 32).toNat % 8 = 0 := by
    have := h.input.state_al
    have hn := h.input.nowrap (r := inState original) (by simp [inWrites])
    rw [h.input.state_eq] at hn
    have hs : (original.gpr .a7) = p.stp := by rw [← h.input.2]; rfl
    rw [hs] at this
    have e : (p.stp + BitVec.ofNat 64 32).toNat = p.stp.toNat + 32 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only at hn; omega
    rw [e]; omega
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have h4 : BitVec.ofNat 64 p.L <<< 2 + p.kp = p.slot 4 := by
    rw [VG.Proof.RsaKeyGen.SearchInit.shl_ofNat _ _ (by omega), BitVec.add_comm]; congr 2; omega
  have h5 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, VG.Proof.RsaKeyGen.SearchInit.add_ofNat]; congr 2; omega
  refine WP.keepS searchArgRegs ?_ (by decide +kernel)
  unfold searchArgs SearchRegs outOf plenOf
  have hph1 := phaseWord_le st.phase
  rcases (by omega : phaseWord st.phase = 0 ∨ phaseWord st.phase = 1) with hp | hp <;>
  rw [hp] at hph <;>
  brun [ldf, h31, hl0, hal0, hl 8 (by decide), hl 16 (by decide), hl 24 (by decide), hl 56 (by decide),
    hl 64 (by decide), h.frame_al (d := 8) (by decide) (by decide), h.frame_al (d := 16) (by decide) (by decide),
    h.frame_al (d := 24) (by decide) (by decide), h.frame_al (d := 56) (by decide) (by decide),
    h.frame_al (d := 64) (by decide) (by decide), hsl 32 (by decide), hsa32, hv0, hv1, hv2, hv3, hv7, hv8, hph,
    h4, h5, hp, exec_li, BitVec.mul_zero, BitVec.mul_one, BitVec.add_zero] <;>
  first | rfl | exact ⟨rfl, rfl⟩

/-! ## The search's regions -/

abbrev rO (p : GenPublic) (st : KeyProgress) : Region := ⟨outOf p st, p.L⟩
abbrev rU (p : GenPublic) : Region := ⟨p.up, 8⟩
abbrev rE (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 48, 8⟩
abbrev rP (p : GenPublic) (st : KeyProgress) : Region := ⟨p.slot 4, plenOf p st⟩
abbrev rR (p : GenPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : GenPublic) : Region := ⟨p.B, p.Z⟩
abbrev rT (p : GenPublic) : Region := ⟨p.stp, 32⟩
abbrev rA (p : GenPublic) : Region := ⟨callSp p, 32⟩
abbrev rLow (p : GenPublic) : Region := below (callSp p) 496
abbrev rTab (p : GenPublic) : Region := ⟨p.T, 8 * 1024⟩

/-- The controller's regions. -/
abbrev cK (p : GenPublic) : Region := ⟨p.kp, 9 * p.L⟩
abbrev cS (p : GenPublic) : Region := ⟨p.stp, 56⟩
abbrev cR (p : GenPublic) : Region := ⟨p.rp, p.randLen⟩
abbrev cStack (p : GenPublic) : Region := below p.sp stackUse


/-- What the controller's precondition says of its regions. -/
structure CFacts (p : GenPublic) : Prop where
  room : stackUse ≤ p.sp.toNat
  sp16 : p.sp.toNat % 16 = 0
  aU : p.up.toNat % 8 = 0
  aS : p.B.toNat % 8 = 0
  aT : p.stp.toNat % 8 = 0
  kU : (cK p).Disjoint (rU p)
  kS : (cK p).Disjoint (rS p)
  kT : (cK p).Disjoint (cS p)
  uS : (rU p).Disjoint (rS p)
  uT : (rU p).Disjoint (cS p)
  sT : (rS p).Disjoint (cS p)
  kR : (cK p).Disjoint (cR p)
  uR : (rU p).Disjoint (cR p)
  sR : (rS p).Disjoint (cR p)
  tR : (cS p).Disjoint (cR p)
  stack : ∀ r ∈ [cK p, rU p, rS p, cS p, cR p], r.Disjoint (cStack p)
  tab : ∀ r ∈ [cK p, rU p, rS p, cS p, cStack p], (rTab p).Disjoint r
  nK : p.kp.toNat + 9 * p.L ≤ 2 ^ 64
  nU : p.up.toNat + 8 ≤ 2 ^ 64
  nS : p.B.toNat + p.Z ≤ 2 ^ 64
  nT : p.stp.toNat + 56 ≤ 2 ^ 64
  nR : p.rp.toNat + p.randLen ≤ 2 ^ 64
  nTab : p.T.toNat + 8 * 1024 ≤ 2 ^ 64
  aTab : p.T.toNat % 64 = 0
  len : primeLenValid p.L
  scratch : Spec.Rsa.scratchWords (2 * p.L) ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  rand_cap : p.randLen ≤ primeEntropy p.L
  rand64 : p.randLen < 2 ^ 64
  z64 : p.Z / 8 < 2 ^ 64

theorem GenInput.cfacts {p : GenPublic} {s : State} (h : GenInput p s) : CFacts p := by
  have htw := fun r (hr : r ∈ inWrites s) => h.tab_wr (by rw [h.wr_eq]; exact hr)
  have hts := h.tab_stack
  have hfit := h.tab_fit
  have hal : (tabR s).base.toNat % 64 = 0 := h.consts.2.2.2 _ (GenInput.tab_reg s)
  obtain ⟨h16, hsp, _, _, hnw, hpw, hwr, hstk, hlen, hkey, hscr, -, -, -, hcap, aU, aS, aT⟩ := h.base
  cases h.2
  simp only [stripConsts_gpr, stripConsts_sp] at h16 hsp hnw hpw hwr hstk hlen hkey hscr hcap aU aS aT
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk htw
  obtain ⟨⟨pku, pks, pkt⟩, ⟨pus, put⟩, pst, -⟩ := hpw
  obtain ⟨wkr, wur, wsr, wtr⟩ := hwr
  obtain ⟨bk, bu, bs, bt, br⟩ := hstk
  obtain ⟨nk, nu, ns, nt, nr⟩ := hnw
  obtain ⟨tk, tu, ts, tt⟩ := htw
  have hk : inKey (stripConsts tables s) = ⟨s.gpr .a0, 9 * genLen s⟩ := by
    simp only [inKey, stripConsts_gpr, hkey]; rfl
  have hk' : inKey s = ⟨s.gpr .a0, 9 * genLen s⟩ := by
    simp only [inKey]; rw [hkey]; rfl
  rw [hk] at pku pks pkt wkr bk nk
  rw [hk'] at tk
  refine ⟨hsp, h16, aU, aS, aT, pku, pks, pkt, pus, put, pst, wkr, wur, wsr, wtr, ?_, ?_, nk, nu, ns, nt, nr, hfit, hal, hlen,
    ?_, ?_, hcap, BitVec.isLt _, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [bk.symm, bu.symm, bs.symm, bt.symm, br.symm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [tk, tu, ts, tt, hts]
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]; exact hscr
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]; exact BitVec.isLt _

/-! ## Sub-regions and disjointness -/

section

variable {p : GenPublic} {used : Nat} {st : KeyProgress}

theorem plen_le : plenOf p st ≤ p.L := by unfold plenOf; split <;> omega

theorem rO_sub (hf : CFacts p) : Region.Sub (rO p st) (cK p) := by
  have := hf.len.1
  unfold rO outOf
  split
  · exact slot_sub _ (by omega)
  · exact slot_sub _ (by omega)

theorem rP_sub : Region.Sub (rP p st) (cK p) := slot_sub _ (by have := plen_le (p := p) (st := st); omega)

theorem rR_sub (hu : used ≤ p.randLen) : Region.Sub (rR p used) (cR p) := Offset.sub_base _ (by omega)

theorem rT_sub : Region.Sub (rT p) (cS p) := Region.sub_prefix (by decide)

theorem rE_sub : Region.Sub (rE p) (cS p) := Offset.sub_base _ (by decide)

theorem rA_sub : Region.Sub (rA p) (cStack p) := Offset.sub_below _ (by decide) (by decide)

theorem rLow_sub : Region.Sub (rLow p) (cStack p) := by
  simp only [rLow, cStack, callSp]
  exact below_body' p.sp 160 496

theorem oP (hf : CFacts p) : (rO p st).Disjoint (rP p st) := by
  have := hf.len.1
  unfold rO rP outOf plenOf
  split
  · intro x _ hy; simp only [Region.Contains] at hy; omega
  · exact slot_disjoint _ (.inr (by omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)

theorem tE : (rT p).Disjoint (rE p) := by
  have := Offset.sep p.stp (d := 0) (n := 32) (e := 48) (k := 8) (.inl (by decide)) (by decide) (by decide)
  rw [BitVec.add_zero] at this
  exact fun x hx hy => this x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

theorem args_low : (rLow p).Disjoint (rA p) := by
  have e : below (callSp p) 496 = ⟨p.sp - BitVec.ofNat 64 656, 496⟩ := by
    simp only [below, callSp, BitVec.sub_sub]; rfl
  rw [rLow, e, rA]
  have hs := Offset.sep_below p.sp 656 (a := 656) (n := 496) (b := 160) (k := 32) (by decide) (by decide)
    (Or.inl (by decide)) (by decide) (by decide)
  exact fun x hx hy => hs x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains, callSp] at hy; omega)

end

/-! ## The search's precondition -/

/-- The regions the search reads, and those it writes. -/
def sReads (p : GenPublic) (used : Nat) (st : KeyProgress) : List Region :=
  [rE p, rP p st, rR p used, rA p, rTab p]
def sWrites (p : GenPublic) (st : KeyProgress) : List Region := [rO p st, rU p, rS p, rT p]

/-- The search's entry, as the call makes it. -/
abbrev callS (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) : State :=
  u.callEntry.withRegions (sReads p used st) (sWrites p st)

theorem callS_gpr {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callS p used st u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem callS_sp (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) :
    (callS p used st u).sp = u.sp := rfl

theorem callS_mem (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) :
    (callS p used st u).mem = u.mem := rfl

theorem callS_syms (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) :
    (callS p used st u).syms = u.syms := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The search's stack arguments. -/
theorem callS_args {p : GenPublic} {used : Nat} {st : KeyProgress} {s u : State}
    (hu : u.sp = callSp p) (hm : u.mem = callMem p used s) :
    stackArg (callS p used st u) 0 = BitVec.ofNat 64 (p.randLen - used) ∧ stackArg (callS p used st u) 1 = p.B ∧
      stackArg (callS p used st u) 2 = BitVec.ofNat 64 (p.Z / 8) ∧ stackArg (callS p used st u) 3 = p.stp := by
  have hw (j : Nat) (hj : j < 4) : stackArg (callS p used st u) j =
      frameValue (callValues p used) j (word s.mem (callSp p) (8 * j)) := by
    unfold stackArg stackArgAddr
    rw [callS_sp, callS_mem, hu, hm, ← writeFrame_word _ _ _ (callValues_bound p used) j (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hw 0 (by decide)]; rfl
  · rw [hw 1 (by decide)]; rfl
  · rw [hw 2 (by decide)]; rfl
  · rw [hw 3 (by decide)]; rfl

section

variable {p : GenPublic} {used : Nat} {st : KeyProgress} {s u : State}

theorem callS_regions (hu : u.sp = callSp p) (ha : SearchRegs p used st u) (hm : u.mem = callMem p used s)
    (hf : CFacts p) :
    Search.inReads (callS p used st u) = (sReads p used st).take 4 ∧
      Search.inWrites (callS p used st u) = sWrites p st := by
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (st := st) hu hm
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  have hL := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by obtain ⟨-, h, -⟩ := hL; omega)
  have tp : (BitVec.ofNat 64 (plenOf p st)).toNat = plenOf p st :=
    toNat_ofNat_lt (by have := plen_le (p := p) (st := st); obtain ⟨-, h, -⟩ := hL; omega)
  have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by rw [toNat_ofNat_lt hf.z64]; exact hf.z8
  have t8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
  have hargs : stackArgAddr (callS p used st u) 0 = callSp p := by
    simp only [stackArgAddr, callS_sp, hu, Nat.mul_zero, BitVec.add_zero]
  simp only [Search.inReads, Search.inWrites, Search.inE, Search.inP, Search.inRand, Search.inArgs,
    Search.inOut, Search.inUsed, Search.inScr, Search.inState, sReads, sWrites,
    callS_gpr (show Reg.a0 ∉ linkRegs by decide), callS_gpr (show Reg.a1 ∉ linkRegs by decide),
    callS_gpr (show Reg.a2 ∉ linkRegs by decide), callS_gpr (show Reg.a3 ∉ linkRegs by decide),
    callS_gpr (show Reg.a4 ∉ linkRegs by decide), callS_gpr (show Reg.a5 ∉ linkRegs by decide),
    callS_gpr (show Reg.a6 ∉ linkRegs by decide), callS_gpr (show Reg.a7 ∉ linkRegs by decide),
    r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3, tl, tp, tr, tz, t8, hargs]
  constructor <;> first | trivial | rfl

theorem slot_nowrap (hf : CFacts p) {j n : Nat} (h : j * p.L + n ≤ 9 * p.L) :
    (p.kp + BitVec.ofNat 64 (j * p.L)).toNat + n ≤ 2 ^ 64 := by
  have := hf.nK
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  omega

theorem callSp_toNat (hf : CFacts p) : (callSp p).toNat = p.sp.toNat - 160 := by
  have := hf.room
  have hs : stackUse = 656 := rfl
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 160).toNat = 160 from rfl]; omega),
    show (BitVec.ofNat 64 160).toNat = 160 from rfl]

/-- The call's frame and its stack arguments: below the controller's stack
pointer. -/
theorem call_stack_frame {original : State} (_h : GenFrame p original used st s) :
    Frame [cStack p] s.mem (callMem p used s) := by
  refine (writeFrame_frame_size _ _ (callValues p used) (size := 32) (by decide) (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, rA_sub⟩

theorem callS_tabs (p : GenPublic) (used : Nat) (st : KeyProgress) {u : State}
    (hT : u.syms Impl.RsaKeyGen.TrialTable32.symbol = p.T) :
    constRegs tables (callS p used st u) = [rTab p] := by
  rw [GenInput.tables_eq, constRegs, Abi.constRegions_cons, Abi.constRegions_nil, GenInput.packed_length,
    callS_syms, hT]

/-- The search's precondition at its entry. -/
theorem callS_pre {original : State} (h : GenLive p original used st s)
    (hu : u.sp = callSp p) (ha : SearchRegs p used st u) (hm : u.mem = callMem p used s)
    (hT : u.syms Impl.RsaKeyGen.TrialTable32.symbol = p.T)
    (htab : ∀ i < 1024, u.mem.readW (p.T + BitVec.ofNat 64 (8 * i)) 64 = Impl.RsaKeyGen.TrialTable32.packed.getD i 0) :
    Search.searchPre (callS p used st u) := by
  have hf := h.input.cfacts
  obtain ⟨hrd, hwr⟩ := callS_regions (st := st) hu ha hm hf
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (st := st) hu hm
  have hfr : Frame (GenInput.callChanges original) s.mem u.mem := by rw [hm]; exact alloc_args_frame h.toGenFrame
  have hL := hf.len
  obtain ⟨hL1, hL2, -⟩ := hL
  have hul := h.used_le
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hr4 : (callS p used st u).gpr .a1 = BitVec.ofNat 64 p.L := by
    rw [callS_gpr (by decide)]; exact ha.2.1
  have hr7 : (callS p used st u).gpr .a4 = BitVec.ofNat 64 8 := by
    rw [callS_gpr (by decide)]; exact ha.2.2.2.2.1
  have hcsp := callSp_toNat hf
  have hroom := hf.room
  have hsu : stackUse = 656 := rfl
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, sU, sS, sT, sR⟩ := hst
  have hfs : Frame [cStack p] s.mem u.mem := by rw [hm]; exact call_stack_frame h.toGenFrame
  have hword (d : Nat) (hd : d + 8 ≤ 56) :
      u.mem.readW (p.stp + BitVec.ofNat 64 d) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 d) 64 :=
    hfs.readW (Offset.contains_base _ hd (by have := hf.nT; omega)) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact sT) (by decide)
  have hE : Spec.Rsa.bytesAt u.mem (p.stp + BitVec.ofNat 64 48) 8 = p.eB := by
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfs.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact sT.sub_left (by
        rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]; exact Offset.sub_base _ (by decide)))
      (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have st0 := h.state
  have oK := rO_sub (st := st) hf
  have pK := rP_sub (p := p) (st := st)
  have rRc := rR_sub (p := p) hul
  have hlowT := hf.tab
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlowT
  obtain ⟨tK, tU, tS, tS', tStk⟩ := hlowT
  have hres : abi.reserved 496 (callS p used st u) = [rLow p] := by
    show stackBelow (callS p used st u).sp 496 = _
    rw [callS_sp, hu]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · show (callS p used st u).sp.toNat % 16 = 0
    rw [callS_sp, hu, hcsp]; have := hf.sp16; omega
  · show (callS p used st u).sp.toNat + 32 ≤ 2 ^ 64
    rw [callS_sp, hu, hcsp]; have := p.sp.isLt; omega
  · show 496 ≤ (callS p used st u).sp.toNat
    rw [callS_sp, hu, hcsp]; omega
  · show (sReads p used st).take (5 - 1) = _
    rw [show Search.inReads (stripConsts Search.tables (callS p used st u)) = Search.inReads (callS p used st u)
      from rfl, hrd]
  · show sWrites p st = _
    rw [show Search.inWrites (stripConsts Search.tables (callS p used st u)) = Search.inWrites (callS p used st u)
      from rfl, hwr]
  · rw [show Search.inWrites (stripConsts Search.tables (callS p used st u)) = Search.inWrites (callS p used st u)
      from rfl, show Search.inReads (stripConsts Search.tables (callS p used st u)) = Search.inReads (callS p used st u)
      from rfl, hwr, hrd]
    intro r hr
    simp only [sWrites, sReads, List.take, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show (outOf p st).toNat + p.L ≤ 2 ^ 64
      unfold outOf; split
      · exact slot_nowrap hf (by omega)
      · exact slot_nowrap hf (by omega)
    · exact hf.nU
    · exact hf.nS
    · have := hf.nT; simp only; omega
    · simp only; rw [BitVec.toNat_add, toNat_ofNat_lt (by decide)]; have := hf.nT; omega
    · show (p.kp + BitVec.ofNat 64 (4 * p.L)).toNat + plenOf p st ≤ 2 ^ 64
      exact slot_nowrap hf (by have := plen_le (p := p) (st := st); omega)
    · simp only; rw [BitVec.toNat_add, toNat_ofNat_lt (by have := hf.rand64; omega)]; have := hf.nR; omega
    · simp only; rw [hcsp]; have := p.sp.isLt; omega
  · rw [show Search.inWrites (stripConsts Search.tables (callS p used st u)) = Search.inWrites (callS p used st u)
      from rfl, hwr]
    simp only [sWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hf.kU.sub_left oK, hf.kS.sub_left oK, (hf.kT.sub_left oK).sub_right rT_sub⟩,
      ⟨hf.uS, hf.uT.sub_right rT_sub⟩, hf.sT.sub_right rT_sub, fun _ h => h.elim⟩
  · rw [show Search.inWrites (stripConsts Search.tables (callS p used st u)) = Search.inWrites (callS p used st u)
      from rfl, show Search.inReads (stripConsts Search.tables (callS p used st u)) = Search.inReads (callS p used st u)
      from rfl, hwr, hrd]
    simp only [sWrites, sReads, List.take, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨(hf.kT.sub_left oK).sub_right rE_sub, oP hf, (hf.kR.sub_left oK).sub_right rRc,
        (sK.sub_left oK).sub_right rA_sub⟩,
      ⟨hf.uT.sub_right rE_sub, (hf.kU.sub_left pK).symm, hf.uR.sub_right rRc, sU.sub_right rA_sub⟩,
      ⟨hf.sT.sub_right rE_sub, (hf.kS.sub_left pK).symm, hf.sR.sub_right rRc, sS.sub_right rA_sub⟩,
      ⟨tE, ((hf.kT.sub_left pK).sub_right rT_sub).symm, (hf.tR.sub_left rT_sub).sub_right rRc,
        (sT.sub_left rT_sub).sub_right rA_sub⟩⟩
  · rw [show Search.inWrites (stripConsts Search.tables (callS p used st u)) = Search.inWrites (callS p used st u)
      from rfl, show Search.inReads (stripConsts Search.tables (callS p used st u)) = Search.inReads (callS p used st u)
      from rfl, hwr, hrd, stripConsts_sp, callS_sp, hu]
    intro r hr
    simp only [sWrites, sReads, List.take, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (sK.sub_left oK).symm.sub_left rLow_sub
    · exact sU.symm.sub_left rLow_sub
    · exact sS.symm.sub_left rLow_sub
    · exact (sT.sub_left rT_sub).symm.sub_left rLow_sub
    · exact (sT.sub_left rE_sub).symm.sub_left rLow_sub
    · exact (sK.sub_left pK).symm.sub_left rLow_sub
    · exact (sR.sub_left rRc).symm.sub_left rLow_sub
    · exact args_low
  · show primeLenValid (Search.searchLen (callS p used st u))
    simp only [Search.searchLen, hr4, tl]; exact ⟨hL1, hL2, hf.len.2.2⟩
  · show 1 ≤ ((callS p used st u).gpr .a4).toNat
    rw [hr7]; decide
  · show ((callS p used st u).gpr .a4).toNat ≤ 8
    rw [hr7]; decide
  · show ((callS p used st u).gpr .a6).toNat = 0 ∨ ((callS p used st u).gpr .a6).toNat = Search.searchLen (callS p used st u)
    rw [callS_gpr (by decide), ha.2.2.2.2.2.2.1]
    simp only [Search.searchLen, hr4, tl]
    rw [toNat_ofNat_lt (by have := plen_le (p := p) (st := st); omega)]
    unfold plenOf; split
    · exact .inl rfl
    · exact .inr rfl
  · show Spec.Rsa.scratchWords (Search.searchLen (callS p used st u)) ≤ (stackArg (callS p used st u) 2).toNat
    simp only [Search.searchLen, hr4, tl, a2]
    rw [toNat_ofNat_lt hf.z64]
    have := hf.scratch; unfold Spec.Rsa.scratchWords at this ⊢; omega
  · show Search.searchRemaining (callS p used st u) ≤
      primeLimit (8 * Search.searchLen (callS p used st u)) (Spec.Rsa.os2ip (Search.searchE (callS p used st u)))
    have h0 := hword 0 (by decide)
    rw [BitVec.add_zero] at h0
    have h0' := st0.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0'
    have hlim : st.remaining < 2 ^ 64 := by
      have := st0.remaining_le
      unfold KeySearch.limitOf primeLimit at this
      split at this <;> omega
    have hrem : (Search.searchRemaining (callS p used st u)) = st.remaining := by
      simp only [Search.searchRemaining, a3, callS_mem, h0, h0']
      exact toNat_ofNat_lt hlim
    have hse : Search.searchE (callS p used st u) = p.eB := by
      simp only [Search.searchE, callS_gpr (show Reg.a3 ∉ linkRegs by decide),
        callS_gpr (show Reg.a4 ∉ linkRegs by decide), ha.2.2.2.1, ha.2.2.2.2.1,
        toNat_ofNat_lt (show 8 < 2 ^ 64 by decide), callS_mem]
      exact hE
    rw [hrem, hse]
    simp only [Search.searchLen, hr4, tl]
    exact st0.remaining_le
  · show (callS p used st u).mem.readW (stackArg (callS p used st u) 3 + 8) 64 =
      BitVec.ofNat 64 (Search.searchLen (callS p used st u))
    simp only [Search.searchLen, hr4, tl, a3, callS_mem]
    rw [show (p.stp + 8 : Addr) = p.stp + BitVec.ofNat 64 8 from rfl, hword 8 (by decide)]
    exact st0.len
  · show (callS p used st u).mem.readW (stackArg (callS p used st u) 3 + 16) 64 =
      BitVec.ofNat 64 (primeEntropy (Search.searchLen (callS p used st u)))
    simp only [Search.searchLen, hr4, tl, a3, callS_mem]
    rw [show (p.stp + 16 : Addr) = p.stp + BitVec.ofNat 64 16 from rfl, hword 16 (by decide)]
    exact st0.cap
  · show (stackArg (callS p used st u) 0).toNat ≤ primeEntropy (Search.searchLen (callS p used st u))
    simp only [Search.searchLen, hr4, tl, a0]
    rw [toNat_ofNat_lt (by have := hf.rand64; omega)]
    have := hf.rand_cap; omega
  · show ((callS p used st u).gpr .a2).toNat % 8 = 0
    rw [callS_gpr (by decide), ha.2.2.1]; exact hf.aU
  · show (stackArg (callS p used st u) 1).toNat % 8 = 0
    rw [a1]; exact hf.aS
  · show (stackArg (callS p used st u) 3).toNat % 8 = 0
    rw [a3]; exact hf.aT
  · show (sReads p used st).drop (5 - 1) = _
    rw [callS_tabs p used st hT]; rfl
  · intro c hc
    have hc' : c ∈ [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := hc
    obtain rfl := List.mem_singleton.mp hc'
    intro i hi
    dsimp only at hi ⊢
    rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at hi
    have e := htab i hi
    rw [← hT] at e
    exact e
  · rw [callS_tabs p used st hT]
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    refine ⟨hf.nTab, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [State.withRegions_wr, sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact tK.sub_right oK
      · exact tU
      · exact tS
      · exact tS'.sub_right rT_sub
    · rw [hres] at hr
      obtain rfl := List.mem_singleton.mp hr
      exact tStk.sub_right rLow_sub
  · rw [callS_tabs p used st hT]
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact hf.aTab

end

/-! ## The prime search, run

`searchRun`: in a frame of its stack arguments, the search's arguments and its
call. It leaves the search's status, its prime or zeros at its output, the
octets it consumed at `used`, and its counted candidates left and request in
the state; it writes nothing else but the working space and the stack below
the frame saving `ra`.
-/

open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

/-- The prime search, as the controller calls it. -/
def searchCall (v : RoundImpl) : Prog isa :=
  .call ("vg_rsa_prime_search" ++ v.suffix) (Search.searchCode v)

theorem search_sdepth (v : RoundImpl) :
    sdepth (Impl.RsaKeyGen.RISCV64.Search.code (Search.Cand.ofRound v).call) ≤ 496 := by
  have := Search.iteration_sdepth (Search.Cand.ofRound v)
  simp only [Impl.RsaKeyGen.RISCV64.Search.code, Impl.RsaKeyGen.RISCV64.Search.search, sdepth,
    Instr.frameBytes, Impl.RsaKeyGen.RISCV64.Search.frameBytes]
  omega

/-- The stack a call may write: below the frame saving `ra`. -/
abbrev rStk (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 stackUse, 528⟩

/-- What the search may write, as the controller sees it. -/
def searchChanges (p : GenPublic) (st : KeyProgress) : List Region :=
  [rO p st, rU p, rS p, rT p, rStk p]

/-- What the search of the progress' prime at `used` leaves. -/
structure AfterSearch (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress)
    (s t : State) : Prop where
  frame : GenFrame p original used ⟨st.left, st.phase, (primeOf p.L p.eB st ((genRand original).drop used)).remaining⟩ t
  status : ((t.gpr .a0).setWidth 32).toNat = (primeOf p.L p.eB st ((genRand original).drop used)).status
  usedw : word t.mem p.up 0 = BitVec.ofNat 64 (primeOf p.L p.eB st ((genRand original).drop used)).used
  out : Spec.Rsa.bytesAt t.mem (outOf p st) p.L =
    (match (primeOf p.L p.eB st ((genRand original).drop used)).outcome with
      | .accepted c => Spec.Rsa.i2osp c p.L
      | _ => List.replicate p.L 0)
  req : ∃ requested, word t.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (primeOf p.L p.eB st ((genRand original).drop used)).Requests (primeEntropy p.L) requested
  mem : Frame (searchChanges p st) s.mem t.mem

section

variable {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}

theorem GenFrame.regions (h : GenFrame p original used st s) :
    inKey original = cK p ∧ inUsed original = rU p ∧ inScr original = rS p ∧
      inState original = cS p ∧ inRand original = cR p ∧ tabR original = rTab p := by
  refine ⟨h.key_region, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← h.input.2] <;> rfl

theorem GenFrame.orig_wr (h : GenFrame p original used st s) : original.wr = [cK p, rU p, rS p, cS p] := by
  obtain ⟨hk, hu, hs, ht, -, -⟩ := h.regions
  rw [h.input.wr_eq, ← hk, ← hu, ← hs, ← ht]; rfl

theorem call_low_frame (_h : GenFrame p original used st s) :
    Frame [rStk p] s.mem (callMem p used s) := by
  refine (writeFrame_frame_size _ _ (callValues p used) (size := 32) (by decide) (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  exact Offset.sub_below _ (by decide) (by decide)

theorem search_covers_writes (h : GenFrame p original used st s)
    (hw : u.wr = (allocd 32 s).wr) : Covers (sWrites p st) u.wr := by
  have hf := h.input.cfacts
  have hwo := h.orig_wr
  rw [hw]
  refine Covers.of_sub fun r hr => ?_
  have hin : ∀ q ∈ [cK p, rU p, rS p, cS p], q ∈ (allocd 32 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hL := hf.len.1
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨cK p, hin _ (by simp), if phaseWord st.phase = 0 then 4 * p.L else 5 * p.L, ?_, ?_⟩
    · simp only [outOf]; split <;> rfl
    · show _ + p.L ≤ 9 * p.L
      split <;> omega
  · exact ⟨rU p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨cS p, hin _ (by simp), 0, by simp, by simp⟩

theorem search_covers_reads (h : GenFrame p original used st s)
    (hrd : u.rd = (allocd 32 s).rd) (hw : u.wr = (allocd 32 s).wr) :
    Covers (sReads p used st ++ sWrites p st) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (search_covers_writes h hw).right
  have hf := h.input.cfacts
  obtain ⟨-, -, -, -, hr, htab⟩ := h.regions
  have hwo := h.orig_wr
  have hrR : cR p ∈ original.rd := by rw [← hr]; exact h.input.rd_mem (by simp [inReads])
  have hrT : rTab p ∈ original.rd := by rw [← htab]; exact h.input.tab_rd
  have hsrd : (allocd 32 s).rd = original.rd := h.rd
  have hul := h.used_le
  have hL := hf.len.1
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  have hwin : ∀ q ∈ [cK p, cS p], q ∈ (allocd 32 s).rd ++ (allocd 32 s).wr := by
    intro q hq
    refine List.mem_append_right _ ?_
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  simp only [sReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl
  · exact ⟨cS p, hwin _ (by simp), 48, rfl, by simp⟩
  · exact ⟨cK p, hwin _ (by simp), 4 * p.L, rfl, by
      show _ + plenOf p st ≤ 9 * p.L; have := plen_le (p := p) (st := st); omega⟩
  · exact ⟨cR p, List.mem_append_left _ (by rw [hsrd]; exact hrR), used, rfl, by simp; omega⟩
  · exact ⟨⟨callSp p, 32⟩, List.mem_append_right _ (by rw [alloc_call_wr h]; exact List.mem_cons_self ..),
      0, by simp, by simp⟩
  · exact ⟨rTab p, List.mem_append_left _ (by rw [hsrd]; exact hrT), 0, by simp, by simp⟩

/-- The search's result, from the controller's loop state. -/
theorem callS_result (h : GenLive p original used st s)
    (hu : u.sp = callSp p) (ha : SearchRegs p used st u) (hm : u.mem = callMem p used s) :
    Search.searchResult (callS p used st u) = primeOf p.L p.eB st ((genRand original).drop used) := by
  have hf := h.input.cfacts
  obtain ⟨a0, -, -, a3⟩ := callS_args (st := st) hu hm
  have hfs : Frame [cStack p] s.mem u.mem := by rw [hm]; exact call_stack_frame h.toGenFrame
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, sR⟩ := hst
  obtain ⟨-, r4, -, r6, r7, r8, r9, r10⟩ := ha
  obtain ⟨hL1, hL2, -⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p) ∨ Region.Sub R (cR p))
      (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callS p used st u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfs.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR, sR.sub_left hR]
  have hlim : st.remaining < 2 ^ 64 := by
    have := h.state.remaining_le
    unfold KeySearch.limitOf primeLimit at this
    split at this <;> omega
  unfold Search.searchResult
  congr 1
  · simp only [Search.searchLen, callS_gpr (show Reg.a1 ∉ linkRegs by decide), r4, tl]
  · simp only [Search.searchE, callS_gpr (show Reg.a3 ∉ linkRegs by decide),
      callS_gpr (show Reg.a4 ∉ linkRegs by decide), r6, r7, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    exact hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr (.inl rE_sub)) (by show 8 ≤ 2 ^ 64; decide)
  · simp only [Search.searchP, callS_gpr (show Reg.a5 ∉ linkRegs by decide),
      callS_gpr (show Reg.a6 ∉ linkRegs by decide), r8, r9,
      toNat_ofNat_lt (show plenOf p st < 2 ^ 64 by have := plen_le (p := p) (st := st); omega)]
    have hk := h.key.other
    unfold plenOf
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => simp [phaseWord, KeyPhase.other, Spec.Rsa.bytesAt]
    | q pB =>
      simp only [phaseWord, Nat.one_ne_zero, ↓reduceIte, KeyPhase.other]
      rw [← hk pB rfl]
      exact hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (slot_sub _ (by omega))) (by show p.L ≤ 2 ^ 64; omega)
  · have hw0 : u.mem.readW (p.stp + BitVec.ofNat 64 0) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 0) 64 :=
      hfs.readW (Offset.contains_base (k := 56) _ (by decide) (by decide)) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact sT) (by decide)
    rw [BitVec.add_zero] at hw0
    have h0' := h.state.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0'
    simp only [Search.searchRemaining, a3, callS_mem, hw0, h0']
    exact toNat_ofNat_lt hlim
  · simp only [Search.searchRand, callS_gpr (show Reg.a7 ∉ linkRegs by decide), r10, a0,
      toNat_ofNat_lt (show p.randLen - used < 2 ^ 64 by have := hf.rand64; omega)]
    have := hbytes (R := rR p used) (.inr (.inr (rR_sub h.used_le))) (by have := hf.rand64; simp; omega)
    simp only at this
    rw [this, Search.bytesAt_drop, h.random]

theorem searchChanges_sub (h : GenFrame p original used st s) :
    ∀ r ∈ searchChanges p st, ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, -, -, -⟩ := h.regions
  have hT : (⟨original.gpr .a7, 32⟩ : Region) = rT p := by rw [← h.input.2]; rfl
  have hS : (⟨original.sp - BitVec.ofNat 64 stackUse, 544⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 stackUse, 544⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hu, hs, hT, hS]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., rO_sub hf⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨p.sp - BitVec.ofNat 64 stackUse, 544⟩, by simp, Region.sub_prefix (by decide)⟩

theorem below_call_sub (sp : Addr) {n : Nat} (hn : n ≤ 496) :
    Region.Sub (below (sp - BitVec.ofNat 64 160) n) ⟨sp - BitVec.ofNat 64 stackUse, 528⟩ := by
  have hsu : stackUse = 656 := rfl
  simp only [below, BitVec.sub_sub]
  rw [← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

end

theorem search_run (v : RoundImpl) {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    WP isa (searchRun (searchCall v)) s (AfterSearch p original used st s) := by
  have hf := h.input.cfacts
  have hspn : s.sp.toNat = p.sp.toNat - 128 := by
    have hF := h.input.F_toNat
    have hr := hf.room
    have hsu : stackUse = 656 := rfl
    rw [h.sp, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (16 : BitVec 64).toNat = 16 from rfl]; omega),
      show (16 : BitVec 64).toNat = 16 from rfl, hF]
    omega
  have hroom : 32 ≤ s.sp.toNat := by have := hf.room; have hsu : stackUse = 656 := rfl; omega
  unfold searchRun searchCall
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (WP.mono (search_stack_ok h.toGenFrame) fun u ⟨⟨hm, ku⟩, hyu⟩ => ?_)
  refine WP.seq (WP.mono (search_args_ok h.toGenFrame hm ku) fun w ⟨⟨⟨ha, hmw⟩, kw⟩, hyw⟩ => ?_)
  have hu : w.sp = callSp p := kw.sp.trans (ku.sp.trans (alloc_call_sp h.toGenFrame))
  have hm' : w.mem = callMem p used s := hmw.trans hm
  have hy : w.syms = original.syms := hyw.trans (hyu.trans h.syms)
  have krd : w.rd = (allocd 32 s).rd := kw.rd.trans ku.rd
  have kwr : w.wr = (allocd 32 s).wr := kw.wr.trans ku.wr
  have hT : w.syms Impl.RsaKeyGen.TrialTable32.symbol = p.T := by rw [hy, ← h.input.2]; rfl
  have hft : Frame (GenInput.changes original) original.mem w.mem :=
    h.tab.trans (frame_of_callChanges original (by rw [hm']; exact alloc_args_frame h.toGenFrame))
  have htab : ∀ i < 1024, w.mem.readW (p.T + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
    intro i hi; rw [← hT, hy]; exact h.input.tab_frame hft i hi
  have hd := search_sdepth v
  refine VG.RISCV64.WP.of_syms (WP.callAny (k := Search.searchContract)
    (Search.search_correct (Search.Cand.ofRound v)) (callS_pre h hu ha hm' hT htab)
    (search_covers_reads h.toGenFrame krd kwr) (search_covers_writes h.toGenFrame kwr) ?_ (by omega))
  intro t htr htw hsp hfr hcs hpost hyt
  have hres := callS_result h hu ha hm'
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (st := st) hu hm'
  have hlen : Search.searchLen (callS p used st w) = p.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.a1 ∉ linkRegs by decide), ha.2.1]
    exact toNat_ofNat_lt (by have := hf.len.2.1; omega)
  obtain ⟨hst, hout, hused, req, hwords, hreq⟩ := hpost
  have h3' : (callS p used st w).gpr .a0 = outOf p st := by rw [callS_gpr (by decide)]; exact ha.1
  have h5' : (callS p used st w).gpr .a2 = p.up := by rw [callS_gpr (by decide)]; exact ha.2.2.1
  simp only [hres, hlen, State.withRegions_mem, State.withRegions_gpr, a3, h3', h5'] at hst hout hused hwords hreq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 1 = [0] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hwords hused
  simp only [Nat.reduceMul] at hwords hused
  obtain ⟨w0, w1, w2, w3⟩ := hwords
  -- The memory: the stack arguments, then the search.
  have f₀ : Frame (searchChanges p st) s.mem w.mem := by
    rw [hm']
    exact (call_low_frame h.toGenFrame).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨rStk p, by simp [searchChanges], fun _ h => h⟩
  have f₁ : Frame (searchChanges p st) w.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨r, ?_, fun _ h => h⟩
      simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨rStk p, by simp [searchChanges], by rw [hu]; exact below_call_sub _ hd⟩
  have hframe := f₀.trans f₁
  have hrem := KeySearch.primeSearch_remaining_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
  have hle := h.state.remaining_le
  refine ⟨h.toGenFrame.restore (show t.rd = s.rd from htr.trans krd)
      (show t.wr.tail = s.wr by rw [htw, kwr]; rfl) ?_ (hyt.trans (hyw.trans hyu))
      (fun r hr => (hcs r hr).trans ((kw.gpr r (by revert r hr; decide)).trans (ku.gpr r (by revert r hr; decide))))
      (hframe.sub (searchChanges_sub h.toGenFrame)) w0 w1 w2 (.inl rfl) rfl (Nat.le_trans hrem hle),
    ?_, hused, hout, ⟨req, w3, hreq⟩, hframe⟩
  · show t.sp + BitVec.ofNat 64 32 = s.sp
    rw [hsp, hu, ← alloc_call_sp h.toGenFrame]
    exact BitVec.sub_add_cancel _ _
  · exact hst

end VG.Proof.RsaKeyGen.RISCV64.Generate

/-! # The controller's blocks after a search (RISC-V)

The octets the search consumed added to the frame's count, and the stores
that start the next prime's search (`nextPrime`) or end the key search
(`finishWith`), each with the frame and the state they leave.
-/

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)
open VG.Proof.RsaKeyGen.RISCV64.Search (WP.keepS KeepS)


/-- The low 32 bits (`slli 32`, `srli 32`), of a status that fits. -/
theorem low32_of {x : BitVec 64} {status : Nat} (hs : (x.setWidth 32).toNat = status) (_h : status < 2 ^ 32) :
    x <<< 32 >>> 32 = BitVec.ofNat 64 status := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := status) (by omega)]
  rw [BitVec.toNat_setWidth] at hs
  have h1 : x.toNat * 2 ^ 32 % 2 ^ 64 = x.toNat % 2 ^ 32 * 2 ^ 32 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right]
  rw [h1, Nat.mul_div_cancel _ (by decide), hs]

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  · rintro rfl; rfl

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

theorem state_region (h : GenFrame p original used st s) : inState original = ⟨p.stp, 56⟩ := by
  rw [← h.input.2]; rfl

theorem used_region (h : GenFrame p original used st s) : inUsed original = ⟨p.up, 8⟩ := by
  rw [← h.input.2]; rfl

theorem stateScr (h : GenFrame p original used st s) : Scr s p.stp 56 := by
  have hn := h.input.nowrap (r := inState original) (by simp [inWrites])
  rw [h.state_region] at hn
  have ha : p.stp.toNat % 8 = 0 := by rw [← h.input.2]; exact h.input.state_al
  refine Scr.of_mem ?_ hn ha
  rw [h.wr, h.input.wr_eq, ← h.state_region]
  simp [inWrites]

theorem usedScr (h : GenFrame p original used st s) : Scr s p.up 8 := by
  have hn := h.input.nowrap (r := inUsed original) (by simp [inWrites])
  rw [h.used_region] at hn
  have ha : p.up.toNat % 8 = 0 := by rw [← h.input.2]; exact h.input.used_al
  refine Scr.of_mem ?_ hn ha
  rw [h.wr, h.input.wr_eq, ← h.used_region]
  simp [inWrites]

theorem state_frame (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.stp, 56⟩ := h.input.frame_state

end GenFrame

/-- The frame's headers after the octets consumed are `u`. -/
theorem slots_used {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (u : Nat) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 14)
    (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (p.headers u) := by
  have hb' : ∀ e ∈ (8, BitVec.ofNat 64 u) :: values, e.1 < 20 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · show 8 < 20; decide
    · have := hb e he; omega
  have hw (j : Nat) (hj : j < 20) (hj8 : j ≠ 8) (hv : ∀ e ∈ values, j ≠ e.1) :
      word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [writeFrame_word _ _ _ hb' j hj]
    show frameValue values j (if j = 8 then _ else _) = _
    rw [ite_eq_right hj8]
    exact frameValue_unchanged _ _ _ hv
  have hw8 : word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * 8) = BitVec.ofNat 64 u := by
    rw [writeFrame_word _ _ _ hb' 8 (by decide)]
    show frameValue values 8 (if 8 = 8 then _ else _) = _
    rw [ite_eq_left rfl]
    exact frameValue_unchanged _ _ _ fun e he heq => (hnot e he).2.2.2.2.2.2.2.2.1 heq.symm
  have hk (j : Nat) (v : BitVec 64) (hj : j < 20) (hj8 : j ≠ 8) (hjv : (j, v) ∈ p.headers used)
      (hv : ∀ e ∈ values, j ≠ e.1) :
      word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * j) = v := by
    have hh := h.headers (j, v) hjv
    dsimp only at hh
    rw [hw j hj hj8 hv]; exact hh
  simp only [Slots, GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨hk 0 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).1 q.symm,
    hk 1 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.1 q.symm,
    hk 2 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.1 q.symm,
    hk 3 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.1 q.symm,
    hk 4 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.2.1 q.symm,
    hk 5 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.2.2.1 q.symm,
    hk 6 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.1 q.symm,
    hk 7 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.2.1 q.symm,
    hw8,
    hk 11 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.2.2.2 q.symm⟩

/-- The status, the octets the search consumed and the count of those
consumed so far. -/
theorem head_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {n status : Nat} (hst : status < 4)
    (hs : ((s.gpr .a0).setWidth 32).toNat = status) (hn : word s.mem p.up 0 = BitVec.ofNat 64 n) :
    WP isa (.block (low32 .a0 ++ ([ldf .t1 2, .load .d .t1 .t1 0, ldf .t2 8, .add .t2 .t2 .t1,
      stf .t2 8] : List Instr))) s fun t =>
      ((t.gpr .a0 = BitVec.ofNat 64 status ∧ t.gpr .t1 = BitVec.ofNat 64 n ∧
        t.mem = writeFrame s.mem p.F [(8, BitVec.ofNat 64 used + BitVec.ofNat 64 n)]) ∧
      KeepS [.a0, .t1, .t2] s t) ∧ t.syms = s.syms := by
  have hl := h.frame_ld
  have hsf := h.frame_st
  have hu := h.usedScr
  have h2 := h.slot (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := h.slot (j := 8) (v := BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h2 h8
  have hlu : InRegions (s.rd ++ s.wr) (p.up + BitVec.ofNat 64 0) 8 := hu.ld (d := 0) (n := 8) (by decide)
  have hau : (p.up + BitVec.ofNat 64 0).toNat % 8 = 0 := hu.al8 (d := 0) (by decide) (by decide)
  have hn' : s.mem.readW (p.up + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 n := by
    simpa only [Bignum.word, off] using hn
  have h0 : s.gpr .a0 <<< 32 >>> 32 = BitVec.ofNat 64 status := low32_of hs (by omega)
  refine WP.keepS [.a0, .t1, .t2] ?_ (by decide +kernel)
  unfold writeFrame low32
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hl 16 (by decide), hl 64 (by decide), h.frame_al (d := 16) (by decide) (by decide),
    h.frame_al (d := 64) (by decide) (by decide), hlu, hau, h2, h8, hn', hsf 64 (by decide), h0, off]

/-! ## Stores to the state and the frame -/

/-- The state's words `0`, `4` and `5` and the frame's status or region to
zero stored. -/
def StateStores (sv fv : List (Nat × BitVec 64)) : Prop :=
  (∀ e ∈ sv, e.1 = 0 ∨ e.1 = 4 ∨ e.1 = 5) ∧ (∀ e ∈ fv, e.1 = 10 ∨ e.1 = 12 ∨ e.1 = 13)

/-- What stores to the state's first six words and to the frame keep: the
memory outside them. -/
theorem stores_frame (p : GenPublic) (m : Mem)
    {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame (writeFrame m p.stp sv) p.F fv) := by
  have h1 : Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame m p.stp sv) :=
    (writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  have h2 : Frame [⟨p.stp, 48⟩, p.frame] (writeFrame m p.stp sv) (writeFrame (writeFrame m p.stp sv) p.F fv) :=
    (writeFrame_frame14 _ _ fv fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide).sub
      fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp, fun _ h => h⟩
  exact h1.trans h2

theorem GenFrame.stores_changes {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    ∀ r ∈ [(⟨p.stp, 48⟩ : Region), p.frame], ∃ q ∈ GenInput.changes original, Region.Sub r q := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨inState original, by simp [GenInput.changes, inWrites], by
      rw [h.state_region]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩

/-- A region apart from the state's first six words and the frame is kept. -/
theorem stores_bytes (p : GenPublic) (m : Mem)
    {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) {R : Region} (hs : (⟨p.stp, 48⟩ : Region).Disjoint R)
    (hf : p.frame.Disjoint R) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame m p.stp sv) p.F fv) R.base R.len =
      Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine (stores_frame p m hv).bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  exacts [hs.symm, hf.symm]

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through stores to the state's words `0`, `4` and `5` and to the frame's
status or region to zero, for the progress `st'` those words hold. -/
theorem setState (h : GenFrame p original used st s) {st' : KeyProgress} {sv fv : List (Nat × BitVec 64)}
    (hv : StateStores sv fv) (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F fv)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64) :
    GenFrame p original used st' t := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hfb14 : ∀ e ∈ fv, e.1 < 14 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hsd := h.state_frame
  have hnst : p.stp.toNat + 56 ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inState original) (by simp [inWrites])
    rwa [h.state_region] at this
  have hF (j : Nat) (hj : j < 14) (hnot : ∀ e ∈ fv, j ≠ e.1) :
      word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [hm, writeFrame_word _ _ _ hfb j (by omega), frameValue_unchanged _ _ _ hnot]
    refine (writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).readW (r := p.frame)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => ?_) (by decide)
    obtain rfl := List.mem_singleton.mp hq
    exact hsd.sub_right (Region.sub_prefix (by decide))
  have hS (j : Nat) (hj : j < 7) :
      word t.mem p.stp (8 * j) = frameValue sv j (word s.mem p.stp (8 * j)) := by
    rw [hm, ← writeFrame_word _ _ _ hsb j (by omega)]
    exact (writeFrame_frame14 _ _ fv hfb14).readW (r := ⟨p.stp, 56⟩)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact hsd.symm) (by decide)
  have hnf : ∀ j, j ≠ 10 → j ≠ 12 → j ≠ 13 → ∀ e ∈ fv, j ≠ e.1 := fun j h10 h12 h13 e he heq => by
    rcases hv.2 e he with h | h | h <;> omega
  have hns : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 5 → ∀ e ∈ sv, j ≠ e.1 := fun j h0 h4 h5 e he heq => by
    rcases hv.1 e he with h | h | h <;> omega
  have hfr : Frame (GenInput.changes original) s.mem t.mem := by
    rw [hm]; exact (stores_frame p s.mem hv).sub h.stores_changes
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .s0 (by decide)).trans h.s0, fun reg hreg hne => (hg reg hreg).trans (h.saved reg hreg hne),
    hy.trans h.syms, ?_, ?_, h.tab.trans hfr, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hrem, hlt⟩⟩
  · exact (hF 9 (by decide) (hnf 9 (by decide) (by decide) (by decide))).trans h.savedS0
  · exact (h.input.random_frame hfr).trans h.random
  · intro e he
    have hj := GenPublic.headers_bound _ _ e he
    rw [hF e.1 hj (hnf _ ?_ ?_ ?_)]
    · exact h.headers e he
    all_goals
      simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · have := hS 0 (by decide); rw [h0] at this; exact this
  · have := hS 1 (by decide)
    rw [frameValue_unchanged _ _ _ (hns 1 (by decide) (by decide) (by decide))] at this
    exact this.trans h.state.len
  · have := hS 2 (by decide)
    rw [frameValue_unchanged _ _ _ (hns 2 (by decide) (by decide) (by decide))] at this
    exact this.trans h.state.cap
  · have := hS 4 (by decide); rw [h4] at this; exact this
  · have := hS 5 (by decide); rw [h5] at this; exact this
  · rw [← h.state.e, hm]
    refine stores_bytes p s.mem (R := ⟨p.stp + 48, 8⟩) hv ?_ ?_ (by show 8 ≤ 2 ^ 64; decide)
    · intro x hx hy
      exact Offset.sep p.stp (d := 0) (n := 48) (e := 48) (k := 8) (.inl (by omega)) (by omega) (by omega) x
        (by rw [BitVec.add_zero]; simp only [Region.Contains] at hx; omega)
        (by
          have e48 : (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 := rfl
          simp only [Region.Contains, e48] at hy; omega)
    · exact hsd.sub_right (Offset.sub_base _ (by decide))

/-- A frame through a step that changes no memory and keeps the regions and
the callee-saved registers. -/
theorem keep (h : GenFrame p original used st s) (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hsp : t.sp = s.sp) (hy : t.syms = s.syms) (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r) :
    GenFrame p original used st t := by
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .s0 (by decide)).trans h.s0, fun reg hreg hne => (hg reg hreg).trans (h.saved reg hreg hne),
    hy.trans h.syms, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedS0, h.random, h.tab, h.headers, h.state]

/-- A frame through a block that keeps the callee-saved registers. -/
theorem keepK (h : GenFrame p original used st s) {rs : List Reg} (k : KeepS rs s t) (hm : t.mem = s.mem)
    (hy : t.syms = s.syms) (hrs : ∀ r ∈ preserved, r ∉ rs) : GenFrame p original used st t :=
  h.keep hm k.rd k.wr k.sp hy fun r hr => k.gpr r (hrs r hr)

end GenFrame

/-! ## The blocks -/

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

/-- The next prime's search, in `phase`: all its counted candidates, and the
status that goes on. -/
theorem nextPrime_ok (h : GenFrame p original used st s) {phase : Nat} (hph : phase < 2) :
    WP isa (.block (nextPrime phase)) s fun t =>
      (t.mem = writeFrame (writeFrame s.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
        (4, BitVec.ofNat 64 phase)]) p.F [(10, BitVec.ofNat 64 4)] ∧ KeepS [.t1, .t2] s t) ∧
        t.syms = s.syms := by
  have hl := h.frame_ld
  have hsf := h.frame_st
  have sst := h.stateScr
  have h7 := h.slot (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.slot (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7 h11
  have hs0 : InRegions s.wr (p.stp + BitVec.ofNat 64 0) 8 := sst.st (d := 0) (n := 8) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (n := 8) (by decide)
  have ha0 : (p.stp + BitVec.ofNat 64 0).toNat % 8 = 0 := sst.al8 (d := 0) (by decide) (by decide)
  have ha4 : (p.stp + BitVec.ofNat 64 32).toNat % 8 = 0 := sst.al8 (d := 32) (by decide) (by decide)
  rcases (by omega : phase = 0 ∨ phase = 1) with rfl | rfl <;>
  refine WP.keepS [.t1, .t2] ?_ (by decide +kernel) <;>
  unfold writeFrame nextPrime <;>
  simp only [List.foldl_cons, List.foldl_nil] <;>
  brun [ldf, stf, h.s0, hl 56 (by decide), hl 88 (by decide), h.frame_al (d := 56) (by decide) (by decide),
    h.frame_al (d := 88) (by decide) (by decide), h.frame_al (d := 80) (by decide) (by decide), h7, h11, hs0, hs4,
    ha0, ha4, hsf 80 (by decide), exec_li, off]

/-- The end of the key search with `status`: no phase or generations left. -/
theorem finishWith_ok (h : GenFrame p original used st s) {status : Nat} (hs : status < 4) :
    WP isa (.block (finishWith status)) s fun t =>
      (t.mem = writeFrame (writeFrame s.mem p.stp [(4, BitVec.ofNat 64 0), (5, BitVec.ofNat 64 0)]) p.F
        [(10, BitVec.ofNat 64 status)] ∧ KeepS [.t1, .t2] s t) ∧ t.syms = s.syms := by
  have hl := h.frame_ld
  have hsf := h.frame_st
  have sst := h.stateScr
  have h7 := h.slot (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (n := 8) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (n := 8) (by decide)
  have ha4 : (p.stp + BitVec.ofNat 64 32).toNat % 8 = 0 := sst.al8 (d := 32) (by decide) (by decide)
  have ha5 : (p.stp + BitVec.ofNat 64 40).toNat % 8 = 0 := sst.al8 (d := 40) (by decide) (by decide)
  rcases (by omega : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3) with rfl | rfl | rfl | rfl <;>
  refine WP.keepS [.t1, .t2] ?_ (by decide +kernel) <;>
  unfold writeFrame finishWith <;>
  simp only [List.foldl_cons, List.foldl_nil] <;>
  brun [ldf, stf, h.s0, hl 56 (by decide), h.frame_al (d := 56) (by decide) (by decide),
    h.frame_al (d := 80) (by decide) (by decide), h7, hs4, hs5, ha4, ha5, hsf 80 (by decide), exec_li, off]

/-- The status, stored. -/
theorem storeStatus_ok (h : GenFrame p original used st s) {status : Nat}
    (hs : s.gpr .a0 = BitVec.ofNat 64 status) :
    WP isa (.block [stf .a0 10]) s fun t =>
      (t.mem = writeFrame (writeFrame s.mem p.stp []) p.F [(10, BitVec.ofNat 64 status)] ∧ KeepS [] s t) ∧
        t.syms = s.syms := by
  have hsf := h.frame_st
  refine WP.keepS [] ?_ (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, hsf 80 (by decide), h.frame_al (d := 80) (by decide) (by decide), hs, off]

theorem half_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 1 == 0) = decide (n ≤ 1) := by
  have e : (BitVec.ofNat 64 n >>> 1).toNat = n / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have z : (0 : BitVec 64).toNat = 0 := rfl
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [e, z] at this
    omega
  · intro hle
    apply BitVec.eq_of_toNat_eq
    rw [e, z]
    omega

/-- The generations left, halved: zero exactly for the last. -/
theorem left_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .t2 7, .load .d .t1 .t2 40, .shift .srl .d .a7 .t1 1]) s fun t =>
      ((isa.eval (.zero .a7) t = some (decide (st.left ≤ 1)) ∧ t.gpr .t2 = p.stp ∧
        t.gpr .t1 = BitVec.ofNat 64 st.left ∧ t.mem = s.mem) ∧ KeepS [.a7, .t1, .t2] s t) ∧
        t.syms = s.syms := by
  have hl := h.frame_ld
  have sst := h.stateScr
  have h7 := h.slot (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  have hl5 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 40) 8 := sst.ld (d := 40) (n := 8) (by decide)
  have h5 : s.mem.readW (p.stp + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 st.left := h.state.left
  have hb := half_beq_zero h.state.left_lt
  have ha5 : (p.stp + BitVec.ofNat 64 40).toNat % 8 = 0 := sst.al8 (d := 40) (by decide) (by decide)
  refine WP.keepS [.a7, .t1, .t2] ?_ (by decide +kernel)
  brun [ldf, h.s0, hl 56 (by decide), h.frame_al (d := 56) (by decide) (by decide), hl5, ha5, h7, h5, off]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hb]

/-- The phase, tested. -/
theorem phase_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .t2 7, .load .d .t1 .t2 32]) s fun t =>
      ((isa.eval (.zero .t1) t = some (decide (phaseWord st.phase = 0)) ∧ t.gpr .t2 = p.stp ∧
        t.mem = s.mem) ∧ KeepS [.t1, .t2] s t) ∧ t.syms = s.syms := by
  have hl := h.frame_ld
  have sst := h.stateScr
  have h7 := h.slot (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  have hl4 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 32) 8 := sst.ld (d := 32) (n := 8) (by decide)
  have h4 : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) := h.state.phase
  have hz := ofNat_beq_zero (k := phaseWord st.phase) (by have := phaseWord_le st.phase; omega)
  have ha4 : (p.stp + BitVec.ofNat 64 32).toNat % 8 = 0 := sst.al8 (d := 32) (by decide) (by decide)
  refine WP.keepS [.t1, .t2] ?_ (by decide +kernel)
  brun [ldf, h.s0, hl 56 (by decide), h.frame_al (d := 56) (by decide) (by decide), hl4, ha4, h7, h4, off]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hz]

end

end VG.Proof.RsaKeyGen.RISCV64.Generate
