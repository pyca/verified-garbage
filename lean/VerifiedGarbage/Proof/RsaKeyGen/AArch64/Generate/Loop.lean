module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Generate
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Verified
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! # The controller's loop (AArch64)

Its public data, frame and entry; the prime search's call and run; the
blocks after a search; the key's call and run; how a step ends; and the
loop. One module: each part is the next's only importer.
-/

@[expose] public section

/-! ## The controller's public data, its frame, its loop states and its entry (AArch64)

As on x86-64 (`Proof/RsaKeyGen/X86_64/Generate/Classify.lean`): `GenPublic` is
everything two constant-time runs share: the arguments, the primes' octets
and the exponent. The controller keeps its working state in a frame of 20
words at `sp - 160` (`GenPublic.F`), with its base in `x19`; the rest runs
below it, in the frame saving `x30`. A loop state (`GenLive`) is at an offset
into the tape with the search's progress in the state and the key's buffer.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
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

/-- The frame's base. -/
abbrev GenPublic.F (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 160

/-- The frame's region. -/
abbrev GenPublic.frame (p : GenPublic) : Region := ⟨p.F, 160⟩

/-- The frame's words while the search goes on (but the status, and the
region to zero). -/
def GenPublic.headers (p : GenPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, p.kp), (1, BitVec.ofNat 64 p.L), (2, p.up), (3, p.rp), (4, BitVec.ofNat 64 p.randLen), (5, p.B),
    (6, BitVec.ofNat 64 (p.Z / 8)), (7, p.stp), (8, BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (limitOf p.L p.eB))]

theorem GenPublic.headers_bound (p : GenPublic) (used : Nat) : ∀ e ∈ p.headers used, e.1 < 20 := by
  simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

def genOfState (s : State) : GenPublic where
  kp := s.gpr .x0
  up := s.gpr .x2
  rp := s.gpr .x3
  B := s.gpr .x5
  stp := s.gpr .x7
  sp := s.sp
  L := genLen s
  randLen := (s.gpr .x4).toNat
  Z := (s.gpr .x6).toNat * 8
  eB := genE s

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

/-- A state of the controller in the frame saving `x30`: `used` octets
consumed, the progress `st` in the state. The entry state is
functional-proof data only: its callee-saved registers may hold secrets, and
its tape and key buffer are secret. -/
structure GenFrame (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop where
  input : GenInput p original
  used_le : used ≤ p.randLen
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  sp : s.sp = p.F - 16
  x19 : s.gpr .x19 = p.F
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.F 72 = original.gpr .x19
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = genRand original
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

/-! ### Whether the exponent is 3 -/

/-- Equality of all eight bytes is equality of words. -/
theorem eq_of_bytes {x y : BitVec 64}
    (h : ∀ j < 8, x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  ext i hi
  have e := congrArg (fun v : Byte => v.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and] at e
  rw [show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

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
    apply eq_of_bytes
    intro j hj
    rw [hb j hj, hc j hj]
    by_cases h : j = 7
    · subst h; rw [ite_eq_left rfl]; exact h7
    · rw [ite_eq_right h]
      exact h0 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)

/-! ### Where the buffers are -/

namespace GenInput

variable {p : GenPublic} {s : State}

theorem nowrap (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.1 r hr

theorem write_disjoint (h : GenInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (below s.sp stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : GenInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.1

theorem sp_eq (h : GenInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem room (h : GenInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.1

theorem F_toNat (h : GenInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 416 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [GenPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : GenInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  refine Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) ?_
  have := h.F_toNat
  have : 416 ≤ p.sp.toNat := h.room
  have := p.sp.isLt
  omega

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

/-- The frame is in the stack the controller may use. -/
theorem frame_sub (h : GenInput p s) : Region.Sub p.frame (below s.sp stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

theorem frame_disjoint_writes (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s) : p.frame.Disjoint r :=
  fun x hx hy => (h.stack_disjoint (List.mem_append_left _ hr)) x (h.frame_sub x hx) hy

end GenInput

/-! ### The entry's stores -/

open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld mov movi)

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem exec_movz3 {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 3) s = some (s.write .x d (imm.setWidth 64 <<< 48)) := by
  simp only [exec, Size.bits, show 16 * 3 < 64 from by decide, ite_true]

theorem three56 : (BitVec.ofNat 16 0x300).setWidth 64 <<< 48 = (0x0300000000000000 : BitVec 64) := by decide

/-- The counted candidates of a prime's search, from the primes' octets `w`
and the exponent's word `ew`. -/
def limitBV (w ew : BitVec 64) : BitVec 64 :=
  if ew = 0x0300000000000000 then w <<< 6 else w <<< 3 + w <<< 5

/-- The frame's words on entry, in the order the entry stores them. -/
def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(9, s.gpr .x19), (0, s.gpr .x0), (2, s.gpr .x2), (3, s.gpr .x3), (4, s.gpr .x4), (5, s.gpr .x5),
    (6, s.gpr .x6), (7, s.gpr .x7), (1, s.mem.readW (s.gpr .x7 + 8) 64), (8, 0),
    (11, limitBV (s.mem.readW (s.gpr .x7 + 8) 64) (s.mem.readW (s.gpr .x7 + 48) 64))]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem alloc_wr {p : GenPublic} {s : State} (h : GenInput p s) :
    (allocated 160 s).wr = p.frame :: s.wr := by
  show _ = (⟨p.sp - _, 160⟩ : Region) :: s.wr
  rw [h.sp_eq]; rfl

theorem alloc_sp {p : GenPublic} {s : State} (h : GenInput p s) : (allocated 160 s).sp = p.F := by
  show _ = p.sp - _
  rw [h.sp_eq]; rfl

theorem subs0_carry (x : BitVec 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 0).toNat + (~~~x).toNat + (true).toNat) = decide (x = 0) := by
  have hx := x.isLt
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  · rintro rfl
    rw [show (0 : BitVec 64).toNat = 0 from rfl]

theorem entry_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block entry) (allocated 160 s) fun t =>
      (t.gpr .x19 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s)) ∧
      Keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] (allocated 160 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 160 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 160 s).wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hsp := alloc_sp h
  have hst (d : Nat) (hd : d + 8 ≤ 56) :
      InRegions ((allocated 160 s).rd ++ (allocated 160 s).wr) (s.gpr .x7 + BitVec.ofNat 64 d) 8 := by
    refine ⟨inState s, ?_, Offset.contains_base _ hd (by omega)⟩
    rw [alloc_wr h, h.1.2.2.1]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
  have hmem : (allocated 160 s).mem = s.mem := rfl
  refine WP.keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] ?_ (by decide) (by decide)
    (by decide +kernel)
  have hw8 := hst 8 (by decide)
  have hw48 := hst 48 (by decide)
  unfold entry writeFrame entryValues limitBV
  simp only [List.foldl_cons, List.foldl_nil]
  have hag : ∀ r, (allocated 160 s).gpr r = s.gpr r := fun _ => rfl
  by_cases he : s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 48) 64 = 0x0300000000000000 <;>
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), exec_movz3, three56, imm64 (show 0 < 65536 by decide),
    hsp, hmem, hag, hw8, hw48, subs0_carry, BitVec.xor_eq_zero_iff, he, hs0, hs 0 (by decide), hs 8 (by decide),
    hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 88 (by decide), BitVec.add_zero]
  all_goals simp only [off, BitVec.ofNat_eq_ofNat, Nat.reduceMul] at he ⊢
  · rw [ite_eq_left he]
  · rw [ite_eq_right (by rw [decide_eq_true_iff, BitVec.xor_eq_zero_iff]; exact he), ite_eq_right he]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

namespace GenInput

variable {p : GenPublic} {s : State}

theorem frame_state (h : GenInput p s) : p.frame.Disjoint ⟨p.stp, 56⟩ := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  rw [← hst]; exact h.frame_disjoint_writes (by simp [inWrites])

theorem state_nowrap (h : GenInput p s) : p.stp.toNat + 56 ≤ 2 ^ 64 := by
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  rw [hst] at hn
  exact hn

/-- The state's words through changes disjoint from it. -/
theorem state_words {m m' : Mem} {R : List Region} (hf : Frame R m m') (hd : ∀ r ∈ R, Region.Disjoint ⟨p.stp, 56⟩ r)
    (d : Nat) (hd' : d + 8 ≤ 56) :
    m'.readW (p.stp + BitVec.ofNat 64 d) 64 = m.readW (p.stp + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd' (by omega)) hd (by decide)

theorem state_bytes {m m' : Mem} {R : List Region} (hf : Frame R m m')
    (hd : ∀ r ∈ R, Region.Disjoint ⟨p.stp, 56⟩ r) :
    Spec.Rsa.bytesAt m' (p.stp + 48) 8 = Spec.Rsa.bytesAt m (p.stp + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hsub : Region.Sub ⟨p.stp + 48, 8⟩ ⟨p.stp, 56⟩ := by
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]
    exact Offset.sub_base _ (by decide)
  exact hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => (hd r hr).sub_left hsub) (by show 8 ≤ 2 ^ 64; decide) hi

/-- The state through stores to the frame. -/
theorem stateOk_frame (h : GenInput p s) {m m' : Mem} (hf : Frame [p.frame] m m') {st : KeyProgress}
    (hs : StateOk p st m) : StateOk p st m' := by
  have hd : ∀ r ∈ [p.frame], Region.Disjoint ⟨p.stp, 56⟩ r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact h.frame_state.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs.remaining_le, hs.left_lt⟩
  · change m'.readW (p.stp + BitVec.ofNat 64 0) 64 = _
    rw [state_words hf hd 0 (by decide)]; exact hs.remaining
  · change m'.readW (p.stp + BitVec.ofNat 64 8) 64 = _
    rw [state_words hf hd 8 (by decide)]; exact hs.len
  · change m'.readW (p.stp + BitVec.ofNat 64 16) 64 = _
    rw [state_words hf hd 16 (by decide)]; exact hs.cap
  · change m'.readW (p.stp + BitVec.ofNat 64 32) 64 = _
    rw [state_words hf hd 32 (by decide)]; exact hs.phase
  · change m'.readW (p.stp + BitVec.ofNat 64 40) 64 = _
    rw [state_words hf hd 40 (by decide)]; exact hs.left
  · rw [state_bytes hf hd]; exact hs.e

/-- The state through stores to the frame, then a store below it. -/
theorem stateOk_frame' (h : GenInput p s) {m m' m'' : Mem} {R : Region} (hf : Frame [p.frame] m m')
    (hf' : Frame [R] m' m'') (hd : ∀ r ∈ [R], Region.Disjoint ⟨p.stp, 56⟩ r) {st : KeyProgress}
    (hs : StateOk p st m) : StateOk p st m'' := by
  have hs' := h.stateOk_frame hf hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs'.remaining_le, hs'.left_lt⟩
  · change m''.readW (p.stp + BitVec.ofNat 64 0) 64 = _
    rw [state_words hf' hd 0 (by decide)]; exact hs'.remaining
  · change m''.readW (p.stp + BitVec.ofNat 64 8) 64 = _
    rw [state_words hf' hd 8 (by decide)]; exact hs'.len
  · change m''.readW (p.stp + BitVec.ofNat 64 16) 64 = _
    rw [state_words hf' hd 16 (by decide)]; exact hs'.cap
  · change m''.readW (p.stp + BitVec.ofNat 64 32) 64 = _
    rw [state_words hf' hd 32 (by decide)]; exact hs'.phase
  · change m''.readW (p.stp + BitVec.ofNat 64 40) 64 = _
    rw [state_words hf' hd 40 (by decide)]; exact hs'.left
  · rw [state_bytes hf' hd]; exact hs'.e

end GenInput

/-- The state's words for the progress on entry. -/
theorem stateOk_entry {p : GenPublic} {s : State} (h : GenInput p s) :
    StateOk p (genProgress s) s.mem := by
  have hpre := h.1
  obtain ⟨-, -, -, -, -, -, -, hL, -, -, hrem, hcap, hph, -⟩ := hpre
  have hstp : p.stp = s.gpr .x7 := by rw [← h.2]; rfl
  have hLp : p.L = genLen s := by rw [← h.2]; rfl
  have heB : p.eB = genE s := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, BitVec.isLt _⟩
  · change s.mem.readW (p.stp + BitVec.ofNat 64 0) 64 = _
    rw [BitVec.add_zero, hstp]; exact (ofNat_toNat64 _).symm
  · change s.mem.readW (p.stp + BitVec.ofNat 64 8) 64 = _
    rw [hLp, hstp, ofNat_toNat64]; rfl
  · change s.mem.readW (p.stp + BitVec.ofNat 64 16) 64 = _
    rw [hLp, hstp]; exact hcap
  · change s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = _
    rw [hstp]
    simp only [genProgress, keyProgressAt]
    have hph' : (s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 32) 64).toNat ≤ 1 := hph
    split
    · rename_i h0
      have h0' : (s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      rw [h0']; rfl
    · rename_i h0
      have h0' : ¬(s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      have : (s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 32) 64).toNat = 1 := by omega
      rw [this]; rfl
  · change s.mem.readW (p.stp + BitVec.ofNat 64 40) 64 = _
    rw [hstp]; exact (ofNat_toNat64 _).symm
  · rw [heB, hstp]
  · rw [hLp, heB]
    exact hrem

/-! ### What the controller's steps keep

The callees and the controller's own stores change only the key's buffer,
`used`, the working space, the state's first four words and the stack below
the frame (`callChanges`); through such changes a loop state keeps its frame,
its tape and the state's last three words.
-/

namespace GenInput

variable {p : GenPublic} {s : State}

/-- What a step may write: the key's buffer, `used`, the working space, the
state's first four words, and the stack below the frame. -/
def callChanges (s : State) : List Region :=
  [inKey s, inUsed s, inScr s, ⟨s.gpr .x7, 32⟩, ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩]

theorem state32_sub (s : State) : Region.Sub ⟨s.gpr .x7, 32⟩ (inState s) := by
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

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (callChanges s) m m') :
    Frame (changes s) m m' := hf.sub (callChanges_sub s)

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
    have hs := Offset.sep_below p.sp 416 (a := 160) (n := 160) (b := 416) (k := 256) (by decide) (by decide)
      (Or.inr (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (by simp only [Region.Contains, GenPublic.F] at hx; omega)
      (by simp only [Region.Contains] at hy; exact hy)

theorem frame_words (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 20) : word m' p.F (8 * j) = word m p.F (8 * j) :=
  hf.readW (r := p.frame) (Offset.contains_base _ (by omega) (by omega)) h.frame_disjoint (by decide)

/-- The state's last three words. -/
abbrev stateTail (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 32, 24⟩

theorem tail_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, (stateTail p).Disjoint r := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hstp : s.gpr .x7 = p.stp := by rw [← h.2]; rfl
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

/-- The push of `x30` writes only below the frame. -/
theorem push_frame (h : GenInput p s) (m : Mem) (v : BitVec 64) :
    Frame (callChanges s) m (m.write (p.F - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩)
    (by simp [callChanges]) _ ?_
  rw [show p.F - 16 = p.sp - BitVec.ofNat 64 176 by rw [GenPublic.F, BitVec.sub_sub]; rfl, h.sp_eq]
  exact Offset.contains_below s.sp (a := 176) (b := 416) (by decide) (by decide) (by decide)

end GenInput

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

/-- The region below the frame the push of `x30` writes in. -/
abbrev belowFrame (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩

/-- The controller's state on leaving its entry, in the frame saving `x30`,
before it clears the key's buffer. -/
theorem gen_start {p : GenPublic} {s t : State} (h : GenInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] (allocated 160 s) t) :
    GenFrame p s 0 (genProgress s) (pushedX30 t) ∧ Frame [p.frame, belowFrame s] s.mem (pushedX30 t).mem := by
  have hb := entryValues_bound s
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame s.mem p.F _ hb
  have hpush : Frame [belowFrame s] t.mem (pushedX30 t).mem := by
    refine Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
    rw [htsp, show p.F - 16 = p.sp - BitVec.ofNat 64 176 by rw [GenPublic.F, BitVec.sub_sub]; rfl, h.sp_eq]
    exact Offset.contains_below s.sp (a := 176) (b := 416) (by decide) (by decide) (by decide)
  have hp : Frame (GenInput.callChanges s) t.mem (pushedX30 t).mem :=
    hpush.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp [GenInput.callChanges], fun _ h => h⟩
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hdf : ∀ r ∈ [p.frame], Region.Disjoint ⟨p.stp, 56⟩ r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact h.frame_state.symm
  have hdb : ∀ r ∈ [belowFrame s], Region.Disjoint ⟨p.stp, 56⟩ r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    rw [← hst]
    exact fun x hx hy => (h.stack_disjoint (r := inState s) (by simp [inWrites])) x
      (Region.sub_prefix (base := s.sp - BitVec.ofNat 64 stackUse) (by decide) x hy) hx
  have hc (j : Nat) (hj : j < 20) : word (pushedX30 t).mem p.F (8 * j) = word t.mem p.F (8 * j) :=
    h.frame_words hp j hj
  have hw (j : Nat) (hj : j < 20) :
      word (pushedX30 t).mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm]; exact writeFrame_word _ _ _ hb j hj
  have hL : p.L ≤ 512 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.1.2.1
  have hall : Frame [p.frame, belowFrame s] s.mem (pushedX30 t).mem :=
    (hfr.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (hpush.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩)
  have hch : Frame (GenInput.changes s) s.mem (pushedX30 t).mem := by
    refine hall.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [GenInput.changes], h.frame_sub⟩
    · exact ⟨below s.sp stackUse, by simp [GenInput.changes], Region.sub_prefix (by decide)⟩
  refine ⟨⟨h, Nat.zero_le _, k.rd, k.wr.trans (alloc_wr h), ?_, hx, fun r hr h19 h30 => ?_, k.vcs, ?_, ?_, ?_,
    ?_⟩, hall⟩
  · show t.sp - 16 = p.F - 16
    rw [htsp]
  · exact k.gpr r (by revert r hr h19; decide)
  · rw [show (72 : Nat) = 8 * 9 from rfl, hw 9 (by decide)]
    rfl
  · rw [h.random_frame hch]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (GenPublic.headers_bound _ _ e he)]
    have hLs : genLen s = p.L := by rw [← h.2]; rfl
    have hlim : limitBV (s.mem.readW (s.gpr .x7 + 8) 64) (s.mem.readW (s.gpr .x7 + 48) 64) =
        BitVec.ofNat 64 (limitOf p.L p.eB) := by
      rw [show s.mem.readW (s.gpr .x7 + 8) 64 = BitVec.ofNat 64 p.L by rw [← hLs]; exact (ofNat_toNat64 _).symm]
      unfold limitBV limitOf primeLimit
      rw [SearchInit.shl_ofNat _ 6 (by omega), SearchInit.shl_ofNat _ 3 (by omega),
        SearchInit.shl_ofNat _ 5 (by omega), SearchInit.add_ofNat]
      have he : s.mem.readW (s.gpr .x7 + 48) 64 = 0x0300000000000000 ↔ Spec.Rsa.os2ip p.eB = 3 := by
        rw [word_eq_three]; rw [← h.2]; rfl
      by_cases hh : s.mem.readW (s.gpr .x7 + 48) 64 = 0x0300000000000000
      · rw [ite_eq_left hh, ite_eq_left (he.mp hh)]; congr 1; omega
      · rw [ite_eq_right hh, ite_eq_right (fun h' => hh (he.mpr h'))]; congr 1; omega
    rw [← h.2] at he hlim
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [frameValue, entryValues, List.foldl_cons, List.foldl_nil, genOfState, genLen, ofNat_toNat64, hlim,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl
  · exact h.stateOk_frame' hfr hpush hdb (stateOk_entry h)

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through a step that keeps `x19`, the stack pointer, the regions and the
callee-saved registers, and writes only what a step may, with the state's
first three words for the progress `st'`, whose phase and generations are
`st`'s. -/
theorem restore (h : GenFrame p original used st s) {st' : KeyProgress}
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame (GenInput.callChanges original) s.mem t.mem)
    (h0 : word t.mem p.stp 0 = BitVec.ofNat 64 st'.remaining)
    (h1 : word t.mem p.stp 8 = BitVec.ofNat 64 p.L)
    (h2 : word t.mem p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L))
    (hph : st'.phase = st.phase ∨ phaseWord st'.phase = phaseWord st.phase) (hl : st'.left = st.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) :
    GenFrame p original used st' t := by
  have hc := h.input.frame_words hf
  have hf' := GenInput.frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, hsp.trans h.sp,
    (hg .x19 (by decide) (by decide)).trans h.x19,
    fun r hr h19 h30 => (hg r hr h30).trans (h.saved r hr h19 h30),
    fun r hr => (hv r hr).trans (h.vcs r hr), ?_, ?_, ?_,
    ⟨h0, h1, h2, ?_, ?_, ?_, hrem, by rw [hl]; exact h.state.left_lt⟩⟩
  · exact (hc 9 (by decide)).trans h.savedX19
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (GenPublic.headers_bound _ _ e he)).trans (h.headers e he)
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.phase]
    rcases hph with hph | hph <;> rw [hph]
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.left, hl]
  · rw [h.input.tail_bytes hf, h.state.e]

theorem key_region (h : GenFrame p original used st s) : inKey original = ⟨p.kp, 9 * p.L⟩ := by
  have := h.input.1.2.2.2.2.2.2.2.2.1
  rw [← h.input.2]
  simp only [inKey, genOfState, this]

theorem key_state (h : GenFrame p original used st s) : (inKey original).Disjoint (inState original) := by
  have hpw := h.input.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.1.2.2

/-- Through a step that changes only the key's buffer. -/
theorem restoreKey (h : GenFrame p original used st s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hf : Frame [inKey original] s.mem t.mem) : GenFrame p original used st t := by
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  have hd := h.key_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d :=
    hf.readW (r := inState original) (by rw [hst]; exact Offset.contains_base _ hd' (by omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine h.restore hr hw hsp hg hv (hf.sub fun r hr => ?_) ?_ ?_ ?_ (.inl rfl) rfl h.state.remaining_le
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩
  · rw [hword 0 (by decide)]; exact h.state.remaining
  · rw [hword 8 (by decide)]; exact h.state.len
  · rw [hword 16 (by decide)]; exact h.state.cap

theorem keep (h : GenFrame p original used st s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    GenFrame p original used st t :=
  h.restoreKey kp.rd kp.wr kp.sp (fun reg hr _ => kp.gpr reg (hregs reg hr)) kp.vcs
    (by rw [hm]; exact Frame.refl _ _)

/-- Through stores to the frame but its saved `x19`, with the words for the
octets consumed `u`. -/
theorem store (h : GenFrame p original used st s) {u : Nat} (hu : u ≤ p.randLen)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20) (h9 : ∀ e ∈ values, 9 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values)
    {rs : List Reg} (kp : Keep rs s t) (hregs : ∀ reg ∈ preserved, reg ∉ rs)
    (hh : Slots t.mem p.F (p.headers u)) : GenFrame p original u st t := by
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame s.mem p.F values hb
  have hf : Frame (GenInput.changes original) s.mem t.mem := by
    apply hfr.sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (hregs r hr)
  refine ⟨h.input, hu, kp.rd.trans h.rd, kp.wr.trans h.wr, kp.sp.trans h.sp,
    (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, hh, h.input.stateOk_frame hfr h.state⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 9) = _
    rw [writeFrame_word _ _ _ hb 9 (by decide), frameValue_unchanged _ _ _ h9]
    exact h.savedX19
  · exact (h.input.random_frame hf).trans h.random

/-- The words of the frame's headers, kept through stores of others. -/
theorem slots_kept (h : GenFrame p original used st s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F values) p.F (p.headers used) := by
  intro e he
  have hj := GenPublic.headers_bound _ _ e he
  rw [writeFrame_word _ _ _ hb e.1 hj, frameValue_unchanged _ _ _ ?_]
  · exact h.headers e he
  · intro x hx heq
    have := hnot x hx
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem key_nowrap (h : GenFrame p original used st s) : p.kp.toNat + 9 * p.L ≤ 2 ^ 64 := by
  have := h.input.nowrap (r := inKey original) (by simp [inWrites])
  rw [h.key_region] at this
  exact this

theorem len_valid (h : GenFrame p original used st s) : primeLenValid p.L := by
  rw [← h.input.2]; exact h.input.1.2.2.2.2.2.2.2.1

theorem frame_key (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.kp, 9 * p.L⟩ := by
  rw [← h.key_region]; exact h.input.frame_disjoint_writes (by simp [inWrites])

/-- The frame's words are loadable. -/
theorem frame_ld (h : GenFrame p original used st s) :
    ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem frame_st (h : GenFrame p original used st s) :
    ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 :=
  fun _ hd => (h.input.frame_scr h.wr).st hd

end GenFrame

/-! ### Zeros in the key's buffer

`clear` writes zeros to the region in frame words 12 and 13, which is in the
key's buffer: the frame, the state and everything else is kept.
-/

/-- `clear`: zeros at the region in frame words 12 and 13. -/
theorem clear_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {op : Addr} {len : Nat}
    (h12 : word s.mem p.F (8 * 12) = op) (h13 : word s.mem p.F (8 * 13) = BitVec.ofNat 64 len)
    (hsub : Region.Sub ⟨op, len⟩ (inKey original)) (h1 : 1 ≤ len) (hlt : len < 2 ^ 63) :
    WP isa clear s fun t => GenFrame p original used st t ∧ (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      Frame [⟨op, len⟩] s.mem t.mem ∧ (∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) ∧
      Keep [.x1, .x2, .x3] s t := by
  have hl := h.frame_ld
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13
  have hin : inKey original ∈ s.wr := by
    rw [h.wr, h.input.1.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
  have hout : ∀ i < len, InRegions s.wr (op + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨_, hin, hsub _ (Offset.contains_base _ (by omega) (by omega))⟩
  unfold clear
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl 96 (by decide), hl 104 (by decide), h12, h13])
      (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨hx1, hx2, hx3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := len) (by omega) (by omega) (BInv s₁ op)
    (fun i hi t hI _ => bStep_ok hlt hx3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
    ⟨Keep.refl _ _, hx1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ hx2) fun t hI => ?_
  have kk := k₁.trans hI.keep
  have hframe : Frame [⟨op, len⟩] s.mem t.mem := by
    intro a ha
    rw [hI.frame a ?_, hm₁]
    intro i hi he
    apply ha _ (List.mem_singleton_self _)
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)
  have hkey : Frame [inKey original] s.mem t.mem := by
    refine hframe.sub fun r hr => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, hsub⟩
  have hfw : ∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    intro j hj
    exact h.input.frame_words (hkey.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩) j hj
  exact ⟨h.restoreKey kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs hkey,
    hI.bytes, hframe, hfw, kk.mono (by decide)⟩

/-! ### The key's buffer but `p` -/

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

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem setLow_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .x9 0, ldf .x10 1, stf .x9 12, .lsl .x .x10 .x10 2, stf .x10 13]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 2)] ∧ Keep [.x9, .x10] s t := by
  have hl := h.frame_ld
  have hs := h.frame_st
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h0 h1
  refine WP.keep [.x9, .x10] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, hl 0 (by decide), hl 8 (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

theorem setHigh_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .x10 1, .lsl .x .x11 .x10 2, .add .x .x11 .x11 .x10, ldf .x9 0, .add .x .x9 .x9 .x11,
      stf .x9 12, .lsl .x .x10 .x10 2, stf .x10 13]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp + (BitVec.ofNat 64 p.L <<< 2 + BitVec.ofNat 64 p.L)),
        (13, BitVec.ofNat 64 p.L <<< 2)] ∧ Keep [.x9, .x10, .x11] s t := by
  have hl := h.frame_ld
  have hs := h.frame_st
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h0 h1
  refine WP.keep [.x9, .x10, .x11] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, hl 0 (by decide), hl 8 (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

theorem store_region (h : GenFrame p original used st s) {t : State} {a b : BitVec 64}
    (hm : t.mem = writeFrame s.mem p.F [(12, a), (13, b)]) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ preserved, r ∉ rs) :
    GenFrame p original used st t ∧ word t.mem p.F (8 * 12) = a ∧ word t.mem p.F (8 * 13) = b ∧
      Frame [p.frame] s.mem t.mem := by
  have hb : ∀ e ∈ [(12, a), (13, b)], e.1 < 20 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.store h.used_le _ hb (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide)
    hm k hrs (by
      rw [hm]; exact h.slots_kept _ hb (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide)), ?_, ?_, ?_⟩
  · rw [hm, writeFrame_word _ _ _ hb 12 (by decide)]; rfl
  · rw [hm, writeFrame_word _ _ _ hb 13 (by decide)]; rfl
  · rw [hm]; exact writeFrame_frame s.mem p.F _ hb

end

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
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h5 : p.kp + (BitVec.ofNat 64 p.L <<< 2 + BitVec.ofNat 64 p.L) = p.slot 5 := by
    rw [h4, SearchInit.add_ofNat]; congr 2; omega
  unfold clearAround
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (setLow_ok h) fun t1 ⟨hm1, k1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 (by decide)
  rw [h4] at w13
  refine WP.seq (WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega))
    (by omega) (by omega)) fun t2 ⟨g2, z2, f2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (setHigh_ok g2) fun t3 ⟨hm3, k3⟩ => ?_)
  obtain ⟨g3, w12', w13', f3⟩ := store_region g2 hm3 k3 (by decide)
  rw [h4] at w13'
  rw [h5] at w12'
  refine WP.mono (clear_ok g3 w12' w13' (by rw [hkr]; exact slot_sub _ (by omega)) (by omega) (by omega))
    fun t4 ⟨g4, z4, f4, _, _⟩ => ?_
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

end VG.Proof.RsaKeyGen.AArch64.Generate

/-! ## The prime search's call and run (AArch64)

For the search of the progress' prime: `out` is `p`'s slot for `p`, `q`'s for
`q`; `p` is `p`'s slot, of `p_len` octets for `q` and none for `p`; `e` the
state's last word; the tape after the octets consumed. Its four stack
arguments in the call's frame of 32 bytes below the frame saving `x30`, at
`sp - 208` for the controller's stack pointer on entry; the search's own
frames below that. It leaves the search's status, its prime or zeros at its
output, the octets it consumed at `used`, and its counted candidates left
and request in the state; it writes nothing else but the working space and
the stack.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld mov movi)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)

/-- The search's output: `p`'s slot for `p`, `q`'s for `q`. -/
def outOf (p : GenPublic) (st : KeyProgress) : Addr := if phaseWord st.phase = 0 then p.slot 4 else p.slot 5

/-- The other prime's length: none for `p`. -/
def plenOf (p : GenPublic) (st : KeyProgress) : Nat := if phaseWord st.phase = 0 then 0 else p.L

/-- The stack pointer in the search's call frame. -/
abbrev callSp (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 208

theorem callSp_eq (p : GenPublic) : p.F - 16 - BitVec.ofNat 64 32 = callSp p := by
  rw [GenPublic.F, BitVec.sub_sub, BitVec.sub_sub]; rfl

/-- The search's stack arguments. -/
def callValues (p : GenPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (p.randLen - used)), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8)), (3, p.stp)]

/-- The search's arguments in registers. -/
def SearchRegs (p : GenPublic) (used : Nat) (st : KeyProgress) (s : State) : Prop :=
  s.gpr .x0 = outOf p st ∧ s.gpr .x1 = BitVec.ofNat 64 p.L ∧ s.gpr .x2 = p.up ∧
    s.gpr .x3 = p.stp + BitVec.ofNat 64 48 ∧ s.gpr .x4 = BitVec.ofNat 64 8 ∧ s.gpr .x5 = p.slot 4 ∧
    s.gpr .x6 = BitVec.ofNat 64 (plenOf p st) ∧ s.gpr .x7 = p.rp + BitVec.ofNat 64 used

theorem phaseWord_le (ph : KeyPhase) : phaseWord ph ≤ 1 := by cases ph <;> simp only [phaseWord] <;> omega

/-- The registers the search's arguments' block writes. -/
abbrev searchArgRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem GenFrame.state_ld {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {t : State} {k : Nat}
    (hw : t.wr = (allocated k s).wr) :
    ∀ d, d + 8 ≤ 56 → InRegions (t.rd ++ t.wr) (p.stp + BitVec.ofNat 64 d) 8 := by
  intro d hd
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  refine ⟨inState original, List.mem_append_right _ ?_, by rw [hst]; exact Offset.contains_base _ hd (by omega)⟩
  rw [hw]
  exact List.mem_cons_of_mem _ (by rw [h.wr, h.input.1.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites]))

theorem GenFrame.frame_ld' {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {t : State} {k : Nat} (hw : t.wr = (allocated k s).wr) :
    ∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

theorem alloc32_sp {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : (allocated 32 s).sp = callSp p := by
  show s.sp - _ = _
  rw [h.sp, callSp_eq]

theorem search_args_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block searchArgs) (allocated 32 s) fun t =>
      (SearchRegs p used st t ∧ t.mem = writeFrame s.mem (callSp p) (callValues p used)) ∧
      Keep searchArgRegs (allocated 32 s) t := by
  have hl := h.frame_ld' (t := allocated 32 s) rfl
  have hsl := h.state_ld (t := allocated 32 s) rfl
  have hsp := alloc32_sp h
  have haw : (allocated 32 s).wr = ⟨callSp p, 32⟩ :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ : Region) :: s.wr = _
    rw [h.sp, callSp_eq]
  have hw : ∀ d, d + 8 ≤ 32 → InRegions (allocated 32 s).wr (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 32⟩, by rw [haw]; exact List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  have hw0 : InRegions (allocated 32 s).wr (callSp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used) :
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv0 := hv 0 p.kp (by simp [GenPublic.headers])
  have hv1 := hv 1 (BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv2 := hv 2 p.up (by simp [GenPublic.headers])
  have hv3 := hv 3 p.rp (by simp [GenPublic.headers])
  have hv4 := hv 4 (BitVec.ofNat 64 p.randLen) (by simp [GenPublic.headers])
  have hv5 := hv 5 p.B (by simp [GenPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := hv 7 p.stp (by simp [GenPublic.headers])
  have hv8 := hv 8 (BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8
  have hph : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) :=
    h.state.phase
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have hul := h.used_le
  have hrl : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hsub : BitVec.ofNat 64 p.randLen - BitVec.ofNat 64 used = BitVec.ofNat 64 (p.randLen - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl,
      Nat.mod_eq_of_lt (by omega : used < 2 ^ 64)]
    omega
  have h4 : BitVec.ofNat 64 p.L <<< 2 + p.kp = p.slot 4 := by
    rw [SearchInit.shl_ofNat _ _ (by omega), BitVec.add_comm]; congr 2; omega
  have h5 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  have hmem : (allocated 32 s).mem = s.mem := rfl
  have hx19 : (allocated 32 s).gpr .x19 = p.F := h.x19
  refine WP.keep searchArgRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold searchArgs SearchRegs writeFrame callValues outOf plenOf
  simp only [List.foldl_cons, List.foldl_nil]
  have hph1 := phaseWord_le st.phase
  rcases (by omega : phaseWord st.phase = 0 ∨ phaseWord st.phase = 1) with hp | hp <;>
  rw [hp] at hph <;>
  brun [ldf, hsp, hmem, hx19, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide),
    imm64 (show 8 < 65536 by decide), subs0_carry, hl 0 (by decide), hl 8 (by decide), hl 16 (by decide),
    hl 24 (by decide), hl 32 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hl 64 (by decide), hsl 32 (by decide), hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hph, hsub, h4, h5, hp,
    hw0, hw 0 (by decide), hw 8 (by decide), hw 16 (by decide), hw 24 (by decide)]
  all_goals simp only [off, Nat.mul_zero, BitVec.add_zero]

/-! ### The search's regions -/

abbrev rO (p : GenPublic) (st : KeyProgress) : Region := ⟨outOf p st, p.L⟩
abbrev rU (p : GenPublic) : Region := ⟨p.up, 8⟩
abbrev rE (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 48, 8⟩
abbrev rP (p : GenPublic) (st : KeyProgress) : Region := ⟨p.slot 4, plenOf p st⟩
abbrev rR (p : GenPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : GenPublic) : Region := ⟨p.B, p.Z⟩
abbrev rT (p : GenPublic) : Region := ⟨p.stp, 32⟩
abbrev rA (p : GenPublic) : Region := ⟨callSp p, 32⟩
abbrev rLow (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 416, 208⟩

/-- The controller's regions. -/
abbrev cK (p : GenPublic) : Region := ⟨p.kp, 9 * p.L⟩
abbrev cS (p : GenPublic) : Region := ⟨p.stp, 56⟩
abbrev cR (p : GenPublic) : Region := ⟨p.rp, p.randLen⟩
abbrev cStack (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 416, 416⟩

theorem disj_of_sep {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) :
    (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩ :=
  fun x hx hy => h x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

/-- What the controller's precondition says of its regions. -/
structure CFacts (p : GenPublic) : Prop where
  room : 416 ≤ p.sp.toNat
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
  nK : p.kp.toNat + 9 * p.L ≤ 2 ^ 64
  nU : p.up.toNat + 8 ≤ 2 ^ 64
  nS : p.B.toNat + p.Z ≤ 2 ^ 64
  nT : p.stp.toNat + 56 ≤ 2 ^ 64
  nR : p.rp.toNat + p.randLen ≤ 2 ^ 64
  len : primeLenValid p.L
  scratch : Spec.Rsa.scratchWords (2 * p.L) ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  rand_cap : p.randLen ≤ primeEntropy p.L
  rand64 : p.randLen < 2 ^ 64
  z64 : p.Z / 8 < 2 ^ 64

theorem GenInput.cfacts {p : GenPublic} {s : State} (h : GenInput p s) : CFacts p := by
  obtain ⟨hsp, _, _, hnw, hpw, hwr, hstk, hlen, hkl, hscr, -, -, -, hcap⟩ := h.1
  cases h.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pku, pks, pkt⟩, ⟨pus, put⟩, pst, -⟩ := hpw
  obtain ⟨wkr, wur, wsr, wtr⟩ := hwr
  obtain ⟨bk, bu, bs, bt, br⟩ := hstk
  obtain ⟨nk, nu, ns, nt, nr⟩ := hnw
  have hk : inKey s = ⟨s.gpr .x0, 9 * genLen s⟩ := by simp only [inKey, hkl]
  rw [hk] at pku pks pkt wkr bk nk
  refine ⟨hsp, pku, pks, pkt, pus, put, pst, wkr, wur, wsr, wtr, ?_, nk, nu, ns, nt, nr, hlen,
    ?_, ?_, hcap, BitVec.isLt _, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [bk.symm, bu.symm, bs.symm, bt.symm, br.symm]
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]; exact hscr
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]; exact BitVec.isLt _

/-! ### Sub-regions and disjointness -/

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

theorem rLow_sub : Region.Sub (rLow p) (cStack p) := Region.sub_prefix (by decide)

theorem oP (hf : CFacts p) : (rO p st).Disjoint (rP p st) := by
  have := hf.len.1
  unfold rO rP outOf plenOf
  split
  · intro x _ hy; simp only [Region.Contains] at hy; omega
  · exact slot_disjoint _ (.inr (by omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)

theorem tE : (rT p).Disjoint (rE p) := by
  have := Offset.sep p.stp (d := 0) (n := 32) (e := 48) (k := 8) (.inl (by decide)) (by decide) (by decide)
  rw [BitVec.add_zero] at this
  exact disj_of_sep this

theorem args_low : (rA p).Disjoint (rLow p) :=
  disj_of_sep (Offset.sep_below p.sp 416 (a := 208) (n := 32) (b := 416) (k := 208) (by decide) (by decide)
    (Or.inr (by decide)) (by decide) (by decide))

end

/-! ### The search's precondition -/

/-- The regions the search reads, and those it writes. -/
def sReads (p : GenPublic) (used : Nat) (st : KeyProgress) : List Region := [rE p, rP p st, rR p used, rA p]
def sWrites (p : GenPublic) (st : KeyProgress) : List Region := [rO p st, rU p, rS p, rT p]

/-- The search's entry, as the call makes it. -/
abbrev callS (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) : State :=
  u.callEntry.withRegions (sReads p used st) (sWrites p st)

theorem callS_gpr {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callS p used st u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem callS_stackArg (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) (j : Nat) :
    stackArg (callS p used st u) j = stackArg u j := rfl

theorem callS_arg {p : GenPublic} {used : Nat} {u : State} {m : Mem} (hu : u.sp = callSp p)
    (hm : u.mem = writeFrame m (callSp p) (callValues p used)) (j : Nat) (hj : j < 4) :
    stackArg u j = frameValue (callValues p used) j (word m (callSp p) (8 * j)) := by
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeFrame_word _ _ _ (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) j (by omega)

theorem callS_args {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State} {m : Mem}
    (hu : u.sp = callSp p) (hm : u.mem = writeFrame m (callSp p) (callValues p used)) :
    stackArg (callS p used st u) 0 = BitVec.ofNat 64 (p.randLen - used) ∧
      stackArg (callS p used st u) 1 = p.B ∧ stackArg (callS p used st u) 2 = BitVec.ofNat 64 (p.Z / 8) ∧
      stackArg (callS p used st u) 3 = p.stp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [callS_stackArg, callS_arg hu hm 0 (by decide)]; rfl
  · rw [callS_stackArg, callS_arg hu hm 1 (by decide)]; rfl
  · rw [callS_stackArg, callS_arg hu hm 2 (by decide)]; rfl
  · rw [callS_stackArg, callS_arg hu hm 3 (by decide)]; rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section

variable {p : GenPublic} {used : Nat} {st : KeyProgress} {s u : State}

/-- The stores of the search's stack arguments. -/
theorem callS_frame (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) :
    Frame [cStack p] s.mem (callS p used st u).mem := by
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [hm]
  apply (Search.writeFrame_frame_size _ _ (callValues p used) (size := 32) (by decide) (by
    simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, rA_sub⟩

theorem callS_regions (hu : u.sp = callSp p) (ha : SearchRegs p used st u)
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) (hf : CFacts p) :
    Search.inReads (callS p used st u) = sReads p used st ∧
      Search.inWrites (callS p used st u) = sWrites p st := by
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have hL := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by obtain ⟨-, h, -⟩ := hL; omega)
  have tp : (BitVec.ofNat 64 (plenOf p st)).toNat = plenOf p st :=
    toNat_ofNat_lt (by have := plen_le (p := p) (st := st); obtain ⟨-, h, -⟩ := hL; omega)
  have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by rw [toNat_ofNat_lt hf.z64]; exact hf.z8
  have hargs : stackArgAddr (callS p used st u) 0 = callSp p := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu, Nat.mul_zero, BitVec.add_zero]
  simp only [Search.inReads, Search.inWrites, Search.inE, Search.inP, Search.inRand, Search.inArgs,
    Search.inOut, Search.inUsed, Search.inScr, Search.inState, sReads, sWrites,
    callS_gpr (by decide : Reg.x0 ∉ linkRegs), callS_gpr (by decide : Reg.x1 ∉ linkRegs),
    callS_gpr (by decide : Reg.x2 ∉ linkRegs), callS_gpr (by decide : Reg.x3 ∉ linkRegs),
    callS_gpr (by decide : Reg.x4 ∉ linkRegs), callS_gpr (by decide : Reg.x5 ∉ linkRegs),
    callS_gpr (by decide : Reg.x6 ∉ linkRegs), callS_gpr (by decide : Reg.x7 ∉ linkRegs),
    r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, tl, tp, tr, tz, hargs]
  exact ⟨rfl, trivial⟩

theorem slot_nowrap (hf : CFacts p) {j n : Nat} (h : j * p.L + n ≤ 9 * p.L) :
    (p.kp + BitVec.ofNat 64 (j * p.L)).toNat + n ≤ 2 ^ 64 := by
  have := hf.nK
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  omega

theorem callSp_toNat (hf : CFacts p) : (callSp p).toNat = p.sp.toNat - 208 := by
  have := hf.room
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 208).toNat = 208 from rfl]; omega),
    show (BitVec.ofNat 64 208).toNat = 208 from rfl]

/-- The search's precondition at its entry. -/
theorem callS_pre {original : State} (h : GenLive p original used st s)
    (hu : u.sp = callSp p) (ha : SearchRegs p used st u)
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) :
    Search.searchPre (callS p used st u) := by
  have hf := h.input.cfacts
  obtain ⟨hrd, hwr⟩ := callS_regions hu ha hm hf
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (used := used) (st := st) hu hm
  have hsp : (callS p used st u).sp = callSp p := by
    simp only [State.withRegions_sp, State.callEntry_sp, hu]
  have hfr := callS_frame (st := st) hm
  have hL := hf.len
  obtain ⟨hL1, hL2, -⟩ := hL
  have hul := h.used_le
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hx1 : (callS p used st u).gpr .x1 = BitVec.ofNat 64 p.L := by
    rw [callS_gpr (by decide)]; exact ha.2.1
  have hx4 : (callS p used st u).gpr .x4 = BitVec.ofNat 64 8 := by
    rw [callS_gpr (by decide)]; exact ha.2.2.2.2.1
  have hcS : ∀ r ∈ [cStack p], (cS p).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact hf.stack (cS p) (by simp)
  have hword (d : Nat) (hd : d + 8 ≤ 56) :
      (callS p used st u).mem.readW (p.stp + BitVec.ofNat 64 d) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 d) 64 :=
    hfr.readW (Offset.contains_base _ hd (by omega)) hcS (by decide)
  have hE : Spec.Rsa.bytesAt (callS p used st u).mem (p.stp + BitVec.ofNat 64 48) 8 = p.eB := by
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfr.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hf.stack (cS p) (by simp)).sub_left (by
        rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]; exact Offset.sub_base _ (by decide)))
      (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have hlow : below (callSp p) Search.stackUse = rLow p := by
    simp only [below, rLow, callSp, BitVec.sub_sub]; rfl
  have st0 := h.state
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, sU, sS, sT, sR⟩ := hst
  have oK := rO_sub (st := st) hf
  have pK := rP_sub (p := p) (st := st)
  have rRc := rR_sub (p := p) hul
  have hspn := callSp_toNat hf
  have hroom := hf.room
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp, hspn]; have := p.sp.isLt; omega
  · rw [hsp, hspn]; show 208 ≤ _; omega
  · rw [hrd]; rfl
  · rw [hwr]; rfl
  · rw [hwr, hrd]
    intro r hr
    simp only [sWrites, sReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
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
    · simp only; rw [hspn]; have := p.sp.isLt; omega
  · rw [hwr]
    simp only [sWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hf.kU.sub_left oK, hf.kS.sub_left oK, (hf.kT.sub_left oK).sub_right rT_sub⟩,
      ⟨hf.uS, hf.uT.sub_right rT_sub⟩, hf.sT.sub_right rT_sub, fun _ h => h.elim⟩
  · rw [hwr, hrd]
    simp only [sWrites, sReads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨(hf.kT.sub_left oK).sub_right rE_sub, oP hf, (hf.kR.sub_left oK).sub_right rRc,
        (sK.sub_left oK).sub_right rA_sub⟩,
      ⟨hf.uT.sub_right rE_sub, (hf.kU.sub_left pK).symm, hf.uR.sub_right rRc, sU.sub_right rA_sub⟩,
      ⟨hf.sT.sub_right rE_sub, (hf.kS.sub_left pK).symm, hf.sR.sub_right rRc, sS.sub_right rA_sub⟩,
      ⟨tE, ((hf.kT.sub_left pK).sub_right rT_sub).symm, (hf.tR.sub_left rT_sub).sub_right rRc,
        (sT.sub_left rT_sub).sub_right rA_sub⟩⟩
  · rw [hwr, hrd, hsp, hlow]
    intro r hr
    simp only [sWrites, sReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (sK.sub_left oK).symm.sub_left rLow_sub
    · exact sU.symm.sub_left rLow_sub
    · exact sS.symm.sub_left rLow_sub
    · exact (sT.sub_left rT_sub).symm.sub_left rLow_sub
    · exact (sT.sub_left rE_sub).symm.sub_left rLow_sub
    · exact (sK.sub_left pK).symm.sub_left rLow_sub
    · exact (sR.sub_left rRc).symm.sub_left rLow_sub
    · exact args_low.symm
  · simp only [Search.searchLen, hx1, tl]; exact ⟨hL1, hL2, hf.len.2.2⟩
  · rw [hx4]; decide
  · rw [hx4]; decide
  · simp only [Search.searchLen, hx1, tl]
    rw [callS_gpr (by decide), ha.2.2.2.2.2.2.1, toNat_ofNat_lt (by have := plen_le (p := p) (st := st); omega)]
    unfold plenOf; split
    · exact .inl rfl
    · exact .inr rfl
  · simp only [Search.searchLen, hx1, tl, a2]
    rw [toNat_ofNat_lt hf.z64]
    have := hf.scratch; unfold Spec.Rsa.scratchWords at this ⊢; omega
  · have h0 := hword 0 (by decide)
    rw [BitVec.add_zero] at h0
    have h0' := st0.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0'
    have hlim : st.remaining < 2 ^ 64 := by
      have := st0.remaining_le
      unfold KeySearch.limitOf primeLimit at this
      split at this <;> omega
    have hrem : (Search.searchRemaining (callS p used st u)) = st.remaining := by
      simp only [Search.searchRemaining, a3, h0, h0']
      exact toNat_ofNat_lt hlim
    have hse : Search.searchE (callS p used st u) = p.eB := by
      simp only [Search.searchE, callS_gpr (by decide : Reg.x3 ∉ linkRegs), hx4, ha.2.2.2.1,
        toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
      exact hE
    rw [hrem, hse]
    simp only [Search.searchLen, hx1, tl]
    exact st0.remaining_le
  · simp only [Search.searchLen, hx1, tl, a3]
    rw [show (p.stp + 8 : Addr) = p.stp + BitVec.ofNat 64 8 from rfl, hword 8 (by decide)]
    exact st0.len
  · simp only [Search.searchLen, hx1, tl, a3]
    rw [show (p.stp + 16 : Addr) = p.stp + BitVec.ofNat 64 16 from rfl, hword 16 (by decide)]
    exact st0.cap
  · simp only [Search.searchLen, hx1, tl, a0]
    rw [toNat_ofNat_lt (by have := hf.rand64; omega)]
    have := hf.rand_cap; omega

end

/-! ### The prime search, run -/

/-- The prime search, as the controller calls it. -/
def searchCall (v : RoundImpl) : Prog isa :=
  .call ("vg_rsa_prime_search" ++ v.suffix) (Search.searchCode v)

theorem searchCode_depth (v : RoundImpl) : (Search.searchCode v).aarch64Depth = 13 := by
  simp only [Search.searchCode, Impl.RsaKeyGen.AArch64.Search.code, Impl.RsaKeyGen.AArch64.Search.search,
    Code.aarch64Depth, Search.iteration_depth, Instr.frameUnits, Impl.RsaKeyGen.AArch64.Search.frameBytes]
  decide

/-- What the search may write, as the controller sees it. -/
def searchChanges (p : GenPublic) (st : KeyProgress) : List Region :=
  [rO p st, rU p, rS p, rT p, ⟨p.sp - BitVec.ofNat 64 416, 256⟩]

/-- What the search of the progress' prime at `used` leaves. -/
structure AfterSearch (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress)
    (s t : State) : Prop where
  frame : GenFrame p original used ⟨st.left, st.phase, (primeOf p.L p.eB st ((genRand original).drop used)).remaining⟩ t
  status : ((t.gpr .x0).setWidth 32).toNat = (primeOf p.L p.eB st ((genRand original).drop used)).status
  usedw : word t.mem p.up 0 = BitVec.ofNat 64 (primeOf p.L p.eB st ((genRand original).drop used)).used
  out : Spec.Rsa.bytesAt t.mem (outOf p st) p.L =
    (match (primeOf p.L p.eB st ((genRand original).drop used)).outcome with
      | .accepted c => Spec.Rsa.i2osp c p.L
      | _ => List.replicate p.L 0)
  req : ∃ requested, word t.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (primeOf p.L p.eB st ((genRand original).drop used)).Requests (primeEntropy p.L) requested
  mem : Frame (searchChanges p st) s.mem t.mem

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem GenFrame.regions (h : GenFrame p original used st s) :
    inKey original = ⟨p.kp, 9 * p.L⟩ ∧ inUsed original = rU p ∧ inScr original = rS p ∧
      inState original = cS p ∧ inRand original = cR p := by
  refine ⟨h.key_region, ?_, ?_, ?_, ?_⟩ <;> rw [← h.input.2] <;> rfl

theorem search_covers_writes (h : GenFrame p original used st s) {u : State}
    (hw : u.wr = (allocated 32 s).wr) : Covers (sWrites p st) u.wr := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, ht, -⟩ := h.regions
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.1
  rw [hk, hu, hs, ht] at hwo
  rw [hw]
  refine Covers.of_sub fun r hr => ?_
  have hin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), rU p, rS p, cS p], q ∈ (allocated 32 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hL := hf.len.1
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), if phaseWord st.phase = 0 then 4 * p.L else 5 * p.L, ?_, ?_⟩
    · simp only [outOf]; split <;> rfl
    · show _ + p.L ≤ 9 * p.L
      split <;> omega
  · exact ⟨rU p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨cS p, hin _ (by simp), 0, by simp, by simp⟩

theorem search_covers_reads (h : GenFrame p original used st s) {u : State}
    (hrd : u.rd = (allocated 32 s).rd) (hw : u.wr = (allocated 32 s).wr) :
    Covers (sReads p used st ++ sWrites p st) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (search_covers_writes h hw).right
  have hf := h.input.cfacts
  obtain ⟨hk, -, -, ht, hr⟩ := h.regions
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.1
  have hro : original.rd = [inRand original] := h.input.1.2.1
  rw [hk, ht] at hwo
  rw [hr] at hro
  have hul := h.used_le
  have hL := hf.len.1
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [sReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  have hwin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), cS p], q ∈ (allocated 32 s).rd ++ (allocated 32 s).wr := by
    intro q hq
    refine List.mem_append_right _ ?_
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  rcases hr' with rfl | rfl | rfl | rfl
  · exact ⟨cS p, hwin _ (by simp), 48, rfl, by simp⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hwin _ (by simp), 4 * p.L, rfl, by
      show _ + plenOf p st ≤ 9 * p.L; have := plen_le (p := p) (st := st); omega⟩
  · refine ⟨cR p, List.mem_append_left _ ?_, used, rfl, by simp; omega⟩
    show cR p ∈ s.rd
    rw [h.rd, hro]; simp
  · refine ⟨⟨s.sp - BitVec.ofNat 64 32, 32⟩, List.mem_append_right _ (List.mem_cons_self ..), 0, ?_, by simp⟩
    rw [h.sp, callSp_eq, BitVec.add_zero]

end

/-- The search's result, from the controller's loop state. -/
theorem callS_result {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s)
    (hu : u.sp = callSp p) (ha : SearchRegs p used st u)
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) :
    Search.searchResult (callS p used st u) = primeOf p.L p.eB st ((genRand original).drop used) := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (used := used) (st := st) hu hm
  have hfr := callS_frame (st := st) hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, sR⟩ := hst
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  have hL := hf.len
  obtain ⟨hL1, hL2, -⟩ := hL
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p) ∨ Region.Sub R (cR p))
      (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callS p used st u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfr.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR, sR.sub_left hR]
  have hlim : st.remaining < 2 ^ 64 := by
    have := h.state.remaining_le
    unfold KeySearch.limitOf primeLimit at this
    split at this <;> omega
  unfold Search.searchResult
  congr 1
  · simp only [Search.searchLen, callS_gpr (by decide : Reg.x1 ∉ linkRegs), r1, tl]
  · simp only [Search.searchE, callS_gpr (by decide : Reg.x3 ∉ linkRegs), callS_gpr (by decide : Reg.x4 ∉ linkRegs),
      r3, r4, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    exact hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr (.inl rE_sub)) (by show 8 ≤ 2 ^ 64; decide)
  · simp only [Search.searchP, callS_gpr (by decide : Reg.x5 ∉ linkRegs), callS_gpr (by decide : Reg.x6 ∉ linkRegs),
      r5, r6, toNat_ofNat_lt (show plenOf p st < 2 ^ 64 by have := plen_le (p := p) (st := st); omega)]
    have hk := h.key.other
    unfold plenOf
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => simp [phaseWord, KeyPhase.other, Spec.Rsa.bytesAt]
    | q pB =>
      simp only [phaseWord, Nat.one_ne_zero, ↓reduceIte, KeyPhase.other]
      rw [← hk pB rfl]
      exact hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (slot_sub _ (by omega))) (by show p.L ≤ 2 ^ 64; omega)
  · simp only [Search.searchRemaining, a3]
    have h0 := h.state.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0
    have := hfr.readW (r := cS p) (a := p.stp) (w := 64)
      (by simpa only [BitVec.add_zero] using Offset.contains_base p.stp (d := 0) (n := 8) (k := 56) (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sT) (by decide)
    rw [this, h0, toNat_ofNat_lt hlim]
  · simp only [Search.searchRand, callS_gpr (by decide : Reg.x7 ∉ linkRegs), r7, a0,
      toNat_ofNat_lt (show p.randLen - used < 2 ^ 64 by have := hf.rand64; omega)]
    have := hbytes (R := rR p used) (.inr (.inr (rR_sub h.used_le))) (by have := hf.rand64; simp; omega)
    simp only at this
    rw [this, Search.bytesAt_drop, h.random]

theorem stack_mem (p : GenPublic) (st : KeyProgress) :
    (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region) ∈ searchChanges p st := by
  simp [searchChanges]

theorem searchChanges_sub {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    ∀ r ∈ searchChanges p st, ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, -, -⟩ := h.regions
  have hT : (⟨original.gpr .x7, 32⟩ : Region) = rT p := by rw [← h.input.2]; rfl
  have hS : (⟨original.sp - BitVec.ofNat 64 stackUse, 256⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 416, 256⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hu, hs, hT, hS]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., rO_sub hf⟩
  all_goals exact ⟨_, by simp, fun _ h => h⟩

theorem search_run (v : RoundImpl) {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    WP isa (searchRun (searchCall v)) s (AfterSearch p original used st s) := by
  have hf := h.input.cfacts
  have hF := h.input.F_toNat
  have hroom := hf.room
  have hsp32 : 32 ≤ s.sp.toNat := by
    rw [h.sp, show p.F - 16 = p.sp - BitVec.ofNat 64 176 by rw [GenPublic.F, BitVec.sub_sub]; rfl,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 176).toNat = 176 from rfl]; omega),
      show (BitVec.ofNat 64 176).toNat = 176 from rfl]
    omega
  unfold searchRun searchCall
  refine WP.alloc (by decide) hsp32 ?_
  refine WP.seq (WP.mono (search_args_ok h.toGenFrame) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = callSp p := k.sp.trans (alloc32_sp h.toGenFrame)
  have hd : 16 * (Search.searchCode v).aarch64Depth < 2 ^ 64 := by rw [searchCode_depth]; decide
  refine WP.callFV (k := Search.searchContract) (Search.search_correct _) (callS_pre h hu ha hm)
    (search_covers_reads h.toGenFrame k.rd k.wr) (search_covers_writes h.toGenFrame k.wr) ?_ hd
  intro t htr htw htsp hfr hg hvs hpost
  have hres := callS_result h hu ha hm
  obtain ⟨a0, a1, a2, a3⟩ := callS_args (used := used) (st := st) hu hm
  have hlen : Search.searchLen (callS p used st u) = p.L := by
    simp only [Search.searchLen, callS_gpr (by decide : Reg.x1 ∉ linkRegs), ha.2.1]
    exact toNat_ofNat_lt (by have := hf.len.2.1; omega)
  obtain ⟨hst, hout, hused, req, hwords, hreq⟩ := hpost
  have hx0 : (callS p used st u).gpr .x0 = outOf p st := by rw [callS_gpr (by decide)]; exact ha.1
  have hx2 : (callS p used st u).gpr .x2 = p.up := by rw [callS_gpr (by decide)]; exact ha.2.2.1
  simp only [hres, hlen, State.withRegions_mem, State.withRegions_gpr, a3, hx0, hx2]
    at hst hout hused hwords hreq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 1 = [0] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hwords hused
  simp only [Nat.reduceMul] at hwords hused
  obtain ⟨w0, w1, w2, w3⟩ := hwords
  have f₀ : Frame (searchChanges p st) s.mem u.mem := by
    rw [hm]
    apply (Search.writeFrame_frame_size _ _ (callValues p used) (size := 32) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, stack_mem p st, Offset.sub_below _ (by decide) (by decide)⟩
  have f₁ : Frame (searchChanges p st) u.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨r, ?_, fun _ h => h⟩
      simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, stack_mem p st, ?_⟩
      rw [hu, searchCode_depth]
      simp only [below, callSp, BitVec.sub_sub]
      exact Offset.sub_below _ (by decide) (by decide)
  have hframe := f₀.trans f₁
  have hrem := KeySearch.primeSearch_remaining_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
  have hle := h.state.remaining_le
  have hfree : (freed 32 t).mem = t.mem := rfl
  refine ⟨h.toGenFrame.restore (htr.trans k.rd) (show t.wr.tail = s.wr by rw [htw, k.wr]; rfl)
      (show t.sp + BitVec.ofNat 64 32 = s.sp by rw [htsp, k.sp]; exact BitVec.sub_add_cancel _ _)
      (fun r hr h30 => (hg r hr h30).trans (k.gpr r (by revert r hr; decide)))
      (fun r hr => (hvs r hr).trans (k.vcs r hr)) (hframe.sub (searchChanges_sub h.toGenFrame)) ?_ w1 w2
      (.inl rfl) rfl (Nat.le_trans hrem hle), ?_, ?_, ?_, ⟨req, ?_, hreq⟩, hframe⟩
  · exact w0
  · exact hst
  · exact hused
  · exact hout
  · exact w3

end VG.Proof.RsaKeyGen.AArch64.Generate

/-! ## The controller's blocks after a search (AArch64)

The octets the search consumed added to the frame's count, and the stores
that start the next prime's search (`nextPrime`) or end the key search
(`finishWith`), each with the frame and the state they leave.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld st mov movi)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

namespace GenFrame

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem scr (h : GenFrame p original used st s) : Scr s p.F 160 := h.input.frame_scr h.wr

theorem state_region (h : GenFrame p original used st s) : inState original = ⟨p.stp, 56⟩ := by
  rw [← h.input.2]; rfl

theorem used_region (h : GenFrame p original used st s) : inUsed original = ⟨p.up, 8⟩ := by
  rw [← h.input.2]; rfl

theorem stateScr (h : GenFrame p original used st s) : Scr s p.stp 56 := by
  have hn := h.input.nowrap (r := inState original) (by simp [inWrites])
  rw [h.state_region] at hn
  refine Scr.of_mem ?_ hn
  rw [h.wr, h.input.1.2.2.1, ← h.state_region]
  simp [inWrites]

theorem usedScr (h : GenFrame p original used st s) : Scr s p.up 8 := by
  have hn := h.input.nowrap (r := inUsed original) (by simp [inWrites])
  rw [h.used_region] at hn
  refine Scr.of_mem ?_ hn
  rw [h.wr, h.input.1.2.2.1, ← h.used_region]
  simp [inWrites]

/-- A header word of the frame. -/
theorem header (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64} (hj : (j, v) ∈ p.headers used) :
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj

end GenFrame

/-- The frame's headers after the octets consumed are `u`. -/
theorem slots_used {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (u : Nat) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20)
    (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (p.headers u) := by
  have hb' : ∀ e ∈ (8, BitVec.ofNat 64 u) :: values, e.1 < 20 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · show 8 < 20; decide
    · exact hb e he
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

theorem exec_addImm_w {s : State} {d n : Reg} :
    exec (.addImm .w d n 0) s = some (s.write .x d (BitVec.setWidth 64 ((s.gpr n).setWidth 32))) := by
  simp only [exec, State.read, State.write, Size.bits, BitVec.add_zero,
    show (0 : Nat) < 4096 by decide, ite_true, BitVec.setWidth_eq]

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · rintro rfl; rfl

/-- The status, the octets the search consumed and the count of those
consumed so far. -/
theorem head_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {n status : Nat}
    (hs : ((s.gpr .x0).setWidth 32).toNat = status) (hn : word s.mem p.up 0 = BitVec.ofNat 64 n) :
    WP isa (.block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8, .add .x .x12 .x12 .x10,
      stf .x12 8]) s fun t =>
      (t.gpr .x9 = BitVec.ofNat 64 status ∧ t.gpr .x10 = BitVec.ofNat 64 n ∧
        t.mem = writeFrame s.mem p.F [(8, BitVec.ofNat 64 used + BitVec.ofNat 64 n)]) ∧
      Keep [.x9, .x10, .x11, .x12] s t := by
  have scr := h.scr
  have hu := h.usedScr
  have h2 := h.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := h.header (j := 8) (v := BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  have hl2 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 16) 8 := scr.ld (d := 16) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 64) 8 := scr.ld (d := 64) (by decide)
  have hs8 : InRegions s.wr (p.F + BitVec.ofNat 64 64) 8 := scr.st (d := 64) (by decide)
  have hlu : InRegions (s.rd ++ s.wr) (p.up + BitVec.ofNat 64 0) 8 := hu.ld (d := 0) (by decide)
  have hn' : s.mem.readW (p.up + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 n := hn
  have hlu0 : InRegions (s.rd ++ s.wr) p.up 8 := by simpa only [BitVec.add_zero] using hlu
  have hn0 : s.mem.readW p.up 64 = BitVec.ofNat 64 n := by simpa only [BitVec.add_zero] using hn'
  simp only [Nat.reduceMul] at h2 h8
  have hax : ((s.gpr .x0).setWidth 32).setWidth 64 = BitVec.ofNat 64 status := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]
  refine WP.keep [.x9, .x10, .x11, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [exec_addImm_w, ldf, stf, h.x19, hl2, hl8, hs8, hlu, h2, h8, hn', hlu0, hn0, hax]

/-! ### Stores to the state and the frame -/

/-- The state's words `0`, `4` and `5` and the frame's status or region to
zero stored. -/
def StateStores (sv fv : List (Nat × BitVec 64)) : Prop :=
  (∀ e ∈ sv, e.1 = 0 ∨ e.1 = 4 ∨ e.1 = 5) ∧ (∀ e ∈ fv, e.1 = 10 ∨ e.1 = 12 ∨ e.1 = 13)

/-- What stores to the state's first six words and to the frame keep: the
memory outside them. -/
theorem stores_frame (p : GenPublic) (m : Mem) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame (writeFrame m p.stp sv) p.F fv) := by
  have h1 : Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame m p.stp sv) :=
    (Search.writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  have h2 : Frame [⟨p.stp, 48⟩, p.frame] (writeFrame m p.stp sv) (writeFrame (writeFrame m p.stp sv) p.F fv) :=
    (writeFrame_frame _ _ fv fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide).sub
      fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp, fun _ h => h⟩
  exact h1.trans h2

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

theorem stores_changes (h : GenFrame p original used st s) :
    ∀ r ∈ [(⟨p.stp, 48⟩ : Region), p.frame], ∃ q ∈ GenInput.changes original, Region.Sub r q := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨inState original, by simp [GenInput.changes, inWrites], by
      rw [h.state_region]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩

/-- Through stores to the state's words `0`, `4` and `5` and to the frame's
status or region to zero, for the progress `st'` those words hold. -/
theorem setState (h : GenFrame p original used st s) {st' : KeyProgress} {sv fv : List (Nat × BitVec 64)}
    (hv : StateStores sv fv) (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F fv)
    {rs : List Reg} (kp : Keep rs s t) (hregs : ∀ reg ∈ preserved, reg ∉ rs)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64) :
    GenFrame p original used st' t := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hsd := h.input.frame_state
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (hregs r hr)
  have hF (j : Nat) (hj : j < 20) (hnot : ∀ e ∈ fv, j ≠ e.1) :
      word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [hm, writeFrame_word _ _ _ hfb j hj, frameValue_unchanged _ _ _ hnot]
    refine (Search.writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).readW (r := p.frame)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => ?_) (by decide)
    obtain rfl := List.mem_singleton.mp hq
    exact hsd.sub_right (Region.sub_prefix (by decide))
  have hS (j : Nat) (hj : j < 7) :
      word t.mem p.stp (8 * j) = frameValue sv j (word s.mem p.stp (8 * j)) := by
    rw [hm, ← writeFrame_word _ _ _ hsb j (by omega)]
    exact (writeFrame_frame _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact hsd.symm) (by decide)
  have hnf : ∀ j, j ≠ 10 → j ≠ 12 → j ≠ 13 → ∀ e ∈ fv, j ≠ e.1 := fun j h10 h12 h13 e he heq => by
    rcases hv.2 e he with h | h | h <;> omega
  have hns : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 5 → ∀ e ∈ sv, j ≠ e.1 := fun j h0 h4 h5 e he heq => by
    rcases hv.1 e he with h | h | h <;> omega
  have hfr : Frame (GenInput.changes original) s.mem t.mem := by
    rw [hm]; exact (stores_frame p s.mem hv).sub h.stores_changes
  refine ⟨h.input, h.used_le, kp.rd.trans h.rd, kp.wr.trans h.wr, kp.sp.trans h.sp,
    (hg .x19 (by decide)).trans h.x19, fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hrem, hlt⟩⟩
  · exact (hF 9 (by decide) (hnf 9 (by decide) (by decide) (by decide))).trans h.savedX19
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
    have hnst := h.input.state_nowrap
    refine stores_bytes p s.mem (R := ⟨p.stp + 48, 8⟩) hv ?_ ?_ (by show 8 ≤ 2 ^ 64; decide)
    · intro x hx hy
      exact Offset.sep p.stp (d := 0) (n := 48) (e := 48) (k := 8) (.inl (by omega)) (by omega) (by omega) x
        (by rw [BitVec.add_zero]; simp only [Region.Contains] at hx; omega)
        (by
          have e48 : (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 := rfl
          simp only [Region.Contains, e48] at hy; omega)
    · exact hsd.sub_right (Offset.sub_base _ (by decide))

end GenFrame

/-! ### The blocks -/

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

/-- The next prime's search, in `phase`: all its counted candidates, and the
status that goes on. -/
theorem nextPrime_ok (h : GenFrame p original used st s) {phase : Nat} (hph : phase < 2) :
    WP isa (.block (nextPrime phase)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
        (4, BitVec.ofNat 64 phase)]) p.F [(10, BitVec.ofNat 64 4)] ∧ Keep [.x8, .x11] s t := by
  obtain rfl | rfl : phase = 0 ∨ phase = 1 := by omega
  all_goals
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.header (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl11 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 88) 8 := scr.ld (d := 88) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs0 : InRegions s.wr (p.stp + BitVec.ofNat 64 0) 8 := sst.st (d := 0) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs00 : InRegions s.wr p.stp 8 := by simpa only [BitVec.add_zero] using hs0
  simp only [Nat.reduceMul] at h7 h11
  refine WP.keep [.x8, .x11] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, hl7, hl11, hs10, hs0, hs00, hs4, h7, h11, imm64 (show 0 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), imm64 (show 4 < 65536 by decide)]
  all_goals simp only [off, Nat.reduceMul, BitVec.add_zero]

/-- The end of the key search with `status`: no phase or generations left. -/
theorem finishWith_ok (h : GenFrame p original used st s) {status : Nat} (hs : status < 4) :
    WP isa (.block (finishWith status)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(4, BitVec.ofNat 64 0), (5, BitVec.ofNat 64 0)]) p.F
        [(10, BitVec.ofNat 64 status)] ∧ Keep [.x8, .x11] s t := by
  obtain rfl | rfl | rfl | rfl : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 := by omega
  all_goals
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  simp only [Nat.reduceMul] at h7
  refine WP.keep [.x8, .x11] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame finishWith
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, hl7, hs10, hs4, hs5, h7, imm64 (show 0 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), imm64 (show 2 < 65536 by decide), imm64 (show 3 < 65536 by decide)]

/-- The status, stored. -/
theorem storeStatus_ok (h : GenFrame p original used st s) {status : Nat}
    (hs : s.gpr .x9 = BitVec.ofNat 64 status) :
    WP isa (.block [stf .x9 10]) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp []) p.F [(10, BitVec.ofNat 64 status)] ∧ Keep [] s t := by
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := h.scr.st (d := 80) (by decide)
  refine WP.keep [] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [stf, h.x19, hs10, hs]

/-- The generations left: `x12` is 1 exactly when at least two are. -/
theorem left_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .x8 7, ld .x10 .x8 40, movi .x15 2, movi .x13 1, movi .x17 0, .subs .x .x16 .x10 .x15,
      .csel .x .x12 .x13 .x17]) s fun t =>
      (t.gpr .x12 = (if 2 ≤ st.left then 1 else 0) ∧ t.gpr .x8 = p.stp ∧ t.gpr .x10 = BitVec.ofNat 64 st.left ∧
        t.mem = s.mem) ∧ Keep [.x8, .x10, .x12, .x13, .x15, .x16, .x17] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl5 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 40) 8 := sst.ld (d := 40) (by decide)
  have h5 : s.mem.readW (p.stp + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 st.left := h.state.left
  simp only [Nat.reduceMul] at h7
  have hlt := h.state.left_lt
  refine WP.keep [.x8, .x10, .x12, .x13, .x15, .x16, .x17] ?_ (by decide) (by decide) (by decide +kernel)
  by_cases h2 : 2 ≤ st.left <;>
  brun [ldf, h.x19, hl7, hl5, h7, h5, imm64 (show 2 < 65536 by decide), imm64 (show 1 < 65536 by decide),
    imm64 (show 0 < 65536 by decide), subs_ge hlt (show 2 < 2 ^ 64 by decide), h2]

/-- The phase, loaded. -/
theorem phase_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .x8 7, ld .x10 .x8 32]) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (phaseWord st.phase) ∧ t.mem = s.mem) ∧ Keep [.x8, .x10] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl4 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 32) 8 := sst.ld (d := 32) (by decide)
  have h4 : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) := h.state.phase
  simp only [Nat.reduceMul] at h7
  refine WP.keep [.x8, .x10] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ldf, h.x19, hl7, hl4, h7, h4]

end

end VG.Proof.RsaKeyGen.AArch64.Generate

/-! ## The key's arguments, call and run (AArch64)

`n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` at the key's buffer's slots 0, 2,
4, 5, 6, 7 and 8; the exponent the state's last word; the working space. The
ten stack arguments in the call's frame of 80 bytes below the frame saving
`x30`, at `sp - 256` for the controller's stack pointer on entry. The key has
no frames. It leaves the key's status and its outputs at the key's buffer,
and writes nothing else but the working space and the stack.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld st mov movi)
open VG.Spec.RsaKeyGen

/-- The stack pointer in the key's call frame. -/
abbrev keySp (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 256

theorem keySp_eq (p : GenPublic) : p.F - 16 - BitVec.ofNat 64 80 = keySp p := by
  rw [GenPublic.F, BitVec.sub_sub, BitVec.sub_sub]; rfl

/-- The key's stack arguments. -/
def keyValues (p : GenPublic) : List (Nat × BitVec 64) :=
  [(0, p.slot 6), (1, BitVec.ofNat 64 p.L), (2, p.slot 7), (3, BitVec.ofNat 64 p.L), (4, p.slot 8),
    (5, BitVec.ofNat 64 p.L), (6, p.stp + BitVec.ofNat 64 48), (7, BitVec.ofNat 64 8), (8, p.B),
    (9, BitVec.ofNat 64 (p.Z / 8))]

theorem keyValues_bound (p : GenPublic) : ∀ e ∈ keyValues p, 8 * e.1 + 8 ≤ 80 := by
  simp only [keyValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem keyValues_bound20 (p : GenPublic) : ∀ e ∈ keyValues p, e.1 < 20 := fun e he => by
  have := keyValues_bound p e he; omega

/-- The key's arguments in registers. -/
def KeyRegs (p : GenPublic) (s : State) : Prop :=
  s.gpr .x0 = p.kp ∧ s.gpr .x1 = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .x2 = p.slot 2 ∧
    s.gpr .x3 = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .x4 = p.slot 4 ∧ s.gpr .x5 = BitVec.ofNat 64 p.L ∧
    s.gpr .x6 = p.slot 5 ∧ s.gpr .x7 = BitVec.ofNat 64 p.L

/-- The registers the key's arguments' block writes. -/
abbrev keyArgRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12, .x15]

theorem alloc80_sp {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : (allocated 80 s).sp = keySp p := by
  show s.sp - _ = _
  rw [h.sp, keySp_eq]

theorem key_args_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block keyArgs) (allocated 80 s) fun t =>
      (KeyRegs p t ∧ t.mem = writeFrame s.mem (keySp p) (keyValues p)) ∧ Keep keyArgRegs (allocated 80 s) t := by
  have hl := h.frame_ld' (t := allocated 80 s) rfl
  have hsp := alloc80_sp h
  have haw : (allocated 80 s).wr = ⟨keySp p, 80⟩ :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 80, 80⟩ : Region) :: s.wr = _
    rw [h.sp, keySp_eq]
  have hw : ∀ d, d + 8 ≤ 80 → InRegions (allocated 80 s).wr (keySp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨keySp p, 80⟩, by rw [haw]; exact List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  have hw0 : InRegions (allocated 80 s).wr (keySp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hv0 := h.header (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv5 := h.header (j := 5) (v := p.B) (by simp [GenPublic.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul] at hv0 hv1 hv5 hv6 hv7
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have h2 : BitVec.ofNat 64 p.L <<< 1 = BitVec.ofNat 64 (2 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h02 : p.kp + BitVec.ofNat 64 (2 * p.L) = p.slot 2 := rfl
  have h24 : p.slot 2 + BitVec.ofNat 64 (2 * p.L) = p.slot 4 := by
    rw [GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  have hn (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; rw [Nat.succ_mul]
  have h45 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := hn 4
  have h56 : p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 := hn 5
  have h67 : p.slot 6 + BitVec.ofNat 64 p.L = p.slot 7 := hn 6
  have h78 : p.slot 7 + BitVec.ofNat 64 p.L = p.slot 8 := hn 7
  have hmem : (allocated 80 s).mem = s.mem := rfl
  have hx19 : (allocated 80 s).gpr .x19 = p.F := h.x19
  refine WP.keep keyArgRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold keyArgs KeyRegs writeFrame keyValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, hsp, hmem, hx19, exec_addSp (show 0 < 4096 by decide), imm64 (show 8 < 65536 by decide),
    hl 0 (by decide), hl 8 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hv0, hv1, hv5, hv6, hv7, h2, h02, h24, h45, h56, h67, h78,
    hw0, hw 0 (by decide), hw 8 (by decide), hw 16 (by decide), hw 24 (by decide), hw 32 (by decide),
    hw 40 (by decide), hw 48 (by decide), hw 56 (by decide), hw 64 (by decide), hw 72 (by decide)]
  all_goals simp only [off, Nat.mul_zero, BitVec.add_zero, Nat.reduceMul]

/-! ### The key's call -/

/-- The key's buffer's slot `j`, of `n` octets. -/
abbrev kSlot (p : GenPublic) (j n : Nat) : Region := ⟨p.slot j, n⟩

/-- `n`, of `2 p_len` octets at the key's buffer. -/
abbrev kN (p : GenPublic) : Region := ⟨p.kp, 2 * p.L⟩

/-- The key's stack arguments. -/
abbrev kA (p : GenPublic) : Region := ⟨keySp p, 80⟩

/-- The regions the key reads, and those it writes. -/
def kReads (p : GenPublic) : List Region := [rE p, kA p]
def kWrites (p : GenPublic) : List Region :=
  [kN p, kSlot p 2 (2 * p.L), kSlot p 4 p.L, kSlot p 5 p.L, kSlot p 6 p.L, kSlot p 7 p.L, kSlot p 8 p.L, rS p]

/-- The key's entry, as the call makes it. -/
abbrev callK (p : GenPublic) (u : State) : State := u.callEntry.withRegions (kReads p) (kWrites p)

section

variable {p : GenPublic}

theorem kA_sub : Region.Sub (kA p) (cStack p) := Offset.sub_below _ (by decide) (by decide)

theorem kk (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) : (kSlot p i a).Disjoint (kSlot p j b) :=
  slot_disjoint p.kp h (by have := hf.nK; omega) (by have := hf.nK; omega)

theorem kN_slot (hf : CFacts p) {j b : Nat} (h : 2 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (kN p).Disjoint (kSlot p j b) := by
  have := slot_disjoint p.kp (d := 0) (n := 2 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

theorem kSlot_sub {j n : Nat} (h : j * p.L + n ≤ 9 * p.L) : Region.Sub (kSlot p j n) (cK p) := slot_sub _ h

theorem kN_sub : Region.Sub (kN p) (cK p) := Region.sub_prefix (by omega)

end

section

variable {p : GenPublic} {s u : State}

theorem callK_gpr {r : Reg} (hr : r ∉ linkRegs) : (callK p u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem callK_arg (hu : u.sp = keySp p)
    (hm : u.mem = writeFrame s.mem (keySp p) (keyValues p)) (j : Nat) (hj : j < 10) :
    Key.arg (callK p u) j = frameValue (keyValues p) j (word s.mem (keySp p) (8 * j)) := by
  show stackArg u j = _
  unfold stackArg stackArgAddr
  rw [hu, hm]
  exact writeFrame_word _ _ _ (keyValues_bound20 p) j (by omega)

/-- The key's stack arguments. -/
theorem callK_args (hu : u.sp = keySp p) (hm : u.mem = writeFrame s.mem (keySp p) (keyValues p)) :
    Key.arg (callK p u) 0 = p.slot 6 ∧ Key.arg (callK p u) 1 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 2 = p.slot 7 ∧ Key.arg (callK p u) 3 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 4 = p.slot 8 ∧ Key.arg (callK p u) 5 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 6 = p.stp + BitVec.ofNat 64 48 ∧ Key.arg (callK p u) 7 = BitVec.ofNat 64 8 ∧
      Key.arg (callK p u) 8 = p.B ∧ Key.arg (callK p u) 9 = BitVec.ofNat 64 (p.Z / 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [callK_arg hu hm _ (by decide)]; rfl)

/-- The stores of the key's stack arguments. -/
theorem callK_frame (hm : u.mem = writeFrame s.mem (keySp p) (keyValues p)) :
    Frame [cStack p] s.mem (callK p u).mem := by
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [hm]
  apply (Search.writeFrame_frame_size _ _ (keyValues p) (size := 80) (by decide) (keyValues_bound p)).sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, kA_sub⟩

end

/-! ### The key's precondition -/

/-- The key's precondition at its entry. -/
theorem callK_pre {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s)
    (hu : u.sp = keySp p) (ha : KeyRegs p u) (hm : u.mem = writeFrame s.mem (keySp p) (keyValues p)) :
    Key.keyPre (callK p u) := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := callK_args (s := s) hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have t8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by rw [toNat_ofNat_lt hf.z64]; exact hf.z8
  have hargs : stackArgAddr (callK p u) 0 = keySp p := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hu, Nat.mul_zero, BitVec.add_zero]
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, sS, sT, -⟩ := hst
  have hn := hf.nK
  have s2 : Region.Sub (kSlot p 2 (2 * p.L)) (cK p) := kSlot_sub (by omega)
  have s4 : Region.Sub (kSlot p 4 p.L) (cK p) := kSlot_sub (by omega)
  have s5 : Region.Sub (kSlot p 5 p.L) (cK p) := kSlot_sub (by omega)
  have s6 : Region.Sub (kSlot p 6 p.L) (cK p) := kSlot_sub (by omega)
  have s7 : Region.Sub (kSlot p 7 p.L) (cK p) := kSlot_sub (by omega)
  have s8 : Region.Sub (kSlot p 8 p.L) (cK p) := kSlot_sub (by omega)
  have sN : Region.Sub (kN p) (cK p) := kN_sub
  have kE {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (rE p) := (hf.kT.sub_left hR).sub_right rE_sub
  have kS {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (rS p) := hf.kS.sub_left hR
  have kAr {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (kA p) := (sK.sub_left hR).sub_right kA_sub
  have hsp : (callK p u).sp = keySp p := by simp only [State.withRegions_sp, State.callEntry_sp, hu]
  have hroom := hf.room
  simp only [Key.keyPre, Key.args, Key.arg, callK_gpr (by decide : Reg.x0 ∉ linkRegs),
    callK_gpr (by decide : Reg.x1 ∉ linkRegs), callK_gpr (by decide : Reg.x2 ∉ linkRegs),
    callK_gpr (by decide : Reg.x3 ∉ linkRegs), callK_gpr (by decide : Reg.x4 ∉ linkRegs),
    callK_gpr (by decide : Reg.x5 ∉ linkRegs), callK_gpr (by decide : Reg.x6 ∉ linkRegs),
    callK_gpr (by decide : Reg.x7 ∉ linkRegs), r0, r1, r2, r3, r4, r5, r6, r7]
  simp only [show stackArg (callK p u) 0 = _ from a0, show stackArg (callK p u) 1 = _ from a1,
    show stackArg (callK p u) 2 = _ from a2, show stackArg (callK p u) 3 = _ from a3,
    show stackArg (callK p u) 4 = _ from a4, show stackArg (callK p u) 5 = _ from a5,
    show stackArg (callK p u) 6 = _ from a6, show stackArg (callK p u) 7 = _ from a7,
    show stackArg (callK p u) 8 = _ from a8, show stackArg (callK p u) 9 = _ from a9,
    tl, t2, t8, tz, hargs, hsp, State.withRegions_rd, State.withRegions_wr]
  refine ⟨?_, rfl, rfl, kN_slot hf (by decide) (by omega), kN_slot hf (by decide) (by omega),
    kN_slot hf (by decide) (by omega), kN_slot hf (by decide) (by omega), kN_slot hf (by decide) (by omega),
    kN_slot hf (by decide) (by omega), kE sN, kS sN, kAr sN,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kE s2, kS s2, kAr s2,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega), kE s4, kS s4, kAr s4,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kE s5, kS s5, kAr s5,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega), kE s6, kS s6, kAr s6,
    kk hf (by omega) (by omega) (by omega), kE s7, kS s7, kAr s7,
    kE s8, kS s8, kAr s8,
    (hf.sT.sub_right rE_sub).symm, sS.sub_right kA_sub,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hL1, hL2, hL3⟩, trivial, trivial, trivial, trivial, trivial, trivial,
    by decide, by decide, ?_⟩
  · have := p.sp.isLt
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 256).toNat = 256 from rfl]; omega),
      show (BitVec.ofNat 64 256).toNat = 256 from rfl]
    omega
  · omega
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · rw [BitVec.toNat_add, toNat_ofNat_lt (by decide)]; have := hf.nT; omega
  · exact hf.nS
  · have := hf.scratch
    rw [toNat_ofNat_lt hf.z64]
    exact this

/-! ### The key, run -/

/-- The key, as the controller calls it. -/
def keyCall : Prog isa := .call "vg_rsa_keygen_key" VG.Impl.RsaKeyGen.AArch64.Key.code

theorem keyCode_noFrames : VG.Impl.RsaKeyGen.AArch64.Key.code.noFrames = true := by decide +kernel

/-- The key from the primes at the slots of `p` and `q`. -/
abbrev keyOf (p : GenPublic) (m : Mem) : Except Failure (List (List Byte)) ⊕ Unit :=
  keyOp p.L p.eB (Spec.Rsa.bytesAt m (p.slot 4) p.L) (Spec.Rsa.bytesAt m (p.slot 5) p.L)

/-- The key's outputs at the key's buffer. -/
def keyOutsOf (p : GenPublic) : List (Addr × Nat) :=
  [(p.kp, 2 * p.L), (p.slot 2, 2 * p.L), (p.slot 4, p.L), (p.slot 5, p.L), (p.slot 6, p.L), (p.slot 7, p.L),
    (p.slot 8, p.L)]

/-- What the key leaves. -/
structure AfterKey (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p original used st t
  status : ((t.gpr .x0).setWidth 32).toNat = keyStatus (keyOf p s.mem)
  out : match keyOf p s.mem with
    | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
  mem : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 416, 256⟩] s.mem t.mem

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem key_covers_writes (h : GenFrame p original used st s) {u : State}
    (hw : u.wr = (allocated 80 s).wr) : Covers (kWrites p) u.wr := by
  have hf := h.input.cfacts
  have hk := h.key_region
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.1
  rw [hk, hs] at hwo
  rw [hw]
  have hin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), rS p], q ∈ (allocated 80 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  obtain ⟨hL1, -, -⟩ := hf.len
  refine Covers.of_sub fun r hr => ?_
  simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 0, by simp, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 2 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 4 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 5 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 6 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 7 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 8 * p.L, rfl, by simp; omega⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩

theorem key_covers_reads (h : GenFrame p original used st s) {u : State}
    (hrd : u.rd = (allocated 80 s).rd) (hw : u.wr = (allocated 80 s).wr) :
    Covers (kReads p ++ kWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (key_covers_writes h hw).right
  have ht : inState original = cS p := by rw [← h.input.2]; rfl
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.1
  rw [ht] at hwo
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [kReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · refine ⟨cS p, List.mem_append_right _ ?_, 48, rfl, by simp⟩
    show cS p ∈ _ :: s.wr
    rw [h.wr, hwo]; simp
  · refine ⟨⟨s.sp - BitVec.ofNat 64 80, 80⟩, List.mem_append_right _ (List.mem_cons_self ..), 0, ?_, by simp⟩
    rw [h.sp, keySp_eq, BitVec.add_zero]

theorem key_frame_sub (h : GenFrame p original used st s) :
    ∀ r ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region)],
      ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hk := h.key_region
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  have hS : (⟨original.sp - BitVec.ofNat 64 stackUse, 256⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 416, 256⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hs, hS]
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end

/-- The key's result at its entry: the key from the slots of `p` and `q`. -/
theorem callK_res {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hu : u.sp = keySp p) (ha : KeyRegs p u)
    (hm : u.mem = writeFrame s.mem (keySp p) (keyValues p)) :
    Key.keyRes (callK p u) = keyOf p s.mem ∧
      Spec.Rsa.bytesAt (callK p u).mem (Key.arg (callK p u) 6) (Key.arg (callK p u) 7).toNat = p.eB := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := callK_args (s := s) hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hcf := callK_frame (s := s) (u := u) hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -⟩ := hst
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callK p u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hcf.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR]
  have he : Spec.Rsa.bytesAt (callK p u).mem (Key.arg (callK p u) 6) (Key.arg (callK p u) 7).toNat = p.eB := by
    rw [a6, a7, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide),
      hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide)]
    exact h.state.e
  refine ⟨?_, he⟩
  simp only [Key.keyRes, callK_gpr (by decide : Reg.x4 ∉ linkRegs), callK_gpr (by decide : Reg.x5 ∉ linkRegs),
    callK_gpr (by decide : Reg.x6 ∉ linkRegs), r4, r5, r6, tl]
  rw [he, hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega),
    hbytes (R := ⟨p.slot 5, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega)]

theorem key_run [Key.KeyProof] {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (keyRun keyCall) s (AfterKey p original used st s) := by
  have hf := h.input.cfacts
  have hroom := hf.room
  have hsp80 : 80 ≤ s.sp.toNat := by
    rw [h.sp, show p.F - 16 = p.sp - BitVec.ofNat 64 176 by rw [GenPublic.F, BitVec.sub_sub]; rfl,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 176).toNat = 176 from rfl]; omega),
      show (BitVec.ofNat 64 176).toNat = 176 from rfl]
    omega
  unfold keyRun keyCall
  refine WP.alloc (by decide) hsp80 ?_
  refine WP.seq (WP.mono (key_args_ok h) fun u ⟨⟨ha, hm⟩, k⟩ => ?_)
  have hu : u.sp = keySp p := k.sp.trans (alloc80_sp h)
  refine WP.callV (k := Key.keyA) Key.KeyProof.correct (callK_pre h hu ha hm) (key_covers_reads h k.rd k.wr)
    (key_covers_writes h k.wr) ?_ keyCode_noFrames
  intro t htr htw htsp hfr hg _ hvs hpost
  obtain ⟨hres, -⟩ := callK_res h hu ha hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := callK_args (s := s) hu hm
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have houts : Key.keyOuts (callK p u) = keyOutsOf p := by
    simp only [Key.keyOuts, callK_gpr (by decide : Reg.x0 ∉ linkRegs), callK_gpr (by decide : Reg.x1 ∉ linkRegs),
      callK_gpr (by decide : Reg.x2 ∉ linkRegs), callK_gpr (by decide : Reg.x4 ∉ linkRegs),
      callK_gpr (by decide : Reg.x5 ∉ linkRegs), callK_gpr (by decide : Reg.x6 ∉ linkRegs),
      r0, r1, r2, r4, r5, r6, tl, t2, a0, a2, a4]
    rfl
  obtain ⟨hstat, hout⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem] at hstat hout
  rw [hres] at hstat hout
  rw [houts] at hout
  have mK : cK p ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region)] := List.mem_cons_self ..
  have mS : rS p ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region)] :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have mT : (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region) ∈
      [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region)] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f₀ : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 416, 256⟩] s.mem u.mem := by
    rw [hm]
    apply (Search.writeFrame_frame_size _ _ (keyValues p) (size := 80) (by decide) (keyValues_bound p)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, mT, Offset.sub_below _ (by decide) (by decide)⟩
  have f₁ : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 416, 256⟩] u.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cK p, mK, kN_sub⟩
    · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
    · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
    · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
    · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
    · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
    · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
    · exact ⟨rS p, mS, fun _ h => h⟩
  have hframe := f₀.trans f₁
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d := by
    refine hframe.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega)) (fun q hq => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (Region.sub_prefix (by decide))
  refine ⟨h.restore (htr.trans k.rd) (show t.wr.tail = s.wr by rw [htw, k.wr]; rfl)
      (show t.sp + BitVec.ofNat 64 80 = s.sp by rw [htsp, k.sp]; exact BitVec.sub_add_cancel _ _)
      (fun r hr h30 => (hg r hr h30).trans (k.gpr r (by revert r hr; decide)))
      (fun r hr => (hvs r hr).trans (k.vcs r hr)) (hframe.sub (key_frame_sub h))
      ((hword 0 (by decide)).trans h.state.remaining)
      ((hword 8 (by decide)).trans h.state.len) ((hword 16 (by decide)).trans h.state.cap) (.inl rfl) rfl
      h.state.remaining_le, hstat, hout, hframe⟩

end VG.Proof.RsaKeyGen.AArch64.Generate

/-! ## After a prime's search (AArch64)

The loop's states: one about to search (`GenIter`), with a measure that each
step that goes on lowers (`genMeasure`), and one that ended the key search
with `final` (`GenDone`). After a search and the count of the octets it
consumed (`Mid`): the frame for the octets consumed so far and the search's
counted candidates left, and the key's buffer.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld st mov movi)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

/-- A loop state that ended the key search with `final`: the frame for its
consumption and its state for the next call, its status in the frame, the
key's buffer, and its request in the state. -/
def GenDone (p : GenPublic) (original : State) (final : KeySearchResult) (s : State) : Prop :=
  GenFrame p original final.used final.progress s ∧ word s.mem p.F 80 = BitVec.ofNat 64 final.keyStatus ∧
    Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final ∧
    ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested

/-- What each step that goes on lowers: the octets left of the tape, then the
generations left. -/
def genMeasure (p : GenPublic) (used : Nat) (st : KeyProgress) : Nat := (p.randLen - used) * 2 ^ 64 + st.left

/-- The loop's invariant, at the measure `n`. -/
def GenInv (p : GenPublic) (original : State) (final : KeySearchResult) (n : Nat) (s : State) : Prop :=
  ∃ used st, n = genMeasure p used st ∧ GenIter p original final used st s

/-- What a prime's search leaves: its prime's octets, or zeros. -/
def outBytes (L : Nat) (r : PrimeSearchResult) : List Byte :=
  match r.outcome with
  | .accepted c => Spec.Rsa.i2osp c L
  | _ => List.replicate L 0

/-- The search of the progress' prime from octet `used`. -/
abbrev rOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : PrimeSearchResult :=
  primeOf p.L p.eB st ((genRand original).drop used)

/-- After a search and the count of the octets it consumed. -/
structure Mid (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (u : State) : Prop where
  frame : GenFrame p original (used + (rOf p original used st).used)
    ⟨st.left, st.phase, (rOf p original used st).remaining⟩ u
  final : ∃ tr, final = (tailOf p original used st).consume used tr
  low : Spec.Rsa.bytesAt u.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0
  slot4 : Spec.Rsa.bytesAt u.mem (p.slot 4) p.L =
    (match st.phase with
      | .p => outBytes p.L (rOf p original used st)
      | .q pB => pB)
  slot5 : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L =
    (match st.phase with
      | .p => List.replicate p.L 0
      | .q _ => outBytes p.L (rOf p original used st))
  high : Spec.Rsa.bytesAt u.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0
  req : ∃ requested, word u.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (rOf p original used st).Requests (primeEntropy p.L) requested

/-! ### The key's buffer -/

theorem bytesAt_add (m : Mem) (a : Addr) (x y : Nat) :
    Spec.Rsa.bytesAt m a (x + y) = Spec.Rsa.bytesAt m a x ++ Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

/-- The key's buffer: the low four slots, `p`'s, `q`'s and the high three. -/
theorem key_bytes (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) = Spec.Rsa.bytesAt m p.kp (4 * p.L) ++
      Spec.Rsa.bytesAt m (p.slot 4) p.L ++ Spec.Rsa.bytesAt m (p.slot 5) p.L ++
      Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) := by
  rw [show 9 * p.L = 4 * p.L + p.L + p.L + 3 * p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]

/-- The key's buffer, as the key's outputs. -/
theorem key_outs (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) =
      ((keyOutsOf p).map fun o => Spec.Rsa.bytesAt m o.1 o.2).flatten := by
  simp only [keyOutsOf, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show 9 * p.L = 2 * p.L + 2 * p.L + p.L + p.L + p.L + p.L + p.L by omega]
  rw [bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    show 2 * p.L + 2 * p.L = 4 * p.L by omega, show 4 * p.L + p.L = 5 * p.L by omega,
    show 5 * p.L + p.L = 6 * p.L by omega, show 6 * p.L + p.L = 7 * p.L by omega,
    show 7 * p.L + p.L = 8 * p.L by omega]
  simp only [List.append_assoc]

/-! ### After the search -/

section

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- A region of the key's buffer apart from the search's output is kept
through the search. -/
theorem search_kept (h : GenLive p original used st s) (hm : Frame (searchChanges p st) s.mem t.mem)
    {R : Region} (hR : Region.Sub R (cK p)) (hO : R.Disjoint (rO p st)) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have hf := h.input.cfacts
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, -, -⟩ := hst
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine hm.bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hO
  · exact hf.kU.sub_left hR
  · exact hf.kS.sub_left hR
  · exact (hf.kT.sub_left hR).sub_right rT_sub
  · exact (sK.sub_left hR).sub_right
      (show Region.Sub (⟨p.sp - BitVec.ofNat 64 416, 256⟩ : Region) (cStack p) from Region.sub_prefix (by decide))

theorem genRand_length (h : GenFrame p original used st s) : (genRand original).length = p.randLen := by
  rw [← h.random]; simp [Spec.Rsa.bytesAt]

theorem rOf_used_le (h : GenFrame p original used st s) : used + (rOf p original used st).used ≤ p.randLen := by
  have h2 : (rOf p original used st).used ≤ p.randLen - used := by
    have := primeSearch_used_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
    rw [List.length_drop, genRand_length h] at this
    exact this
  have := h.used_le
  omega

/-- The key's buffer and the state's request through the count of the octets
consumed. -/
theorem head_kept (h : GenFrame p original used st s) {u : State} {v : BitVec 64}
    (hm : u.mem = writeFrame s.mem p.F [(8, v)]) {R : Region} (hR : Region.Sub R (cK p)) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  rw [hm]
  exact bytes_kept (writeFrame_frame _ _ _ fun e he => by
    obtain rfl := List.mem_singleton.mp he; show 8 < 20; decide) (h.frame_key.sub_right hR) hn

theorem slot_disj (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.slot i, a⟩ : Region).Disjoint ⟨p.slot j, b⟩ := kk hf h ha hb

theorem low_disj (hf : CFacts p) {j b : Nat} (h : 4 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.kp, 4 * p.L⟩ : Region).Disjoint ⟨p.slot j, b⟩ := by
  have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

end

/-- The status and the count of the octets consumed, after the search. -/
theorem after_head {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (.block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8, .add .x .x12 .x12 .x10,
      stf .x12 8]) t fun u =>
      u.gpr .x9 = BitVec.ofNat 64 (rOf p original used st).status ∧
        u.gpr .x10 = BitVec.ofNat 64 (rOf p original used st).used ∧ Mid p original final used st u := by
  obtain ⟨hl, hfin⟩ := hi
  have hf := hl.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := rOf_used_le hl.toGenFrame
  refine WP.mono (head_ok ha.frame ha.status ha.usedw) fun u ⟨⟨hx9, hx10, hm⟩, k⟩ => ⟨hx9, hx10, ?_⟩
  rw [SearchInit.add_ofNat] at hm
  have hb : ∀ e ∈ [(8, BitVec.ofNat 64 (used + (rOf p original used st).used))], e.1 < 20 := by
    intro e he; obtain rfl := List.mem_singleton.mp he; show 8 < 20; decide
  have hhead : ∀ {R : Region}, Region.Sub R (cK p) → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt t.mem R.base R.len :=
    fun hR hn => head_kept ha.frame hm hR hn
  have hkey := hl.key
  have hlow : Spec.Rsa.bytesAt t.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [← hkey.low]
    refine search_kept hl ha.mem (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) ?_ (by
      show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact low_disj hf (by decide) (by omega)
    · exact low_disj hf (by decide) (by omega)
  have hsplit : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) =
      Spec.Rsa.bytesAt s.mem (p.slot 5) p.L ++ Spec.Rsa.bytesAt s.mem (p.slot 6) (3 * p.L) := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega]
  have hhigh5 := hkey.high
  rw [hsplit, show 4 * p.L = p.L + 3 * p.L by omega, ← List.replicate_append_replicate] at hhigh5
  obtain ⟨h5s, h6s⟩ := List.append_inj hhigh5 (by simp [Spec.Rsa.bytesAt]) |>.imp id id
  have hhigh : Spec.Rsa.bytesAt t.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0 := by
    rw [← h6s]
    refine search_kept hl ha.mem (R := ⟨p.slot 6, 3 * p.L⟩) (kSlot_sub (by omega)) ?_ (by
      show 3 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact slot_disj hf (by omega) (by omega) (by omega)
    · exact slot_disj hf (by omega) (by omega) (by omega)
  have hout := ha.out
  have hs4 : Spec.Rsa.bytesAt t.mem (p.slot 4) p.L =
      (match st.phase with
        | .p => outBytes p.L (rOf p original used st)
        | .q pB => pB) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      have ho : outOf p ⟨left, .p, remaining⟩ = p.slot 4 := rfl
      rw [ho] at hout
      rw [hout]; rfl
    | q pB =>
      rw [← hkey.other pB rfl]
      exact search_kept hl ha.mem (R := ⟨p.slot 4, p.L⟩) (kSlot_sub (by omega))
        (slot_disj hf (by omega) (by omega) (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
  have hs5 : Spec.Rsa.bytesAt t.mem (p.slot 5) p.L =
      (match st.phase with
        | .p => List.replicate p.L 0
        | .q _ => outBytes p.L (rOf p original used st)) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      rw [← h5s]
      exact search_kept hl ha.mem (R := ⟨p.slot 5, p.L⟩) (kSlot_sub (by omega))
        (slot_disj hf (by omega) (by omega) (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
    | q pB =>
      have ho : outOf p ⟨left, .q pB, remaining⟩ = p.slot 5 := rfl
      rw [ho] at hout
      rw [hout]; rfl
  obtain ⟨req, hreq, hreqs⟩ := ha.req
  refine ⟨ha.frame.store hle _ hb (by intro e he; obtain rfl := List.mem_singleton.mp he; show 9 ≠ 8; decide) hm k
      (by decide) (by rw [hm]; exact slots_used ha.frame _ [] (by simp) (by simp)),
    hfin, ?_, ?_, ?_, ?_, ⟨req, ?_, hreqs⟩⟩
  · rw [hhead (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) (by show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hlow
  · rw [hhead (R := ⟨p.slot 4, p.L⟩) (kSlot_sub (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hs4
  · rw [hhead (R := ⟨p.slot 5, p.L⟩) (kSlot_sub (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hs5
  · rw [hhead (R := ⟨p.slot 6, 3 * p.L⟩) (kSlot_sub (by omega)) (by show 3 * p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hhigh
  · rw [hm]
    refine Eq.trans ((writeFrame_frame _ _ _ hb).readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hreq
    obtain rfl := List.mem_singleton.mp hq
    exact ha.frame.input.frame_state.symm

theorem Mid.keep {p : GenPublic} {original u v : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (h : Mid p original final used st u) {rs : List Reg} (kp : Keep rs u v) (hm : v.mem = u.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : Mid p original final used st v := by
  refine ⟨h.frame.keep kp hm hregs, h.final, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.low, h.slot4, h.slot5, h.high, h.req]

end VG.Proof.RsaKeyGen.AArch64.Generate

/-! ## How a step ends (AArch64)

Zeros at the whole key's buffer (`clearAll`); the end of the key search
(`finishWith`), to `GenDone`; the start of the next prime's search, to a loop
state of a lower measure; and the branches after a search that asked for
entropy, was exhausted, or accepted `p`.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld st mov movi)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem setAll_ok (h : GenFrame p original used st s) :
    WP isa (.block [ldf .x9 0, ldf .x10 1, stf .x9 12, .lsl .x .x11 .x10 3, .add .x .x11 .x11 .x10,
      stf .x11 13]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L)] ∧
        Keep [.x9, .x10, .x11] s t := by
  have hl := h.frame_ld
  have hs := h.frame_st
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h0 h1
  refine WP.keep [.x9, .x10, .x11] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, hl 0 (by decide), hl 8 (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

/-- `clearAll`: zeros at the whole key's buffer. -/
theorem clearAll_ok (h : GenFrame p original used st s) :
    WP isa clearAll s fun t => GenFrame p original used st t ∧
      Spec.Rsa.bytesAt t.mem p.kp (9 * p.L) = List.replicate (9 * p.L) 0 ∧
      Frame [cK p, p.frame] s.mem t.mem := by
  have hn := h.key_nowrap
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have hkr := h.key_region
  have h9 : BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L = BitVec.ofNat 64 (9 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]; congr 1; omega
  unfold clearAll
  refine WP.seq (WP.mono (setAll_ok h) fun t1 ⟨hm1, k1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 (by decide)
  rw [h9] at w13
  refine WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega)) (by omega) (by omega))
    fun t2 ⟨g2, z2, f2, _, _⟩ => ⟨g2, bytes_zero z2, ?_⟩
  refine (f1.sub fun r hr => ?_).trans (f2.sub fun r hr => ?_)
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩

end

/-- The state's word `j` through stores to the state and the frame. -/
theorem stores_word {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv)
    (j : Nat) (hj : j < 7) :
    word (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.stp (8 * j) =
      frameValue sv j (word s.mem p.stp (8 * j)) := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hnst := h.input.state_nowrap
  rw [← writeFrame_word _ _ _ hsb j (by omega)]
  exact (writeFrame_frame _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
    (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact h.input.frame_state.symm) (by decide)

/-- The key's buffer through stores to the state and the frame. -/
theorem stores_key {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv)
    {j n : Nat} (hj : j * p.L + n ≤ 9 * p.L) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) (p.kp + BitVec.ofNat 64 (j * p.L)) n =
      Spec.Rsa.bytesAt s.mem (p.kp + BitVec.ofNat 64 (j * p.L)) n := by
  have hf := h.input.cfacts
  refine stores_bytes p s.mem (R := ⟨p.kp + BitVec.ofNat 64 (j * p.L), n⟩) hv ?_ ?_ (by have := hf.nK; simp; omega)
  · exact (hf.kT.symm.sub_right (slot_sub _ hj)).sub_left (Region.sub_prefix (by decide))
  · exact h.frame_key.sub_right (slot_sub _ hj)

/-- The key's buffer through stores to the state and the frame. -/
theorem stores_key9 {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.kp (9 * p.L) =
      Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) := by
  have := stores_key h hv (j := 0) (n := 9 * p.L) (by omega)
  rwa [Nat.zero_mul, ← kp_zero] at this

/-- `finishWith status`: the key search ended with `final`. -/
theorem finish_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0)
    (hkey : Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (.block (finishWith status)) s (GenDone p original final) := by
  refine WP.mono (finishWith_ok h hstat) fun t ⟨hm, k⟩ => ?_
  have hv : StateStores [(4, BitVec.ofNat 64 0), (5, BitVec.ofNat 64 0)] [(10, BitVec.ofNat 64 status)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have h0 := h.state.remaining
  rw [hr0] at h0
  have hg : GenFrame p original u ⟨0, .p, 0⟩ t :=
    h.setState hv hm k (by decide) h0 rfl rfl (Nat.zero_le _) (by decide)
  obtain ⟨req, hw, hr⟩ := hreq
  refine ⟨by rw [hu, hpr]; exact hg, ?_, ?_, ⟨req, ?_, hr⟩⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide), hs]
    rfl
  · rw [hm, stores_key9 h hv, hkey]
  · rw [hm]
    exact (stores_word h hv 3 (by decide)).trans hw

/-- The start of the next prime's search, for the progress `st'`: a loop
state, its status 4. -/
theorem cont_of {p : GenPublic} {original s t : State} {u : Nat} {st st' : KeyProgress}
    (h : GenFrame p original u st s) {sv : List (Nat × BitVec 64)}
    (hv : StateStores sv [(10, BitVec.ofNat 64 4)])
    (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F [(10, BitVec.ofNat 64 4)])
    {rs : List Reg} (kp : Keep rs s t) (hregs : ∀ reg ∈ preserved, reg ∉ rs)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64)
    (hlow : Spec.Rsa.bytesAt s.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0)
    (hhigh : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hother : ∀ pB, st'.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB)
    (hreq : word s.mem p.stp 24 = BitVec.ofNat 64 0) :
    word t.mem p.F 80 = BitVec.ofNat 64 4 ∧ GenLive p original u st' t ∧
      word t.mem p.stp 24 = BitVec.ofNat 64 0 := by
  obtain ⟨hL1, -, -⟩ := h.len_valid
  have hg' := h.setState hv hm kp hregs h0 h4 h5 hrem hlt
  have h3 : ∀ e ∈ sv, 3 ≠ e.1 := fun e he heq => by rcases hv.1 e he with h | h | h <;> omega
  refine ⟨?_, ⟨hg', ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; decide) 10 (by decide)]
    rfl
  · have := stores_key h hv (j := 0) (n := 4 * p.L) (by omega)
    rw [Nat.zero_mul, ← kp_zero] at this
    rw [hm, this, hlow]
  · rw [hm, stores_key h hv (j := 5) (n := 4 * p.L) (by omega), hhigh]
  · intro pB hpB
    rw [hm, stores_key h hv (j := 4) (n := p.L) (by omega), hother pB hpB]
  · rw [hm]
    exact (stores_word h hv 3 (by decide)).trans ((frameValue_unchanged _ _ _ h3).trans hreq)

/-! ### A prime's search that asked for entropy or was exhausted -/

/-- How the key search goes on after the prime's search `r` from the progress
`st`: to the progress `st'`, with `e` this step's trace. -/
def NextPub (st : KeyProgress) (r : PrimeSearchResult) (st' : KeyProgress) (e : List Nat) : Prop :=
  (r.outcome = .exhausted ∧ st'.left = st.left - 1 ∧ st'.phase = .p ∧ e = primeEntry r) ∨
  (∃ c, r.outcome = .accepted c ∧ st.phase = .p ∧ st'.left = st.left ∧ phaseWord st'.phase = 1 ∧
    e = primeEntry r) ∨
  (∃ c pB, r.outcome = .accepted c ∧ st.phase = .q pB ∧ st'.left = st.left ∧ st'.phase = .p ∧
    e = primeEntry r ++ [1, 2])

/-- After a step that goes on: its status 4, and the loop state of the next
prime's search, of a lower measure. -/
structure Cont (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop where
  status : word t.mem p.F 80 = BitVec.ofNat 64 4
  req : word t.mem p.stp 24 = BitVec.ofNat 64 0
  next : ∃ st' e, GenLive p original (used + (rOf p original used st).used) st' t ∧
    genMeasure p (used + (rOf p original used st).used) st' < genMeasure p used st ∧
    tailOf p original used st =
      (tailOf p original (used + (rOf p original used st).used) st').consume (rOf p original used st).used e ∧
    st'.remaining = limitOf p.L p.eB ∧ NextPub st (rOf p original used st) st' e
  final : ∃ tr, final = (tailOf p original used st).consume used tr

/-- Whether the key search goes on after the prime's search from `st`: to the
next generation, to `q` after `p`, or to both primes again after a `d` too
small. -/
def ContSpec (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : Prop :=
  ((rOf p original used st).outcome = .exhausted ∧ ¬st.left < 2) ∨
  (∃ c, (rOf p original used st).outcome = .accepted c ∧ (rOf p original used st).used ≠ 0 ∧
    (st.phase = .p ∨ ∃ pB, st.phase = .q pB ∧ keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) = .inr ()))

/-- After a step: the next prime's search, or the key search ended with
`final`. -/
def Classified (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  (ContSpec p original used st ∧ Cont p original final used st t) ∨
    (¬ContSpec p original used st ∧ GenDone p original final t)

/-- `fail status`: zeros at the key's buffer, and the key search ended with
`final`. -/
theorem fail_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0) (hz : keySearchBytes p.L final = List.replicate (9 * p.L) 0)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (fail status) s (GenDone p original final) := by
  have hf := h.input.cfacts
  unfold fail
  refine WP.seq (WP.mono (clearAll_ok h) fun w ⟨g, z, fr⟩ => ?_)
  obtain ⟨req, hw, hr⟩ := hreq
  refine finish_done g hstat hu hpr hs hr0 (z.trans hz.symm) ⟨req, ?_, hr⟩
  refine Eq.trans (fr.readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
    (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
    (fun q hq => ?_) (by decide)) hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hf.kT.symm
  · exact h.input.frame_state.symm

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem rOf_status (r : PrimeSearchResult) : r.status = r.outcome.status := rfl

/-- The search asked for more entropy: so does the key search. -/
theorem classify_entropy (hm : Mid p original final used st u)
    (hx9 : u.gpr .x9 = BitVec.ofNat 64 (rOf p original used st).status) {k a : Nat}
    (ho : (rOf p original used st).outcome = .entropy k a) :
    WP isa (.block [stf .x9 10]) u (Classified p original final used st) := by
  have hs0 : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
  have hrem : (rOf p original used st).remaining = k := by
    simp only [PrimeSearchResult.remaining, ho]
  have hframe := hm.frame
  rw [hrem] at hframe
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_entropy (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
  have hfinal : final = ⟨.entropy ⟨st.left, st.phase, k⟩ a, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  refine WP.mono (storeStatus_ok hframe hx9) fun t ⟨htm, k'⟩ => Or.inr ⟨?_, ?_⟩
  · rintro (⟨h, -⟩ | ⟨c, h, -⟩) <;> rw [ho] at h <;> cases h
  rw [hs0] at htm
  have hv : StateStores [] [(10, BitVec.ofNat 64 0)] := by
    constructor
    · simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hg : GenFrame p original (used + (rOf p original used st).used) ⟨st.left, st.phase, k⟩ t :=
    hframe.setState hv htm k' (by decide) hframe.state.remaining
      hframe.state.phase hframe.state.left hframe.state.remaining_le hframe.state.left_lt
  obtain ⟨req, hw, hr⟩ := hm.req
  subst hfinal
  refine ⟨hg, ?_, ?_, ⟨req, ?_, ?_⟩⟩
  · rw [htm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide)]
    rfl
  · rw [htm, stores_key9 hframe hv, key_bytes, hm.low, hm.slot4, hm.slot5, hm.high]
    have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
      simp only [outBytes, ho]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only [hout, keySearchBytes, List.replicate_append_replicate]
      congr 1; omega
    | q pB =>
      simp only [hout, keySearchBytes, List.append_assoc, List.replicate_append_replicate]
      congr 3; omega
  · rw [htm]; exact (stores_word hframe hv 3 (by decide)).trans hw
  · simp only [Spec.Entropy.Result.Requests, ho] at hr ⊢
    exact hr

/-- The search was exhausted, and so is the key search: its last generation. -/
theorem classify_last (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : st.left < 2) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_last (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- The search was exhausted: the next generation, from `p`. -/
theorem classify_next (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : ¬st.left < 2) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
      (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, BitVec.ofNat 64 4)])
    {rs : List Reg} (kp : Keep rs u t) (hregs : ∀ reg ∈ preserved, reg ∉ rs) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hks := ks_exhausted_next (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by omega)
  have hv : StateStores [(5, BitVec.ofNat 64 (st.left - 1)), (0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 0)] [(10, BitVec.ofNat 64 4)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
    simp only [outBytes, ho]
  have hle := hm.frame.used_le
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, hm.slot5, hm.high,
      ← List.replicate_append_replicate]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => rfl
    | q pB => simp only [hout]
  have hreq0 : word u.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [hw', this]
  obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left - 1, .p, limitOf p.L p.eB⟩) hm.frame hv htm kp hregs rfl
    rfl rfl (Nat.le_refl _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hm.frame.state.left_lt) hm.low hhigh5
    (fun _ h => by cases h) hreq0
  refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st), hlive, ?_, ?_, rfl, .inl ⟨ho, rfl, rfl, rfl⟩⟩, hm.final⟩
  · unfold genMeasure
    dsimp only
    have hmul : (p.randLen - (used + (rOf p original used st).used)) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [tailOf, hks, tailOf, List.drop_drop]

end

/-! ### A generation exhausted, or `p` accepted -/

/-- One generation fewer, and the next prime's search from `p`. -/
theorem dec_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hx8 : s.gpr .x8 = p.stp)
    (hx10 : s.gpr .x10 = BitVec.ofNat 64 st.left) (hl : 2 ≤ st.left) :
    WP isa (.block (([.subImm .x .x10 .x10 1, VG.Impl.Bignum.AArch64.st .x10 .x8 40] : List Instr) ++ nextPrime 0)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
        (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, BitVec.ofNat 64 4)] ∧
        Keep [.x8, .x10, .x11] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.header (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl11 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 88) 8 := scr.ld (d := 88) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs0 : InRegions s.wr (p.stp + BitVec.ofNat 64 0) 8 := sst.st (d := 0) (by decide)
  have hs00 : InRegions s.wr p.stp 8 := by simpa only [BitVec.add_zero] using hs0
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  simp only [Nat.reduceMul] at h7 h11
  have hlt := h.state.left_lt
  have hsub : BitVec.ofNat 64 st.left - 1#64 = BitVec.ofNat 64 (st.left - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, show (1#64).toNat = 1 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show st.left - 1 < 2 ^ 64 by omega)]
    omega
  have hnF : p.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hnS : p.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 160) :
      (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 d) 64 =
        s.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨p.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega))).readW (r := p.frame)
      (Offset.contains_base _ hd (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact h.input.frame_state) (by decide)
  have hk7 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 56) 64 =
      p.stp := fun v => (hkeep v 56 (by decide)).trans h7
  have hk11 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 88) 64 =
      BitVec.ofNat 64 (limitOf p.L p.eB) := fun v => (hkeep v 88 (by decide)).trans h11
  refine WP.keep [.x8, .x10, .x11] ?_ (by decide) (by decide) (by decide +kernel)
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]
  brun [ldf, stf, h.x19, hx8, hx10, hsub, hl7, hl11, hs10, hs0, hs00, hs4, hs5, hk7, hk11,
    imm64 (show 0 < 65536 by decide), imm64 (show 4 < 65536 by decide)]
  simp only [off, Nat.reduceMul, BitVec.add_zero]

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- `exhaustedGen`: the key search exhausted, or the next generation. -/
theorem classify_exhausted (hm : Mid p original final used st u)
    (ho : (rOf p original used st).outcome = .exhausted) :
    WP isa exhaustedGen u (Classified p original final used st) := by
  unfold exhaustedGen
  refine WP.seq (WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hx8, hx10, hmem⟩, k⟩ => ?_)
  have hv := hm.keep k hmem
  refine WP.ite (decide (st.left < 2)) (by
    rw [eval_zero, hb]; by_cases h2 : 2 ≤ st.left <;> simp [h2]; omega) (fun hl => ?_) (fun hl => ?_)
  · refine WP.mono (classify_last hv ho (of_decide_eq_true hl)) fun _ h => Or.inr ⟨?_, h⟩
    rintro (⟨-, h⟩ | ⟨c, h, -⟩)
    · exact h (of_decide_eq_true hl)
    · rw [ho] at h; cases h
  · have hl' := of_decide_eq_false hl
    refine WP.mono (dec_ok hv.frame hx8 hx10 (by show 2 ≤ st.left; omega)) fun t ⟨htm, k2⟩ =>
      Or.inl ⟨.inl ⟨ho, hl'⟩, ?_⟩
    exact classify_next hv ho hl' htm k2 (by decide)

theorem drop_lt {rest : List Byte} {n : Nat} (h0 : 0 < n) (hn : n ≤ rest.length) :
    (rest.drop n).length < rest.length := by
  rw [List.length_drop]; omega

theorem measure_lt (p : GenPublic) {used n : Nat} {st st' : KeyProgress} (h0 : 0 < n)
    (hn : used + n ≤ p.randLen) (hl : st'.left ≤ st.left) :
    genMeasure p (used + n) st' < genMeasure p used st := by
  unfold genMeasure
  have hmul : (p.randLen - (used + n) + 1) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

/-- A prime accepted having read nothing: the key search is exhausted. -/
theorem classify_none (hm : Mid p original final used st u) {c : Nat}
    (ho : (rOf p original used st).outcome = .accepted c) (h0 : (rOf p original used st).used = 0) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_accepted_none (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by show ¬(List.drop (rOf p original used st).used _).length < _; rw [h0, List.drop_zero]; omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- `p` accepted: `q` next. -/
theorem classify_p (hm : Mid p original final used st u) {c : Nat}
    (ho : (rOf p original used st).outcome = .accepted c) (hpos : 0 < (rOf p original used st).used)
    (hph : st.phase = .p) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 1)]) p.F [(10, BitVec.ofNat 64 4)])
    {rs : List Reg} (kp : Keep rs u t) (hregs : ∀ reg ∈ preserved, reg ∉ rs) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hks := ks_accepted_p (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (drop_lt hpos hrest) hph
  have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 1)]
      [(10, BitVec.ofNat 64 4)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs4
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, hs5, hm.high,
      ← List.replicate_append_replicate]
  have hreq0 : word u.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [hw', this]
  obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left, .q (Spec.Rsa.i2osp c p.L), limitOf p.L p.eB⟩) hm.frame
    hv htm kp hregs rfl rfl hm.frame.state.left (Nat.le_refl _) hm.frame.state.left_lt hm.low hhigh5
    (fun pB h => by cases h; exact hs4) hreq0
  refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st), hlive, measure_lt p hpos hle (Nat.le_refl _), ?_, rfl,
    .inr (.inl ⟨c, ho, hph, rfl, rfl, rfl⟩)⟩, hm.final⟩
  rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.AArch64.Generate

/-! ## The key from `p` and `q`, and the loop (AArch64)

After `q`'s search accepted a prime: the key, which ends the key search with
it or with its failed check, or, for a `d` too small, both primes again in
the same generation. Each iteration searches for the progress' prime,
classifies the result, and goes on while the status is 4, to a state of a
lower measure; the loop ends with the key search's result.
-/
namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld mov movi)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ### The status's tests -/

theorem sub_ofNat_beq {w k : Nat} (hw : w < 2 ^ 64) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 w - BitVec.ofNat 64 k == 0) = decide (w = k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' := congrArg (· + BitVec.ofNat 64 k) h
    simp only [BitVec.sub_add_cancel] at h'
    have := congrArg BitVec.toNat h'
    simp [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hk] at this
    omega
  · rintro rfl; exact BitVec.sub_self _

/-- `x12 := x9 − k`: zero exactly when the status is `k`. -/
theorem sub_guard {s : State} {w k : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (hs : s.gpr .x9 = BitVec.ofNat 64 w) (h64 : w < 2 ^ 64) :
    WP isa (.block [.subImm .x .x12 .x9 k]) s fun t =>
      (isa.eval (.zero .x .x12) t = some (decide (w = k)) ∧ t.mem = s.mem) ∧ Keep [.x12] s t := by
  have hk64 : k < 2 ^ 64 := by omega
  rcases hk with rfl | rfl | rfl
  all_goals
  refine WP.keep [.x12] ?_ (by decide) (by decide) (by decide +kernel)
  brun [hs]
  show isa.eval (.zero .x .x12) _ = _
  rw [eval_zero, RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, sub_ofNat_beq h64 hk64]

/-- The key's status, in `x9`, and whether it is 1. -/
theorem keyStatus_guard {s : State} {status : Nat} (hs : ((s.gpr .x0).setWidth 32).toNat = status) :
    WP isa (.block [.addImm .w .x9 .x0 0, .subImm .x .x12 .x9 1]) s fun t =>
      (t.gpr .x9 = BitVec.ofNat 64 status ∧ isa.eval (.zero .x .x12) t = some (decide (status = 1)) ∧
        t.mem = s.mem) ∧ Keep [.x9, .x12] s t := by
  have hax : ((s.gpr .x0).setWidth 32).setWidth 64 = BitVec.ofNat 64 status := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]
  have h64 : status < 2 ^ 64 := by
    rw [← hs]; exact Nat.lt_trans (BitVec.isLt _) (by decide)
  refine WP.keep [.x9, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  brun [exec_addImm_w, hax]
  show isa.eval (.zero .x .x12) _ = _
  rw [eval_zero, RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, sub_ofNat_beq h64 (show 1 < 2 ^ 64 by decide)]

theorem low_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = 2 * p.L + 2 * p.L by omega, bytesAt_add, ← List.replicate_append_replicate]
  rw [h (p.kp, 2 * p.L) (by simp [keyOutsOf]), h (p.slot 2, 2 * p.L) (by simp [keyOutsOf])]

theorem high_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  have e (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; rw [Nat.succ_mul]
  rw [show 4 * p.L = p.L + p.L + p.L + p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L + p.L) = p.slot 8 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L) = p.slot 7 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, e 5,
    h (p.slot 5, p.L) (by simp [keyOutsOf]), h (p.slot 6, p.L) (by simp [keyOutsOf]),
    h (p.slot 7, p.L) (by simp [keyOutsOf]), h (p.slot 8, p.L) (by simp [keyOutsOf]),
    List.replicate_append_replicate, List.replicate_append_replicate, List.replicate_append_replicate]

/-! ### The key -/

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After `q`: the key. -/
theorem classify_key [Key.KeyProof] (hm : Mid p original final used st u) {c : Nat} {pB : List Byte}
    (ho : (rOf p original used st).outcome = .accepted c) (hpos : 0 < (rOf p original used st).used)
    (hph : st.phase = .q pB) :
    WP isa (.seq (keyRun keyCall) afterKey) u (Classified p original final used st) := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  obtain ⟨tr, hfin⟩ := hm.final
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hg := drop_lt hpos hrest
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hr0
  refine WP.seq (WP.mono (key_run hm.frame) fun v hk => ?_)
  have hkey : keyOf p u.mem = keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L) := by
    simp only [keyOf, hs4, hs5]
  have hstat := hk.status
  have hout := hk.out
  rw [hkey] at hstat hout
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have hwv : word v.mem p.stp 24 = BitVec.ofNat 64 0 := by
    refine Eq.trans (hk.mem.readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (Region.sub_prefix (by decide))
  unfold afterKey
  refine WP.seq (WP.mono (keyStatus_guard hstat) fun w ⟨⟨hx9, he1, hmem1⟩, k1⟩ => ?_)
  have hgw := hk.frame.keep k1 hmem1
  have hfin' : ∀ {r : KeySearchResult}, keySearch p.L p.eB st ((genRand original).drop used) = r →
      final = r.consume used tr := fun h => by rw [hfin, tailOf, h]
  have hfin0 := hm.final
  cases hkf : keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) with
  | inl res =>
    cases res with
    | ok key =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .ok key) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hout
      refine WP.ite true he1 (fun _ => ?_) (fun h => by cases h)
      refine WP.mono (finish_done (final := final) hgw (by decide) (by rw [hks]; rfl) (by rw [hks]; rfl)
        (by rw [hks]; rfl) hrem ?_ ⟨0, by rw [hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr ⟨?_, h⟩
      · rw [hmem1, key_outs, hout, hks]
        simp only [keySearchBytes, Spec.Entropy.Result.consume, keyBytes, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
      · rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
        · rw [ho] at h; cases h
        · rw [hph] at h'; cases h'
        · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
    | error fl =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .error fl) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hx9
      refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
      refine WP.seq (WP.mono (sub_guard (k := 2) (by decide) hx9 (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
      have hgw2 := hgw.keep k2 hmem2
      refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
      refine WP.mono (fail_done (final := final) hgw2 (by decide) (by rw [hks]; rfl) (by rw [hks]; rfl)
        (by rw [hks]; rfl) hrem (by rw [hks]; rfl)
        ⟨0, by rw [hmem2, hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
      · rw [ho] at h; cases h
      · rw [hph] at h'; cases h'
      · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
  | inr _ =>
    have hks := ks_accepted_small (L := p.L) (eB := p.eB) ho hg hph hkf
    simp only [keyOp, hkf, keyStatus] at he1 hx9 hout
    refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (sub_guard (k := 2) (by decide) hx9 (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
    have hgw2 := hgw.keep k2 hmem2
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (nextPrime_ok hgw2 (phase := 0) (by decide)) fun t ⟨htm, k3⟩ =>
      Or.inl ⟨.inr ⟨c, ho, by omega, .inr ⟨pB, hph, hkf⟩⟩, ?_⟩
    have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]
        [(10, BitVec.ofNat 64 4)] := by
      constructor
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
    obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left, .p, limitOf p.L p.eB⟩) hgw2 hv htm k3 (by decide)
      rfl rfl hgw2.state.left (Nat.le_refl _) hgw2.state.left_lt
      (by rw [hmem2, hmem1]; exact low_of_outs hout) (by rw [hmem2, hmem1]; exact high_of_outs hout)
      (fun _ h => by cases h) (by rw [hmem2, hmem1]; exact hwv)
    refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st) ++ [1, 2], hlive, measure_lt p hpos hle (Nat.le_refl _),
      ?_, rfl, .inr (.inr ⟨c, pB, ho, hph, rfl, rfl, rfl⟩)⟩, hfin0⟩
    rw [tailOf, hks, tailOf, List.drop_drop]

end

/-! ### The loop -/

section

variable {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After the search: what it leaves, classified. -/
theorem classify_ok [Key.KeyProof] (hi : GenIter p original final used st s)
    (ha : AfterSearch p original used st s t) :
    WP isa (classify keyCall) t (Classified p original final used st) := by
  have hf := hi.1.input.cfacts
  unfold classify
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (after_head hi ha) fun u ⟨hx9, hx10, hm⟩ => ?_)
  have hu64 : (rOf p original used st).used < 2 ^ 64 := by
    have := hm.frame.used_le; have := hf.rand64; omega
  cases ho : (rOf p original used st).outcome with
  | entropy k a =>
    have hs : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
    refine WP.ite true (by rw [eval_zero, hx9, hs]; rfl) (fun _ => classify_entropy hm hx9 ho) (fun h => by cases h)
  | exhausted =>
    have hs : (rOf p original used st).status = 3 := by rw [rOf_status, ho]; rfl
    rw [hs] at hx9
    refine WP.ite false (by rw [eval_zero, hx9]; rfl) (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (sub_guard (k := 3) (by decide) hx9 (by decide)) fun v ⟨⟨he2, hmem⟩, k⟩ => ?_)
    have hv := hm.keep k hmem
    exact WP.ite true he2 (fun _ => classify_exhausted hv ho) (fun h => by cases h)
  | accepted c =>
    have hs : (rOf p original used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs] at hx9
    refine WP.ite false (by rw [eval_zero, hx9]; rfl) (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (sub_guard (k := 3) (by decide) hx9 (by decide)) fun v ⟨⟨he2, hmem⟩, k⟩ => ?_)
    have hv := hm.keep k hmem
    have hx10' : v.gpr .x10 = BitVec.ofNat 64 (rOf p original used st).used := by
      rw [k.gpr _ (by decide)]; exact hx10
    refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
    refine WP.ite (decide ((rOf p original used st).used = 0)) (by rw [eval_zero, hx10', ofNat_beq_zero hu64])
      (fun h0 => ?_) (fun h0 => ?_)
    · refine WP.mono (classify_none hv ho (of_decide_eq_true h0)) fun _ h => Or.inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', -, hu, -⟩)
      · rw [ho] at h; cases h
      · exact hu (of_decide_eq_true h0)
    · have hpos : 0 < (rOf p original used st).used := by
        have := of_decide_eq_false h0; omega
      unfold accepted
      refine WP.seq (WP.mono (phase_ok hv.frame) fun x ⟨⟨hx10x, hmem4⟩, k4⟩ => ?_)
      have hx := hv.keep k4 hmem4
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p =>
        refine WP.ite true (by rw [eval_zero, hx10x]; rfl) (fun _ => ?_) (fun h => by cases h)
        refine WP.mono (nextPrime_ok hx.frame (phase := 1) (by decide)) fun y ⟨hym, k5⟩ =>
          Or.inl ⟨.inr ⟨c, ho, by omega, .inl rfl⟩, ?_⟩
        exact classify_p hx ho hpos rfl hym k5 (by decide)
      | q pB =>
        refine WP.ite false (by rw [eval_zero, hx10x]; rfl) (fun h => by cases h) (fun _ => ?_)
        exact classify_key hx ho hpos rfl

/-- The loop's test: the status, against 4. -/
theorem status_guard (h : GenFrame p original used st s) {w : Nat} (hw : word s.mem p.F 80 = BitVec.ofNat 64 w)
    (h64 : w < 2 ^ 64) :
    WP isa (.block [ldf .x9 10, .subImm .x .x9 .x9 4]) s fun t =>
      (isa.eval (.zero .x .x9) t = some (decide (w = 4)) ∧ t.mem = s.mem) ∧ Keep [.x9] s t := by
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 80) 8 := h.scr.ld (d := 80) (by decide)
  have hw' : s.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 w := hw
  refine WP.keep [.x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ldf, h.x19, hl, hw']
  show isa.eval (.zero .x .x9) _ = _
  rw [eval_zero, RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, sub_ofNat_beq h64 (show 4 < 2 ^ 64 by decide)]

theorem GenInv.keep {n : Nat} (h : GenInv p original final n s) {rs : List Reg} (kp : Keep rs s t)
    (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : GenInv p original final n t := by
  obtain ⟨used, st, hn, ⟨hl, hfin⟩⟩ := h
  refine ⟨used, st, hn, ⟨⟨hl.toGenFrame.keep kp hm hregs, ?_⟩, hfin⟩⟩
  rw [hm]; exact hl.key

theorem GenDone.keep (h : GenDone p original final s) {rs : List Reg} (kp : Keep rs s t)
    (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : GenDone p original final t := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨g.keep kp hm hregs, ?_, ?_, ?_⟩ <;> rw [hm]
  exacts [h1, h2, h3]

theorem keyStatus_lt (r : KeySearchResult) : r.keyStatus < 4 := by
  unfold KeySearchResult.keyStatus
  split <;> decide

end

/-- An iteration: the search, its classification and the loop's test. -/
theorem gen_iteration [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {original s : State}
    {final : KeySearchResult} {n : Nat} (h : GenInv p original final n s) :
    WP isa (iteration (searchCall v) keyCall) s fun t =>
      (isa.eval (.zero .x .x9) t = some false ∧ GenDone p original final t) ∨
      (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, GenInv p original final m t) := by
  obtain ⟨used, st, rfl, hi⟩ := h
  unfold iteration
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (search_run v hi.1) fun t ha => ?_)
  refine WP.seq (WP.mono (classify_ok hi ha) fun u hc => ?_)
  rcases hc with ⟨-, h4, -, ⟨st', e, hl', hm, htail, -, -⟩, ⟨tr, hfin⟩⟩ | ⟨-, hd⟩
  · refine WP.mono (status_guard hl'.toGenFrame h4 (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ => Or.inr ⟨hx, _, hm, ?_⟩
    refine GenInv.keep ⟨_, st', rfl, ⟨hl', tr ++ e, ?_⟩⟩ k hmem
    rw [hfin, htail, consume_consume]
  · have hlt := keyStatus_lt final
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega)) fun x ⟨⟨hx, hmem⟩, k⟩ => Or.inl ⟨?_, ?_⟩
    · refine hx.trans ?_; congr 1; simp only [decide_eq_false_iff_not]; omega
    · exact hd.keep k hmem

theorem gen_loop [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult}
    {n : Nat} (h : GenInv p original final n s) :
    WP isa (.loop (iteration (searchCall v) keyCall) (.zero .x .x9)) s (GenDone p original final) :=
  WP.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .zero .x .x9) (Q := GenDone p original final)
    (GenInv p original final) (fun _ _ h => gen_iteration v h) n s h

end VG.Proof.RsaKeyGen.AArch64.Generate
