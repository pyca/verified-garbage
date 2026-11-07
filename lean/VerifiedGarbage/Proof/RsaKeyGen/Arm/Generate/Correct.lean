module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top1
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Generate
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Correct
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.RsaKeyGen.Arm.SearchInit
import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.RsaKeyGen.Contract
meta import VerifiedGarbage.TCB.Arm.Target

/-! # The controller's correctness (ARMv7)

Its frame and loop states, entry and clearing, the prime search's and the
key's calls, the steps after each, the loop, and the whole controller.
-/

@[expose] public section

/-! ## The controller's public data and its loop states (ARMv7)

As on AArch64 (`Proof/RsaKeyGen/AArch64/Generate/Loop.lean`), but the
controller's working state is in the callee-saved registers (`r4`–`r10`,
and the status in `r11`), as the prime search's is
(`Proof/RsaKeyGen/Arm/Search/Data.lean`): it saves them in the frame it
pushes, of 40 bytes at `sp - 40`. Its memory moves only within what it may
write (`changes`).
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-- What two constant-time runs share: the arguments, the primes' octets and
the exponent. -/
structure GenPublic where
  kp : BitVec 32
  up : BitVec 32
  rp : BitVec 32
  B : BitVec 32
  stp : BitVec 32
  sp : BitVec 32
  L : Nat
  randLen : Nat
  Z : Nat
  eB : List Byte

def genOfState (s : State) : GenPublic where
  kp := s.gpr .r0
  up := s.gpr .r2
  rp := s.gpr .r3
  B := stackArg s 1
  stp := stackArg s 3
  sp := s.sp
  L := genLen s
  randLen := (stackArg s 0).toNat
  Z := (stackArg s 2).toNat
  eB := genE s

def GenInput (p : GenPublic) (s : State) : Prop := genPre s ∧ genOfState s = p

/-- The frame the controller pushes. -/
abbrev GenPublic.S1 (p : GenPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 40

/-- The state's base. -/
abbrev GenPublic.st (p : GenPublic) : Addr := State.addr p.stp

/-- The key's buffer's slot `j` (`p_len` octets each). -/
abbrev GenPublic.slot (p : GenPublic) (j : Nat) : Addr := State.addr p.kp + BitVec.ofNat 64 (j * p.L)

/-- The registers the controller pushes, in order. -/
abbrev pushRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- Where the pushed registers are, from `S1`. -/
abbrev slots : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.r12, 32), (.lr, 36)]

/-- The saved registers, in the frame at `S1`. -/
def Saved (m : Mem) (S1 : BitVec 32) (o : State) : Prop := Spill.Saved m (State.addr S1) o.gpr slots

/-- The regions the controller (and its callees) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [inStack s]

/-- The precondition's facts of numbers, in terms of the public data. -/
structure PreFacts (p : GenPublic) : Prop where
  room : 256 ≤ p.sp.toNat
  top : p.sp.toNat + 16 ≤ 2 ^ 32
  nK : p.kp.toNat + 9 * p.L ≤ 2 ^ 32
  nU : p.up.toNat + 8 ≤ 2 ^ 32
  nR : p.rp.toNat + p.randLen ≤ 2 ^ 32
  nS : p.B.toNat + p.Z * 8 ≤ 2 ^ 32
  nT : p.stp.toNat + 56 ≤ 2 ^ 32
  valid : primeLenValid p.L
  scr : Spec.Rsa.scratchWords (2 * p.L) ≤ p.Z
  randLen : p.randLen ≤ primeEntropy p.L

namespace GenInput

variable {p : GenPublic} {s : State}

theorem facts (h : GenInput p s) : PreFacts p := by
  obtain ⟨⟨room, top, -, -, -, -, -, nK, nU, nR, nS, nT, valid, k9, scr, -, -, -, rl⟩, rfl⟩ := h
  exact ⟨room, top, by change (s.gpr .r0).toNat + 9 * genLen s ≤ 2 ^ 32; omega, nU, nR, nS, nT, valid, scr, rl⟩

theorem sp_eq (h : GenInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem rd (h : GenInput p s) : s.rd = inReads s := h.1.2.2.1

theorem wr (h : GenInput p s) : s.wr = inWrites s := h.1.2.2.2.1

theorem writes_pairwise (h : GenInput p s) : (inWrites s).Pairwise Region.Disjoint := h.1.2.2.2.2.1

theorem write_disjoint (h : GenInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (inStack s).Disjoint r := h.1.2.2.2.2.2.2.1 r hr

theorem key_len (h : GenInput p s) : (s.gpr .r1).toNat = 9 * p.L := by
  rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem regions (h : GenInput p s) :
    inKey s = ⟨State.addr p.kp, 9 * p.L⟩ ∧ inUsed s = ⟨State.addr p.up, 8⟩ ∧
      inRand s = ⟨State.addr p.rp, p.randLen⟩ ∧ inScr s = ⟨State.addr p.B, p.Z * 8⟩ ∧
      inState s = ⟨p.st, 56⟩ := by
  have hk := h.key_len
  obtain ⟨-, rfl⟩ := h
  exact ⟨by simp only [inKey, hk]; rfl, rfl, rfl, rfl, rfl⟩

theorem read_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem reads_len (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) : r.len ≤ 2 ^ 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfr, -⟩ := h.1
  simp only [inReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [inRand, inArgs] <;> omega

theorem bytes_frame (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (h.read_disjoint hr) (h.reads_len hr) (List.mem_range.mp hi)

theorem random_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.rp) p.randLen = Spec.Rsa.bytesAt m (State.addr p.rp) p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

/-- The stack arguments, through what the controller may write. -/
theorem arg_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') {j : Nat} (hj : j < 4) :
    m'.readW (stackArgAddr s j) 32 = m.readW (stackArgAddr s j) 32 := by
  have hsp := h.1.2.1
  have hc : (inArgs s).Contains (stackArgAddr s j) 4 := by
    have e : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (4 * j) := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega)
    rw [e]
    exact Offset.contains_base _ (by omega) (by omega)
  exact hf.readW hc (h.read_disjoint (by simp [inReads])) (by decide)

end GenInput

/-- The phase's word in the state. -/
def phaseWord : KeyPhase → Nat
  | .p => 0
  | .q _ => 1

theorem phaseWord_le (ph : KeyPhase) : phaseWord ph ≤ 1 := by cases ph <;> simp only [phaseWord] <;> omega

/-- The state's words for the progress `st`, and the exponent. -/
structure StateOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  remaining : m.readW (off p.st 0) 64 = BitVec.ofNat 64 st.remaining
  len : m.readW (off p.st 8) 64 = BitVec.ofNat 64 p.L
  cap : m.readW (off p.st 16) 64 = BitVec.ofNat 64 (primeEntropy p.L)
  phase : m.readW (off p.st 32) 64 = BitVec.ofNat 64 (phaseWord st.phase)
  left : m.readW (off p.st 40) 64 = BitVec.ofNat 64 st.left
  e : Spec.Rsa.bytesAt m (off p.st 48) 8 = p.eB
  remaining_le : st.remaining ≤ limitOf p.L p.eB
  left_lt : st.left < 2 ^ 64

/-- The key's buffer for the progress `st`: zeros but `p`'s slot, which holds
`p` for `q`'s search. -/
structure KeyOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  low : Spec.Rsa.bytesAt m (State.addr p.kp) (4 * p.L) = List.replicate (4 * p.L) 0
  high : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0
  other : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB

/-- A state of the controller below its push: `used` octets consumed, the
progress `st` in the state, the arguments in `r4`–`r10`. The entry state is
functional-proof data only. -/
structure GenFrame (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) (s : State) : Prop where
  input : GenInput p o
  used_le : used ≤ p.randLen
  rd : s.rd = o.rd
  wr : s.wr = ⟨State.addr p.S1, 40⟩ :: o.wr
  sp : s.sp = p.S1
  r4 : s.gpr .r4 = p.kp
  r5 : s.gpr .r5 = BitVec.ofNat 32 p.L
  r6 : s.gpr .r6 = p.up
  r7 : s.gpr .r7 = p.rp
  r8 : s.gpr .r8 = BitVec.ofNat 32 used
  r9 : s.gpr .r9 = p.stp
  r10 : s.gpr .r10 = BitVec.ofNat 32 (limitOf p.L p.eB)
  saved : Saved s.mem p.S1 o
  frame : Frame (changes o) o.mem s.mem
  state : StateOk p st s.mem

/-- A state of the loop: the frame's, the search going on, and the key's
buffer for the progress. -/
structure GenLive (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) (s : State) : Prop
    extends GenFrame p o used st s where
  r11 : s.gpr .r11 = 4
  key : KeyOk p st s.mem

/-- The key search from octet `used` of the tape, from the progress `st`. -/
abbrev tailOf (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) : KeySearchResult :=
  keySearch p.L p.eB st ((genRand o).drop used)

/-- A loop state, whose key search from there finishes as `final`. -/
def GenIter (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (s : State) : Prop :=
  GenLive p o used st s ∧ ∃ tr, final = (tailOf p o used st).consume used tr

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## Through the controller's code (ARMv7): its loop states kept, its stack
arguments, and the state's halves -/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Spec.RsaKeyGen

theorem sub_add_ofNat (x : BitVec 32) (k d : Nat) :
    x - BitVec.ofNat 32 k + BitVec.ofNat 32 (k + d) = x + BitVec.ofNat 32 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem toNat_small {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem addr_toNat (x : BitVec 32) : (State.addr x).toNat = x.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-! ## The state's halves -/

/-- The low half of a word below `2^32`. -/
theorem low_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) :
    m.readW a 32 = BitVec.ofNat 32 n := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

/-- The high half of a word. -/
theorem high_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    m.readW (a + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (n / 2 ^ 32) := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]

/-- A word from its halves. -/
theorem word_of_halves {m : Mem} {a : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hlo : m.readW a 32 = BitVec.ofNat 32 (n % 2 ^ 32))
    (hhi : m.readW (a + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (n / 2 ^ 32)) :
    m.readW a 64 = BitVec.ofNat 64 n := by
  rw [VG.Proof.Rc2.Word32.read64_pair, hlo, hhi]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt hn,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
  omega

namespace GenFrame

variable {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress}

theorem facts (h : GenFrame p o used st s) : PreFacts p := h.input.facts

theorem S1_toNat (h : GenFrame p o used st s) : p.S1.toNat = p.sp.toNat - 40 :=
  FrameStack.sub_toNat' (Nat.le_trans (by decide) h.facts.room)

/-- Through code that keeps `r4`–`r10`, the regions and the stack pointer,
and writes only within `rs`, which the controller may write and which are
apart from its saved registers and its state. -/
theorem step (h : GenFrame p o used st s) {ws : List Reg} (k : Rest ws s t)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10], r ∉ ws := by decide) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hsub : ∀ r ∈ rs, ∃ q ∈ changes o, Region.Sub r q)
    (happ : ∀ r ∈ rs, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r)
    (hst : StateOk p st t.mem) : GenFrame p o used st t :=
  ⟨h.input, h.used_le, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    (k.gpr .r4 (hws _ (by simp))).trans h.r4, (k.gpr .r5 (hws _ (by simp))).trans h.r5,
    (k.gpr .r6 (hws _ (by simp))).trans h.r6, (k.gpr .r7 (hws _ (by simp))).trans h.r7,
    (k.gpr .r8 (hws _ (by simp))).trans h.r8, (k.gpr .r9 (hws _ (by simp))).trans h.r9,
    (k.gpr .r10 (hws _ (by simp))).trans h.r10,
    Spill.Saved.frame h.saved (lo := 0) (hi := 40) (by decide) hf happ, h.frame.trans (hf.sub hsub), hst⟩

theorem keep (h : GenFrame p o used st s) {ws : List Reg} (k : Rest ws s t) (hm : t.mem = s.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10], r ∉ ws := by decide) : GenFrame p o used st t :=
  h.step k hws (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (by rw [hm]; exact h.state)

/-- The controller's stack argument `j`, below `extra` more bytes of frame. -/
theorem arg_addr (h : GenFrame p o used st s) {u : State} {extra : Nat} (hu : u.sp = p.S1 - BitVec.ofNat 32 extra)
    (j : Nat) : State.addr (u.sp + BitVec.ofNat 32 (40 + extra + 4 * j)) = stackArgAddr o j := by
  rw [hu, SearchPublicSub (p := p), h.input.sp_eq]
  rfl
where
  SearchPublicSub {p : GenPublic} : p.S1 - BitVec.ofNat 32 extra + BitVec.ofNat 32 (40 + extra + 4 * j) =
      p.sp + BitVec.ofNat 32 (4 * j) := by
    rw [GenPublic.S1, BitVec.sub_sub, ← BitVec.ofNat_add, show 40 + extra + 4 * j = (40 + extra) + 4 * j by omega,
      sub_add_ofNat]

theorem arg_read (h : GenFrame p o used st s) {u : State} (hrd : u.rd = o.rd) {j : Nat} (hj : j < 4) :
    InRegions (u.rd ++ u.wr) (stackArgAddr o j) 4 := by
  have top := h.facts.top
  refine ⟨inArgs o, List.mem_append_left _ (by rw [hrd, h.input.rd]; simp [inReads]), ?_⟩
  have e : stackArgAddr o j = stackArgAddr o 0 + BitVec.ofNat 64 (4 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact VG.Arm.addr_add (by rw [← h.input.sp_eq]; omega)
  rw [e]; exact Offset.contains_base _ (by omega) (by omega)

theorem arg_value (h : GenFrame p o used st s) {j : Nat} (hj : j < 4) :
    s.mem.readW (stackArgAddr o j) 32 = stackArg o j := by
  rw [h.input.arg_frame h.frame hj]; rfl

theorem randLen_arg (h : GenFrame p o used st s) : stackArg o 0 = BitVec.ofNat 32 p.randLen := by
  rw [← h.input.2]; exact (ofNat_toNat32 _).symm

theorem scr_arg (h : GenFrame p o used st s) : stackArg o 1 = p.B := by rw [← h.input.2]; rfl

theorem scrLen_arg (h : GenFrame p o used st s) : stackArg o 2 = BitVec.ofNat 32 p.Z := by
  rw [← h.input.2]; exact (ofNat_toNat32 _).symm

/-! ### The state -/

theorem state_region (h : GenFrame p o used st s) : inState o = ⟨p.st, 56⟩ := h.input.regions.2.2.2.2

theorem state_addr (h : GenFrame p o used st s) {u : State} (h9 : u.gpr .r9 = p.stp) {d : Nat} (hd : d < 56) :
    State.addr (u.gpr .r9 + BitVec.ofNat 32 d) = off p.st d := by
  rw [h9]; exact VG.Arm.addr_add (by have := h.facts.nT; omega)

theorem state_wr (h : GenFrame p o used st s) {u : State} (hw : u.wr = ⟨State.addr p.S1, 40⟩ :: o.wr) {d : Nat}
    (hd : d + 4 ≤ 56) : InRegions u.wr (off p.st d) 4 := by
  refine ⟨⟨p.st, 56⟩, ?_, Offset.contains_base _ hd (by omega)⟩
  rw [hw, h.input.wr, ← h.state_region]; simp [inWrites]

theorem state_rd (h : GenFrame p o used st s) {u : State} (hw : u.wr = ⟨State.addr p.S1, 40⟩ :: o.wr) {d : Nat}
    (hd : d + 4 ≤ 56) : InRegions (u.rd ++ u.wr) (off p.st d) 4 := by
  obtain ⟨R, hR, hc⟩ := h.state_wr hw hd
  exact ⟨R, List.mem_append_right _ hR, hc⟩

/-- The low half of the state's word `j`, below `2^32`. -/
theorem half {m : Mem} {j n : Nat} (hm : m.readW (off p.st (8 * j)) 64 = BitVec.ofNat 64 n) :
    m.readW (off p.st (8 * j)) 32 = BitVec.ofNat 32 n := low_half hm

theorem high_zero {m : Mem} {j n : Nat} (hm : m.readW (off p.st (8 * j)) 64 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 32) : m.readW (off p.st (8 * j + 4)) 32 = 0 := by
  have e := high_half hm (by omega)
  rw [show off p.st (8 * j) + BitVec.ofNat 64 4 = off p.st (8 * j + 4) by
    rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]] at e
  rw [e, Nat.div_eq_of_lt hn]; rfl

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The controller's entry (ARMv7): the push, the first state, and the key's
buffer cleared but `p` -/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-! ## Whether the exponent is 3 -/

/-- Equality of all eight bytes is equality of words. -/
theorem eq_of_bytes {x y : BitVec 64}
    (h : ∀ j < 8, x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  ext i hi
  have e := congrArg (fun v : Byte => v.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and] at e
  rwa [show 8 * (i / 8) + i % 8 = i by omega] at e

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

theorem xor_zero32 (x y : BitVec 32) : x ^^^ y = 0 ↔ x = y := BitVec.xor_eq_zero_iff

theorem or_zero32 (x y : BitVec 32) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 32).toNat = 0 from rfl] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by rw [this.1]; rfl), BitVec.eq_of_toNat_eq (by rw [this.2]; rfl)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The exponent is 3 exactly when its low word is zero and its high word
`3 · 2^24`, as `entry` tests it. -/
theorem halves_three (m : Mem) (a : Addr) :
    (m.readW a 32 ||| (m.readW (a + BitVec.ofNat 64 4) 32 ^^^ 0x03000000)) = 0 ↔
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a 8) = 3 := by
  rw [← word_eq_three, VG.Proof.Rc2.Word32.read64_pair, or_zero32, xor_zero32]
  generalize m.readW (a + BitVec.ofNat 64 4) 32 = hi
  generalize m.readW a 32 = lo
  constructor
  · rintro ⟨rfl, rfl⟩; decide
  · intro h
    have e := congrArg BitVec.toNat h
    rw [BitVec.toNat_append] at e
    have hl := lo.isLt
    have hh := hi.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq] at e
    change hi.toNat * 2 ^ 32 + lo.toNat = 216172782113783808 at e
    exact ⟨BitVec.eq_of_toNat_eq (by change lo.toNat = 0; omega),
      BitVec.eq_of_toNat_eq (by change hi.toNat = 50331648; omega)⟩

/-! ## The push -/

theorem push_frame {p : GenPublic} {o : State} (h : GenInput p o) :
    Frame (changes o) o.mem (pushed pushRegs o).mem := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  refine (FrameStack.pushed_frameA (rs := pushRegs) hroom).sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨inStack o, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
  rw [FrameStack.addr_sub' hroom]
  exact Offset.sub_below _ (by decide) (by decide)

theorem push_saved {p : GenPublic} {o : State} (h : GenInput p o) :
    Saved (pushed pushRegs o).mem p.S1 o := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have top := h.1.2.1
  let sp := o.sp - BitVec.ofNat 32 40
  have bound : sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [show sp = o.sp - BitVec.ofNat 32 40 from rfl, FrameStack.sub_toNat' hroom]; omega
  have address (k : Nat) (hk : k < 40) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    VG.Arm.addr_add (by omega)
  have memEq : (pushed pushRegs o).mem = Spill.saveMem o.mem (State.addr sp) o.gpr slots := by
    change storeWords o.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide), address 16 (by decide),
      address 20 (by decide), address 24 (by decide), address 28 (by decide), address 32 (by decide),
      address 36 (by decide)]
    simp only [off, BitVec.add_zero]
  have hS : p.S1 = sp := by rw [GenPublic.S1, h.sp_eq]
  unfold Saved
  rw [memEq, hS]
  exact Spill.saveMem_saved (lo := 0) (hi := 40) (State.addr sp) o.gpr o.mem slots (by decide)

/-! ## The state on entry -/

/-- The state's words are kept through writes apart from it. -/
theorem StateOk.frame {p : GenPublic} {st : KeyProgress} {m m' : Mem} (h : StateOk p st m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨p.st, 56⟩ r) :
    StateOk p st m' := by
  have w (d : Nat) (hd' : d + 8 ≤ 56) : m'.readW (off p.st d) 64 = m.readW (off p.st d) 64 :=
    hf.readW (r := ⟨p.st, 56⟩) (Offset.contains_base _ hd' (by omega)) hd (by decide)
  refine ⟨by rw [w 0 (by decide)]; exact h.remaining, by rw [w 8 (by decide)]; exact h.len,
    by rw [w 16 (by decide)]; exact h.cap, by rw [w 32 (by decide)]; exact h.phase,
    by rw [w 40 (by decide)]; exact h.left, ?_, h.remaining_le, h.left_lt⟩
  rw [← h.e]
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hf.bytes (R := ⟨off p.st 48, 8⟩) (fun r hr => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
  exact (hd r hr).sub_left (Offset.sub_base _ (by decide))

theorem stateOk_entry {p : GenPublic} {o : State} (h : GenInput p o) :
    StateOk p (genProgress o) o.mem := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrem, hcap, hph, -⟩, rfl⟩ := h
  have ofn (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨?_, ?_, hcap, ?_, ?_, rfl, hrem, BitVec.isLt _⟩
  · change o.mem.readW (genStp o + BitVec.ofNat 64 0) 64 = _
    rw [BitVec.add_zero]; exact ofn _
  · exact ofn _
  · change o.mem.readW (genStp o + 32) 64 =
      BitVec.ofNat 64 (phaseWord (if (o.mem.readW (genStp o + 32) 64).toNat = 0 then .p else .q _))
    split
    · rename_i h0
      exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
    · rename_i h0
      exact BitVec.eq_of_toNat_eq (by
        change _ = (BitVec.ofNat 64 1).toNat; rw [BitVec.toNat_ofNat]; change _ = 1; omega)
  · exact ofn _

/-! ## The entry -/

theorem push_state {p : GenPublic} {o : State} (h : GenInput p o) :
    StateOk p (genProgress o) (pushed pushRegs o).mem := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have hst : (inState o).Disjoint (FrameStack.belowA o.sp 40) := by
    have hd := h.stack_disjoint (r := inState o) (by simp [inWrites])
    refine fun x hx hy => hd x ?_ hx
    have hsub : Region.Sub (FrameStack.belowA o.sp 40) (inStack o) := by
      change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
      rw [FrameStack.addr_sub' hroom]; exact Offset.sub_below _ (by decide) (by decide)
    exact hsub x hy
  have e := h.regions.2.2.2.2
  refine (stateOk_entry h).frame (FrameStack.pushed_frameA (rs := pushRegs) hroom) fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  rw [← e]; exact hst

theorem limit_value {p : GenPublic} {m : Mem} (hst : Spec.Rsa.bytesAt m (off p.st 48) 8 = p.eB) (hL : p.L ≤ 512) :
    BitVec.ofNat 32 p.L <<< 6 - BitVec.ofNat 32
        (decide (1 ≤ (m.readW (off p.st 48) 32 ||| (m.readW (off p.st 48 + BitVec.ofNat 64 4) 32 ^^^ 0x03000000)).toNat)).toNat *
      (BitVec.ofNat 32 p.L <<< 3 + BitVec.ofNat 32 p.L <<< 4) = BitVec.ofNat 32 (limitOf p.L p.eB) := by
  rw [VG.Proof.RsaKeyGen.Arm.SearchInit.first_value p.L hL]
  unfold limitOf primeLimit
  have h3 := halves_three m (off p.st 48)
  rw [hst] at h3
  by_cases e3 : Spec.Rsa.os2ip p.eB = 3
  · have hz := h3.mpr e3
    rw [hz, ite_eq_left e3, show decide (1 ≤ (0 : BitVec 32).toNat) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1; omega
  · have hz : (m.readW (off p.st 48) 32 ||| (m.readW (off p.st 48 + BitVec.ofNat 64 4) 32 ^^^ 0x03000000)) ≠ 0 :=
      fun e => e3 (h3.mp e)
    rw [ite_eq_right e3, decide_eq_true (show 1 ≤ _ from
      Nat.pos_of_ne_zero fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))]
    simp only [↓reduceIte]
    congr 1; omega

theorem enc3 : encodable 0x03000000 = true := by decide

theorem entry_ok {p : GenPublic} {o : State} (h : GenInput p o) :
    WP isa (.block entry) (pushed pushRegs o) fun s => GenFrame p o 0 (genProgress o) s ∧ s.gpr .r11 = 4 ∧
      s.mem = (pushed pushRegs o).mem := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have top := h.1.2.1
  have f := h.facts
  have hv := f.valid
  unfold primeLenValid at hv
  have hf := push_frame h
  have hS : p.S1 = o.sp - BitVec.ofNat 32 40 := by rw [GenPublic.S1, h.sp_eq]
  have hso := push_state h
  -- the state pointer, a stack argument
  have a52 : State.addr (o.sp - BitVec.ofNat 32 40 + BitVec.ofNat 32 (40 + 0 + 4 * 3)) = stackArgAddr o 3 := by
    rw [show (40 + 0 + 4 * 3 : Nat) = 40 + 4 * 3 from rfl, sub_add_ofNat]; rfl
  have r52 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (stackArgAddr o 3) 4 := by
    refine ⟨inArgs o, List.mem_append_left _ (by rw [h.rd]; simp [inReads]), ?_⟩
    have e : stackArgAddr o 3 = stackArgAddr o 0 + BitVec.ofNat 64 12 := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega)
    rw [e]; exact Offset.contains_base _ (by decide) (by decide)
  have v52 : (pushed pushRegs o).mem.readW (stackArgAddr o 3) 32 = p.stp := by
    rw [h.arg_frame hf (by decide), ← h.2]; rfl
  have aT (d : Nat) (hd : d < 56) : State.addr (p.stp + BitVec.ofNat 32 d) = off p.st d :=
    VG.Arm.addr_add (by have := f.nT; omega)
  have hstR : ⟨p.st, 56⟩ ∈ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr := by
    rw [h.wr, ← h.regions.2.2.2.2]; simp [inWrites]
  have rT (d : Nat) (hd : d + 4 ≤ 56) :
      InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (off p.st d) 4 :=
    ⟨_, List.mem_append_right _ hstR, Offset.contains_base _ hd (by omega)⟩
  have v8 : (pushed pushRegs o).mem.readW (off p.st 8) 32 = BitVec.ofNat 32 p.L := by
    rw [low_half hso.len]
  generalize hlo : (pushed pushRegs o).mem.readW (off p.st 48) 32 = lo
  generalize hhi : (pushed pushRegs o).mem.readW (off p.st 52) 32 = hi
  have hlv := limit_value (m := (pushed pushRegs o).mem) hso.e hv.2.1
  rw [hlo, show off p.st 48 + BitVec.ofNat 64 4 = off p.st 52 by
    rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add], hhi] at hlv
  have k3 : ∀ u : State, u.gpr .r5 = BitVec.ofNat 32 p.L → u.gpr .r0 = BitVec.ofNat 32
      (decide (1 ≤ (lo ||| (hi ^^^ 0x03000000)).toNat)).toNat →
      WP isa (.block entryLimit) u fun t => (t.gpr .r10 = BitVec.ofNat 32 (limitOf p.L p.eB) ∧ t.mem = u.mem) ∧
        Rest [.r0, .r1, .r10] u t := fun u h5 h0 => by
    refine withRest_all [.r0, .r1, .r10] ?_ (by rfl) (by rfl)
    unfold entryLimit
    ffrun [h5, h0, hlv]
  have carry (P : Prop) [Decidable P] :
      ((0 : BitVec 32) + 0 + if decide P = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide P).toNat := by
    by_cases hP : P
    · rw [decide_eq_true hP]; rfl
    · rw [decide_eq_false hP]; rfl
  refine WP.mono (Q := fun (t : State) =>
      t.gpr .r4 = o.gpr .r0 ∧ t.gpr .r5 = BitVec.ofNat 32 p.L ∧ t.gpr .r6 = o.gpr .r2 ∧ t.gpr .r7 = o.gpr .r3 ∧
      t.gpr .r8 = 0 ∧ t.gpr .r9 = p.stp ∧ t.gpr .r10 = BitVec.ofNat 32 (limitOf p.L p.eB) ∧ t.gpr .r11 = 4 ∧
      t.mem = (pushed pushRegs o).mem ∧ Rest [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] (pushed pushRegs o) t)
    ?_ fun (t : State) ⟨h4, h5, h6, h7, h8, h9, h10, h11, hm, k⟩ => ?_
  · unfold entry
    refine WP.block_append (WP.block_append (WP.mono (withRest_all [.r4, .r5, .r6, .r7, .r8, .r9, .r11]
      (c := .block entryHead) (Q := fun t => t.gpr .r4 = o.gpr .r0 ∧ t.gpr .r5 = BitVec.ofNat 32 p.L ∧
        t.gpr .r6 = o.gpr .r2 ∧ t.gpr .r7 = o.gpr .r3 ∧ t.gpr .r8 = 0 ∧ t.gpr .r9 = p.stp ∧ t.gpr .r11 = 4 ∧
        t.mem = (pushed pushRegs o).mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u4, u5, u6, u7, u8, u9, u11, um⟩, ku⟩ => ?_))
    · unfold entryHead arg pushBytes
      ffrun [pushed_gpr, pushed_sp, pushed_rd, pushed_wr, a52, r52, v52, aT 8 (by decide), rT 8 (by decide), v8,
        show 4 * pushRegs.length = 40 from rfl]
    refine WP.mono (withRest_all [.r0, .r1] (c := .block entryThree) (Q := fun t => t.gpr .r0 = BitVec.ofNat 32
        (decide (1 ≤ (lo ||| (hi ^^^ 0x03000000)).toNat)).toNat ∧ t.mem = u.mem) ?_ (by rfl) (by rfl))
      fun w ⟨⟨w0, wm⟩, kw⟩ => ?_
    · have wr : u.wr = ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr := by rw [ku.wr, pushed_wr]; rfl
      have rd : u.rd = o.rd := by rw [ku.rd, pushed_rd]
      unfold entryThree
      ffrun [u9, aT 48 (by decide), aT 52 (by decide), wr, rd, rT 48 (by decide), rT 52 (by decide), um, hlo, hhi,
        enc3, show (1 : BitVec 32).toNat = 1 from rfl, carry]
    refine WP.mono (k3 w ((kw.gpr .r5 (by decide)).trans u5) w0) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
    have k : Rest [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] (pushed pushRegs o) t :=
      (ku.mono (by decide)).trans ((kw.mono (by decide)).trans (kt.mono (by decide)))
    refine ⟨(kt.gpr .r4 (by decide)).trans ((kw.gpr .r4 (by decide)).trans u4),
      (kt.gpr .r5 (by decide)).trans ((kw.gpr .r5 (by decide)).trans u5),
      (kt.gpr .r6 (by decide)).trans ((kw.gpr .r6 (by decide)).trans u6),
      (kt.gpr .r7 (by decide)).trans ((kw.gpr .r7 (by decide)).trans u7),
      (kt.gpr .r8 (by decide)).trans ((kw.gpr .r8 (by decide)).trans u8),
      (kt.gpr .r9 (by decide)).trans ((kw.gpr .r9 (by decide)).trans u9), t10,
      (kt.gpr .r11 (by decide)).trans ((kw.gpr .r11 (by decide)).trans u11), by rw [tm, wm, um], k⟩
  · refine ⟨⟨h, Nat.zero_le _, ?_, ?_, ?_, ?_, h5, ?_, ?_, h8, h9, h10, ?_, ?_, ?_⟩, h11, hm⟩
    · rw [k.rd]; rfl
    · rw [k.wr, pushed_wr, hS]; rfl
    · rw [k.sp, pushed_sp, hS]; rfl
    · rw [h4, ← h.2]; rfl
    · rw [h6, ← h.2]; rfl
    · rw [h7, ← h.2]; rfl
    · rw [hm]; exact push_saved h
    · rw [hm]; exact hf
    · rw [hm]; exact hso

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## Zeros in the key's buffer (ARMv7): `clearAround` and `clearAll` -/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen

/-- A part of the key's buffer. -/
abbrev kRegion (p : GenPublic) (d n : Nat) : Region := ⟨State.addr p.kp + BitVec.ofNat 64 d, n⟩

theorem bytes_zero {m : Mem} {op : Addr} {len : Nat} (h : ∀ i < len, m (op + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m op len = List.replicate len 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)

theorem bytes_kept {m m' : Mem} {rs : List Region} {a : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨a, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨a, n⟩) hd hn (List.mem_range.mp hi)

theorem kp_zero (kp : Addr) : kp = kp + BitVec.ofNat 64 0 := (BitVec.add_zero kp).symm

namespace GenFrame

variable {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress}

theorem key_region (h : GenFrame p o used st s) : inKey o = ⟨State.addr p.kp, 9 * p.L⟩ := h.input.regions.1

theorem kp_nowrap (h : GenFrame p o used st s) : (State.addr p.kp).toNat + 9 * p.L ≤ 2 ^ 32 := by
  rw [addr_toNat]; exact h.facts.nK

/-- The parts of the key's buffer are apart. -/
theorem kDisjoint (h : GenFrame p o used st s) {d n e k : Nat} (hde : d + n ≤ e ∨ e + k ≤ d)
    (hd : d + n ≤ 9 * p.L) (he : e + k ≤ 9 * p.L) : (kRegion p d n).Disjoint (kRegion p e k) :=
  Offset.disjoint _ hde (by have := h.kp_nowrap; omega) (by have := h.kp_nowrap; omega)

theorem kSub (h : GenFrame p o used st s) {d n : Nat} (hd : d + n ≤ 9 * p.L) :
    Region.Sub (kRegion p d n) (inKey o) := by
  rw [h.key_region]; exact Offset.sub_base _ hd

/-- The key's buffer is apart from the state. -/
theorem key_state (h : GenFrame p o used st s) : (inKey o).Disjoint (inState o) := by
  have pw := h.input.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at pw
  exact pw.1.2.2

/-- The push's frame is apart from what the controller may write. -/
theorem push_apart (h : GenFrame p o used st s) :
    ∀ q ∈ inWrites o, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ q := by
  have room := h.facts.room
  have push : Region.Sub ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ (inStack o) := by
    rw [BitVec.add_zero, GenPublic.S1, FrameStack.addr_sub' (by omega), h.input.sp_eq]
    exact Offset.sub_below _ (by decide) (by decide)
  exact fun q hq => (h.input.stack_disjoint (List.mem_append_left _ hq)).sub_left push

/-- Through stores within a part of the key's buffer. -/
theorem keyStep (h : GenFrame p o used st s) {t : State} {ws : List Reg} (k : Rest ws s t)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10], r ∉ ws := by decide) {d n : Nat} (hd : d + n ≤ 9 * p.L)
    (hf : Frame [kRegion p d n] s.mem t.mem) : GenFrame p o used st t := by
  have hsub := h.kSub hd
  refine h.step k hws hf (fun r hr => ?_) (fun r hr => ?_) (h.state.frame hf fun r hr => ?_)
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨inKey o, by simp [changes, inWrites], hsub⟩
  · obtain rfl := List.mem_singleton.mp hr
    exact (h.push_apart _ (by simp [inWrites])).sub_right hsub
  · obtain rfl := List.mem_singleton.mp hr
    rw [← h.state_region]; exact (h.key_state.sub_left hsub).symm

end GenFrame

theorem kAddr {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s) {d : Nat}
    (hd : d < 9 * p.L) : State.addr (p.kp + BitVec.ofNat 32 d) = State.addr p.kp + BitVec.ofNat 64 d :=
  VG.Arm.addr_add (by have := h.facts.nK; omega)

/-- Zeros at `n` octets of the key's buffer from `d`, `r0` and `lr` set up. -/
theorem zeros_ok {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s)
    {setup : List Instr} {d n : Nat} (hn : 0 < n) (hdn : d + n ≤ 9 * p.L)
    (hset : WP isa (.block (setup ++ ([.mov .r2 (.imm 0)] : List Instr))) s fun u =>
      (u.gpr .r0 = p.kp + BitVec.ofNat 32 d ∧ u.gpr .lr = BitVec.ofNat 32 n ∧ u.gpr .r2 = 0 ∧ u.mem = s.mem) ∧
        Rest [.r0, .r2, .lr] s u) :
    WP isa (zeros setup) s fun t => GenFrame p o used st t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.kp + BitVec.ofNat 64 d) n = List.replicate n 0 ∧
      Frame [kRegion p d n] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have hk := h.facts.nK
  unfold zeros
  refine WP.seq (WP.mono hset fun u ⟨⟨h0, hlr, h2, hm⟩, ku⟩ => ?_)
  have write : InRegions u.wr (State.addr (p.kp + BitVec.ofNat 32 d)) n := by
    refine ⟨inKey o, ?_, ?_⟩
    · rw [ku.wr, h.wr, h.input.wr]; simp [inWrites]
    · rw [kAddr h (by omega), h.key_region]; exact Offset.contains_base _ hdn (by omega)
  refine WP.mono (VG.Proof.Ffdh.Arm.zeroBuffer_ok false u (src := u.gpr .r1) hn (by omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (p.kp).isLt; omega) write h2 rfl h0 hlr)
    fun t ⟨hz, _, _, hf, kt⟩ => ?_
  rw [kAddr h (by omega)] at hz hf
  rw [hm] at hf
  have k : Rest [.r0, .r1, .r2, .lr] s t := (ku.mono (by decide)).trans (kt.mono (by decide))
  exact ⟨h.keyStep k (by decide) hdn hf, hz, hf, k⟩

theorem shl32 (L k : Nat) (h : L * 2 ^ k < 2 ^ 32) :
    BitVec.ofNat 32 L <<< k = BitVec.ofNat 32 (L * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hL : L < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- `clearAround`: zeros at the key's buffer but `p`. -/
theorem clearAround_ok {p : GenPublic} {o s : State} {st : KeyProgress} (h : GenFrame p o 0 st s)
    (h11 : s.gpr .r11 = 4) (hother : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    WP isa clearAround s fun t => GenLive p o 0 st t ∧
      Frame [kRegion p 0 (4 * p.L), kRegion p (5 * p.L) (4 * p.L)] s.mem t.mem := by
  have hv := h.facts.valid
  unfold primeLenValid at hv
  unfold clearAround
  refine WP.seq (WP.mono (zeros_ok h (d := 0) (n := 4 * p.L) (by omega) (by omega) ?_)
    fun u ⟨gu, zu, fu, ku⟩ => ?_)
  · refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
    ffrun [List.cons_append, List.nil_append, h.r4, h.r5, BitVec.add_zero, shl32 p.L 2 (by omega),
      show p.L * 2 ^ 2 = 4 * p.L by omega]
  refine WP.mono (zeros_ok gu (d := 5 * p.L) (n := 4 * p.L) (by omega) (by omega) ?_) fun t ⟨gt, zt, ft, kt⟩ => ?_
  · refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
    ffrun [List.cons_append, List.nil_append, gu.r4, gu.r5, shl32 p.L 2 (by omega), show p.L * 2 ^ 2 = 4 * p.L by omega, BitVec.add_assoc,
      add_ofNat32, show 4 * p.L + p.L = 5 * p.L by omega]
  have hd (a n : Nat) (ha : a + n ≤ 9 * p.L) (hsep : a + n ≤ 5 * p.L ∨ 9 * p.L ≤ a) :
      ∀ r ∈ [kRegion p (5 * p.L) (4 * p.L)], (⟨State.addr p.kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact h.kDisjoint (by omega) ha (by omega)
  have hd0 (a n : Nat) (ha : a + n ≤ 9 * p.L) (hsep : 4 * p.L ≤ a) :
      ∀ r ∈ [kRegion p 0 (4 * p.L)], (⟨State.addr p.kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact h.kDisjoint (by omega) ha (by omega)
  refine ⟨⟨gt, (kt.gpr .r11 (by decide)).trans ((ku.gpr .r11 (by decide)).trans h11), ⟨?_, zt, fun pB hpB => ?_⟩⟩,
    (fu.mono (by simp)).trans (ft.mono (by simp))⟩
  · rw [kp_zero (State.addr p.kp), bytes_kept ft (hd 0 (4 * p.L) (by omega) (by omega)) (by omega), zu]
  · rw [bytes_kept ft (hd (4 * p.L) p.L (by omega) (by omega)) (by omega),
      bytes_kept fu (hd0 (4 * p.L) p.L (by omega) (by omega)) (by omega)]
    exact hother pB hpB

/-- `clearAll`: zeros at the whole key's buffer. -/
theorem clearAll_ok {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s) :
    WP isa clearAll s fun t => GenFrame p o used st t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.kp) (9 * p.L) = List.replicate (9 * p.L) 0 ∧
      Frame [kRegion p 0 (9 * p.L)] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have hv := h.facts.valid
  unfold primeLenValid at hv
  unfold clearAll
  refine WP.mono (zeros_ok h (d := 0) (n := 9 * p.L) (by omega) (by omega) ?_) fun t ⟨gt, zt, ft, kt⟩ =>
    ⟨gt, by rw [kp_zero (State.addr p.kp)]; exact zt, ft, kt⟩
  refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
  ffrun [List.cons_append, List.nil_append, h.r4, h.r5, BitVec.add_zero, shl32 p.L 3 (by omega), add_ofNat32, show p.L * 2 ^ 3 + p.L = 9 * p.L by omega]

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The prime search's call (ARMv7)

`searchRun`: the search's frame of 32 bytes at `S2 = sp - 72`, its
arguments, and the call of `vg_rsa_prime_search` on the tape from `used`,
for the progress' prime: its output `p`'s slot for `p`, `q`'s for `q`, and
the other prime `p`'s slot for `q`. What the controller's precondition says
of the regions (`CFacts`), the search's precondition, and what the search
leaves (`AfterSearch`).
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue slot_writeSlots writeSlots_frame readW_writeSlots_sep writeSlots_append)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Proof.RsaKeyGen.KeySearch (limitOf primeOf)

/-! ## The regions -/

abbrev cK (p : GenPublic) : Region := ⟨State.addr p.kp, 9 * p.L⟩
abbrev cU (p : GenPublic) : Region := ⟨State.addr p.up, 8⟩
abbrev cS (p : GenPublic) : Region := ⟨State.addr p.B, p.Z * 8⟩
abbrev cT (p : GenPublic) : Region := ⟨p.st, 56⟩
abbrev cR (p : GenPublic) : Region := ⟨State.addr p.rp, p.randLen⟩
abbrev cA (p : GenPublic) : Region := ⟨State.addr p.sp, 16⟩
abbrev cStack (p : GenPublic) : Region := ⟨State.addr p.sp - BitVec.ofNat 64 256, 256⟩
/-- The search's frame of arguments. -/
abbrev rA' (p : GenPublic) : Region := ⟨State.addr (p.sp - BitVec.ofNat 32 72), 32⟩

/-- What the controller's precondition says of its regions. -/
structure CFacts (p : GenPublic) : Prop where
  kU : (cK p).Disjoint (cU p)
  kS : (cK p).Disjoint (cS p)
  kT : (cK p).Disjoint (cT p)
  uS : (cU p).Disjoint (cS p)
  uT : (cU p).Disjoint (cT p)
  sT : (cS p).Disjoint (cT p)
  kR : (cK p).Disjoint (cR p)
  uR : (cU p).Disjoint (cR p)
  sR : (cS p).Disjoint (cR p)
  tR : (cT p).Disjoint (cR p)
  kA : (cK p).Disjoint (cA p)
  uA : (cU p).Disjoint (cA p)
  sA : (cS p).Disjoint (cA p)
  tA : (cT p).Disjoint (cA p)
  stack : ∀ r ∈ [cK p, cU p, cS p, cT p, cR p, cA p], (cStack p).Disjoint r

theorem GenInput.cfacts {p : GenPublic} {s : State} (h : GenInput p s) : CFacts p := by
  have hk := h.key_len
  obtain ⟨⟨-, -, -, -, hpw, hwr, hstk, -⟩, rfl⟩ := h
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hpw hwr hstk
  obtain ⟨⟨pku, pks, pkt⟩, ⟨pus, put⟩, pst, -⟩ := hpw
  obtain ⟨⟨wkr, wka⟩, ⟨wur, wua⟩, ⟨wsr, wsa⟩, ⟨wtr, wta⟩⟩ := hwr
  obtain ⟨bk, bu, bs, bt, br, ba⟩ := hstk
  have ek : inKey s = cK (genOfState s) := by simp only [inKey, hk]; rfl
  have ea : inArgs s = cA (genOfState s) := by
    simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]; rfl
  rw [ek] at pku pks pkt wkr wka bk
  rw [ea] at wka wua wsa wta ba
  refine ⟨pku, pks, pkt, pus, put, pst, wkr, wur, wsr, wtr, wka, wua, wsa, wta, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bk, bu, bs, bt, br, ba]

/-! ## The search's arguments -/

/-- The search's output: `p`'s slot for `p`, `q`'s for `q`. -/
abbrev outOf (p : GenPublic) (st : KeyProgress) : Nat := (4 + phaseWord st.phase) * p.L

/-- The other prime's octets the search reads: none for `p`, `p_len` for `q`. -/
abbrev plenOf (p : GenPublic) (st : KeyProgress) : Nat := phaseWord st.phase * p.L

/-- The search's frame. -/
abbrev GenPublic.S2 (p : GenPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 72

/-- Where the search's tape starts, past `rand`: `used` while octets are
left, else 0 (`randPtr`). -/
def usedPtr (p : GenPublic) (used : Nat) : Nat := if used < p.randLen then used else 0

/-- The search's stack arguments, for the tape from `used`. -/
def callArgs (p : GenPublic) (used : Nat) (st : KeyProgress) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 8), (3, p.rp + BitVec.ofNat 32 (usedPtr p used)),
    (4, BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used), (5, p.B), (6, BitVec.ofNat 32 p.Z), (7, p.stp),
    (1, p.kp + BitVec.ofNat 32 (4 * p.L)), (2, BitVec.ofNat 32 (plenOf p st))]

theorem callArgs_bound (p : GenPublic) (used : Nat) (st : KeyProgress) : ∀ e ∈ callArgs p used st, e.1 < 8 := by
  simp only [callArgs, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The search's argument registers. -/
def SearchRegs (p : GenPublic) (st : KeyProgress) (u : State) : Prop :=
  u.gpr .r0 = p.kp + BitVec.ofNat 32 (outOf p st) ∧ u.gpr .r1 = BitVec.ofNat 32 p.L ∧ u.gpr .r2 = p.up ∧
    u.gpr .r3 = p.stp + BitVec.ofNat 32 48

theorem mul_ofNat32 (a b : Nat) : BitVec.ofNat 32 a * BitVec.ofNat 32 b = BitVec.ofNat 32 (a * b) :=
  (BitVec.ofNat_mul a b).symm

namespace GenFrame

variable {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress}

theorem S2_toNat (h : GenFrame p o used st s) : p.S2.toNat = p.sp.toNat - 72 :=
  FrameStack.sub_toNat' (Nat.le_trans (by decide) h.facts.room)

theorem alloc_sp (h : GenFrame p o used st s) : (allocated 32 s).sp = p.S2 := by
  change s.sp - BitVec.ofNat 32 32 = p.S2
  rw [h.sp, GenPublic.S1, GenPublic.S2, BitVec.sub_sub, ← BitVec.ofNat_add]

theorem slotS2 (h : GenFrame p o used st s) {d : Nat} (hd : d < 32) :
    State.addr (p.S2 + BitVec.ofNat 32 d) = off (State.addr p.S2) d :=
  VG.Arm.addr_add (by have := h.S2_toNat; have := h.facts.top; omega)

/-- Bytes below the controller's stack pointer, within its stack, are apart
from its regions. -/
theorem below_disjoint (h : GenFrame p o used st s) {a n : Nat} (h1 : n ≤ a) (h2 : a ≤ 256) {r : Region}
    (hr : r ∈ inWrites o ++ inReads o) :
    Region.Disjoint ⟨State.addr (p.sp - BitVec.ofNat 32 a), n⟩ r := by
  have room := h.facts.room
  refine (h.input.stack_disjoint hr).sub_left ?_
  rw [FrameStack.addr_sub' (by omega), h.input.sp_eq]
  exact Offset.sub_below _ (by have : stackUse = 256 := rfl; omega) (by have : stackUse = 256 := rfl; omega)

theorem S2_state (h : GenFrame p o used st s) : Region.Disjoint ⟨State.addr p.S2, 32⟩ ⟨p.st, 56⟩ := by
  rw [← h.state_region]; exact h.below_disjoint (by decide) (by decide) (by simp [inWrites])

/-- A store in the search's frame keeps the state. -/
theorem S2_keep (h : GenFrame p o used st s) {m : Mem} {d : Nat} (hd : d + 4 ≤ 32) {e w : Nat}
    (he : e + w / 8 ≤ 56) (v : BitVec 32) :
    (m.writeW (off (State.addr p.S2) d) v).readW (off p.st e) w = m.readW (off p.st e) w :=
  Mem.readW_writeW_sep (h.S2_state.symm.sep (Offset.contains_base _ he (by omega))
    (Offset.contains_base _ (show d + 32 / 8 ≤ 32 by omega) (by omega))) (by omega)

theorem S2_wr (p : GenPublic) (o : State) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions (⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr) (off (State.addr p.S2) d) 4 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩

/-- The search's argument registers, and its stack arguments `p` and `p_len`. -/
theorem searchRegs_ok (h : GenFrame p o used st s) {u : State} (hlr : u.gpr .lr = p.S2) (h4 : u.gpr .r4 = p.kp)
    (h5 : u.gpr .r5 = BitVec.ofNat 32 p.L) (h6 : u.gpr .r6 = p.up) (h9 : u.gpr .r9 = p.stp)
    (hrd : u.rd = o.rd) (hwr : u.wr = ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr)
    (hph : u.mem.readW (off p.st 32) 32 = BitVec.ofNat 32 (phaseWord st.phase)) :
    WP isa (.block searchRegs) u fun t =>
      (SearchRegs p st t ∧ t.mem = writeSlots u.mem (State.addr p.S2) ((callArgs p used st).drop 6)) ∧
      Rest [.r0, .r1, .r2, .r3, .r12] u t := by
  have hv := h.facts.valid
  unfold primeLenValid at hv
  have hph1 := phaseWord_le st.phase
  have aT : State.addr (p.stp + 32#32) = off p.st 32 := by
    have e := h.state_addr (u := s) h.r9 (d := 32) (by decide); rwa [h.r9] at e
  have hT : InRegions (o.rd ++ ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr) (off p.st 32) 4 := by
    refine ⟨⟨p.st, 56⟩, List.mem_append_right _ ?_, Offset.contains_base _ (by decide) (by decide)⟩
    rw [h.input.wr, ← h.state_region]; simp [inWrites]
  refine withRest_all [.r0, .r1, .r2, .r3, .r12] ?_ (by rfl) (by rfl)
  unfold searchRegs SearchRegs callArgs writeSlots
  ffrun [hlr, h4, h5, h6, h9, hrd, hwr, h.S2_keep (d := 4) (by decide) (e := 32) (w := 32) (by decide),
    h.slotS2 (d := 4) (by decide), h.slotS2 (d := 8) (by decide), S2_wr p o, aT, hT, hph,
    shl32 p.L 2 (by omega), mul_ofNat32, show p.L * 2 ^ 2 = 4 * p.L by omega]
  refine ⟨⟨by rw [BitVec.add_assoc, add_ofNat32, outOf, Nat.add_mul], rfl⟩, ?_⟩
  simp only [List.drop_succ_cons, List.drop_zero, List.foldl_cons, List.foldl_nil, Nat.reduceMul, plenOf]

theorem args_region (h : GenFrame p o used st s) {j : Nat} (hj : j < 4) :
    (inArgs o).Contains (stackArgAddr o j) 4 := by
  have top := h.facts.top
  have e : stackArgAddr o j = stackArgAddr o 0 + BitVec.ofNat 64 (4 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact VG.Arm.addr_add (by rw [← h.input.sp_eq]; omega)
  rw [e]; exact Offset.contains_base _ (by omega) (by omega)

/-- A store in the search's frame keeps the controller's stack arguments. -/
theorem S2_keepA (h : GenFrame p o used st s) {m : Mem} {d : Nat} (hd : d + 4 ≤ 32) {j : Nat} (hj : j < 4)
    (v : BitVec 32) :
    (m.writeW (off (State.addr p.S2) d) v).readW (stackArgAddr o j) 32 = m.readW (stackArgAddr o j) 32 :=
  Mem.readW_writeW_sep ((h.below_disjoint (a := 72) (n := 32) (by decide) (by decide)
    (r := inArgs o) (by simp [inReads])).symm.sep (h.args_region hj)
    (Offset.contains_base _ (show d + 32 / 8 ≤ 32 by omega) (by omega))) (by omega)

theorem S2_arg (h : GenFrame p o used st s) (j : Nat) :
    State.addr (p.S2 + BitVec.ofNat 32 (72 + 4 * j)) = stackArgAddr o j := by
  rw [GenPublic.S2, sub_add_ofNat, h.input.sp_eq]; rfl

/-- A carry, as `mov 0; adc 0` reads it. -/
theorem carry32 (P : Prop) [Decidable P] :
    ((0 : BitVec 32) + 0 + if decide P = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide P).toNat := by
  by_cases hP : P
  · rw [decide_eq_true hP]; rfl
  · rw [decide_eq_false hP]; rfl

theorem ptr_value {R U : Nat} (hR : R < 2 ^ 32) (hU : U ≤ R) :
    BitVec.ofNat 32 (decide ((BitVec.ofNat 32 U).toNat ≤ (BitVec.ofNat 32 R - 1).toNat)).toNat * BitVec.ofNat 32 U =
      BitVec.ofNat 32 (if U < R then U else 0) := by
  rcases Nat.eq_zero_or_pos R with rfl | hpos
  · obtain rfl : U = 0 := by omega
    simp
  have e1 : (BitVec.ofNat 32 R - 1).toNat = R - 1 := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hpos,
      toNat_small (by omega)]
  rw [e1, toNat_small (by omega)]
  by_cases hu : U < R
  · rw [decide_eq_true (by omega), ite_eq_left hu]; simp
  · rw [decide_eq_false (by omega), ite_eq_right hu]; simp

/-- The tape's pointer for the search. -/
theorem randPtr_ok (h : GenFrame p o used st s) {u : State} (hlr : u.gpr .lr = p.S2)
    (h7 : u.gpr .r7 = p.rp) (h8 : u.gpr .r8 = BitVec.ofNat 32 used)
    (hrd : u.rd = o.rd) (hwr : u.wr = ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr)
    (hargs : ∀ j < 4, u.mem.readW (stackArgAddr o j) 32 = stackArg o j) :
    WP isa (.block randPtr) u fun t =>
      (t.gpr .r12 = p.rp + BitVec.ofNat 32 (usedPtr p used) ∧ t.mem = u.mem) ∧ Rest [.r0, .r12] u t := by
  refine withRest_all [.r0, .r12] ?_ (by rfl) (by rfl)
  have a0 := h.S2_arg 0
  simp only [Nat.mul_zero, Nat.add_zero] at a0
  have ar : ∀ j < 4, InRegions (o.rd ++ ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr) (stackArgAddr o j) 4 :=
    fun j hj => by have e := h.arg_read (u := u) hrd hj; rwa [hrd, hwr] at e
  have hR : p.randLen < 2 ^ 32 := by
    have := h.facts.randLen; have hv := h.facts.valid; unfold primeLenValid at hv; unfold primeEntropy at *; omega
  unfold randPtr
  ffrun [hlr, h7, h8, hrd, hwr, a0, ar, hargs, h.randLen_arg]
  have hpu := ptr_value hR h.used_le
  rw [usedPtr, ← hpu]
  exact congrArg (fun x => p.rp + x * BitVec.ofNat 32 used) (carry32 _)

/-- The search's stack arguments but `p` and `p_len`. -/
theorem searchStack_ok (h : GenFrame p o used st s) {u : State} (hlr : u.gpr .lr = p.S2)
    (h7 : u.gpr .r7 = p.rp) (h8 : u.gpr .r8 = BitVec.ofNat 32 used) (h9 : u.gpr .r9 = p.stp)
    (hrd : u.rd = o.rd) (hwr : u.wr = ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr)
    (hargs : ∀ j < 4, u.mem.readW (stackArgAddr o j) 32 = stackArg o j) :
    WP isa (.block searchStack) u fun t =>
      t.mem = writeSlots u.mem (State.addr p.S2) ((callArgs p used st).take 6) ∧ Rest [.r0, .r12] u t := by
  have a0 := h.S2_arg 0
  have a1 := h.S2_arg 1
  have a2 := h.S2_arg 2
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2
  have ar : ∀ j < 4, InRegions (o.rd ++ ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr) (stackArgAddr o j) 4 :=
    fun j hj => by have e := h.arg_read (u := u) hrd hj; rwa [hrd, hwr] at e
  rw [searchStack, List.append_assoc]
  refine WP.block_append (WP.mono (withRest_all [.r12] (c := .block stackHead)
    (Q := fun t => t.mem = u.mem.writeW (off (State.addr p.S2) 0) (BitVec.ofNat 32 8)) ?_ (by rfl) (by rfl))
    fun u1 ⟨hm1, k1⟩ => ?_)
  · unfold stackHead
    ffrun [hlr, hwr, h.slotS2 (d := 0) (by decide), S2_wr p o, show (8 : BitVec 32) = 8#32 from rfl]
  have hargs1 : ∀ j < 4, u1.mem.readW (stackArgAddr o j) 32 = stackArg o j := fun j hj => by
    rw [hm1, h.S2_keepA (by decide) hj, hargs j hj]
  refine WP.block_append (WP.mono (h.randPtr_ok ((k1.gpr .lr (by decide)).trans hlr)
    ((k1.gpr .r7 (by decide)).trans h7) ((k1.gpr .r8 (by decide)).trans h8) (k1.rd.trans hrd) (k1.wr.trans hwr)
    hargs1) fun u2 ⟨⟨h12, hm2⟩, k2⟩ => ?_)
  have hargs2 : ∀ j < 4, u2.mem.readW (stackArgAddr o j) 32 = stackArg o j := fun j hj => by
    rw [hm2, hargs1 j hj]
  have k12 : Rest [.r0, .r12] u u2 := (k1.mono (by decide)).trans k2
  refine WP.mono (withRest_all [.r12] (c := .block stackTail)
    (Q := fun t => t.mem = writeSlots u2.mem (State.addr p.S2) (((callArgs p used st).take 6).drop 1)) ?_
      (by rfl) (by rfl))
    fun t ⟨hmt, kt⟩ => ⟨?_, k12.trans (kt.mono (by decide))⟩
  · have u8 := (k12.gpr .r8 (by decide)).trans h8
    have u9 := (k12.gpr .r9 (by decide)).trans h9
    have ulr := (k12.gpr .lr (by decide)).trans hlr
    have urd := k12.rd.trans hrd
    have uwr := k12.wr.trans hwr
    unfold stackTail callArgs writeSlots
    ffrun [ulr, h12, u8, u9, urd, uwr, a0, a1, a2, h.slotS2 (d := 12) (by decide),
      h.slotS2 (d := 16) (by decide), h.slotS2 (d := 20) (by decide), h.slotS2 (d := 24) (by decide),
      h.slotS2 (d := 28) (by decide), S2_wr p o, ar, h.S2_keepA, hargs2, h.randLen_arg, h.scr_arg,
      h.scrLen_arg, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.foldl_cons,
      List.foldl_nil]
  · rw [hmt, hm2, hm1]
    simp only [callArgs, writeSlots, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.foldl_cons, List.foldl_nil, Nat.reduceMul]

/-- The search's arguments in place, from a loop state `s`. -/
structure SearchReady (p : GenPublic) (o s : State) (used : Nat) (st : KeyProgress) (u : State) : Prop where
  regs : SearchRegs p st u
  sp : u.sp = p.S2
  rd : u.rd = o.rd
  wr : u.wr = ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr
  mem : u.mem = writeSlots s.mem (State.addr p.S2) (callArgs p used st)

theorem searchArgs_ok (h : GenFrame p o used st s) :
    WP isa (.block searchArgs) (allocated 32 s) fun u =>
      SearchReady p o s used st u ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] (allocated 32 s) u := by
  have hsp := h.alloc_sp
  have hwr : (allocated 32 s).wr = ⟨State.addr p.S2, 32⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr := by
    change ⟨State.addr (s.sp - BitVec.ofNat 32 32), 32⟩ :: s.wr = _
    rw [← h.alloc_sp, h.wr]; rfl
  have ag : (allocated 32 s).gpr = s.gpr := rfl
  have am : (allocated 32 s).mem = s.mem := rfl
  have hrd : (allocated 32 s).rd = o.rd := h.rd
  unfold searchArgs
  rw [show ∀ (i : Instr) (l : List Instr), i :: l = [i] ++ l from fun _ _ => rfl]
  refine WP.block_append (WP.mono (withRest_all [.lr] (c := .block [.addSp .lr 0])
    (Q := fun t => t.gpr .lr = p.S2 ∧ t.mem = s.mem) (by ffrun [hsp, am, BitVec.add_zero]) (by rfl) (by rfl))
    fun u0 ⟨⟨hlr, hm0⟩, k0⟩ => ?_)
  have g (r : Reg) (hr : r ≠ .lr) : u0.gpr r = s.gpr r := (k0.gpr r (by simp [hr])).trans (ag ▸ rfl)
  have hargs : ∀ j < 4, u0.mem.readW (stackArgAddr o j) 32 = stackArg o j := fun j hj => by
    rw [hm0, h.arg_value hj]
  refine WP.block_append (WP.mono (h.searchStack_ok hlr ((g .r7 (by decide)).trans h.r7) ((g .r8 (by decide)).trans h.r8)
    ((g .r9 (by decide)).trans h.r9) (k0.rd.trans hrd) (k0.wr.trans hwr) hargs) fun u1 ⟨hm1, k1⟩ => ?_)
  have hf1 : Frame [rA' p] s.mem u1.mem := by
    rw [hm1, hm0]
    exact writeSlots_frame _ _ (N := 8) (by decide) _ fun e he => callArgs_bound p used st e (List.mem_of_mem_take he)
  have hph : u1.mem.readW (off p.st 32) 32 = BitVec.ofNat 32 (phaseWord st.phase) := by
    rw [hf1.readW (r := ⟨off p.st 32, 4⟩) (by
        have := Offset.contains_base (off p.st 32) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        simpa only [BitVec.add_zero] using this)
      (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (h.S2_state.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)]
    exact low_half h.state.phase
  have g1 (r : Reg) (h0 : r ≠ .r0) (h12 : r ≠ .r12) (hlr : r ≠ .lr) : u1.gpr r = s.gpr r := by
    rw [k1.gpr r (by simp [h0, h12]), g r hlr]
  refine WP.mono (h.searchRegs_ok ((k1.gpr .lr (by decide)).trans hlr) ((g1 .r4 (by decide) (by decide) (by decide)).trans h.r4)
    ((g1 .r5 (by decide) (by decide) (by decide)).trans h.r5) ((g1 .r6 (by decide) (by decide) (by decide)).trans h.r6) ((g1 .r9 (by decide) (by decide) (by decide)).trans h.r9)
    (k1.rd.trans (k0.rd.trans hrd)) (k1.wr.trans (k0.wr.trans hwr)) hph) fun t ⟨⟨hr, hmt⟩, k2⟩ =>
      ⟨⟨hr, ?_, ?_, ?_, ?_⟩, (k0.mono (by decide)).trans ((k1.mono (by decide)).trans (k2.mono (by decide)))⟩
  · exact k2.sp.trans (k1.sp.trans (k0.sp.trans hsp))
  · exact k2.rd.trans (k1.rd.trans (k0.rd.trans hrd))
  · exact k2.wr.trans (k1.wr.trans (k0.wr.trans hwr))
  · rw [hmt, hm1, hm0, ← writeSlots_append, List.take_append_drop]

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The prime search's precondition and result, as the controller calls it (ARMv7)

The regions the search reads and writes, its entry state (`callS`), its
precondition there, and its result in terms of the controller's progress.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue slot_writeSlots writeSlots_frame)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf primeOf)

/-! ## The search's regions -/

abbrev rO (p : GenPublic) (st : KeyProgress) : Region := ⟨State.addr (p.kp + BitVec.ofNat 32 (outOf p st)), p.L⟩
abbrev rE (p : GenPublic) : Region := ⟨State.addr (p.stp + BitVec.ofNat 32 48), 8⟩
abbrev rP (p : GenPublic) (st : KeyProgress) : Region :=
  ⟨State.addr (p.kp + BitVec.ofNat 32 (4 * p.L)), plenOf p st⟩
abbrev rR (p : GenPublic) (used : Nat) : Region :=
  ⟨State.addr (p.rp + BitVec.ofNat 32 (usedPtr p used)), p.randLen - used⟩
abbrev rT (p : GenPublic) : Region := ⟨p.st, 32⟩
abbrev rA (p : GenPublic) : Region := ⟨State.addr p.S2, 32⟩

/-- The regions the search reads, and those it writes. -/
def sReads (p : GenPublic) (used : Nat) (st : KeyProgress) : List Region := [rE p, rP p st, rR p used, rA p]
def sWrites (p : GenPublic) (st : KeyProgress) : List Region := [rO p st, cU p, cS p, rT p]

/-- The search's entry, as the call makes it. -/
abbrev callS (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) : State :=
  u.callEntry.withRegions (sReads p used st) (sWrites p st)

theorem callS_gpr {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State} {r : Reg} (hr : r ∉ linkRegs) :
    (callS p used st u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem outOf_eq (p : GenPublic) (st : KeyProgress) : outOf p st = 4 * p.L + plenOf p st := by
  unfold outOf plenOf; rw [Nat.add_mul]

namespace GenFrame

variable {p : GenPublic} {o s u : State} {used : Nat} {st : KeyProgress}

theorem stArg (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) {j : Nat} (hj : j < 8) :
    stackArg (callS p used st u) j = slotValue (callArgs p used st) j (slot s.mem (State.addr p.S2) j) := by
  have e : stackArgAddr (callS p used st u) j = off (State.addr p.S2) (4 * j) := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hr.sp]
    exact h.slotS2 (by omega)
  unfold stackArg
  rw [e, State.withRegions_mem, State.callEntry_mem, hr.mem]
  exact slot_writeSlots _ _ (N := 8) (by decide) _ (callArgs_bound p used st) j hj

theorem sa0 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 0 = BitVec.ofNat 32 8 := h.stArg hr (by decide)
theorem sa1 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 1 = p.kp + BitVec.ofNat 32 (4 * p.L) := h.stArg hr (by decide)
theorem sa2 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 2 = BitVec.ofNat 32 (plenOf p st) := h.stArg hr (by decide)
theorem sa3 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 3 = p.rp + BitVec.ofNat 32 (usedPtr p used) := h.stArg hr (by decide)
theorem sa4 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 4 = BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used := h.stArg hr (by decide)
theorem sa5 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 5 = p.B := h.stArg hr (by decide)
theorem sa6 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 6 = BitVec.ofNat 32 p.Z := h.stArg hr (by decide)
theorem sa7 (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    stackArg (callS p used st u) 7 = p.stp := h.stArg hr (by decide)

theorem plen_le (st : KeyProgress) : plenOf p st ≤ p.L := by
  have := phaseWord_le st.phase
  unfold plenOf
  rcases Nat.lt_or_ge (phaseWord st.phase) 1 with e | e
  · rw [show phaseWord st.phase = 0 by omega]; omega
  · rw [show phaseWord st.phase = 1 by omega]; omega

theorem L_le (h : GenFrame p o used st s) : 32 ≤ p.L ∧ p.L ≤ 512 := by
  have hv := h.facts.valid; unfold primeLenValid at hv; omega

theorem tL (h : GenFrame p o used st s) : (BitVec.ofNat 32 p.L).toNat = p.L :=
  toNat_small (by have := h.L_le; omega)

theorem tP (h : GenFrame p o used st s) : (BitVec.ofNat 32 (plenOf p st)).toNat = plenOf p st :=
  toNat_small (by have := plen_le (p := p) st; have := h.L_le; omega)

theorem randLen_lt (h : GenFrame p o used st s) : p.randLen < 2 ^ 32 := by
  have := h.facts.randLen; have := h.L_le; unfold primeEntropy at *; omega

theorem tR (h : GenFrame p o used st s) :
    (BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used).toNat = p.randLen - used :=
  Search.toNat_diff h.used_le h.randLen_lt

theorem tZ (h : GenFrame p o used st s) : (BitVec.ofNat 32 p.Z).toNat = p.Z :=
  toNat_small (by have := h.facts.nS; omega)

/-! ### The regions as offsets -/

theorem eO (h : GenFrame p o used st s) : rO p st = kRegion p (outOf p st) p.L := by
  have := plen_le (p := p) st; have := h.L_le
  rw [rO, kAddr h (by rw [outOf_eq]; omega)]

theorem eP (h : GenFrame p o used st s) : rP p st = kRegion p (4 * p.L) (plenOf p st) := by
  have := h.L_le
  rw [rP, kAddr h (by omega)]

theorem eE (h : GenFrame p o used st s) : rE p = ⟨off p.st 48, 8⟩ := by
  rw [rE, VG.Arm.addr_add (by have := h.facts.nT; omega)]

theorem ptr_lt (h : GenFrame p o used st s) : p.rp.toNat + usedPtr p used < 2 ^ 32 := by
  have := h.facts.nR; have := p.rp.isLt
  unfold usedPtr; split <;> omega

theorem ptr_le : usedPtr p used + (p.randLen - used) ≤ p.randLen := by
  unfold usedPtr; split <;> omega

theorem eR (h : GenFrame p o used st s) :
    rR p used = ⟨State.addr p.rp + BitVec.ofNat 64 (usedPtr p used), p.randLen - used⟩ := by
  rw [rR, VG.Arm.addr_add h.ptr_lt]

theorem st_toNat (p : GenPublic) : p.st.toNat = p.stp.toNat := addr_toNat _

theorem oK (h : GenFrame p o used st s) : Region.Sub (rO p st) (cK p) := by
  have := plen_le (p := p) st; have := h.L_le
  rw [h.eO]; exact Offset.sub_base _ (by rw [outOf_eq]; omega)

theorem pK (h : GenFrame p o used st s) : Region.Sub (rP p st) (cK p) := by
  have := plen_le (p := p) st; have := h.L_le
  rw [h.eP]; exact Offset.sub_base _ (by omega)

theorem eT (h : GenFrame p o used st s) : Region.Sub (rE p) (cT p) := by
  rw [h.eE]; exact Offset.sub_base _ (by decide)

theorem tT : Region.Sub (rT p) (cT p) := Region.sub_prefix (by decide)

theorem rRc (h : GenFrame p o used st s) : Region.Sub (rR p used) (cR p) := by
  rw [h.eR]; exact Offset.sub_base _ ptr_le

theorem S2_eq (h : GenFrame p o used st s) : State.addr p.S2 = State.addr p.sp - BitVec.ofNat 64 72 :=
  FrameStack.addr_sub' (by have := h.facts.room; omega)

theorem aStack (h : GenFrame p o used st s) : Region.Sub (rA p) (cStack p) := by
  rw [rA, h.S2_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem oP (h : GenFrame p o used st s) : (rO p st).Disjoint (rP p st) := by
  have := plen_le (p := p) st; have := h.L_le
  rw [h.eO, h.eP]; exact h.kDisjoint (.inr (by rw [outOf_eq])) (by rw [outOf_eq]; omega) (by omega)

theorem tE (h : GenFrame p o used st s) : (rT p).Disjoint (rE p) := by
  rw [h.eE]; exact Offset.base_disjoint _ (by decide) (by decide)

/-- The search's stack, below its frame of arguments. -/
abbrev rLow (p : GenPublic) : Region := ⟨State.addr p.sp - BitVec.ofNat 64 256, 184⟩

theorem low_eq (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.inStack (callS p used st u) = rLow p := by
  simp only [Search.inStack, State.withRegions_sp, State.callEntry_sp, hr.sp, h.S2_eq, BitVec.sub_sub,
    ← BitVec.ofNat_add, Search.stackUse, Nat.reduceAdd]

theorem low_sub : Region.Sub (rLow p) (cStack p) := Region.sub_prefix (by decide)

theorem args_low (h : GenFrame p o used st s) : (rA p).Disjoint (rLow p) := by
  have e : State.addr p.sp - BitVec.ofNat 64 256 = State.addr p.S2 - BitVec.ofNat 64 184 := by
    rw [h.S2_eq, BitVec.sub_sub, ← BitVec.ofNat_add]
  rw [rLow, e]
  exact Offset.base_disjoint_below _ (by decide)

/-! ### The search's precondition -/

theorem callS_regions (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.inReads (callS p used st u) = sReads p used st ∧
      Search.inWrites (callS p used st u) = sWrites p st := by
  obtain ⟨r0, r1, r2, r3⟩ := hr.regs
  have hargs : stackArgAddr (callS p used st u) 0 = State.addr p.S2 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hr.sp, Nat.mul_zero, BitVec.add_zero]
  simp only [Search.inReads, Search.inWrites, Search.inE, Search.inP, Search.inRand, Search.inArgs,
    Search.inOut, Search.inUsed, Search.inScr, Search.inState, sReads, sWrites,
    callS_gpr (by decide : Reg.r0 ∉ linkRegs), callS_gpr (by decide : Reg.r1 ∉ linkRegs),
    callS_gpr (by decide : Reg.r2 ∉ linkRegs), callS_gpr (by decide : Reg.r3 ∉ linkRegs),
    r0, r1, r2, r3, h.sa0 hr, h.sa1 hr, h.sa2 hr, h.sa3 hr, h.sa4 hr, h.sa5 hr, h.sa6 hr, h.sa7 hr,
    h.tL, h.tP, h.tR, h.tZ, hargs]
  refine ⟨?_, ?_⟩ <;> first | rfl | trivial

theorem frame_args (_h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Frame [rA p] s.mem u.mem := by
  rw [hr.mem]
  exact writeSlots_frame _ _ (N := 8) (by decide) _ (callArgs_bound p used st)

theorem state_word (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) {d : Nat} (hd : d + 8 ≤ 56) :
    u.mem.readW (off p.st d) 64 = s.mem.readW (off p.st d) 64 :=
  (h.frame_args hr).readW (Offset.contains_base _ (show d + 64 / 8 ≤ 56 by omega) (by omega))
    (fun r hr' => by obtain rfl := List.mem_singleton.mp hr'; exact (h.S2_state).symm) (by decide)

theorem addr_toNat_add {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).toNat = x.toNat + d := by
  rw [BitVec.toNat_add, toNat_small (by omega), Nat.mod_eq_of_lt h]

theorem remaining_lt (h : GenFrame p o used st s) : st.remaining < 2 ^ 64 := by
  have := h.L_le
  have := h.state.remaining_le
  unfold KeySearch.limitOf primeLimit at this
  split at this <;> omega

/-- The search's precondition at its entry. -/
theorem callS_pre (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.searchPre (callS p used st u) := by
  have cf := h.input.cfacts
  have f := h.facts
  obtain ⟨hrd, hwr⟩ := h.callS_regions hr
  obtain ⟨r0, r1, r2, r3⟩ := hr.regs
  have hsp : (callS p used st u).sp = p.S2 := by
    simp only [State.withRegions_sp, State.callEntry_sp, hr.sp]
  have hL := h.L_le
  have hpl := plen_le (p := p) st
  have hul := h.used_le
  have hS2 := h.S2_toNat
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, sU, sS, sT, sR, -⟩ := hst
  have e8 : ∀ x : Addr, x + 8 = off x 8 := fun _ => rfl
  have e16 : ∀ x : Addr, x + 16 = off x 16 := fun _ => rfl
  have g1 : (callS p used st u).gpr .r1 = BitVec.ofNat 32 p.L := by rw [callS_gpr (by decide)]; exact r1
  have hlen : Search.searchLen (callS p used st u) = p.L := by simp only [Search.searchLen, g1, h.tL]
  have hE : Search.searchE (callS p used st u) = p.eB := by
    simp only [Search.searchE, callS_gpr (by decide : Reg.r3 ∉ linkRegs), r3, h.sa0 hr,
      show (BitVec.ofNat 32 8).toNat = 8 from rfl, State.withRegions_mem, State.callEntry_mem]
    rw [← h.state.e, show State.addr (p.stp + BitVec.ofNat 32 48) = off p.st 48 from congrArg Region.base h.eE]
    exact bytes_kept (h.frame_args hr) (fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'
      exact (h.S2_state.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)
  refine ⟨?_, ?_, hrd ▸ rfl, hwr ▸ rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp, hS2]; show 184 ≤ _; have := f.room; omega
  · rw [hsp, hS2]; have := f.top; omega
  · rw [hwr]
    simp only [sWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    exact ⟨⟨cf.kU.sub_left h.oK, cf.kS.sub_left h.oK, (cf.kT.sub_left h.oK).sub_right tT⟩,
      ⟨cf.uS, cf.uT.sub_right tT⟩, cf.sT.sub_right tT⟩
  · rw [hwr, hrd]
    simp only [sWrites, sReads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨(cf.kT.sub_left h.oK).sub_right h.eT, h.oP, (cf.kR.sub_left h.oK).sub_right h.rRc,
        (sK.sub_left h.aStack).symm.sub_left h.oK⟩,
      ⟨cf.uT.sub_right h.eT, (cf.kU.sub_left h.pK).symm, cf.uR.sub_right h.rRc, (sU.sub_left h.aStack).symm⟩,
      ⟨cf.sT.sub_right h.eT, (cf.kS.sub_left h.pK).symm, cf.sR.sub_right h.rRc, (sS.sub_left h.aStack).symm⟩,
      ⟨h.tE, ((cf.kT.sub_left h.pK).sub_right tT).symm, (cf.tR.sub_left tT).sub_right h.rRc,
        ((sT.sub_left h.aStack).symm.sub_left tT)⟩⟩
  · rw [hwr, hrd, h.low_eq hr]
    intro r hr'
    simp only [sWrites, sReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (sK.sub_left low_sub).sub_right h.oK
    · exact sU.sub_left low_sub
    · exact sS.sub_left low_sub
    · exact (sT.sub_left low_sub).sub_right tT
    · exact (sT.sub_left low_sub).sub_right h.eT
    · exact (sK.sub_left low_sub).sub_right h.pK
    · exact (sR.sub_left low_sub).sub_right h.rRc
    · exact h.args_low.symm
  · rw [callS_gpr (by decide), r0, g1, h.tL, addr_toNat_add (by rw [outOf_eq]; have := f.nK; omega)]
    rw [outOf_eq]; have := f.nK; omega
  · rw [callS_gpr (by decide), r2]; exact f.nU
  · rw [callS_gpr (by decide), r3, h.sa0 hr, addr_toNat_add (by have := f.nT; omega)]
    show _ + 48 + 8 ≤ _; have := f.nT; omega
  · rw [h.sa1 hr, h.sa2 hr, h.tP, addr_toNat_add (by have := f.nK; omega)]; have := f.nK; omega
  · rw [h.sa3 hr, h.sa4 hr, h.tR, addr_toNat_add h.ptr_lt]; have := ptr_le (p := p) (used := used); have := f.nR; omega
  · rw [h.sa5 hr, h.sa6 hr, h.tZ]; exact f.nS
  · rw [h.sa7 hr]; have := f.nT; omega
  · rw [hlen]; exact f.valid
  · rw [h.sa0 hr]; decide
  · rw [h.sa0 hr]; decide
  · rw [h.sa2 hr, h.tP, hlen]
    have := phaseWord_le st.phase
    unfold plenOf
    rcases Nat.lt_or_ge (phaseWord st.phase) 1 with e | e
    · exact .inl (by rw [show phaseWord st.phase = 0 by omega]; omega)
    · exact .inr (by rw [show phaseWord st.phase = 1 by omega]; omega)
  · rw [h.sa6 hr, h.tZ, hlen]
    have := f.scr; unfold Spec.Rsa.scratchWords at this ⊢; omega
  · have h0 := h.state_word hr (d := 0) (by decide)
    rw [h.state.remaining] at h0
    have hrem : Search.searchRemaining (callS p used st u) = st.remaining := by
      simp only [Search.searchRemaining, h.sa7 hr, State.withRegions_mem, State.callEntry_mem]
      rw [show p.stp = p.stp from rfl, show State.addr p.stp = off p.st 0 from (BitVec.add_zero _).symm, h0]
      exact toNat_small' h.remaining_lt
    rw [hrem, hE, hlen]
    exact h.state.remaining_le
  · simp only [h.sa7 hr, hlen, State.withRegions_mem, State.callEntry_mem]
    rw [e8, h.state_word hr (by decide)]; exact h.state.len
  · simp only [h.sa7 hr, hlen, State.withRegions_mem, State.callEntry_mem]
    rw [e16, h.state_word hr (by decide)]; exact h.state.cap
  · rw [h.sa4 hr, h.tR, hlen]; have := f.randLen; omega
where
  toNat_small' {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The prime search, run (ARMv7)

The search's call in its frame of arguments (`searchRun`), from a loop state:
what it leaves (`AfterSearch`) for the progress' prime from octet `used`.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf primeOf)

/-- The stack the prime search uses. -/
theorem search_stack (c : Search.Cand) : FrameStack.armStack (Impl.RsaKeyGen.Arm.Search.code c.call) ≤ 184 := by
  have := c.stack
  simp only [Impl.RsaKeyGen.Arm.Search.code, Impl.RsaKeyGen.Arm.Search.body, Impl.RsaKeyGen.Arm.Search.iteration,
    Impl.RsaKeyGen.Arm.Search.candidateStep, Impl.RsaKeyGen.Arm.Search.candidateRun,
    Impl.RsaKeyGen.Arm.Search.classify, Impl.RsaKeyGen.Arm.Search.reject, Impl.RsaKeyGen.Arm.Search.short,
    Impl.RsaKeyGen.Arm.Search.request, Impl.RsaKeyGen.Arm.Search.cap, Impl.RsaKeyGen.Arm.Search.raise,
    Impl.RsaKeyGen.Arm.Search.exhausted, Impl.RsaKeyGen.Arm.Search.zeroOut, Impl.Ffdh.Arm.Domain.GenerateKey.zeros,
    Search.Cand.call, FrameStack.armStack, List.length_cons, List.length_nil, Nat.max_zero, Nat.zero_max,
    Nat.max_self]
  omega

/-- What the search may change, as the controller sees it. -/
def callChanges (p : GenPublic) (st : KeyProgress) : List Region :=
  [rA p, rO p st, cU p, cS p, rT p, GenFrame.rLow p]

/-- What the search of the progress' prime from octet `used` leaves. -/
structure AfterSearch (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p o used ⟨st.left, st.phase, (primeOf p.L p.eB st ((genRand o).drop used)).remaining⟩ t
  r11 : t.gpr .r11 = s.gpr .r11
  status : (t.gpr .r0).toNat = (primeOf p.L p.eB st ((genRand o).drop used)).status
  usedw : t.mem.readW (State.addr p.up) 64 = BitVec.ofNat 64 (primeOf p.L p.eB st ((genRand o).drop used)).used
  out : Spec.Rsa.bytesAt t.mem (State.addr (p.kp + BitVec.ofNat 32 (outOf p st))) p.L =
    (match (primeOf p.L p.eB st ((genRand o).drop used)).outcome with
      | .accepted c => Spec.Rsa.i2osp c p.L
      | _ => List.replicate p.L 0)
  req : ∃ requested, t.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 requested ∧
    (primeOf p.L p.eB st ((genRand o).drop used)).Requests (primeEntropy p.L) requested
  mem : Frame (callChanges p st) s.mem t.mem

namespace GenFrame

variable {p : GenPublic} {o s u : State} {used : Nat} {st : KeyProgress}

theorem eU (h : GenFrame p o used st s) : inUsed o = cU p := h.input.regions.2.1
theorem eS (h : GenFrame p o used st s) : inScr o = cS p := h.input.regions.2.2.2.1
theorem eRand (h : GenFrame p o used st s) : inRand o = cR p := h.input.regions.2.2.1
theorem eK (h : GenFrame p o used st s) : inKey o = cK p := h.input.regions.1
theorem eT' (h : GenFrame p o used st s) : inState o = cT p := h.input.regions.2.2.2.2

theorem eStack (h : GenFrame p o used st s) : inStack o = cStack p := by
  simp only [inStack, stackUse, ← h.input.sp_eq]

theorem eArgs (h : GenFrame p o used st s) : inArgs o = cA p := by
  simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero, ← h.input.sp_eq]

/-! ### The call's regions -/

theorem search_covers (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Covers (sReads p used st ++ sWrites p st) (u.rd ++ u.wr) ∧ Covers (sWrites p st) u.wr := by
  have hL := h.L_le
  have hpl := plen_le (p := p) st
  have hrd : u.rd = [cR p, cA p] := by rw [hr.rd, h.input.rd, inReads, h.eRand, h.eArgs]
  have hwr : u.wr = rA p :: ⟨State.addr p.S1, 40⟩ :: [cK p, cU p, cS p, cT p] := by
    rw [hr.wr, h.input.wr, inWrites, h.eK, h.eU, h.eS, h.eT']
  have z (x : Addr) : x = x + BitVec.ofNat 64 0 := (BitVec.add_zero x).symm
  have w : Covers (sWrites p st) u.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr' => ?_
    simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · refine ⟨cK p, by simp, outOf p st, by rw [h.eO], ?_⟩
      show _ + p.L ≤ 9 * p.L
      rw [outOf_eq]; omega
    · exact ⟨cU p, by simp, 0, z _, by simp⟩
    · exact ⟨cS p, by simp, 0, z _, by simp⟩
    · exact ⟨cT p, by simp, 0, z _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr' => ?_) w.right, w⟩
  rw [hrd, hwr]
  simp only [sReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · exact ⟨cT p, by simp, 48, by rw [h.eE], by simp⟩
  · exact ⟨cK p, by simp, 4 * p.L, by rw [h.eP], by show _ + plenOf p st ≤ 9 * p.L; omega⟩
  · exact ⟨cR p, by simp, usedPtr p used, by rw [h.eR], ptr_le⟩
  · exact ⟨rA p, by simp, 0, z _, by simp⟩

theorem lowA (h : GenFrame p o used st s) {k : Nat} (hk : k ≤ 184) :
    Region.Sub (FrameStack.belowA p.S2 k) (rLow p) := by
  have room := h.facts.room
  have hS2 := h.S2_toNat
  change Region.Sub ⟨State.addr (p.S2 - BitVec.ofNat 32 k), k⟩ _
  rw [FrameStack.addr_sub' (by omega), h.S2_eq, BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem callChanges_sub (h : GenFrame p o used st s) :
    ∀ r ∈ callChanges p st, ∃ q ∈ changes o, Region.Sub r q := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hs : inStack o ∈ changes o := by simp [changes]
  have hw : ∀ q ∈ inWrites o, q ∈ changes o := fun q hq => List.mem_append_left _ hq
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hs, by rw [h.eStack]; exact h.aStack⟩
  · exact ⟨inKey o, hw _ (by simp [inWrites]), by rw [h.eK]; exact h.oK⟩
  · exact ⟨inUsed o, hw _ (by simp [inWrites]), by rw [h.eU]; exact fun _ h => h⟩
  · exact ⟨inScr o, hw _ (by simp [inWrites]), by rw [h.eS]; exact fun _ h => h⟩
  · exact ⟨inState o, hw _ (by simp [inWrites]), by rw [h.eT']; exact tT⟩
  · exact ⟨_, hs, by rw [h.eStack]; exact low_sub⟩

theorem callChanges_apart (h : GenFrame p o used st s) :
    ∀ r ∈ callChanges p st, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r := by
  have room := h.facts.room
  have top := h.facts.top
  have e1 : (State.addr p.S1).toNat = p.sp.toNat - 40 := by rw [addr_toNat]; exact h.S1_toNat
  have e2 : (State.addr p.S2).toNat = p.sp.toNat - 72 := by rw [addr_toNat]; exact h.S2_toNat
  have ap := h.push_apart
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · refine (Offset.disjoint_of_le (by simp only [BitVec.add_zero]; rw [e2, e1]; omega) ?_).symm
    simp only; rw [BitVec.add_zero, e1]; omega
  · exact (ap (inKey o) (by simp [inWrites])).sub_right (by rw [h.eK]; exact h.oK)
  · exact (ap (inUsed o) (by simp [inWrites])).sub_right (by rw [h.eU]; exact fun _ h => h)
  · exact (ap (inScr o) (by simp [inWrites])).sub_right (by rw [h.eS]; exact fun _ h => h)
  · exact (ap (inState o) (by simp [inWrites])).sub_right (by rw [h.eT']; exact tT)
  · refine (Offset.disjoint_of_le ?_ ?_).symm
    · simp only
      rw [← FrameStack.addr_sub' (by omega), addr_toNat, FrameStack.sub_toNat' (by omega), BitVec.add_zero, e1]
      omega
    · simp only; rw [BitVec.add_zero, e1]; omega

/-! ### The search's result -/

theorem callS_len (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.searchLen (callS p used st u) = p.L := by
  simp only [Search.searchLen, callS_gpr (by decide : Reg.r1 ∉ linkRegs), hr.regs.2.1, h.tL]

theorem callS_e (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.searchE (callS p used st u) = p.eB := by
  simp only [Search.searchE, callS_gpr (by decide : Reg.r3 ∉ linkRegs), hr.regs.2.2.2, h.sa0 hr,
    show (BitVec.ofNat 32 8).toNat = 8 from rfl, State.withRegions_mem, State.callEntry_mem]
  rw [← h.state.e, show State.addr (p.stp + BitVec.ofNat 32 48) = off p.st 48 from congrArg Region.base h.eE]
  exact bytes_kept (h.frame_args hr) (fun r hr' => by
    obtain rfl := List.mem_singleton.mp hr'
    exact (h.S2_state.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)

theorem callS_remaining (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.searchRemaining (callS p used st u) = st.remaining := by
  have h0 := h.state_word hr (d := 0) (by decide)
  rw [h.state.remaining] at h0
  simp only [Search.searchRemaining, h.sa7 hr, State.withRegions_mem, State.callEntry_mem]
  rw [show State.addr p.stp = off p.st 0 from (BitVec.add_zero _).symm, h0, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h.remaining_lt]

theorem frame_all (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Frame (changes o) o.mem u.mem :=
  h.frame.trans ((h.frame_args hr).sub fun r hr' => by
    obtain rfl := List.mem_singleton.mp hr'
    exact ⟨inStack o, by simp [changes], by rw [h.eStack]; exact h.aStack⟩)

theorem callS_rand (h : GenFrame p o used st s) (hr : SearchReady p o s used st u) :
    Search.searchRand (callS p used st u) = (genRand o).drop used := by
  have hg : genRand o = Spec.Rsa.bytesAt o.mem (State.addr p.rp) p.randLen := by rw [← h.input.2]; rfl
  have hu := h.input.random_frame (h.frame_all hr)
  simp only [Search.searchRand, h.sa3 hr, h.sa4 hr, h.tR, State.withRegions_mem, State.callEntry_mem]
  rw [hg, ← hu, show State.addr (p.rp + BitVec.ofNat 32 (usedPtr p used)) = (rR p used).base from rfl, h.eR]
  simp only
  unfold usedPtr
  split
  · exact Search.bytesAt_drop _ _ _ _
  · have e : p.randLen - used = 0 := by have := h.used_le; omega
    rw [e, List.drop_eq_nil_of_le (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega)]
    rfl

theorem callS_p (h : GenFrame p o used st s) (hr : SearchReady p o s used st u)
    (hk : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    Search.searchP (callS p used st u) = st.phase.other := by
  have hL := h.L_le
  simp only [Search.searchP, h.sa1 hr, h.sa2 hr, h.tP, State.withRegions_mem, State.callEntry_mem]
  rw [show State.addr (p.kp + BitVec.ofNat 32 (4 * p.L)) = (rP p st).base from rfl, h.eP]
  obtain ⟨left, phase, remaining⟩ := st
  cases phase with
  | p => simp [plenOf, phaseWord, KeyPhase.other, Spec.Rsa.bytesAt]
  | q pB =>
    simp only [plenOf, phaseWord, Nat.one_mul, KeyPhase.other]
    rw [← hk pB rfl]
    exact bytes_kept (h.frame_args hr) (fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'
      have := (h.input.cfacts.stack (cK p) (by simp)).sub_left h.aStack
      exact this.symm.sub_left (Offset.sub_base _ (by omega))) (by omega)

theorem callS_result (h : GenFrame p o used st s) (hr : SearchReady p o s used st u)
    (hk : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    Search.searchResult (callS p used st u) = primeOf p.L p.eB st ((genRand o).drop used) := by
  unfold Search.searchResult
  rw [h.callS_len hr, h.callS_e hr, h.callS_p hr hk, h.callS_remaining hr, h.callS_rand hr]

/-! ### What the search keeps -/

theorem upper_kept (h : GenFrame p o used st s) {d n : Nat} (hd : 32 ≤ d) (hdn : d + n ≤ 56) :
    ∀ r ∈ callChanges p st, Region.Disjoint ⟨off p.st d, n⟩ r := by
  have cf := h.input.cfacts
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -, -⟩ := hst
  have sub : Region.Sub ⟨off p.st d, n⟩ (cT p) := Offset.sub_base _ hdn
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (sT.sub_left h.aStack).symm.sub_left sub
  · exact (cf.kT.sub_left h.oK).symm.sub_left sub
  · exact cf.uT.symm.sub_left sub
  · exact cf.sT.symm.sub_left sub
  · exact (Offset.base_disjoint _ (k := 32) hd (by have := addr_toNat p.stp; omega)).symm
  · exact (sT.sub_left low_sub).symm.sub_left sub

/-- Through code that keeps `r4`–`r10`, the regions and the stack pointer,
to a new progress. -/
theorem stepTo (h : GenFrame p o used st s) {t : State} {ws : List Reg} (k : Rest ws s t)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10], r ∉ ws := by decide) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hsub : ∀ r ∈ rs, ∃ q ∈ changes o, Region.Sub r q)
    (happ : ∀ r ∈ rs, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r) {st' : KeyProgress}
    (hst : StateOk p st' t.mem) : GenFrame p o used st' t :=
  ⟨h.input, h.used_le, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    (k.gpr .r4 (hws _ (by simp))).trans h.r4, (k.gpr .r5 (hws _ (by simp))).trans h.r5,
    (k.gpr .r6 (hws _ (by simp))).trans h.r6, (k.gpr .r7 (hws _ (by simp))).trans h.r7,
    (k.gpr .r8 (hws _ (by simp))).trans h.r8, (k.gpr .r9 (hws _ (by simp))).trans h.r9,
    (k.gpr .r10 (hws _ (by simp))).trans h.r10,
    Spill.Saved.frame h.saved (lo := 0) (hi := 40) (by decide) hf happ, h.frame.trans (hf.sub hsub), hst⟩

theorem callRegs : ∀ r : Reg, r ∉ [Reg.r0, .r1, .r2, .r3, .r12, .lr] → r ∈ preserved ∧ r ≠ .lr := by
  intro r hr; cases r <;> simp [preserved] at hr ⊢

/-- The prime search's call, in its frame of arguments. -/
theorem search_run (name : String) (c : Search.Cand) (h : GenFrame p o used st s)
    (hk : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    WP isa (searchRun (.call name (Impl.RsaKeyGen.Arm.Search.code c.call))) s (AfterSearch p o used st s) := by
  have room := h.facts.room
  have hsp32 : 32 ≤ s.sp.toNat := by rw [h.sp, h.S1_toNat]; omega
  unfold searchRun
  refine WP.alloc (by decide) hsp32 ?_
  refine WP.seq (WP.mono h.searchArgs_ok fun u ⟨hr, ku⟩ => ?_)
  obtain ⟨cov, covW⟩ := h.search_covers hr
  have hS2 : 184 ≤ u.sp.toNat := by rw [hr.sp, h.S2_toNat]; omega
  refine FrameStack.WP.callF (Search.search_correct c) (h.callS_pre hr) cov covW
    (Nat.le_trans (search_stack c) hS2) fun t htr htw htsp hfr hpres hpost => ?_
  have hres := h.callS_result hr hk
  have hlen := h.callS_len hr
  obtain ⟨hst, hout, hused, req, hwords, hreq⟩ := hpost
  have hx0 : (callS p used st u).gpr .r0 = p.kp + BitVec.ofNat 32 (outOf p st) := by
    rw [callS_gpr (by decide)]; exact hr.regs.1
  have hx2 : (callS p used st u).gpr .r2 = p.up := by rw [callS_gpr (by decide)]; exact hr.regs.2.2.1
  simp only [hres, hlen, State.withRegions_mem, State.withRegions_gpr, h.sa7 hr, hx0, hx2]
    at hst hout hused hwords hreq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 1 = [0] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true, Nat.reduceMul] at hwords hused
  obtain ⟨w0, w1, w2, w3⟩ := hwords
  have f0 : Frame (callChanges p st) s.mem u.mem :=
    (h.frame_args hr).sub fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'; exact ⟨rA p, by simp [callChanges], fun _ h => h⟩
  have f1 : Frame (callChanges p st) u.mem t.mem := by
    refine hfr.sub fun r hr' => ?_
    rcases List.mem_append.mp hr' with hr' | hr'
    · refine ⟨r, ?_, fun _ h => h⟩
      simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> simp [callChanges]
    · obtain rfl := List.mem_singleton.mp hr'
      exact ⟨GenFrame.rLow p, by simp [callChanges], by rw [hr.sp]; exact h.lowA (search_stack c)⟩
  have hframe := f0.trans f1
  have hreg : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3, .r12, .lr] → t.gpr r = s.gpr r := fun r hr' =>
    (hpres r (callRegs r hr').1 (callRegs r hr').2).trans (ku.gpr r hr')
  have k : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s (freed 32 t) :=
    ⟨hreg, htr.trans (ku.rd.trans rfl), show t.wr.tail = s.wr by rw [htw, ku.wr]; rfl,
      show t.sp + BitVec.ofNat 32 32 = s.sp by rw [htsp, ku.sp]; exact BitVec.sub_add_cancel _ _⟩
  have kept {d n : Nat} (hd : 32 ≤ d) (hdn : d + n ≤ 56) (hn : n ≤ 8) :
      Spec.Rsa.bytesAt t.mem (off p.st d) n = Spec.Rsa.bytesAt s.mem (off p.st d) n :=
    bytes_kept hframe (h.upper_kept hd hdn) (by omega)
  have keptW {d : Nat} (hd : 32 ≤ d) (hdn : d + 8 ≤ 56) :
      t.mem.readW (off p.st d) 64 = s.mem.readW (off p.st d) 64 :=
    hframe.readW (r := ⟨off p.st d, 8⟩) (by
      have := Offset.contains_base (off p.st d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this) (h.upper_kept hd hdn) (by decide)
  have hst' : StateOk p ⟨st.left, st.phase, (primeOf p.L p.eB st ((genRand o).drop used)).remaining⟩ t.mem :=
    ⟨by simpa only [off, BitVec.add_zero] using w0, w1, w2, by rw [keptW (by decide) (by decide)]; exact h.state.phase,
      by rw [keptW (by decide) (by decide)]; exact h.state.left,
      by rw [kept (by decide) (by decide) (by decide)]; exact h.state.e,
      Nat.le_trans (KeySearch.primeSearch_remaining_le _ _ _ _ _) h.state.remaining_le, h.state.left_lt⟩
  refine ⟨h.stepTo k (by decide) hframe h.callChanges_sub h.callChanges_apart hst', ?_, ?_, ?_, hout,
    ⟨req, w3, hreq⟩, hframe⟩
  · exact hreg .r11 (by decide)
  · rw [← hst, BitVec.setWidth_append_eq_right]; rfl
  · change t.mem.readW _ 64 = _
    simpa only [BitVec.add_zero] using hused

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The key's arguments (ARMv7)

`keyArgs`: in the key's frame of 56 bytes at `S3 = sp - 96`, its stack
arguments (`p`, `q`, `dP`, `dQ`, `qInv` and their lengths, `e`, the working
space), and `n`, `d` in its argument registers.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue slot_writeSlots writeSlots_frame writeSlots_append)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen

/-- The key's frame. -/
abbrev GenPublic.S3 (p : GenPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 96

/-- The key's stack arguments, as `keyPrimes`, `keyCrt` and `keyRest` store them. -/
def keyVals1 (p : GenPublic) : List (Nat × BitVec 32) :=
  [(0, p.kp + BitVec.ofNat 32 (4 * p.L)), (1, BitVec.ofNat 32 p.L), (2, p.kp + BitVec.ofNat 32 (5 * p.L)),
    (3, BitVec.ofNat 32 p.L), (4, p.kp + BitVec.ofNat 32 (6 * p.L)), (5, BitVec.ofNat 32 p.L)]
def keyVals2 (p : GenPublic) : List (Nat × BitVec 32) :=
  [(6, p.kp + BitVec.ofNat 32 (7 * p.L)), (7, BitVec.ofNat 32 p.L), (8, p.kp + BitVec.ofNat 32 (8 * p.L)),
    (9, BitVec.ofNat 32 p.L)]
def keyVals3 (p : GenPublic) : List (Nat × BitVec 32) :=
  [(10, p.stp + BitVec.ofNat 32 48), (11, BitVec.ofNat 32 8), (12, p.B), (13, BitVec.ofNat 32 p.Z)]

def keyVals (p : GenPublic) : List (Nat × BitVec 32) := keyVals1 p ++ keyVals2 p ++ keyVals3 p

theorem keyVals_bound (p : GenPublic) : ∀ e ∈ keyVals p, e.1 < 14 := by
  simp only [keyVals, keyVals1, keyVals2, keyVals3, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The key's arguments in place, from a loop state `s`. -/
structure KeyReady (p : GenPublic) (o s : State) (u : State) : Prop where
  r0 : u.gpr .r0 = p.kp
  r1 : u.gpr .r1 = BitVec.ofNat 32 (2 * p.L)
  r2 : u.gpr .r2 = p.kp + BitVec.ofNat 32 (2 * p.L)
  r3 : u.gpr .r3 = BitVec.ofNat 32 (2 * p.L)
  sp : u.sp = p.S3
  rd : u.rd = o.rd
  wr : u.wr = ⟨State.addr p.S3, 56⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr
  mem : u.mem = writeSlots s.mem (State.addr p.S3) (keyVals p)

theorem kadd (x : BitVec 32) (a b : Nat) : x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, add_ofNat32]

namespace GenFrame

variable {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress}

theorem S3_toNat (h : GenFrame p o used st s) : p.S3.toNat = p.sp.toNat - 96 :=
  FrameStack.sub_toNat' (Nat.le_trans (by decide) h.facts.room)

theorem alloc56_sp (h : GenFrame p o used st s) : (allocated 56 s).sp = p.S3 := by
  change s.sp - BitVec.ofNat 32 56 = p.S3
  rw [h.sp, GenPublic.S1, GenPublic.S3, BitVec.sub_sub, ← BitVec.ofNat_add]

theorem slotS3 (h : GenFrame p o used st s) {d : Nat} (hd : d < 56) :
    State.addr (p.S3 + BitVec.ofNat 32 d) = off (State.addr p.S3) d :=
  VG.Arm.addr_add (by have := h.S3_toNat; have := h.facts.top; omega)

theorem S3_eq (h : GenFrame p o used st s) : State.addr p.S3 = State.addr p.sp - BitVec.ofNat 64 96 :=
  FrameStack.addr_sub' (by have := h.facts.room; omega)

theorem S3_keepA (h : GenFrame p o used st s) {m : Mem} {d : Nat} (hd : d + 4 ≤ 56) {j : Nat} (hj : j < 4)
    (v : BitVec 32) :
    (m.writeW (off (State.addr p.S3) d) v).readW (stackArgAddr o j) 32 = m.readW (stackArgAddr o j) 32 :=
  Mem.readW_writeW_sep ((h.below_disjoint (a := 96) (n := 56) (by decide) (by decide)
    (r := inArgs o) (by simp [inReads])).symm.sep (h.args_region hj)
    (Offset.contains_base _ (show d + 32 / 8 ≤ 56 by omega) (by omega))) (by omega)

theorem S3_wr (p : GenPublic) (o : State) {d : Nat} (hd : d + 4 ≤ 56) :
    InRegions (⟨State.addr p.S3, 56⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr) (off (State.addr p.S3) d) 4 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩

theorem S3_arg (h : GenFrame p o used st s) (j : Nat) :
    State.addr (p.S3 + BitVec.ofNat 32 (96 + 4 * j)) = stackArgAddr o j := by
  rw [GenPublic.S3, sub_add_ofNat, h.input.sp_eq]; rfl

theorem keyArgs_ok (h : GenFrame p o used st s) :
    WP isa (.block keyArgs) (allocated 56 s) fun u =>
      KeyReady p o s u ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] (allocated 56 s) u := by
  have hv := h.facts.valid
  unfold primeLenValid at hv
  have hsp := h.alloc56_sp
  have hwr : (allocated 56 s).wr = ⟨State.addr p.S3, 56⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr := by
    change ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ :: s.wr = _
    rw [← h.alloc56_sp, h.wr]; rfl
  have ag : (allocated 56 s).gpr = s.gpr := rfl
  have am : (allocated 56 s).mem = s.mem := rfl
  have hrd : (allocated 56 s).rd = o.rd := h.rd
  have a1 := h.S3_arg 1
  have a2 := h.S3_arg 2
  simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a1 a2
  have ar : ∀ j < 4, InRegions (o.rd ++ ⟨State.addr p.S3, 56⟩ :: ⟨State.addr p.S1, 40⟩ :: o.wr) (stackArgAddr o j) 4 :=
    fun j hj => by have e := h.arg_read (u := allocated 56 s) hrd hj; rwa [hrd, hwr] at e
  have aT : State.addr (p.stp + 48#32) = off p.st 48 := by
    have e := h.state_addr (u := s) h.r9 (d := 48) (by decide); rwa [h.r9] at e
  unfold keyArgs
  rw [show ∀ (l₁ l₂ l₃ l₄ : List Instr), Instr.addSp .lr 0 :: (l₁ ++ l₂ ++ l₃ ++ l₄) =
    ([.addSp .lr 0] ++ l₁) ++ (l₂ ++ (l₃ ++ l₄)) from fun _ _ _ _ => by simp]
  -- the registers
  refine WP.block_append (WP.mono (withRest_all [.r0, .r1, .r2, .r3, .r12, .lr]
    (c := .block ([.addSp .lr 0] ++ keyRegs))
    (Q := fun t => t.gpr .r0 = p.kp ∧ t.gpr .r1 = BitVec.ofNat 32 (2 * p.L) ∧
      t.gpr .r2 = p.kp + BitVec.ofNat 32 (2 * p.L) ∧ t.gpr .r3 = BitVec.ofNat 32 (2 * p.L) ∧
      t.gpr .r12 = p.kp + BitVec.ofNat 32 (4 * p.L) ∧ t.gpr .lr = p.S3 ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u1 ⟨⟨r0, r1, r2, r3, r12, hlr, hm1⟩, k1⟩ => ?_)
  · unfold keyRegs
    ffrun [List.cons_append, List.nil_append, hsp, ag, am, h.r4, h.r5, BitVec.add_zero, shl32 p.L 1 (by omega), kadd,
      show p.L * 2 ^ 1 = 2 * p.L by omega, show 2 * p.L + 2 * p.L = 4 * p.L by omega]
  have u5 : u1.gpr .r5 = BitVec.ofNat 32 p.L := (k1.gpr .r5 (by decide)).trans (ag ▸ h.r5)
  have u9 : u1.gpr .r9 = p.stp := (k1.gpr .r9 (by decide)).trans (ag ▸ h.r9)
  have usp : u1.sp = p.S3 := k1.sp.trans hsp
  have urd : u1.rd = o.rd := k1.rd.trans hrd
  have uwr : u1.wr = _ := k1.wr.trans hwr
  have hargs1 : ∀ j < 4, u1.mem.readW (stackArgAddr o j) 32 = stackArg o j := fun j hj => by
    rw [hm1, h.arg_value hj]
  -- p, q and dP
  refine WP.block_append (WP.mono (withRest_all [.r12] (c := .block keyPrimes)
    (Q := fun t => t.gpr .r12 = p.kp + BitVec.ofNat 32 (6 * p.L) ∧
      t.mem = writeSlots u1.mem (State.addr p.S3) (keyVals1 p)) ?_ (by rfl) (by rfl))
    fun u2 ⟨⟨r12', hm2⟩, k2⟩ => ?_)
  · unfold keyPrimes keyVals1 writeSlots
    ffrun [hlr, r12, u5, uwr, h.slotS3 (d := 0) (by decide), h.slotS3 (d := 4) (by decide),
      h.slotS3 (d := 8) (by decide), h.slotS3 (d := 12) (by decide), h.slotS3 (d := 16) (by decide),
      h.slotS3 (d := 20) (by decide), S3_wr p o, kadd, List.foldl_cons, List.foldl_nil,
      show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]
  have v5 := (k2.gpr .r5 (by decide)).trans u5
  have vlr := (k2.gpr .lr (by decide)).trans hlr
  -- dQ and qInv
  refine WP.block_append (WP.mono (withRest_all [.r12] (c := .block keyCrt)
    (Q := fun t => t.mem = writeSlots u2.mem (State.addr p.S3) (keyVals2 p)) ?_ (by rfl) (by rfl))
    fun u3 ⟨hm3, k3⟩ => ?_)
  · unfold keyCrt keyVals2 writeSlots
    ffrun [vlr, r12', v5, k2.wr.trans uwr, h.slotS3 (d := 24) (by decide), h.slotS3 (d := 28) (by decide),
      h.slotS3 (d := 32) (by decide), h.slotS3 (d := 36) (by decide), S3_wr p o, kadd, List.foldl_cons,
      List.foldl_nil, show 6 * p.L + p.L = 7 * p.L by omega, show 7 * p.L + p.L = 8 * p.L by omega]
  have hargs3 : ∀ j < 4, u3.mem.readW (stackArgAddr o j) 32 = stackArg o j := fun j hj => by
    rw [hm3, hm2]
    simp only [keyVals1, keyVals2, writeSlots, List.foldl_cons, List.foldl_nil, Nat.reduceMul]
    rw [h.S3_keepA (by decide) hj, h.S3_keepA (by decide) hj, h.S3_keepA (by decide) hj,
      h.S3_keepA (by decide) hj, h.S3_keepA (by decide) hj, h.S3_keepA (by decide) hj,
      h.S3_keepA (by decide) hj, h.S3_keepA (by decide) hj, h.S3_keepA (by decide) hj,
      h.S3_keepA (by decide) hj, hargs1 j hj]
  have k23 : Rest [.r12] u1 u3 := k2.trans k3
  -- e and the working space
  refine WP.mono (withRest_all [.r12] (c := .block keyRest)
    (Q := fun t => t.mem = writeSlots u3.mem (State.addr p.S3) (keyVals3 p)) ?_ (by rfl) (by rfl))
    fun t ⟨hmt, kt⟩ => ?_
  · unfold keyRest keyVals3 writeSlots
    ffrun [(k23.gpr .lr (by decide)).trans hlr, (k23.gpr .r9 (by decide)).trans u9, k23.sp.trans usp,
      k23.rd.trans urd, k23.wr.trans uwr, a1, a2, aT, h.slotS3 (d := 40) (by decide),
      h.slotS3 (d := 44) (by decide), h.slotS3 (d := 48) (by decide), h.slotS3 (d := 52) (by decide),
      S3_wr p o, ar, h.S3_keepA, hargs3, h.scr_arg, h.scrLen_arg, List.foldl_cons, List.foldl_nil,
      show (8 : BitVec 32) = 8#32 from rfl, show (48 : BitVec 32) = 48#32 from rfl]
  have k : Rest [.r12] u1 t := k23.trans kt
  refine ⟨⟨(k.gpr .r0 (by decide)).trans r0, (k.gpr .r1 (by decide)).trans r1, (k.gpr .r2 (by decide)).trans r2,
    (k.gpr .r3 (by decide)).trans r3, k.sp.trans usp, k.rd.trans urd, k.wr.trans uwr, ?_⟩,
    k1.trans (k.mono (by decide))⟩
  rw [hmt, hm3, hm2, hm1, keyVals, writeSlots_append, writeSlots_append]

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The key's precondition, as the controller calls it (ARMv7)

The key's entry (`callK`), its precondition there in the form its proof
states it (`Key.CIn`), and the contract's from that (`pre_of_cin`).
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue slot_writeSlots)
open VG.Spec.RsaKeyGen

/-- The contract's precondition from the key proof's. -/
theorem pre_of_cin {s : State} (h : Key.CIn s) : (Spec.RsaKeyGen.keyContract abi 56).pre s := by
  sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val]
  exact ⟨h.spLo, h.spHi, h.rd, h.wr, h.nD, h.nP, h.nQ, h.nDp, h.nDq, h.nQi, h.nE, h.nS, h.nA, h.dP, h.dQ, h.dDp,
    h.dDq, h.dQi, h.dE, h.dS, h.dA, h.pQ, h.pDp, h.pDq, h.pQi, h.pE, h.pS, h.pA, h.qDp, h.qDq, h.qQi, h.qE, h.qS,
    h.qA, h.dpDq, h.dpQi, h.dpE, h.dpS, h.dpA, h.dqQi, h.dqE, h.dqS, h.dqA, h.qiE, h.qiS, h.qiA, h.eS, h.SA, h.Fn,
    h.Fd, h.Fp, h.Fq, h.Fdp, h.Fdq, h.Fqi, h.Fe, h.FS, h.FA, h.fn, h.fd, h.fp, h.fq, h.fdp, h.fdq, h.fqi, h.fe,
    h.fS, h.valid, h.nl, h.dl, h.ql, h.dpl, h.dql, h.qil, h.el1, h.el2, h.scr⟩

/-! ## The key's regions -/

/-- `n`, `d` (`2 p_len` octets each), then `p`, `q`, `dP`, `dQ`, `qInv` at
`key + j p_len` for `j = 4, …, 8`. -/
abbrev kOut (p : GenPublic) (j n : Nat) : Region := ⟨State.addr (p.kp + BitVec.ofNat 32 (j * p.L)), n⟩

def kRd (p : GenPublic) : List Region := [rE p, ⟨State.addr p.S3, 56⟩]
def kWr (p : GenPublic) : List Region :=
  [⟨State.addr p.kp, 2 * p.L⟩, kOut p 2 (2 * p.L), kOut p 4 p.L, kOut p 5 p.L, kOut p 6 p.L, kOut p 7 p.L,
    kOut p 8 p.L, cS p]

/-- The key's entry, as the call makes it. -/
abbrev callK (p : GenPublic) (u : State) : State := u.callEntry.withRegions (kRd p) (kWr p)

theorem callK_gpr {p : GenPublic} {u : State} {r : Reg} (hr : r ∉ linkRegs) : (callK p u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

namespace GenFrame

variable {p : GenPublic} {o s u : State} {used : Nat} {st : KeyProgress}

theorem kArg (h : GenFrame p o used st s) (hr : KeyReady p o s u) {j : Nat} (hj : j < 14) :
    stackArg (callK p u) j = slotValue (keyVals p) j (slot s.mem (State.addr p.S3) j) := by
  have e : stackArgAddr (callK p u) j = off (State.addr p.S3) (4 * j) := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hr.sp]
    exact h.slotS3 (by omega)
  unfold stackArg
  rw [e, State.withRegions_mem, State.callEntry_mem, hr.mem]
  exact slot_writeSlots _ _ (N := 14) (by decide) _ (keyVals_bound p) j hj

theorem kOut_eq (h : GenFrame p o used st s) {j n : Nat} (hj : j * p.L < 9 * p.L) :
    kOut p j n = kRegion p (j * p.L) n := by
  rw [kOut, kAddr h hj]

theorem kSubK {d n : Nat} (hd : d + n ≤ 9 * p.L) : Region.Sub (kRegion p d n) (cK p) := Offset.sub_base _ hd

abbrev rA3 (p : GenPublic) : Region := ⟨State.addr p.S3, 56⟩
abbrev rF3 (p : GenPublic) : Region := ⟨State.addr p.S3 - 56#64, 56⟩

theorem a3Stack (h : GenFrame p o used st s) : Region.Sub (rA3 p) (cStack p) := by
  rw [rA3, h.S3_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem f3Stack (h : GenFrame p o used st s) : Region.Sub (rF3 p) (cStack p) := by
  rw [rF3, h.S3_eq, BitVec.sub_sub, show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by decide) (by decide)

/-- The key's precondition at its entry. -/
theorem callK_cin (h : GenFrame p o used st s) (hr : KeyReady p o s u) : Key.CIn (callK p u) := by
  have cf := h.input.cfacts
  have f := h.facts
  have hL := h.L_le
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, sS, sT, -, -⟩ := hst
  have a0 : stackArg (callK p u) 0 = p.kp + BitVec.ofNat 32 (4 * p.L) := h.kArg hr (by decide)
  have a1 : stackArg (callK p u) 1 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a2 : stackArg (callK p u) 2 = p.kp + BitVec.ofNat 32 (5 * p.L) := h.kArg hr (by decide)
  have a3 : stackArg (callK p u) 3 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a4 : stackArg (callK p u) 4 = p.kp + BitVec.ofNat 32 (6 * p.L) := h.kArg hr (by decide)
  have a5 : stackArg (callK p u) 5 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a6 : stackArg (callK p u) 6 = p.kp + BitVec.ofNat 32 (7 * p.L) := h.kArg hr (by decide)
  have a7 : stackArg (callK p u) 7 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a8 : stackArg (callK p u) 8 = p.kp + BitVec.ofNat 32 (8 * p.L) := h.kArg hr (by decide)
  have a9 : stackArg (callK p u) 9 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a10 : stackArg (callK p u) 10 = p.stp + BitVec.ofNat 32 48 := h.kArg hr (by decide)
  have a11 : stackArg (callK p u) 11 = BitVec.ofNat 32 8 := h.kArg hr (by decide)
  have a12 : stackArg (callK p u) 12 = p.B := h.kArg hr (by decide)
  have a13 : stackArg (callK p u) 13 = BitVec.ofNat 32 p.Z := h.kArg hr (by decide)
  have g0 : (callK p u).gpr .r0 = p.kp := by rw [callK_gpr (by decide)]; exact hr.r0
  have g1 : (callK p u).gpr .r1 = BitVec.ofNat 32 (2 * p.L) := by rw [callK_gpr (by decide)]; exact hr.r1
  have g2 : (callK p u).gpr .r2 = p.kp + BitVec.ofNat 32 (2 * p.L) := by rw [callK_gpr (by decide)]; exact hr.r2
  have g3 : (callK p u).gpr .r3 = BitVec.ofNat 32 (2 * p.L) := by rw [callK_gpr (by decide)]; exact hr.r3
  have hsp : (callK p u).sp = p.S3 := by simp only [State.withRegions_sp, State.callEntry_sp, hr.sp]
  have tL : (BitVec.ofNat 32 p.L).toNat = p.L := h.tL
  have t2 : (BitVec.ofNat 32 (2 * p.L)).toNat = 2 * p.L := toNat_small (by omega)
  have t8 : (BitVec.ofNat 32 8).toNat = 8 := rfl
  have hargs : stackArgAddr (callK p u) 0 = State.addr p.S3 := by
    simp only [stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]
  -- the regions, as offsets
  have eN : Key.cN (callK p u) = kRegion p 0 (2 * p.L) := by
    simp only [Key.cN, g0, g1, t2]; rw [kRegion, BitVec.add_zero]
  have eD : Key.cD (callK p u) = kRegion p (2 * p.L) (2 * p.L) := by
    simp only [Key.cD, g2, g3, t2]; rw [kAddr h (by omega)]
  have eJ {j : Nat} (hj : j * p.L < 9 * p.L) {x y : BitVec 32} (hx : x = p.kp + BitVec.ofNat 32 (j * p.L))
      (hy : y = BitVec.ofNat 32 p.L) : (⟨State.addr x, y.toNat⟩ : Region) = kRegion p (j * p.L) p.L := by
    rw [hx, hy, tL, kAddr h hj]
  have eP : Key.cP (callK p u) = kRegion p (4 * p.L) p.L := eJ (j := 4) (by omega) a0 a1
  have eQ : Key.cQ (callK p u) = kRegion p (5 * p.L) p.L := eJ (j := 5) (by omega) a2 a3
  have eDp : Key.cDp (callK p u) = kRegion p (6 * p.L) p.L := eJ (j := 6) (by omega) a4 a5
  have eDq : Key.cDq (callK p u) = kRegion p (7 * p.L) p.L := eJ (j := 7) (by omega) a6 a7
  have eQi : Key.cQi (callK p u) = kRegion p (8 * p.L) p.L := eJ (j := 8) (by omega) a8 a9
  have eE : Key.cE (callK p u) = ⟨off p.st 48, 8⟩ := by
    simp only [Key.cE, a10, a11, t8]; exact h.eE
  have eS : Key.cS (callK p u) = cS p := by simp only [Key.cS, a12, a13, h.tZ]
  have eA : Key.cA (callK p u) = rA3 p := by simp only [Key.cA, hargs]
  have eF : Key.cF (callK p u) = rF3 p := by simp only [Key.cF, hsp]
  have kd {a n b m : Nat} (h1 : a + n ≤ b ∨ b + m ≤ a) (h2 : a + n ≤ 9 * p.L) (h3 : b + m ≤ 9 * p.L) :
      (kRegion p a n).Disjoint (kRegion p b m) := h.kDisjoint h1 h2 h3
  have eSub : Region.Sub ⟨off p.st 48, 8⟩ (cT p) := Offset.sub_base _ (by decide)
  have kE {a n : Nat} (h2 : a + n ≤ 9 * p.L) : (kRegion p a n).Disjoint ⟨off p.st 48, 8⟩ :=
    (cf.kT.sub_left (kSubK h2)).sub_right eSub
  have kS {a n : Nat} (h2 : a + n ≤ 9 * p.L) : (kRegion p a n).Disjoint (cS p) := cf.kS.sub_left (kSubK h2)
  have kA {a n : Nat} (h2 : a + n ≤ 9 * p.L) : (kRegion p a n).Disjoint (rA3 p) :=
    (sK.sub_left h.a3Stack).symm.sub_left (kSubK h2)
  have Fk {a n : Nat} (h2 : a + n ≤ 9 * p.L) : (rF3 p).Disjoint (kRegion p a n) :=
    (sK.sub_left h.f3Stack).sub_right (kSubK h2)
  have tK (j : Nat) (hj : j * p.L + p.L ≤ 9 * p.L) : (p.kp + BitVec.ofNat 32 (j * p.L)).toNat + p.L ≤ 2 ^ 32 := by
    rw [addr_toNat_add (by have := f.nK; omega)]; have := f.nK; omega
  have hS3 := h.S3_toNat
  have hwr : (callK p u).wr = [Key.cN (callK p u), Key.cD (callK p u), Key.cP (callK p u), Key.cQ (callK p u),
      Key.cDp (callK p u), Key.cDq (callK p u), Key.cQi (callK p u), Key.cS (callK p u)] := by
    rw [eN, eD, eP, eQ, eDp, eDq, eQi, eS, State.withRegions_wr, kWr, kOut_eq h (by omega), kOut_eq h (by omega),
      kOut_eq h (by omega), kOut_eq h (by omega), kOut_eq h (by omega), kOut_eq h (by omega)]
    simp only [kRegion, BitVec.add_zero]
  exact {
    spLo := by rw [hsp, hS3]; have := f.room; omega
    spHi := by rw [hsp, hS3]; have := f.top; omega
    rd := by simp only [State.withRegions_rd, kRd, eE, eA, h.eE]
    wr := hwr
    nD := by rw [eN, eD]; exact kd (by omega) (by omega) (by omega)
    nP := by rw [eN, eP]; exact kd (by omega) (by omega) (by omega)
    nQ := by rw [eN, eQ]; exact kd (by omega) (by omega) (by omega)
    nDp := by rw [eN, eDp]; exact kd (by omega) (by omega) (by omega)
    nDq := by rw [eN, eDq]; exact kd (by omega) (by omega) (by omega)
    nQi := by rw [eN, eQi]; exact kd (by omega) (by omega) (by omega)
    nE := by rw [eN, eE]; exact kE (by omega)
    nS := by rw [eN, eS]; exact kS (by omega)
    nA := by rw [eN, eA]; exact kA (by omega)
    dP := by rw [eD, eP]; exact kd (by omega) (by omega) (by omega)
    dQ := by rw [eD, eQ]; exact kd (by omega) (by omega) (by omega)
    dDp := by rw [eD, eDp]; exact kd (by omega) (by omega) (by omega)
    dDq := by rw [eD, eDq]; exact kd (by omega) (by omega) (by omega)
    dQi := by rw [eD, eQi]; exact kd (by omega) (by omega) (by omega)
    dE := by rw [eD, eE]; exact kE (by omega)
    dS := by rw [eD, eS]; exact kS (by omega)
    dA := by rw [eD, eA]; exact kA (by omega)
    pQ := by rw [eP, eQ]; exact kd (by omega) (by omega) (by omega)
    pDp := by rw [eP, eDp]; exact kd (by omega) (by omega) (by omega)
    pDq := by rw [eP, eDq]; exact kd (by omega) (by omega) (by omega)
    pQi := by rw [eP, eQi]; exact kd (by omega) (by omega) (by omega)
    pE := by rw [eP, eE]; exact kE (by omega)
    pS := by rw [eP, eS]; exact kS (by omega)
    pA := by rw [eP, eA]; exact kA (by omega)
    qDp := by rw [eQ, eDp]; exact kd (by omega) (by omega) (by omega)
    qDq := by rw [eQ, eDq]; exact kd (by omega) (by omega) (by omega)
    qQi := by rw [eQ, eQi]; exact kd (by omega) (by omega) (by omega)
    qE := by rw [eQ, eE]; exact kE (by omega)
    qS := by rw [eQ, eS]; exact kS (by omega)
    qA := by rw [eQ, eA]; exact kA (by omega)
    dpDq := by rw [eDp, eDq]; exact kd (by omega) (by omega) (by omega)
    dpQi := by rw [eDp, eQi]; exact kd (by omega) (by omega) (by omega)
    dpE := by rw [eDp, eE]; exact kE (by omega)
    dpS := by rw [eDp, eS]; exact kS (by omega)
    dpA := by rw [eDp, eA]; exact kA (by omega)
    dqQi := by rw [eDq, eQi]; exact kd (by omega) (by omega) (by omega)
    dqE := by rw [eDq, eE]; exact kE (by omega)
    dqS := by rw [eDq, eS]; exact kS (by omega)
    dqA := by rw [eDq, eA]; exact kA (by omega)
    qiE := by rw [eQi, eE]; exact kE (by omega)
    qiS := by rw [eQi, eS]; exact kS (by omega)
    qiA := by rw [eQi, eA]; exact kA (by omega)
    eS := by rw [eE, eS]; exact (cf.sT.sub_right eSub).symm
    SA := by rw [eS, eA]; exact (sS.sub_left h.a3Stack).symm
    Fn := by rw [eF, eN]; exact Fk (by omega)
    Fd := by rw [eF, eD]; exact Fk (by omega)
    Fp := by rw [eF, eP]; exact Fk (by omega)
    Fq := by rw [eF, eQ]; exact Fk (by omega)
    Fdp := by rw [eF, eDp]; exact Fk (by omega)
    Fdq := by rw [eF, eDq]; exact Fk (by omega)
    Fqi := by rw [eF, eQi]; exact Fk (by omega)
    Fe := by rw [eF, eE]; exact (sT.sub_left h.f3Stack).sub_right eSub
    FS := by rw [eF, eS]; exact sS.sub_left h.f3Stack
    FA := by rw [eF, eA]; exact (Offset.base_disjoint_below _ (by decide)).symm
    fn := by rw [g0, g1, t2]; have := f.nK; omega
    fd := by rw [g2, g3, t2, addr_toNat_add (by have := f.nK; omega)]; have := f.nK; omega
    fp := by rw [a0, a1, tL]; exact tK 4 (by omega)
    fq := by rw [a2, a3, tL]; exact tK 5 (by omega)
    fdp := by rw [a4, a5, tL]; exact tK 6 (by omega)
    fdq := by rw [a6, a7, tL]; exact tK 7 (by omega)
    fqi := by rw [a8, a9, tL]; exact tK 8 (by omega)
    fe := by rw [a10, a11, t8, addr_toNat_add (by have := f.nT; omega)]; have := f.nT; omega
    fS := by rw [a12, a13, h.tZ]; exact f.nS
    valid := by rw [a1, tL]; exact f.valid
    nl := by rw [g1, a1, t2, tL]
    dl := by rw [g1, g3]
    ql := by rw [a1, a3]
    dpl := by rw [a1, a5]
    dql := by rw [a1, a7]
    qil := by rw [a1, a9]
    el1 := by rw [a11]; decide
    el2 := by rw [a11]; decide
    scr := by rw [g1, a13, t2, h.tZ]; exact f.scr }

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The key, run (ARMv7)

The key's call in its frame of arguments (`keyRun`), from a loop state: what
it leaves (`AfterKey`), from the primes at the slots of `p` and `q`.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue writeSlots_frame)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen

/-- The key from the primes at the slots of `p` and `q`. -/
abbrev keyOf (p : GenPublic) (m : Mem) : Except Failure (List (List Byte)) ⊕ Unit :=
  keyOp p.L p.eB (Spec.Rsa.bytesAt m (p.slot 4) p.L) (Spec.Rsa.bytesAt m (p.slot 5) p.L)

/-- The key's outputs at the key's buffer. -/
def keyOutsOf (p : GenPublic) : List (Addr × Nat) :=
  [(State.addr p.kp, 2 * p.L), (p.slot 2, 2 * p.L), (p.slot 4, p.L), (p.slot 5, p.L), (p.slot 6, p.L),
    (p.slot 7, p.L), (p.slot 8, p.L)]

/-- What the key may change, as the controller sees it. -/
def keyChanges (p : GenPublic) : List Region := [GenFrame.rA3 p, cK p, cS p, GenFrame.rF3 p]

/-- What the key leaves. -/
structure AfterKey (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p o used st t
  r11 : t.gpr .r11 = s.gpr .r11
  status : (t.gpr .r0).toNat = keyStatus (keyOf p s.mem)
  out : match keyOf p s.mem with
    | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
  mem : Frame (keyChanges p) s.mem t.mem

namespace GenFrame

variable {p : GenPublic} {o s u : State} {used : Nat} {st : KeyProgress}

theorem key_covers (h : GenFrame p o used st s) (hr : KeyReady p o s u) :
    Covers (kRd p ++ kWr p) (u.rd ++ u.wr) ∧ Covers (kWr p) u.wr := by
  have hL := h.L_le
  have hrd : u.rd = [cR p, cA p] := by rw [hr.rd, h.input.rd, inReads, h.eRand, h.eArgs]
  have hwr : u.wr = rA3 p :: ⟨State.addr p.S1, 40⟩ :: [cK p, cU p, cS p, cT p] := by
    rw [hr.wr, h.input.wr, inWrites, h.eK, h.eU, h.eS, h.eT']
  have z (x : Addr) : x = x + BitVec.ofNat 64 0 := (BitVec.add_zero x).symm
  have w : Covers (kWr p) u.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr' => ?_
    simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cK p, by simp, 0, z _, by simp only; omega⟩
    · exact ⟨cK p, by simp, 2 * p.L, by rw [h.kOut_eq (by omega)], by simp only; omega⟩
    · exact ⟨cK p, by simp, 4 * p.L, by rw [h.kOut_eq (by omega)], by simp only; omega⟩
    · exact ⟨cK p, by simp, 5 * p.L, by rw [h.kOut_eq (by omega)], by simp only; omega⟩
    · exact ⟨cK p, by simp, 6 * p.L, by rw [h.kOut_eq (by omega)], by simp only; omega⟩
    · exact ⟨cK p, by simp, 7 * p.L, by rw [h.kOut_eq (by omega)], by simp only; omega⟩
    · exact ⟨cK p, by simp, 8 * p.L, by rw [h.kOut_eq (by omega)], by simp only; omega⟩
    · exact ⟨cS p, by simp, 0, z _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr' => ?_) w.right, w⟩
  rw [hrd, hwr]
  simp only [kRd, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact ⟨cT p, by simp, 48, by rw [h.eE], by simp⟩
  · exact ⟨rA3 p, by simp, 0, z _, by simp⟩

theorem frame_kargs (_h : GenFrame p o used st s) (hr : KeyReady p o s u) :
    Frame [rA3 p] s.mem u.mem := by
  rw [hr.mem]
  exact writeSlots_frame _ _ (N := 14) (by decide) _ (keyVals_bound p)

theorem keyChanges_sub (h : GenFrame p o used st s) :
    ∀ r ∈ keyChanges p, ∃ q ∈ changes o, Region.Sub r q := by
  intro r hr
  simp only [keyChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hs : inStack o ∈ changes o := by simp [changes]
  have hw : ∀ q ∈ inWrites o, q ∈ changes o := fun q hq => List.mem_append_left _ hq
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, hs, by rw [h.eStack]; exact h.a3Stack⟩
  · exact ⟨inKey o, hw _ (by simp [inWrites]), by rw [h.eK]; exact fun _ h => h⟩
  · exact ⟨inScr o, hw _ (by simp [inWrites]), by rw [h.eS]; exact fun _ h => h⟩
  · exact ⟨_, hs, by rw [h.eStack]; exact h.f3Stack⟩

theorem keyChanges_apart (h : GenFrame p o used st s) :
    ∀ r ∈ keyChanges p, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r := by
  have room := h.facts.room
  have e1 : (State.addr p.S1).toNat = p.sp.toNat - 40 := by rw [addr_toNat]; exact h.S1_toNat
  have e3 : (State.addr p.S3).toNat = p.sp.toNat - 96 := by rw [addr_toNat]; exact h.S3_toNat
  have ap := h.push_apart
  intro r hr
  simp only [keyChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine (Offset.disjoint_of_le (by simp only [BitVec.add_zero]; rw [e3, e1]; omega) ?_).symm
    simp only; rw [BitVec.add_zero, e1]; omega
  · exact (ap (inKey o) (by simp [inWrites])).sub_right (by rw [h.eK]; exact fun _ h => h)
  · exact (ap (inScr o) (by simp [inWrites])).sub_right (by rw [h.eS]; exact fun _ h => h)
  · refine (Offset.disjoint_of_le ?_ ?_).symm
    · simp only
      rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, ← FrameStack.addr_sub' (by rw [h.S3_toNat]; omega),
        addr_toNat, FrameStack.sub_toNat' (by rw [h.S3_toNat]; omega), h.S3_toNat, BitVec.add_zero, e1]
      omega
    · simp only; rw [BitVec.add_zero, e1]; omega

theorem state_apartK (h : GenFrame p o used st s) {d n : Nat} (hdn : d + n ≤ 56) :
    ∀ r ∈ keyChanges p, Region.Disjoint ⟨off p.st d, n⟩ r := by
  have cf := h.input.cfacts
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -, -⟩ := hst
  have sub : Region.Sub ⟨off p.st d, n⟩ (cT p) := Offset.sub_base _ hdn
  intro r hr
  simp only [keyChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (sT.sub_left h.a3Stack).symm.sub_left sub
  · exact cf.kT.symm.sub_left sub
  · exact cf.sT.symm.sub_left sub
  · exact (sT.sub_left h.f3Stack).symm.sub_left sub

/-- The key's call, in its frame of arguments. -/
theorem key_run (name : String) {kc : Prog isa} (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56))
    (hks : FrameStack.armStack kc ≤ 56) (h : GenFrame p o used st s) :
    WP isa (keyRun (.call name kc)) s (AfterKey p o used st s) := by
  have room := h.facts.room
  have hL := h.L_le
  have hsp56 : 56 ≤ s.sp.toNat := by rw [h.sp, h.S1_toNat]; omega
  unfold keyRun
  refine WP.alloc (by decide) hsp56 ?_
  refine WP.seq (WP.mono h.keyArgs_ok fun u ⟨hr, ku⟩ => ?_)
  obtain ⟨cov, covW⟩ := h.key_covers hr
  have hS3 : 56 ≤ u.sp.toNat := by rw [hr.sp, h.S3_toNat]; omega
  refine FrameStack.WP.callF hv.1 (pre_of_cin (h.callK_cin hr)) cov covW
    (Nat.le_trans hks hS3) fun t htr htw htsp hfr hpres hpost => ?_
  sig_post [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val] at hpost
  have a0 : stackArg (callK p u) 0 = p.kp + BitVec.ofNat 32 (4 * p.L) := h.kArg hr (by decide)
  have a1 : stackArg (callK p u) 1 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a2 : stackArg (callK p u) 2 = p.kp + BitVec.ofNat 32 (5 * p.L) := h.kArg hr (by decide)
  have a4 : stackArg (callK p u) 4 = p.kp + BitVec.ofNat 32 (6 * p.L) := h.kArg hr (by decide)
  have a6 : stackArg (callK p u) 6 = p.kp + BitVec.ofNat 32 (7 * p.L) := h.kArg hr (by decide)
  have a8 : stackArg (callK p u) 8 = p.kp + BitVec.ofNat 32 (8 * p.L) := h.kArg hr (by decide)
  have a10 : stackArg (callK p u) 10 = p.stp + BitVec.ofNat 32 48 := h.kArg hr (by decide)
  have a11 : stackArg (callK p u) 11 = BitVec.ofNat 32 8 := h.kArg hr (by decide)
  have t2 : (BitVec.ofNat 32 (2 * p.L)).toNat = 2 * p.L := toNat_small (by omega)
  have sl (j : Nat) (hj : j * p.L < 9 * p.L) : BitVec.setWidth 64 (p.kp + BitVec.ofNat 32 (j * p.L)) = p.slot j :=
    kAddr h hj
  have s0 : BitVec.setWidth 64 p.kp = State.addr p.kp := rfl
  have se : BitVec.setWidth 64 (p.stp + BitVec.ofNat 32 48) = off p.st 48 := congrArg Region.base h.eE
  simp only [a0, a1, a2, a4, a6, a8, a10, a11, hr.r0, hr.r1, hr.r2, h.tL, t2,
    show (BitVec.ofNat 32 8).toNat = 8 from rfl, sl 4 (by omega), sl 5 (by omega), sl 6 (by omega),
    sl 7 (by omega), sl 8 (by omega), sl 2 (by omega), s0, se] at hpost
  -- the entry's memory
  have fa := h.frame_kargs hr
  have hst := h.input.cfacts.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -, -⟩ := hst
  have kb (j : Nat) (hj : j * p.L + p.L ≤ 9 * p.L) :
      Spec.Rsa.bytesAt u.mem (p.slot j) p.L = Spec.Rsa.bytesAt s.mem (p.slot j) p.L :=
    bytes_kept fa (fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'
      exact (sK.sub_left h.a3Stack).symm.sub_left (kSubK hj)) (by omega)
  have eb : Spec.Rsa.bytesAt u.mem (off p.st 48) 8 = p.eB := by
    rw [bytes_kept fa (fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'
      exact (sT.sub_left h.a3Stack).symm.sub_left (Offset.sub_base _ (by decide))) (by decide)]
    exact h.state.e
  rw [eb, kb 4 (by omega), kb 5 (by omega)] at hpost
  obtain ⟨hstat, hout⟩ := hpost
  -- the frames
  have f0 : Frame (keyChanges p) s.mem u.mem :=
    fa.sub fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'; exact ⟨rA3 p, by simp [keyChanges], fun _ h => h⟩
  have f1 : Frame (keyChanges p) u.mem t.mem := by
    refine hfr.sub fun r hr' => ?_
    have mK : cK p ∈ keyChanges p := by simp [keyChanges]
    rcases List.mem_append.mp hr' with hr' | hr'
    · simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cK p, mK, Region.sub_prefix (by omega)⟩
      · exact ⟨cK p, mK, by rw [h.kOut_eq (by omega)]; exact kSubK (by omega)⟩
      · exact ⟨cK p, mK, by rw [h.kOut_eq (by omega)]; exact kSubK (by omega)⟩
      · exact ⟨cK p, mK, by rw [h.kOut_eq (by omega)]; exact kSubK (by omega)⟩
      · exact ⟨cK p, mK, by rw [h.kOut_eq (by omega)]; exact kSubK (by omega)⟩
      · exact ⟨cK p, mK, by rw [h.kOut_eq (by omega)]; exact kSubK (by omega)⟩
      · exact ⟨cK p, mK, by rw [h.kOut_eq (by omega)]; exact kSubK (by omega)⟩
      · exact ⟨cS p, by simp [keyChanges], fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr'
      refine ⟨rF3 p, by simp [keyChanges], ?_⟩
      rw [hr.sp]
      change Region.Sub ⟨State.addr (p.S3 - BitVec.ofNat 32 (FrameStack.armStack kc)), _⟩ _
      rw [FrameStack.addr_sub' (by rw [h.S3_toNat]; omega), rF3,
        show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl]
      exact Offset.sub_below _ hks (by omega)
  have hframe := f0.trans f1
  have hreg : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3, .r12, .lr] → t.gpr r = s.gpr r := fun r hr' =>
    (hpres r (callRegs r hr').1 (callRegs r hr').2).trans (ku.gpr r hr')
  have k : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s (freed 56 t) :=
    ⟨hreg, htr.trans (ku.rd.trans rfl), show t.wr.tail = s.wr by rw [htw, ku.wr]; rfl,
      show t.sp + BitVec.ofNat 32 56 = s.sp by rw [htsp, ku.sp]; exact BitVec.sub_add_cancel _ _⟩
  have hstk : StateOk p st t.mem := h.state.frame hframe fun r hr' => by
    have := h.state_apartK (d := 0) (n := 56) (by decide) r hr'
    simpa only [off, BitVec.add_zero] using this
  refine ⟨h.stepTo k (by decide) hframe h.keyChanges_sub h.keyChanges_apart hstk, hreg .r11 (by decide), ?_, ?_,
    hframe⟩
  · rw [← hstat, BitVec.setWidth_append_eq_right]; rfl
  · revert hout
    dsimp only [keyOf]
    generalize keyOp p.L p.eB (Spec.Rsa.bytesAt s.mem (p.slot 4) p.L) (Spec.Rsa.bytesAt s.mem (p.slot 5) p.L) = res
    rcases res with (f | ys) | u'
    · intro hout o' ho
      simp only [keyOutsOf, List.mem_cons, List.not_mem_nil, or_false] at ho
      obtain ⟨o0, o1, o2, o3, o4, o5, o6⟩ := hout
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [o0, o1, o2, o3, o4, o5, o6]
    · intro hout; exact hout
    · intro hout o' ho
      simp only [keyOutsOf, List.mem_cons, List.not_mem_nil, or_false] at ho
      obtain ⟨o0, o1, o2, o3, o4, o5, o6⟩ := hout
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [o0, o1, o2, o3, o4, o5, o6]

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The controller's stores to its state (ARMv7)

The blocks that set the state's words from their halves: the next prime's
search (`nextPrime`), the end of the key search (`finishWith`), and one
generation fewer (`decLeft`). They write within the state's words 0 and 4–5
(`stW`), and keep the others.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-- The state's words the controller's stores write: 0, 4 and 5. -/
abbrev stW (p : GenPublic) : List Region := [⟨off p.st 0, 8⟩, ⟨off p.st 32, 16⟩]

theorem off_add4 (a : Addr) (d : Nat) : off a d + BitVec.ofNat 64 4 = off a (d + 4) := by
  rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem st_self (p : GenPublic) (m : Mem) (d : Nat) (v : BitVec 32) :
    (m.writeW (off p.st d) v).readW (off p.st d) 32 = v := Mem.readW_writeW_self32 _ _ _

theorem st_sep (p : GenPublic) (m : Mem) {d e w : Nat} (hde : d + w / 8 ≤ e ∨ e + 4 ≤ d) (hd : d + w / 8 ≤ 56)
    (he : e + 4 ≤ 56) (hw : w / 8 < 2 ^ 64) (v : BitVec 32) :
    (m.writeW (off p.st e) v).readW (off p.st d) w = m.readW (off p.st d) w :=
  Mem.readW_writeW_sep (Offset.sep p.st (n := w / 8) (k := 32 / 8) hde (by omega) (by omega)) hw

theorem stW_write {p : GenPublic} {m m' : Mem} (hf : Frame (stW p) m m') {d : Nat}
    (hd : d + 4 ≤ 8 ∨ 32 ≤ d ∧ d + 4 ≤ 48) (v : BitVec 32) : Frame (stW p) m (m'.writeW (off p.st d) v) := by
  rcases hd with hd | hd
  · exact hf.writeW (r := ⟨off p.st 0, 8⟩) (List.mem_cons_self ..) v (by
      rw [show off p.st d = off p.st 0 + BitVec.ofNat 64 d by rw [off, off, BitVec.add_zero]]
      exact Offset.contains_base _ (show d + 32 / 8 ≤ 8 by omega) (by omega))
  · exact hf.writeW (r := ⟨off p.st 32, 16⟩) (by simp) v (by
      rw [show off p.st d = off p.st 32 + BitVec.ofNat 64 (d - 32) by
        rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
      exact Offset.contains_base _ (show d - 32 + 32 / 8 ≤ 16 by omega) (by omega))

theorem stW_kept {p : GenPublic} {m m' : Mem} (_hf : Frame (stW p) m m') {d n : Nat}
    (hd : 8 ≤ d ∧ d + n ≤ 32 ∨ 48 ≤ d ∧ d + n ≤ 56) : ∀ r ∈ stW p, Region.Disjoint ⟨off p.st d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- A word of the state from its halves. -/
theorem st_word {p : GenPublic} {m : Mem} {d n : Nat} (hn : n < 2 ^ 32)
    (hlo : m.readW (off p.st d) 32 = BitVec.ofNat 32 n) (hhi : m.readW (off p.st (d + 4)) 32 = 0) :
    m.readW (off p.st d) 64 = BitVec.ofNat 64 n :=
  word_of_halves (by omega) (by rw [hlo, Nat.mod_eq_of_lt hn])
    (by rw [off_add4, hhi, Nat.div_eq_of_lt hn]; rfl)

namespace GenFrame

variable {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress}

theorem stW_changes (h : GenFrame p o used st s) : ∀ r ∈ stW p, ∃ q ∈ changes o, Region.Sub r q := by
  intro r hr
  refine ⟨inState o, by simp [changes, inWrites], ?_⟩
  rw [h.eT']
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)

theorem stW_apart (h : GenFrame p o used st s) :
    ∀ r ∈ stW p, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r := by
  intro r hr
  have := h.push_apart (inState o) (by simp [inWrites])
  rw [h.eT'] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact this.sub_right (Offset.sub_base _ (by decide))

/-- The state for the progress `st'` after stores within `stW`: its words 0,
4 and 5 for `st'`. -/
theorem restate (h : GenFrame p o used st s) {m : Mem} (hf : Frame (stW p) s.mem m) {st' : KeyProgress}
    (h0 : m.readW (off p.st 0) 64 = BitVec.ofNat 64 st'.remaining)
    (h32 : m.readW (off p.st 32) 64 = BitVec.ofNat 64 (phaseWord st'.phase))
    (h40 : m.readW (off p.st 40) 64 = BitVec.ofNat 64 st'.left)
    (hle : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64) : StateOk p st' m := by
  have w (d : Nat) (hd : 8 ≤ d ∧ d + 8 ≤ 32) : m.readW (off p.st d) 64 = s.mem.readW (off p.st d) 64 :=
    hf.readW (r := ⟨off p.st d, 8⟩) (by
      have := Offset.contains_base (off p.st d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this) (stW_kept hf (.inl hd)) (by decide)
  refine ⟨h0, by rw [w 8 (by decide)]; exact h.state.len, by rw [w 16 (by decide)]; exact h.state.cap, h32, h40,
    ?_, hle, hlt⟩
  rw [bytes_kept hf (stW_kept hf (.inr (by decide))) (by decide)]
  exact h.state.e

theorem limit_lt (h : GenFrame p o used st s) : limitOf p.L p.eB < 2 ^ 32 := by
  have := h.L_le
  unfold limitOf primeLimit; split <;> omega

/-! ### The blocks -/

theorem nextPrime_ok (h : GenFrame p o used st s) (ph : KeyPhase) :
    WP isa (.block (nextPrime (phaseWord ph))) s fun t =>
      (t.gpr .r11 = 4 ∧ t.mem = (((s.mem.writeW (off p.st 0) (BitVec.ofNat 32 (limitOf p.L p.eB))).writeW
        (off p.st 4) (0 : BitVec 32)).writeW (off p.st 36) (0 : BitVec 32)).writeW (off p.st 32) (BitVec.ofNat 32 (phaseWord ph))) ∧
      Rest [.r11, .r12] s t := by
  refine withRest_all [.r11, .r12] ?_ (by rfl) (by rfl)
  have hw := h.wr
  have hrd := h.rd
  have w0 : InRegions s.wr (State.addr p.stp) 4 := by
    have := h.state_wr hw (u := s) (d := 0) (by decide); simpa only [off, BitVec.add_zero] using this
  unfold nextPrime
  have aT (d : Nat) (hd : d < 56) : State.addr (p.stp + BitVec.ofNat 32 d) = off p.st d :=
    VG.Arm.addr_add (by have := h.facts.nT; omega)
  have enc : encodable (BitVec.ofNat 32 (phaseWord ph)) = true := by cases ph <;> simp only [phaseWord] <;> decide
  ffrun [enc, w0, h.r9, h.r10, aT 4 (by decide), aT 32 (by decide), aT 36 (by decide), BitVec.add_zero,
    h.state_wr hw (u := s) (d := 4) (by decide), h.state_wr hw (u := s) (d := 32) (by decide),
    h.state_wr hw (u := s) (d := 36) (by decide), show (0 : BitVec 32) = 0#32 from rfl]
  done

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## After a prime's search (ARMv7)

The octets the search consumed added to `r8`, its status against 0 (the
head of `classify`), and the state that leaves (`Mid`): the frame for the
octets consumed so far and the search's counted candidates left, its status
and consumption in registers, and the key's buffer. The loop's ends: a state
that ended the key search (`GenDone`), and the measure each step that goes on
lowers.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

/-- What a prime's search leaves: its prime's octets, or zeros. -/
def outBytes (L : Nat) (r : PrimeSearchResult) : List Byte :=
  match r.outcome with
  | .accepted c => Spec.Rsa.i2osp c L
  | _ => List.replicate L 0

/-- The search of the progress' prime from octet `used`. -/
abbrev rOf (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) : PrimeSearchResult :=
  primeOf p.L p.eB st ((genRand o).drop used)

/-- A loop state that ended the key search with `final`: the frame for its
consumption and its state for the next call, its status in `r11`, the key's
buffer, and its request in the state. -/
def GenDone (p : GenPublic) (o : State) (final : KeySearchResult) (s : State) : Prop :=
  GenFrame p o final.used final.progress s ∧ s.gpr .r11 = BitVec.ofNat 32 final.keyStatus ∧
    Spec.Rsa.bytesAt s.mem (State.addr p.kp) (9 * p.L) = keySearchBytes p.L final ∧
    ∃ requested, s.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested

/-- What each step that goes on lowers: the octets left of the tape, then the
generations left. -/
def genMeasure (p : GenPublic) (used : Nat) (st : KeyProgress) : Nat := (p.randLen - used) * 2 ^ 64 + st.left

/-- After a search and the count of the octets it consumed. -/
structure Mid (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (u : State) : Prop where
  frame : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ u
  r11 : u.gpr .r11 = 4
  final : ∃ tr, final = (tailOf p o used st).consume used tr
  low : Spec.Rsa.bytesAt u.mem (State.addr p.kp) (4 * p.L) = List.replicate (4 * p.L) 0
  slot4 : Spec.Rsa.bytesAt u.mem (p.slot 4) p.L =
    (match st.phase with
      | .p => outBytes p.L (rOf p o used st)
      | .q pB => pB)
  slot5 : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L =
    (match st.phase with
      | .p => List.replicate p.L 0
      | .q _ => outBytes p.L (rOf p o used st))
  high : Spec.Rsa.bytesAt u.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0
  req : ∃ requested, u.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 requested ∧
    (rOf p o used st).Requests (primeEntropy p.L) requested

theorem bytesAt_add (m : Mem) (a : Addr) (x y : Nat) :
    Spec.Rsa.bytesAt m a (x + y) = Spec.Rsa.bytesAt m a x ++ Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem slot_add (p : GenPublic) (j n : Nat) : p.slot j + BitVec.ofNat 64 (n * p.L) = p.slot (j + n) := by
  rw [GenPublic.slot, GenPublic.slot, Offset.add_add, Nat.add_mul]

theorem slot_addL (p : GenPublic) (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
  rw [← slot_add, Nat.one_mul]

/-- The key's buffer: the low four slots, `p`'s, `q`'s and the high three. -/
theorem key_bytes (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m (State.addr p.kp) (9 * p.L) = Spec.Rsa.bytesAt m (State.addr p.kp) (4 * p.L) ++
      Spec.Rsa.bytesAt m (p.slot 4) p.L ++ Spec.Rsa.bytesAt m (p.slot 5) p.L ++
      Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) := by
  rw [show 9 * p.L = 4 * p.L + p.L + p.L + 3 * p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]

/-- The key's buffer, as the key's outputs. -/
theorem key_outs (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m (State.addr p.kp) (9 * p.L) =
      ((keyOutsOf p).map fun o => Spec.Rsa.bytesAt m o.1 o.2).flatten := by
  simp only [keyOutsOf, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show 9 * p.L = 2 * p.L + 2 * p.L + p.L + p.L + p.L + p.L + p.L by omega]
  rw [bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    show 2 * p.L + 2 * p.L = 4 * p.L by omega, show 4 * p.L + p.L = 5 * p.L by omega,
    show 5 * p.L + p.L = 6 * p.L by omega, show 6 * p.L + p.L = 7 * p.L by omega,
    show 7 * p.L + p.L = 8 * p.L by omega]
  simp only [List.append_assoc]

namespace GenFrame

variable {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress}

theorem genRand_length (h : GenFrame p o used st s) : (genRand o).length = p.randLen := by
  have hg : genRand o = Spec.Rsa.bytesAt o.mem (State.addr p.rp) p.randLen := by rw [← h.input.2]; rfl
  rw [hg]; simp [Spec.Rsa.bytesAt]

theorem rOf_used_le (h : GenFrame p o used st s) : used + (rOf p o used st).used ≤ p.randLen := by
  have h2 : (rOf p o used st).used ≤ p.randLen - used := by
    have := Spec.RsaKeyGen.primeSearch_used_le p.L p.eB st.phase.other st.remaining ((genRand o).drop used)
    rw [List.length_drop, h.genRand_length] at this
    exact this
  have := h.used_le
  omega

/-- A part of the key's buffer apart from the search's output is kept through
the search. -/
theorem search_kept (h : GenFrame p o used st s) (hm : Frame (callChanges p st) s.mem t.mem) {d n : Nat}
    (hdn : d + n ≤ 9 * p.L) (hO : (kRegion p d n).Disjoint (rO p st)) :
    Spec.Rsa.bytesAt t.mem (State.addr p.kp + BitVec.ofNat 64 d) n =
      Spec.Rsa.bytesAt s.mem (State.addr p.kp + BitVec.ofNat 64 d) n := by
  have cf := h.input.cfacts
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, -, -, -⟩ := hst
  have hR : Region.Sub (kRegion p d n) (cK p) := kSubK hdn
  refine bytes_kept hm (fun q hq => ?_) (by have := h.facts.nK; omega)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (sK.sub_left h.aStack).symm.sub_left hR
  · exact hO
  · exact cf.kU.sub_left hR
  · exact cf.kS.sub_left hR
  · exact (cf.kT.sub_left hR).sub_right tT
  · exact (sK.sub_left low_sub).symm.sub_left hR

theorem rO_eq (h : GenFrame p o used st s) : rO p st = kRegion p (outOf p st) p.L := h.eO

/-- The status and the count of the octets consumed, after the search. -/
theorem after_head {final : KeySearchResult} (hl : GenLive p o used st s)
    (hfin : ∃ tr, final = (tailOf p o used st).consume used tr) (ha : AfterSearch p o used st s t) :
    WP isa (.block [.ldr .r12 .r6 0, .dp .add .r8 .r8 (.reg .r12), .cmp .r0 (.imm 0)]) t fun u =>
      isa.eval .eq u = some (decide ((rOf p o used st).status = 0)) ∧
        u.gpr .r0 = BitVec.ofNat 32 (rOf p o used st).status ∧
        u.gpr .r12 = BitVec.ofNat 32 (rOf p o used st).used ∧ Mid p o final used st u := by
  have h := hl.toGenFrame
  have hf := ha.frame
  have hL := h.L_le
  have hle := h.rOf_used_le
  have hst := hl.key
  have hs32 : (rOf p o used st).status < 2 ^ 32 := by
    unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
  have h0 : t.gpr .r0 = BitVec.ofNat 32 (rOf p o used st).status := by
    rw [← ha.status]; exact (ofNat_toNat32 _).symm
  have hU : InRegions (t.rd ++ t.wr) (State.addr p.up) 4 := by
    refine ⟨cU p, List.mem_append_right _ ?_, ?_⟩
    · rw [hf.wr, h.input.wr, inWrites, h.eU]; simp
    · have := Offset.contains_base (State.addr p.up) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
  have hu32 : t.mem.readW (State.addr p.up) 32 = BitVec.ofNat 32 (rOf p o used st).used := low_half ha.usedw
  refine WP.mono (withRest_all [.r8, .r12] (c := .block [.ldr .r12 .r6 0, .dp .add .r8 .r8 (.reg .r12),
      .cmp .r0 (.imm 0)])
    (Q := fun u => isa.eval .eq u = some (decide ((rOf p o used st).status = 0)) ∧
      u.gpr .r12 = BitVec.ofNat 32 (rOf p o used st).used ∧
      u.gpr .r8 = BitVec.ofNat 32 (used + (rOf p o used st).used) ∧ u.mem = t.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨he, h12, h8, hm⟩, k⟩ => ⟨he, (k.gpr .r0 (by decide)).trans h0, h12, ?_⟩
  · ffrun [hf.r6, hf.r8, h0, hU, hu32, BitVec.add_zero, add_ofNat32]
    exact congrArg some (Search.sub_eq_beq hs32 (by decide))
  -- the key's buffer
  have kept {d n : Nat} (hdn : d + n ≤ 9 * p.L) (hO : (kRegion p d n).Disjoint (rO p st)) :=
    h.search_kept ha.mem hdn hO
  have hO := h.rO_eq (st := st)
  have hpl := plen_le (p := p) st
  have hoo := outOf_eq p st
  have hlow : Spec.Rsa.bytesAt t.mem (State.addr p.kp) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [← hst.low]
    have := kept (d := 0) (n := 4 * p.L) (by omega) (by
      rw [hO]; exact h.kDisjoint (.inl (by omega)) (by omega) (by omega))
    simpa only [BitVec.add_zero] using this
  have hsplit : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) =
      Spec.Rsa.bytesAt s.mem (p.slot 5) p.L ++ Spec.Rsa.bytesAt s.mem (p.slot 6) (3 * p.L) := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add, slot_addL]
  have hhigh5 := hst.high
  rw [hsplit, show 4 * p.L = p.L + 3 * p.L by omega, ← List.replicate_append_replicate] at hhigh5
  obtain ⟨h5s, h6s⟩ := List.append_inj hhigh5 (by simp [Spec.Rsa.bytesAt])
  have hhigh : Spec.Rsa.bytesAt t.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0 := by
    rw [← h6s]
    exact kept (d := 6 * p.L) (n := 3 * p.L) (by omega) (by
      rw [hO]; exact h.kDisjoint (.inr (by rw [hoo]; omega)) (by omega) (by rw [hoo]; omega))
  have hout := ha.out
  have hs4 : Spec.Rsa.bytesAt t.mem (p.slot 4) p.L =
      (match st.phase with
        | .p => outBytes p.L (rOf p o used st)
        | .q pB => pB) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      have ho : State.addr (p.kp + BitVec.ofNat 32 (outOf p ⟨left, .p, remaining⟩)) = p.slot 4 := by
        rw [kAddr h (by simp only [outOf, phaseWord]; omega)]; simp [outOf, phaseWord]
      rw [ho] at hout
      rw [hout]; rfl
    | q pB =>
      rw [← hst.other pB rfl]
      exact kept (d := 4 * p.L) (n := p.L) (by omega) (by
        rw [hO]; exact h.kDisjoint (.inl (by simp only [outOf, phaseWord]; omega)) (by omega)
          (by simp only [outOf, phaseWord]; omega))
  have hs5 : Spec.Rsa.bytesAt t.mem (p.slot 5) p.L =
      (match st.phase with
        | .p => List.replicate p.L 0
        | .q _ => outBytes p.L (rOf p o used st)) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      rw [← h5s]
      exact kept (d := 5 * p.L) (n := p.L) (by omega) (by
        rw [hO]; exact h.kDisjoint (.inr (by simp only [outOf, phaseWord]; omega)) (by omega)
          (by simp only [outOf, phaseWord]; omega))
    | q pB =>
      have ho : State.addr (p.kp + BitVec.ofNat 32 (outOf p ⟨left, .q pB, remaining⟩)) = p.slot 5 := by
        rw [kAddr h (by simp only [outOf, phaseWord]; omega)]; simp [outOf, phaseWord]
      rw [ho] at hout
      rw [hout]; rfl
  obtain ⟨req, hreq, hreqs⟩ := ha.req
  have hg : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ u :=
    ⟨hf.input, hle, k.rd.trans hf.rd, k.wr.trans hf.wr, k.sp.trans hf.sp, (k.gpr .r4 (by decide)).trans hf.r4,
      (k.gpr .r5 (by decide)).trans hf.r5, (k.gpr .r6 (by decide)).trans hf.r6,
      (k.gpr .r7 (by decide)).trans hf.r7, h8, (k.gpr .r9 (by decide)).trans hf.r9,
      (k.gpr .r10 (by decide)).trans hf.r10, hm ▸ hf.saved, hm ▸ hf.frame, hm ▸ hf.state⟩
  exact ⟨hg, (k.gpr .r11 (by decide)).trans (ha.r11.trans hl.r11), hfin,
    hm ▸ hlow, hm ▸ hs4, hm ▸ hs5, hm ▸ hhigh, ⟨req, hm ▸ hreq, hreqs⟩⟩

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## How a step ends (ARMv7)

The end of the key search (`finishWith`, and `fail` after zeros at the key's
buffer), to `GenDone`; the start of the next prime's search (`nextPrime`), to
a loop state; one generation fewer (`decLeft`).
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

namespace GenFrame

variable {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress}

theorem stW_key (h : GenFrame p o used st s) {m m' : Mem} (hf : Frame (stW p) m m') {d n : Nat}
    (hdn : d + n ≤ 9 * p.L) :
    Spec.Rsa.bytesAt m' (State.addr p.kp + BitVec.ofNat 64 d) n =
      Spec.Rsa.bytesAt m (State.addr p.kp + BitVec.ofNat 64 d) n := by
  have cf := h.input.cfacts
  refine bytes_kept hf (fun q hq => ?_) (by have := h.facts.nK; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> exact (cf.kT.sub_left (kSubK hdn)).sub_right (Offset.sub_base _ (by decide))

theorem stW_key0 (h : GenFrame p o used st s) {m m' : Mem} (hf : Frame (stW p) m m') {n : Nat}
    (hn : n ≤ 9 * p.L) :
    Spec.Rsa.bytesAt m' (State.addr p.kp) n = Spec.Rsa.bytesAt m (State.addr p.kp) n := by
  have := h.stW_key hf (d := 0) (n := n) (by omega)
  simpa only [BitVec.add_zero] using this

theorem stW_req {m m' : Mem} (hf : Frame (stW p) m m') :
    m'.readW (off p.st 24) 64 = m.readW (off p.st 24) 64 :=
  hf.readW (r := ⟨off p.st 24, 8⟩) (by
    have := Offset.contains_base (off p.st 24) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
    simpa only [BitVec.add_zero] using this) (stW_kept hf (.inl (by decide))) (by decide)

theorem finishWith_ok (h : GenFrame p o used st s) {status : Nat} (hs : status < 4) :
    WP isa (.block (finishWith status)) s fun t =>
      (t.gpr .r11 = BitVec.ofNat 32 status ∧ t.mem = (((s.mem.writeW (off p.st 32) (0 : BitVec 32)).writeW
        (off p.st 36) (0 : BitVec 32)).writeW (off p.st 40) (0 : BitVec 32)).writeW (off p.st 44) (0 : BitVec 32)) ∧
      Rest [.r11, .r12] s t := by
  refine withRest_all [.r11, .r12] ?_ (by rfl) (by rfl)
  have hw := h.wr
  have aT (d : Nat) (hd : d < 56) : State.addr (p.stp + BitVec.ofNat 32 d) = off p.st d :=
    VG.Arm.addr_add (by have := h.facts.nT; omega)
  have enc : encodable (BitVec.ofNat 32 status) = true := by
    rcases (by omega : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3) with rfl | rfl | rfl | rfl <;> decide
  unfold finishWith
  ffrun [enc, h.r9, aT 32 (by decide), aT 36 (by decide), aT 40 (by decide), aT 44 (by decide),
    h.state_wr hw (u := s) (d := 32) (by decide), h.state_wr hw (u := s) (d := 36) (by decide),
    h.state_wr hw (u := s) (d := 40) (by decide), h.state_wr hw (u := s) (d := 44) (by decide),
    show (0 : BitVec 32) = 0#32 from rfl]

/-- The end of the key search with `final`. -/
theorem finish_done (h : GenFrame p o used st s) {final : KeySearchResult} {status : Nat} (hstat : status < 4)
    (hu : final.used = used) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0)
    (hkey : Spec.Rsa.bytesAt s.mem (State.addr p.kp) (9 * p.L) = keySearchBytes p.L final)
    (hreq : ∃ requested, s.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (.block (finishWith status)) s (GenDone p o final) := by
  refine WP.mono (h.finishWith_ok hstat) fun t ⟨⟨h11, hm⟩, k⟩ => ?_
  have hf : Frame (stW p) s.mem t.mem := by
    rw [hm]
    exact stW_write (stW_write (stW_write (stW_write (Frame.refl _ _) (.inr (by decide)) _) (.inr (by decide)) _)
      (.inr (by decide)) _) (.inr (by decide)) _
  have hw (d : Nat) (hd : d = 32 ∨ d = 36 ∨ d = 40 ∨ d = 44) : t.mem.readW (off p.st d) 32 = 0 := by
    rw [hm]
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [st_self, st_sep]
  have h0 : t.mem.readW (off p.st 0) 64 = BitVec.ofNat 64 0 := by
    rw [hm]
    simp (disch := decide) only [st_sep]
    rw [h.state.remaining, hr0]
  have hst : StateOk p ⟨0, .p, 0⟩ t.mem :=
    h.restate hf h0 (st_word (by decide) (hw 32 (by decide)) (hw 36 (by decide)))
      (st_word (by decide) (hw 40 (by decide)) (hw 44 (by decide))) (Nat.zero_le _) (by decide)
  obtain ⟨req, hrw, hr⟩ := hreq
  refine ⟨?_, by rw [h11, hs], by rw [h.stW_key0 hf (by omega), hkey], ⟨req, by rw [stW_req hf, hrw], hr⟩⟩
  rw [hu, hpr]
  exact h.stepTo k (by decide) hf h.stW_changes h.stW_apart hst

/-- `fail status`: zeros at the key's buffer, and the end of the key search
with `final`. -/
theorem fail_done (h : GenFrame p o used st s) {final : KeySearchResult} {status : Nat} (hstat : status < 4)
    (hu : final.used = used) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0) (hz : keySearchBytes p.L final = List.replicate (9 * p.L) 0)
    (hreq : ∃ requested, s.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (fail status) s (GenDone p o final) := by
  have cf := h.input.cfacts
  unfold fail
  refine WP.seq (WP.mono (clearAll_ok h) fun w ⟨g, z, fr, _⟩ => ?_)
  obtain ⟨req, hw, hr⟩ := hreq
  refine g.finish_done hstat hu hpr hs hr0 (z.trans hz.symm) ⟨req, ?_, hr⟩
  refine Eq.trans (fr.readW (r := ⟨off p.st 24, 8⟩)
    (by have := Offset.contains_base (off p.st 24) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
        simpa only [BitVec.add_zero] using this) (fun q hq => ?_) (by decide)) hw
  obtain rfl := List.mem_singleton.mp hq
  exact (cf.kT.sub_left (kSubK (by omega))).symm.sub_left (Offset.sub_base _ (by decide))

/-- The start of the next prime's search, for the progress `st'` (from all
its counted candidates, in phase `ph`): a loop state. -/
theorem cont_of (h : GenFrame p o used st s) (ph : KeyPhase) {st' : KeyProgress} (hph : st'.phase = ph)
    (hl : st'.left = st.left) (hrem : st'.remaining = limitOf p.L p.eB)
    (hlow : Spec.Rsa.bytesAt s.mem (State.addr p.kp) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hhigh : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hother : ∀ pB, ph = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    WP isa (.block (nextPrime (phaseWord ph))) s fun t =>
      GenLive p o used st' t ∧ t.mem.readW (off p.st 24) 64 = s.mem.readW (off p.st 24) 64 ∧
        Rest [.r11, .r12] s t := by
  have hL := h.L_le
  refine WP.mono (h.nextPrime_ok ph) fun t ⟨⟨h11, hm⟩, k⟩ => ?_
  have hf : Frame (stW p) s.mem t.mem := by
    rw [hm]
    exact stW_write (stW_write (stW_write (stW_write (Frame.refl _ _) (.inl (by decide)) _) (.inl (by decide)) _)
      (.inr (by decide)) _) (.inr (by decide)) _
  have hlim := h.limit_lt
  have hp1 := phaseWord_le ph
  have h0 : t.mem.readW (off p.st 0) 64 = BitVec.ofNat 64 st'.remaining := by
    rw [hrem]
    refine st_word hlim ?_ ?_ <;> rw [hm] <;> simp (disch := decide) only [st_self, st_sep]
  have h32 : t.mem.readW (off p.st 32) 64 = BitVec.ofNat 64 (phaseWord st'.phase) := by
    rw [hph]
    refine st_word (by omega) ?_ ?_ <;> rw [hm] <;> simp (disch := decide) only [st_self, st_sep]
  have h40 : t.mem.readW (off p.st 40) 64 = BitVec.ofNat 64 st'.left := by
    rw [hm]
    simp (disch := decide) only [st_sep]
    rw [h.state.left, hl]
  have hst : StateOk p st' t.mem :=
    h.restate hf h0 h32 h40 (by rw [hrem]) (by rw [hl]; exact h.state.left_lt)
  refine ⟨⟨h.stepTo k (by decide) hf h.stW_changes h.stW_apart hst, h11, ?_, ?_, ?_⟩, stW_req hf, k⟩
  · rw [h.stW_key0 hf (by omega), hlow]
  · rw [show p.slot 5 = State.addr p.kp + BitVec.ofNat 64 (5 * p.L) from rfl, h.stW_key hf (by omega)]
    exact hhigh
  · intro pB hpB
    rw [show p.slot 4 = State.addr p.kp + BitVec.ofNat 64 (4 * p.L) from rfl, h.stW_key hf (by omega)]
    exact hother pB (hph ▸ hpB)

end GenFrame

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## After a prime's search, its outcome (ARMv7)

`classify`: more entropy ends the key search; an exhausted search, the next
generation or the end; an accepted prime having read nothing, the end;
`p`, `q`'s search next; `q`, the key, which ends the key search or, for a `d`
too small, starts both primes again. Each step either ends the key search
(`GenDone`) or goes on to a loop state of a lower measure (`StepPost`).
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf ks_entropy ks_exhausted_last ks_exhausted_next
  ks_accepted_none ks_accepted_p ks_accepted_key ks_accepted_small primeEntry consume_consume)

/-- How the key search goes on after the prime's search `r` from the progress
`st`: to the progress `st'`, with `e` this step's trace. -/
def NextPub (st : KeyProgress) (r : PrimeSearchResult) (st' : KeyProgress) (e : List Nat) : Prop :=
  (r.outcome = .exhausted ∧ st'.left = st.left - 1 ∧ st'.phase = .p ∧ e = primeEntry r) ∨
  (∃ c, r.outcome = .accepted c ∧ st.phase = .p ∧ st'.left = st.left ∧ phaseWord st'.phase = 1 ∧
    e = primeEntry r) ∨
  (∃ c pB, r.outcome = .accepted c ∧ st.phase = .q pB ∧ st'.left = st.left ∧ st'.phase = .p ∧
    e = primeEntry r ++ [1, 2])

/-- After a step that goes on: the next prime's search, from all its counted
candidates and a lower measure, no request in the state. -/
def ContPost (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  ∃ st' e, GenIter p o final (used + (rOf p o used st).used) st' t ∧
    genMeasure p (used + (rOf p o used st).used) st' < genMeasure p used st ∧
    t.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 0 ∧ st'.remaining = limitOf p.L p.eB ∧
    tailOf p o used st = (tailOf p o (used + (rOf p o used st).used) st').consume (rOf p o used st).used e ∧
    NextPub st (rOf p o used st) st' e

/-- Whether the key search goes on after the prime's search from `st`: to the
next generation, to `q` after `p`, or to both primes again after a `d` too
small. -/
def ContSpec (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) : Prop :=
  ((rOf p o used st).outcome = .exhausted ∧ ¬st.left < 2) ∨
  (∃ c, (rOf p o used st).outcome = .accepted c ∧ (rOf p o used st).used ≠ 0 ∧
    (st.phase = .p ∨ ∃ pB, st.phase = .q pB ∧ keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) = .inr ()))

/-- After a step: the next prime's search, from a lower measure, or the key
search ended with `final`. -/
def StepPost (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  (ContSpec p o used st ∧ ContPost p o final used st t) ∨ (¬ContSpec p o used st ∧ GenDone p o final t)

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

theorem measure_le (p : GenPublic) {used n : Nat} {st st' : KeyProgress} (hl : st'.left < st.left) :
    genMeasure p (used + n) st' < genMeasure p used st := by
  unfold genMeasure
  have : (p.randLen - (used + n)) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem low_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (State.addr p.kp) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = 2 * p.L + 2 * p.L by omega, bytesAt_add, ← List.replicate_append_replicate]
  rw [h (State.addr p.kp, 2 * p.L) (by simp [keyOutsOf]), show State.addr p.kp + BitVec.ofNat 64 (2 * p.L) = p.slot 2
    from rfl, h (p.slot 2, 2 * p.L) (by simp [keyOutsOf])]

theorem high_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = p.L + p.L + p.L + p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show p.L + p.L + p.L = 3 * p.L by omega, show p.L + p.L = 2 * p.L by omega, slot_add, slot_add, slot_addL,
    h (p.slot 5, p.L) (by simp [keyOutsOf]), h (p.slot 6, p.L) (by simp [keyOutsOf]),
    h (p.slot 7, p.L) (by simp [keyOutsOf]), h (p.slot 8, p.L) (by simp [keyOutsOf]),
    List.replicate_append_replicate, List.replicate_append_replicate, List.replicate_append_replicate]
  exact congrArg (List.replicate · 0) (by simp only; omega)

theorem rOf_status (r : PrimeSearchResult) : r.status = r.outcome.status := rfl

/-- Through a block that keeps the memory and the controller's registers. -/
theorem Mid.keep {p : GenPublic} {o u v : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}
    (h : Mid p o final used st u) {ws : List Reg} (k : Rest ws u v) (hm : v.mem = u.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∉ ws := by decide) :
    Mid p o final used st v := by
  refine ⟨h.frame.keep k hm (fun r hr => hws r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)), (k.gpr .r11 (hws _ (by simp))).trans h.r11,
    h.final,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.low, h.slot4, h.slot5, h.high, h.req]

section

variable {p : GenPublic} {o u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem Mid.used_le (hm : Mid p o final used st u) : used + (rOf p o used st).used ≤ p.randLen :=
  hm.frame.used_le

/-- More entropy: so does the key search. -/
theorem classify_entropy (hm : Mid p o final used st u) {k a : Nat}
    (ho : (rOf p o used st).outcome = .entropy k a) :
    WP isa (.block [.mov .r11 (.imm 0)]) u (StepPost p o final used st) := by
  have hrem : (rOf p o used st).remaining = k := by simp only [PrimeSearchResult.remaining, ho]
  have hframe := hm.frame
  rw [hrem] at hframe
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_entropy (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho
  have hfinal : final = ⟨.entropy ⟨st.left, st.phase, k⟩ a, used + (rOf p o used st).used,
      tr ++ primeEntry (rOf p o used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  refine WP.mono (withRest_all [.r11] (c := .block [.mov .r11 (.imm 0)]) (Q := fun t => t.gpr .r11 = 0 ∧
    t.mem = u.mem) (by ffrun []) (by rfl) (by rfl)) fun t ⟨⟨h11, htm⟩, kt⟩ =>
    .inr ⟨(by rintro (⟨h, -⟩ | ⟨c, h, -⟩) <;> rw [ho] at h <;> cases h), ?_⟩
  have hg := hframe.keep kt htm
  obtain ⟨req, hw, hr⟩ := hm.req
  subst hfinal
  refine ⟨hg, h11, ?_, ⟨req, by rw [htm]; exact hw, ?_⟩⟩
  · rw [htm, key_bytes, hm.low, hm.slot4, hm.slot5, hm.high]
    have hout : outBytes p.L (rOf p o used st) = List.replicate p.L 0 := by simp only [outBytes, ho]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only [hout, keySearchBytes, List.replicate_append_replicate]
      congr 1; omega
    | q pB =>
      simp only [hout, keySearchBytes, List.append_assoc, List.replicate_append_replicate]
      congr 3; omega
  · simp only [Spec.Entropy.Result.Requests, ho] at hr ⊢
    exact hr

/-- An exhausted search, its generation the last: the key search is exhausted. -/
theorem classify_last (hm : Mid p o final used st u) (ho : (rOf p o used st).outcome = .exhausted)
    (hl : st.left < 2) : WP isa (fail 3) u (GenDone p o final) := by
  have hrem : (rOf p o used st).remaining = 0 := by simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_last (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho (by omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p o used st).used, tr ++ primeEntry (rOf p o used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact hm.frame.fail_done (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- A prime accepted having read nothing: the key search is exhausted. -/
theorem classify_none (hm : Mid p o final used st u) {c : Nat}
    (ho : (rOf p o used st).outcome = .accepted c) (h0 : (rOf p o used st).used = 0) :
    WP isa (fail 3) u (GenDone p o final) := by
  have hrem : (rOf p o used st).remaining = 0 := by simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_accepted_none (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho
    (by show ¬(List.drop (rOf p o used st).used _).length < _; rw [h0, List.drop_zero]; omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p o used st).used, tr ++ primeEntry (rOf p o used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact hm.frame.fail_done (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- `p` accepted: `q` next. -/
theorem classify_p (hm : Mid p o final used st u) {c : Nat}
    (ho : (rOf p o used st).outcome = .accepted c) (hpos : 0 < (rOf p o used st).used) (hph : st.phase = .p) :
    WP isa (.block (nextPrime 1)) u (StepPost p o final used st) := by
  have hL := hm.frame.L_le
  have hle := hm.used_le
  have hrest : (rOf p o used st).used ≤ ((genRand o).drop used).length := by
    rw [List.length_drop, hm.frame.genRand_length]; omega
  have hks := ks_accepted_p (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho
    (drop_lt hpos hrest) hph
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs4
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add, slot_addL, hs5, hm.high, ← List.replicate_append_replicate]
  obtain ⟨tr, hfin⟩ := hm.final
  refine WP.mono (hm.frame.cont_of (.q (Spec.Rsa.i2osp c p.L))
    (st' := ⟨st.left, .q (Spec.Rsa.i2osp c p.L), limitOf p.L p.eB⟩) rfl rfl rfl hm.low hhigh5
    (fun pB h => by cases h; exact hs4)) fun t ⟨hlive, h24, _⟩ => .inl ⟨.inr ⟨c, ho, by omega, .inl hph⟩,
      ⟨st.left, .q (Spec.Rsa.i2osp c p.L),
      limitOf p.L p.eB⟩, primeEntry (rOf p o used st), ⟨hlive, tr ++ primeEntry (rOf p o used st), ?_⟩,
      measure_lt p hpos hle (Nat.le_refl _), ?_, rfl, ?_, .inr (.inl ⟨c, ho, hph, rfl, rfl, rfl⟩)⟩
  · rw [hfin, tailOf, hks, tailOf, List.drop_drop, consume_consume]
  · obtain ⟨req, hw, hr⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
    rw [h24, hw, this]
  · rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## An exhausted prime's search (ARMv7)

`exhaustedGen`: the generations left, a `u64` read as its halves, at most 1
(the end) or not; then one generation fewer (`decLeft`), the low half less
one and the high half less its borrow, and the next generation.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf ks_exhausted_next primeEntry consume_consume)

theorem dec_lo {n : Nat} (hn : 1 ≤ n) : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 ((n - 1) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show (2 ^ 32 - 1 % 2 ^ 32 + n % 2 ^ 32) % 2 ^ 32 = (n - 1) % 2 ^ 32 % 2 ^ 32
  omega

theorem dec_hi {n : Nat} (hn : 1 ≤ n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 32 (n / 2 ^ 32) + BitVec.ofNat 32 (decide (1 ≤ (BitVec.ofNat 32 n).toNat)).toNat - 1#32 =
      BitVec.ofNat 32 ((n - 1) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have hlo : (BitVec.ofNat 32 n).toNat = n % 2 ^ 32 := BitVec.toNat_ofNat _ _
  rw [hlo]
  by_cases h0 : n % 2 ^ 32 = 0
  · rw [decide_eq_false (by omega)]
    simp only [Bool.toNat_false, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [decide_eq_true (by omega)]
    simp only [Bool.toNat_true, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem left_flag {n : Nat} (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 32 (decide ((2 : BitVec 32).toNat ≤ (BitVec.ofNat 32 n).toNat)).toNat |||
      BitVec.ofNat 32 (n / 2 ^ 32)) - 0 == 0) = decide (n < 2) := by
  have z : ∀ x : BitVec 32, x - 0 = x := fun x => BitVec.sub_zero x
  rw [z, show (2 : BitVec 32).toNat = 2 from rfl, BitVec.toNat_ofNat]
  by_cases h2 : n < 2
  · rw [decide_eq_false (by omega), decide_eq_true h2, Nat.div_eq_of_lt (by omega)]; rfl
  · rw [decide_eq_false h2]
    apply Bool.eq_false_iff.mpr
    intro he
    have he' := (beq_iff_eq).mp he
    rw [or_zero32] at he'
    obtain ⟨h1, h3⟩ := he'
    by_cases h4 : 2 ≤ n % 2 ^ 32
    · rw [decide_eq_true h4] at h1; exact absurd h1 (by decide)
    · have : n / 2 ^ 32 ≠ 0 := by omega
      have h5 := congrArg BitVec.toNat h3
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h5
      exact this h5

namespace GenFrame

variable {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress}

theorem left_lo (h : GenFrame p o used st s) : s.mem.readW (off p.st 40) 32 = BitVec.ofNat 32 st.left :=
  low_half h.state.left

theorem left_hi (h : GenFrame p o used st s) :
    s.mem.readW (off p.st 44) 32 = BitVec.ofNat 32 (st.left / 2 ^ 32) := by
  rw [← off_add4]; exact high_half h.state.left h.state.left_lt

/-- One generation fewer. -/
theorem decLeft_ok (h : GenFrame p o used st s) (hl : 1 ≤ st.left) :
    WP isa (.block decLeft) s fun t =>
      t.mem = (s.mem.writeW (off p.st 40) (BitVec.ofNat 32 ((st.left - 1) % 2 ^ 32))).writeW (off p.st 44)
        (BitVec.ofNat 32 ((st.left - 1) / 2 ^ 32)) ∧ Rest [.r0, .r1, .r2] s t := by
  refine withRest_all [.r0, .r1, .r2] ?_ (by rfl) (by rfl)
  have hw := h.wr
  have aT (d : Nat) (hd : d < 56) : State.addr (p.stp + BitVec.ofNat 32 d) = off p.st d :=
    VG.Arm.addr_add (by have := h.facts.nT; omega)
  have hrd (d : Nat) (hd : d + 4 ≤ 56) : InRegions (s.rd ++ s.wr) (off p.st d) 4 := h.state_rd hw hd
  have carry (P : Prop) [Decidable P] :
      ((0 : BitVec 32) + 0 + if decide P = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide P).toNat :=
    carry32 P
  unfold decLeft
  ffrun [h.r9, aT 40 (by decide), aT 44 (by decide), hrd 40 (by decide), hrd 44 (by decide), h.left_lo, h.left_hi,
    h.state_wr hw (u := s) (d := 40) (by decide), h.state_wr hw (u := s) (d := 44) (by decide),
    show (1 : BitVec 32) = 1#32 from rfl, carry, dec_lo hl, dec_hi hl h.state.left_lt,
    show ∀ (t : State) a b, (subFlags t a b).wr = t.wr from fun _ _ _ => rfl]
  refine congrArg (fun v => (s.mem.writeW (off p.st 40) (BitVec.ofNat 32 ((st.left - 1) % 2 ^ 32))).writeW
    (off p.st 44) v) ?_
  rw [← dec_hi hl h.state.left_lt]
  exact congrArg (fun c => BitVec.ofNat 32 (st.left / 2 ^ 32) + c - 1#32) (carry32 _)

theorem gen_flag (h : GenFrame p o used st s) :
    WP isa (.block [.ldr .r0 .r9 40, .ldr .r1 .r9 44, .cmp .r0 (.imm 2), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0),
      .dp .orr .r0 .r0 (.reg .r1), .cmp .r0 (.imm 0)]) s fun t =>
      (isa.eval .eq t = some (decide (st.left < 2)) ∧ t.mem = s.mem) ∧ Rest [.r0, .r1] s t := by
  refine withRest_all [.r0, .r1] ?_ (by rfl) (by rfl)
  have hw := h.wr
  have aT (d : Nat) (hd : d < 56) : State.addr (p.stp + BitVec.ofNat 32 d) = off p.st d :=
    VG.Arm.addr_add (by have := h.facts.nT; omega)
  have hrd (d : Nat) (hd : d + 4 ≤ 56) : InRegions (s.rd ++ s.wr) (off p.st d) 4 := h.state_rd hw hd
  ffrun [h.r9, aT 40 (by decide), aT 44 (by decide), hrd 40 (by decide), hrd 44 (by decide), h.left_lo, h.left_hi,
    show ∀ (t : State) a b, (subFlags t a b).wr = t.wr from fun _ _ _ => rfl]
  exact congrArg some ((congrArg (fun c => (c ||| BitVec.ofNat 32 (st.left / 2 ^ 32)) - 0 == 0) (carry32 _)).trans
    (left_flag h.state.left_lt))

end GenFrame

section

variable {p : GenPublic} {o u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- The search was exhausted, and the generation not the last: the next one. -/
theorem classify_next (hm : Mid p o final used st u) (ho : (rOf p o used st).outcome = .exhausted)
    (hl : ¬st.left < 2) : WP isa (.block (decLeft ++ nextPrime 0)) u (StepPost p o final used st) := by
  have h := hm.frame
  have hL := h.L_le
  refine WP.block_append (WP.mono (h.decLeft_ok (by simp only; omega)) fun v ⟨hvm, kv⟩ => ?_)
  have hf : Frame (stW p) u.mem v.mem := by
    rw [hvm]
    exact stW_write (stW_write (Frame.refl _ _) (.inr (by decide)) _) (.inr (by decide)) _
  have hv0 : v.mem.readW (off p.st 0) 64 = u.mem.readW (off p.st 0) 64 := by
    rw [hvm]; simp (disch := decide) only [st_sep]
  have hv32 : v.mem.readW (off p.st 32) 64 = u.mem.readW (off p.st 32) 64 := by
    rw [hvm]; simp (disch := decide) only [st_sep]
  have hv40 : v.mem.readW (off p.st 40) 64 = BitVec.ofNat 64 (st.left - 1) := by
    refine word_of_halves (by have := h.state.left_lt; simp only at this; omega) ?_ ?_
    · rw [hvm]; simp (disch := decide) only [st_self, st_sep]
    · rw [off_add4, hvm]; simp (disch := decide) only [st_self]
  have hst : StateOk p ⟨st.left - 1, st.phase, (rOf p o used st).remaining⟩ v.mem :=
    h.restate hf (by rw [hv0]; exact h.state.remaining) (by rw [hv32]; exact h.state.phase) hv40
      h.state.remaining_le (by have := h.state.left_lt; simp only at this ⊢; omega)
  have g := h.stepTo kv (by decide) hf h.stW_changes h.stW_apart hst
  have hs5 := hm.slot5
  have hout : outBytes p.L (rOf p o used st) = List.replicate p.L 0 := by simp only [outBytes, ho]
  have hs5' : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L = List.replicate p.L 0 := by
    rw [hs5]; cases st.phase <;> simp only [hout]
  have hhigh5 : Spec.Rsa.bytesAt v.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show p.slot 5 = State.addr p.kp + BitVec.ofNat 64 (5 * p.L) from rfl, h.stW_key hf (by omega),
      show State.addr p.kp + BitVec.ofNat 64 (5 * p.L) = p.slot 5 from rfl,
      show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add, slot_addL, hs5', hm.high, ← List.replicate_append_replicate]
  have hlow : Spec.Rsa.bytesAt v.mem (State.addr p.kp) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [h.stW_key0 hf (by omega), hm.low]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_next (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho (by omega)
  refine WP.mono (g.cont_of .p (st' := ⟨st.left - 1, .p, limitOf p.L p.eB⟩) rfl rfl rfl hlow hhigh5
    (fun _ h => by cases h)) fun t ⟨hlive, h24, _⟩ => .inl ⟨.inl ⟨ho, hl⟩, ⟨st.left - 1, .p, limitOf p.L p.eB⟩,
      primeEntry (rOf p o used st), ⟨hlive, tr ++ primeEntry (rOf p o used st), ?_⟩,
      measure_le p (by simp only; omega), ?_, rfl, ?_, .inl ⟨ho, rfl, rfl, rfl⟩⟩
  · rw [hfin, tailOf, hks, tailOf, List.drop_drop, consume_consume]
  · obtain ⟨req, hw, hr⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
    rw [h24, GenFrame.stW_req hf, hw, this]
  · rw [tailOf, hks, tailOf, List.drop_drop]

theorem exhausted_ok (hm : Mid p o final used st u) (ho : (rOf p o used st).outcome = .exhausted) :
    WP isa exhaustedGen u (StepPost p o final used st) := by
  unfold exhaustedGen
  refine WP.seq (WP.mono hm.frame.gen_flag fun v ⟨⟨he, hvm⟩, kv⟩ => ?_)
  have hv := hm.keep kv hvm (by decide)
  refine WP.ite _ he (fun z => ?_) (fun z => ?_)
  · refine WP.mono (classify_last hv ho (of_decide_eq_true z)) fun t ht => .inr ⟨?_, ht⟩
    rintro (⟨-, h⟩ | ⟨c, h, -⟩)
    · exact h (of_decide_eq_true z)
    · rw [ho] at h; cases h
  · exact classify_next hv ho (of_decide_eq_false z)

end

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## A prime accepted (ARMv7)

`accepted`: after `p`, `q`'s search; after `q`, the key (`afterKey`), which
ends the key search with it or with its failed check, or, for a `d` too
small, starts both primes again. And `classify` as a whole.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf ks_accepted_key ks_accepted_small primeEntry consume_consume)

section

variable {p : GenPublic} {o u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem keyStatus_lt (r : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus r < 4 := by
  unfold keyStatus; split <;> decide

/-- After `q`: the key. -/
theorem classify_key (name : String) {kc : Prog isa} (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56))
    (hks : FrameStack.armStack kc ≤ 56) (hm : Mid p o final used st u) {c : Nat} {pB : List Byte}
    (ho : (rOf p o used st).outcome = .accepted c) (hpos : 0 < (rOf p o used st).used)
    (hph : st.phase = .q pB) :
    WP isa (.seq (keyRun (.call name kc)) afterKey) u (StepPost p o final used st) := by
  have hL := hm.frame.L_le
  obtain ⟨tr, hfin⟩ := hm.final
  have hle := hm.used_le
  have hrest : (rOf p o used st).used ≤ ((genRand o).drop used).length := by
    rw [List.length_drop, hm.frame.genRand_length]; omega
  have hg := drop_lt hpos hrest
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  have hrem : (rOf p o used st).remaining = 0 := by simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hr0
  refine WP.seq (WP.mono (hm.frame.key_run name hv hks) fun v hk => ?_)
  have hkey : keyOf p u.mem = keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L) := by
    simp only [keyOf, hs4, hs5]
  have hstat := hk.status
  have hout := hk.out
  rw [hkey] at hstat hout
  have hwv : v.mem.readW (off p.st 24) 64 = BitVec.ofNat 64 0 := by
    refine Eq.trans (hk.mem.readW (r := ⟨off p.st 24, 8⟩) (by
      have := Offset.contains_base (off p.st 24) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this) (hm.frame.state_apartK (by decide)) (by decide)) hw
  have h0 : v.gpr .r0 = BitVec.ofNat 32 (keyStatus (keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L))) := by
    rw [← hstat]; exact (ofNat_toNat32 _).symm
  have hlt := keyStatus_lt (keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L))
  have hfin' : ∀ {r : KeySearchResult}, keySearch p.L p.eB st ((genRand o).drop used) = r →
      final = r.consume used tr := fun h => by rw [hfin, tailOf, h]
  unfold afterKey
  refine WP.seq (WP.mono (Search.cmp_ok (c := 1) h0 (by omega) (by decide)) fun w ⟨⟨he1, hmem1⟩, k1⟩ => ?_)
  have hgw := hk.frame.keep k1 hmem1
  have w0 : w.gpr .r0 = _ := (k1.gpr .r0 (by decide)).trans h0
  cases hkf : keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) with
  | inl res =>
    cases res with
    | ok key =>
      have hks' := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .ok key) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hout
      refine WP.ite true he1 (fun _ => ?_) (fun h => by cases h)
      refine WP.mono (hgw.finish_done (final := final) (by decide) (by rw [hks']; rfl) (by rw [hks']; rfl)
        (by rw [hks']; rfl) hrem ?_ ⟨0, by rw [hmem1]; exact hwv, by rw [hks']; rfl⟩) fun _ h => .inr ⟨?_, h⟩
      rw [hmem1, key_outs, hout, hks']
      · simp only [keySearchBytes, Spec.Entropy.Result.consume, keyBytes, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
      · rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
        · rw [ho] at h; cases h
        · rw [hph] at h'; cases h'
        · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
    | error fl =>
      have hks' := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .error fl) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 w0
      refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
      refine WP.seq (WP.mono (Search.cmp_ok (c := 2) w0 (by decide) (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
      have hgw2 := hgw.keep k2 hmem2
      refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
      refine WP.mono (hgw2.fail_done (final := final) (by decide) (by rw [hks']; rfl) (by rw [hks']; rfl)
        (by rw [hks']; rfl) hrem (by rw [hks']; rfl)
        ⟨0, by rw [hmem2, hmem1]; exact hwv, by rw [hks']; rfl⟩) fun _ h => .inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
      · rw [ho] at h; cases h
      · rw [hph] at h'; cases h'
      · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
  | inr _ =>
    have hks' := ks_accepted_small (L := p.L) (eB := p.eB) ho hg hph hkf
    simp only [keyOp, hkf, keyStatus] at he1 w0 hout
    refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (Search.cmp_ok (c := 2) w0 (by decide) (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
    have hgw2 := hgw.keep k2 hmem2
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (hgw2.cont_of .p (st' := ⟨st.left, .p, limitOf p.L p.eB⟩) rfl rfl rfl
      (by rw [hmem2, hmem1]; exact low_of_outs hout) (by rw [hmem2, hmem1]; exact high_of_outs hout)
      (fun _ h => by cases h)) fun t ⟨hlive, h24, _⟩ => .inl ⟨.inr ⟨c, ho, by omega, .inr ⟨pB, hph, hkf⟩⟩,
        ⟨st.left, .p, limitOf p.L p.eB⟩,
        primeEntry (rOf p o used st) ++ [1, 2], ⟨hlive, tr ++ (primeEntry (rOf p o used st) ++ [1, 2]), ?_⟩,
        measure_lt p hpos hle (Nat.le_refl _), ?_, rfl, ?_, .inr (.inr ⟨c, pB, ho, hph, rfl, rfl, rfl⟩)⟩
    · rw [hfin, tailOf, hks', tailOf, List.drop_drop, consume_consume]
    · rw [h24, hmem2, hmem1]; exact hwv
    · rw [tailOf, hks', tailOf, List.drop_drop]

/-- A prime accepted, having read some octets: `q`'s search, or the key. -/
theorem accepted_ok (name : String) {kc : Prog isa}
    (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56)
    (hm : Mid p o final used st u) {c : Nat} (ho : (rOf p o used st).outcome = .accepted c)
    (hpos : 0 < (rOf p o used st).used) :
    WP isa (accepted (.call name kc)) u (StepPost p o final used st) := by
  have h := hm.frame
  have hw := h.wr
  have aT : State.addr (p.stp + BitVec.ofNat 32 32) = off p.st 32 := VG.Arm.addr_add (by have := h.facts.nT; omega)
  have hp1 := phaseWord_le st.phase
  unfold accepted
  refine WP.seq (WP.mono (withRest_all [.r12] (c := .block [.ldr .r12 .r9 32, .cmp .r12 (.imm 0)])
    (Q := fun t => isa.eval .eq t = some (decide (phaseWord st.phase = 0)) ∧ t.mem = u.mem) ?_ (by rfl) (by rfl))
    fun v ⟨⟨he, hvm⟩, kv⟩ => ?_)
  · ffrun [h.r9, aT, h.state_rd hw (u := u) (d := 32) (by decide), low_half h.state.phase]
    exact congrArg some (Search.sub_eq_beq (by omega) (by decide))
  have hv' := hm.keep kv hvm
  refine WP.ite _ he (fun z => ?_) (fun z => ?_)
  · have z := of_decide_eq_true z
    have hph : st.phase = .p := by cases hq : st.phase <;> simp_all [phaseWord]
    exact classify_p hv' ho hpos hph
  · have z := of_decide_eq_false z
    obtain ⟨pB, hph⟩ : ∃ pB, st.phase = .q pB := by
      cases hq : st.phase with
      | p => simp_all [phaseWord]
      | q pB => exact ⟨pB, rfl⟩
    exact classify_key name hv hks hv' ho hpos hph

end

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The controller's loop (ARMv7)

An iteration: the progress' prime's search, its outcome (`classify`), and the
status against 4. Each one that goes on lowers the measure, so the loop ends
with the key search's result.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

section

variable {p : GenPublic} {o s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem status_cases (r : PrimeSearchResult) :
    (r.status = 0 ∧ ∃ k a, r.outcome = .entropy k a) ∨ (r.status = 3 ∧ r.outcome = .exhausted) ∨
      (r.status = 1 ∧ ∃ c, r.outcome = .accepted c) := by
  rw [rOf_status]
  cases r.outcome with
  | entropy k a => exact .inl ⟨rfl, k, a, rfl⟩
  | exhausted => exact .inr (.inl ⟨rfl, rfl⟩)
  | accepted c => exact .inr (.inr ⟨rfl, c, rfl⟩)

/-- After the search: its outcome. -/
theorem classify_ok (name : String) {kc : Prog isa}
    (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56)
    (hi : GenIter p o final used st s) (ha : AfterSearch p o used st s t) :
    WP isa (Impl.RsaKeyGen.Arm.Generate.classify (.call name kc)) t (StepPost p o final used st) := by
  obtain ⟨hl, hfin⟩ := hi
  unfold Impl.RsaKeyGen.Arm.Generate.classify
  refine WP.seq (WP.mono (GenFrame.after_head hl hfin ha) fun u ⟨he, h0, h12, hm⟩ => ?_)
  have hs32 : (rOf p o used st).status < 2 ^ 32 := by
    unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
  have hu32 : (rOf p o used st).used < 2 ^ 32 := by
    have := hm.used_le; have := hm.frame.randLen_lt; omega
  refine WP.ite _ he (fun z => ?_) (fun z => ?_)
  · have z := of_decide_eq_true z
    rcases status_cases (rOf p o used st) with ⟨_, k, a, ho⟩ | ⟨h3, _⟩ | ⟨h1, _⟩
    · exact classify_entropy hm ho
    · omega
    · omega
  have z := of_decide_eq_false z
  refine WP.seq (WP.mono (Search.cmp_ok (c := 3) h0 hs32 (by decide)) fun v ⟨⟨he3, hvm⟩, kv⟩ => ?_)
  have hv' := hm.keep kv hvm
  refine WP.ite _ he3 (fun z3 => ?_) (fun z3 => ?_)
  · have z3 := of_decide_eq_true z3
    rcases status_cases (rOf p o used st) with ⟨h0', _⟩ | ⟨_, ho⟩ | ⟨h1, _⟩
    · omega
    · exact exhausted_ok hv' ho
    · omega
  have z3 := of_decide_eq_false z3
  obtain ⟨c, ho⟩ : ∃ c, (rOf p o used st).outcome = .accepted c := by
    rcases status_cases (rOf p o used st) with ⟨h0', _⟩ | ⟨h3, _⟩ | ⟨_, c, ho⟩
    · omega
    · omega
    · exact ⟨c, ho⟩
  refine WP.seq (WP.mono (Search.cmp0_ok ((kv.gpr .r12 (by decide)).trans h12) hu32) fun w ⟨⟨he0, hwm⟩, kw⟩ => ?_)
  have hw' := hv'.keep kw hwm
  refine WP.ite _ he0 (fun z0 => ?_) (fun z0 => ?_)
  · refine WP.mono (classify_none hw' ho (of_decide_eq_true z0)) fun _ h => .inr ⟨?_, h⟩
    rintro (⟨h', -⟩ | ⟨c', h', hne, -⟩)
    · rw [ho] at h'; cases h'
    · exact hne (of_decide_eq_true z0)
  · exact accepted_ok name hv hks hw' ho (Nat.pos_of_ne_zero (of_decide_eq_false z0))

/-- What an iteration leaves. -/
def IterPost (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  (isa.eval .eq t = some false ∧ GenDone p o final t) ∨
    (isa.eval .eq t = some true ∧ ∃ used' st', genMeasure p used' st' < genMeasure p used st ∧
      GenIter p o final used' st' t)

theorem keyStatus_lt' (r : KeySearchResult) : r.keyStatus < 4 := by
  unfold KeySearchResult.keyStatus; split <;> decide

theorem GenDone.keep {t' : State} (h : GenDone p o final t) {ws : List Reg} (k : Rest ws t t') (hm : t'.mem = t.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∉ ws := by decide) : GenDone p o final t' := by
  obtain ⟨g, h11, hk, req, hw, hr⟩ := h
  exact ⟨g.keep k hm (fun r hr' => hws r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)),
    (k.gpr .r11 (hws _ (by simp))).trans h11, hm ▸ hk, req, hm ▸ hw, hr⟩

theorem GenIter.keep {t' : State} (h : GenIter p o final used st t) {ws : List Reg} (k : Rest ws t t')
    (hm : t'.mem = t.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∉ ws := by decide) : GenIter p o final used st t' := by
  obtain ⟨⟨g, h11, hk⟩, hfin⟩ := h
  refine ⟨⟨g.keep k hm (fun r hr' => hws r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)),
    (k.gpr .r11 (hws _ (by simp))).trans h11, ?_, ?_, ?_⟩, hfin⟩
  · rw [hm]; exact hk.low
  · rw [hm]; exact hk.high
  · intro pB h; rw [hm]; exact hk.other pB h

/-- One iteration. -/
theorem iteration_ok (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56)
    (hi : GenIter p o final used st s) :
    WP isa (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) s
      (IterPost p o final used st) := by
  unfold iteration
  refine WP.seq (WP.mono (hi.1.toGenFrame.search_run sname c hi.1.key.other) fun t ha => ?_)
  refine WP.seq (WP.mono (classify_ok name hv hks hi ha) fun u hu => ?_)
  rcases hu with ⟨-, st', e, hit, hlt, -⟩ | ⟨-, hd⟩
  · refine WP.mono (Search.cmp_ok (c := 4) (n := 4) hit.1.r11 (by decide) (by decide)) fun v ⟨⟨he, hvm⟩, kv⟩ =>
      .inr ⟨he, _, st', hlt, hit.keep kv hvm⟩
  · have hlt := keyStatus_lt' final
    refine WP.mono (Search.cmp_ok (c := 4) hd.2.1 (by omega) (by decide)) fun v ⟨⟨he, hvm⟩, kv⟩ =>
      .inl ⟨by rw [he, decide_eq_false (by omega)], hd.keep kv hvm⟩

/-- The loop: the key search's result. -/
theorem gen_loop (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56)
    (hi : GenIter p o final used st s) :
    WP isa (.loop (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) .eq) s
      (GenDone p o final) := by
  refine WP.loop (fun m t => ∃ u st', m = genMeasure p u st' ∧ GenIter p o final u st' t)
    (fun m t ⟨u, st', hm, ht⟩ => WP.mono (iteration_ok sname c name hv hks ht) fun t' ht' => ?_) _ s
    ⟨used, st, rfl, hi⟩
  rcases ht' with ⟨he, hd⟩ | ⟨he, u', st'', hlt, hit⟩
  · exact .inl ⟨he, hd⟩
  · exact .inr ⟨he, _, by rw [hm]; exact hlt, u', st'', rfl, hit⟩

end

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The whole controller (ARMv7): its results stored, and the contract -/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf consume_zero)

section

variable {p : GenPublic} {o s : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- The octets consumed to `used`, and the status returned. -/
theorem results_ok (hd : GenDone p o final s) :
    WP isa (.block results) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 final.keyStatus ∧
        t.mem = (s.mem.writeW (State.addr p.up) (BitVec.ofNat 32 final.used)).writeW
          (off (State.addr p.up) 4) (0 : BitVec 32)) ∧ Rest [.r0] s t := by
  obtain ⟨h, h11, -, -⟩ := hd
  refine withRest_all [.r0] ?_ (by rfl) (by rfl)
  have aU : State.addr (p.up + BitVec.ofNat 32 4) = off (State.addr p.up) 4 :=
    VG.Arm.addr_add (by have := h.facts.nU; omega)
  have wU (d : Nat) (hd : d + 4 ≤ 8) : InRegions s.wr (off (State.addr p.up) d) 4 :=
    ⟨cU p, by rw [h.wr, h.input.wr, inWrites, h.eU]; simp, Offset.contains_base _ hd (by omega)⟩
  have w0 : InRegions s.wr (State.addr p.up) 4 := by
    have := wU 0 (by decide); simpa only [off, BitVec.add_zero] using this
  unfold results
  ffrun [h.r6, h.r8, h11, aU, wU 4 (by decide), w0, BitVec.add_zero, show (0 : BitVec 32) = 0#32 from rfl]

/-- The callee-saved registers but `r4`, from the frame. -/
theorem restore_ok (h : GenFrame p o used st s) :
    WP isa (.block restore) s fun t =>
      ((∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], t.gpr r = o.gpr r) ∧ t.mem = s.mem) ∧
        Rest [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s t := by
  have room := h.facts.room
  have top := h.facts.top
  have S1n := h.S1_toNat
  have hw : ⟨State.addr p.S1, 40⟩ ∈ s.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have a (d : Nat) (hd : d < 40) : State.addr (s.sp + BitVec.ofNat 32 d) = State.addr p.S1 + BitVec.ofNat 64 d := by
    rw [h.sp]; exact VG.Arm.addr_add (by omega)
  have r (d : Nat) (hd : d + 4 ≤ 40) : InRegions (s.rd ++ s.wr) (State.addr p.S1 + BitVec.ofNat 64 d) 4 :=
    ⟨_, List.mem_append_right _ hw, Offset.contains_base _ hd (by omega)⟩
  have v (q : Reg × Nat) (hq : q ∈ slots) : s.mem.readW (State.addr p.S1 + BitVec.ofNat 64 q.2) 32 = o.gpr q.1 :=
    h.saved q hq
  refine withRest_all [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] ?_ (by rfl) (by rfl)
  unfold restore
  ffrun [a 4 (by decide), a 8 (by decide), a 12 (by decide), a 16 (by decide), a 20 (by decide), a 24 (by decide),
    a 28 (by decide), a 36 (by decide), r 4 (by decide), r 8 (by decide), r 12 (by decide), r 16 (by decide),
    r 20 (by decide), r 24 (by decide), r 28 (by decide), r 36 (by decide),
    v (.r5, 4) (by simp), v (.r6, 8) (by simp), v (.r7, 12) (by simp), v (.r8, 16) (by simp), v (.r9, 20) (by simp),
    v (.r10, 24) (by simp), v (.r11, 28) (by simp), v (.lr, 36) (by simp)]
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

theorem phaseWord_eq (ph : KeyPhase) : phaseWord ph = if ph = .p then 0 else 1 := by
  cases ph <;> rfl

/-- The controller from its contract's precondition. -/
theorem gen_correct_ok (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Spec.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56)
    {s : State} (hpre : genPre s) :
    WP isa (code (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) s fun t =>
      genPost s t ∧ abiPreserved s t := by
  let p := genOfState s
  have hp : GenInput p s := ⟨hpre, rfl⟩
  have f := hp.facts
  have room : 256 ≤ s.sp.toNat := hpre.1
  unfold code body
  rw [show pushBytes = 4 * pushRegs.length from rfl]
  refine WP.frame (rs := pushRegs) (r := .r4) (by decide) (by simp; omega) (by decide) ?_
  refine WP.seq (WP.mono (entry_ok hp) fun s1 ⟨g1, h11, hm1⟩ => ?_)
  have hroom : 40 ≤ s.sp.toNat := by omega
  have cf := hp.cfacts
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, -, -, -⟩ := hst
  have hL : 32 ≤ p.L ∧ p.L ≤ 512 := by have hv := f.valid; unfold primeLenValid at hv; omega
  have hother : ∀ pB, (genProgress s).phase = .q pB → Spec.Rsa.bytesAt s1.mem (p.slot 4) p.L = pB := by
    intro pB hpB
    have e : pB = Spec.Rsa.bytesAt s.mem (p.slot 4) p.L := by
      simp only [genProgress, keyProgressAt] at hpB
      split at hpB
      · cases hpB
      · injection hpB with h; exact h.symm
    have hsub : Region.Sub (FrameStack.belowA s.sp 40) (cStack p) := by
      change Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 40), 40⟩ _
      rw [FrameStack.addr_sub' hroom]; exact Offset.sub_below _ (by decide) (by decide)
    rw [hm1, e]
    exact bytes_kept (FrameStack.pushed_frameA (rs := pushRegs) hroom) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (sK.sub_left hsub).symm.sub_left (Offset.sub_base _ (by omega))) (by omega)
  refine WP.seq (WP.mono (clearAround_ok g1 h11 hother) fun s2 ⟨hl, _⟩ => ?_)
  have hit : GenIter p s (genResult s) 0 (genProgress s) s2 :=
    ⟨hl, [], by rw [consume_zero]; rfl⟩
  refine WP.seq (WP.mono (gen_loop sname c name hv hks hit) fun s3 hd => ?_)
  unfold finish
  refine WP.block_append (WP.mono (results_ok hd) fun s4 ⟨⟨h0, hm4⟩, k4⟩ => ?_)
  obtain ⟨g3, h11, hkey, req, hreq, hreqs⟩ := hd
  have hU : Region.Sub ⟨off (State.addr p.up) 4, 4⟩ (cU p) := Offset.sub_base _ (by decide)
  have hf4 : Frame [cU p] s3.mem s4.mem := by
    rw [hm4]
    refine ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (show 4 + 32 / 8 ≤ 8 by decide) (by decide))
    have := Offset.contains_base (State.addr p.up) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    simpa only [BitVec.add_zero] using this
  have tU : ∀ r ∈ [cU p], Region.Disjoint (cT p) r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact cf.uT.symm
  have hst4 : StateOk p (genResult s).progress s4.mem := g3.state.frame hf4 tU
  have g4 : GenFrame p s (genResult s).used (genResult s).progress s4 :=
    g3.step k4 (by decide) hf4 (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inUsed s, by simp [changes, inWrites], by rw [g3.eU]; exact fun _ h => h⟩)
      (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (g3.push_apart (inUsed s) (by simp [inWrites])).sub_right (by rw [g3.eU]; exact fun _ h => h)) hst4
  refine WP.mono (restore_ok g4) fun s5 ⟨⟨hr5, hm5⟩, k5⟩ => ?_
  have sp5 : s5.sp = p.S1 := k5.sp.trans g4.sp
  have hu32 : (genResult s).used < 2 ^ 32 := by have := g3.used_le; have := g3.randLen_lt; omega

  have hst5 : StateOk p (genResult s).progress s5.mem := hm5 ▸ hst4
  have hw (d : Nat) (hd : d + 8 ≤ 56) : s5.mem.readW (off p.st d) 64 = s3.mem.readW (off p.st d) 64 := by
    rw [hm5]
    exact hf4.readW (r := ⟨off p.st d, 8⟩) (by
      have := Offset.contains_base (off p.st d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact cf.uT.symm.sub_left (Offset.sub_base _ hd)) (by decide)
  have g0 : (popped .r4 (4 * pushRegs.length) s5).gpr .r0 = BitVec.ofNat 32 (genResult s).keyStatus := by
    rw [popped_gpr (by decide), k5.gpr .r0 (by decide), h0]
  have g4r : (popped .r4 (4 * pushRegs.length) s5).gpr .r4 = s.gpr .r4 := by
    simp only [popped, RegUpd.gpr_setReg, ite_true]
    rw [sp5, hm5, ← BitVec.add_zero (State.addr p.S1)]
    exact g4.saved (.r4, 0) (by simp)
  have hlt := keyStatus_lt' (genResult s)
  refine ⟨⟨?_, ?_, ?_, ⟨req, ?_, ?_, hreqs⟩⟩, fun r hr' => ?_, ?_⟩
  · rw [BitVec.setWidth_append_eq_right, g0, toNat_small (by omega)]
  · change Spec.Rsa.bytesAt _ (State.addr p.kp) (9 * p.L) = keySearchBytes p.L (genResult s)
    rw [popped_mem, hm5, bytes_kept hf4 (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact cf.kU) (by have := f.nK; omega), hkey]
  · change Spec.Rsa.wordsAt _ (State.addr p.up) 1 = [BitVec.ofNat 64 (genResult s).used]
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      popped_mem, hm5, hm4, List.cons.injEq, and_true]
    refine word_of_halves (by omega) ?_ ?_
    · rw [Mem.readW_writeW_sep (Offset.sep_base _ (n := 32 / 8) (k := 32 / 8) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32, Nat.mod_eq_of_lt hu32]
    · rw [show State.addr p.up + BitVec.ofNat 64 4 = off (State.addr p.up) 4 from rfl, Mem.readW_writeW_self32,
        Nat.div_eq_of_lt hu32]; rfl
  · change Spec.Rsa.wordsAt _ p.st 6 = _
    have e0 := (hw 0 (by decide)).trans g3.state.remaining
    have e8 := (hw 8 (by decide)).trans g3.state.len
    have e16 := (hw 16 (by decide)).trans g3.state.cap
    have e24 := (hw 24 (by decide)).trans hreq
    have e32 := (hw 32 (by decide)).trans g3.state.phase
    have e40 := (hw 40 (by decide)).trans g3.state.left
    simp only [Spec.Rsa.wordsAt, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, List.map_cons, List.map_nil,
      Nat.reduceMul, popped_mem]
    simp only [off] at e0 e8 e16 e24 e32 e40
    rw [e0, e8, e16, e24, e32, e40, phaseWord_eq]
    rfl
  · change Spec.Rsa.bytesAt _ (off p.st 48) 8 = p.eB
    rw [popped_mem]
    exact hst5.e
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g4r
    all_goals rw [popped_gpr (by decide)]; exact hr5 _ (by simp)
  · change s5.sp + BitVec.ofNat 32 (4 * pushRegs.length) = s.sp
    rw [sp5, GenPublic.S1, show 4 * pushRegs.length = 40 from rfl, BitVec.sub_add_cancel]
    rfl

end VG.Proof.RsaKeyGen.Arm.Generate
