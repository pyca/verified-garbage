module

public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.ABI
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Generate
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.ByteDigits
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.ABI
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Generate
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
meta import VerifiedGarbage.Proof.Bignum.ByteDigits

/-! # The controller to the key's call (i686)

Its frame and loop states, entry and clearing, the prime search's arguments,
precondition and run, and the key's.
-/

@[expose] public section

/-! ## The controller's public data and its loop states (i686)

The controller's state is in the callee-saved registers (`esi`, `ebx`, `edi`,
`ebp`), which it saves in the frame it pushes, of 16 bytes below the stack
pointer; its memory moves only within what it may write (`changes`): the
key's buffer, `used`, the working space, the state and the stack below the
stack pointer.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86

/-- The arguments, the stack pointer and the state's public words. -/
structure GenPublic where
  kp : BitVec 32
  up : BitVec 32
  rp : BitVec 32
  B : BitVec 32
  stp : BitVec 32
  sp : BitVec 32
  L : Nat
  randLen : Nat
  words : Nat
  eB : List Byte
  /-- RSA's table, which the prime search reads. -/
  tab : BitVec 32

def genOfState (s : State) : GenPublic where
  kp := arg s 0
  up := arg s 2
  rp := arg s 3
  B := arg s 5
  stp := arg s 7
  sp := s.gpr .esp
  L := genLen s
  randLen := (arg s 4).toNat
  words := (arg s 6).toNat
  eB := genE s
  tab := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol

def GenInput (p : GenPublic) (s : State) : Prop := contract.pre s ∧ genOfState s = p

/-- The frame the controller pushes. -/
abbrev GenPublic.S1 (p : GenPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 16

/-- The registers the controller pushes, in order. -/
abbrev pushRegs : List Reg := [.ebx, .ebp, .esi, .edi]

/-- The regions the controller (and its callees) may write, and its stack. -/
def changes (s : State) : List Region := [kR s, uR s, bR s, sR s, below (s.gpr .esp) 284]

namespace GenInput

variable {p : GenPublic} {s : State}

theorem abi (h : GenInput p s) : GenABI s := genABI_of h.1

theorem sp_eq (h : GenInput p s) : p.sp = s.gpr .esp := by rw [← h.2]; rfl
theorem L_eq (h : GenInput p s) : p.L = genLen s := by rw [← h.2]; rfl
theorem kp_eq (h : GenInput p s) : p.kp = arg s 0 := by rw [← h.2]; rfl
theorem up_eq (h : GenInput p s) : p.up = arg s 2 := by rw [← h.2]; rfl
theorem rp_eq (h : GenInput p s) : p.rp = arg s 3 := by rw [← h.2]; rfl
theorem B_eq (h : GenInput p s) : p.B = arg s 5 := by rw [← h.2]; rfl
theorem stp_eq (h : GenInput p s) : p.stp = arg s 7 := by rw [← h.2]; rfl
theorem randLen_eq (h : GenInput p s) : p.randLen = (arg s 4).toNat := by rw [← h.2]; rfl
theorem words_eq (h : GenInput p s) : p.words = (arg s 6).toNat := by rw [← h.2]; rfl
theorem eB_eq (h : GenInput p s) : p.eB = genE s := by rw [← h.2]; rfl

theorem len_valid (h : GenInput p s) : 32 ≤ p.L ∧ p.L ≤ 512 ∧ p.L % 8 = 0 := by
  have hv := h.abi.lenValid
  rw [← h.L_eq] at hv
  unfold Spec.RsaKeyGen.primeLenValid at hv
  omega

theorem low_eq (h : GenInput p s) : lowR s = below (s.gpr .esp) 284 := by
  change (⟨(s.gpr .esp).setWidth 64 - 284#64, 284⟩ : Region) = ⟨(s.gpr .esp - BitVec.ofNat 32 284).setWidth 64, 284⟩
  rw [Taint.sub_setWidth h.abi.stackLow]

/-- The regions the controller only reads, and the arguments. -/
theorem read_disjoint (h : GenInput p s) {r : Region} (hr : r = rR s ∨ r = aR s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  have A := h.abi
  have L := h.low_eq
  intro w hw
  simp only [changes, ← L, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hr with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl | rfl
  exacts [A.kr.symm, A.ur.symm, A.rb, A.rs, A.lowRand.symm, A.ka.symm, A.ua.symm, A.ba.symm, A.sa.symm,
    A.lowA.symm]

theorem bytes_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' (rR s).base (rR s).len = Spec.Rsa.bytesAt m (rR s).base (rR s).len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (h.read_disjoint (.inl rfl)) (by have := (arg s 4).isLt; change (arg s 4).toNat ≤ _; omega)
    (List.mem_range.mp hi)

/-- The arguments, through what the controller may write. -/
theorem arg_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') {i : Nat} (hi : i < 8) :
    m'.readW (argAddr s i) 32 = m.readW (argAddr s i) 32 := by
  have A := h.abi
  have hc : (aR s).Contains (argAddr s i) 4 := by
    have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
    have ai : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
    rw [ai, show aR s = ⟨argAddr s 0, 32⟩ from rfl, a0]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  exact hf.readW hc (h.read_disjoint (.inr rfl)) (by decide)

end GenInput

/-- The saved registers, in the frame at `S1`: `edi`, `esi`, `ebp` and
`ebx` from its base. -/
def Saved (m : Mem) (S1 : BitVec 32) (o : State) : Prop :=
  m.readW ((S1 + BitVec.ofNat 32 0).setWidth 64) 32 = o.gpr .edi ∧
    m.readW ((S1 + BitVec.ofNat 32 4).setWidth 64) 32 = o.gpr .esi ∧
    m.readW ((S1 + BitVec.ofNat 32 8).setWidth 64) 32 = o.gpr .ebp ∧
    m.readW ((S1 + BitVec.ofNat 32 12).setWidth 64) 32 = o.gpr .ebx

/-- The registers and memory every state inside the frame has: the frame,
and memory that moved only within what may be written. -/
structure GenBase (p : GenPublic) (o : State) (s : State) : Prop where
  input : GenInput p o
  rd : s.rd = o.rd
  wr : s.wr = below p.sp 16 :: o.wr
  syms : s.syms = o.syms
  sp : s.gpr .esp = p.S1
  saved : Saved s.mem p.S1 o
  frame : Frame (changes o) o.mem s.mem

end VG.Proof.RsaKeyGen.X86.Generate

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-- The state's 64-bit word at byte `d`. -/
abbrev word (m : Mem) (stp : BitVec 32) (d : Nat) : BitVec 64 := m.readW (stp.setWidth 64 + BitVec.ofNat 64 d) 64

/-- The phase's word in the state. -/
def phaseWord : KeyPhase → Nat
  | .p => 0
  | .q _ => 1

/-- The key's buffer's slot `j` (`p_len` octets each). -/
abbrev GenPublic.slot (p : GenPublic) (j : Nat) : Addr := p.kp.setWidth 64 + BitVec.ofNat 64 (j * p.L)

/-- The state's words for the progress `st`, and the exponent. -/
structure StateOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  remaining : word m p.stp 0 = BitVec.ofNat 64 st.remaining
  len : word m p.stp 8 = BitVec.ofNat 64 p.L
  cap : word m p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L)
  phase : word m p.stp 32 = BitVec.ofNat 64 (phaseWord st.phase)
  left : word m p.stp 40 = BitVec.ofNat 64 st.left
  e : Spec.Rsa.bytesAt m (p.stp.setWidth 64 + 48) 8 = p.eB
  remaining_le : st.remaining ≤ limitOf p.L p.eB
  left_lt : st.left < 2 ^ 64

/-- The key's buffer for the progress `st`: zeros but `p`'s slot, which holds
`p` for `q`'s search. -/
structure KeyOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  low : Spec.Rsa.bytesAt m (p.kp.setWidth 64) (4 * p.L) = List.replicate (4 * p.L) 0
  high : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0
  other : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB

/-- A state of the controller in its frame: `used` octets consumed (`esi`),
the counted candidates each prime's search starts with (`edi`), the progress
`st` in the state, and the tape as it was. -/
structure GenFrame (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop
    extends GenBase p original s where
  used_le : used ≤ p.randLen
  ebp : s.gpr .ebp = BitVec.ofNat 32 p.L
  esi : s.gpr .esi = BitVec.ofNat 32 used
  edi : s.gpr .edi = BitVec.ofNat 32 (limitOf p.L p.eB)
  random : Spec.Rsa.bytesAt s.mem (p.rp.setWidth 64) p.randLen = genRand original
  state : StateOk p st s.mem

/-- A state of the loop: the frame's, the search going on, and the key's
buffer for the progress. -/
structure GenLive (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop
    extends GenFrame p original used st s where
  ebx : s.gpr .ebx = 4
  key : KeyOk p st s.mem

/-- The key search from octet `used` of the tape, from the progress `st`. -/
abbrev tailOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : KeySearchResult :=
  keySearch p.L p.eB st ((genRand original).drop used)

/-- A loop state, whose key search from there finishes as `final`. -/
def GenIter (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (s : State) : Prop :=
  GenLive p original used st s ∧ ∃ tr, final = (tailOf p original used st).consume used tr

/-- A loop state that ended the key search with `final`: the frame for its
consumption and its state for the next call, its status in `ebx`, the key's
buffer, and its request in the state. -/
def GenDone (p : GenPublic) (original : State) (final : KeySearchResult) (s : State) : Prop :=
  GenFrame p original final.used final.progress s ∧ s.gpr .ebx = BitVec.ofNat 32 final.keyStatus ∧
    Spec.Rsa.bytesAt s.mem (p.kp.setWidth 64) (9 * p.L) = keySearchBytes p.L final ∧
    ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested

/-- What each step that goes on lowers: the octets left of the tape, then the
generations left. -/
def genMeasure (p : GenPublic) (used : Nat) (st : KeyProgress) : Nat := (p.randLen - used) * 2 ^ 64 + st.left

/-- The loop's invariant, at the measure `n`. -/
def GenInv (p : GenPublic) (original : State) (final : KeySearchResult) (n : Nat) (s : State) : Prop :=
  ∃ used st, n = genMeasure p used st ∧ GenIter p original final used st s

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The controller's push and entry (i686)

The push of the four callee-saved registers, which changes only the
controller's stack and saves them (`push_base`); the arguments, which every
state in the frame reads at the same addresses (`GenBase.arg_*`); and the
entry, which leaves `p_len`, nothing consumed and the counted candidates of a
prime's search (`entry_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-- A block's run, with what it keeps: the registers but `rs`, the
regions and the statics. -/
theorem WP.blockKeep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hw : writesOnly rs (.block is) = true) :
    WP isa (.block is) s fun t => Q t ∧ Keep rs s t ∧ t.syms = s.syms :=
  WP.mono_syms (WP.keep rs h hw) fun _ ⟨q, k⟩ sy => ⟨q, k, sy⟩

/-- The push changes only the controller's stack. -/
theorem push_frame {p : GenPublic} {o : State} (h : GenInput p o) :
    Frame (changes o) o.mem (pushed pushRegs o).mem := by
  have hroom : 284 ≤ (o.gpr .esp).toNat := h.abi.stackLow
  refine (pushed_frame (rs := pushRegs) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)).sub
    fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨below (o.gpr .esp) 284, by simp [changes], below_sub (by decide) hroom⟩

theorem push_saved {p : GenPublic} {o : State} (h : GenInput p o) :
    Saved (pushed pushRegs o).mem p.S1 o := by
  have hroom : 284 ≤ (o.gpr .esp).toNat := h.abi.stackLow
  have hn : 4 * pushRegs.length ≤ (o.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega
  have hS : p.S1 = (pushed pushRegs o).gpr .esp := by rw [GenPublic.S1, h.sp_eq, pushed_esp]; rfl
  have w (i : Nat) (hi : i < 4) := pushed_word (rs := pushRegs) (s := o) (by decide) hn hi
  rw [hS]
  exact ⟨w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide)⟩

namespace GenBase

variable {p : GenPublic} {o s : State}

/-- A state in the frame, through code that keeps `esp`, the regions, the
statics and the memory but in what the controller may write. -/
theorem keep (hb : GenBase p o s) {t : State} {rs : List Reg} (k : Keep rs s t) (hrs : .esp ∉ rs)
    (sy : t.syms = s.syms) (hs : Saved t.mem p.S1 o) (hf : Frame (changes o) s.mem t.mem) :
    GenBase p o t :=
  ⟨hb.input, k.2.1.trans hb.rd, k.2.2.trans hb.wr, sy.trans hb.syms, (k.gpr hrs).trans hb.sp, hs,
    hb.frame.trans hf⟩

/-- The same, for code that keeps memory. -/
theorem step (hb : GenBase p o s) {t : State} {rs : List Reg} (k : Keep rs s t) (hrs : .esp ∉ rs)
    (sy : t.syms = s.syms) (hm : t.mem = s.mem) : GenBase p o t :=
  hb.keep k hrs sy (by rw [hm]; exact hb.saved) (by rw [hm]; exact Frame.refl _ _)

/-- The address of argument `i`, at displacement `d = 20 + 4 i` from `esp`. -/
theorem arg_ea (hb : GenBase p o s) {i d : Nat} (hd : 20 + 4 * i = d) :
    (s.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = argAddr o i := by
  rw [hb.sp, GenPublic.S1, hb.input.sp_eq, ← hd]
  unfold argAddr
  congr 1
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem arg_in (hb : GenBase p o s) {i : Nat} (hi : i < 8) : InRegions (s.rd ++ s.wr) (argAddr o i) 4 := by
  have A := hb.input.abi
  have a0 : argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  refine ⟨aR o, ?_, ?_⟩
  · rw [hb.rd, hb.wr, A.wr]; simp
  · rw [ai, show aR o = ⟨argAddr o 0, 32⟩ from rfl, a0]
    exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arg_val (hb : GenBase p o s) {i : Nat} (hi : i < 8) : s.mem.readW (argAddr o i) 32 = arg o i :=
  (hb.input.arg_frame hb.frame hi).trans rfl

end GenBase

theorem push_base {p : GenPublic} {o : State} (h : GenInput p o) : GenBase p o (pushed pushRegs o) where
  input := h
  rd := pushed_rd _ _
  wr := by rw [pushed_wr, h.sp_eq]; rfl
  syms := pushRegs_syms _ _
  sp := by rw [pushed_esp, GenPublic.S1, h.sp_eq]; rfl
  saved := push_saved h
  frame := push_frame h

/-! ## Whether the exponent is 3 -/

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

theorem append_eq (hi lo : BitVec 32) (c : BitVec 64) (hc : c.toNat = 0x03000000 * 2 ^ 32) :
    hi ++ lo = c ↔ hi = 0x03000000 ∧ lo = 0 := by
  have e : (hi ++ lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  have := lo.isLt
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [e, hc] at h'
    exact ⟨BitVec.eq_of_toNat_eq (by rw [show (0x03000000 : BitVec 32).toNat = 0x03000000 from rfl]; omega),
      BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega)⟩
  · rintro ⟨rfl, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [e, hc]; rfl

theorem xor_or_zero (hi lo c : BitVec 32) : (hi ^^^ c ||| lo) = 0 ↔ hi = c ∧ lo = 0 := by
  rw [Proof.RsaKeyGen.X86.KeyInit.or_eq_zero32, show (0 : BitVec 32) = 0#32 from rfl, BitVec.xor_eq_zero_iff]

/-- The exponent is 3 exactly when the halves of its word are. -/
theorem three_iff (m : Mem) (a : Addr) :
    decide (((m.readW (a + BitVec.ofNat 64 4) 32 ^^^ 0x03000000) ||| m.readW a 32).toNat < 1) =
      decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a 8) = 3) := by
  rw [Proof.RsaKeyGen.X86.KeyInit.lt_one_iff]
  apply decide_eq_decide.mpr
  rw [xor_or_zero, ← word_eq_three, Proof.Ffdh.X86.KeyInit.readW64_split, append_eq _ _ _ rfl]

/-! ## The entry -/

/-- The progress the state holds on entry. -/
def genProgress (o : State) : KeyProgress :=
  keyProgressAt o.mem ((arg o 0).setWidth 64) ((arg o 7).setWidth 64) (genLen o)

theorem low_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) :
    m.readW a 32 = BitVec.ofNat 32 n := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

namespace GenInput

variable {p : GenPublic} {o : State}

/-- The state's bytes, through the push. -/
theorem state_pushed (h : GenInput p o) {d n : Nat} (hd : d + n ≤ 56) :
    Spec.Rsa.bytesAt (pushed pushRegs o).mem ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Rsa.bytesAt o.mem ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) n := by
  have A := h.abi
  have hf := pushed_frame (rs := pushRegs) (s := o) (by decide)
    (by simp only [List.length_cons, List.length_nil]; have := A.stackLow; simp only [stack] at this; omega)
  have hd' : (sR o).Disjoint (below (o.gpr .esp) 16) :=
    A.lowS.symm.sub_right (by rw [h.low_eq]; exact below_sub (by decide) A.stackLow)
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 d, n⟩) (fun q hq => ?_)
    (by show n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  obtain rfl := List.mem_singleton.mp hq
  exact hd'.sub_left (Offset.sub_base _ hd)

theorem word_pushed (h : GenInput p o) {d : Nat} (hd : d + 8 ≤ 56) :
    (pushed pushRegs o).mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) 64 =
      o.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) 64 := by
  have A := h.abi
  have hf := pushed_frame (rs := pushRegs) (s := o) (by decide)
    (by simp only [List.length_cons, List.length_nil]; have := A.stackLow; simp only [stack] at this; omega)
  have hd' : (sR o).Disjoint (below (o.gpr .esp) 16) :=
    A.lowS.symm.sub_right (by rw [h.low_eq]; exact below_sub (by decide) A.stackLow)
  refine hf.readW (r := sR o) (Offset.contains_base _ (by omega) (by omega)) (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  exact hd'

theorem half_pushed (h : GenInput p o) {d : Nat} (hd : d + 4 ≤ 56) :
    (pushed pushRegs o).mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) 32 =
      o.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) 32 := by
  have A := h.abi
  have hf := pushed_frame (rs := pushRegs) (s := o) (by decide)
    (by simp only [List.length_cons, List.length_nil]; have := A.stackLow; simp only [stack] at this; omega)
  have hd' : (sR o).Disjoint (below (o.gpr .esp) 16) :=
    A.lowS.symm.sub_right (by rw [h.low_eq]; exact below_sub (by decide) A.stackLow)
  refine hf.readW (r := sR o) (Offset.contains_base _ (by omega) (by omega)) (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  exact hd'

end GenInput

/-- The state's words for the progress on entry. -/
theorem stateOk_entry {p : GenPublic} {o : State} (h : GenInput p o) :
    StateOk p (genProgress o) (pushed pushRegs o).mem := by
  have A := h.abi
  have hw (d : Nat) (hd : d + 8 ≤ 56) := h.word_pushed hd
  have hstp := h.stp_eq
  have hLp := h.L_eq
  have heB := h.eB_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, BitVec.isLt _⟩ <;> try simp only [word]
  · rw [hstp, hw 0 (by decide), BitVec.add_zero]; exact (ofNat_toNat64 _).symm
  · rw [hstp, hw 8 (by decide), hLp, ofNat_toNat64]; rfl
  · rw [hstp, hw 16 (by decide), hLp]; exact A.budget
  · rw [hstp, hw 32 (by decide)]
    simp only [genProgress, keyProgressAt]
    have hph : (o.mem.readW ((arg o 7).setWidth 64 + 32) 64).toNat ≤ 1 := A.phase
    split
    · rename_i h0
      apply BitVec.eq_of_toNat_eq
      rw [show (o.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 64).toNat = 0 from h0]; rfl
    · rename_i h0
      apply BitVec.eq_of_toNat_eq
      have : (o.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 64).toNat = 1 := by
        have h0' : ¬(o.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
        have : (o.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 64).toNat ≤ 1 := hph
        omega
      rw [this]; rfl
  · rw [hstp, hw 40 (by decide)]; exact (ofNat_toNat64 _).symm
  · rw [hstp, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, h.state_pushed (by decide), heB]; rfl
  · rw [hLp, heB]; exact A.remaining

theorem param_eq (extra i : Nat) : param extra i = at_ .esp (4 + 4 * i + 4 * (pushWords + extra)) := rfl

/-- The state's slot at byte `d`, its pointer `stp`. -/
theorem st_ea {p : GenPublic} {o : State} (h : GenInput p o) {d : Nat} (hd : d < 56) :
    (arg o 7 + BitVec.ofNat 32 d).setWidth 64 = (arg o 7).setWidth 64 + BitVec.ofNat 64 d :=
  VG.Proof.MlKem.X86.ea_off (by have := h.abi.sBound; omega)

theorem GenBase.st_in {p : GenPublic} {o s : State} (hb : GenBase p o s) {d n : Nat} (hd : d + n ≤ 56) :
    InRegions (s.rd ++ s.wr) ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) n := by
  have A := hb.input.abi
  refine ⟨sR o, ?_, Offset.contains_base _ hd (by omega)⟩
  rw [hb.rd, hb.wr, A.wr]; simp

theorem GenBase.st_inW {p : GenPublic} {o s : State} (hb : GenBase p o s) {d n : Nat} (hd : d + n ≤ 56) :
    InRegions s.wr ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) n := by
  have A := hb.input.abi
  refine ⟨sR o, ?_, Offset.contains_base _ hd (by omega)⟩
  rw [hb.wr, A.wr]; simp

/-- The counted candidates of a prime's search, from the mask of `e = 3`. -/
theorem limit_val (L : Nat) (three : Bool) :
    (BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L) +
          (BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L)) +
        (BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L) +
          (BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L))) +
        (BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L) +
          (BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L))) &&&
        Proof.RsaKeyGen.X86.KeyInit.mk three) + BitVec.ofNat 32 (40 * L) =
      BitVec.ofNat 32 (if three then 64 * L else 40 * L) := by
  cases three
  · simp only [Proof.RsaKeyGen.X86.KeyInit.mk_false, BitVec.and_zero, BitVec.zero_add, Bool.false_eq_true,
      ↓reduceIte]
  · simp only [Proof.RsaKeyGen.X86.KeyInit.mk_true, Proof.RsaKeyGen.X86.KeyInit.and_ones, ↓reduceIte,
      ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

theorem entry_ok {p : GenPublic} {o : State} (h : GenInput p o) :
    WP isa (.block entry) (pushed pushRegs o) fun t =>
      GenFrame p o 0 (genProgress o) t ∧ t.gpr .ebx = 4 ∧ t.mem = (pushed pushRegs o).mem := by
  have hb := push_base h
  have A := h.abi
  have hv := h.len_valid
  have hst : p.stp = arg o 7 := h.stp_eq
  have r8 : (pushed pushRegs o).mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 8) 32 = BitVec.ofNat 32 p.L := by
    apply low_half
    rw [h.word_pushed (by decide), h.L_eq]
    exact (ofNat_toNat64 _).symm
  have e52 : (arg o 7).setWidth 64 + BitVec.ofNat 64 52 = ((arg o 7).setWidth 64 + BitVec.ofNat 64 48) + BitVec.ofNat 64 4 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have three := three_iff (pushed pushRegs o).mem ((arg o 7).setWidth 64 + BitVec.ofNat 64 48)
  rw [← e52, show Spec.Rsa.bytesAt (pushed pushRegs o).mem ((arg o 7).setWidth 64 + BitVec.ofNat 64 48) 8 = p.eB by
    rw [h.state_pushed (by decide), h.eB_eq]; rfl] at three
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx, .ebp, .esi, .edi, .ebx] (Q := fun t =>
      t.gpr .ebp = BitVec.ofNat 32 p.L ∧ t.gpr .esi = 0 ∧ t.gpr .ebx = 4 ∧
      t.gpr .edi = BitVec.ofNat 32 (if decide (Spec.Rsa.os2ip p.eB = 3) then 64 * p.L else 40 * p.L) ∧
      t.mem = (pushed pushRegs o).mem) ?_ (by rfl)) fun t ⟨⟨hbp, hsi, hbx, hdi, hm⟩, k, sy⟩ => ?_
  · simp only [entry, st, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 7) (d := 48) rfl, hb.arg_in (i := 7) (by decide),
      hb.arg_val (i := 7) (by decide), st_ea h (d := 8) (by decide), st_ea h (d := 48) (by decide),
      st_ea h (d := 52) (by decide), hb.st_in (d := 8) (n := 4) (by decide), hb.st_in (d := 48) (n := 4) (by decide),
      hb.st_in (d := 52) (n := 4) (by decide), r8, execMul, Proof.RsaKeyGen.X86.KeyInit.mk_def, three,
      show (40 : BitVec 32).toNat = 40 from rfl, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show p.L < 2 ^ 32 by omega)]
    exact limit_val p.L _
  · refine ⟨⟨hb.step k (by decide) sy hm, Nat.zero_le _, hbp, by rw [hsi]; rfl, ?_, ?_, ?_⟩, hbx, hm⟩
    · rw [hdi]; unfold limitOf primeLimit
      by_cases h3 : Spec.Rsa.os2ip p.eB = 3
      · simp only [h3, decide_true, ↓reduceIte]; congr 1; omega
      · simp only [h3, decide_false, ↓reduceIte, Bool.false_eq_true]; congr 1; omega
    · rw [hm, h.rp_eq, h.randLen_eq]
      have hf := pushed_frame (rs := pushRegs) (s := o) (by decide)
        (by simp only [List.length_cons, List.length_nil]; have := A.stackLow; simp only [stack] at this; omega)
      have hd' : (rR o).Disjoint (below (o.gpr .esp) 16) :=
        A.lowRand.symm.sub_right (by rw [h.low_eq]; exact below_sub (by decide) A.stackLow)
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      refine hf.bytes (R := rR o) (fun q hq => ?_) (by have := (arg o 4).isLt; show (arg o 4).toNat ≤ 2 ^ 64; omega)
        (List.mem_range.mp hi)
      obtain rfl := List.mem_singleton.mp hq
      exact hd'
    · rw [hm]; exact stateOk_entry h

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## Zeros in the key's buffer (i686)

`zeroLoop`: `ecx` zeros from `edx` (at least one), inside a region it may
write (`zeroLoop_ok`), as FFDH's search zeroes its output
(`Proof/Ffdh/X86/KeySearch/Zero.lean`), but in part of a region.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Proof.Ffdh.X86.KeySearch (ZInv byte_write wp_store8 Upd.keeps)
open VG.Impl.RsaKeyGen.X86.Generate

theorem zeroStep_in {s₀ t : State} {P : BitVec 32} {n k : Nat}
    (hW : ∀ i < n, InRegions s₀.wr (P.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hb : P.toNat + n ≤ 2 ^ 32) (hn : n < 2 ^ 32) (hk : k < n) (I : ZInv s₀ P n k t) :
    WP isa (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun u => ZInv s₀ P n (k + 1) u ∧ u.zf = some (decide (n - (k + 1) = 0)) := by
  have hp : t.ea (at_ .edx 0) = P.setWidth 64 + BitVec.ofNat 64 k := by
    show (t.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, I.edx]; exact addr_eq (by omega)
  have hw : InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 k) 1 := by
    rw [I.keeps.2.2]; exact hW k hk
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .edx] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [⟨P.setWidth 64, n⟩] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.edx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃, byte_write]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) hik)]
      exact I.zero i (by omega)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- `n ≥ 1` zeros from `P`, within what the state may write. -/
theorem zeroLoop_ok {t : State} {P : BitVec 32} {n : Nat} (h1 : 1 ≤ n)
    (hW : ∀ i < n, InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hb : P.toNat + n ≤ 2 ^ 32) (hn : n < 2 ^ 32)
    (hd : t.gpr .edx = P) (hc : t.gpr .ecx = BitVec.ofNat 32 n) (ha : t.gpr .eax = 0) :
    WP isa zeroLoop t fun u => Frame [⟨P.setWidth 64, n⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] t u := by
  have I₀ : ZInv t P n 0 t := ⟨by rw [hd, BitVec.add_zero], by rw [hc, Nat.sub_zero], ha,
    Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), Keeps.refl _ _⟩
  unfold zeroLoop
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = n - k ∧ k < n ∧ ZInv t P n k u)
    (fun j u hu => ?_) _ t ⟨0, rfl, by omega, I₀⟩
  obtain ⟨i, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_in hW hb hn hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : n - (i + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], J.frame, ?_, J.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro j h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero j (by omega)
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega,
      i + 1, rfl, by omega, J⟩

open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Spec.RsaKeyGen (KeyProgress)

/-- The state's words, through writes apart from the state. -/
theorem StateOk.frame {p : GenPublic} {st : KeyProgress} {m m' : Mem} {R : Region} (h : StateOk p st m)
    (hd : R.Disjoint ⟨p.stp.setWidth 64, 56⟩) (fr : Frame [R] m m') :
    StateOk p st m' := by
  have rd (d : Nat) (hd' : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d :=
    fr.readW (r := ⟨p.stp.setWidth 64, 56⟩) (Offset.contains_base _ hd' (by omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine ⟨(rd 0 (by decide)).trans h.remaining, (rd 8 (by decide)).trans h.len, (rd 16 (by decide)).trans h.cap,
    (rd 32 (by decide)).trans h.phase, (rd 40 (by decide)).trans h.left, ?_, h.remaining_le, h.left_lt⟩
  rw [← h.e]
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine fr.bytes (R := ⟨p.stp.setWidth 64 + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide)
    (List.mem_range.mp hi)
  obtain rfl := List.mem_singleton.mp hq
  exact hd.symm.sub_left (Offset.sub_base (d := 48) (n := 8) (k := 56) _ (by decide))

/-- A state in the frame, through writes inside the key's buffer. -/
theorem GenFrame.keyWrite {p : GenPublic} {o t u : State} {used : Nat} {st : KeyProgress}
    (hf : GenFrame p o used st t) (k : Keep [.eax, .ecx, .edx] t u) (sy : u.syms = t.syms) {R : Region}
    (hR : R.Sub (kR o)) (fr : Frame [R] t.mem u.mem) : GenFrame p o used st u := by
  have hi := hf.input
  have A := hi.abi
  have hsp := hi.sp_eq
  have room : 284 ≤ p.sp.toNat := by rw [hsp]; exact A.stackLow
  have bd : (below p.sp 16).Disjoint R := by
    have hs : Region.Sub (below p.sp 16) (lowR o) := by
      rw [hi.low_eq, ← hsp]; exact below_sub (by decide) room
    exact (A.lowK.sub_left hs).sub_right hR |>.symm.symm
  have sv : Saved u.mem p.S1 o := by
    have keepW (j : Nat) (hj : j < 4) : u.mem.readW ((p.S1 + BitVec.ofNat 32 (4 * j)).setWidth 64) 32 =
        t.mem.readW ((p.S1 + BitVec.ofNat 32 (4 * j)).setWidth 64) 32 := by
      have e : (p.S1 + BitVec.ofNat 32 (4 * j)).setWidth 64 = (p.sp - BitVec.ofNat 32 16).setWidth 64 +
          BitVec.ofNat 64 (4 * j) := VG.Proof.MlKem.X86.ea_off (by
        rw [VG.X86.sub_toNat (by omega)]; have := p.sp.isLt; omega)
      rw [e]
      exact fr.readW (r := below p.sp 16) (Offset.contains_base _ (by omega) (by omega))
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact bd) (by decide)
    obtain ⟨h0, h1, h2, h3⟩ := hf.saved
    exact ⟨(keepW 0 (by decide)).trans h0, (keepW 1 (by decide)).trans h1, (keepW 2 (by decide)).trans h2,
      (keepW 3 (by decide)).trans h3⟩
  have fc : Frame (changes o) t.mem u.mem := fr.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ⟨kR o, by simp [changes], hR⟩
  refine ⟨hf.toGenBase.keep k (by decide) sy sv fc, hf.used_le, (k.gpr (by decide)).trans hf.ebp,
    (k.gpr (by decide)).trans hf.esi, (k.gpr (by decide)).trans hf.edi, ?_, ?_⟩
  · rw [← hf.random, hi.rp_eq, hi.randLen_eq]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi' => fr.bytes (R := rR o) (fun q hq => ?_)
      (by have := (arg o 4).isLt; show (arg o 4).toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi')
    obtain rfl := List.mem_singleton.mp hq
    exact (A.kr.sub_left hR).symm
  · have hst : p.stp = arg o 7 := hi.stp_eq
    refine hf.state.frame ?_ fr
    rw [hst]; exact A.ks.sub_left hR

open VG.Proof.MlDsa.X86.Pack (WP.keep writesOnly)

theorem Keep.ofKeeps {rs : List Reg} {s t : State} (h : Keeps rs s t) : Keep rs s t := ⟨h.1, h.2.1, h.2.2⟩

theorem four_val (L : Nat) : BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L) =
    BitVec.ofNat 32 (4 * L) := by
  simp only [← BitVec.ofNat_add]; congr 1; omega

/-- A byte of the key's buffer is writable. -/
theorem GenBase.key_in {p : GenPublic} {o s : State} (hb : GenBase p o s) {i : Nat} (hi : i < (arg o 1).toNat) :
    InRegions s.wr ((arg o 0).setWidth 64 + BitVec.ofNat 64 i) 1 := by
  have A := hb.input.abi
  refine ⟨kR o, ?_, Offset.contains_base _ (by omega) (by omega)⟩
  rw [hb.wr, A.wr]; simp

/-- The first zeros: `4 p_len` octets from `key`. -/
theorem clearLow_ok {p : GenPublic} {o t : State} {st : KeyProgress} (hf : GenFrame p o 0 st t) :
    WP isa (.seq (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++ ([.mov .eax (.imm 0)] : List Instr)))
      zeroLoop) t fun u =>
      GenFrame p o 0 st u ∧ Frame [⟨(arg o 0).setWidth 64, 4 * p.L⟩] t.mem u.mem ∧
        Spec.Rsa.bytesAt u.mem ((arg o 0).setWidth 64) (4 * p.L) = List.replicate (4 * p.L) 0 ∧
        Keep [.eax, .ecx, .edx] t u := by
  have hi := hf.input
  have A := hi.abi
  have hv := hi.len_valid
  have hkl : (arg o 1).toNat = 9 * p.L := by rw [A.keyLen, ← hi.L_eq]
  refine WP.seq (WP.mono (WP.blockKeep [.eax, .ecx, .edx] (Q := fun v =>
      v.gpr .edx = arg o 0 ∧ v.gpr .ecx = BitVec.ofNat 32 (4 * p.L) ∧ v.gpr .eax = 0 ∧ v.mem = t.mem) ?_ (by rfl))
    fun v ⟨⟨hd, hc, ha, hm⟩, k, sy⟩ => ?_)
  · simp only [four, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
    xrun [State.ea, at_, hf.arg_ea (i := 0) (d := 20) rfl, hf.arg_in (i := 0) (by decide),
      hf.arg_val (i := 0) (by decide), hf.ebp, four_val]
  have hfv : GenFrame p o 0 st v := hf.keyWrite (k.mono (by simp)) sy (R := kR o)
    (fun x hx => hx) (by rw [hm]; exact Frame.refl _ _)
  refine WP.mono_syms (zeroLoop_ok (P := arg o 0) (n := 4 * p.L) (by omega)
    (fun i hi' => (hfv.key_in (by omega))) (by have := A.kBound; omega) (by omega) hd hc ha)
    fun u ⟨fr, hz, ku⟩ sy' => ?_
  have ku' : Keep [.eax, .ecx, .edx] v u := Keep.ofKeeps ku
  have sub : Region.Sub ⟨(arg o 0).setWidth 64, 4 * p.L⟩ (kR o) := fun x hx => by
    simp only [Region.Contains] at hx ⊢; omega
  exact ⟨hfv.keyWrite ku' sy' sub fr, by rw [← hm]; exact fr, hz, (k.trans ku').mono (by simp)⟩

/-- The second zeros: `4 p_len` octets from `key + 5 p_len`. -/
theorem clearHigh_ok {p : GenPublic} {o t : State} {st : KeyProgress} (hf : GenFrame p o 0 st t) :
    WP isa (.seq (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++ ([.alu .add .edx (.reg .ecx),
        .alu .add .edx (.reg .ebp), .mov .eax (.imm 0)] : List Instr))) zeroLoop) t fun u =>
      GenFrame p o 0 st u ∧ Frame [⟨p.slot 5, 4 * p.L⟩] t.mem u.mem ∧
        Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 ∧
        Keep [.eax, .ecx, .edx] t u := by
  have hi := hf.input
  have A := hi.abi
  have hv := hi.len_valid
  have hkl : (arg o 1).toNat = 9 * p.L := by rw [A.keyLen, ← hi.L_eq]
  have kb := A.kBound
  have e5 : (arg o 0 + BitVec.ofNat 32 (5 * p.L)).setWidth 64 = p.slot 5 := by
    rw [GenPublic.slot, hi.kp_eq]; exact VG.Proof.MlKem.X86.ea_off (by omega)
  refine WP.seq (WP.mono (WP.blockKeep [.eax, .ecx, .edx] (Q := fun v =>
      v.gpr .edx = arg o 0 + BitVec.ofNat 32 (5 * p.L) ∧ v.gpr .ecx = BitVec.ofNat 32 (4 * p.L) ∧
        v.gpr .eax = 0 ∧ v.mem = t.mem) ?_ (by rfl))
    fun v ⟨⟨hd, hc, ha, hm⟩, k, sy⟩ => ?_)
  · simp only [four, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
    xrun [State.ea, at_, hf.arg_ea (i := 0) (d := 20) rfl, hf.arg_in (i := 0) (by decide),
      hf.arg_val (i := 0) (by decide), hf.ebp, four_val]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * p.L + p.L = 5 * p.L by omega]
  have hfv : GenFrame p o 0 st v := hf.keyWrite (k.mono (by simp)) sy (R := kR o)
    (fun x hx => hx) (by rw [hm]; exact Frame.refl _ _)
  have P5 : (arg o 0 + BitVec.ofNat 32 (5 * p.L)).toNat = (arg o 0).toNat + 5 * p.L := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine WP.mono_syms (zeroLoop_ok (P := arg o 0 + BitVec.ofNat 32 (5 * p.L)) (n := 4 * p.L) (by omega)
    (fun i hi' => by
      rw [e5, GenPublic.slot, hi.kp_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hfv.key_in (by omega)) (by omega) (by omega) hd hc ha)
    fun u ⟨fr, hz, ku⟩ sy' => ?_
  rw [e5] at fr hz
  have ku' : Keep [.eax, .ecx, .edx] v u := Keep.ofKeeps ku
  have sub : Region.Sub ⟨p.slot 5, 4 * p.L⟩ (kR o) := by
    rw [GenPublic.slot, hi.kp_eq]
    exact Offset.sub_base _ (by omega)
  exact ⟨hfv.keyWrite ku' sy' sub fr, by rw [← hm]; exact fr, hz, (k.trans ku').mono (by simp)⟩

/-- The key's buffer but `p` cleared: the loop's first state. -/
theorem clearAround_ok {p : GenPublic} {o t : State} {st : KeyProgress} (hf : GenFrame p o 0 st t)
    (hbx : t.gpr .ebx = 4)
    (hother : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt t.mem (p.slot 4) p.L = pB) :
    WP isa clearAround t fun u => GenLive p o 0 st u ∧ Frame [kR o] t.mem u.mem := by
  have hi := hf.input
  have A := hi.abi
  have hv := hi.len_valid
  have hkl : (arg o 1).toNat = 9 * p.L := by rw [A.keyLen, ← hi.L_eq]
  have kb := A.kBound
  have hk0 : (arg o 0).setWidth 64 = p.kp.setWidth 64 := by rw [hi.kp_eq]
  unfold clearAround
  refine WP.seq (WP.mono (clearLow_ok hf) fun v ⟨fv, frv, zv, kv⟩ => ?_)
  refine WP.mono (clearHigh_ok fv) fun u ⟨fu, fru, zu, ku⟩ => ?_
  have disj (d n : Nat) (hdn : 4 * p.L ≤ d ∧ d + n ≤ 5 * p.L) :
      Region.Disjoint ⟨p.kp.setWidth 64 + BitVec.ofNat 64 d, n⟩ ⟨p.slot 5, 4 * p.L⟩ := by
    rw [GenPublic.slot]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have bytes_keep {m m' : Mem} {R : Region} (fr : Frame [R] m m') {a : Addr} {n : Nat}
      (hd : Region.Disjoint ⟨a, n⟩ R) (hn : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi' => fr.bytes (R := ⟨a, n⟩)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd) hn (List.mem_range.mp hi')
  refine ⟨⟨fu, (ku.gpr (by decide)).trans ((kv.gpr (by decide)).trans hbx), ⟨?_, zu, fun pB hp => ?_⟩⟩, ?_⟩
  · rw [bytes_keep fru (by
      have := Offset.disjoint (p.kp.setWidth 64) (d := 0) (n := 4 * p.L) (e := 5 * p.L) (k := 4 * p.L)
        (by omega) (by omega) (by omega)
      simpa [GenPublic.slot] using this) (by omega), ← hk0]
    exact zv
  · rw [bytes_keep fru (by simpa [GenPublic.slot] using disj (4 * p.L) p.L ⟨Nat.le_refl _, by omega⟩) (by omega)]
    rw [bytes_keep frv (R := ⟨(arg o 0).setWidth 64, 4 * p.L⟩) (by
      rw [hk0, GenPublic.slot]
      have := Offset.disjoint (p.kp.setWidth 64) (d := 4 * p.L) (n := p.L) (e := 0) (k := 4 * p.L)
        (by omega) (by omega) (by omega)
      simpa using this) (by omega)]
    exact hother pB hp
  · refine Frame.trans (m₂ := v.mem) (frv.sub fun r hr => ?_) (fru.sub fun r hr => ?_)
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨kR o, List.mem_singleton_self _, fun x hx => by simp only [Region.Contains] at hx ⊢; omega⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨kR o, List.mem_singleton_self _, by rw [GenPublic.slot, hi.kp_eq]; exact Offset.sub_base _ (by omega)⟩

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The controller's stack and its calls' frames of arguments (i686)

The controller's 284 bytes of stack, at offsets of `low o`: the saved
registers at 268; the search's frame of 48 bytes of arguments at 220, its
return address at 216 and its own 216 below; the key's frame of 72 at 196,
its return address at 192 and its own 68 below.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86

/-- The base of the stack the controller uses. -/
abbrev low (o : State) : Addr := (o.gpr .esp).setWidth 64 - 284#64

theorem low_toNat {o : State} (A : GenABI o) : (low o).toNat = (o.gpr .esp).toNat - 284 := by
  have : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have := (o.gpr .esp).isLt
  simp only [low, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A word at `d` above a stack pointer `k ≤ 284` bytes below the entry's. -/
theorem addr_sub {o : State} (A : GenABI o) {k d : Nat} (hk : k ≤ 284) (hd : d < k + 36) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (284 - k + d) := by
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := A.stackBound
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega

theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 284) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

/-- A frame of `n` bytes of a call's arguments, below the saved registers. -/
abbrev fR (o : State) (n : Nat) : Region := ⟨low o + BitVec.ofNat 64 (268 - n), n⟩

/-- The frame the controller pushes, at its offset. -/
theorem push_eq {p : GenPublic} {o : State} (h : GenInput p o) :
    below p.sp 16 = ⟨low o + BitVec.ofNat 64 268, 16⟩ := by
  have A := h.abi
  rw [h.sp_eq]
  have e := addr_sub A (k := 16) (d := 0) (by decide) (by decide)
  simp only [addr, BitVec.add_zero] at e
  change (⟨(o.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region) = _
  rw [e]

theorem saved_addr {p : GenPublic} {o : State} (h : GenInput p o) {i : Nat} (hi : i < 4) :
    (p.S1 + BitVec.ofNat 32 (4 * i)).setWidth 64 = low o + BitVec.ofNat 64 (268 + 4 * i) := by
  have A := h.abi
  rw [GenPublic.S1, h.sp_eq]
  exact addr_sub A (by decide) (by omega)

/-- A state in a call's frame of `n` bytes of arguments: `GenBase` but for
the stack pointer and the frame's region, with the registers but `eax`,
`ecx` and `edx` those of `s₀`, the state before the frame. -/
structure Fr (p : GenPublic) (o s₀ : State) (n : Nat) (s : State) : Prop where
  input : GenInput p o
  rd : s.rd = o.rd
  wr : s.wr = fR o n :: below p.sp 16 :: o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = p.S1 - BitVec.ofNat 32 n
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esp → s.gpr r = s₀.gpr r
  saved : Saved s.mem p.S1 o
  frame : Frame (changes o) o.mem s.mem

theorem GenBase.alloc {p : GenPublic} {o s : State} (h : GenBase p o s) {n : Nat} (hn : n ≤ 268) :
    Fr p o s n (allocFrame n s) := by
  have A := h.input.abi
  refine ⟨h.input, h.rd, ?_, h.syms, by rw [allocFrame_esp, h.sp],
    fun r _ _ _ hsp => allocFrame_gpr _ _ hsp, h.saved, h.frame⟩
  change ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ :: s.wr = _
  rw [h.wr, h.sp, GenPublic.S1, h.input.sp_eq, BitVec.sub_sub, ← BitVec.ofNat_add]
  have e := addr_sub A (k := 16 + n) (d := 0) (by omega) (by omega)
  simp only [addr, BitVec.add_zero] at e
  rw [e, show 284 - (16 + n) + 0 = 268 - n by omega]

/-- A store to word `j` of a call's frame of `n` bytes. -/
theorem Fr.slot_ea {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) (hn : n ≤ 268) {j : Nat}
    (hj : 4 * j + 4 ≤ n) :
    (s.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = low o + BitVec.ofNat 64 (268 - n + 4 * j) := by
  have A := h.input.abi
  rw [h.esp, GenPublic.S1, h.input.sp_eq, BitVec.sub_sub, ← BitVec.ofNat_add]
  have e := addr_sub A (k := 16 + n) (d := 4 * j) (by omega) (by omega)
  rw [show 284 - (16 + n) + 4 * j = 268 - n + 4 * j by omega] at e
  exact e

theorem Fr.slot_ea' {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) (hn : n ≤ 268) {j d e : Nat}
    (hd : 4 * j = d) (hj : 4 * j + 4 ≤ n) (he : 268 - n + d = e) :
    (s.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = low o + BitVec.ofNat 64 e := by
  subst hd he; exact h.slot_ea hn hj

theorem Fr.slot_in' {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) (hn : n ≤ 268) {j e : Nat}
    (hj : 4 * j + 4 ≤ n) (he : 268 - n + 4 * j = e) : InRegions s.wr (low o + BitVec.ofNat 64 e) 4 := by
  subst he
  exact ⟨fR o n, by rw [h.wr]; exact List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩

theorem Fr.slot_in {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) (hn : n ≤ 268) {j : Nat}
    (hj : 4 * j + 4 ≤ n) : InRegions s.wr (low o + BitVec.ofNat 64 (268 - n + 4 * j)) 4 :=
  ⟨fR o n, by rw [h.wr]; exact List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- The controller's argument `i`, from a call's frame of `w` words. -/
theorem Fr.arg_ea {p : GenPublic} {o s₀ s : State} {w : Nat} (h : Fr p o s₀ (4 * w) s) {i d : Nat}
    (hd : 4 + 4 * i + 4 * (4 + w) = d) :
    (s.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = argAddr o i := by
  rw [h.esp, GenPublic.S1, h.input.sp_eq, ← hd]
  unfold argAddr
  congr 1
  rw [show 4 + 4 * i + 4 * (4 + w) = (16 + 4 * w) + (4 + 4 * i) by omega, BitVec.ofNat_add (16 + 4 * w),
    ← BitVec.add_assoc, BitVec.sub_sub, ← BitVec.ofNat_add, BitVec.sub_add_cancel]

theorem Fr.arg_in {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) {i : Nat} (hi : i < 8) :
    InRegions (s.rd ++ s.wr) (argAddr o i) 4 := by
  have A := h.input.abi
  have a0 : argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  refine ⟨aR o, ?_, ?_⟩
  · rw [h.rd, h.wr, A.wr]; simp
  · rw [ai, show aR o = ⟨argAddr o 0, 32⟩ from rfl, a0]
    exact Offset.contains _ (by omega) (by omega) (by omega)

theorem Fr.arg_val {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) {i : Nat} (hi : i < 8) :
    s.mem.readW (argAddr o i) 32 = arg o i :=
  (h.input.arg_frame h.frame hi).trans rfl

theorem Fr.st_in {p : GenPublic} {o s₀ s : State} {n : Nat} (h : Fr p o s₀ n s) {d m : Nat} (hd : d + m ≤ 56) :
    InRegions (s.rd ++ s.wr) ((arg o 7).setWidth 64 + BitVec.ofNat 64 d) m := by
  have A := h.input.abi
  refine ⟨sR o, ?_, Offset.contains_base _ hd (by omega)⟩
  rw [h.rd, h.wr, A.wr]; simp

theorem argAddr_low {o : State} (A : GenABI o) {i : Nat} (hi : i < 8) :
    argAddr o i = low o + BitVec.ofNat 64 (288 + 4 * i) := by
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := A.stackBound
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega

/-- An argument's read, through a store below the entry's stack pointer. -/
theorem rd_arg {o : State} (A : GenABI o) (m : Mem) {e : Nat} (he : e + 4 ≤ 284) {i : Nat} (hi : i < 8)
    (v : BitVec 32) :
    (m.writeW (low o + BitVec.ofNat 64 e) v).readW (argAddr o i) 32 = m.readW (argAddr o i) 32 := by
  rw [argAddr_low A hi]
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- A 32-bit read at an offset of `B`, through a 32-bit write at another. -/
theorem rdN (m : Mem) (B : Addr) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (v : BitVec 32) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep B h (by omega) (by omega)) (by decide)

theorem rdS (m : Mem) (B : Addr) (d : Nat) (v : BitVec 32) :
    (m.writeW (B + BitVec.ofNat 64 d) v).readW (B + BitVec.ofNat 64 d) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The search's arguments (i686)

For the search of the progress' prime: `out` is `p`'s slot for `p`, `q`'s for
`q`; `p` is `p`'s slot, of `p_len` octets for `q` and none for `p`; `e` the
state's last word; the tape after the octets consumed. In the call's frame
of 48 bytes, at 220 above `low o` (`searchArgs_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (KeyProgress)

/-- `p_len` for `q`'s search, nothing for `p`'s: the phase's word `ph`. -/
def pLenOf (L ph : Nat) : Nat := if ph = 0 then 0 else L

/-- The search's argument `j`, `used` octets consumed, in the phase `ph`. -/
def searchArg (p : GenPublic) (used ph : Nat) : Nat → BitVec 32
  | 0 => p.kp + BitVec.ofNat 32 (4 * p.L) + BitVec.ofNat 32 (pLenOf p.L ph)
  | 1 => BitVec.ofNat 32 p.L
  | 2 => p.up
  | 3 => p.stp + 48
  | 4 => 8
  | 5 => p.kp + BitVec.ofNat 32 (4 * p.L)
  | 6 => BitVec.ofNat 32 (pLenOf p.L ph)
  | 7 => if used < p.randLen then p.rp + BitVec.ofNat 32 used else p.rp
  | 8 => BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used
  | 9 => p.B
  | 10 => BitVec.ofNat 32 p.words
  | _ => p.stp

/-- The search's arguments are in its frame. -/
def SArgs (p : GenPublic) (o : State) (used ph : Nat) (m : Mem) : Prop :=
  ∀ j < 12, m.readW (low o + BitVec.ofNat 64 (220 + 4 * j)) 32 = searchArg p used ph j

theorem mask_phase (L : Nat) (ph : Nat) (hph : ph ≤ 1) :
    (0 - BitVec.ofNat 32 ph) &&& BitVec.ofNat 32 L = BitVec.ofNat 32 (pLenOf L ph) := by
  unfold pLenOf
  rcases (show ph = 0 ∨ ph = 1 by omega) with rfl | rfl
  · simp
  · simp only [Nat.one_ne_zero, ↓reduceIte]
    rw [show (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 from rfl, BitVec.allOnes_and]

theorem four_add (k : BitVec 32) (L : Nat) :
    BitVec.ofNat 32 L + BitVec.ofNat 32 L + (BitVec.ofNat 32 L + BitVec.ofNat 32 L) + k =
      k + BitVec.ofNat 32 (4 * L) := by
  rw [Proof.RsaKeyGen.X86.Generate.four_val, BitVec.add_comm]

/-- The tape's pointer: after the octets consumed, or `rand` with none left. -/
theorem win_ptr (x y : BitVec 32) {used n : Nat} (hy : y.toNat = n) (hu : used ≤ n) :
    x + BitVec.ofNat 32 used -
        ((0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide ((y - BitVec.ofNat 32 used).toNat < BitVec.toNat (1 : BitVec 32))))) &&&
          BitVec.ofNat 32 used) =
      if used < n then x + BitVec.ofNat 32 used else x := by
  have hn := y.isLt
  have e : (y - BitVec.ofNat 32 used).toNat = n - used := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hy]; omega
  rw [e, show (1 : BitVec 32).toNat = 1 from rfl]
  by_cases h : used < n
  · have h1 : ¬ (n - used < 1) := by omega
    simp only [h1, h, decide_false, ↓reduceIte]
    rw [show 0#32 - (BitVec.ofBool false).setWidth 32 = 0#32 from by decide, BitVec.zero_and, BitVec.sub_zero]
  · have h1 : n - used < 1 := by omega
    simp only [h1, h, decide_true, ↓reduceIte]
    rw [show 0#32 - (BitVec.ofBool true).setWidth 32 = BitVec.allOnes 32 from by decide, BitVec.allOnes_and,
      BitVec.add_sub_cancel]

theorem fr_slot {o : State} {m m' : Mem} {n k : Nat} (h : Frame [fR o n] m m') (hk : k + 4 ≤ n ∧ n ≤ 268)
    (v : BitVec 32) : Frame [fR o n] m (m'.writeW (low o + BitVec.ofNat 64 (268 - n + k)) v) :=
  Frame.writeW h (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem searchArgs_ok {p : GenPublic} {o s₀ t : State} {used ph : Nat} (h : Fr p o s₀ 48 t)
    (hbp : t.gpr .ebp = BitVec.ofNat 32 p.L) (hsi : t.gpr .esi = BitVec.ofNat 32 used)
    (hph : t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 32 = BitVec.ofNat 32 ph) (hph1 : ph ≤ 1)
    (hu : used ≤ p.randLen) :
    WP isa (.block searchArgs) t fun u =>
      (SArgs p o used ph u.mem ∧ Frame [fR o 48] t.mem u.mem) ∧ Keep [.eax, .ecx, .edx] t u := by
  have hi := h.input
  refine WP.keep _ ?_ (by rfl)
  simp only [searchArgs, st, param_eq, pushWords, searchWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, h.slot_ea' (by decide) (j := 0) (d := 0) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 1) (d := 4) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 2) (d := 8) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 3) (d := 12) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 4) (d := 16) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 5) (d := 20) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 6) (d := 24) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 7) (d := 28) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 8) (d := 32) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 9) (d := 36) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 10) (d := 40) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 11) (d := 44) rfl (by decide) rfl, h.slot_in' (by decide) (j := 0) (by decide) rfl, h.slot_in' (by decide) (j := 1) (by decide) rfl, h.slot_in' (by decide) (j := 2) (by decide) rfl, h.slot_in' (by decide) (j := 3) (by decide) rfl, h.slot_in' (by decide) (j := 4) (by decide) rfl, h.slot_in' (by decide) (j := 5) (by decide) rfl, h.slot_in' (by decide) (j := 6) (by decide) rfl, h.slot_in' (by decide) (j := 7) (by decide) rfl, h.slot_in' (by decide) (j := 8) (by decide) rfl, h.slot_in' (by decide) (j := 9) (by decide) rfl, h.slot_in' (by decide) (j := 10) (by decide) rfl, h.slot_in' (by decide) (j := 11) (by decide) rfl, h.arg_ea (w := 12) (i := 0) (d := 68) rfl, h.arg_in (i := 0) (by decide), h.arg_val (i := 0) (by decide), h.arg_ea (w := 12) (i := 2) (d := 76) rfl, h.arg_in (i := 2) (by decide), h.arg_val (i := 2) (by decide), h.arg_ea (w := 12) (i := 3) (d := 80) rfl, h.arg_in (i := 3) (by decide), h.arg_val (i := 3) (by decide), h.arg_ea (w := 12) (i := 4) (d := 84) rfl, h.arg_in (i := 4) (by decide), h.arg_val (i := 4) (by decide), h.arg_ea (w := 12) (i := 5) (d := 88) rfl, h.arg_in (i := 5) (by decide), h.arg_val (i := 5) (by decide), h.arg_ea (w := 12) (i := 6) (d := 92) rfl, h.arg_in (i := 6) (by decide), h.arg_val (i := 6) (by decide), h.arg_ea (w := 12) (i := 7) (d := 96) rfl, h.arg_in (i := 7) (by decide), h.arg_val (i := 7) (by decide), st_ea hi (d := 32) (by decide),
    h.st_in (d := 32) (m := 4) (by decide), hph, hbp, hsi, mask_phase _ _ hph1, four_add]
  have A := hi.abi
  simp (disch := decide) only [rd_arg A, h.arg_val]
  rw [win_ptr (arg o 3) (arg o 4) hi.randLen_eq.symm hu]
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11
      by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, rdS, rdN, searchArg,
      hi.kp_eq, hi.up_eq, hi.rp_eq, hi.B_eq, hi.stp_eq, hi.randLen_eq, hi.words_eq, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · iterate 12 (refine fr_slot ?_ ?hk _; case hk => decide)
    exact Frame.refl _ _

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The search's precondition (i686)

With its twelve arguments in the frame (`SArgs`), `vg_rsa_prime_search`'s
contract holds on its entry, narrowed to `e`, `p`, the rest of the tape and
RSA's table, which it reads, and to `out`, `used`, the working space, the
state's first 32 bytes and its frame of arguments, which it writes
(`search_pre`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Spec.RsaKeyGen (KeyProgress)

/-- An implementation of `vg_rsa_prime_search`, as the controller calls it:
its name, its code, its proof and the stack it uses. -/
structure Srch where
  name : String
  code : Prog isa
  verified : Verified target code VG.Proof.RsaKeyGen.X86.Search.contract
  noSp : NoSp code
  stack : stackUse code ≤ 216

/-- The search, as the controller calls it. -/
abbrev Srch.call (c : Srch) : Prog isa := .call c.name c.code

section
variable (p : GenPublic) (used ph : Nat)

/-- The search's regions: `out`, `used`, `e`, `p`, the rest of the tape, the
working space and the state. -/
abbrev cO : Region := ⟨(searchArg p used ph 0).setWidth 64, (searchArg p used ph 1).toNat⟩
abbrev cU : Region := ⟨(searchArg p used ph 2).setWidth 64, 8⟩
abbrev cE : Region := ⟨(searchArg p used ph 3).setWidth 64, (searchArg p used ph 4).toNat⟩
abbrev cP : Region := ⟨(searchArg p used ph 5).setWidth 64, (searchArg p used ph 6).toNat⟩
abbrev cW : Region := ⟨(searchArg p used ph 7).setWidth 64, (searchArg p used ph 8).toNat⟩
abbrev cB : Region := ⟨(searchArg p used ph 9).setWidth 64, (searchArg p used ph 10).toNat * 8⟩
abbrev cS : Region := ⟨(searchArg p used ph 11).setWidth 64, 32⟩

end

/-- RSA's table. -/
abbrev tR (o : State) : Region := ⟨(o.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩

/-- What the search may read and write. -/
abbrev sRd (p : GenPublic) (used ph : Nat) (o : State) : List Region :=
  [cE p used ph, cP p used ph, cW p used ph, tR o]
abbrev sWr (p : GenPublic) (used ph : Nat) (o : State) : List Region :=
  [cO p used ph, cU p used ph, cB p used ph, cS p used ph, fR o 48]

theorem ce_arg {p : GenPublic} {o s₀ t : State} {used ph : Nat} (h : Fr p o s₀ 48 t)
    (ha : SArgs p o used ph t.mem) (rd wr : List Region) {j : Nat} (hj : j < 12) :
    arg (t.callEntry.withRegions rd wr) j = searchArg p used ph j := by
  have A := h.input.abi
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 (16 + 48) := by
    rw [h.esp, GenPublic.S1, h.input.sp_eq, BitVec.sub_sub, ← BitVec.ofNat_add]
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 64 := by
    rw [he]; exact VG.X86.sub_toNat (by omega)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    addr_sub A (by decide) (by omega), show 284 - (16 + 48) + 4 * j = 220 + 4 * j by omega]

theorem pLen_le (L ph : Nat) : pLenOf L ph ≤ L := by unfold pLenOf; split <;> omega

theorem pLen_cases (L ph : Nat) : pLenOf L ph = 0 ∨ pLenOf L ph = L := by unfold pLenOf; split <;> simp

theorem sa7_lt {p : GenPublic} {used ph : Nat} (h : used < p.randLen) :
    searchArg p used ph 7 = p.rp + BitVec.ofNat 32 used := by
  simp only [searchArg, h, ↓reduceIte]

theorem sa7_ge {p : GenPublic} {used ph : Nat} (h : p.randLen ≤ used) : searchArg p used ph 7 = p.rp := by
  simp only [searchArg, show ¬ used < p.randLen by omega, ↓reduceIte]

theorem tn_add (x : BitVec 32) {k : Nat} (h : x.toNat + k < 2 ^ 32) : (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_eq_of_lt h

theorem tn_add_le (x : BitVec 32) (k : Nat) : (x + BitVec.ofNat 32 k).toNat ≤ x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)

namespace GenInput

variable {p : GenPublic} {o : State}

theorem kBound' (h : GenInput p o) : p.kp.toNat + 9 * p.L ≤ 2 ^ 32 := by
  have A := h.abi
  have := A.kBound
  rw [A.keyLen, ← h.L_eq] at this; rw [h.kp_eq]; exact this

theorem rBound' (h : GenInput p o) : p.rp.toNat + p.randLen ≤ 2 ^ 32 := by
  rw [h.rp_eq, h.randLen_eq]; exact h.abi.rBound

theorem uBound' (h : GenInput p o) : p.up.toNat + 8 ≤ 2 ^ 32 := by
  rw [h.up_eq]; exact h.abi.uBound

theorem bBound' (h : GenInput p o) : p.B.toNat + p.words * 8 ≤ 2 ^ 32 := by
  rw [h.B_eq, h.words_eq]; exact h.abi.bBound

theorem sBound' (h : GenInput p o) : p.stp.toNat + 56 ≤ 2 ^ 32 := by
  rw [h.stp_eq]; exact h.abi.sBound

theorem kR_eq (h : GenInput p o) : kR o = ⟨p.kp.setWidth 64, 9 * p.L⟩ := by
  rw [h.kp_eq, h.L_eq, ← h.abi.keyLen]

theorem rR_eq (h : GenInput p o) : rR o = ⟨p.rp.setWidth 64, p.randLen⟩ := by
  rw [h.rp_eq, h.randLen_eq]

theorem sR_eq (h : GenInput p o) : sR o = ⟨p.stp.setWidth 64, 56⟩ := by
  rw [h.stp_eq]

theorem randLen_lt (h : GenInput p o) : p.randLen < 2 ^ 32 := by rw [h.randLen_eq]; exact (arg o 4).isLt

theorem words_lt (h : GenInput p o) : p.words < 2 ^ 32 := by rw [h.words_eq]; exact (arg o 6).isLt

end GenInput

section Facts

variable {p : GenPublic} {o : State} (h : GenInput p o) {used : Nat} (ph : Nat) (hu : used ≤ p.randLen)
include h

theorem sa1 : (searchArg p used ph 1).toNat = p.L := by
  have := h.len_valid
  show (BitVec.ofNat 32 p.L).toNat = p.L
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sa6 : (searchArg p used ph 6).toNat = pLenOf p.L ph := by
  have := h.len_valid
  have := pLen_le p.L ph
  show (BitVec.ofNat 32 (pLenOf p.L ph)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

include hu in
theorem sa8 : (searchArg p used ph 8).toNat = p.randLen - used := by
  have := h.randLen_lt
  show (BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used).toNat = _
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem sa10 : (searchArg p used ph 10).toNat = p.words := by
  have := h.words_lt
  show (BitVec.ofNat 32 p.words).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

theorem sb0 : (searchArg p used ph 0).setWidth 64 = p.kp.setWidth 64 + BitVec.ofNat 64 (4 * p.L + pLenOf p.L ph) := by
  have := h.kBound'
  have := h.len_valid
  have := pLen_le p.L ph
  show (p.kp + BitVec.ofNat 32 (4 * p.L) + BitVec.ofNat 32 (pLenOf p.L ph)).setWidth 64 = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact VG.Proof.MlKem.X86.ea_off (by omega)

theorem st0 : (searchArg p used ph 0).toNat = p.kp.toNat + (4 * p.L + pLenOf p.L ph) := by
  have := h.kBound'
  have := h.len_valid
  have := pLen_le p.L ph
  show (p.kp + BitVec.ofNat 32 (4 * p.L) + BitVec.ofNat 32 (pLenOf p.L ph)).toNat = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact tn_add _ (by omega)

theorem sb3 : (searchArg p used ph 3).setWidth 64 = p.stp.setWidth 64 + 48 := by
  have := h.sBound'
  exact VG.Proof.MlKem.X86.ea_off (x := p.stp) (d := 48) (by omega)

theorem st3 : (searchArg p used ph 3).toNat = p.stp.toNat + 48 := by
  have := h.sBound'
  exact tn_add p.stp (k := 48) (by omega)

theorem sb5 : (searchArg p used ph 5).setWidth 64 = p.kp.setWidth 64 + BitVec.ofNat 64 (4 * p.L) := by
  have := h.kBound'
  have := h.len_valid
  exact VG.Proof.MlKem.X86.ea_off (by omega)

theorem st5 : (searchArg p used ph 5).toNat = p.kp.toNat + 4 * p.L := by
  have := h.kBound'
  have := h.len_valid
  exact tn_add _ (by omega)

/-- The search's regions, within the controller's. -/
theorem subO : Region.Sub (cO p used ph) (kR o) := by
  have := h.len_valid
  have := pLen_le p.L ph
  simp only [cO]
  rw [sb0 h, sa1 h, h.kR_eq]
  exact Offset.sub_base _ (by omega)

theorem subP : Region.Sub (cP p used ph) (kR o) := by
  have := h.len_valid
  have := pLen_le p.L ph
  simp only [cP]
  rw [sb5 h, sa6 h, h.kR_eq]
  exact Offset.sub_base _ (by omega)

theorem subE : Region.Sub (cE p used ph) (sR o) := by
  simp only [cE]
  rw [sb3 h, h.sR_eq, show (searchArg p used ph 4).toNat = 8 from rfl]
  exact Offset.sub_base _ (d := 48) (n := 8) (by decide)

theorem subS : Region.Sub (cS p used ph) (sR o) := by
  rw [h.sR_eq]; exact Region.sub_prefix (by decide)

include hu in
theorem subW : Region.Sub (cW p used ph) (rR o) := by
  have hr := h.rBound'
  simp only [cW]
  rw [sa8 h ph hu, h.rR_eq]
  rcases Nat.lt_or_ge used p.randLen with hl | hl
  · rw [show (searchArg p used ph 7).setWidth 64 = p.rp.setWidth 64 + BitVec.ofNat 64 used by
      rw [sa7_lt hl]; exact VG.Proof.MlKem.X86.ea_off (by omega)]
    exact Offset.sub_base _ (by omega)
  · intro a ha
    simp only [Region.Contains] at ha
    omega

theorem eqU : cU p used ph = uR o := by
  show (⟨p.up.setWidth 64, 8⟩ : Region) = _
  rw [h.up_eq]

theorem eqB : cB p used ph = bR o := by
  simp only [cB]
  rw [sa10 h, show searchArg p used ph 9 = p.B from rfl, h.B_eq, h.words_eq]

theorem dOP : (cO p used ph).Disjoint (cP p used ph) := by
  have := h.len_valid
  have := pLen_le p.L ph
  simp only [cO, cP]
  rw [sb0 h, sb5 h, sa1 h, sa6 h]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem dSE : (cS p used ph).Disjoint (cE p used ph) := by
  simp only [cS, cE]
  rw [sb3 h, show searchArg p used ph 11 = p.stp from rfl, show (searchArg p used ph 4).toNat = 8 from rfl]
  exact Offset.base_disjoint _ (e := 48) (by decide) (by decide)

end Facts

/-- Constants held, through writes apart from them. -/
theorem held_frame {m m' : Mem} {f : String → BitVec 64} {cs : List (String × List (BitVec 64))}
    (h : Abi.constsHeld m f cs) {rs : List Region} (hf : Frame rs m m') (hb : ∀ c ∈ cs, 8 * c.2.length ≤ 2 ^ 64)
    (hd : ∀ t ∈ Abi.constRegions f cs, ∀ r ∈ rs, t.Disjoint r) : Abi.constsHeld m' f cs := by
  intro c hc i hi
  have := hb c hc
  rw [hf.readW (r := ⟨f c.1, 8 * c.2.length⟩) (Offset.contains_base _ (by omega) (by omega))
    (hd _ (List.mem_map_of_mem hc)) (by decide)]
  exact h c hc i hi

theorem dj {a b P Q : Region} (F : P.Disjoint Q) (ha : Region.Sub a P) (hb : Region.Sub b Q) : a.Disjoint b :=
  (F.sub_left ha).sub_right hb

theorem search_pre {p : GenPublic} {o s₀ t : State} {used ph : Nat} {st : KeyProgress} (h : Fr p o s₀ 48 t)
    (ha : SArgs p o used ph t.mem) (hst : StateOk p st t.mem) (hu : used ≤ p.randLen) :
    VG.Proof.RsaKeyGen.X86.Search.contract.pre (t.callEntry.withRegions (sRd p used ph o) (sWr p used ph o)) := by
  have hi := h.input
  have A := hi.abi
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hl := low_toNat A
  have hv := hi.len_valid
  -- The stack.
  have hE : t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 68 := by
    rw [h.esp, GenPublic.S1, hi.sp_eq, BitVec.sub_sub, BitVec.sub_sub]; rfl
  have hn68 : (o.gpr .esp - BitVec.ofNat 32 68).toNat = (o.gpr .esp).toNat - 68 := VG.X86.sub_toNat (by omega)
  have hret : (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 216 := by
    rw [hE]
    have e := addr_sub A (k := 68) (d := 0) (by decide) (by decide)
    simpa only [addr, BitVec.add_zero] using e
  have ha0 : argAddr (t.callEntry.withRegions (sRd p used ph o) (sWr p used ph o)) 0 =
      low o + BitVec.ofNat 64 220 := by
    rw [argAddr_withRegions, argAddr_callEntry, h.slot_ea (by decide) (j := 0) (by decide)]
  have hsl : VG.Proof.RsaKeyGen.X86.Search.stack ≤ (t.gpr .esp - 4).toNat := by
    rw [hE, hn68]; show 216 ≤ _; omega
  have hsb : (t.gpr .esp - 4).toNat + 4 + 48 ≤ 2 ^ 32 := by rw [hE, hn68]; omega
  -- The regions.
  have sU : Region.Sub (cU p used ph) (uR o) := by rw [eqU hi ph]; exact fun _ h => h
  have sB : Region.Sub (cB p used ph) (bR o) := by rw [eqB hi ph]; exact fun _ h => h
  have sA : Region.Sub ⟨low o + BitVec.ofNat 64 220, 48⟩ (lowR o) := low_sub (by decide)
  have sT : Region.Sub ⟨low o + BitVec.ofNat 64 216, 4⟩ (lowR o) := low_sub (by decide)
  have sL : Region.Sub ⟨low o, 216⟩ (lowR o) := Region.sub_prefix (by decide)
  have dOU : Region.Disjoint (cO p used ph) (cU p used ph) := dj A.ku (subO hi ph) sU
  have dOE : Region.Disjoint (cO p used ph) (cE p used ph) := dj A.ks (subO hi ph) (subE hi ph)
  have dOP : Region.Disjoint (cO p used ph) (cP p used ph) := dOP hi ph
  have dOW : Region.Disjoint (cO p used ph) (cW p used ph) := dj A.kr (subO hi ph) (subW hi ph hu)
  have dOB : Region.Disjoint (cO p used ph) (cB p used ph) := dj A.kb (subO hi ph) sB
  have dOS : Region.Disjoint (cO p used ph) (cS p used ph) := dj A.ks (subO hi ph) (subS hi ph)
  have dOA : Region.Disjoint (cO p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowK.symm (subO hi ph) sA
  have dUE : Region.Disjoint (cU p used ph) (cE p used ph) := dj A.us sU (subE hi ph)
  have dUP : Region.Disjoint (cU p used ph) (cP p used ph) := dj A.ku.symm sU (subP hi ph)
  have dUW : Region.Disjoint (cU p used ph) (cW p used ph) := dj A.ur sU (subW hi ph hu)
  have dUB : Region.Disjoint (cU p used ph) (cB p used ph) := dj A.ub sU sB
  have dUS : Region.Disjoint (cU p used ph) (cS p used ph) := dj A.us sU (subS hi ph)
  have dUA : Region.Disjoint (cU p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowU.symm sU sA
  have dEP : Region.Disjoint (cE p used ph) (cP p used ph) := dj A.ks.symm (subE hi ph) (subP hi ph)
  have dEW : Region.Disjoint (cE p used ph) (cW p used ph) := dj A.rs.symm (subE hi ph) (subW hi ph hu)
  have dEB : Region.Disjoint (cE p used ph) (cB p used ph) := dj A.bs.symm (subE hi ph) sB
  have dES : Region.Disjoint (cE p used ph) (cS p used ph) := (dSE hi ph).symm
  have dEA : Region.Disjoint (cE p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowS.symm (subE hi ph) sA
  have dPW : Region.Disjoint (cP p used ph) (cW p used ph) := dj A.kr (subP hi ph) (subW hi ph hu)
  have dPB : Region.Disjoint (cP p used ph) (cB p used ph) := dj A.kb (subP hi ph) sB
  have dPS : Region.Disjoint (cP p used ph) (cS p used ph) := dj A.ks (subP hi ph) (subS hi ph)
  have dPA : Region.Disjoint (cP p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowK.symm (subP hi ph) sA
  have dWB : Region.Disjoint (cW p used ph) (cB p used ph) := dj A.rb (subW hi ph hu) sB
  have dWS : Region.Disjoint (cW p used ph) (cS p used ph) := dj A.rs (subW hi ph hu) (subS hi ph)
  have dWA : Region.Disjoint (cW p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowRand.symm (subW hi ph hu) sA
  have dBS : Region.Disjoint (cB p used ph) (cS p used ph) := dj A.bs sB (subS hi ph)
  have dBA : Region.Disjoint (cB p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowB.symm sB sA
  have dSA : Region.Disjoint (cS p used ph) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := dj A.lowS.symm (subS hi ph) sA
  have dTO : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cO p used ph) := dj A.lowK sT (subO hi ph)
  have dTU : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cU p used ph) := dj A.lowU sT sU
  have dTE : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cE p used ph) := dj A.lowS sT (subE hi ph)
  have dTP : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cP p used ph) := dj A.lowK sT (subP hi ph)
  have dTW : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cW p used ph) := dj A.lowRand sT (subW hi ph hu)
  have dTB : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cB p used ph) := dj A.lowB sT sB
  have dTS : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (cS p used ph) := dj A.lowS sT (subS hi ph)
  have dTA : Region.Disjoint (⟨low o + BitVec.ofNat 64 216, 4⟩ : Region) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have dLO : Region.Disjoint (⟨low o, 216⟩ : Region) (cO p used ph) := dj A.lowK sL (subO hi ph)
  have dLU : Region.Disjoint (⟨low o, 216⟩ : Region) (cU p used ph) := dj A.lowU sL sU
  have dLE : Region.Disjoint (⟨low o, 216⟩ : Region) (cE p used ph) := dj A.lowS sL (subE hi ph)
  have dLP : Region.Disjoint (⟨low o, 216⟩ : Region) (cP p used ph) := dj A.lowK sL (subP hi ph)
  have dLW : Region.Disjoint (⟨low o, 216⟩ : Region) (cW p used ph) := dj A.lowRand sL (subW hi ph hu)
  have dLB : Region.Disjoint (⟨low o, 216⟩ : Region) (cB p used ph) := dj A.lowB sL sB
  have dLS : Region.Disjoint (⟨low o, 216⟩ : Region) (cS p used ph) := dj A.lowS sL (subS hi ph)
  have dLA : Region.Disjoint (⟨low o, 216⟩ : Region) (⟨low o + BitVec.ofNat 64 220, 48⟩ : Region) := Offset.base_disjoint _ (by decide) (by decide)
  -- The table.
  have hT : Abi.constRegions (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] = [tR o] := by
    rw [h.syms, Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
  have tMem : tR o ∈ tableRegions o := by
    simp only [tableRegions, Abi.constRegions_cons, Abi.constRegions_nil,
      VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
    exact List.mem_singleton_self _
  have TF := A.tableFar (tR o) tMem
  have tAl : (tR o).base.toNat % 64 = 0 := A.tableAligned (tR o) tMem
  have tW : ∀ r ∈ o.wr, (tR o).Disjoint r := TF.2.1
  have tL : (tR o).Disjoint (lowR o) := TF.2.2.2
  have tK : (tR o).Disjoint (kR o) := tW _ (by rw [A.wr]; simp)
  have tO : (tR o).Disjoint (cO p used ph) := tK.sub_right (subO hi ph)
  have tU : (tR o).Disjoint (cU p used ph) := (tW _ (by rw [A.wr]; simp)).sub_right sU
  have tB : (tR o).Disjoint (cB p used ph) := (tW _ (by rw [A.wr]; simp)).sub_right sB
  have tS : (tR o).Disjoint (cS p used ph) := (tW _ (by rw [A.wr]; simp)).sub_right (subS hi ph)
  have tA : (tR o).Disjoint (fR o 48) := tL.sub_right sA
  have tT : (tR o).Disjoint ⟨low o + BitVec.ofNat 64 216, 4⟩ := tL.sub_right sT
  have tLo : (tR o).Disjoint ⟨low o, 216⟩ := tL.sub_right sL
  have held : Abi.constsHeld (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0))
      (fun name => BitVec.setWidth 64 (t.syms name))
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] := by
    have H := A.held
    rw [h.syms]
    have hb : ∀ c ∈ [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)],
        8 * c.2.length ≤ 2 ^ 64 := by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc
      rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
    refine held_frame (held_frame H h.frame hb fun r hr => ?_) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) hb fun r hr => ?_
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr
      intro q hq
      simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact tK
      · exact tW _ (by rw [A.wr]; simp)
      · exact tW _ (by rw [A.wr]; simp)
      · exact tW _ (by rw [A.wr]; simp)
      · rw [← hi.low_eq]; exact tL
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length] at hr
      simp only [List.mem_singleton] at hr; subst hr
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact tT
  -- The bounds and the values.
  have pl := pLen_le p.L ph
  have g0 : (searchArg p used ph 0).toNat + (searchArg p used ph 1).toNat ≤ 2 ^ 32 := by
    rw [st0 hi, sa1 hi]; have := hi.kBound'; omega
  have g2 : (searchArg p used ph 2).toNat + 8 ≤ 2 ^ 32 := hi.uBound'
  have g3 : (searchArg p used ph 3).toNat + (searchArg p used ph 4).toNat ≤ 2 ^ 32 := by
    rw [st3 hi, show (searchArg p used ph 4).toNat = 8 from rfl]; have := hi.sBound'; omega
  have g5 : (searchArg p used ph 5).toNat + (searchArg p used ph 6).toNat ≤ 2 ^ 32 := by
    rw [st5 hi, sa6 hi]; have := hi.kBound'; omega
  have g7 : (searchArg p used ph 7).toNat + (searchArg p used ph 8).toNat ≤ 2 ^ 32 := by
    rw [sa8 hi ph hu]
    have := hi.rBound'
    rcases Nat.lt_or_ge used p.randLen with hl | hl
    · rw [sa7_lt hl]; have := tn_add_le p.rp used; omega
    · rw [sa7_ge hl]; omega
  have g9 : (searchArg p used ph 9).toNat + (searchArg p used ph 10).toNat * 8 ≤ 2 ^ 32 := by
    rw [sa10 hi]; exact hi.bBound'
  have g11 : (searchArg p used ph 11).toNat + 32 ≤ 2 ^ 32 := by
    show p.stp.toNat + 32 ≤ _; have := hi.sBound'; omega
  have gLen : Spec.RsaKeyGen.primeLenValid (searchArg p used ph 1).toNat := by
    rw [sa1 hi, hi.L_eq]; exact A.lenValid
  have gE1 : 1 ≤ (searchArg p used ph 4).toNat := (by decide : 1 ≤ 8)
  have gE8 : (searchArg p used ph 4).toNat ≤ 8 := Nat.le_refl 8
  have gP : (searchArg p used ph 6).toNat = 0 ∨ (searchArg p used ph 6).toNat = (searchArg p used ph 1).toNat := by
    rw [sa6 hi, sa1 hi]; exact pLen_cases _ _
  have gScr : Spec.Rsa.scratchWords (searchArg p used ph 1).toNat ≤ (searchArg p used ph 10).toNat := by
    rw [sa1 hi, sa10 hi]
    have := A.scratchLength
    rw [← hi.L_eq, ← hi.words_eq] at this
    unfold Spec.Rsa.scratchWords at *; omega
  have gRand : (searchArg p used ph 8).toNat ≤ Spec.RsaKeyGen.primeEntropy (searchArg p used ph 1).toNat := by
    rw [sa8 hi ph hu, sa1 hi]
    have := A.randLen
    rw [← hi.L_eq, ← hi.randLen_eq] at this
    omega
  -- The state, through the return address.
  have fe : Frame [⟨low o + BitVec.ofNat 64 216, 4⟩] t.mem (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have sTS : Region.Disjoint ⟨p.stp.setWidth 64, 56⟩ ⟨low o + BitVec.ofNat 64 216, 4⟩ := by
    rw [← hi.sR_eq]; exact (A.lowS.sub_left sT).symm
  have rdw (d : Nat) (hd : d + 8 ≤ 56) :
      (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)).readW (p.stp.setWidth 64 + BitVec.ofNat 64 d) 64 =
        word t.mem p.stp d :=
    fe.readW (Offset.contains_base _ hd (by omega)) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact sTS) (by decide)
  have rdw0 : (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)).readW (p.stp.setWidth 64) 64 =
      word t.mem p.stp 0 := by
    have := rdw 0 (by decide); simpa only [BitVec.add_zero] using this
  have bye : Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)) (p.stp.setWidth 64 + 48) 8 =
      p.eB := by
    rw [← hst.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi' => ?_
    have hsub : Region.Sub ⟨p.stp.setWidth 64 + 48, 8⟩ ⟨p.stp.setWidth 64, 56⟩ :=
      Offset.sub_base _ (d := 48) (n := 8) (by decide)
    exact fe.bytes (R := ⟨p.stp.setWidth 64 + 48, 8⟩)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sTS.sub_left hsub) (show 8 ≤ 2 ^ 64 by decide)
      (List.mem_range.mp hi')
  have hrem : st.remaining < 2 ^ 64 := by
    have := hst.remaining_le
    unfold Proof.RsaKeyGen.KeySearch.limitOf Spec.RsaKeyGen.primeLimit at this
    split at this <;> omega
  have gRem : ((t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)).readW
      ((searchArg p used ph 11).setWidth 64) 64).toNat ≤
      Spec.RsaKeyGen.primeLimit (8 * (searchArg p used ph 1).toNat)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0))
          ((searchArg p used ph 3).setWidth 64) (searchArg p used ph 4).toNat)) := by
    rw [show searchArg p used ph 11 = p.stp from rfl, sb3 hi, sa1 hi, show (searchArg p used ph 4).toNat = 8 from rfl,
      rdw0, bye, hst.remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem]
    exact hst.remaining_le
  have gW : (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)).readW
      ((searchArg p used ph 11).setWidth 64 + 8) 64 = BitVec.ofNat 64 (searchArg p used ph 1).toNat := by
    rw [show searchArg p used ph 11 = p.stp from rfl, sa1 hi, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      rdw 8 (by decide)]
    exact hst.len
  have gC : (t.mem.writeW (low o + BitVec.ofNat 64 216) (t.unknowns 0)).readW
      ((searchArg p used ph 11).setWidth 64 + 16) 64 =
        BitVec.ofNat 64 (Spec.RsaKeyGen.primeEntropy (searchArg p used ph 1).toNat) := by
    rw [show searchArg p used ph 11 = p.stp from rfl, sa1 hi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      rdw 16 (by decide)]
    exact hst.cap
  sig_pre [VG.Proof.RsaKeyGen.X86.Search.contract, Proof.RsaKeyGen.primeSearchContract,
    Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal, argBytes, Abi.withConsts,
    VG.Impl.RsaKeyGen.TrialTable32.consts, VG.Proof.RsaKeyGen.X86.Candidate.packed_length, stackBelow]
  simp only [ce_arg h ha _ _ (show 0 < 12 by decide), ce_arg h ha _ _ (show 1 < 12 by decide),
    ce_arg h ha _ _ (show 2 < 12 by decide), ce_arg h ha _ _ (show 3 < 12 by decide),
    ce_arg h ha _ _ (show 4 < 12 by decide), ce_arg h ha _ _ (show 5 < 12 by decide),
    ce_arg h ha _ _ (show 6 < 12 by decide), ce_arg h ha _ _ (show 7 < 12 by decide),
    ce_arg h ha _ _ (show 8 < 12 by decide), ce_arg h ha _ _ (show 9 < 12 by decide),
    ce_arg h ha _ _ (show 10 < 12 by decide), ce_arg h ha _ _ (show 11 < 12 by decide), ha0, hret,
    BitVec.add_sub_cancel]
  sig_and_intros
  all_goals first
    | exact True.intro
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | (rw [hT]; rfl)
    | rfl
    | (intro r hr; rw [hT] at hr; simp only [List.mem_singleton] at hr; subst hr
       exact ⟨TF.1, tO, tU, tB, tS, tA, tT, tLo⟩)
    | (intro r hr; rw [hT] at hr; simp only [List.mem_singleton] at hr; subst hr; exact tAl)

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The search's call (i686)

`vg_rsa_prime_search`, called in its frame of arguments for the progress'
prime from the octets consumed, leaves its status in `eax`, the prime (or
zeros) in the prime's slot, the octets it consumed at `used`, the state's
first four words, and the rest of the controller's state as it was
(`search_run`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Spec.RsaKeyGen (KeyProgress PrimeSearchResult primeEntropy)
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

/-- The prime's slot: `p`'s (4) in the phase 0, `q`'s (5) otherwise. -/
abbrev outOf (p : GenPublic) (ph : Nat) : Addr := p.kp.setWidth 64 + BitVec.ofNat 64 (4 * p.L + pLenOf p.L ph)

/-- What the search's run may change. -/
def searchChanges (p : GenPublic) (o : State) (ph : Nat) : List Region :=
  [⟨outOf p ph, p.L⟩, uR o, bR o, ⟨p.stp.setWidth 64, 32⟩, below (o.gpr .esp) 284]

/-- The search of the progress' prime, from `used`. -/
abbrev rOf (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) : PrimeSearchResult :=
  primeOf p.L p.eB st ((genRand o).drop used)

/-- What the search of the progress' prime at `used` leaves. -/
structure AfterSearch (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p o used ⟨st.left, st.phase, (rOf p o used st).remaining⟩ t
  ebx : t.gpr .ebx = 4
  status : (t.gpr .eax).toNat = (rOf p o used st).status
  usedw : word t.mem p.up 0 = BitVec.ofNat 64 (rOf p o used st).used
  out : Spec.Rsa.bytesAt t.mem (outOf p (phaseWord st.phase)) p.L =
    (match (rOf p o used st).outcome with
      | .accepted c => Spec.Rsa.i2osp c p.L
      | _ => List.replicate p.L 0)
  req : ∃ requested, word t.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (rOf p o used st).Requests (primeEntropy p.L) requested
  mem : Frame (searchChanges p o (phaseWord st.phase)) s.mem t.mem

theorem rd_eq {o : State} (A : GenABI o) : o.rd = [rR o, tR o] := by
  have hp := A.rdPrefix
  have hd := A.rdTable
  rw [← List.take_append_drop (o.rd.length - 1) o.rd, hp, hd]
  simp only [tableRegions, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
  rfl

/-- The saved registers, through writes apart from the push's frame. -/
theorem saved_frame {p : GenPublic} {o : State} (h : GenInput p o) {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨low o + BitVec.ofNat 64 268, 16⟩ r) {m m' : Mem} (hf : Frame rs m m')
    (hs : Saved m p.S1 o) : Saved m' p.S1 o := by
  have A := h.abi
  have hl := low_toNat A
  have h1 := A.stackLow
  have hb := A.stackBound
  have keep (k : Nat) (hk : k < 4) : m'.readW ((p.S1 + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 =
      m.readW ((p.S1 + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 := by
    rw [saved_addr h hk]
    exact hf.readW (Offset.contains _ (by omega) (by omega) (by omega)) hd (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := hs
  exact ⟨(keep 0 (by decide)).trans h0, (keep 1 (by decide)).trans h1, (keep 2 (by decide)).trans h2,
    (keep 3 (by decide)).trans h3⟩

/-- A frame of arguments' stores keep a state in the frame. -/
theorem Fr.stores {p : GenPublic} {o s₀ t u : State} {n : Nat} (h : Fr p o s₀ n t) (hn : n ≤ 268)
    (k : Keep [.eax, .ecx, .edx] t u) (sy : u.syms = t.syms) (hf : Frame [fR o n] t.mem u.mem) :
    Fr p o s₀ n u := by
  have hi := h.input
  have A := hi.abi
  refine ⟨hi, k.2.1.trans h.rd, k.2.2.trans h.wr, sy.trans h.syms, (k.gpr (by decide)).trans h.esp,
    fun r h1 h2 h3 h4 => (k.gpr (by simp [h1, h2, h3])).trans (h.keep r h1 h2 h3 h4),
    saved_frame hi (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) hf h.saved,
    h.frame.trans (hf.sub fun r hr => ?_)⟩
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨below (o.gpr .esp) 284, by simp [changes], by rw [← hi.low_eq]; exact low_sub (by omega)⟩

/-- The search's regions, among those of a state in its frame. -/
theorem search_covers {p : GenPublic} {o s₀ u : State} {used : Nat} (ph : Nat) (h : Fr p o s₀ 48 u)
    (hu : used ≤ p.randLen) :
    Covers (sRd p used ph o ++ sWr p used ph o) (u.rd ++ u.wr) ∧ Covers (sWr p used ph o) u.wr := by
  have hi := h.input
  have A := hi.abi
  have hv := hi.len_valid
  have pl := pLen_le p.L ph
  have hw : ∀ r ∈ sWr p used ph o, ∃ r' ∈ u.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := by
    intro r hr
    rw [h.wr, A.wr]
    simp only [sWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · refine ⟨kR o, by simp, 4 * p.L + pLenOf p.L ph, ?_, ?_⟩
      · show (searchArg p used ph 0).setWidth 64 = (arg o 0).setWidth 64 + _
        rw [sb0 hi, hi.kp_eq]
      · show _ + (searchArg p used ph 1).toNat ≤ (arg o 1).toNat
        rw [sa1 hi, A.keyLen, ← hi.L_eq]; omega
    · rw [eqU hi ph]; exact ⟨uR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · rw [eqB hi ph]; exact ⟨bR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · refine ⟨sR o, by simp, 0, ?_, by show 0 + 32 ≤ 56; decide⟩
      rw [BitVec.add_zero]; show p.stp.setWidth 64 = _; rw [hi.stp_eq]
    · exact ⟨fR o 48, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [sRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨sR o, List.mem_append_right _ (by rw [h.wr, A.wr]; simp), 48, ?_,
        (by decide : 48 + 8 ≤ 56)⟩
      show (searchArg p used ph 3).setWidth 64 = (arg o 7).setWidth 64 + _
      rw [sb3 hi, hi.stp_eq]; rfl
    · refine ⟨kR o, List.mem_append_right _ (by rw [h.wr, A.wr]; simp), 4 * p.L, ?_, ?_⟩
      · show (searchArg p used ph 5).setWidth 64 = (arg o 0).setWidth 64 + _
        rw [sb5 hi, hi.kp_eq]
      · show _ + (searchArg p used ph 6).toNat ≤ (arg o 1).toNat
        rw [sa6 hi, A.keyLen, ← hi.L_eq]; omega
    · have hr := hi.rBound'
      have e8 := sa8 hi ph hu
      rcases Nat.lt_or_ge used p.randLen with hl | hl
      · refine ⟨rR o, List.mem_append_left _ (by rw [h.rd, rd_eq A]; simp), used, ?_, ?_⟩
        · show (searchArg p used ph 7).setWidth 64 = (arg o 3).setWidth 64 + _
          rw [sa7_lt hl, ← hi.rp_eq]; exact VG.Proof.MlKem.X86.ea_off (by omega)
        · show _ + (searchArg p used ph 8).toNat ≤ (arg o 4).toNat
          rw [e8, ← hi.randLen_eq]; omega
      · refine ⟨rR o, List.mem_append_left _ (by rw [h.rd, rd_eq A]; simp), 0, ?_, ?_⟩
        · show (searchArg p used ph 7).setWidth 64 = (arg o 3).setWidth 64 + _
          rw [sa7_ge hl, ← hi.rp_eq, BitVec.add_zero]
        · show _ + (searchArg p used ph 8).toNat ≤ (arg o 4).toNat
          rw [e8, ← hi.randLen_eq]; omega
    · exact ⟨tR o, List.mem_append_left _ (by rw [h.rd, rd_eq A]; simp), 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', off, hb⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', off, hb⟩

theorem body_noSp (c : Srch) : NoSp (.seq (.block searchArgs) c.call) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · have h : (Code.block searchArgs : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true := by decide
    rw [Code.allInstrs_eq] at h
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi
  · exact c.noSp i hi

theorem bytesAt_drop (m : Mem) (P : Addr) (k n : Nat) :
    Spec.Rsa.bytesAt m (P + BitVec.ofNat 64 k) (n - k) = (Spec.Rsa.bytesAt m P n).drop k := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_drop,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Octets apart from what a run writes. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' R.base R.len = Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

/-- A 64-bit word apart from what a run writes. -/
theorem word_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {stp : BitVec 32} {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨stp.setWidth 64 + BitVec.ofNat 64 d, 8⟩ r) :
    word m' stp d = word m stp d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem ret_eq {p : GenPublic} {o s₀ u : State} (h : Fr p o s₀ 48 u) :
    (u.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 216 := by
  have A := h.input.abi
  have hE : u.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 68 := by
    rw [h.esp, GenPublic.S1, h.input.sp_eq, BitVec.sub_sub, BitVec.sub_sub]; rfl
  rw [hE]
  have e := addr_sub A (k := 68) (d := 0) (by decide) (by decide)
  simpa only [addr, BitVec.add_zero] using e

/-- The `n ≤ 220` bytes below the call's stack pointer. -/
theorem below_call {p : GenPublic} {o s₀ u : State} (h : Fr p o s₀ 48 u) {n : Nat} (hn : n ≤ 220) :
    below (u.gpr .esp) n = ⟨low o + BitVec.ofNat 64 (220 - n), n⟩ := by
  have A := h.input.abi
  rw [h.esp, GenPublic.S1, h.input.sp_eq]
  change (⟨(o.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 48 - BitVec.ofNat 32 n).setWidth 64, n⟩ : Region) = _
  rw [BitVec.sub_sub, BitVec.sub_sub, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  have e := addr_sub A (k := 16 + (48 + n)) (d := 0) (by omega) (by omega)
  simp only [addr, BitVec.add_zero] at e
  rw [e, show 284 - (16 + (48 + n)) + 0 = 220 - n by omega]

/-- The search's inputs, on its entry: `e`, the other prime, the counted
candidates left and the tape after the octets consumed. -/
theorem entry_result {p : GenPublic} {o s₀ u : State} {used : Nat} {st : KeyProgress} (F : Fr p o s₀ 48 u)
    (hu : used ≤ p.randLen) (hst : StateOk p st u.mem) (hk : KeyOk p st u.mem) (v : BitVec 32) :
    Spec.RsaKeyGen.primeSearch (searchArg p used (phaseWord st.phase) 1).toNat
      (Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v)
        (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 3)) (searchArg p used (phaseWord st.phase) 4).toNat)
      (Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v)
        (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 5)) (searchArg p used (phaseWord st.phase) 6).toNat)
      ((u.mem.writeW (low o + BitVec.ofNat 64 216) v).readW
        (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 11)) 64).toNat
      (Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v)
        (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 7)) (searchArg p used (phaseWord st.phase) 8).toNat) =
      rOf p o used st := by
  have hi := F.input
  have A := hi.abi
  have hv := hi.len_valid
  have sT : Region.Sub ⟨low o + BitVec.ofNat 64 216, 4⟩ (lowR o) := low_sub (by decide)
  have fe : Frame [⟨low o + BitVec.ofNat 64 216, 4⟩] u.mem (u.mem.writeW (low o + BitVec.ofNat 64 216) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have far {R : Region} (hR : (lowR o).Disjoint R) : ∀ r ∈ [(⟨low o + BitVec.ofNat 64 216, 4⟩ : Region)],
      R.Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact (hR.sub_left sT).symm
  have sS : (lowR o).Disjoint ⟨p.stp.setWidth 64, 56⟩ := by rw [← hi.sR_eq]; exact A.lowS
  have sK : (lowR o).Disjoint ⟨p.kp.setWidth 64, 9 * p.L⟩ := by rw [← hi.kR_eq]; exact A.lowK
  have sR' : (lowR o).Disjoint ⟨p.rp.setWidth 64, p.randLen⟩ := by rw [← hi.rR_eq]; exact A.lowRand
  -- `e`
  have hE : Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v)
      (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 3)) (searchArg p used (phaseWord st.phase) 4).toNat =
      p.eB := by
    rw [sb3 hi, show (searchArg p used (phaseWord st.phase) 4).toNat = 8 from rfl, ← hst.e]
    exact bytes_keep (R := ⟨p.stp.setWidth 64 + 48, 8⟩) fe
      (far (sS.sub_right (Offset.sub_base _ (d := 48) (n := 8) (by decide)))) (show 8 ≤ 2 ^ 64 by decide)
  -- the other prime
  have hP : Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v)
      (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 5)) (searchArg p used (phaseWord st.phase) 6).toNat =
      st.phase.other := by
    rw [sa6 hi, sb5 hi]
    rcases hph : st.phase with _ | pB
    · simp [phaseWord, pLenOf, Spec.Rsa.bytesAt, Spec.RsaKeyGen.KeyPhase.other]
    · simp only [phaseWord, pLenOf, Nat.one_ne_zero, ↓reduceIte, Spec.RsaKeyGen.KeyPhase.other]
      rw [← hk.other pB hph]
      exact bytes_keep (R := ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (4 * p.L), p.L⟩) fe
        (far (sK.sub_right (Offset.sub_base _ (by omega)))) (show p.L ≤ 2 ^ 64 by omega)
  -- the counted candidates left
  have hR : ((u.mem.writeW (low o + BitVec.ofNat 64 216) v).readW
      (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 11)) 64).toNat = st.remaining := by
    have hrem : st.remaining < 2 ^ 64 := by
      have := hst.remaining_le
      unfold Proof.RsaKeyGen.KeySearch.limitOf Spec.RsaKeyGen.primeLimit at this
      split at this <;> omega
    have := word_keep (stp := p.stp) (d := 0) fe (far (sS.sub_right (Offset.sub_base _ (by decide))))
    simp only [word, BitVec.add_zero] at this
    rw [show searchArg p used (phaseWord st.phase) 11 = p.stp from rfl, this]
    have h0 := hst.remaining
    simp only [word, BitVec.add_zero] at h0
    rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem]
  -- the tape
  have hW : Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v)
      (BitVec.setWidth 64 (searchArg p used (phaseWord st.phase) 7)) (searchArg p used (phaseWord st.phase) 8).toNat =
      (genRand o).drop used := by
    have hr := hi.rBound'
    have hall : Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 216) v) (p.rp.setWidth 64) p.randLen =
        genRand o := by
      rw [bytes_keep (R := ⟨p.rp.setWidth 64, p.randLen⟩) fe (far sR') (show p.randLen ≤ 2 ^ 64 by omega)]
      have := hi.bytes_frame F.frame
      rw [hi.rR_eq] at this
      exact this.trans (by rw [hi.rp_eq, hi.randLen_eq])
    rw [sa8 hi _ hu]
    rcases Nat.lt_or_ge used p.randLen with hl | hl
    · rw [sa7_lt hl, VG.Proof.MlKem.X86.ea_off (by omega), bytesAt_drop, hall]
    · have hlen : (genRand o).length = p.randLen := by
        rw [← hall]; simp [Spec.Rsa.bytesAt]
      rw [show p.randLen - used = 0 by omega, List.drop_eq_nil_of_le (by omega)]
      simp [Spec.Rsa.bytesAt]
  rw [sa1 hi, hE, hP, hR, hW]

/-- The key's buffer, through writes apart from it. -/
theorem KeyOk.frame {p : GenPublic} {st : KeyProgress} {m m' : Mem} {R : Region} (h : KeyOk p st m)
    (hL : p.kp.toNat + 9 * p.L ≤ 2 ^ 32) (hd : R.Disjoint ⟨p.kp.setWidth 64, 9 * p.L⟩) (fr : Frame [R] m m') :
    KeyOk p st m' := by
  have far {X : Region} (hX : Region.Sub X ⟨p.kp.setWidth 64, 9 * p.L⟩) : ∀ r ∈ [R], X.Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact (hd.sub_right hX).symm
  refine ⟨?_, ?_, fun pB hp => ?_⟩
  · rw [← h.low]
    exact bytes_keep (R := ⟨p.kp.setWidth 64, 4 * p.L⟩) fr (far (Region.sub_prefix (by omega)))
      (show 4 * p.L ≤ 2 ^ 64 by omega)
  · rw [← h.high]
    exact bytes_keep (R := ⟨p.slot 5, 4 * p.L⟩) fr (far (Offset.sub_base _ (by omega))) (show 4 * p.L ≤ 2 ^ 64 by omega)
  · rw [← h.other pB hp]
    exact bytes_keep (R := ⟨p.slot 4, p.L⟩) fr (far (Offset.sub_base _ (by omega))) (show p.L ≤ 2 ^ 64 by omega)

theorem search_run (c : Srch) {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p o used st s) : WP isa (searchRun c.call) s (AfterSearch p o used st s) := by
  have hb := h.toGenBase
  have hi := hb.input
  have A := hi.abi
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have hsn : (s.gpr .esp).toNat = (o.gpr .esp).toNat - 16 := by
    rw [hb.sp, GenPublic.S1, hi.sp_eq]; exact VG.X86.sub_toNat (by omega)
  have hph1 : phaseWord st.phase ≤ 1 := by unfold phaseWord; split <;> omega
  unfold searchRun
  rw [show 4 * searchWords = 48 from rfl]
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (body_noSp c) ?_
  have F0 := hb.alloc (n := 48) (by decide)
  have hph : (allocFrame 48 s).mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 32 =
      BitVec.ofNat 32 (phaseWord st.phase) := by
    show s.mem.readW _ 32 = _
    rw [← hi.stp_eq]; exact low_half h.state.phase
  refine WP.seq (WP.of_syms (WP.mono (searchArgs_ok F0 (by rw [allocFrame_gpr _ _ (by decide)]; exact h.ebp)
    (by rw [allocFrame_gpr _ _ (by decide)]; exact h.esi) hph hph1 h.used_le) fun u ⟨⟨ha, hfr⟩, k⟩ sy => ?_))
  have F := F0.stores (by decide) k sy hfr
  have hst : StateOk p st u.mem := h.state.frame (R := fR o 48)
    (by rw [← hi.sR_eq]; exact A.lowS.sub_left (low_sub (by decide))) hfr
  obtain ⟨cov, covW⟩ := search_covers (phaseWord st.phase) F h.used_le
  have hun : (u.gpr .esp).toNat = (o.gpr .esp).toNat - 64 := by
    rw [F.esp, GenPublic.S1, hi.sp_eq, BitVec.sub_sub, ← BitVec.ofNat_add]; exact VG.X86.sub_toNat (by omega)
  refine WP.of_syms (WP.call c.verified.1 c.noSp (by have := c.stack; omega)
    (search_pre F ha hst h.used_le) cov covW fun u' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ sy' => ?_)
  have hp := hpost
  sig_post [VG.Proof.RsaKeyGen.X86.Search.contract, Proof.RsaKeyGen.primeSearchContract,
    Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal, argBytes, Abi.withConsts,
    VG.Impl.RsaKeyGen.TrialTable32.consts] at hp
  have hk : KeyOk p st u.mem := h.key.frame hi.kBound'
    (by rw [← hi.kR_eq]; exact A.lowK.sub_left (low_sub (by decide))) hfr
  simp only [ce_arg F ha _ _ (show 0 < 12 by decide), ce_arg F ha _ _ (show 1 < 12 by decide), ce_arg F ha _ _ (show 2 < 12 by decide), ce_arg F ha _ _ (show 3 < 12 by decide), ce_arg F ha _ _ (show 4 < 12 by decide), ce_arg F ha _ _ (show 5 < 12 by decide), ce_arg F ha _ _ (show 6 < 12 by decide), ce_arg F ha _ _ (show 7 < 12 by decide), ce_arg F ha _ _ (show 8 < 12 by decide), ce_arg F ha _ _ (show 11 < 12 by decide), ret_eq F,
    entry_result F h.used_le hst hk] at hp
  obtain ⟨hr, hout, hused, req, hwords, hreq⟩ := hp
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 1 = [0] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true, Nat.reduceMul] at hwords hused
  obtain ⟨w0, w1, w2, w3⟩ := hwords
  rw [sa1 hi] at hout hreq w1 w2
  rw [sb0 hi, hm₂] at hout
  rw [show (searchArg p used (phaseWord st.phase) 11).setWidth 64 = p.stp.setWidth 64 from rfl, hm₂] at w0 w1 w2 w3
  rw [show searchArg p used (phaseWord st.phase) 2 = p.up from rfl, hm₂] at hused
  -- What the call wrote.
  have hsl := c.stack
  have hv := hi.len_valid
  have bc := below_call F (n := stackUse c.code + 4) (by omega)
  have Fs : Region.Sub (fR o 48) (lowR o) := low_sub (by decide)
  have Bs : Region.Sub (below (u.gpr .esp) (stackUse c.code + 4)) (lowR o) := by rw [bc]; exact low_sub (by omega)
  have Ps : Region.Sub ⟨low o + BitVec.ofNat 64 268, 16⟩ (lowR o) := low_sub (by decide)
  have sO := subO hi (used := used) (phaseWord st.phase)
  have sS := subS hi (used := used) (phaseWord st.phase)
  have sU : Region.Sub (cU p used (phaseWord st.phase)) (uR o) := by rw [eqU hi]; exact fun _ h => h
  have sB : Region.Sub (cB p used (phaseWord st.phase)) (bR o) := by rw [eqB hi]; exact fun _ h => h
  have eO : cO p used (phaseWord st.phase) = ⟨outOf p (phaseWord st.phase), p.L⟩ := by
    simp only [cO]; rw [sb0 hi, sa1 hi]
  have frC : Frame (changes o) u.mem u'.mem := hf.sub fun r hr => by
    simp only [sWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨kR o, by simp [changes], sO⟩
    · exact ⟨uR o, by simp [changes], sU⟩
    · exact ⟨bR o, by simp [changes], sB⟩
    · exact ⟨sR o, by simp [changes], sS⟩
    · exact ⟨below (o.gpr .esp) 284, by simp [changes], by rw [← hi.low_eq]; exact Fs⟩
    · exact ⟨below (o.gpr .esp) 284, by simp [changes], by rw [← hi.low_eq]; exact Bs⟩
  have sv : Saved u'.mem p.S1 o := saved_frame hi (fun r hr => by
    simp only [sWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (A.lowK.sub_left Ps).sub_right sO
    · exact (A.lowU.sub_left Ps).sub_right sU
    · exact (A.lowB.sub_left Ps).sub_right sB
    · exact (A.lowS.sub_left Ps).sub_right sS
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · rw [bc]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) hf F.saved
  have hiR (d : Nat) (hd : 32 ≤ d) (hd' : d + 8 ≤ 56) :
      ∀ r ∈ sWr p used (phaseWord st.phase) o ++ [below (u.gpr .esp) (stackUse c.code + 4)],
        Region.Disjoint ⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, 8⟩ r := by
    have X : Region.Sub ⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, 8⟩ (sR o) := by
      rw [hi.sR_eq]; exact Offset.sub_base _ hd'
    intro r hr
    simp only [sWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (A.ks.symm.sub_left X).sub_right sO
    · exact (A.us.symm.sub_left X).sub_right sU
    · exact (A.bs.symm.sub_left X).sub_right sB
    · exact (Offset.base_disjoint _ (by omega) (by have := hi.sBound'; omega)).symm
    · exact (A.lowS.symm.sub_left X).sub_right Fs
    · exact (A.lowS.symm.sub_left X).sub_right Bs
  have hrem := Proof.RsaKeyGen.KeySearch.primeSearch_remaining_le p.L p.eB st.phase.other st.remaining
    ((genRand o).drop used)
  have keep (r : Reg) (hr : r ∈ calleeSaved) (h1 : r ≠ .eax) (h2 : r ≠ .ecx) (h3 : r ≠ .edx) (hne : r ≠ .esp) :
      (freed 48 u').gpr r = s.gpr r := by
    rw [freed_gpr _ _ hne, hcs r hr, F.keep r h1 h2 h3 hne]
  have randT : Spec.Rsa.bytesAt u'.mem (p.rp.setWidth 64) p.randLen = genRand o := by
    have := hi.bytes_frame (F.frame.trans frC)
    rw [hi.rR_eq] at this
    exact this.trans (by rw [hi.rp_eq, hi.randLen_eq])
  have stT : StateOk p ⟨st.left, st.phase, (rOf p o used st).remaining⟩ u'.mem :=
    ⟨w0, w1, w2, (word_keep hf (hiR 32 (by decide) (by decide))).trans hst.phase,
      (word_keep hf (hiR 40 (by decide) (by decide))).trans hst.left,
      (bytes_keep (R := ⟨p.stp.setWidth 64 + BitVec.ofNat 64 48, 8⟩) hf (hiR 48 (by decide) (by decide))
        (show 8 ≤ 2 ^ 64 by decide)).trans hst.e,
      Nat.le_trans hrem hst.remaining_le, hst.left_lt⟩
  have memT : Frame (searchChanges p o (phaseWord st.phase)) s.mem u'.mem := by
    refine Frame.trans (m₂ := u.mem) (hfr.sub fun r hr => ?_) (hf.sub fun r hr => ?_)
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨below (o.gpr .esp) 284, by simp [searchChanges], by rw [← hi.low_eq]; exact Fs⟩
    · simp only [sWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨outOf p (phaseWord st.phase), p.L⟩, by simp [searchChanges], by rw [eO]; exact fun _ h => h⟩
      · exact ⟨uR o, by simp [searchChanges], sU⟩
      · exact ⟨bR o, by simp [searchChanges], sB⟩
      · exact ⟨⟨p.stp.setWidth 64, 32⟩, by simp [searchChanges], fun _ h => h⟩
      · exact ⟨below (o.gpr .esp) 284, by simp [searchChanges], by rw [← hi.low_eq]; exact Fs⟩
      · exact ⟨below (o.gpr .esp) 284, by simp [searchChanges], by rw [← hi.low_eq]; exact Bs⟩
  refine ⟨⟨⟨hi, ?_, ?_, sy'.trans F.syms, ?_, sv, F.frame.trans frC⟩, h.used_le,
    (keep .ebp (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.ebp,
    (keep .esi (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.esi,
    (keep .edi (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.edi, randT, stT⟩,
    (keep .ebx (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.ebx,
    by rw [freed_gpr _ _ (by decide)]; exact hr, hused, hout, ⟨req, w3, hreq⟩, memT⟩
  · show u'.rd = o.rd
    rw [hrd, F.rd]
  · change u'.wr.tail = _
    rw [hwr, F.wr]; rfl
  · rw [freed_esp, hcs .esp (by decide), F.esp, BitVec.sub_add_cancel]

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The key's arguments (i686)

`n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` at the key's slots 0, 2, 4, 5, 6,
7 and 8, with their lengths; `e` the state's last word; the working space.
In the call's frame of 72 bytes, at 196 above `low o` (`keyArgs_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)

/-- The key's argument `j`. -/
def keyArg (p : GenPublic) : Nat → BitVec 32
  | 0 => p.kp
  | 1 => BitVec.ofNat 32 (2 * p.L)
  | 2 => p.kp + BitVec.ofNat 32 (2 * p.L)
  | 3 => BitVec.ofNat 32 (2 * p.L)
  | 4 => p.kp + BitVec.ofNat 32 (4 * p.L)
  | 5 => BitVec.ofNat 32 p.L
  | 6 => p.kp + BitVec.ofNat 32 (5 * p.L)
  | 7 => BitVec.ofNat 32 p.L
  | 8 => p.kp + BitVec.ofNat 32 (6 * p.L)
  | 9 => BitVec.ofNat 32 p.L
  | 10 => p.kp + BitVec.ofNat 32 (7 * p.L)
  | 11 => BitVec.ofNat 32 p.L
  | 12 => p.kp + BitVec.ofNat 32 (8 * p.L)
  | 13 => BitVec.ofNat 32 p.L
  | 14 => p.stp + 48
  | 15 => 8
  | 16 => p.B
  | _ => BitVec.ofNat 32 p.words

/-- The key's arguments are in its frame. -/
def KArgs (p : GenPublic) (o : State) (m : Mem) : Prop :=
  ∀ j < 18, m.readW (low o + BitVec.ofNat 64 (196 + 4 * j)) 32 = keyArg p j

theorem keyArgs_ok {p : GenPublic} {o s₀ t : State} (h : Fr p o s₀ 72 t)
    (hbp : t.gpr .ebp = BitVec.ofNat 32 p.L) :
    WP isa (.block keyArgs) t fun u =>
      (KArgs p o u.mem ∧ Frame [fR o 72] t.mem u.mem) ∧ Keep [.ecx, .edx] t u := by
  have hi := h.input
  refine WP.keep _ ?_ (by rfl)
  simp only [keyArgs, param_eq, pushWords, keyWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, h.slot_ea' (by decide) (j := 0) (d := 0) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 1) (d := 4) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 2) (d := 8) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 3) (d := 12) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 4) (d := 16) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 5) (d := 20) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 6) (d := 24) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 7) (d := 28) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 8) (d := 32) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 9) (d := 36) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 10) (d := 40) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 11) (d := 44) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 12) (d := 48) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 13) (d := 52) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 14) (d := 56) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 15) (d := 60) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 16) (d := 64) rfl (by decide) rfl, h.slot_ea' (by decide) (j := 17) (d := 68) rfl (by decide) rfl, h.slot_in' (by decide) (j := 0) (by decide) rfl, h.slot_in' (by decide) (j := 1) (by decide) rfl, h.slot_in' (by decide) (j := 2) (by decide) rfl, h.slot_in' (by decide) (j := 3) (by decide) rfl, h.slot_in' (by decide) (j := 4) (by decide) rfl, h.slot_in' (by decide) (j := 5) (by decide) rfl, h.slot_in' (by decide) (j := 6) (by decide) rfl, h.slot_in' (by decide) (j := 7) (by decide) rfl, h.slot_in' (by decide) (j := 8) (by decide) rfl, h.slot_in' (by decide) (j := 9) (by decide) rfl, h.slot_in' (by decide) (j := 10) (by decide) rfl, h.slot_in' (by decide) (j := 11) (by decide) rfl, h.slot_in' (by decide) (j := 12) (by decide) rfl, h.slot_in' (by decide) (j := 13) (by decide) rfl, h.slot_in' (by decide) (j := 14) (by decide) rfl, h.slot_in' (by decide) (j := 15) (by decide) rfl, h.slot_in' (by decide) (j := 16) (by decide) rfl, h.slot_in' (by decide) (j := 17) (by decide) rfl, h.arg_ea (w := 18) (i := 0) (d := 92) rfl, h.arg_in (i := 0) (by decide), h.arg_val (i := 0) (by decide), h.arg_ea (w := 18) (i := 5) (d := 112) rfl, h.arg_in (i := 5) (by decide), h.arg_val (i := 5) (by decide), h.arg_ea (w := 18) (i := 6) (d := 116) rfl, h.arg_in (i := 6) (by decide), h.arg_val (i := 6) (by decide), h.arg_ea (w := 18) (i := 7) (d := 120) rfl, h.arg_in (i := 7) (by decide), h.arg_val (i := 7) (by decide), hbp]
  have A := hi.abi
  simp (disch := decide) only [rd_arg A, h.arg_val]
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
      j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, rdS, rdN, keyArg,
      hi.kp_eq, hi.B_eq, hi.stp_eq, hi.words_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    all_goals
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
  · iterate 18 (refine fr_slot ?_ ?hk _; case hk => decide)
    exact Frame.refl _ _

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The key's precondition (i686)

With its eighteen arguments in the frame (`KArgs`), `vg_rsa_keygen_key`'s
contract holds on its entry, narrowed to `e`, which it reads, and to the
key's seven numbers, the working space and its frame of arguments, which it
writes (`key_pre`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86

/-- An implementation of `vg_rsa_keygen_key`, as the controller calls it:
its name, its code, its proof and the stack it uses. -/
structure KeyImpl where
  name : String
  code : Prog isa
  verified : Verified target code VG.Proof.RsaKeyGen.X86.Key.contract
  noSp : NoSp code
  stack : stackUse code ≤ 68

/-- The key, as the controller calls it. -/
abbrev KeyImpl.call (c : KeyImpl) : Prog isa := .call c.name c.code

section
variable (p : GenPublic)

/-- The key's regions: the seven numbers and `e` (arguments `i` and `j`), and
the working space. -/
abbrev kG (i j : Nat) : Region := ⟨(keyArg p i).setWidth 64, (keyArg p j).toNat⟩
abbrev kB : Region := ⟨(keyArg p 16).setWidth 64, (keyArg p 17).toNat * 8⟩

end

/-- What the key may read and write. -/
abbrev kRd (p : GenPublic) : List Region := [kG p 14 15]
abbrev kWr (p : GenPublic) (o : State) : List Region :=
  [kG p 0 1, kG p 2 3, kG p 4 5, kG p 6 7, kG p 8 9, kG p 10 11, kG p 12 13, kB p, fR o 72]

theorem ce_key {p : GenPublic} {o s₀ t : State} (h : Fr p o s₀ 72 t)
    (ha : KArgs p o t.mem) (rd wr : List Region) {j : Nat} (hj : j < 18) :
    arg (t.callEntry.withRegions rd wr) j = keyArg p j := by
  have A := h.input.abi
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 (16 + 72) := by
    rw [h.esp, GenPublic.S1, h.input.sp_eq, BitVec.sub_sub, ← BitVec.ofNat_add]
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 88 := by
    rw [he]; exact VG.X86.sub_toNat (by omega)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    addr_sub A (by decide) (by omega), show 284 - (16 + 72) + 4 * j = 196 + 4 * j by omega]

section Facts

variable {p : GenPublic} {o : State} (h : GenInput p o)
include h

/-- A number of the key, at `c p_len` of its buffer, of `n p_len` octets. -/
theorem kNum {i j : Nat} (c n : Nat) (hc : c + n ≤ 9 ∧ c ≤ 8) (hi : keyArg p i = p.kp + BitVec.ofNat 32 (c * p.L))
    (hj : (keyArg p j).toNat = n * p.L) : kG p i j = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c * p.L), n * p.L⟩ := by
  have := h.kBound'
  have := h.len_valid
  have hn : c * p.L + n * p.L ≤ 9 * p.L := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hc.1
  have h8 := Nat.mul_le_mul_right p.L (show c ≤ 8 by omega)
  simp only [kG]
  rw [hi, hj, VG.Proof.MlKem.X86.ea_off (by omega)]

theorem kL1 : (BitVec.ofNat 32 p.L).toNat = 1 * p.L := by
  have := h.len_valid; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem kL2 : (BitVec.ofNat 32 (2 * p.L)).toNat = 2 * p.L := by
  have := h.len_valid; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem kE0 : kG p 0 1 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (0 * p.L), 2 * p.L⟩ :=
  kNum h 0 2 (by decide) (by simp [keyArg]) (kL2 h)

theorem kE1 : kG p 2 3 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (2 * p.L), 2 * p.L⟩ :=
  kNum h 2 2 (by decide) (rfl) (kL2 h)

theorem kE2 : kG p 4 5 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (4 * p.L), 1 * p.L⟩ :=
  kNum h 4 1 (by decide) (rfl) (kL1 h)

theorem kE3 : kG p 6 7 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (5 * p.L), 1 * p.L⟩ :=
  kNum h 5 1 (by decide) (rfl) (kL1 h)

theorem kE4 : kG p 8 9 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (6 * p.L), 1 * p.L⟩ :=
  kNum h 6 1 (by decide) (rfl) (kL1 h)

theorem kE5 : kG p 10 11 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (7 * p.L), 1 * p.L⟩ :=
  kNum h 7 1 (by decide) (rfl) (kL1 h)

theorem kE6 : kG p 12 13 = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (8 * p.L), 1 * p.L⟩ :=
  kNum h 8 1 (by decide) (rfl) (kL1 h)

theorem kSub {c n : Nat} (hc : c + n ≤ 9) :
    Region.Sub ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c * p.L), n * p.L⟩ (kR o) := by
  rw [h.kR_eq]; refine Offset.sub_base _ ?_
  rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hc

theorem kDisj {c n c' n' : Nat} (hc : c + n ≤ 9) (hc' : c' + n' ≤ 9) (hd : c + n ≤ c' ∨ c' + n' ≤ c) :
    Region.Disjoint ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c * p.L), n * p.L⟩
      ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c' * p.L), n' * p.L⟩ := by
  have := h.len_valid
  have m1 : c * p.L + n * p.L ≤ 9 * p.L := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hc
  have m2 : c' * p.L + n' * p.L ≤ 9 * p.L := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hc'
  refine Offset.disjoint _ ?_ (by omega) (by omega)
  rcases hd with hd | hd
  · left; rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hd
  · right; rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hd

theorem kSubE : Region.Sub (kG p 14 15) (sR o) := by
  have := h.sBound'
  simp only [kG]
  rw [show (keyArg p 15).toNat = 8 from rfl, h.sR_eq,
    show (keyArg p 14).setWidth 64 = p.stp.setWidth 64 + BitVec.ofNat 64 48 from
      VG.Proof.MlKem.X86.ea_off (x := p.stp) (d := 48) (by omega)]
  exact Offset.sub_base _ (by decide)

theorem kEqB : kB p = bR o := by
  have := h.words_lt
  simp only [kB]
  rw [show (keyArg p 17).toNat = p.words by
      show (BitVec.ofNat 32 p.words).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this],
    show keyArg p 16 = p.B from rfl, h.B_eq, h.words_eq]

end Facts

theorem key_pre {p : GenPublic} {o s₀ t : State} (h : Fr p o s₀ 72 t) (ha : KArgs p o t.mem) :
    VG.Proof.RsaKeyGen.X86.Key.contract.pre (t.callEntry.withRegions (kRd p) (kWr p o)) := by
  have hi := h.input
  have A := hi.abi
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hl := low_toNat A
  have hv := hi.len_valid
  have hE : t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 92 := by
    rw [h.esp, GenPublic.S1, hi.sp_eq, BitVec.sub_sub, BitVec.sub_sub]; rfl
  have hn92 : (o.gpr .esp - BitVec.ofNat 32 92).toNat = (o.gpr .esp).toNat - 92 := VG.X86.sub_toNat (by omega)
  have hret : (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 192 := by
    rw [hE]
    have e := addr_sub A (k := 92) (d := 0) (by decide) (by decide)
    simpa only [addr, BitVec.add_zero] using e
  have hlw : low o + BitVec.ofNat 64 192 - 68#64 = low o + BitVec.ofNat 64 124 := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ha0 : argAddr (t.callEntry.withRegions (kRd p) (kWr p o)) 0 = low o + BitVec.ofNat 64 196 := by
    rw [argAddr_withRegions, argAddr_callEntry, h.slot_ea (by decide) (j := 0) (by decide)]
  have hsl : 68 ≤ (t.gpr .esp - 4).toNat := by rw [hE, hn92]; omega
  have hsb : (t.gpr .esp - 4).toNat + 4 + 72 ≤ 2 ^ 32 := by rw [hE, hn92]; omega
  have sB : Region.Sub (kB p) (bR o) := by rw [kEqB hi]; exact fun _ h => h
  have sA : Region.Sub ⟨low o + BitVec.ofNat 64 196, 72⟩ (lowR o) := low_sub (by decide)
  have sT : Region.Sub ⟨low o + BitVec.ofNat 64 192, 4⟩ (lowR o) := low_sub (by decide)
  have sW : Region.Sub ⟨low o + BitVec.ofNat 64 124, 68⟩ (lowR o) := low_sub (by decide)
  have dN0N1 : Region.Disjoint (kG p 0 1) (kG p 2 3) := by rw [kE0 hi, kE1 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN0N2 : Region.Disjoint (kG p 0 1) (kG p 4 5) := by rw [kE0 hi, kE2 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN0N3 : Region.Disjoint (kG p 0 1) (kG p 6 7) := by rw [kE0 hi, kE3 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN0N4 : Region.Disjoint (kG p 0 1) (kG p 8 9) := by rw [kE0 hi, kE4 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN0N5 : Region.Disjoint (kG p 0 1) (kG p 10 11) := by rw [kE0 hi, kE5 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN0N6 : Region.Disjoint (kG p 0 1) (kG p 12 13) := by rw [kE0 hi, kE6 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN0E : Region.Disjoint (kG p 0 1) (kG p 14 15) := dj A.ks (by rw [kE0 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN0B : Region.Disjoint (kG p 0 1) (kB p) := dj A.kb (by rw [kE0 hi]; exact kSub hi (by decide)) sB
  have dN0A : Region.Disjoint (kG p 0 1) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE0 hi]; exact kSub hi (by decide)) sA
  have dN1N2 : Region.Disjoint (kG p 2 3) (kG p 4 5) := by rw [kE1 hi, kE2 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN1N3 : Region.Disjoint (kG p 2 3) (kG p 6 7) := by rw [kE1 hi, kE3 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN1N4 : Region.Disjoint (kG p 2 3) (kG p 8 9) := by rw [kE1 hi, kE4 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN1N5 : Region.Disjoint (kG p 2 3) (kG p 10 11) := by rw [kE1 hi, kE5 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN1N6 : Region.Disjoint (kG p 2 3) (kG p 12 13) := by rw [kE1 hi, kE6 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN1E : Region.Disjoint (kG p 2 3) (kG p 14 15) := dj A.ks (by rw [kE1 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN1B : Region.Disjoint (kG p 2 3) (kB p) := dj A.kb (by rw [kE1 hi]; exact kSub hi (by decide)) sB
  have dN1A : Region.Disjoint (kG p 2 3) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE1 hi]; exact kSub hi (by decide)) sA
  have dN2N3 : Region.Disjoint (kG p 4 5) (kG p 6 7) := by rw [kE2 hi, kE3 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN2N4 : Region.Disjoint (kG p 4 5) (kG p 8 9) := by rw [kE2 hi, kE4 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN2N5 : Region.Disjoint (kG p 4 5) (kG p 10 11) := by rw [kE2 hi, kE5 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN2N6 : Region.Disjoint (kG p 4 5) (kG p 12 13) := by rw [kE2 hi, kE6 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN2E : Region.Disjoint (kG p 4 5) (kG p 14 15) := dj A.ks (by rw [kE2 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN2B : Region.Disjoint (kG p 4 5) (kB p) := dj A.kb (by rw [kE2 hi]; exact kSub hi (by decide)) sB
  have dN2A : Region.Disjoint (kG p 4 5) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE2 hi]; exact kSub hi (by decide)) sA
  have dN3N4 : Region.Disjoint (kG p 6 7) (kG p 8 9) := by rw [kE3 hi, kE4 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN3N5 : Region.Disjoint (kG p 6 7) (kG p 10 11) := by rw [kE3 hi, kE5 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN3N6 : Region.Disjoint (kG p 6 7) (kG p 12 13) := by rw [kE3 hi, kE6 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN3E : Region.Disjoint (kG p 6 7) (kG p 14 15) := dj A.ks (by rw [kE3 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN3B : Region.Disjoint (kG p 6 7) (kB p) := dj A.kb (by rw [kE3 hi]; exact kSub hi (by decide)) sB
  have dN3A : Region.Disjoint (kG p 6 7) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE3 hi]; exact kSub hi (by decide)) sA
  have dN4N5 : Region.Disjoint (kG p 8 9) (kG p 10 11) := by rw [kE4 hi, kE5 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN4N6 : Region.Disjoint (kG p 8 9) (kG p 12 13) := by rw [kE4 hi, kE6 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN4E : Region.Disjoint (kG p 8 9) (kG p 14 15) := dj A.ks (by rw [kE4 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN4B : Region.Disjoint (kG p 8 9) (kB p) := dj A.kb (by rw [kE4 hi]; exact kSub hi (by decide)) sB
  have dN4A : Region.Disjoint (kG p 8 9) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE4 hi]; exact kSub hi (by decide)) sA
  have dN5N6 : Region.Disjoint (kG p 10 11) (kG p 12 13) := by rw [kE5 hi, kE6 hi]; exact kDisj hi (by decide) (by decide) (by decide)
  have dN5E : Region.Disjoint (kG p 10 11) (kG p 14 15) := dj A.ks (by rw [kE5 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN5B : Region.Disjoint (kG p 10 11) (kB p) := dj A.kb (by rw [kE5 hi]; exact kSub hi (by decide)) sB
  have dN5A : Region.Disjoint (kG p 10 11) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE5 hi]; exact kSub hi (by decide)) sA
  have dN6E : Region.Disjoint (kG p 12 13) (kG p 14 15) := dj A.ks (by rw [kE6 hi]; exact kSub hi (by decide)) (kSubE hi)
  have dN6B : Region.Disjoint (kG p 12 13) (kB p) := dj A.kb (by rw [kE6 hi]; exact kSub hi (by decide)) sB
  have dN6A : Region.Disjoint (kG p 12 13) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowK.symm (by rw [kE6 hi]; exact kSub hi (by decide)) sA
  have dEB : Region.Disjoint (kG p 14 15) (kB p) := dj A.bs.symm (kSubE hi) sB
  have dEA : Region.Disjoint (kG p 14 15) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowS.symm (kSubE hi) sA
  have dBA : Region.Disjoint (kB p) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := dj A.lowB.symm sB sA
  have dTN0 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 0 1) := dj A.lowK sT (by rw [kE0 hi]; exact kSub hi (by decide))
  have dTN1 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 2 3) := dj A.lowK sT (by rw [kE1 hi]; exact kSub hi (by decide))
  have dTN2 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 4 5) := dj A.lowK sT (by rw [kE2 hi]; exact kSub hi (by decide))
  have dTN3 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 6 7) := dj A.lowK sT (by rw [kE3 hi]; exact kSub hi (by decide))
  have dTN4 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 8 9) := dj A.lowK sT (by rw [kE4 hi]; exact kSub hi (by decide))
  have dTN5 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 10 11) := dj A.lowK sT (by rw [kE5 hi]; exact kSub hi (by decide))
  have dTN6 : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 12 13) := dj A.lowK sT (by rw [kE6 hi]; exact kSub hi (by decide))
  have dTE : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kG p 14 15) := dj A.lowS sT (kSubE hi)
  have dTB : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (kB p) := dj A.lowB sT sB
  have dTA : Region.Disjoint (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have dWN0 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 0 1) := dj A.lowK sW (by rw [kE0 hi]; exact kSub hi (by decide))
  have dWN1 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 2 3) := dj A.lowK sW (by rw [kE1 hi]; exact kSub hi (by decide))
  have dWN2 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 4 5) := dj A.lowK sW (by rw [kE2 hi]; exact kSub hi (by decide))
  have dWN3 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 6 7) := dj A.lowK sW (by rw [kE3 hi]; exact kSub hi (by decide))
  have dWN4 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 8 9) := dj A.lowK sW (by rw [kE4 hi]; exact kSub hi (by decide))
  have dWN5 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 10 11) := dj A.lowK sW (by rw [kE5 hi]; exact kSub hi (by decide))
  have dWN6 : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 12 13) := dj A.lowK sW (by rw [kE6 hi]; exact kSub hi (by decide))
  have dWE : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kG p 14 15) := dj A.lowS sW (kSubE hi)
  have dWB : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (kB p) := dj A.lowB sW sB
  have dWA : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (⟨low o + BitVec.ofNat 64 196, 72⟩ : Region) := Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have dWT : Region.Disjoint (⟨low o + BitVec.ofNat 64 124, 68⟩ : Region) (⟨low o + BitVec.ofNat 64 192, 4⟩ : Region) := Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have kb := hi.kBound'
  have bnum (i j c n : Nat) (hc : c + n ≤ 9 ∧ c ≤ 8) (he : kG p i j = ⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c * p.L), n * p.L⟩)
      (hi' : keyArg p i = p.kp + BitVec.ofNat 32 (c * p.L)) :
      (keyArg p i).toNat + (keyArg p j).toNat ≤ 2 ^ 32 := by
    have hl : (keyArg p j).toNat = n * p.L := congrArg Region.len he
    have hn : c * p.L + n * p.L ≤ 9 * p.L := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hc.1
    have h8 := Nat.mul_le_mul_right p.L (show c ≤ 8 by omega)
    rw [hl, hi', tn_add _ (by omega)]; omega
  have g0 := bnum 0 1 0 2 (by decide) (kE0 hi) (by simp [keyArg])
  have g2 := bnum 2 3 2 2 (by decide) (kE1 hi) rfl
  have g4 := bnum 4 5 4 1 (by decide) (kE2 hi) rfl
  have g6 := bnum 6 7 5 1 (by decide) (kE3 hi) rfl
  have g8 := bnum 8 9 6 1 (by decide) (kE4 hi) rfl
  have g10 := bnum 10 11 7 1 (by decide) (kE5 hi) rfl
  have g12 := bnum 12 13 8 1 (by decide) (kE6 hi) rfl
  have g14 : (keyArg p 14).toNat + (keyArg p 15).toNat ≤ 2 ^ 32 := by
    rw [show (keyArg p 15).toNat = 8 from rfl]
    have := hi.sBound'
    rw [show keyArg p 14 = p.stp + BitVec.ofNat 32 48 from rfl, tn_add _ (by omega)]; omega
  have g16 : (keyArg p 16).toNat + (keyArg p 17).toNat * 8 ≤ 2 ^ 32 := by
    have := congrArg Region.len (kEqB hi)
    simp only at this
    rw [this, show keyArg p 16 = p.B from rfl, hi.B_eq]; exact A.bBound
  have l1 : (keyArg p 1).toNat = 2 * p.L := kL2 hi
  have l3 : (keyArg p 3).toNat = 2 * p.L := kL2 hi
  have l5 : (keyArg p 5).toNat = p.L := by rw [show keyArg p 5 = BitVec.ofNat 32 p.L from rfl, kL1 hi]; omega
  have l7 : (keyArg p 7).toNat = p.L := l5
  have l9 : (keyArg p 9).toNat = p.L := l5
  have l11 : (keyArg p 11).toNat = p.L := l5
  have l13 : (keyArg p 13).toNat = p.L := l5
  have l17 : (keyArg p 17).toNat = p.words := by
    have := hi.words_lt
    show (BitVec.ofNat 32 p.words).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
  have gLen : Spec.RsaKeyGen.primeLenValid (keyArg p 5).toNat := by rw [l5, hi.L_eq]; exact A.lenValid
  have gN : (keyArg p 1).toNat = 2 * (keyArg p 5).toNat := by rw [l1, l5]
  have gD : (keyArg p 3).toNat = (keyArg p 1).toNat := by rw [l1, l3]
  have gQ : (keyArg p 7).toNat = (keyArg p 5).toNat := by rw [l7, l5]
  have gDp : (keyArg p 9).toNat = (keyArg p 5).toNat := by rw [l9, l5]
  have gDq : (keyArg p 11).toNat = (keyArg p 5).toNat := by rw [l11, l5]
  have gQi : (keyArg p 13).toNat = (keyArg p 5).toNat := by rw [l13, l5]
  have gE1 : 1 ≤ (keyArg p 15).toNat := (by decide : 1 ≤ 8)
  have gE8 : (keyArg p 15).toNat ≤ 8 := Nat.le_refl 8
  have gScr : Spec.Rsa.scratchWords (keyArg p 1).toNat ≤ (keyArg p 17).toNat := by
    rw [l1, l17]
    have := A.scratchLength
    rwa [← hi.L_eq, ← hi.words_eq] at this
  sig_pre [VG.Proof.RsaKeyGen.X86.Key.contract, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argSlots,
    argVal, argBytes, stackBelow, VG.Proof.RsaKeyGen.X86.Key.keyStack]
  simp only [ce_key h ha _ _ (show 0 < 18 by decide), ce_key h ha _ _ (show 1 < 18 by decide), ce_key h ha _ _ (show 2 < 18 by decide), ce_key h ha _ _ (show 3 < 18 by decide), ce_key h ha _ _ (show 4 < 18 by decide), ce_key h ha _ _ (show 5 < 18 by decide), ce_key h ha _ _ (show 6 < 18 by decide), ce_key h ha _ _ (show 7 < 18 by decide), ce_key h ha _ _ (show 8 < 18 by decide), ce_key h ha _ _ (show 9 < 18 by decide), ce_key h ha _ _ (show 10 < 18 by decide), ce_key h ha _ _ (show 11 < 18 by decide), ce_key h ha _ _ (show 12 < 18 by decide), ce_key h ha _ _ (show 13 < 18 by decide), ce_key h ha _ _ (show 14 < 18 by decide), ce_key h ha _ _ (show 15 < 18 by decide), ce_key h ha _ _ (show 16 < 18 by decide), ce_key h ha _ _ (show 17 < 18 by decide), ha0, hret, hlw]
  sig_and_intros
  all_goals first
    | exact True.intro
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | rfl

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The key's call (i686)

`vg_rsa_keygen_key`, called in its frame of arguments on the primes at the
slots of `p` and `q`, leaves its status in `eax`, the key (or zeros) at the
key's buffer, and the rest of the controller's state as it was (`key_run`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Spec.RsaKeyGen (KeyProgress)
open VG.Proof.RsaKeyGen (keyOp keyStatus)

/-- The key from the primes at the slots of `p` and `q`. -/
abbrev keyOf (p : GenPublic) (m : Mem) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  keyOp p.L p.eB (Spec.Rsa.bytesAt m (p.slot 4) p.L) (Spec.Rsa.bytesAt m (p.slot 5) p.L)

/-- The key's outputs at the key's buffer. -/
def keyOutsOf (p : GenPublic) : List (Addr × Nat) :=
  [(p.kp.setWidth 64, 2 * p.L), (p.slot 2, 2 * p.L), (p.slot 4, p.L), (p.slot 5, p.L), (p.slot 6, p.L),
    (p.slot 7, p.L), (p.slot 8, p.L)]

/-- What the key leaves. -/
structure AfterKey (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p o used st t
  ebx : t.gpr .ebx = s.gpr .ebx
  status : (t.gpr .eax).toNat = keyStatus (keyOf p s.mem)
  out : match keyOf p s.mem with
    | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
  mem : Frame [kR o, bR o, below (o.gpr .esp) 284] s.mem t.mem

/-- The key's regions, among those of a state in its frame. -/
theorem key_covers {p : GenPublic} {o s₀ u : State} (h : Fr p o s₀ 72 u) :
    Covers (kRd p ++ kWr p o) (u.rd ++ u.wr) ∧ Covers (kWr p o) u.wr := by
  have hi := h.input
  have A := hi.abi
  have hv := hi.len_valid
  have num {c n : Nat} (hc : c + n ≤ 9) : ∃ r' ∈ u.wr, ∃ off,
      (⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c * p.L), n * p.L⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
        off + (⟨p.kp.setWidth 64 + BitVec.ofNat 64 (c * p.L), n * p.L⟩ : Region).len ≤ r'.len := by
    refine ⟨kR o, by rw [h.wr, A.wr]; simp, c * p.L, by rw [hi.kp_eq], ?_⟩
    show c * p.L + n * p.L ≤ (arg o 1).toNat
    rw [A.keyLen, ← hi.L_eq, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ hc
  have hw : ∀ r ∈ kWr p o, ∃ r' ∈ u.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
    intro r hr
    simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [kE0 hi]; exact num (by decide)
    · rw [kE1 hi]; exact num (by decide)
    · rw [kE2 hi]; exact num (by decide)
    · rw [kE3 hi]; exact num (by decide)
    · rw [kE4 hi]; exact num (by decide)
    · rw [kE5 hi]; exact num (by decide)
    · rw [kE6 hi]; exact num (by decide)
    · rw [kEqB hi]; exact ⟨bR o, by rw [h.wr, A.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨fR o 72, by rw [h.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain rfl := List.mem_singleton.mp hr
    have := hi.sBound'
    refine ⟨sR o, List.mem_append_right _ (by rw [h.wr, A.wr]; simp), 48, ?_, (by decide : 48 + 8 ≤ 56)⟩
    show (keyArg p 14).setWidth 64 = (arg o 7).setWidth 64 + _
    rw [← hi.stp_eq]
    exact VG.Proof.MlKem.X86.ea_off (x := p.stp) (d := 48) (by omega)
  · obtain ⟨r', hr', off, hb⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', off, hb⟩

theorem kbody_noSp (c : KeyImpl) : NoSp (.seq (.block keyArgs) c.call) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · have h : (Code.block keyArgs : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true := by decide
    rw [Code.allInstrs_eq] at h
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi
  · exact c.noSp i hi

theorem ret_key {p : GenPublic} {o s₀ u : State} (h : Fr p o s₀ 72 u) :
    (u.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 192 := by
  have A := h.input.abi
  have hE : u.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 92 := by
    rw [h.esp, GenPublic.S1, h.input.sp_eq, BitVec.sub_sub, BitVec.sub_sub]; rfl
  rw [hE]
  have e := addr_sub A (k := 92) (d := 0) (by decide) (by decide)
  simpa only [addr, BitVec.add_zero] using e

theorem below_key {p : GenPublic} {o s₀ u : State} (h : Fr p o s₀ 72 u) {n : Nat} (hn : n ≤ 196) :
    below (u.gpr .esp) n = ⟨low o + BitVec.ofNat 64 (196 - n), n⟩ := by
  have A := h.input.abi
  rw [h.esp, GenPublic.S1, h.input.sp_eq]
  change (⟨(o.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 72 - BitVec.ofNat 32 n).setWidth 64, n⟩ : Region) = _
  rw [BitVec.sub_sub, BitVec.sub_sub, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  have e := addr_sub A (k := 16 + (72 + n)) (d := 0) (by omega) (by omega)
  simp only [addr, BitVec.add_zero] at e
  rw [e, show 284 - (16 + (72 + n)) + 0 = 196 - n by omega]

/-- The state's words, through writes apart from the state. -/
theorem StateOk.frameL {p : GenPublic} {st : KeyProgress} {m m' : Mem} {rs : List Region} (h : StateOk p st m)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p.stp.setWidth 64, 56⟩ r) (fr : Frame rs m m') :
    StateOk p st m' := by
  have rd (d : Nat) (hd' : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d :=
    fr.readW (r := ⟨p.stp.setWidth 64, 56⟩) (Offset.contains_base _ hd' (by omega)) hd (by decide)
  refine ⟨(rd 0 (by decide)).trans h.remaining, (rd 8 (by decide)).trans h.len, (rd 16 (by decide)).trans h.cap,
    (rd 32 (by decide)).trans h.phase, (rd 40 (by decide)).trans h.left, ?_, h.remaining_le, h.left_lt⟩
  rw [← h.e]
  exact bytes_keep (R := ⟨p.stp.setWidth 64 + 48, 8⟩) fr
    (fun q hq => (hd q hq).sub_left (Offset.sub_base (d := 48) (n := 8) (k := 56) _ (by decide)))
    (show 8 ≤ 2 ^ 64 by decide)

theorem key_run (c : KeyImpl) {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p o used st s) : WP isa (keyRun c.call) s (AfterKey p o used st s) := by
  have hb := h.toGenBase
  have hi := hb.input
  have A := hi.abi
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have hsn : (s.gpr .esp).toNat = (o.gpr .esp).toNat - 16 := by
    rw [hb.sp, GenPublic.S1, hi.sp_eq]; exact VG.X86.sub_toNat (by omega)
  unfold keyRun
  rw [show 4 * keyWords = 72 from rfl]
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (kbody_noSp c) ?_
  have F0 := hb.alloc (n := 72) (by decide)
  refine WP.seq (WP.of_syms (WP.mono (keyArgs_ok F0 (by rw [allocFrame_gpr _ _ (by decide)]; exact h.ebp))
    fun u ⟨⟨ha, hfr⟩, k⟩ sy => ?_))
  have F := F0.stores (by decide) (k.mono (by decide)) sy hfr
  obtain ⟨cov, covW⟩ := key_covers F
  have hun : (u.gpr .esp).toNat = (o.gpr .esp).toNat - 88 := by
    rw [F.esp, GenPublic.S1, hi.sp_eq, BitVec.sub_sub, ← BitVec.ofNat_add]; exact VG.X86.sub_toNat (by omega)
  refine WP.of_syms (WP.call c.verified.1 c.noSp (by have := c.stack; omega)
    (key_pre F ha) cov covW fun u' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ sy' => ?_)
  have hp := hpost
  sig_post [VG.Proof.RsaKeyGen.X86.Key.contract, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argSlots,
    argVal, argBytes] at hp
  simp only [ce_key F ha _ _ (show 0 < 18 by decide), ce_key F ha _ _ (show 1 < 18 by decide), ce_key F ha _ _ (show 2 < 18 by decide), ce_key F ha _ _ (show 4 < 18 by decide), ce_key F ha _ _ (show 5 < 18 by decide), ce_key F ha _ _ (show 6 < 18 by decide), ce_key F ha _ _ (show 8 < 18 by decide), ce_key F ha _ _ (show 10 < 18 by decide), ce_key F ha _ _ (show 12 < 18 by decide), ce_key F ha _ _ (show 14 < 18 by decide), ce_key F ha _ _ (show 15 < 18 by decide), ret_key F] at hp
  have hsl := c.stack
  have hv := hi.len_valid
  have l1 : (keyArg p 1).toNat = 2 * p.L := kL2 hi
  have l5 : (keyArg p 5).toNat = p.L := by rw [show keyArg p 5 = BitVec.ofNat 32 p.L from rfl, kL1 hi]; omega
  have b0 : (keyArg p 0).setWidth 64 = p.kp.setWidth 64 := rfl
  have b2 : (keyArg p 2).setWidth 64 = p.slot 2 := congrArg Region.base (kE1 hi)
  have b4 : (keyArg p 4).setWidth 64 = p.slot 4 := congrArg Region.base (kE2 hi)
  have b6 : (keyArg p 6).setWidth 64 = p.slot 5 := congrArg Region.base (kE3 hi)
  have b8 : (keyArg p 8).setWidth 64 = p.slot 6 := congrArg Region.base (kE4 hi)
  have b10 : (keyArg p 10).setWidth 64 = p.slot 7 := congrArg Region.base (kE5 hi)
  have b12 : (keyArg p 12).setWidth 64 = p.slot 8 := congrArg Region.base (kE6 hi)
  have b14 : (keyArg p 14).setWidth 64 = p.stp.setWidth 64 + 48 := by
    have := hi.sBound'
    exact VG.Proof.MlKem.X86.ea_off (x := p.stp) (d := 48) (by omega)
  -- The key's inputs.
  have Fs : Region.Sub (fR o 72) (lowR o) := low_sub (by decide)
  have sT : Region.Sub ⟨low o + BitVec.ofNat 64 192, 4⟩ (lowR o) := low_sub (by decide)
  have sK : (lowR o).Disjoint ⟨p.kp.setWidth 64, 9 * p.L⟩ := by rw [← hi.kR_eq]; exact A.lowK
  have sS : (lowR o).Disjoint ⟨p.stp.setWidth 64, 56⟩ := by rw [← hi.sR_eq]; exact A.lowS
  have hst : StateOk p st u.mem := h.state.frame (R := fR o 72) (sS.sub_left Fs) hfr
  have fe : Frame [⟨low o + BitVec.ofNat 64 192, 4⟩] u.mem (u.mem.writeW (low o + BitVec.ofNat 64 192) (u.unknowns 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have slotIn (j : Nat) (hj : j + 1 ≤ 9) :
      Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 192) (u.unknowns 0)) (p.slot j) p.L =
        Spec.Rsa.bytesAt s.mem (p.slot j) p.L := by
    have hsub : Region.Sub ⟨p.slot j, p.L⟩ ⟨p.kp.setWidth 64, 9 * p.L⟩ := Offset.sub_base _ (by
      have := Nat.mul_le_mul_right p.L hj; rw [Nat.add_mul] at this; omega)
    rw [bytes_keep (R := ⟨p.slot j, p.L⟩) fe (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact (sK.sub_left sT).symm.sub_left hsub) (show p.L ≤ 2 ^ 64 by omega)]
    exact bytes_keep (R := ⟨p.slot j, p.L⟩) hfr (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact (sK.sub_left Fs).symm.sub_left hsub) (show p.L ≤ 2 ^ 64 by omega)
  have eIn : Spec.Rsa.bytesAt (u.mem.writeW (low o + BitVec.ofNat 64 192) (u.unknowns 0)) (p.stp.setWidth 64 + 48) 8 =
      p.eB := by
    rw [← hst.e]
    exact bytes_keep (R := ⟨p.stp.setWidth 64 + 48, 8⟩) fe (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact (sS.sub_left sT).symm.sub_left (Offset.sub_base (d := 48) (n := 8) (k := 56) _ (by decide)))
      (show 8 ≤ 2 ^ 64 by decide)
  rw [l5, b14, show (keyArg p 15).toNat = 8 from rfl, eIn, b4, b6, slotIn 4 (by decide), slotIn 5 (by decide),
    l1, b0, b2, b8, b10, b12, hm₂] at hp
  obtain ⟨hr, hout⟩ := hp
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  -- What the call wrote.
  have bc := below_key F (n := stackUse c.code + 4) (by omega)
  have Bs : Region.Sub (below (u.gpr .esp) (stackUse c.code + 4)) (lowR o) := by rw [bc]; exact low_sub (by omega)
  have Ps : Region.Sub ⟨low o + BitVec.ofNat 64 268, 16⟩ (lowR o) := low_sub (by decide)
  have sB : Region.Sub (kB p) (bR o) := by rw [kEqB hi]; exact fun _ h => h
  -- Each region the call wrote is within the key's buffer, the working space or the stack.
  have wcase : ∀ r ∈ kWr p o ++ [below (u.gpr .esp) (stackUse c.code + 4)],
      Region.Sub r (kR o) ∨ Region.Sub r (bR o) ∨ Region.Sub r (lowR o) ∧
        Region.Disjoint ⟨low o + BitVec.ofNat 64 268, 16⟩ r := by
    intro r hr
    simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl (by rw [kE0 hi]; exact kSub hi (by decide))
    · exact .inl (by rw [kE1 hi]; exact kSub hi (by decide))
    · exact .inl (by rw [kE2 hi]; exact kSub hi (by decide))
    · exact .inl (by rw [kE3 hi]; exact kSub hi (by decide))
    · exact .inl (by rw [kE4 hi]; exact kSub hi (by decide))
    · exact .inl (by rw [kE5 hi]; exact kSub hi (by decide))
    · exact .inl (by rw [kE6 hi]; exact kSub hi (by decide))
    · exact .inr (.inl sB)
    · exact .inr (.inr ⟨Fs, Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)⟩)
    · exact .inr (.inr ⟨Bs, by rw [bc]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)⟩)
  have frC : Frame (changes o) u.mem u'.mem := hf.sub fun r hr => by
    rcases wcase r hr with hs | hs | ⟨hs, -⟩
    · exact ⟨kR o, by simp [changes], hs⟩
    · exact ⟨bR o, by simp [changes], hs⟩
    · exact ⟨below (o.gpr .esp) 284, by simp [changes], by rw [← hi.low_eq]; exact hs⟩
  have sv : Saved u'.mem p.S1 o := saved_frame hi (fun r hr => by
    rcases wcase r hr with hs | hs | ⟨-, hd⟩
    · exact (A.lowK.sub_left Ps).sub_right hs
    · exact (A.lowB.sub_left Ps).sub_right hs
    · exact hd) hf F.saved
  have stT : StateOk p st u'.mem := hst.frameL (fun r hr => by
    rw [← hi.sR_eq]
    rcases wcase r hr with hs | hs | ⟨hs, -⟩
    · exact A.ks.symm.sub_right hs
    · exact A.bs.symm.sub_right hs
    · exact A.lowS.symm.sub_right hs) hf
  have keep (r : Reg) (hr : r ∈ calleeSaved) (h1 : r ≠ .eax) (h2 : r ≠ .ecx) (h3 : r ≠ .edx) (hne : r ≠ .esp) :
      (freed 72 u').gpr r = s.gpr r := by
    rw [freed_gpr _ _ hne, hcs r hr, F.keep r h1 h2 h3 hne]
  have randT : Spec.Rsa.bytesAt u'.mem (p.rp.setWidth 64) p.randLen = genRand o := by
    have := hi.bytes_frame (F.frame.trans frC)
    rw [hi.rR_eq] at this
    exact this.trans (by rw [hi.rp_eq, hi.randLen_eq])
  have memT : Frame [kR o, bR o, below (o.gpr .esp) 284] s.mem u'.mem := by
    refine Frame.trans (m₂ := u.mem) (hfr.sub fun r hr => ?_) (hf.sub fun r hr => ?_)
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨below (o.gpr .esp) 284, by simp, by rw [← hi.low_eq]; exact Fs⟩
    · rcases wcase r hr with hs | hs | ⟨hs, -⟩
      · exact ⟨kR o, by simp, hs⟩
      · exact ⟨bR o, by simp, hs⟩
      · exact ⟨below (o.gpr .esp) 284, by simp, by rw [← hi.low_eq]; exact hs⟩
  refine ⟨⟨⟨hi, ?_, ?_, sy'.trans F.syms, ?_, sv, F.frame.trans frC⟩, h.used_le,
    (keep .ebp (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.ebp,
    (keep .esi (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.esi,
    (keep .edi (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.edi, randT, stT⟩,
    keep .ebx (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [freed_gpr _ _ (by decide)]; exact hr, ?_, memT⟩
  · show u'.rd = o.rd
    rw [hrd, F.rd]
  · change u'.wr.tail = _
    rw [hwr, F.wr]; rfl
  · rw [freed_esp, hcs .esp (by decide), F.esp, BitVec.sub_add_cancel]
  · rw [show (freed 72 u').mem = u'.mem from rfl]
    rw [show keyOp p.L p.eB (Spec.Rsa.bytesAt s.mem (p.slot 4) p.L) (Spec.Rsa.bytesAt s.mem (p.slot 5) p.L) =
      keyOf p s.mem from rfl] at hout
    revert hout
    generalize keyOf p s.mem = k
    intro hout
    rcases k with (_ | ys) | _ <;> simpa [keyOutsOf] using hout


end VG.Proof.RsaKeyGen.X86.Generate
