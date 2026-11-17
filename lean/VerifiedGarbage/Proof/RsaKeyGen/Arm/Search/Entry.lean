module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Search
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! ### `RsaKeyGen.Arm.Search.Data`, which this module and modules that import it used -/

section

/-! # The search's public data and its loop states (ARMv7)

The search's state is in the callee-saved registers (`r4`–`r11`), which it
saves in the frame it pushes, of 40 bytes at `sp - 40`; its memory moves
only within what it may write (`changes`): its outputs, its working space
and the stack below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

/-- What the search's timing may depend on, and the arguments. -/
structure SearchPublic where
  op : BitVec 32
  up : BitVec 32
  ep : BitVec 32
  pp : BitVec 32
  rp : BitVec 32
  B : BitVec 32
  stp : BitVec 32
  sp : BitVec 32
  len : Nat
  elen : Nat
  plen : Nat
  randLen : Nat
  words : Nat
  remaining : Nat
  eB : List Byte

def searchOfState (s : State) : SearchPublic where
  op := s.gpr .r0
  up := s.gpr .r2
  ep := s.gpr .r3
  pp := stackArg s 1
  rp := stackArg s 3
  B := stackArg s 5
  stp := stackArg s 7
  sp := s.sp
  len := searchLen s
  elen := (stackArg s 0).toNat
  plen := (stackArg s 2).toNat
  randLen := (stackArg s 4).toNat
  words := (stackArg s 6).toNat
  remaining := searchRemaining s
  eB := searchE s

def SearchInput (p : SearchPublic) (s : State) : Prop := searchPre s ∧ searchOfState s = p

/-- The frame the search pushes. -/
abbrev SearchPublic.S1 (p : SearchPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 40

/-- The candidate's frame. -/
abbrev SearchPublic.S2 (p : SearchPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 72

/-- The registers the search pushes, in order. -/
abbrev pushRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The regions the search (and its callee) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [inStack s]

/-- The precondition's facts of numbers, in terms of the public data. -/
structure PreFacts (p : SearchPublic) : Prop where
  room : 184 ≤ p.sp.toNat
  top : p.sp.toNat + 32 ≤ 2 ^ 32
  nO : p.op.toNat + p.len ≤ 2 ^ 32
  nU : p.up.toNat + 8 ≤ 2 ^ 32
  nE : p.ep.toNat + p.elen ≤ 2 ^ 32
  nP : p.pp.toNat + p.plen ≤ 2 ^ 32
  nR : p.rp.toNat + p.randLen ≤ 2 ^ 32
  nS : p.B.toNat + p.words * 8 ≤ 2 ^ 32
  nT : p.stp.toNat + 32 ≤ 2 ^ 32
  valid : Spec.RsaKeyGen.primeLenValid p.len
  e1 : 1 ≤ p.elen
  e8 : p.elen ≤ 8
  plen : p.plen = 0 ∨ p.plen = p.len
  scr : Spec.Rsa.scratchWords p.len ≤ p.words
  remaining : p.remaining ≤ Spec.RsaKeyGen.primeLimit (8 * p.len) (Spec.Rsa.os2ip p.eB)
  randLen : p.randLen ≤ primeEntropy p.len

namespace SearchInput

variable {p : SearchPublic} {s : State}

theorem facts (h : SearchInput p s) : PreFacts p := by
  obtain ⟨⟨room, top, -, -, -, -, -, nO, nU, nE, nP, nR, nS, nT, valid, e1, e8, plen, scr, rem, -, -, rl⟩, rfl⟩ := h
  exact ⟨room, top, nO, nU, nE, nP, nR, nS, nT, valid, e1, e8, plen, scr, rem, rl⟩

theorem sp_eq (h : SearchInput p s) : p.sp = s.sp := by rw [← h.2]; rfl

theorem room (h : SearchInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.1

theorem top (h : SearchInput p s) : p.sp.toNat + 32 ≤ 2 ^ 32 := by rw [h.sp_eq]; exact h.1.2.1

theorem rd (h : SearchInput p s) : s.rd = inReads s := h.1.2.2.1

theorem wr (h : SearchInput p s) : s.wr = inWrites s := h.1.2.2.2.1

theorem writes_pairwise (h : SearchInput p s) : (inWrites s).Pairwise Region.Disjoint := h.1.2.2.2.2.1

theorem write_disjoint (h : SearchInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : SearchInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (inStack s).Disjoint r := h.1.2.2.2.2.2.2.1 r hr

theorem read_disjoint (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).symm

theorem reads_len (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) : r.len ≤ 2 ^ 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfe, hfp, hfr, -, -, -⟩ := h.1
  simp only [inReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [inE, inP, inRand, inArgs] <;> omega_using []

theorem bytes_frame (h : SearchInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (h.read_disjoint hr) (h.reads_len hr) (List.mem_range.mp hi)

theorem random_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.rp) p.randLen = Spec.Rsa.bytesAt m (State.addr p.rp) p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

theorem e_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.ep) p.elen = Spec.Rsa.bytesAt m (State.addr p.ep) p.elen := by
  rw [← h.2]
  exact h.bytes_frame (r := inE s) (by simp [inReads]) hf

theorem p_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.pp) p.plen = Spec.Rsa.bytesAt m (State.addr p.pp) p.plen := by
  rw [← h.2]
  exact h.bytes_frame (r := inP s) (by simp [inReads]) hf

/-- The stack arguments, through what the search may write. -/
theorem arg_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') {j : Nat} (hj : j < 8) :
    m'.readW (stackArgAddr s j) 32 = m.readW (stackArgAddr s j) 32 := by
  have hsp := h.1.2.1
  have hc : (inArgs s).Contains (stackArgAddr s j) 4 := by
    have e : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (4 * j) := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega_using [hj, hsp])
    rw [e]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  exact hf.readW hc (h.read_disjoint (by simp [inReads])) (by decide)

end SearchInput

/-- Where the pushed registers are, from `S1`. -/
abbrev slots : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.r12, 32), (.lr, 36)]

/-- The saved registers, in the frame at `S1`. -/
def Saved (m : Mem) (S1 : BitVec 32) (o : State) : Prop := Spill.Saved m (State.addr S1) o.gpr slots

/-- The registers and memory every loop state has: the arguments in
`r4`–`r7`, the frame, and memory that moved only within what may be
written. -/
structure SearchBase (p : SearchPublic) (o : State) (s : State) : Prop where
  input : SearchInput p o
  rd : s.rd = o.rd
  wr : s.wr = ⟨State.addr p.S1, 40⟩ :: o.wr
  sp : s.sp = p.S1
  r4 : s.gpr .r4 = p.op
  r5 : s.gpr .r5 = BitVec.ofNat 32 p.len
  r6 : s.gpr .r6 = p.up
  r7 : s.gpr .r7 = p.ep
  saved : Saved s.mem p.S1 o
  frame : Frame (changes o) o.mem s.mem

/-- A state of the loop: `used` octets consumed, `remaining` counted
candidates left, the search going on. -/
structure SearchLive (p : SearchPublic) (o : State) (used remaining : Nat) (s : State) : Prop extends
    SearchBase p o s where
  used_le : used ≤ p.randLen
  remaining_le : remaining ≤ p.remaining
  r8 : s.gpr .r8 = BitVec.ofNat 32 used
  r9 : s.gpr .r9 = BitVec.ofNat 32 remaining
  r11 : s.gpr .r11 = 4

/-- A finished search, before `finish` stores its results. -/
structure SearchDone (p : SearchPublic) (o : State) (result : PrimeSearchResult) (s : State) : Prop extends
    SearchBase p o s where
  r8 : s.gpr .r8 = BitVec.ofNat 32 result.used
  r9 : s.gpr .r9 = BitVec.ofNat 32 result.remaining
  r10 : s.gpr .r10 = BitVec.ofNat 32 (requested p.len result)
  r11 : s.gpr .r11 = BitVec.ofNat 32 result.status
  output : Spec.Rsa.bytesAt s.mem (State.addr p.op) p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0
  bounds : result.used ≤ p.randLen ∧ result.remaining ≤ p.remaining ∧ (requested p.len result) ≤ primeEntropy p.len

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # The search's entry (ARMv7): the push, and the loop's first state -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit)

namespace SearchInput

variable {p : SearchPublic} {o : State}

theorem len_valid (h : SearchInput p o) : 32 ≤ p.len ∧ p.len ≤ 512 := by
  have hv := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← h.2]; unfold Spec.RsaKeyGen.primeLenValid at hv; exact ⟨hv.1, hv.2.1⟩

theorem remaining_le (h : SearchInput p o) : p.remaining ≤ 32768 := by
  have hr := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv := h.len_valid
  rw [← h.2] at hv ⊢
  unfold primeLimit at hr
  change searchRemaining o ≤ 32768
  split at hr <;> simp only [searchOfState] at hv <;> omega_using [hv, hr]

/-- The `n` bytes `a` below the stack pointer are in the search's stack. -/
theorem stack_sub (_h : SearchInput p o) {a n : Nat} (ha : a ≤ stackUse) (hn : stackUse - a + n ≤ stackUse) :
    Region.Sub ⟨State.addr o.sp - BitVec.ofNat 64 a, n⟩ (inStack o) :=
  Offset.sub_below _ ha hn

end SearchInput

theorem sub_add_ofNat (x : BitVec 32) (k d : Nat) :
    x - BitVec.ofNat 32 k + BitVec.ofNat 32 (k + d) = x + BitVec.ofNat 32 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The push changes only the search's stack. -/
theorem push_frame {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Frame (changes o) o.mem (pushed pushRegs o).mem := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  refine (FrameStack.pushed_frameA (rs := pushRegs) hroom).sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨inStack o, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
  rw [FrameStack.addr_sub' hroom]
  exact h.stack_sub (by decide) (by decide)

theorem push_saved {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Saved (pushed pushRegs o).mem p.S1 o := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have top := h.1.2.1
  let sp := o.sp - BitVec.ofNat 32 40
  have bound : sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [show sp = o.sp - BitVec.ofNat 32 40 from rfl, FrameStack.sub_toNat' hroom]; omega_using []
  have address (k : Nat) (hk : k < 40) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    VG.Arm.addr_add (by omega_using [bound, hk])
  have memEq : (pushed pushRegs o).mem = Spill.saveMem o.mem (State.addr sp) o.gpr slots := by
    change storeWords o.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide), address 16 (by decide),
      address 20 (by decide), address 24 (by decide), address 28 (by decide), address 32 (by decide),
      address 36 (by decide)]
    simp only [off, BitVec.add_zero]
  have hS : p.S1 = sp := by rw [SearchPublic.S1, h.sp_eq]
  unfold Saved
  rw [memEq, hS]
  exact Spill.saveMem_saved (lo := 0) (hi := 40) (State.addr sp) o.gpr o.mem slots (by decide)

theorem low_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) :
    m.readW a 32 = BitVec.ofNat 32 n := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega_using []

theorem entry_ok {p : SearchPublic} {o : State} (h : SearchInput p o) :
    WP isa (.block entry) (pushed pushRegs o) (SearchLive p o 0 p.remaining) := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have top := h.1.2.1
  have hf := push_frame h
  have hS : p.S1 = o.sp - BitVec.ofNat 32 40 := by rw [SearchPublic.S1, h.sp_eq]
  -- the state pointer, a stack argument
  have a68 : State.addr (o.sp - BitVec.ofNat 32 40 + BitVec.ofNat 32 68) = stackArgAddr o 7 := by
    rw [show (68 : Nat) = 40 + 4 * 7 from rfl, sub_add_ofNat]; rfl
  have r68 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (stackArgAddr o 7) 4 := by
    refine ⟨inArgs o, List.mem_append_left _ (by rw [h.rd]; simp [inReads]), ?_⟩
    have e : stackArgAddr o 7 = stackArgAddr o 0 + BitVec.ofNat 64 28 := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega_using [top])
    rw [e]; exact Offset.contains_base _ (by decide) (by decide)
  have v68 : (pushed pushRegs o).mem.readW (stackArgAddr o 7) 32 = p.stp := by
    rw [h.arg_frame hf (by decide), ← h.2]; rfl
  -- the low half of the state's first word
  have hst : (inState o).Disjoint (FrameStack.belowA o.sp 40) := by
    have hd := h.stack_disjoint (r := inState o) (by simp [inWrites])
    refine fun x hx hy => hd x ?_ hx
    have hsub : Region.Sub (FrameStack.belowA o.sp 40) (inStack o) := by
      change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
      rw [FrameStack.addr_sub' hroom]; exact h.stack_sub (by decide) (by decide)
    exact hsub x hy
  have stp : inState o = ⟨State.addr p.stp, 32⟩ := by rw [← h.2]; rfl
  have nstp : p.stp.toNat + 32 ≤ 2 ^ 32 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have a0 : State.addr (p.stp + BitVec.ofNat 32 0) = State.addr p.stp := by rw [BitVec.add_zero]
  have r0 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (State.addr p.stp) 4 := by
    refine ⟨inState o, List.mem_append_right _ (by rw [h.wr]; simp [inWrites]), ?_⟩
    rw [stp]
    simpa using Offset.contains_base (State.addr p.stp) (d := 0) (n := 4) (k := 32) (by decide) (by decide)
  have v0 : (pushed pushRegs o).mem.readW (State.addr p.stp) 32 = BitVec.ofNat 32 p.remaining := by
    have hpf := FrameStack.pushed_frameA (rs := pushRegs) hroom
    have e := hpf.readW (r := inState o) (a := State.addr p.stp) (w := 32)
      (by rw [stp]; simpa using Offset.contains_base (State.addr p.stp) (d := 0) (n := 4) (k := 32) (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hst) (by decide)
    rw [e]
    have hw : o.mem.readW (State.addr p.stp) 64 = BitVec.ofNat 64 p.remaining := by
      rw [← h.2]; change o.mem.readW (State.addr (stackArg o 7)) 64 = BitVec.ofNat 64 (searchRemaining o)
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact low_half hw
  refine WP.mono (withRest_all [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] (Q := fun t =>
      t.gpr .r4 = o.gpr .r0 ∧ t.gpr .r5 = o.gpr .r1 ∧ t.gpr .r6 = o.gpr .r2 ∧ t.gpr .r7 = o.gpr .r3 ∧
      t.gpr .r8 = 0 ∧ t.gpr .r9 = BitVec.ofNat 32 p.remaining ∧ t.gpr .r11 = 4 ∧
      t.mem = (pushed pushRegs o).mem) ?_ (by rfl) (by rfl)) fun t ⟨⟨h4, h5, h6, h7, h8, h9, h11, hm⟩, k⟩ => ?_
  · unfold entry arg pushBytes
    -- reads through the writes before their branches: as post-rewrites `simp` visits each discarded branch
    ffrun [↓RegUpd.gpr_setReg, ↓reduceIte, pushed_gpr, pushed_sp, pushed_rd, pushed_wr, a68, r68, v68, a0, r0, v0,
      show 4 * pushRegs.length = 40 from rfl]
  · have hlen : (o.gpr .r1) = BitVec.ofNat 32 p.len := by
      rw [← h.2]; change o.gpr .r1 = BitVec.ofNat 32 (o.gpr .r1).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Nat.zero_le _, Nat.le_refl _, h8, h9, h11⟩
    · rw [k.rd]; rfl
    · rw [k.wr, pushed_wr, hS]; rfl
    · rw [k.sp, pushed_sp, hS]; rfl
    · rw [h4, ← h.2]; rfl
    · rw [h5, hlen]
    · rw [h6, ← h.2]; rfl
    · rw [h7, ← h.2]; rfl
    · rw [hm]; exact push_saved h
    · rw [hm]; exact hf

end VG.Proof.RsaKeyGen.Arm.Search
