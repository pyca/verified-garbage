module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

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

/-- The search from octet `used` of `rand`, with `remaining` counted
candidates left. -/
abbrev SearchPublic.tail (p : SearchPublic) (pB rand : List Byte) (used remaining : Nat) :
    PrimeSearchResult :=
  primeSearch p.len p.eB pB remaining (rand.drop used)

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

theorem pre (h : SearchInput p s) : searchPre s := h.1

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
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [inE, inP, inRand, inArgs] <;> omega

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
      exact VG.Arm.addr_add (by omega)
    rw [e]
    exact Offset.contains_base _ (by omega) (by omega)
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
  r10 : s.gpr .r10 = BitVec.ofNat 32 result.requested
  r11 : s.gpr .r11 = BitVec.ofNat 32 result.status
  output : Spec.Rsa.bytesAt s.mem (State.addr p.op) p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0

end VG.Proof.RsaKeyGen.Arm.Search
