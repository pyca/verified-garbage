module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.ABI
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # The search's public data and its loop states (i686)

The search's state is in the callee-saved registers (`esi`, `edi`, `ebp`,
`ebx`), which it saves in the frame it pushes, of 16 bytes below the stack
pointer; its memory moves only within what it may write (`changes`): its
outputs, its working space and the stack below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
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
  /-- RSA's table, which the candidate reads. -/
  tab : BitVec 32

def searchOfState (s : State) : SearchPublic where
  op := arg s 0
  up := arg s 2
  ep := arg s 3
  pp := arg s 5
  rp := arg s 7
  B := arg s 9
  stp := arg s 11
  sp := s.gpr .esp
  len := searchLen s
  elen := (arg s 4).toNat
  plen := (arg s 6).toNat
  randLen := (arg s 8).toNat
  words := (arg s 10).toNat
  remaining := searchRemaining s
  eB := searchE s
  tab := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol

def SearchInput (p : SearchPublic) (s : State) : Prop := contract.pre s ∧ searchOfState s = p

/-- The frame the search pushes. -/
abbrev SearchPublic.S1 (p : SearchPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 16

/-- The candidate's frame. -/
abbrev SearchPublic.S2 (p : SearchPublic) : BitVec 32 := p.sp - BitVec.ofNat 32 60

/-- The search from octet `used` of `rand`, with `remaining` counted
candidates left. -/
abbrev SearchPublic.tail (p : SearchPublic) (pB rand : List Byte) (used remaining : Nat) :
    PrimeSearchResult :=
  primeSearch p.len p.eB pB remaining (rand.drop used)

/-- The registers the search pushes, in order. -/
abbrev pushRegs : List Reg := [.ebx, .ebp, .esi, .edi]

/-- The regions the search (and its callee) may write, and its stack. -/
def changes (s : State) : List Region := [oR s, uR s, bR s, sR s, below (s.gpr .esp) 216]

/-- The precondition's facts of numbers, in terms of the public data. -/
structure PreFacts (p : SearchPublic) : Prop where
  room : 216 ≤ p.sp.toNat
  top : p.sp.toNat + 4 + 48 ≤ 2 ^ 32
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

theorem abi (h : SearchInput p s) : SearchABI s := searchABI_of h.1

theorem facts (h : SearchInput p s) : PreFacts p := by
  obtain ⟨h, rfl⟩ := h
  have A := searchABI_of h
  exact ⟨A.stackLow, A.stackBound, A.oBound, A.uBound, A.eBound, A.pBound, A.rBound, A.bBound, A.sBound,
    A.lenValid, A.eLow, A.eHigh, A.pLen, A.scratchLength, A.remaining, A.randLen⟩

theorem sp_eq (h : SearchInput p s) : p.sp = s.gpr .esp := by rw [← h.2]; rfl

theorem low_eq (h : SearchInput p s) : lowR s = below (s.gpr .esp) 216 := by
  change (⟨(s.gpr .esp).setWidth 64 - 216#64, 216⟩ : Region) = ⟨(s.gpr .esp - BitVec.ofNat 32 216).setWidth 64, 216⟩
  rw [Taint.sub_setWidth h.abi.stackLow]

/-- The regions the search only reads, and the arguments. -/
theorem read_disjoint (h : SearchInput p s) {r : Region}
    (hr : r = eR s ∨ r = pR s ∨ r = rR s ∨ r = aR s) : ∀ w ∈ changes s, r.Disjoint w := by
  have A := h.abi
  have L := h.low_eq
  intro w hw
  simp only [changes, ← L, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl | rfl
  exacts [A.oe.symm, A.ue.symm, A.eb, A.es, A.lowE.symm, A.op.symm, A.up.symm, A.pb, A.ps, A.lowP.symm,
    A.or_.symm, A.ur.symm, A.rb, A.rs, A.lowRand.symm, A.oa.symm, A.ua.symm, A.ba.symm, A.sa.symm,
    A.lowA.symm]

theorem bytes_frame (h : SearchInput p s) {r : Region} (hr : r = eR s ∨ r = pR s ∨ r = rR s)
    (hl : r.len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (h.read_disjoint (by rcases hr with h | h | h <;> simp [h])) hl (List.mem_range.mp hi)

/-- The arguments, through what the search may write. -/
theorem arg_frame (h : SearchInput p s) {m m' : Mem} (hf : Frame (changes s) m m') {i : Nat} (hi : i < 12) :
    m'.readW (argAddr s i) 32 = m.readW (argAddr s i) 32 := by
  have A := h.abi
  have hc : (aR s).Contains (argAddr s i) 4 := by
    have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
    have ai : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
    rw [ai, show aR s = ⟨argAddr s 0, 48⟩ from rfl, a0]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  exact hf.readW hc (h.read_disjoint (.inr (.inr (.inr rfl)))) (by decide)

end SearchInput

/-- The saved registers, in the frame at `S1`: `edi`, `esi`, `ebp` and
`ebx` from its base. -/
def Saved (m : Mem) (S1 : BitVec 32) (o : State) : Prop :=
  m.readW ((S1 + BitVec.ofNat 32 0).setWidth 64) 32 = o.gpr .edi ∧
    m.readW ((S1 + BitVec.ofNat 32 4).setWidth 64) 32 = o.gpr .esi ∧
    m.readW ((S1 + BitVec.ofNat 32 8).setWidth 64) 32 = o.gpr .ebp ∧
    m.readW ((S1 + BitVec.ofNat 32 12).setWidth 64) 32 = o.gpr .ebx

/-- The registers and memory every loop state has: the frame, and memory
that moved only within what may be written. -/
structure SearchBase (p : SearchPublic) (o : State) (s : State) : Prop where
  input : SearchInput p o
  rd : s.rd = o.rd
  wr : s.wr = below p.sp 16 :: o.wr
  syms : s.syms = o.syms
  sp : s.gpr .esp = p.S1
  saved : Saved s.mem p.S1 o
  frame : Frame (changes o) o.mem s.mem

/-- A state of the loop: `used` octets consumed, `remaining` counted
candidates left, the search going on. -/
structure SearchLive (p : SearchPublic) (o : State) (used remaining : Nat) (s : State) : Prop extends
    SearchBase p o s where
  used_le : used ≤ p.randLen
  remaining_le : remaining ≤ p.remaining
  esi : s.gpr .esi = BitVec.ofNat 32 used
  edi : s.gpr .edi = BitVec.ofNat 32 remaining
  ebx : s.gpr .ebx = 4

/-- A finished search, before `finish` stores its results. -/
structure SearchDone (p : SearchPublic) (o : State) (result : PrimeSearchResult) (s : State) : Prop extends
    SearchBase p o s where
  esi : s.gpr .esi = BitVec.ofNat 32 result.used
  edi : s.gpr .edi = BitVec.ofNat 32 result.remaining
  ebp : s.gpr .ebp = BitVec.ofNat 32 result.requested
  ebx : s.gpr .ebx = BitVec.ofNat 32 result.status
  output : Spec.Rsa.bytesAt s.mem (p.op.setWidth 64) p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0
  bounds : result.used ≤ p.randLen ∧ result.remaining ≤ p.remaining ∧ result.requested ≤ primeEntropy p.len

end VG.Proof.RsaKeyGen.X86.Search
