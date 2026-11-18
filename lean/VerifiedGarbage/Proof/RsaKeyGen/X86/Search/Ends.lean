module

public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Search
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Search
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.ABI
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.ABI
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `RsaKeyGen.X86.Search.Leaf`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.Search.Entry`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.Search.Data`, which only this module used -/

section

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
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega_using [this])
    have ai : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega_using [hi, this])
    rw [ai, show aR s = ⟨argAddr s 0, 48⟩ from rfl, a0]
    exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])
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
  ebp : s.gpr .ebp = BitVec.ofNat 32 (requested p.len result)
  ebx : s.gpr .ebx = BitVec.ofNat 32 result.status
  output : Spec.Rsa.bytesAt s.mem (p.op.setWidth 64) p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0
  bounds : result.used ≤ p.randLen ∧ result.remaining ≤ p.remaining ∧ (requested p.len result) ≤ primeEntropy p.len

end VG.Proof.RsaKeyGen.X86.Search

end

end

/-! # The search's push and entry (i686)

The push of the four callee-saved registers, which changes only the
search's stack and saves them (`push_base`); the arguments, which every loop
state reads at the same addresses (`SearchBase.arg_*`); and the entry, which
starts the loop with nothing consumed (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit)

/-- A block's run, with what it keeps: the registers but `rs`, the
regions and the statics. -/
theorem WP.blockKeep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hw : writesOnly rs (.block is) = true) :
    WP isa (.block is) s fun t => Q t ∧ Keep rs s t ∧ t.syms = s.syms :=
  WP.mono_syms (WP.keep rs h hw) fun _ ⟨q, k⟩ sy => ⟨q, k, sy⟩

namespace SearchInput

variable {p : SearchPublic} {o : State}

theorem len_valid (h : SearchInput p o) : 32 ≤ p.len ∧ p.len ≤ 512 := by
  have hv := h.facts.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv; exact ⟨hv.1, hv.2.1⟩

theorem remaining_le (h : SearchInput p o) : p.remaining ≤ 32768 := by
  have hr := h.facts.remaining
  have hv := h.len_valid
  unfold primeLimit at hr
  split at hr <;> omega_using [hv, hr]

end SearchInput

/-- The push changes only the search's stack. -/
theorem push_frame {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Frame (changes o) o.mem (pushed pushRegs o).mem := by
  have hroom : 216 ≤ (o.gpr .esp).toNat := h.abi.stackLow
  refine (pushed_frame (rs := pushRegs) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_using [hroom])).sub
    fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨below (o.gpr .esp) 216, by simp [changes], below_sub (by decide) hroom⟩

theorem push_saved {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Saved (pushed pushRegs o).mem p.S1 o := by
  have hroom : 216 ≤ (o.gpr .esp).toNat := h.abi.stackLow
  have hn : 4 * pushRegs.length ≤ (o.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_using [hroom]
  have hS : p.S1 = (pushed pushRegs o).gpr .esp := by rw [SearchPublic.S1, h.sp_eq, pushed_esp]; rfl
  have w (i : Nat) (hi : i < 4) := pushed_word (rs := pushRegs) (s := o) (by decide) hn hi
  rw [hS]
  exact ⟨w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide)⟩

theorem push_base {p : SearchPublic} {o : State} (h : SearchInput p o) : SearchBase p o (pushed pushRegs o) where
  input := h
  rd := pushed_rd _ _
  wr := by rw [pushed_wr, h.sp_eq]; rfl
  syms := pushRegs_syms _ _
  sp := by rw [pushed_esp, SearchPublic.S1, h.sp_eq]; rfl
  saved := push_saved h
  frame := push_frame h

namespace SearchBase

variable {p : SearchPublic} {o s : State}

/-- A state of the loop, through code that keeps `esp`, the regions, the
statics and the memory but in what the search may write. -/
theorem keep (hb : SearchBase p o s) {t : State} {rs : List Reg} (k : Keep rs s t) (hrs : .esp ∉ rs)
    (sy : t.syms = s.syms) (hs : Saved t.mem p.S1 o) (hf : Frame (changes o) s.mem t.mem) :
    SearchBase p o t :=
  ⟨hb.input, k.2.1.trans hb.rd, k.2.2.trans hb.wr, sy.trans hb.syms, (k.gpr hrs).trans hb.sp, hs,
    hb.frame.trans hf⟩

/-- The same, for code that keeps memory. -/
theorem step (hb : SearchBase p o s) {t : State} {rs : List Reg} (k : Keep rs s t) (hrs : .esp ∉ rs)
    (sy : t.syms = s.syms) (hm : t.mem = s.mem) : SearchBase p o t :=
  hb.keep k hrs sy (by rw [hm]; exact hb.saved) (by rw [hm]; exact Frame.refl _ _)

/-- The address of argument `i`, at displacement `d = 20 + 4 i` from `esp`. -/
theorem arg_ea (hb : SearchBase p o s) {i d : Nat} (hd : 20 + 4 * i = d) :
    (s.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = argAddr o i := by
  rw [hb.sp, SearchPublic.S1, hb.input.sp_eq, ← hd]
  unfold argAddr
  congr 1
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem arg_in (hb : SearchBase p o s) {i : Nat} (hi : i < 12) : InRegions (s.rd ++ s.wr) (argAddr o i) 4 := by
  have A := hb.input.abi
  have a0 : argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega_using [this])
  have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega_using [hi, this])
  refine ⟨aR o, ?_, ?_⟩
  · rw [hb.rd, hb.wr, A.wr]; simp
  · rw [ai, show aR o = ⟨argAddr o 0, 48⟩ from rfl, a0]
    exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

theorem arg_val (hb : SearchBase p o s) {i : Nat} (hi : i < 12) : s.mem.readW (argAddr o i) 32 = arg o i :=
  hb.input.arg_frame hb.frame hi

end SearchBase

theorem low_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) :
    m.readW a 32 = BitVec.ofNat 32 n := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega_using []

theorem param_eq (extra i : Nat) : param extra i = at_ .esp (4 + 4 * i + 4 * (pushWords + extra)) := rfl

theorem entry_ok {p : SearchPublic} {o : State} (h : SearchInput p o) :
    WP isa (.block entry) (pushed pushRegs o) (SearchLive p o 0 p.remaining) := by
  have hb := push_base h
  have A := h.abi
  have hst : p.stp = arg o 11 := by rw [← h.2]; rfl
  have r11 := hb.arg_in (i := 11) (by decide)
  have v11 := hb.arg_val (i := 11) (by decide)
  have e11 := hb.arg_ea (i := 11) (d := 64) rfl
  have cs : (sR o).Contains ((arg o 11).setWidth 64) 4 := by
    simpa using Offset.contains_base ((arg o 11).setWidth 64) (d := 0) (n := 4) (k := 32) (by decide) (by decide)
  have rs : InRegions ((pushed pushRegs o).rd ++ (pushed pushRegs o).wr) ((arg o 11).setWidth 64) 4 := by
    refine ⟨sR o, ?_, cs⟩
    rw [hb.rd, hb.wr, A.wr]; simp
  have vs : (pushed pushRegs o).mem.readW ((arg o 11).setWidth 64) 32 = BitVec.ofNat 32 p.remaining := by
    have hd : (sR o).Disjoint (below (o.gpr .esp) 16) :=
      A.lowS.symm.sub_right (by rw [h.low_eq]; exact below_sub (by decide) A.stackLow)
    have e := (pushed_frame (rs := pushRegs) (s := o) (by decide)
      (by simp only [List.length_cons, List.length_nil]; have := A.stackLow; simp only [stack] at this; omega_using [this])).readW (r := sR o)
      (a := (arg o 11).setWidth 64) (w := 32) cs (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact hd) (by decide)
    rw [e]
    have hw : o.mem.readW ((arg o 11).setWidth 64) 64 = BitVec.ofNat 64 p.remaining := by
      rw [← h.2]; change o.mem.readW (sR o).base 64 = BitVec.ofNat 64 (searchRemaining o)
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact low_half hw
  have e0 : (arg o 11 + BitVec.ofNat 32 0).setWidth 64 = (arg o 11).setWidth 64 := by rw [BitVec.add_zero]
  refine WP.mono (WP.blockKeep [.eax, .ebx, .ebp, .esi, .edi] (Q := fun t =>
      t.gpr .esi = 0 ∧ t.gpr .edi = BitVec.ofNat 32 p.remaining ∧ t.gpr .ebx = 4 ∧
      t.mem = (pushed pushRegs o).mem) ?_ (by rfl)) fun t ⟨⟨hsi, hdi, hbx, hm⟩, k, sy⟩ => ?_
  · simp only [entry, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, e11, r11, v11, e0, rs, vs]
  · exact ⟨hb.step k (by decide) sy hm, Nat.zero_le _, Nat.le_refl _, hsi, hdi, hbx⟩

end VG.Proof.RsaKeyGen.X86.Search

end

end

/-! # Zeros at `out` (i686)

`zeroOut` writes `out_len` zeros at `out` and changes nothing else but the
scratch registers (`zeroOut_ok`), with the loop of FFDH's controller
(`Proof/Ffdh/X86/KeySearch/Zero.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86 (Keeps)
open VG.Proof.Ffdh.X86.KeySearch (ZInv zeroStep_ok)

theorem Keep.ofKeeps {rs : List Reg} {s t : State} (h : Keeps rs s t) : Keep rs s t := ⟨h.1, h.2.1, h.2.2⟩

theorem zeroOut_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa zeroOut s fun u => (Frame [oR o] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (p.op.setWidth 64) p.len = List.replicate p.len 0) ∧
        Keep [.eax, .ecx, .edx] s u ∧ u.syms = s.syms := by
  have A := hb.input.abi
  have hv := hb.input.len_valid
  have hop : p.op = arg o 0 := by rw [← hb.input.2]; rfl
  have hlen : BitVec.ofNat 32 p.len = arg o 1 := by
    rw [← hb.input.2]; change BitVec.ofNat 32 (arg o 1).toNat = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hpl : p.len = (arg o 1).toNat := by rw [← hb.input.2]; rfl
  have hR : (⟨(arg o 0).setWidth 64, p.len⟩ : Region) ∈ s.wr := by
    rw [hb.wr, A.wr, hpl]; simp
  have hbnd : (arg o 0).toNat + p.len ≤ 2 ^ 32 := by rw [← hb.input.2]; exact A.oBound
  refine WP.mono_syms (Q := fun u => (Frame [oR o] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (p.op.setWidth 64) p.len = List.replicate p.len 0) ∧
        Keep [.eax, .ecx, .edx] s u) ?_ fun u h sy => ⟨h.1, h.2, sy⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.eax, .ecx, .edx] (Q := fun t => t.gpr .edx = arg o 0 ∧
      t.gpr .ecx = arg o 1 ∧ t.gpr .eax = 0 ∧ t.mem = s.mem) ?_ (by rfl)) fun t ⟨⟨hd, hc, ha, hm⟩, k⟩ => ?_)
  · simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 0) (d := 20) rfl, hb.arg_ea (i := 1) (d := 24) rfl,
      hb.arg_in (i := 0) (by decide), hb.arg_in (i := 1) (by decide), hb.arg_val (i := 0) (by decide),
      hb.arg_val (i := 1) (by decide)]
  have I₀ : ZInv t (arg o 0) p.len 0 t := ⟨by rw [hd, BitVec.add_zero], by rw [hc, Nat.sub_zero, hlen], ha,
    Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), Keeps.refl _ _⟩
  have hRt : (⟨(arg o 0).setWidth 64, p.len⟩ : Region) ∈ t.wr := by rw [k.2.2]; exact hR
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = p.len - k ∧ k < p.len ∧ ZInv t (arg o 0) p.len k u)
    (fun j u hu => ?_) _ t ⟨0, rfl, by omega_using [hv], I₀⟩
  obtain ⟨i, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok hRt hbnd (by omega_using [hv]) hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : p.len - (i + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], ⟨?_, ?_⟩, ?_⟩
    · have f := J.frame
      rw [hm] at f
      rw [show oR o = ⟨(arg o 0).setWidth 64, p.len⟩ by rw [← hb.input.2]; rfl]
      exact f
    · rw [hop]
      apply List.ext_getElem
      · simp [Spec.Rsa.bytesAt]
      · intro j h₁ _
        simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
        simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
        exact J.zero j (by omega_using [he, h₁])
    · exact (k.trans (Keep.ofKeeps J.keeps)).mono (by simp)
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega_using [hk],
      i + 1, rfl, by omega_using [he], J⟩

end VG.Proof.RsaKeyGen.X86.Search

end

end

-- separate module: the search's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # How the search ends (i686)

The terminal states (`exhausted_ok`, `accept_ok`), and the request for more
of the tape (`request_ok`, `short_ok`), whose larger and smaller values are
chosen by masks of the borrows (`select_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit)

/-- Writes to `out` keep the frame and what the search may write. -/
theorem out_changes {o : State} {m m' : Mem} (h : Frame [oR o] m m') : Frame (changes o) m m' :=
  h.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨oR o, by simp [changes], fun _ h => h⟩

theorem frame_apart {p : SearchPublic} {o : State} (h : SearchInput p o) {r : Region}
    (hd : (lowR o).Disjoint r) {m m' : Mem} (hf : Frame [r] m m') (hs : Saved m p.S1 o) : Saved m' p.S1 o := by
  have A := h.abi
  have hS : p.S1 = o.gpr .esp - BitVec.ofNat 32 16 := by rw [SearchPublic.S1, h.sp_eq]
  have sub : Region.Sub (below (o.gpr .esp) 16) (lowR o) := by
    rw [h.low_eq]; exact below_sub (by decide) A.stackLow
  have wd (k : Nat) (hk : k < 4) : (below (o.gpr .esp) 16).Contains ((p.S1 + BitVec.ofNat 32 (4 * k)).setWidth 64) 4 := by
    rw [hS]
    have e : (o.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * k)).setWidth 64 =
        (o.gpr .esp - BitVec.ofNat 32 16).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
      VG.Proof.MlKem.X86.ea_off (by rw [sub_toNat (by have := A.stackLow; simp only [stack] at this; omega_using [this])]; have := A.stackBound; omega_using [hk])
    rw [e]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  have keep (k : Nat) (hk : k < 4) := hf.readW (w := 32) (wd k hk) (fun r' hr' => by
    obtain rfl := List.mem_singleton.mp hr'; exact fun x h₁ h₂ => hd x (sub x h₁) h₂) (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := hs
  exact ⟨(keep 0 (by decide)).trans h0, (keep 1 (by decide)).trans h1, (keep 2 (by decide)).trans h2,
    (keep 3 (by decide)).trans h3⟩

theorem terminal_ok (s : State) (status : Nat) :
    WP isa (.block (terminal status)) s fun t =>
      (t.gpr .edi = 0 ∧ t.gpr .ebp = 0 ∧ t.gpr .ebx = BitVec.ofNat 32 status ∧ t.mem = s.mem) ∧
        Keep [.edi, .ebp, .ebx] s t ∧ t.syms = s.syms := by
  refine WP.blockKeep _ ?_ (by rfl)
  unfold terminal
  xrun

/-- Exhausted: zeros at `out`, after `used` octets. -/
theorem exhausted_ok {p : SearchPublic} {o s : State} {used : Nat} (h : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hu : used ≤ p.randLen) (tr : List Nat) :
    WP isa exhausted s (SearchDone p o ⟨.exhausted, used, tr⟩) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_ok s 3) fun u ⟨⟨h9, h10, h11, hm⟩, k, sy⟩ => ?_)
  have hb := h.step k (by decide) sy hm
  refine WP.mono (zeroOut_ok hb) fun t ⟨⟨hf, hz⟩, kt, syt⟩ => ?_
  have A := h.input.abi
  exact ⟨hb.keep kt (by decide) syt (frame_apart h.input A.lowO hf hb.saved) (out_changes hf),
    (kt.gpr (by decide)).trans ((k.gpr (by decide)).trans hsi), (kt.gpr (by decide)).trans h9,
    (kt.gpr (by decide)).trans h10, (kt.gpr (by decide)).trans h11, hz, hu, Nat.zero_le _, Nat.zero_le _⟩

theorem add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- The prime, after `used + n` octets. -/
theorem accept_ok {p : SearchPublic} {o s : State} {used n c : Nat} (h : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hu : used + n ≤ p.randLen)
    (hout : Spec.Rsa.bytesAt s.mem (p.op.setWidth 64) p.len = Spec.Rsa.i2osp c p.len) (tr : List Nat) :
    WP isa (.block accept) s (SearchDone p o ⟨.accepted c, used + n, tr⟩) := by
  refine WP.mono (WP.blockKeep [.esi, .edi, .ebp, .ebx] (Q := fun t => t.gpr .esi = BitVec.ofNat 32 (used + n) ∧
    t.gpr .edi = 0 ∧ t.gpr .ebp = 0 ∧ t.gpr .ebx = 1 ∧ t.mem = s.mem) ?_ (by rfl))
    fun t ⟨⟨h8', h9, h10, h11, hm⟩, k, sy⟩ => ⟨h.step k (by decide) sy hm, h8', h9, h10, h11,
      by rw [hm]; exact hout, hu, Nat.zero_le _, Nat.zero_le _⟩
  unfold accept terminal
  xrun [hsi, hc, add_ofNat32]

/-! ## Asking for more -/

theorem toNat_small32 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `a`, or `b` where the borrow `c` is set: the mask of `sbb r, r`. -/
theorem select_mask (a b : BitVec 32) (c : Bool) :
    a ^^^ ((b ^^^ a) &&& (0#32 - BitVec.setWidth 32 (BitVec.ofBool c))) = if c then b else a := by
  cases c
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false)) = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · simp only [ite_true]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true)) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem double32 (a : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 a = BitVec.ofNat 32 (2 * a) := by
  rw [add_ofNat32, Nat.two_mul]

/-- The next tape's length, from `left` octets of the tape and the budget in
`ebp`. -/
theorem request_ok {p : SearchPublic} {o s : State} {left : Nat} (h : SearchBase p o s)
    (hleft : left ≤ 32769 * p.len)
    (hax : s.gpr .eax = BitVec.ofNat 32 left) (hbp : s.gpr .ebp = BitVec.ofNat 32 (32769 * p.len)) :
    WP isa (.block request) s fun t =>
      (t.gpr .ebp = BitVec.ofNat 32 (primeRequest p.len left) ∧ t.gpr .ebx = 0 ∧ t.mem = s.mem) ∧
        Keep [.eax, .ecx, .edx, .ebp, .ebx] s t ∧ t.syms = s.syms := by
  have hv := h.input.len_valid
  have hL : arg o 1 = BitVec.ofNat 32 p.len := by
    rw [← h.input.2]; change arg o 1 = BitVec.ofNat 32 (arg o 1).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.blockKeep _ ?_ (by rfl)
  simp only [request, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, h.arg_ea (i := 1) (d := 24) rfl, h.arg_in (i := 1) (by decide),
    h.arg_val (i := 1) (by decide), hL, hax, hbp, double32, select_mask]
  have e16 : 2 * (2 * (2 * (2 * p.len))) = 16 * p.len := by omega_using []
  rw [e16, toNat_small32 (show left < 2 ^ 32 by omega_using [hleft, hv]), toNat_small32 (show 16 * p.len < 2 ^ 32 by omega_using [hv]),
    toNat_small32 (show 32769 * p.len < 2 ^ 32 by omega_using [hv])]
  have hm : (if decide (left < 16 * p.len) = true then BitVec.ofNat 32 (16 * p.len) else BitVec.ofNat 32 left) =
      BitVec.ofNat 32 (max left (16 * p.len)) := by
    by_cases hl : left < 16 * p.len
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hl))]; congr 1; omega_using [hl]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hl))]; congr 1; omega_using [hl]
  rw [hm, double32, toNat_small32 (show 2 * max left (16 * p.len) < 2 ^ 32 by omega_using [hleft, hv])]
  unfold primeRequest Entropy.request primeEntropy
  by_cases hc : 32769 * p.len < 2 * max left (16 * p.len)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hc))]; congr 1; omega_using [hc]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hc))]; congr 1; omega_using [hc]

theorem sub_eq_beq {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0) = decide (a = c) := by
  by_cases e : a = c
  · subst e; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
  · rw [decide_eq_false e]
    refine beq_eq_false_iff_ne.mpr fun h => e ?_
    have h'' : BitVec.ofNat 32 a = BitVec.ofNat 32 c := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 a) (BitVec.ofNat 32 c), h]
      exact BitVec.zero_add _
    have := congrArg BitVec.toNat h''
    rwa [toNat_small32 ha, toNat_small32 hc] at this

theorem SearchInput.len_arg {p : SearchPublic} {o : State} (h : SearchInput p o) :
    arg o 1 = BitVec.ofNat 32 p.len := by
  rw [← h.2]; change arg o 1 = BitVec.ofNat 32 (arg o 1).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem SearchInput.randLen_arg {p : SearchPublic} {o : State} (h : SearchInput p o) :
    arg o 8 = BitVec.ofNat 32 p.randLen := by
  rw [← h.2]; change arg o 8 = BitVec.ofNat 32 (arg o 8).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The tape ended inside a candidate, after `used` octets, with `k`
counted candidates left: exhausted if it had the whole budget, else a
request for more. -/
theorem short_ok {p : SearchPublic} {o s : State} {used k : Nat} (h : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hdi : s.gpr .edi = BitVec.ofNat 32 k) (hu : used ≤ p.randLen)
    (hk : k ≤ p.remaining)
    (hout : Spec.Rsa.bytesAt s.mem (p.op.setWidth 64) p.len = List.replicate p.len 0) (tr : List Nat) :
    WP isa short s (SearchDone p o (if primeEntropy p.len ≤ p.randLen - used then ⟨.exhausted, used, tr⟩
      else ⟨.entropy k (p.randLen - used), used, tr⟩)) := by
  have hi := h.input
  have f := hi.facts
  have hv := hi.len_valid
  have rl := f.randLen
  unfold primeEntropy at rl
  unfold short
  refine WP.seq (WP.mono (WP.blockKeep [.eax, .ecx, .edx, .ebp]
    (Q := fun t => t.gpr .eax = BitVec.ofNat 32 (p.randLen - used) ∧ t.gpr .ebp = BitVec.ofNat 32 (32769 * p.len) ∧
      t.zf = some (decide (p.randLen - used = 32769 * p.len)) ∧ t.mem = s.mem) ?_ (by rfl))
    fun u ⟨⟨h0, h1, he, hm⟩, k', sy⟩ => ?_)
  · simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, h.arg_ea (i := 1) (d := 24) rfl, h.arg_ea (i := 8) (d := 52) rfl,
      h.arg_in (i := 1) (by decide), h.arg_in (i := 8) (by decide), h.arg_val (i := 1) (by decide),
      h.arg_val (i := 8) (by decide), hi.len_arg, hi.randLen_arg, hsi, execMul,
      show (32769 : BitVec 32).toNat = 32769 from rfl, toNat_small32 (show p.len < 2 ^ 32 by omega_using [hv]),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega_using [hu, hv, rl]) hu]
    rw [sub_eq_beq (by omega_using [hv, rl]) (by omega_using [hv]), Nat.mul_comm]
  have hu' := h.step k' (by decide) sy hm
  have hsi' : u.gpr .esi = BitVec.ofNat 32 used := (k'.gpr (by decide)).trans hsi
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    rw [ite_eq_left_of_eq_true _ _ (by unfold primeEntropy; exact eq_true (by omega_using [hz]))]
    exact exhausted_ok hu' hsi' hu tr
  · have hz := of_decide_eq_false hz
    rw [ite_eq_right_of_eq_false _ _ (by unfold primeEntropy; exact eq_false (by omega_using [rl, hz]))]
    refine WP.mono (request_ok hu' (by omega_using [rl]) h0 h1)
      fun t ⟨⟨h10, h11, hmt⟩, kt, syt⟩ => ⟨hu'.step kt (by decide) syt hmt, (kt.gpr (by decide)).trans hsi',
        (kt.gpr (by decide)).trans ((k'.gpr (by decide)).trans hdi), h10, h11,
        by rw [hmt, hm]; exact hout, hu, hk, by
          show primeRequest p.len (p.randLen - used) ≤ _
          unfold primeRequest Entropy.request; exact Nat.min_le_right _ _⟩

end VG.Proof.RsaKeyGen.X86.Search
