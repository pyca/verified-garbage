module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Data
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ffdh.X86_64.Cached.SearchProof.CallPre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Cached.SearchProof.Entry`, which this module and modules that import it used -/

section

/-! # The key-generation controller's entry -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame writeController_word
  writeController_append controllerValue)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

def headValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r12), (5, s.gpr .rdi), (6, s.gpr .rdx), (15, s.gpr .r8), (7, s.gpr .r9)]

def tailValues (s : State) : List (Nat × BitVec 64) :=
  [(8, stackArg s 0), (9, stackArg s 2), (10, stackArg s 3), (12, stackArg s 4),
    (13, stackArg s 5), (11, 0)]

def entryValues (s : State) : List (Nat × BitVec 64) := headValues s ++ tailValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, headValues, tailValues, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem arg_contains (s : State) {j : Nat} (hj : j < 9) :
    (inArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega_using [hj]]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) :
    ∀ j < 9, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inArgs s, ?_, arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (by simp [inReads])

theorem entry_head_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entryHead) s fun t =>
      t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (headValues s) ∧
      Keep [.rax, .r12] s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 56) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 56) 8 := input_args h 6 (by decide)
  refine WP.mono (WP.keep [.rax, .r12] (Q := fun t =>
    t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (headValues s)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold entryHead writeController headValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hd, ha,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 120 (by decide), hs 56 (by decide)]

theorem entry_head_args {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hm : t.mem = writeController s.mem p.control (headValues s))
    (k : Keep [.rax, .r12] s t) (j : Nat) (hj : j < 7) : stackArg t j = stackArg s j := by
  have hf := writeController_frame s.mem p.control (headValues s) (fun e he =>
    entryValues_bound s e (List.mem_append_left _ he))
  have hd : (inArgs s).Disjoint ⟨p.control, 128⟩ := by
    rw [← h.2]
    exact h.write_disjoint (w := inCtl s) (by simp [inWrites]) (by simp [inReads]) |>.symm
  change t.mem.readW (stackArgAddr t j) 64 = _
  have ha : stackArgAddr t j = stackArgAddr s j := by
    simp only [stackArgAddr, k.1 .rsp (by simp)]
  rw [ha, hm]
  exact hf.readW (arg_contains s (by omega_using [hj] : j < 9)) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hd) (by decide)

theorem entry_tail_ok {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hm : t.mem = writeController s.mem p.control (headValues s))
    (k : Keep [.rax, .r12] s t) (hr : t.gpr .r12 = p.control) :
    WP isa (.block entryTail) t fun u =>
      u.mem = writeController t.mem p.control (tailValues s) ∧ Keep [.rax, .r10, .r11, .rcx, .rsi] t u := by
  have scr := h.control_scr (t := t) k.2.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions t.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha (j : Nat) (hj : j < 7) : InRegions (t.rd ++ t.wr) (stackArgAddr t j) 8 := by
    simpa only [k.2.1, k.2.2, stackArgAddr, k.1 .rsp (by simp)] using input_args h j (by omega_using [hj])
  have hv (j : Nat) (hj : j < 7) : t.mem.readW (stackArgAddr t j) 64 = stackArg s j :=
    entry_head_args h hm k j hj
  refine WP.keep [.rax, .r10, .r11, .rcx, .rsi] ?_ rfl
  unfold entryTail writeController tailValues
  simp only [List.foldl_cons, List.foldl_nil]
  have ha0 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 8) 8 := ha 0 (by decide)
  have ha2 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 24) 8 := ha 2 (by decide)
  have ha3 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 32) 8 := ha 3 (by decide)
  have ha4 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 40) 8 := ha 4 (by decide)
  have ha5 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 48) 8 := ha 5 (by decide)
  have hv0 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := hv 0 (by decide)
  have hv2 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := hv 2 (by decide)
  have hv3 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s 3 := hv 3 (by decide)
  have hv4 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := hv 4 (by decide)
  have hv5 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 48) 64 = stackArg s 5 := hv 5 (by decide)
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    hr, ha0, ha2, ha3, ha4, ha5, hv0, hv2, hv3, hv4, hv5, hs 64 (by decide), hs 72 (by decide),
    hs 80 (by decide), hs 96 (by decide), hs 104 (by decide), hs 88 (by decide)]
  rfl

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s) ∧
      Keep [.rax, .r12, .r10, .r11, .rcx, .rsi] s t := by
  rw [entry, WP.block_append_iff]
  refine WP.mono (entry_head_ok h) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (entry_tail_ok h hm k hr) fun u ⟨hu, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr,
    by rw [hu, hm, entryValues, writeController_append],
    (k.trans ku).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! # The attempt's precondition, at the callee's entry -/

@[expose] public section

/-! # The attempt's arguments -/

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The attempt's stack arguments, in the order the code stores them: `p_len`
twice (as the width and as `rand_len`), the tape's current pointer,
`scratch` and `scratch_len`, then the context and its length. -/
def callValues (p : KeyPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (2, BitVec.ofNat 64 p.len), (1, p.rp + BitVec.ofNat 64 used),
    (3, p.B), (4, BitVec.ofNat 64 (p.Z / 8)), (5, p.ctx), (6, BitVec.ofNat 64 p.ctxLen)]

private theorem readW_writeW_off64 (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 < 2 ^ 63) (he : e + 8 < 2 ^ 63) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  VG.X86_64.readW_writeW_off m p v (n := 8) hd he h

private theorem readW_writeW_base64 (m : Mem) (p : Addr) (v : BitVec 64) {d : Nat}
    (h : 8 ≤ d) (hd : d + 8 < 2 ^ 63) :
    (m.writeW p v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 := by
  have := readW_writeW_off64 m p v (d := d) (e := 0) (.inr (by omega_using [h])) hd (by decide)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (t : State) : Prop :=
  t.gpr .rdi = p.xp ∧ t.gpr .rsi = BitVec.ofNat 64 p.len ∧
  t.gpr .rdx = p.yp ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧
  t.gpr .r8 = p.dp ∧ t.gpr .r9 = BitVec.ofNat 64 p.dlen

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Cached.Search.cachedArguments) (allocated 56 s) fun t =>
      KeyArgs p t ∧ t.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 56 s) t := by
  have scr : Scr (allocated 56 s) p.control 128 := by
    have sc := h.input.control_scr (t := s) h.wr
    obtain ⟨B, o, L, hm, hb, hL, hl⟩ := sc.wr
    exact ⟨⟨B, o, L, List.mem_cons_of_mem _ hm, hb, hL, hl⟩, sc.nowrap⟩
  have hs : ∀ d, d + 8 ≤ 128 → InRegions ((allocated 56 s).rd ++ (allocated 56 s).wr)
      (p.control + BitVec.ofNat 64 d) 8 := fun _ hd => scr.ld hd
  have hw : ∀ d, d + 8 ≤ 56 → InRegions (allocated 56 s).wr
      ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨⟨s.gpr .rsp - BitVec.ofNat 64 56, 56⟩, List.mem_cons_self ..,
      Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 56)
        (n := 8) (d := d) (k := 56) hd (by omega_using [hd])⟩
  have hw0 : InRegions (allocated 56 s).wr (s.gpr .rsp - BitVec.ofNat 64 56) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  simp only [allocated, State.setReg] at hs hw hw0
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := h.header (j := 5) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := h.header (j := 6) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := h.header (j := 7) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := h.header (j := 12) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := h.header (j := 13) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  have hsp : s.gpr .rsp = original.gpr .rsp := h.rsp.trans (congrArg KeyPublic.sp h.input.2).symm
  have ha7 : (s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 120 = stackArgAddr original 7 := by
    rw [hsp, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ha8 : (s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 128 = stackArgAddr original 8 := by
    rw [hsp, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hr7 : InRegions ((allocated 56 s).rd ++ (allocated 56 s).wr)
      ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 120) 8 := by
    rw [ha7]
    obtain ⟨r, hr, hc⟩ := input_args h.input 7 (by decide)
    refine ⟨r, ?_, hc⟩
    change r ∈ s.rd ++ (_ :: s.wr)
    rw [h.rd, h.wr]
    simp only [List.mem_append, List.mem_cons] at hr ⊢
    rcases hr with hr | hr
    exacts [.inl hr, .inr (.inr hr)]
  have hr8 : InRegions ((allocated 56 s).rd ++ (allocated 56 s).wr)
      ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 128) 8 := by
    rw [ha8]
    obtain ⟨r, hr, hc⟩ := input_args h.input 8 (by decide)
    refine ⟨r, ?_, hc⟩
    change r ∈ s.rd ++ (_ :: s.wr)
    rw [h.rd, h.wr]
    simp only [List.mem_append, List.mem_cons] at hr ⊢
    rcases hr with hr | hr
    exacts [.inl hr, .inr (.inr hr)]
  have hc7 : s.mem.readW ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 120) 64 = p.ctx := by
    rw [ha7, h.args 7 (by decide), ← h.input.2]; rfl
  have hc8 : s.mem.readW ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 128) 64 =
      BitVec.ofNat 64 p.ctxLen := by
    rw [ha8, h.args 8 (by decide), ← h.input.2]; simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  simp only [allocated, State.setReg] at hr7 hr8
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (Q := fun t =>
    KeyArgs p t ∧ t.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold VG.Impl.Ffdh.X86_64.Cached.Search.cachedArguments arguments KeyArgs writeController callValues
  simp only [List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]
  xrun [State.ea, field, off, allocated, State.setReg, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, BitVec.add_zero, h.r12, hs 16 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 96 (by decide), hs 104 (by decide),
    hw0, hw 8 (by decide), hw 16 (by decide), hw 24 (by decide), hw 32 (by decide),
    hw 40 (by decide), hw 48 (by decide), hr7, hr8, hc7, hc8,
    hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]
  simp (disch := decide) only [readW_writeW_off64, readW_writeW_base64]
  rw [hc7, hc8]
  rfl

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word controllerValue allocated)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkPre)

/-- The regions the attempt reads: the domain, `p_len` octets of the tape at
`used`, the context and its stack arguments. -/
def callReads (p : KeyPublic) (used : Nat) : List Region :=
  [⟨p.dp, p.dlen⟩, ⟨p.rp + BitVec.ofNat 64 used, p.len⟩, ⟨p.ctx, p.ctxLen * 8⟩, ⟨p.sp - 56, 56⟩]

/-- The regions the attempt writes: `x`, `y` and the working space. -/
def callWrites (p : KeyPublic) : List Region := [⟨p.xp, p.len⟩, ⟨p.yp, p.len⟩, ⟨p.B, p.Z⟩]

theorem callValues_bound (p : KeyPublic) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : KeyPublic) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callReads p used) (callWrites p)

theorem call_rsp {p : KeyPublic} {used : Nat} {u : State} (hu : u.gpr .rsp = p.sp - 56) :
    (callState p used u).gpr .rsp = p.sp - 56 - 8 := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, hu]

theorem call_argAddr {p : KeyPublic} {used : Nat} {u : State} (hu : u.gpr .rsp = p.sp - 56) :
    stackArgAddr (callState p used u) 0 = p.sp - 56 := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
  exact BitVec.sub_add_cancel _ _

theorem call_arg {p : KeyPublic} {used : Nat} {s u : State} (hu : u.gpr .rsp = p.sp - 56)
    (hs : s.gpr .rsp = p.sp)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used)) (j : Nat) (hj : j < 7) :
    stackArg (callState p used u) j = controllerValue (callValues p used) j
      (word s.mem (p.sp - 56) (8 * j)) := by
  have ha : stackArgAddr (callState p used u) j = p.sp - 56 + BitVec.ofNat 64 (8 * j) := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
    rw [show 8 * (j + 1) = 8 + 8 * j by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  have e1 : p.sp - 56 - 8 + BitVec.ofNat 64 (8 + 8 * j) = p.sp - 56 + BitVec.ofNat 64 (8 * j) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      BitVec.sub_add_cancel]
  have sep : Mem.Sep (p.sp - 56 + BitVec.ofNat 64 (8 * j)) (64 / 8) (p.sp - 56 - 8) (64 / 8) := by
    have := Offset.sep (p.sp - 56 - 8) (d := 8 + 8 * j) (n := 8) (e := 0) (k := 8)
      (.inr (by omega_using [])) (by omega_using [hj]) (by decide)
    rw [e1, BitVec.add_zero] at this
    exact this
  unfold stackArg
  rw [ha, State.withRegions_mem, State.callEntry_mem, hu, Mem.readW_writeW_sep sep (by decide), hm, hs]
  exact writeController_word _ _ _ (callValues_bound p used) j (by omega_using [hj])

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! # One attempt of the key-generation controller

In its frame, the controller passes `vg_ffdh_generate_key_cached` the next `p_len`
octets of the tape. The attempt keeps the controller's state, and leaves
its status, and the key pair or zeros, in `x` and `y`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame_size allocated freed
  allocated_rsp allocated_reg freed_rsp freed_reg frame_alloc)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- What an attempt at `used` leaves: its status, and the key pair for 1,
zeros otherwise. -/
def AttemptPost (p : KeyPublic) (rand : List Byte) (used : Nat) (t : State) : Prop :=
  let st := attemptStatus .cached p.a p.len (rand.drop used)
  let x := Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)
  ((t.gpr .rax).setWidth 32).toNat = st ∧
    if st = 1 then
      Spec.Rsa.bytesAt t.mem p.xp p.len = Spec.Rsa.i2osp x p.len ∧
        Spec.Rsa.bytesAt t.mem p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
    else Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0

theorem AttemptPost.keep {p : KeyPublic} {rand : List Byte} {used : Nat} {s t : State}
    (h : AttemptPost p rand used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32) : AttemptPost p rand used t := by
  unfold AttemptPost at h ⊢
  rw [hm, hr]
  exact h

/-- `AttemptPost` holds whatever the bytes of a frame on the search's stack
hold once released: the key pair's buffers lie apart from it. -/
theorem AttemptPost.lost {p : KeyPublic} {original : State} {rand : List Byte} {used : Nat} {t t' : State}
    (hi : KeyInput p original) (h : AttemptPost p rand used t) (hr : t'.gpr .rax = t.gpr .rax)
    {R : Region} (fm : Frame [R] t.mem t'.mem) (hR : R.Sub (below (original.gpr .rsp) stackUse)) :
    AttemptPost p rand used t' := by
  have hd := hi.1.2.2.2.2.2.2.2.1
  have hrsi := hi.1.2.2.2.2.2.2.2.2.2.2.1
  have hrcx := hi.1.2.2.2.2.2.2.2.2.2.2.2.1
  have sep : ∀ {B : Region}, (below (original.gpr .rsp) stackUse).Disjoint B → ∀ q ∈ [R], B.Disjoint q :=
    fun hB q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact fun x h₁ h₂ => hB x (hR x h₂) h₁
  have hX : (below (original.gpr .rsp) stackUse).Disjoint ⟨p.xp, p.len⟩ := by
    have := (hd (inX original) (by simp [inWrites])).2
    cases hi.2
    simp only [inX, hrsi] at this
    exact this
  have hY : (below (original.gpr .rsp) stackUse).Disjoint ⟨p.yp, p.len⟩ := by
    have := (hd (inY original) (by simp [inWrites])).2
    cases hi.2
    simp only [inY, hrcx] at this
    exact this
  have fit : p.len < 2 ^ 64 := by cases hi.2; exact (stackArg original 1).isLt
  unfold AttemptPost at h ⊢
  rw [hr, Proof.Rsa.rsa_bytes_frame fm fit (sep hX), Proof.Rsa.rsa_bytes_frame fm fit (sep hY)]
  exact h

section

variable {p : KeyPublic} {original s : State} {used keys scalars : Nat}

theorem call_covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (hw : u.wr = (allocated 56 s).wr) : Covers (callWrites p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [hw]
  apply List.mem_cons_of_mem
  have hi := h.input
  obtain ⟨-, -, -, hwr, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := hi.1
  rw [h.wr, hwr]
  cases hi.2
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp [inWrites, inX, keyOfState, hrsi]
  · simp [inWrites, inY, keyOfState, hrcx]
  · simp [inWrites, inScr, keyOfState]

theorem call_covers_reads (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    {u : State} (hrd : u.rd = (allocated 56 s).rd) (hw : u.wr = (allocated 56 s).wr) :
    Covers (callReads p used ++ callWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (call_covers_writes h hw).right
  apply Covers.of_sub
  have hi := h.input
  obtain ⟨-, -, hrd', -⟩ := hi.1
  intro r hr
  simp only [callReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨inDom original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inDom original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨inRand original, ?_, used, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inRand original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; rfl
    · cases hi.2; exact hroom
  · refine ⟨inContext original, ?_, 0, ?_, ?_⟩
    · rw [hrd]; exact List.mem_append_left _ (by
        change inContext original ∈ s.rd; rw [h.rd, hrd']; simp [inReads])
    · cases hi.2; simp only [BitVec.add_zero]; rfl
    · cases hi.2; simp only [Nat.zero_add]; exact Nat.le_refl _
  · refine ⟨⟨s.gpr .rsp - BitVec.ofNat 64 56, 56⟩, ?_, 0, ?_, Nat.le_refl _⟩
    · rw [hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [h.rsp, BitVec.add_zero]; rfl

/-- What the attempt writes, as the controller sees it. -/
theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State}
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 56) {d : Nat} (hd : d ≤ 8)
    (hf : Frame (callWrites p ++ [below (u.gpr .rsp) (d + 8)]) u.mem t.mem) :
    Frame (KeyInput.callChanges original) s.mem t.mem := by
  have hi := h.input
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := hi.1
  have hsp : s.gpr .rsp = original.gpr .rsp := by rw [h.rsp, ← hi.2]; rfl
  have h1 : Frame (KeyInput.callChanges original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p used) (size := 56) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨below (original.gpr .rsp) stackUse, by simp [KeyInput.callChanges], ?_⟩
    rw [hsp]
    exact Offset.sub_below _ (by decide) (by decide)
  have h2 : Frame (KeyInput.callChanges original) u.mem t.mem := by
    apply hf.sub
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · cases hi.2
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨inX original, by simp [KeyInput.callChanges], by
          simp only [inX, keyOfState, hrsi]; exact fun _ hi => hi⟩
      · exact ⟨inY original, by simp [KeyInput.callChanges], by
          simp only [inY, keyOfState, hrcx]; exact fun _ hi => hi⟩
      · exact ⟨inScr original, by simp [KeyInput.callChanges], fun _ hi => hi⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨below (original.gpr .rsp) stackUse, by simp [KeyInput.callChanges], ?_⟩
      rw [hu, ← hsp, h.rsp]
      show Region.Sub ⟨p.sp - 56 - BitVec.ofNat 64 (d + 8), d + 8⟩ ⟨p.sp - BitVec.ofNat 64 72, 72⟩
      rw [BitVec.sub_sub, show (56 : BitVec 64) + BitVec.ofNat 64 (d + 8) = BitVec.ofNat 64 (64 + d) by
        rw [show (56 : BitVec 64) = BitVec.ofNat 64 56 from rfl, ← BitVec.ofNat_add]; congr 1; omega_using []]
      exact Offset.sub_below _ (by omega_using [hd]) (by omega_using [hd])
  exact h1.trans h2

/-- What the call's entry changes: the arguments and its return address. -/
theorem call_mem_frame (h : KeyLive p original used keys scalars s) {u : State}
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 56) : Frame (KeyInput.changes original) s.mem (callState p used u).mem := by
  have hi := h.input
  have hsp : s.gpr .rsp = original.gpr .rsp := by rw [h.rsp, ← hi.2]; rfl
  have hb : Region.Sub (below (original.gpr .rsp) stackUse) (below (original.gpr .rsp) stackUse) :=
    fun _ h => h
  have hin : below (original.gpr .rsp) stackUse ∈ KeyInput.changes original := by
    simp [KeyInput.changes]
  have h1 : Frame (KeyInput.changes original) s.mem u.mem := by
    rw [hm]
    apply (writeController_frame_size _ _ (callValues p used) (size := 56) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, hin, ?_⟩
    rw [hsp]
    exact Offset.sub_below _ (by decide) (by decide)
  refine h1.trans ?_
  simp only [State.withRegions_mem, State.callEntry_mem]
  refine Frame.writeW (Frame.refl _ _) hin _ ?_
  rw [hu, ← h.rsp, hsp]
  have he : original.gpr .rsp - 56 - 8 = original.gpr .rsp - BitVec.ofNat 64 64 := by
    rw [BitVec.sub_sub]; rfl
  rw [he, show original.gpr .rsp - BitVec.ofNat 64 64 =
      original.gpr .rsp - BitVec.ofNat 64 72 + BitVec.ofNat 64 8 from Offset.sub_ofNat_eq _ (by decide)]
  exact Offset.contains_base _ (by decide) (by decide)

end

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
