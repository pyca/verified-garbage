module

import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Key
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import Mathlib.Tactic.Attr.Core

/-! ### `RsaKeyGen.X86_64.Key.Halve`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.Key.Front`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.Key.Pieces`, which this module and modules that import it used -/

section

/-! ## State -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: the state between the pieces

`KF B W cs`: memory that changes only in the arrays and header slots the
codes `cs` name, so that what a piece keeps is decided on the codes
(`KF.wv`, `KF.word`). `KS I m₀`: what every piece keeps (the working space
for `W` words, the arguments in the header, the inputs, and memory outside
the working space), after a piece that changes only arrays and the header
slots `sMo`, `kEv` and `kOk` (`KS.step`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Rsa
open VG.Impl.RsaKeyGen.X86_64.Candidate (kE kElen)

/-! ## Frames by codes -/

/-- A part of the working space: an array (`w + 2` words), or a header
slot. -/
inductive Rc where
  | arr (i : Nat)
  | hdr (i : Nat)
  /-- The private arrays of `inverse`, 16 to 25. -/
  | priv
  deriving DecidableEq

/-- Its byte range, for arrays of `W + 2` words. -/
def Rc.range (W : Nat) : Rc → Nat × Nat
  | .arr i => (slot W i, 8 * (W + 2))
  | .hdr i => (8 * i, 8)
  | .priv => (slot W 16, 80 * (W + 2))

/-- One of the sixteen arrays, or of the header's 32 slots. -/
def Rc.ok : Rc → Bool
  | .arr i => decide (i < 16)
  | .hdr i => decide (i < 32)
  | .priv => true

/-- One the pieces may change: an array, or `sMo`, `kEv` or `kOk`. -/
def Rc.mut : Rc → Bool
  | .arr i => decide (i < 16)
  | .hdr i => decide (29 ≤ i ∧ i < 32)
  | .priv => true

/-- Memory that changes only in the parts `cs`. -/
def KF (B : Addr) (W : Nat) (cs : List Rc) (m m' : Mem) : Prop := Frm B (cs.map (Rc.range W)) m m'

theorem KF.refl (B : Addr) (W : Nat) (m : Mem) : KF B W [] m m := Frm.refl _ _ _

theorem KF.trans {B : Addr} {W : Nat} {cs cs' : List Rc} {m₁ m₂ m₃ : Mem} (h₁ : KF B W cs m₁ m₂)
    (h₂ : KF B W cs' m₂ m₃) : KF B W (cs ++ cs') m₁ m₃ := by
  unfold KF at *; rw [List.map_append]; exact Frm.append h₁ h₂

theorem KF.mono {B : Addr} {W : Nat} {cs cs' : List Rc} {m m' : Mem} (h : KF B W cs m m')
    (hs : ∀ c ∈ cs, c ∈ cs') : KF B W cs' m m' :=
  Frm.mono h fun r hr => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨c, hs c hc, rfl⟩

/-- Ranges, each within a part of `cs`. -/
theorem KF.of_frm {B : Addr} {W : Nat} {rs : List (Nat × Nat)} {cs : List Rc} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, ∃ c ∈ cs, (c.range W).1 ≤ r.1 ∧ r.1 + r.2 ≤ (c.range W).1 + (c.range W).2) :
    KF B W cs m m' :=
  fun x hx => h x fun r hr' => by
    obtain ⟨c, hc, h1, h2⟩ := hr r hr'
    have := hx (c.range W) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    omega_arith

theorem KF.of_outside {B : Addr} {W : Nat} {o n : Nat} {cs : List Rc} {m m' : Mem} (h : Outside B o n m m')
    (c : Rc) (hc : c ∈ cs) (h1 : (c.range W).1 ≤ o) (h2 : o + n ≤ (c.range W).1 + (c.range W).2) :
    KF B W cs m m' :=
  KF.of_frm (Frm.of_outside h (List.mem_singleton_self _)) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨c, hc, h1, h2⟩

/-- An array's range, against a part other than it. -/
theorem range_sep_arr {W j : Nat} (hj : j < 16) {c : Rc} (hc : c.ok = true) (hne : c ≠ .arr j) {d k : Nat}
    (hd : slot W j ≤ d) (hdk : d + 8 * k ≤ slot W j + 8 * (W + 2)) :
    d + 8 * k ≤ (c.range W).1 ∨ (c.range W).1 + (c.range W).2 ≤ d := by
  cases c with
  | arr i =>
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    have := slot_far (w := W) hij
    simp only [Rc.range]; omega_arith
  | hdr i =>
    simp only [Rc.ok, decide_eq_true_eq] at hc
    have := hdr_lt_slot W j hc
    simp only [Rc.range]; omega_arith
  | priv =>
    have := slot_lt (w := W) hj
    simp only [Rc.range]; omega_arith

/-- A header slot's word, against a part other than it. -/
theorem range_sep_hdr {W i : Nat} (hi : i < 32) {c : Rc} (hc : c.ok = true) (hne : c ≠ .hdr i) :
    8 * i + 8 ≤ (c.range W).1 ∨ (c.range W).1 + (c.range W).2 ≤ 8 * i := by
  cases c with
  | arr j =>
    simp only [Rc.ok, decide_eq_true_eq] at hc
    have := hdr_lt_slot W j hi
    simp only [Rc.range]; omega_arith
  | hdr h =>
    have hij : h ≠ i := fun e => hne (e ▸ rfl)
    simp only [Rc.range]; omega_arith
  | priv =>
    have := hdr_lt_slot W 16 hi
    simp only [Rc.range]; omega_arith

/-- Words of an array the parts do not include. -/
theorem KF.wv {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) {d k : Nat} (hd : slot W j ≤ d)
    (hdk : d + 8 * k ≤ slot W j + 8 * (W + 2)) (hZ : slot W 16 ≤ 2 ^ 64) :
    VG.Proof.Bignum.wv m' B d k = VG.Proof.Bignum.wv m B d k := by
  have := slot_lt (w := W) hj
  refine Frm.wv_eq h (fun r hr => ?_) (by omega_arith)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact range_sep_arr hj (List.all_eq_true.mp hok c hc) (fun e => hn (e ▸ hc)) hd hdk

/-- An array the parts do not include. -/
theorem KF.arr {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot W 16 ≤ 2 ^ 64) :
    VG.Proof.Bignum.wv m' B (slot W j) W = VG.Proof.Bignum.wv m B (slot W j) W :=
  h.wv hok hj hn (Nat.le_refl _) (by omega_arith) hZ

/-- Word `W` of an array the parts do not include. -/
theorem KF.top {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot W 16 ≤ 2 ^ 64) :
    word m' B (slot W j + 8 * W) = word m B (slot W j + 8 * W) := by
  have := slot_lt (w := W) hj
  refine Frm.word_eq h (fun r hr => ?_) (by omega_arith)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact range_sep_arr (k := 1) hj (List.all_eq_true.mp hok c hc) (fun e => hn (e ▸ hc)) (by omega_arith) (by omega_arith)

/-- A header slot the parts do not include. -/
theorem KF.word {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {i : Nat} (hi : i < 32) (hn : .hdr i ∉ cs) : word m' B (8 * i) = word m B (8 * i) :=
  Frm.word_eq h (fun r hr => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact range_sep_hdr hi (List.all_eq_true.mp hok c hc) (fun e => hn (e ▸ hc))) (by omega_arith)

/-! ## The inputs and the state -/

/-- The inputs of `vg_rsa_keygen_key` and where they are: the working
space at `B` of `Z` bytes, the primes' length `pl`, the outputs, `e`, the
saved registers, the inputs' bytes, the writable regions and the stack
pointer. -/
structure KIn where
  B : Addr
  Z : Nat
  pl : Nat
  pN : Addr
  pD : Addr
  pP : Addr
  pQ : Addr
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pE : Addr
  el : Nat
  sv : Nat → BitVec 64
  pb : List Byte
  qb : List Byte
  eb : List Byte
  Wr : List Region
  sp : Addr

/-- The words of `n`: `n_len / 8 = 2 pl / 8`. -/
abbrev KIn.W (I : KIn) : Nat := 2 * I.pl / 8

/-- The arguments in the header. -/
structure KArgs (m : Mem) (I : KIn) : Prop where
  no : word m I.B (8 * kNo) = I.pN
  nl : word m I.B (8 * kNl) = BitVec.ofNat 64 (2 * I.pl)
  dd : word m I.B (8 * kDo) = I.pD
  pp : word m I.B (8 * kPp) = I.pP
  pl : word m I.B (8 * kPl) = BitVec.ofNat 64 I.pl
  qp : word m I.B (8 * kQp) = I.pQ
  dp : word m I.B (8 * kDp) = I.pDp
  dq : word m I.B (8 * kDq) = I.pDq
  qi : word m I.B (8 * kQi) = I.pQi
  e : word m I.B (8 * kE) = I.pE
  el : word m I.B (8 * kElen) = BitVec.ofNat 64 I.el
  saved : ∀ i < 6, word m I.B (8 * i) = I.sv i

/-- The header slots of `KArgs`: below 6, or from 16 to 27. -/
theorem KArgs.congr {m m' : Mem} {I : KIn} (h : KArgs m I)
    (hm : ∀ i, (i < 6 ∨ (16 ≤ i ∧ i < 28)) → word m' I.B (8 * i) = word m I.B (8 * i)) : KArgs m' I :=
  ⟨(hm _ (by simp [kNo, sFn])).trans h.no, (hm _ (by simp [kNl, sFn])).trans h.nl,
    (hm _ (by simp [kDo, sFn])).trans h.dd, (hm _ (by simp [kPp, sFn])).trans h.pp,
    (hm _ (by simp [kPl, sFn])).trans h.pl, (hm _ (by simp [kQp, sFn])).trans h.qp,
    (hm _ (by simp [kDp, sFn])).trans h.dp, (hm _ (by simp [kDq, sFn])).trans h.dq,
    (hm _ (by simp [kQi, sFn])).trans h.qi,
    (hm _ (by simp [kE, Impl.RsaKeyGen.X86_64.Candidate.kE, sFn])).trans h.e,
    (hm _ (by simp [kElen, Impl.RsaKeyGen.X86_64.Candidate.kElen, sFn])).trans h.el,
    fun i hi => (hm i (Or.inl hi)).trans (h.saved i hi)⟩

/-- What every piece keeps, from the memory `m₀` after the entry. -/
structure KS (I : KIn) (m₀ : Mem) (s : State) : Prop where
  ws : Ws s I.B I.Z I.W
  args : KArgs s.mem I
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  e : Src s I.B I.Z I.pE I.eb
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.Wr
  rsp : s.gpr .rsp = I.sp
  /-- Room for `inverse`'s private arrays. -/
  z26 : slot I.W 26 ≤ I.Z
  /-- The width `inverse` needs. -/
  w20 : I.W < 2 ^ 20

theorem Rc.ok_of_mut {c : Rc} (h : c.mut = true) : c.ok = true := by
  cases c <;> simp only [Rc.mut, Rc.ok, decide_eq_true_eq] at h ⊢ <;> omega_arith

theorem KS.hZ {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) : slot I.W 16 ≤ 2 ^ 64 := by
  have := h.ws.hZ; have := h.ws.scr.nowrap; omega_arith

/-- `KS` after a piece that changes only parts the pieces may change. -/
theorem KS.step {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) {cs : List Rc}
    (hf : KF I.B I.W cs s.mem t.mem) (hc : cs.all Rc.mut = true) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : KS I m₀ t := by
  have hok : cs.all Rc.ok = true :=
    List.all_eq_true.mpr fun c hc' => Rc.ok_of_mut (List.all_eq_true.mp hc c hc')
  have hhdr : ∀ i, i < 29 → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi =>
    hf.word hok (by omega_arith) fun hm => by
      have := List.all_eq_true.mp hc _ hm
      simp only [Rc.mut, decide_eq_true_eq] at this; omega_arith
  have hZ := h.ws.hZ
  have hn := h.ws.scr.nowrap
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf fun r hr => by
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hr
    have := List.all_eq_true.mp hc c hc'
    cases c with
    | arr i =>
      simp only [Rc.mut, decide_eq_true_eq] at this
      have := slot_lt (w := I.W) this
      simp only [Rc.range]; omega_arith
    | hdr i =>
      simp only [Rc.mut, decide_eq_true_eq] at this
      have := hdr_lt_slot I.W 16 (show 31 < 32 by decide)
      simp only [Rc.range]; omega_arith
    | priv =>
      have := h.z26
      simp only [Rc.range]; unfold slot at *; omega_arith
  refine ⟨⟨h.ws.scr.congr k.2.2, (k.gpr hr.1).trans h.ws.rdi, (hhdr sW (by decide)).trans h.ws.hw,
      (hhdr sStride (by decide)).trans h.ws.hS, fun j hj => (hhdr (sArr j) (by unfold sArr; omega_arith)).trans
      (h.ws.harr j hj), hZ, h.ws.w1, h.ws.w2⟩,
    h.args.congr fun i hi => hhdr i (by omega_arith), h.p.congrK hi k, h.q.congrK hi k, h.e.congrK hi k,
    h.inScr.trans hi, k.2.2.trans h.wr, (k.gpr hr.2).trans h.rsp, h.z26, h.w20⟩

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Pieces -/
section

/-!
# An RSA key from its primes on x86-64: the pieces

The routines the code is made of, from `KS`: what each leaves in the arrays
(`av`, the low `W` words of one), and the parts it changes (`KF`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Array `j`'s value: its low `W` words. -/
abbrev av (I : KIn) (m : Mem) (j : Nat) : Nat := wv m I.B (slot I.W j) I.W

/-- Word `W` of array `j`. -/
abbrev atop (I : KIn) (m : Mem) (j : Nat) : BitVec 64 := word m I.B (slot I.W j + 8 * I.W)

/-- `KF.arr` for `av`. -/
theorem KF.av {I : KIn} {cs : List Rc} {m m' : Mem} (h : KF I.B I.W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot I.W 16 ≤ 2 ^ 64) : av I m' j = av I m j :=
  h.arr hok hj hn hZ

/-- `KF.top` for `atop`. -/
theorem KF.at {I : KIn} {cs : List Rc} {m m' : Mem} (h : KF I.B I.W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot I.W 16 ≤ 2 ^ 64) : atop I m' j = atop I m j :=
  h.top hok hj hn hZ

theorem all_mut_arr {j : Nat} (hj : j < 16) : [Rc.arr j].all Rc.mut = true := by
  simp only [List.all_cons, List.all_nil, Rc.mut, Bool.and_true, decide_eq_true_eq]; exact hj

theorem KF.arr1 {I : KIn} {m m' : Mem} {j : Nat} {o n : Nat} (h : Outside I.B o n m m') (h1 : slot I.W j ≤ o)
    (h2 : o + n ≤ slot I.W j + 8 * (I.W + 2)) : KF I.B I.W [.arr j] m m' :=
  KF.of_outside h (.arr j) (List.mem_singleton_self _) h1 h2

/-- A zero number of `W + 2` words: its low `W` words and word `W`. -/
theorem wv_zero2 {m : Mem} {B : Addr} {d W : Nat} (hz : wv m B d (W + 2) = 0) :
    wv m B d W = 0 ∧ word m B (d + 8 * W) = 0 := by
  have := (wv_eq_zero_iff _ _ _ _).mp hz
  exact ⟨wv_zero fun k hk => this k (by omega_arith), this W (by omega_arith)⟩

/-- Word `k` of a zero number written. -/
theorem wv_put {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : ∀ q < N, word m B (d + 8 * q) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = if k < n then 2 ^ (64 * k) * v.toNat else 0
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv_put v hz hd hk n (by omega_arith)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega_arith)).word (by omega_arith) (by omega_arith), hz n (by omega_arith)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega_arith]
      · simp [hk', show ¬ k < n + 1 by omega_arith]

/-! ## Clearing and copying -/

theorem zeroA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 0 ∧ Keep [.r12, .r9, .r8, .rax, .r14] s t :=
  WP.mono (zeroA_ok h.ws hj) fun t ⟨hz, o, k⟩ =>
    have f := KF.arr1 o (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.step f (all_mut_arr hj) k (by decide), f, hz, k⟩

theorem copyA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      av I t.mem o = av I s.mem a ∧ atop I t.mem o = atop I s.mem o ∧
      Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t :=
  WP.mono (copyA_ok h.ws ho ha hoa) fun t ⟨hv, o', k⟩ =>
    have f := KF.arr1 o' (Nat.le_refl _) (by omega_arith)
    have hn := h.ws.scr.nowrap
    have := h.ws.sl ho
    ⟨h.step f (all_mut_arr ho) k (by decide), f, hv, o'.word (Or.inr (Nat.le_refl _)) (by omega_arith), k⟩

/-- `zeroA` then `copyA`: `[o] := [a]` with words `W` and `W + 1` zero. -/
theorem zc_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (seqs [zeroA o, copyA o a]) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      av I t.mem o = av I s.mem a ∧ atop I t.mem o = 0 := by
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h ho) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  refine WP.mono (copyA_k h₁ ho ha hoa) fun t ⟨ht, f₂, v₂, t₂, _⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (f₁.trans f₂).mono (by simp)
  · rw [v₂]; exact f₁.arr (by simp [Rc.ok, ho]) ha (by simp [hoa.symm]) h.hZ
  · rw [t₂]; exact (wv_zero2 z₁).2

/-- `constA x`: `[aC] := x` over `W + 2` words. -/
theorem constA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (x : BitVec 32) :
    WP isa (seqs (constA x)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aC) (I.W + 2) = x.toNat ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rbx] s t := by
  have hn := h.ws.scr.nowrap
  have sC := h.ws.sl (j := aC) (by decide)
  simp only [constA, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aC) (by decide)) fun s₁ ⟨h₁, f₁, z₁, k₁⟩ => ?_)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h₁.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h₁.ws.scr.congr (k₂.trans k₃).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC)) (x.setWidth 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.st (d := slot I.W aC) (by omega_arith), m₃, m₂]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s₁.mem I.B (x.setWidth 64) (d := slot I.W aC) (by omega_arith)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega_arith)
  have kk := (k₂.trans k₃).trans k₄
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) kk (by decide), (f₁.trans f₄).mono (by decide), ?_,
    (k₁.trans kk).mono (by decide)⟩
  rw [hm]
  have := wv_put (m := s₁.mem) (B := I.B) (d := slot I.W aC) (N := I.W + 2) (k := 0) (x.setWidth 64)
    ((wv_eq_zero_iff _ _ _ _).mp z₁) (by omega_arith) (by omega_arith) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this]
  rw [ite_eq_left (show 0 < I.W + 2 by omega_arith), Nat.pow_zero, Nat.one_mul, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))

/-- A number of `W + 2` words below `2^(64 W)` is its low `W` words. -/
theorem av_of_full {I : KIn} {m : Mem} {j v : Nat} (h : wv m I.B (slot I.W j) (I.W + 2) = v)
    (hv : v < 2 ^ (64 * I.W)) : av I m j = v :=
  (wv_low_of_lt (Nat.le_add_right _ 2) (by rw [h]; exact hv)).trans h

/-! ## Masks -/

/-- `ltA a b`: `rbp := ` the mask of `[a] < [b]`. -/
theorem ltA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (ltA a b)) s fun t => KS I m₀ t ∧ t.mem = s.mem ∧
      t.gpr .rbp = mask (decide (av I s.mem a < av I s.mem b)) ∧
      t.gpr .rbx = off I.B (slot I.W a) ∧ t.gpr .r10 = off I.B (slot I.W b) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  have hn := h.ws.scr.nowrap
  have sa := h.ws.sl ha
  have sb := h.ws.sl hb
  simp only [ltA, seqs]
  have hb : WP isa (.block (ws ++ base a .rbx ++ base b .r10 ++ [.mov32 .rbp (.imm 0)])) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .rbx = off I.B (slot I.W a) ∧
      t.gpr .r10 = off I.B (slot I.W b) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp] s t := by
    rw [List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
    refine WP.mono (base_ok a (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi) h9)
      fun s₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok b (r := .r10) (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi)
      ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => ?_
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₃.mem) (by xrun) rfl)
      fun t ⟨⟨hbp, hm⟩, k₄⟩ => ⟨((k₂.trans k₃).trans k₄).gpr (by decide) |>.trans h12,
        (k₃.trans k₄).gpr (by decide) |>.trans hbx, (k₄.gpr (by decide)).trans h10, hbp,
        by rw [hm, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  refine WP.seq (WP.mono hb ?_)
  · intro s₁ ⟨h12, hbx, h10, hbp, m₁, k₁⟩
    refine WP.mono (cmpLoop_ok (h.ws.scr.congr k₁.2.2) hbx h10 h12 hbp (by have := h.ws.w1; omega_arith)
      (by have := h.ws.w2; omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨hbp', m₂, k₂⟩ => ?_
    rw [m₁] at hbp'
    have kk := k₁.trans k₂
    exact ⟨h.step (cs := []) (by rw [m₂, m₁]; exact KF.refl _ _ _) rfl kk (by decide), by rw [m₂, m₁], hbp',
      (k₂.gpr (by decide)).trans hbx, (k₂.gpr (by decide)).trans h10, (k₂.gpr (by decide)).trans h12,
      kk.mono (by decide)⟩

theorem isZero_mask {x : BitVec 64} {c : Prop} [Decidable c] (hx : x = 0 ↔ c) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) = mask (decide c) := by
  by_cases hc : c
  · rw [hx.mpr hc, decide_eq_true hc]; decide
  · have : x ≠ 0 := fun e => hc (hx.mp e)
    have : ¬ x.toNat < 1 := fun h => this (BitVec.eq_of_toNat_eq (by simp; omega_arith))
    rw [decide_eq_false hc]
    simp [this, mask]

/-- `eqMask a b`: `rbp := ` the mask of `[a] = [b]`. -/
theorem eqMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (eqMask a b)) s fun t => KS I m₀ t ∧ t.mem = s.mem ∧
      t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  rw [eqMask]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) ∧
    t.mem = s₁.mem) ?_ rfl) fun t ⟨⟨hbp, m₂⟩, k₂⟩ => ?_
  · unfold isZero
    xrun
    exact isZero_mask hz
  · have kk := k₁.trans k₂
    exact ⟨h.step (cs := []) (by rw [m₂, m₁]; exact KF.refl _ _ _) rfl kk (by decide), by rw [m₂, m₁], hbp,
      kk.mono (by decide)⟩

/-- `selC j`: `[j] := rbp ? [j] : [aC]`. -/
theorem selC_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjC : j ≠ aC)
    {c : Bool} (hbp : s.gpr .rbp = mask c) :
    WP isa (seqs (selC j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j else av I s.mem aC) ∧ atop I t.mem j = atop I s.mem j ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sC := h.ws.sl (j := aC) (by decide)
  have sp := slot_far (w := I.W) hjC
  simp only [selC, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j aC (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr (k₁.trans k₂).2.2) h8 hsi (((k₁.trans k₂).gpr (by decide)).trans hbp)
    ((k₂.gpr (by decide)).trans h12) (by have := h.ws.w1; omega_arith) (by have := h.ws.w2; omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t ⟨hv, o, k₃⟩ => ?_
  rw [m₂, m₁] at hv o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega_arith)
  have kk := (k₁.trans k₂).trans k₃
  exact ⟨h.step f (all_mut_arr hj) kk (by decide), f, hv, o.word (Or.inr (Nat.le_refl _)) (by omega_arith),
    kk.mono (by decide)⟩

/-- `subC o a`: `[o] := [a] - ([aC] & r15)` over `W` words. -/
theorem subC_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoC : o ≠ aC) (haC : a ≠ aC) (hoa : o = a ∨ o ≠ a) {c : Bool} (h15 : s.gpr .r15 = mask c) :
    WP isa (seqs (subC o a)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      (∃ b : Bool, av I t.mem o + (if c then av I s.mem aC else 0) = av I s.mem a + 2 ^ (64 * I.W) * b.toNat) ∧
      atop I t.mem o = atop I s.mem o ∧ Keep [.r12, .r9, .r8, .r10, .rsi, .rbp, .rax, .rdx, .r14] s t := by
  have hn := h.ws.scr.nowrap
  have so := h.ws.sl ho
  have sa := h.ws.sl ha
  have sC := h.ws.sl (j := aC) (by decide)
  have pC := slot_far (w := I.W) hoC
  have pA : slot I.W o ≤ slot I.W a ∨ slot I.W a + 8 * I.W ≤ slot I.W o := by
    rcases hoa with rfl | hne
    · exact Or.inl (Nat.le_refl _)
    · have := slot_far (w := I.W) hne; omega_arith
  simp only [subC, seqs]
  have hb : WP isa (.block (ws ++ base a .r8 ++ base aC .r10 ++ base o .rsi ++ [.mov32 .rbp (.imm 0)])) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .r8 = off I.B (slot I.W a) ∧ t.gpr .r10 = off I.B (slot I.W aC) ∧
      t.gpr .rsi = off I.B (slot I.W o) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r8, .r10, .rsi, .rbp] s t := by
    simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : s₁.gpr .rdi = I.B := (k₁.gpr (by decide)).trans h.ws.rdi
    refine WP.mono (base_ok a (r := .r8) (by decide) hdi₁ h9) fun s₂ ⟨h8, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
      ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok o (r := .rsi) (by decide) (((k₂.trans k₃).gpr (by decide)).trans hdi₁)
      (((k₂.trans k₃).gpr (by decide)).trans h9)) fun s₄ ⟨hsi, m₄, k₄⟩ => ?_
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₄.mem) (by xrun) rfl)
      fun t ⟨⟨hbp, hm⟩, k₅⟩ => ⟨(((k₂.trans k₃).trans k₄).trans k₅).gpr (by decide) |>.trans h12,
        ((k₃.trans k₄).trans k₅).gpr (by decide) |>.trans h8, ((k₄.trans k₅).gpr (by decide)).trans h10,
        (k₅.gpr (by decide)).trans hsi, hbp, by rw [hm, m₄, m₃, m₂, m₁],
        ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨h12, h8, h10, hsi, hbp, m₁, k₁⟩ => ?_)
  refine WP.mono (subM_ok (h.ws.scr.congr k₁.2.2) hsi h8 h10 ((k₁.gpr (by decide)).trans h15) h12 hbp
    (by have := h.ws.w1; omega_arith) (by have := h.ws.w2; omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) pA (by omega_arith))
    fun t ⟨b, _, hv, o', k₂⟩ => ?_
  rw [m₁] at hv o'
  have f := KF.arr1 (I := I) (j := o) o' (Nat.le_refl _) (by omega_arith)
  have kk := k₁.trans k₂
  exact ⟨h.step f (all_mut_arr ho) kk (by decide), f, ⟨b, hv⟩, o'.word (Or.inr (Nat.le_refl _)) (by omega_arith),
    kk.mono (by decide)⟩

/-- `oddMask j`: `rax := ` the mask of `[j]` odd. -/
theorem oddMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) :
    WP isa (.block (oddMask j)) s fun t => t.mem = s.mem ∧ t.gpr .rax = mask (decide (av I s.mem j % 2 = 1)) ∧
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  unfold oddMask
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (k₁.trans k₂).2.2
  have e0 : (s₂.mem.readW (off I.B (slot I.W j)) 64).toNat % 2 = av I s.mem j % 2 := by
    rw [m₂, m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₂.mem ∧
    t.gpr .rax = mask (decide (av I s.mem j % 2 = 1))) (by
      xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot I.W j) (by omega_arith), mask_low, e0]) rfl) fun t ⟨⟨hm, hax⟩, k₃⟩ =>
    ⟨by rw [hm, m₂, m₁], hax, ((k₂.trans k₃).gpr (by decide)).trans h12, ((k₂.trans k₃).gpr (by decide)).trans h9,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `setOneA j` on a zero array: `[j] := 1` over `W + 2` words. -/
theorem setOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16)
    (hz : wv s.mem I.B (slot I.W j) (I.W + 2) = 0) :
    WP isa (.block (setOneA j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 1 ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  refine WP.mono (setOneA_ok h.ws hj) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot I.W j) (by omega_arith)
  rw [← hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega_arith)
  refine ⟨h.step f (all_mut_arr hj) k (by decide), f, ?_, k⟩
  rw [hm]
  have := wv_put (m := s.mem) (B := I.B) (d := slot I.W j) (N := I.W + 2) (k := 0) (1 : BitVec 64)
    ((wv_eq_zero_iff _ _ _ _).mp hz) (by omega_arith) (by omega_arith) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < I.W + 2 by omega_arith)]
  rfl

/-! ## Division and inverses -/

theorem all_mut_arrs {js : List Nat} (h : ∀ j ∈ js, j < 16) : (js.map Rc.arr).all Rc.mut = true :=
  List.all_eq_true.mpr fun c hc => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    simp only [Rc.mut, decide_eq_true_eq]; exact h j hj

/-- `divmod q r d t`: `[r] := [q] mod [d]`, `[q] := [q] / [d]`. -/
theorem divmod_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {iQ iR iD iT : Nat}
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divmod iQ iR iD iT) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem ∧
      (0 < av I s.mem iD →
        wv t.mem I.B (slot I.W iR) (I.W + 1) = av I s.mem iQ % av I s.mem iD ∧
        av I t.mem iQ = av I s.mem iQ / av I s.mem iD) := by
  refine WP.mono (divmod_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega_arith) h.ws.w2 h.ws.hZ hQ hR hD hT
    dQR dQD dQT dRD dRT dDT) fun t ⟨hdi, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf
  have k' : Keep (List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)) s t :=
    ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
      ⟨hm, by simp [e]⟩), k.2⟩
  exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k' (by decide), f, hv⟩

/-- `inverse u v x₂ m`: for an odd `m`, `v = gcd(u, m)` and `x₂ u ≡ v (mod m)`,
`x₂ < m`. -/
theorem inverse_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {iU iV iX₂ iM : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (dVX₂ : iV ≠ iX₂) :
    WP isa (inverse iU iV iX₂ iM) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr iV, .arr iX₂, .priv] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (av I s.mem iM % 2 = 1 →
        av I t.mem iV = Nat.gcd (av I s.mem iU) (av I s.mem iM) ∧
        ((av I s.mem iM : Nat) : Int) ∣ (av I t.mem iX₂ : Int) * av I s.mem iU - av I t.mem iV ∧
        av I t.mem iX₂ < av I s.mem iM) := by
  refine WP.mono (InvLaw.inverse_ok h.ws h.z26 h.w20 hU hV hX₂ hM dVX₂) fun t ⟨_, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iV, .arr iX₂, .priv] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.priv, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  refine ⟨h.step f ?_ k (by decide), f, k, hv⟩
  simp only [List.all_cons, List.all_nil, Rc.mut, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega_arith

/-- `kHalf`: `r13 := w / 2`. -/
theorem kHalf_ok {t : State} {W : Nat} (h12 : t.gpr .r12 = BitVec.ofNat 64 W) (hW : W < 2 ^ 63) :
    WP isa (.block kHalf) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 (W / 2) ∧ t'.mem = t.mem ∧ Keep [.r13] t t' := by
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 (W / 2) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨h, m⟩, k⟩ => ⟨h, m, k⟩
  unfold kHalf
  xrun [h12]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hW]),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [hW])]

/-- `kOne`: `r13 := 1`. -/
theorem kOne_ok {t : State} :
    WP isa (.block kOne) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 1 ∧ t'.mem = t.mem ∧ Keep [.r13] t t' := by
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 1 ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨h, m⟩, k⟩ => ⟨h, m, k⟩
  unfold kOne
  xrun []

/-- `inverseK k`, the inverse at the width `n` that `k` puts into `r13`: its
frame for any arrays, and `inverse_k`'s result for `u` and `m` below
`2^(64 n)`. -/
theorem inverseK_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {k : List Instr} {n : Nat}
    (hk : ∀ t : State, t.gpr .r12 = BitVec.ofNat 64 I.W → I.W < 2 ^ 20 → WP isa (.block k) t fun t' =>
      t'.gpr .r13 = BitVec.ofNat 64 n ∧ t'.mem = t.mem ∧ Keep [.r13] t t')
    (hn1 : 1 ≤ n) (hnw : n ≤ I.W) {iU iV iX₂ iM : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (dVX₂ : iV ≠ iX₂) :
    WP isa (inverseK k iU iV iX₂ iM) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr iV, .arr iX₂, .priv] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (av I s.mem iU < 2 ^ (64 * n) → av I s.mem iM < 2 ^ (64 * n) → av I s.mem iM % 2 = 1 →
        av I t.mem iV = Nat.gcd (av I s.mem iU) (av I s.mem iM) ∧
        ((av I s.mem iM : Nat) : Int) ∣ (av I t.mem iX₂ : Int) * av I s.mem iU - av I t.mem iV ∧
        av I t.mem iX₂ < av I s.mem iM) := by
  unfold inverseK
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (hk s₁ h12 h.w20) fun s₂ ⟨h13, m₂, k₂⟩ => ?_))
  have hm : s₂.mem = s.mem := by rw [m₂, m₁]
  have h₂ : Ws s₂ I.B I.Z I.W :=
    h.ws.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (k₁.trans k₂) (by decide)
  refine WP.mono (InvLaw.inverseN_ok h₂ h.z26 ((k₂.gpr (by decide)).trans h9) h13 hn1 hnw
    (by have := h.w20; omega_using [hnw, this]) hU hV hX₂ hM dVX₂) fun t ⟨_, hf, kt, hv⟩ => ?_
  rw [hm] at hf hv
  have k : Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t :=
    ((k₁.trans k₂).trans kt).mono (by decide)
  have f : KF I.B I.W [.arr iV, .arr iX₂, .priv] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.priv, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  refine ⟨h.step f ?_ k (by decide), f, k, fun hu hmm => ?_⟩
  · simp only [List.all_cons, List.all_nil, Rc.mut, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega_arith
  · rw [wv_low_of_lt hnw hu, wv_low_of_lt hnw hmm] at hv
    exact hv

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

end

/-!
# An RSA key from its primes on x86-64: the primes

The loads of `p`, `q` and `e` (`loads_k`), `p` and `q` ordered (`order_k`),
and `p − 1` and `q − 1` (`decTo_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE kE kElen)

theorem sxM1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem maskNot (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by cases b <;> decide

/-- A header slot the pieces may change, written. -/
theorem KS.hdrW {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) {i : Nat} (hi : 29 ≤ i ∧ i < 32)
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off I.B (8 * i)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) :
    KS I m₀ t ∧ KF I.B I.W [.hdr i] s.mem t.mem ∧ word t.mem I.B (8 * i) = v := by
  have hn := h.ws.scr.nowrap
  have := h.ws.h256
  have o := writeW_outside s.mem I.B v (d := 8 * i) (by omega_arith)
  rw [← hm] at o
  have f : KF I.B I.W [.hdr i] s.mem t.mem := KF.of_outside o (.hdr i) (List.mem_singleton_self _)
    (by simp [Rc.range]) (by simp [Rc.range])
  exact ⟨h.step f (by simp [Rc.mut, hi.1, hi.2]) k hr, f, by rw [hm, word_writeW_self]⟩

/-! ## The loads -/

/-- `p`, `q` (`pl` octets each) into `aPa` and `aQa`, and `e` into `kEv`. -/
theorem loads_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hpl : I.pb.length = I.pl)
    (hql : I.qb.length = I.pl) (hel : I.eb.length = I.el) (hpl1 : 1 ≤ I.pl) (hplW : I.pl ≤ 8 * I.W)
    (hel1 : 1 ≤ I.el) (hel8 : I.el ≤ 8) :
    WP isa (seqs (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa)))))) s
      fun t => KS I m₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa, .hdr kEv] s.mem t.mem ∧
        av I t.mem aPa = Spec.Rsa.os2ip I.pb ∧ av I t.mem aQa = Spec.Rsa.os2ip I.qb ∧
        word t.mem I.B (8 * kEv) = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
  have hZ := h.hZ
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (j := aPa) (by decide)
    (by decide) (by decide) h.args.pp h.args.pl h.p hpl hpl1 hplW) fun s₁ ⟨v₁, o₁, k₁⟩ => ?_)
  have f₁ := KF.arr1 (I := I) (j := aPa) o₁ (Nat.le_refl _) (Nat.le_refl _)
  have h₁ := h.step f₁ (all_mut_arr (by decide)) k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadE]) (WP.mono (loadA_ok h₁.ws (j := aQa) (by decide)
    (by decide) (by decide) h₁.args.qp h₁.args.pl h₁.q hql hpl1 hplW) fun s₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have f₂ := KF.arr1 (I := I) (j := aQa) o₂ (Nat.le_refl _) (Nat.le_refl _)
  have h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂ (by decide)
  obtain ⟨hg, hZ8⟩ := h₂.ws.good
  refine wp_seqs_append (by simp [loadE]) (by simp) (WP.mono (loadE_ok hg hZ8 h₂.args.e
    (by rw [h₂.args.el, hel]) (by omega_arith) (by omega_arith) h₂.e) fun s₃ ⟨hbx, m₃, k₃⟩ => ?_)
  have h₃ := h₂.step (cs := []) (by rw [m₃]; exact KF.refl _ _ _) rfl k₃ (by decide)
  simp only [seqs]
  have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega_arith)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
    (BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb))) (by
      have hbx' : s₃.gpr .rbx = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
        rw [← hbx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hst, hbx']) rfl) fun t ⟨hm, k₄⟩ => ?_
  obtain ⟨ht, f₄, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega_arith) hm k₄ (by decide)
  have hok : [Rc.arr aPa, Rc.arr aQa, Rc.hdr kEv].all Rc.ok = true := by decide
  refine ⟨ht, ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono (by simp), ?_, ?_, hw⟩
  · dsimp only [av]
    rw [f₄.arr (by decide) (j := aPa) (by decide) (by decide) h.hZ, m₃,
      f₂.arr (by decide) (j := aPa) (by decide) (by decide) h.hZ]; exact v₁
  · dsimp only [av]
    rw [f₄.arr (by decide) (j := aQa) (by decide) (by decide) h.hZ, m₃]; exact v₂

/-! ## The order -/

/-- `order`: `p` and `q` swapped if `p < q`. -/
theorem order_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (seqs order) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem ∧
      av I t.mem aPa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aQa else av I s.mem aPa) ∧
      av I t.mem aQa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aPa else av I s.mem aQa) := by
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl (j := aPa) (by decide)
  have sQ := h.ws.sl (j := aQa) (by decide)
  have sp := slot_far (w := I.W) (i := aPa) (j := aQa) (by decide)
  unfold order
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h (a := aPa) (b := aQa) (by decide) (by decide))
    fun s₁ ⟨h₁, m₁, hbp, hbx, h10, h12, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (decide (av I s.mem aPa < av I s.mem aQa)) ∧
    t.mem = s₁.mem) (by xrun [hbp]) rfl) fun s₂ ⟨⟨h15, m₂⟩, k₂⟩ => ?_)
  refine WP.mono (cswap_ok (h₁.ws.scr.congr k₂.2.2) ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h10)
    h15 ((k₂.gpr (by decide)).trans h12) (by have := h.ws.w1; omega_arith) (by have := h.ws.w2; omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t ⟨hX, hY, hf, k₃⟩ => ?_
  have f : KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem := by
    rw [m₂, m₁] at hf
    exact KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aPa, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
      · exact ⟨.arr aQa, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_arith⟩
  rw [m₂, m₁] at hX hY
  refine ⟨h.step f (all_mut_arrs (js := [aPa, aQa]) (by decide)) ((k₁.trans k₂).trans k₃) (by decide), f, ?_, ?_⟩
  · dsimp only [av]; rw [hX]; split <;> simp_all
  · dsimp only [av]; rw [hY]; split <;> simp_all

/-! ## Minus one -/

theorem dec_arith {x y L : Nat} {b : Bool} (hx : x < L)
    (hv : x + (if (!decide (y = 0)) = true then 1 else 0) = y + L * b.toNat) : x = y - 1 := by
  by_cases hz : y = 0
  · simp only [hz, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_add] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega_arith
  · simp only [hz, decide_false, Bool.not_false, ite_true] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega_arith

/-- `decTo o j`: `[o] := [j] − 1` (0 for 0), with word `W` zero. -/
theorem decTo_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o j : Nat} (ho : o < 16) (hj : j < 16)
    (hoj : o ≠ j) (hoC : o ≠ aC) (hjC : j ≠ aC) :
    WP isa (seqs (decTo o j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o, .arr aC] s.mem t.mem ∧
      av I t.mem o = av I s.mem j - 1 ∧ atop I t.mem o = 0 := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have e : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (eqMask j aC ++
      ([.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]] ++ (constA 1 ++ subC o o)))) := by
    simp only [decTo, subC, List.append_assoc]
  rw [e]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h ho hj hoj) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₁ 0) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have hok : [Rc.arr aC].all Rc.ok = true := by decide
  have cz : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₂ (a := j) (b := aC) hj (by decide))
    fun s₃ ⟨h₃, m₃, hbp, _, k₃⟩ => ?_)
  have vj : av I s₂.mem j = av I s.mem j := by
    dsimp only [av]
    rw [f₂.arr hok hj (by simp [hjC]) hZ]
    exact f₁.arr (by simp [Rc.ok, ho]) hj (by simp [hoj.symm]) hZ
  rw [cz, vj] at hbp
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!decide (av I s.mem j = 0)) ∧ t.mem = s₃.mem)
    (by xrun [hbp, sxM1, maskNot]) rfl) fun s₄ ⟨⟨h15, m₄⟩, k₄⟩ => ?_
  have h₄ := h₃.step (cs := []) (by rw [m₄]; exact KF.refl _ _ _) rfl k₄ (by decide)
  refine wp_seqs_append (by simp [constA]) (by simp [subC]) (WP.mono (constA_k h₄ 1) fun s₅ ⟨h₅, f₅, c₅, k₅⟩ => ?_)
  have c1 : av I s₅.mem aC = 1 := av_of_full c₅ (Nat.one_lt_two_pow (by have := h.ws.w1; omega_arith))
  refine WP.mono (subC_k h₅ (o := o) (a := o) ho ho hoC hoC (.inl rfl) (c := !decide (av I s.mem j = 0))
    (by rw [(k₅.gpr (by decide)), h15])) fun t ⟨ht, f₆, hb, t₆, _⟩ => ?_
  obtain ⟨b, hv⟩ := hb
  have vo : av I s₅.mem o = av I s.mem j := by
    dsimp only [av]
    rw [f₅.arr hok ho (by simp [hoC]) hZ, m₄, m₃, f₂.arr hok ho (by simp [hoC]) hZ]; exact v₁
  have tO : atop I s₅.mem o = 0 := by
    dsimp only [atop]
    rw [f₅.top hok ho (by simp [hoC]) hZ, m₄, m₃, f₂.top hok ho (by simp [hoC]) hZ]; exact t₁
  refine ⟨ht, ((((f₁.trans f₂).trans (by rw [← m₃, ← m₄]; exact f₅)).trans f₆)).mono (by simp), ?_, by rw [t₆]; exact tO⟩
  rw [c1, vo] at hv
  exact dec_arith (wv_lt t.mem I.B (slot I.W o) I.W) hv

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

/-!
# An RSA key from its primes on x86-64: `φ` and the halving

`φ = (p − 1)(q − 1)` (`phi_k`), and the `64 W` steps that halve `u`, `v` and
`φ` while `u` and `v` are both even (`twos_k`, `halveIter`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## `φ` -/

theorem ofNat_shr1 {W : Nat} (hW : W < 2 ^ 64) : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

theorem ofNat_sub' {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega_arith)]
  omega_arith

/-- `phi`: `[aL] := [aPm] [aQm]`, `w` words each, for `W = 2 w`. -/
theorem phi_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs phi) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aL] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aL) (I.W + 2) = a * b := by
  have hn := h.ws.scr.nowrap
  obtain sP := h.ws.sl (j := aPm) (by decide)
  obtain sQ := h.ws.sl (j := aQm) (by decide)
  obtain sL := h.ws.sl (j := aL) (by decide)
  obtain p1 := slot_far (w := I.W) (i := aPm) (j := aL) (by decide)
  obtain p2 := slot_far (w := I.W) (i := aQm) (j := aL) (by decide)
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  simp only [phi, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aL) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  obtain hok : [Rc.arr aL].all Rc.ok = true := by decide
  obtain va : wv s₁.mem I.B (slot I.W aPm) w = a := by
    rw [f₁.wv hok (j := aPm) (by decide) (by decide) (Nat.le_refl _) (by omega_arith) h.hZ, ← ha]
    dsimp only [av] at ha
    exact wv_low_of_lt (by omega_arith) (by rw [ha]; exact ha')
  obtain vb : wv s₁.mem I.B (slot I.W aQm) w = b := by
    rw [f₁.wv hok (j := aQm) (by decide) (by decide) (Nat.le_refl _) (by omega_arith) h.hZ, ← hb]
    dsimp only [av] at hb
    exact wv_low_of_lt (by omega_arith) (by rw [hb]; exact hb')
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  obtain hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h₁.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok aPm (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQm (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aL (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  obtain h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  obtain hax₅ : s₅.gpr .rax = off I.B (slot I.W aQm) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQm) ∧
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega_arith)]
    refine ⟨by rw [hW]; congr 1; omega_arith, ?_⟩
    rw [ofNat_sub' (by omega_arith) (by omega_arith)]; congr 1; omega_arith) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  obtain k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  obtain hm₆ : s₆.mem = s₁.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  obtain hz₆ : wv s₆.mem I.B (slot I.W aL) (w + w + 2) = 0 := by rw [hm₆, ← z₁]; congr 1; omega_arith
  refine WP.mono (mulRows_ok (h₁.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₇⟩ => ?_
  rw [hz₆, hm₆, va, vb, Nat.zero_add] at hv
  rw [hm₆] at o
  obtain f := KF.arr1 (I := I) (j := aL) o (Nat.le_refl _) (by omega_arith)
  refine ⟨h₁.step f (all_mut_arr (by decide)) (k26.trans k₇) (by decide), (f₁.trans f).mono (by decide), ?_⟩
  rw [show I.W + 2 = w + w + 2 by omega_arith]; exact hv

/-! ## Halving -/

theorem shr_half {X x0 y : Nat} (h : y * 2 + x0 % 2 = X) (hx : X % 2 = x0 % 2) : y = X / 2 := by omega_arith

/-- `halfIf j`: `[j] := [j] / 2` if `sMo` is the mask of `c`, for word `W`
of `[j]` zero. -/
theorem halfIf_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (hmo : word s.mem I.B (8 * sMo) = mask c) (htop : atop I s.mem j = 0) :
    WP isa (seqs (halfIf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j / 2 else av I s.mem j) ∧ atop I t.mem j = 0 ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  obtain sj := h.ws.sl hj
  obtain sT := h.ws.sl (j := aT) (by decide)
  obtain sp := slot_far (w := I.W) hjT
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  have hZ := h.hZ
  simp only [halfIf, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.seq (WP.mono (shr_ok (h.ws.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) hw1
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at hv₃ o₃
  obtain f₃ := KF.arr1 (I := I) (j := aT) o₃ (Nat.le_refl _) (by omega_arith)
  obtain h₃ := h.step f₃ (all_mut_arr (by decide)) ((k₁.trans k₂).trans k₃) (by decide)
  have htop' : word s.mem I.B (slot I.W j + 8 * I.W) = 0 := htop
  rw [htop'] at hv₃
  obtain hT₃ : av I s₃.mem aT = av I s.mem j / 2 := by
    refine shr_half (x0 := (word s.mem I.B (slot I.W j)).toNat) (by simpa using hv₃) ?_
    rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  obtain hok : [Rc.arr aT].all Rc.ok = true := by decide
  obtain hj₃ : av I s₃.mem j = av I s.mem j := f₃.arr hok hj (by simp [hjT]) hZ
  obtain tj₃ : atop I s₃.mem j = 0 := by rw [← htop]; exact f₃.top hok hj (by simp [hjT]) hZ
  obtain hmo₃ : word s₃.mem I.B (8 * sMo) = mask c := by rw [f₃.word hok (by decide) (by decide), hmo]
  obtain k13 := (k₁.trans k₂).trans k₃
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!c) ∧
      t.mem = s₃.mem) (by
    obtain hl := h₃.ws.scr.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_arith)
    xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hl, hmo₃, sxM1, maskNot]) rfl) fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₄.gpr (by decide)).trans h₃.ws.rdi) ((k₄.gpr (by decide)).trans (((k₂.trans k₃).gpr (by decide)).trans h9))
      (by decide)) fun s₅ ⟨h8₅, hsi₅, m₅, k₅⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr ((k13.trans k₄).trans k₅).2.2) h8₅ hsi₅ ((k₅.gpr (by decide)).trans hbp)
    (((k₄.trans k₅).gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨hv, o, k₆⟩ => ?_
  rw [m₅, m₄] at hv o
  obtain f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega_arith)
  refine ⟨h₃.step f (all_mut_arr hj) ((k₄.trans k₅).trans k₆) (by decide), (f₃.trans f).mono (by simp), ?_, ?_,
    (((k13.trans k₄).trans k₅).trans k₆).mono (by decide)⟩
  · dsimp only [av] at hv ⊢; rw [hv]
    cases c <;> simp only [Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true]
    · exact hj₃
    · exact hT₃
  · dsimp only [atop]; rw [o.word (Or.inr (Nat.le_refl _)) (by omega_arith)]; exact tj₃

theorem and1_ofNat (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega_arith

/-- The mask of `x` and `y` both even. -/
theorem twoMask (x y : BitVec 64) :
    ((x ||| y) &&& 1) - 1 = mask (decide (x.toNat % 2 = 0 ∧ y.toNat % 2 = 0)) := by
  rw [BitVec.and_or_distrib_right, and1_ofNat, and1_ofNat]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> rw [hx, hy] <;> decide

/-- `add r13, 1; cmp r13, r11`. -/
theorem countP_ok (s : State) {j N : Nat} (hj : s.gpr .r13 = BitVec.ofNat 64 j)
    (hN : s.gpr .r11 = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block countP) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ Keep [.r13] s s' := by
  refine WP.mono (WP.keep [.r13] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold countP
  xrun [hj, hN, ofNat_add_one, ofNat_sub_beq hjN hN']

/-- What a step of the halving keeps and changes. -/
def TwoP (I : KIn) (m₀ : Mem) (s t : State) : Prop :=
  KS I m₀ t ∧ KF I.B I.W [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] s.mem t.mem ∧
    atop I t.mem aU = 0 ∧ atop I t.mem aV = 0 ∧ atop I t.mem aL = 0

/-- One step of the halving, and the count. -/
theorem twoStep_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) {j : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 j)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (64 * I.W)) (hj : j < 64 * I.W) :
    WP isa twoStep s fun t => t.zf = some (decide (j + 1 = 64 * I.W)) ∧ t.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧
      t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ TwoP I m₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveStep (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hn := h.ws.scr.nowrap
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  have hZ := h.hZ
  obtain sU := h.ws.sl (j := aU) (by decide)
  obtain sV := h.ws.sl (j := aV) (by decide)
  unfold twoStep
  simp only [List.append_assoc]
  -- The mask of both even into `sMo`.
  generalize hc : decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0) = c
  obtain hb : WP isa (.block (ws ++ base aU .rbx ++ base aV .r10 ++ [.mov .rax (.mem (at0 .rbx)),
      .alu .or .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1), .store (hdr sMo) .rax])) s
      fun t => t.mem = s.mem.writeW (off I.B (8 * sMo)) (mask c) ∧ Keep [.r12, .r9, .rbx, .r10, .rax] s t := by
    rw [List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
    obtain hdi₁ : s₁.gpr .rdi = I.B := (k₁.gpr (by decide)).trans h.ws.rdi
    refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₁ h9) fun s₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
      ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => ?_
    obtain hs₃ := h.ws.scr.congr ((k₁.trans k₂).trans k₃).2.2
    obtain hbx₃ : s₃.gpr .rbx = off I.B (slot I.W aU) := (k₃.gpr (by decide)).trans hbx
    obtain hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans hdi₁
    obtain hm₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
    obtain eU : (s.mem.readW (off I.B (slot I.W aU)) 64).toNat % 2 = av I s.mem aU % 2 := by
      rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
    obtain eV : (s.mem.readW (off I.B (slot I.W aV)) 64).toNat % 2 = av I s.mem aV % 2 := by
      rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
    obtain hmask : ((s.mem.readW (off I.B (slot I.W aU)) 64 ||| s.mem.readW (off I.B (slot I.W aV)) 64) &&& 1) -
        1 = mask c := by
      rw [twoMask, eU, eV, hc]
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * sMo)) (mask c)) (by
      xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₃.ld (d := slot I.W aU) (by omega_arith), hs₃.ld (d := slot I.W aV) (by omega_arith),
        hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_arith), hm₃, hmask]) rfl)
      fun t ⟨hm, k₄⟩ => ⟨hm, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  refine wp_seqs_append (by simp) (by simp [halfIf]) (WP.mono hb fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain ⟨h₁, f₁, hmo₁⟩ := h.hdrW (i := sMo) (by unfold sMo sFn; omega_arith) hm₁ k₁ (by decide)
  obtain hok1 : [Rc.hdr sMo].all Rc.ok = true := by decide
  obtain tU₁ : atop I s₁.mem aU = 0 := by rw [← hU0]; exact f₁.top hok1 (by decide) (by decide) hZ
  obtain tV₁ : atop I s₁.mem aV = 0 := by rw [← hV0]; exact f₁.top hok1 (by decide) (by decide) hZ
  obtain tL₁ : atop I s₁.mem aL = 0 := by rw [← hL0]; exact f₁.top hok1 (by decide) (by decide) hZ
  obtain vU₁ : av I s₁.mem aU = av I s.mem aU := f₁.arr hok1 (by decide) (by decide) hZ
  obtain vV₁ : av I s₁.mem aV = av I s.mem aV := f₁.arr hok1 (by decide) (by decide) hZ
  obtain vL₁ : av I s₁.mem aL = av I s.mem aL := f₁.arr hok1 (by decide) (by decide) hZ
  -- `u`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₁ (j := aU) (by decide)
    (by decide) hmo₁ tU₁) fun s₂ ⟨h₂, f₂, vU₂, tU₂, k₂⟩ => ?_)
  obtain hok2 : [Rc.arr aU, Rc.arr aT].all Rc.ok = true := by decide
  obtain hmo₂ : word s₂.mem I.B (8 * sMo) = mask c := by rw [f₂.word hok2 (by decide) (by decide), hmo₁]
  obtain tV₂ : atop I s₂.mem aV = 0 := by rw [← tV₁]; exact f₂.top hok2 (by decide) (by decide) hZ
  obtain tL₂ : atop I s₂.mem aL = 0 := by rw [← tL₁]; exact f₂.top hok2 (by decide) (by decide) hZ
  obtain vV₂ : av I s₂.mem aV = av I s.mem aV := by rw [← vV₁]; exact f₂.arr hok2 (by decide) (by decide) hZ
  obtain vL₂ : av I s₂.mem aL = av I s.mem aL := by rw [← vL₁]; exact f₂.arr hok2 (by decide) (by decide) hZ
  -- `v`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₂ (j := aV) (by decide)
    (by decide) hmo₂ tV₂) fun s₃ ⟨h₃, f₃, vV₃, tV₃, k₃⟩ => ?_)
  obtain hok3 : [Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  obtain hmo₃ : word s₃.mem I.B (8 * sMo) = mask c := by rw [f₃.word hok3 (by decide) (by decide), hmo₂]
  obtain tU₃ : atop I s₃.mem aU = 0 := by rw [← tU₂]; exact f₃.top hok3 (by decide) (by decide) hZ
  obtain tL₃ : atop I s₃.mem aL = 0 := by rw [← tL₂]; exact f₃.top hok3 (by decide) (by decide) hZ
  obtain vU₃ : av I s₃.mem aU = av I s₂.mem aU := f₃.arr hok3 (by decide) (by decide) hZ
  obtain vL₃ : av I s₃.mem aL = av I s.mem aL := by rw [← vL₂]; exact f₃.arr hok3 (by decide) (by decide) hZ
  -- `φ`.
  refine wp_seqs_append (by simp [halfIf]) (by simp) (WP.mono (halfIf_k h₃ (j := aL) (by decide)
    (by decide) hmo₃ tL₃) fun s₄ ⟨h₄, f₄, vL₄, tL₄, k₄⟩ => ?_)
  obtain hok4 : [Rc.arr aL, Rc.arr aT].all Rc.ok = true := by decide
  obtain tU₄ : atop I s₄.mem aU = 0 := by rw [← tU₃]; exact f₄.top hok4 (by decide) (by decide) hZ
  obtain tV₄ : atop I s₄.mem aV = 0 := by rw [← tV₃]; exact f₄.top hok4 (by decide) (by decide) hZ
  obtain vU₄ : av I s₄.mem aU = av I s₂.mem aU := by rw [← vU₃]; exact f₄.arr hok4 (by decide) (by decide) hZ
  obtain vV₄ : av I s₄.mem aV = av I s₃.mem aV := f₄.arr hok4 (by decide) (by decide) hZ
  obtain k14 := ((k₁.trans k₂).trans k₃).trans k₄
  simp only [seqs]
  refine WP.mono (countP_ok s₄ ((k14.gpr (by decide)).trans h13) ((k14.gpr (by decide)).trans h11) (by omega_arith)
    (by omega_arith)) fun t ⟨hz, h13', hm, k₅⟩ => ⟨hz, h13', (k₅.gpr (by decide)).trans ((k14.gpr (by decide)).trans h11),
      ⟨h₄.step (cs := []) (by rw [hm]; exact KF.refl _ _ _) rfl k₅ (by decide),
        by rw [hm]; exact ((((f₁.trans f₂).trans f₃).trans f₄)).mono (by decide),
        by rw [hm]; exact tU₄, by rw [hm]; exact tV₄, by rw [hm]; exact tL₄⟩, ?_⟩
  rw [hm, vU₄, vU₂, vV₄, vV₃, vL₄, vU₁, vV₂, vL₃]
  unfold halveStep
  dsimp only
  rw [← hc]
  by_cases hb : av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false]

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

/-!
# An RSA key from its primes on x86-64: `lcm(p − 1, q − 1)`

The halving's loop (`twos_k`), `gcd(u, v)` after it (`gcdUV_k`), and
`lcmPart` (`lcm_k`): `[aL] := lcm(p − 1, q − 1)` (`lcm_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## The loop -/

/-- `divInit t`: `r11 := 64 W`, `r13 := 0`. -/
theorem divInit_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (iT : Nat) :
    WP isa (.block (divInit iT)) s fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧
      t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧ Keep [.r12, .r9, .r8, .r11, .r13] s t := by
  rw [divInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  refine WP.mono (base_ok iT (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi) h9) fun s₂ ⟨_, m₂, k₂⟩ => ?_
  obtain e12 : s₂.gpr .r12 = BitVec.ofNat 64 I.W := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 I.W ∧ t.mem = s₂.mem)
    (by xrun [e12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.mem = s₃.mem)
    (by
      xrun [h11, ofNat_dbl, List.replicate]
      congr 1; omega_using []) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
    (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
  exact ⟨(k₅.gpr (by decide)).trans h11', h13, by rw [m₅, m₄, m₃, m₂, m₁],
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩

theorem TwoP.trans {I : KIn} {m₀ : Mem} {s t u : State} (h₁ : TwoP I m₀ s t) (h₂ : TwoP I m₀ t u) :
    TwoP I m₀ s u :=
  ⟨h₂.1, (h₁.2.1.trans h₂.2.1).mono (by decide), h₂.2.2⟩

/-- `twos`: `64 W` steps of the halving. -/
theorem twos_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa (seqs twos) s fun t => TwoP I m₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) =
        halveIter (64 * I.W) (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  simp only [twos, seqs]
  refine WP.seq (WP.mono (divInit_k h aT) fun s₁ ⟨h11, h13, m₁, k₁⟩ => ?_)
  obtain h₁ := h.step (cs := []) (by rw [m₁]; exact KF.refl _ _ _) rfl k₁ (by decide)
  refine wp_upto (a := 0) (N := 64 * I.W) (by omega_using [hw1])
    (fun j t => t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.gpr .r13 = BitVec.ofNat 64 j ∧ TwoP I m₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveIter j (av I s.mem aU, av I s.mem aV, av I s.mem aL))
    (fun j _ hj t ⟨t11, t13, tp, tv⟩ => ?_) (fun t ⟨_, _, tp, tv⟩ => ⟨tp, tv⟩)
    ⟨h11, h13, ⟨h₁, by rw [m₁]; exact (KF.refl _ _ _).mono (by decide), by rw [m₁]; exact hU0, by rw [m₁]; exact hV0,
      by rw [m₁]; exact hL0⟩, by rw [m₁]; rfl⟩
  refine WP.mono (twoStep_k tp.1 tp.2.2.1 tp.2.2.2.1 tp.2.2.2.2 t13 t11 hj) fun t' ⟨hz, h13', h11', tp', tv'⟩ =>
    ⟨hz, h11', h13', tp.trans tp', ?_⟩
  rw [tv', tv, halveIter_succ']

/-! ## `gcd(u, v)` -/

theorem ite_not_odd {α : Sort _} (v : Nat) (a b : α) :
    (if (!decide (v % 2 = 1)) = true then a else b) = (if v % 2 = 0 then a else b) := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

theorem gcdUV_eq : gcdUV = ([.block (oddMask aV ++ ([.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++
      base aU .rbx ++ base aV .r10), wordLoop 0 cswapBody] : List (Prog isa)) ++ (constA 2 ++ (ltA aV aC ++
    (([.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++ (constA 3 ++ (selC aV ++
    ([zeroA aM, copyA aM aV, inverseK kHalf aU aV aX₂ aM] ++
    (constA 1 ++ (([.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++
      selC aV)))))))) := by
  simp only [gcdUV, List.append_assoc]

/-- `gcdUV`: `v` made odd by a swap, then `[aV] := gcd(u, v)`, or 1 for
`v ≤ 1`, for an odd `v` unless `v ≤ 1`. -/
theorem gcdUV_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hU0 : atop I s.mem aU = 0)
    (hw : 1 ≤ I.W / 2) (hUb : av I s.mem aU < 2 ^ (64 * (I.W / 2))) (hVb : av I s.mem aV < 2 ^ (64 * (I.W / 2)))
    (hodd : let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV; 2 ≤ v → v % 2 = 1) :
    WP isa (seqs gcdUV) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk, .priv]
        s.mem t.mem ∧
      av I t.mem aV =
        (let u := if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU
         let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV
         if v ≤ 1 then 1 else Nat.gcd u v) := by
  have hn := h.ws.scr.nowrap
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  have hZ := h.hZ
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  have spUV := slot_far (w := I.W) (i := aU) (j := aV) (by decide)
  generalize hu0 : av I s.mem aU = u0 at hodd hUb
  generalize hv0 : av I s.mem aV = v0 at hodd hVb
  generalize hu1 : (if v0 % 2 = 0 then v0 else u0) = u1
  generalize hv1 : (if v0 % 2 = 0 then u0 else v0) = v1 at hodd
  dsimp only at hodd ⊢
  rw [gcdUV_eq]
  -- The swap.
  have hb : WP isa (.block (oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++
      base aU .rbx ++ base aV .r10)) s fun t => t.mem = s.mem ∧ t.gpr .r15 = mask (!decide (v0 % 2 = 1)) ∧
      t.gpr .rbx = off I.B (slot I.W aU) ∧ t.gpr .r10 = off I.B (slot I.W aV) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .r15, .r10] s t := by
    simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aV) (by decide)) fun s₁ ⟨m₁, hax, h12, h9, k₁⟩ => ?_)
    rw [hv0] at hax
    refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!decide (v0 % 2 = 1)) ∧
      t.mem = s₁.mem) (by xrun [hax, sxM1, maskNot]) rfl) fun s₂ ⟨⟨h15, m₂⟩, k₂⟩ => WP.block_append_iff.mpr ?_)
    have hdi₂ : s₂.gpr .rdi = I.B := ((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi
    have h9₂ : s₂.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := (k₂.gpr (by decide)).trans h9
    refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₂ h9₂) fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
    refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
      ((k₃.gpr (by decide)).trans h9₂)) fun t ⟨h10, m₄, k₄⟩ => ⟨by rw [m₄, m₃, m₂, m₁],
        ((k₃.trans k₄).gpr (by decide)).trans h15, (k₄.gpr (by decide)).trans hbx, h10,
        (((k₂.trans k₃).trans k₄).gpr (by decide)).trans h12, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono hb fun s₁ ⟨m₁, h15, hbx, h10, h12, k₁⟩ => ?_)
  refine WP.mono (cswap_ok (h.ws.scr.congr k₁.2.2) hbx h10 h15 h12 (by omega_using [hw1]) (by omega_using [hw2])
      (by omega_using [sU]) (by omega_using [sV])
    (by omega_using [spUV])) fun s₂ ⟨hX, hY, hf, k₂⟩ => ?_
  have hu0' : wv s.mem I.B (slot I.W aU) I.W = u0 := hu0
  have hv0' : wv s.mem I.B (slot I.W aV) I.W = v0 := hv0
  rw [m₁, hu0', hv0', ite_not_odd, hu1] at hX
  rw [m₁, hu0', hv0', ite_not_odd, hv1] at hY
  have f₂ : KF I.B I.W [.arr aU, .arr aV] s.mem s₂.mem := by
    rw [m₁] at hf
    exact KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_using []⟩
      · exact ⟨.arr aV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_using []⟩
  have h₂ := h.step f₂ (all_mut_arrs (js := [aU, aV]) (by decide)) (k₁.trans k₂) (by decide)
  have tU₂ : atop I s₂.mem aU = 0 := by
    rw [← hU0]
    dsimp only [atop]
    rw [m₁] at hf
    exact hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_using [spUV]) (by omega_using [hn, sU])
  -- `kOk := ` the mask of `v ≤ 1`.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₂ 2) fun s₃ ⟨h₃, f₃, c₃, _⟩ => ?_)
  have hokC : [Rc.arr aC].all Rc.ok = true := by decide
  have c2 : av I s₃.mem aC = 2 := av_of_full c₃ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega_using [hw1])))
  have vV₃ : av I s₃.mem aV = v1 := by rw [← hY]; exact f₃.av hokC (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₃ (a := aV) (b := aC) (by decide) (by decide))
    fun s₄ ⟨h₄, m₄, hbp, _, _, _, k₄⟩ => ?_)
  rw [vV₃, c2] at hbp
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  have hst := h₄.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₄.mem.writeW (off I.B (8 * kOk)) (mask (decide (v1 < 2))) ∧
    t.gpr .rbp = mask (!decide (v1 < 2))) (by xrun [State.ea, hdr, h₄.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun s₅ ⟨⟨hm₅, hbp₅⟩, k₅⟩ => ?_
  obtain ⟨h₅, f₅, ok₅⟩ := h₄.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) hm₅ k₅ (by decide)
  have hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  -- `[aV] := 3` for `v ≤ 1`.
  refine wp_seqs_append (by simp [constA]) (by simp [selC]) (WP.mono (constA_k h₅ 3) fun s₆ ⟨h₆, f₆, c₆, k₆⟩ => ?_)
  have c3 : av I s₆.mem aC = 3 := av_of_full c₆ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega_using [hw1])))
  have vV₆ : av I s₆.mem aV = v1 := by
    rw [← vV₃, f₆.av hokC (by decide) (by decide) hZ, f₅.av hokO (by decide) (by decide) hZ, m₄]
  refine wp_seqs_append (by simp [selC]) (by simp) (WP.mono (selC_k h₆ (j := aV) (by decide) (by decide)
    (c := !decide (v1 < 2)) (by rw [k₆.gpr (by decide), hbp₅])) fun s₇ ⟨h₇, f₇, vV₇, _, _⟩ => ?_)
  rw [vV₆, c3] at vV₇
  generalize hM : (if (!decide (v1 < 2)) = true then v1 else 3) = M at vV₇
  have hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]
    by_cases hv : v1 < 2
    · simp [hv]
    · simp only [hv, decide_false, Bool.not_false, ite_true]; exact ⟨hodd (by omega_using [hv]), by omega_using [hv]⟩
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aM) (by decide)) fun s₇' ⟨h₇', f₇', _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₇' (o := aM) (a := aV) (by decide) (by decide) (by decide))
    fun s₈ ⟨h₈, f₈', vM₈, _, _⟩ => ?_))
  have f₈ : KF I.B I.W [.arr aM] s₇.mem s₈.mem := (f₇'.trans f₈').mono (by decide)
  rw [f₇'.av (by decide) (j := aV) (by decide) (by decide) hZ] at vM₈
  have hokM : [Rc.arr aM].all Rc.ok = true := by decide
  have vU₈ : av I s₈.mem aU = u1 := by
    rw [f₈.av hokM (by decide) (by decide) hZ, ← hX,
      f₇.av (by decide) (j := aU) (by decide) (by decide) hZ, f₆.av hokC (by decide) (by decide) hZ,
      f₅.av hokO (by decide) (by decide) hZ, m₄, f₃.av hokC (by decide) (by decide) hZ]
  have vM₈' : av I s₈.mem aM = M := by rw [vM₈, vV₇]
  have hu1b : u1 < 2 ^ (64 * (I.W / 2)) := by rw [← hu1]; split <;> with_reducible assumption
  have hMb : M < 2 ^ (64 * (I.W / 2)) := by
    rw [← hM]; split
    · rw [← hv1]; split <;> with_reducible assumption
    · exact Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 64) (Nat.pow_le_pow_right (by decide) (by omega_using [hw]))
  refine WP.mono (inverseK_k h₈ (k := kHalf) (n := I.W / 2) (fun _ h12 hw20 => kHalf_ok h12 (by omega_using [hw2]))
    hw (by omega_using []) (iU := aU) (iV := aV) (iX₂ := aX₂) (iM := aM) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁₂ ⟨h₁₂, f₁₂, _, hinv⟩ => ?_
  rw [vM₈', vU₈] at hinv
  have hg := (hinv hu1b hMb hMo.1).1
  -- The result 1 for `v ≤ 1`.
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₁₂ 1) fun s₁₃ ⟨h₁₃, f₁₃, c₁₃, k₁₃⟩ => ?_)
  have c1 : av I s₁₃.mem aC = 1 := av_of_full c₁₃ (Nat.one_lt_two_pow (by omega_using [hw1]))
  have hokI : [Rc.arr aV, Rc.arr aX₂, Rc.priv].all Rc.ok = true := by decide
  have ok₁₃ : word s₁₃.mem I.B (8 * kOk) = mask (decide (v1 < 2)) := by
    rw [f₁₃.word hokC (by decide) (by decide), f₁₂.word hokI (by decide) (by decide),
      f₈.word hokM (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), f₆.word hokC (by decide) (by decide), ok₅]
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  have hl := h₁₃.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!decide (v1 < 2)) ∧ t.mem = s₁₃.mem)
    (by xrun [State.ea, hdr, h₁₃.ws.rdi, hdrOff, hl, ok₁₃, sxM1, maskNot]) rfl) fun s₁₄ ⟨⟨hbp₁₄, m₁₄⟩, k₁₄⟩ => ?_
  have h₁₄ := h₁₃.step (cs := []) (by rw [m₁₄]; exact KF.refl _ _ _) rfl k₁₄ (by decide)
  refine WP.mono (selC_k h₁₄ (j := aV) (by decide) (by decide) hbp₁₄) fun t ⟨ht, f₁₅, vV, _, _⟩ => ?_
  have f₅' : KF I.B I.W [.hdr kOk] s₃.mem s₅.mem := by rw [← m₄]; exact f₅
  have f₁₅' : KF I.B I.W [.arr aV] s₁₃.mem t.mem := by rw [← m₁₄]; exact f₁₅
  refine ⟨ht, ?_, ?_⟩
  · exact ((((((((f₂.trans f₃).trans f₅').trans f₆).trans f₇).trans f₈).trans
      f₁₂).trans f₁₃).trans f₁₅').mono (by decide)
  · rw [vV, m₁₄, c1, f₁₃.av hokC (by decide) (by decide) hZ, hg]
    by_cases hv : v1 < 2
    · simp [hv, show v1 ≤ 1 by omega_using [hv]]
    · simp only [hv, decide_false, Bool.not_false, ite_true, show ¬ v1 ≤ 1 by omega_using [hv], ite_false]
      rw [← hM]; simp [hv]

/-! ## The lcm -/

/-- Word `W` of a number of `W + 2` words below `2^(64 W)`. -/
theorem top_zero_of_lt {m : Mem} {B : Addr} {d W : Nat} (h : wv m B d (W + 2) < 2 ^ (64 * W)) :
    word m B (d + 8 * W) = 0 := by
  obtain e := wv_add m B d W 2
  have : wv m B (d + 8 * W) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (d + 8 * W) 2) with h0 | h0
    · exact h0
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * W)) h0; omega_using [h, e, this]
  have := (wv_eq_zero_iff _ _ _ _).mp this 0 (by decide)
  simpa using this

theorem lcmPart_eq : lcmPart = phi ++ ([zeroA aU, copyA aU aPm, zeroA aV, copyA aV aQm] ++ (twos ++ (gcdUV ++
    [divmod aL aR aV aT]))) := by
  simp only [lcmPart, List.append_assoc]

/-- `lcmPart`: `[aL] := lcm(a, b)` for `[aPm] = a` and `[aQm] = b`, below
`2^(64 w)`, `W = 2 w`. -/
theorem lcm_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs lcmPart) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr aL, .arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .arr aR, .hdr sMo,
        .hdr kOk, .priv] s.mem t.mem ∧ av I t.mem aL = Nat.lcm a b := by
  have hZ := h.hZ
  have hw1 := h.ws.w1
  obtain hab : a * b < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * w) = 64 * w + 64 * w by omega_using [], Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le ha' (by omega_using [hb']) (Nat.two_pow_pos _)
  rw [lcmPart_eq]
  refine wp_seqs_append (by simp [phi]) (by simp) (WP.mono (phi_k h hW ha hb ha' hb') fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  obtain hokL : [Rc.arr aL].all Rc.ok = true := by decide
  obtain vL₁ : av I s₁.mem aL = a * b := av_of_full v₁ hab
  obtain tL₁ : atop I s₁.mem aL = 0 := top_zero_of_lt (by rw [v₁]; exact hab)
  obtain vP₁ : av I s₁.mem aPm = a := by rw [f₁.av hokL (by decide) (by decide) hZ]; exact ha
  obtain vQ₁ : av I s₁.mem aQm = b := by rw [f₁.av hokL (by decide) (by decide) hZ]; exact hb
  refine wp_seqs_append (by simp) (by simp [twos]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, z₂, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aPm) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, t₃, _⟩ =>
      WP.seq (WP.mono (zeroA_k h₃ (j := aV) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _⟩ =>
        WP.mono (copyA_k h₄ (o := aV) (a := aQm) (by decide) (by decide) (by decide))
          fun s₅ ⟨h₅, f₅, v₅, t₅, _⟩ => ?_)))
  obtain hU : [Rc.arr aU].all Rc.ok = true := by decide
  obtain hV : [Rc.arr aV].all Rc.ok = true := by decide
  obtain vU₅ : av I s₅.mem aU = a := by
    rw [f₅.av hV (by decide) (by decide) hZ, f₄.av hV (by decide) (by decide) hZ, v₃,
      f₂.av hU (by decide) (by decide) hZ, vP₁]
  obtain vV₅ : av I s₅.mem aV = b := by
    rw [v₅, f₄.av hV (by decide) (by decide) hZ, f₃.av hU (by decide) (by decide) hZ,
      f₂.av hU (by decide) (by decide) hZ, vQ₁]
  obtain vL₅ : av I s₅.mem aL = a * b := by
    rw [f₅.av hV (by decide) (by decide) hZ, f₄.av hV (by decide) (by decide) hZ,
      f₃.av hU (by decide) (by decide) hZ, f₂.av hU (by decide) (by decide) hZ, vL₁]
  obtain tU₅ : atop I s₅.mem aU = 0 := by
    rw [f₅.at hV (by decide) (by decide) hZ, f₄.at hV (by decide) (by decide) hZ, t₃]; exact (wv_zero2 z₂).2
  obtain tV₅ : atop I s₅.mem aV = 0 := by rw [t₅]; exact (wv_zero2 z₄).2
  obtain tL₅ : atop I s₅.mem aL = 0 := by
    rw [f₅.at hV (by decide) (by decide) hZ, f₄.at hV (by decide) (by decide) hZ,
      f₃.at hU (by decide) (by decide) hZ, f₂.at hU (by decide) (by decide) hZ, tL₁]
  -- The halving.
  refine wp_seqs_append (by simp [twos]) (by simp [gcdUV]) (WP.mono (twos_k h₅ tU₅ tV₅ tL₅)
    fun s₆ ⟨⟨h₆, f₆, tU₆, tV₆, tL₆⟩, hv₆⟩ => ?_)
  rw [vU₅, vV₅, vL₅] at hv₆
  obtain hK : a < 2 ^ (64 * I.W) ∧ b < 2 ^ (64 * I.W) := by
    rw [hW]; exact ⟨Nat.lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by decide) (by omega_using [])),
      Nat.lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by decide) (by omega_using []))⟩
  obtain hle := lcm_eq hK.1 hK.2
  dsimp only at hle
  obtain hB := halveIter_bounds (64 * I.W) (st := (a, b, a * b)) (a := 2 ^ (64 * w)) (b := 2 ^ (64 * w))
    (f := 2 ^ (64 * I.W)) ⟨ha', hb', hab⟩
  generalize halveIter (64 * I.W) (a, b, a * b) = st at hv₆ hle hB
  obtain ⟨x, y, f⟩ := st
  simp only [Prod.mk.injEq] at hv₆
  obtain ⟨hx, hy, hf⟩ := hv₆
  dsimp only at hle hB
  obtain hW2 : I.W / 2 = w := by omega_using [hW]
  -- `gcd(u, v)`.
  refine wp_seqs_append (by simp [gcdUV]) (by simp) (WP.mono (gcdUV_k h₆ tU₆ (by rw [hW2]; omega_using [hw1, hW]) (by rw [hx, hW2]; exact hB.1)
    (by rw [hy, hW2]; exact hB.2.1) (by rw [hx, hy]; exact hle.1))
    fun s₇ ⟨h₇, f₇, vV₇⟩ => ?_)
  rw [hx, hy] at vV₇
  dsimp only at vV₇
  obtain hokG : [Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo,
    Rc.hdr kOk].all Rc.ok = true := by decide
  obtain vL₇ : av I s₇.mem aL = f := by rw [f₇.av hokG (by decide) (by decide) hZ, hf]
  generalize hg : (if (if y % 2 = 0 then x else y) ≤ 1 then 1 else
    Nat.gcd (if y % 2 = 0 then y else x) (if y % 2 = 0 then x else y)) = g at vV₇ hle
  obtain hg0 : 0 < g := by
    rw [← hg]
    generalize (if y % 2 = 0 then x else y) = v
    generalize (if y % 2 = 0 then y else x) = u
    by_cases hv : v ≤ 1
    · simp [hv]
    · simp only [hv, ite_false]; exact Nat.gcd_pos_of_pos_right _ (by omega_using [hv])
  simp only [seqs]
  refine WP.mono (divmod_k h₇ (iQ := aL) (iR := aR) (iD := aV) (iT := aT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ht, f₈, hd⟩ => ⟨ht, ?_, ?_⟩
  · have f₂₅ := ((f₂.trans f₃).trans f₄).trans f₅
    exact ((((f₁.trans f₂₅).trans f₆).trans f₇).trans f₈).mono (by decide)
  · rw [vV₇] at hd
    rw [(hd hg0).2, vL₇, hle.2]

end VG.Proof.RsaKeyGen.X86_64.Key
