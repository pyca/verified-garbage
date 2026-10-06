import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key

/-!
# An RSA key from its primes on AArch64: the state between the pieces

`KF B W cs`: memory that changes only in the arrays and header slots the
codes `cs` name, so that what a piece keeps is decided on the codes
(`KF.wv`, `KF.word`). `KS I s₀`: what every piece keeps, from the state
`s₀` on entry (the working space for `W` words, the arguments in the
header, the inputs, memory outside the working space, and every register
the code does not write), after a piece that changes only arrays and the
header slots 29 to 31 (`kEv`, `kOk`) and writes only registers of
`mmRegs` (`KS.step`, `KS.hdrW`).

The facts between the stages: `KPrimes` after `p − 1` and `q − 1`
(`Front.lean`), and `KFront` after `smallMask` (see `PLAN.md`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (kE kElen)

/-! ## Frames by codes -/

/-- A part of the working space: an array (`W + 2` words), or a header
slot. -/
inductive Rc where
  | arr (i : Nat)
  | hdr (i : Nat)
  deriving DecidableEq

/-- Its byte range, for arrays of `W + 2` words. -/
def Rc.range (W : Nat) : Rc → Nat × Nat
  | .arr i => (slot W i, 8 * (W + 2))
  | .hdr i => (8 * i, 8)

/-- One of the sixteen arrays, or of the header's 32 slots. -/
def Rc.ok : Rc → Bool
  | .arr i => decide (i < 16)
  | .hdr i => decide (i < 32)

/-- One the pieces may change: an array, or the header slots 29 to 31
(`kEv`, `kOk`). -/
def Rc.mut : Rc → Bool
  | .arr i => decide (i < 16)
  | .hdr i => decide (29 ≤ i ∧ i < 32)

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

/-- Memory that did not change. -/
theorem KF.of_eq {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (hm : m' = m) : KF B W cs m m' := by
  rw [hm]; exact (KF.refl _ _ _).mono (by simp)

/-- Ranges, each within a part of `cs`. -/
theorem KF.of_frm {B : Addr} {W : Nat} {rs : List (Nat × Nat)} {cs : List Rc} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, ∃ c ∈ cs, (c.range W).1 ≤ r.1 ∧ r.1 + r.2 ≤ (c.range W).1 + (c.range W).2) :
    KF B W cs m m' :=
  fun x hx => h x fun r hr' => by
    obtain ⟨c, hc, h1, h2⟩ := hr r hr'
    have := hx (c.range W) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    omega

theorem KF.of_outside {B : Addr} {W : Nat} {o n : Nat} {cs : List Rc} {m m' : Mem} (h : Outside B o n m m')
    (c : Rc) (hc : c ∈ cs) (h1 : (c.range W).1 ≤ o) (h2 : o + n ≤ (c.range W).1 + (c.range W).2) :
    KF B W cs m m' :=
  KF.of_frm (Frm.of_outside h (List.mem_singleton_self _)) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨c, hc, h1, h2⟩

/-- A change within array `j`. -/
theorem KF.arr1 {B : Addr} {W j o n : Nat} {m m' : Mem} (h : Outside B o n m m') (h1 : slot W j ≤ o)
    (h2 : o + n ≤ slot W j + 8 * (W + 2)) : KF B W [.arr j] m m' :=
  KF.of_outside h (.arr j) (List.mem_singleton_self _) h1 h2

/-- An array's range, against a part other than it. -/
theorem range_sep_arr {W j : Nat} {c : Rc} (hc : c.ok = true) (hne : c ≠ .arr j) {d k : Nat}
    (hd : slot W j ≤ d) (hdk : d + 8 * k ≤ slot W j + 8 * (W + 2)) :
    d + 8 * k ≤ (c.range W).1 ∨ (c.range W).1 + (c.range W).2 ≤ d := by
  cases c with
  | arr i =>
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    have := slot_sep (w := W) hij
    simp only [Rc.range]; omega
  | hdr i =>
    simp only [Rc.ok, decide_eq_true_eq] at hc
    have := hdr_lt_slot W j hc
    simp only [Rc.range]; omega

/-- A header slot's word, against a part other than it. -/
theorem range_sep_hdr {W i : Nat} (hi : i < 32) {c : Rc} (hc : c.ok = true) (hne : c ≠ .hdr i) :
    8 * i + 8 ≤ (c.range W).1 ∨ (c.range W).1 + (c.range W).2 ≤ 8 * i := by
  cases c with
  | arr j =>
    have := hdr_lt_slot W j hi
    simp only [Rc.range]; omega
  | hdr h =>
    have hij : h ≠ i := fun e => hne (e ▸ rfl)
    simp only [Rc.range]; omega

/-- Words of an array the parts do not include. -/
theorem KF.wv {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) {d k : Nat} (hd : slot W j ≤ d)
    (hdk : d + 8 * k ≤ slot W j + 8 * (W + 2)) (hZ : slot W 16 ≤ 2 ^ 64) :
    VG.Proof.Bignum.wv m' B d k = VG.Proof.Bignum.wv m B d k := by
  have := slot_lt (w := W) hj
  refine Frm.wv_eq h (fun r hr => ?_) (by omega)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact range_sep_arr (List.all_eq_true.mp hok c hc) (fun e => hn (e ▸ hc)) hd hdk

/-- An array the parts do not include. -/
theorem KF.arr {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot W 16 ≤ 2 ^ 64) :
    VG.Proof.Bignum.wv m' B (slot W j) W = VG.Proof.Bignum.wv m B (slot W j) W :=
  h.wv hok hj hn (Nat.le_refl _) (by omega) hZ

/-- Word `W` of an array the parts do not include. -/
theorem KF.top {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot W 16 ≤ 2 ^ 64) :
    word m' B (slot W j + 8 * W) = word m B (slot W j + 8 * W) := by
  have := slot_lt (w := W) hj
  refine Frm.word_eq h (fun r hr => ?_) (by omega)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact range_sep_arr (k := 1) (List.all_eq_true.mp hok c hc) (fun e => hn (e ▸ hc)) (by omega) (by omega)

/-- A header slot the parts do not include. -/
theorem KF.word {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (h : KF B W cs m m') (hok : cs.all Rc.ok = true)
    {i : Nat} (hi : i < 32) (hn : .hdr i ∉ cs) : word m' B (8 * i) = word m B (8 * i) :=
  Frm.word_eq h (fun r hr => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact range_sep_hdr hi (List.all_eq_true.mp hok c hc) (fun e => hn (e ▸ hc))) (by omega)

theorem Rc.ok_of_mut {c : Rc} (h : c.mut = true) : c.ok = true := by
  cases c <;> simp only [Rc.mut, Rc.ok, decide_eq_true_eq] at h ⊢ <;> omega

theorem all_mut_arr {j : Nat} (hj : j < 16) : [Rc.arr j].all Rc.mut = true := by
  simp only [List.all_cons, List.all_nil, Rc.mut, Bool.and_true, decide_eq_true_eq]; exact hj

theorem all_mut_arrs {js : List Nat} (h : ∀ j ∈ js, j < 16) : (js.map Rc.arr).all Rc.mut = true :=
  List.all_eq_true.mpr fun c hc => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    simp only [Rc.mut, decide_eq_true_eq]; exact h j hj

/-! ## The inputs and the state -/

/-- The inputs of `vg_rsa_keygen_key` and where they are: the working
space at `B` of `Z` bytes, the primes' length `pl`, the outputs, `e`, the
inputs' bytes and the writable regions. -/
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
  pb : List Byte
  qb : List Byte
  eb : List Byte
  Wr : List Region

/-- The words of `n`: `n_len / 8 = 2 pl / 8`. -/
abbrev KIn.W (I : KIn) : Nat := 2 * I.pl / 8

/-- The inputs as numbers: `p`, `q`, `e`, ordered, and `L`. -/
abbrev KIn.P₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev KIn.Q₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev KIn.E (I : KIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev KIn.P (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.Q₀ else I.P₀
abbrev KIn.Q (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.P₀ else I.Q₀
abbrev KIn.L (I : KIn) : Nat := Nat.lcm (I.P - 1) (I.Q - 1)

/-- The lengths. -/
structure KLens (I : KIn) : Prop where
  pl1 : 32 ≤ I.pl
  pl2 : I.pl ≤ 512
  pl8 : I.pl % 8 = 0
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.pl
  ebl : I.eb.length = I.el
  el1 : 1 ≤ I.el
  el8 : I.el ≤ 8

theorem KLens.W {I : KIn} (L : KLens I) : I.W = 2 * (I.pl / 8) := by
  have := L.pl8; simp only [KIn.W]; omega

/-- The arguments in the header (`entry`). -/
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

/-- The header slots of `KArgs`: from 16 to 27, but `sMask` (22). -/
theorem KArgs.congr {m m' : Mem} {I : KIn} (h : KArgs m I)
    (hm : ∀ i, 16 ≤ i ∧ i < 28 ∧ i ≠ 22 → word m' I.B (8 * i) = word m I.B (8 * i)) : KArgs m' I :=
  ⟨(hm _ (by simp [kNo, sFn])).trans h.no, (hm _ (by simp [kNl, Public.sK, sFn])).trans h.nl,
    (hm _ (by simp [kDo, sFn])).trans h.dd, (hm _ (by simp [kPp, sFn])).trans h.pp,
    (hm _ (by simp [kPl, sFn])).trans h.pl, (hm _ (by simp [kQp, sFn])).trans h.qp,
    (hm _ (by simp [kDp, sFn])).trans h.dp, (hm _ (by simp [kDq, sFn])).trans h.dq,
    (hm _ (by simp [kQi, sFn])).trans h.qi,
    (hm _ (by simp [kE, Impl.RsaKeyGen.AArch64.Candidate.kE, sFn])).trans h.e,
    (hm _ (by simp [kElen, Impl.RsaKeyGen.AArch64.Candidate.kElen, sFn])).trans h.el⟩

/-- The registers the code may write: `x0` and `mmRegs` (`x1` to `x17`). -/
abbrev kRegs : List Reg := .x0 :: mmRegs

/-- What every piece keeps, from the state `s₀` on entry. -/
structure KS (I : KIn) (s₀ : State) (s : State) : Prop where
  ws : Ws s I.B I.Z I.W
  args : KArgs s.mem I
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  e : Src s I.B I.Z I.pE I.eb
  inScr : InScr I.B I.Z s₀.mem s.mem
  wr : s.wr = I.Wr
  keep : Keep kRegs s₀ s

theorem KS.hZ {I : KIn} {s₀ s : State} (h : KS I s₀ s) : slot I.W 16 ≤ 2 ^ 64 := by
  have := h.ws.hZ; have := h.ws.scr.nowrap; omega

theorem KS.x0 {I : KIn} {s₀ s : State} (h : KS I s₀ s) : s.gpr .x0 = I.B := h.ws.x0

theorem not_x0_of_mm {regs : List Reg} (hr : ∀ r ∈ regs, r ∈ mmRegs) : .x0 ∉ regs := fun h => by
  have := hr _ h; revert this; decide

/-- `KS` after a piece that changes only parts the pieces may change, and
only registers of `mmRegs`. -/
theorem KS.step {I : KIn} {s₀ s t : State} (h : KS I s₀ s) {cs : List Rc}
    (hf : KF I.B I.W cs s.mem t.mem) (hc : cs.all Rc.mut = true) {regs : List Reg} (k : Keep regs s t)
    (hr : ∀ r ∈ regs, r ∈ mmRegs := by decide) : KS I s₀ t := by
  have hok : cs.all Rc.ok = true :=
    List.all_eq_true.mpr fun c hc' => Rc.ok_of_mut (List.all_eq_true.mp hc c hc')
  have hhdr : ∀ i, i < 29 → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi =>
    hf.word hok (by omega) fun hm => by
      have := List.all_eq_true.mp hc _ hm
      simp only [Rc.mut, decide_eq_true_eq] at this; omega
  have hZ := h.ws.hZ
  have hn := h.ws.scr.nowrap
  have hrng : ∀ r ∈ cs.map (Rc.range I.W), r.1 + r.2 ≤ I.Z ∧ KMut r := fun r hr' => by
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hr'
    have := List.all_eq_true.mp hc c hc'
    cases c with
    | arr i =>
      simp only [Rc.mut, decide_eq_true_eq] at this
      have := slot_lt (w := I.W) this
      exact ⟨by simp only [Rc.range]; omega, KMut.ofSlot _ _ _⟩
    | hdr i =>
      simp only [Rc.mut, decide_eq_true_eq] at this
      have := hdr_lt_slot I.W 16 (show 31 < 32 by decide)
      exact ⟨by simp only [Rc.range]; omega, KMut.hdr (Or.inr (Or.inr (Or.inr (by unfold sStride sFn; omega))))⟩
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf fun r hr' => (hrng r hr').1
  exact ⟨h.ws.congr' hf (fun r hr' => (hrng r hr').2) k (not_x0_of_mm hr),
    h.args.congr fun i hi' => hhdr i (by omega), h.p.congrK hi k, h.q.congrK hi k, h.e.congrK hi k,
    h.inScr.trans hi, k.wr.trans h.wr, (h.keep.trans k).mono fun r hr' => by
      rcases List.mem_append.mp hr' with h' | h'
      · exact h'
      · exact List.mem_cons_of_mem _ (hr r h')⟩

/-- `KS` after a piece that changes neither memory nor registers outside
`mmRegs`. -/
theorem KS.regs {I : KIn} {s₀ s t : State} (h : KS I s₀ s) (hm : t.mem = s.mem) {regs : List Reg}
    (k : Keep regs s t) (hr : ∀ r ∈ regs, r ∈ mmRegs := by decide) : KS I s₀ t :=
  h.step (cs := []) (KF.of_eq hm) rfl k hr

/-- A header slot the pieces may change, written. -/
theorem KS.hdrW {I : KIn} {s₀ s t : State} (h : KS I s₀ s) {i : Nat} (hi : 29 ≤ i ∧ i < 32)
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off I.B (8 * i)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : ∀ r ∈ regs, r ∈ mmRegs := by decide) :
    KS I s₀ t ∧ KF I.B I.W [.hdr i] s.mem t.mem ∧ word t.mem I.B (8 * i) = v := by
  have hn := h.ws.scr.nowrap
  have := h.ws.h256
  have o := writeW_outside s.mem I.B v (d := 8 * i) (by omega)
  rw [← hm] at o
  have f : KF I.B I.W [.hdr i] s.mem t.mem := KF.of_outside o (.hdr i) (List.mem_singleton_self _)
    (by simp [Rc.range]) (by simp [Rc.range])
  exact ⟨h.step f (by simp [Rc.mut, hi.1, hi.2]) k hr, f, by rw [hm, word_writeW_self]⟩

/-! ## Arrays' values -/

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

/-- A number of `W + 2` words below `2^(64 W)` is its low `W` words. -/
theorem av_of_full {I : KIn} {m : Mem} {j v : Nat} (h : wv m I.B (slot I.W j) (I.W + 2) = v)
    (hv : v < 2 ^ (64 * I.W)) : av I m j = v :=
  (wv_low_of_lt (Nat.le_add_right _ 2) (by rw [h]; exact hv)).trans h

/-! ## The facts between the stages -/

/-- The parts `lcmPart` changes. -/
abbrev csL : List Rc :=
  [.arr aL, .arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .arr aR, .hdr kOk]

/-- The parts `dPart` changes. -/
abbrev csD : List Rc :=
  [.arr aE, .arr aQt, .arr aR, .arr aT, .arr aU, .arr aV, .arr aX₁, .arr aX₂, .arr aC, .arr aM, .arr aDd, .hdr kOk]

/-- What `dPart` leaves: `kOk` the mask of `e⁻¹ mod L` existing, and that
inverse in `aDd`. -/
def DRes (I : KIn) (e L : Nat) (m : Mem) : Prop :=
  ∃ ok : Bool, word m I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse e L = some d) ↔ ok = true) ∧
    ∀ d, Spec.Rsa.inverse e L = some d → av I m aDd = d

/-- After `p − 1` and `q − 1` (`front_k`): the primes ordered, minus one,
and `e` in `kEv`. -/
structure KPrimes (I : KIn) (s₀ : State) (t : State) : Prop where
  ks : KS I s₀ t
  vP : av I t.mem aPa = I.P
  vQ : av I t.mem aQa = I.Q
  vPm : av I t.mem aPm = I.P - 1
  vQm : av I t.mem aQm = I.Q - 1
  ev : word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E

/-- After `smallMask`: as `KPrimes`, and `d` with `kOk` (`DRes`), and `x15`
the mask of `d` too small, which decides the status 2. -/
structure KFront (I : KIn) (s₀ : State) (t : State) : Prop where
  ks : KS I s₀ t
  vP : av I t.mem aPa = I.P
  vQ : av I t.mem aQa = I.Q
  vPm : av I t.mem aPm = I.P - 1
  vQm : av I t.mem aQm = I.Q - 1
  ev : word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E
  d : DRes I I.E I.L t.mem
  x15 : ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧
    ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.gpr .x15 = mask (decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok)

end VG.Proof.RsaKeyGen.AArch64.Key
