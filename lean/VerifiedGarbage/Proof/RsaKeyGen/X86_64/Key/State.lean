import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Key

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
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (kE kElen)

/-! ## Frames by codes -/

/-- A part of the working space: an array (`w + 2` words), or a header
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

/-- One the pieces may change: an array, or `sMo`, `kEv` or `kOk`. -/
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

/-- An array's range, against a part other than it. -/
theorem range_sep_arr {W j : Nat} {c : Rc} (hc : c.ok = true) (hne : c ≠ .arr j) {d k : Nat}
    (hd : slot W j ≤ d) (hdk : d + 8 * k ≤ slot W j + 8 * (W + 2)) :
    d + 8 * k ≤ (c.range W).1 ∨ (c.range W).1 + (c.range W).2 ≤ d := by
  cases c with
  | arr i =>
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    have := slot_far (w := W) hij
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
    simp only [Rc.ok, decide_eq_true_eq] at hc
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

theorem Rc.ok_of_mut {c : Rc} (h : c.mut = true) : c.ok = true := by
  cases c <;> simp only [Rc.mut, Rc.ok, decide_eq_true_eq] at h ⊢ <;> omega

theorem KS.hZ {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) : slot I.W 16 ≤ 2 ^ 64 := by
  have := h.ws.hZ; have := h.ws.scr.nowrap; omega

/-- `KS` after a piece that changes only parts the pieces may change. -/
theorem KS.step {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) {cs : List Rc}
    (hf : KF I.B I.W cs s.mem t.mem) (hc : cs.all Rc.mut = true) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : KS I m₀ t := by
  have hok : cs.all Rc.ok = true :=
    List.all_eq_true.mpr fun c hc' => Rc.ok_of_mut (List.all_eq_true.mp hc c hc')
  have hhdr : ∀ i, i < 29 → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi =>
    hf.word hok (by omega) fun hm => by
      have := List.all_eq_true.mp hc _ hm
      simp only [Rc.mut, decide_eq_true_eq] at this; omega
  have hZ := h.ws.hZ
  have hn := h.ws.scr.nowrap
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf fun r hr => by
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hr
    have := List.all_eq_true.mp hc c hc'
    cases c with
    | arr i =>
      simp only [Rc.mut, decide_eq_true_eq] at this
      have := slot_lt (w := I.W) this
      simp only [Rc.range]; omega
    | hdr i =>
      simp only [Rc.mut, decide_eq_true_eq] at this
      have := hdr_lt_slot I.W 16 (show 31 < 32 by decide)
      simp only [Rc.range]; omega
  refine ⟨⟨h.ws.scr.congr k.2.2, (k.gpr hr.1).trans h.ws.rdi, (hhdr sW (by decide)).trans h.ws.hw,
      (hhdr sStride (by decide)).trans h.ws.hS, fun j hj => (hhdr (sArr j) (by unfold sArr; omega)).trans
      (h.ws.harr j hj), hZ, h.ws.w1, h.ws.w2⟩,
    h.args.congr fun i hi => hhdr i (by omega), h.p.congrK hi k, h.q.congrK hi k, h.e.congrK hi k,
    h.inScr.trans hi, k.2.2.trans h.wr, (k.gpr hr.2).trans h.rsp⟩

end VG.Proof.RsaKeyGen.X86_64.Key
