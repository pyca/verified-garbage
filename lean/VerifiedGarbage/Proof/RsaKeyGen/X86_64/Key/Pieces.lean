import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Key
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

/-! ## State -/
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
  exact ⟨wv_zero fun k hk => this k (by omega), this W (by omega)⟩

/-- Word `k` of a zero number written. -/
theorem wv_put {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : ∀ q < N, word m B (d + 8 * q) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = if k < n then 2 ^ (64 * k) * v.toNat else 0
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv_put v hz hd hk n (by omega)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega)).word (by omega) (by omega), hz n (by omega)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega]
      · simp [hk', show ¬ k < n + 1 by omega]

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
    have f := KF.arr1 o' (Nat.le_refl _) (by omega)
    have hn := h.ws.scr.nowrap
    have := h.ws.sl ho
    ⟨h.step f (all_mut_arr ho) k (by decide), f, hv, o'.word (Or.inr (Nat.le_refl _)) (by omega), k⟩

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
      hs₃.st (d := slot I.W aC) (by omega), m₃, m₂]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s₁.mem I.B (x.setWidth 64) (d := slot I.W aC) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega)
  have kk := (k₂.trans k₃).trans k₄
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) kk (by decide), (f₁.trans f₄).mono (by simp), ?_,
    (k₁.trans kk).mono (by simp)⟩
  rw [hm]
  have := wv_put (m := s₁.mem) (B := I.B) (d := slot I.W aC) (N := I.W + 2) (k := 0) (x.setWidth 64)
    ((wv_eq_zero_iff _ _ _ _).mp z₁) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this]
  rw [ite_eq_left (show 0 < I.W + 2 by omega), Nat.pow_zero, Nat.one_mul, BitVec.toNat_setWidth]
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
        by rw [hm, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp)⟩
  refine WP.seq (WP.mono hb ?_)
  · intro s₁ ⟨h12, hbx, h10, hbp, m₁, k₁⟩
    refine WP.mono (cmpLoop_ok (h.ws.scr.congr k₁.2.2) hbx h10 h12 hbp (by have := h.ws.w1; omega)
      (by have := h.ws.w2; omega) (by omega) (by omega)) fun t ⟨hbp', m₂, k₂⟩ => ?_
    rw [m₁] at hbp'
    have kk := k₁.trans k₂
    exact ⟨h.step (cs := []) (by rw [m₂, m₁]; exact KF.refl _ _ _) rfl kk (by decide), by rw [m₂, m₁], hbp',
      (k₂.gpr (by decide)).trans hbx, (k₂.gpr (by decide)).trans h10, (k₂.gpr (by decide)).trans h12,
      kk.mono (by simp)⟩

theorem isZero_mask {x : BitVec 64} {c : Prop} [Decidable c] (hx : x = 0 ↔ c) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) = mask (decide c) := by
  by_cases hc : c
  · rw [hx.mpr hc, decide_eq_true hc]; decide
  · have : x ≠ 0 := fun e => hc (hx.mp e)
    have : ¬ x.toNat < 1 := fun h => this (BitVec.eq_of_toNat_eq (by simp; omega))
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
      kk.mono (by simp)⟩

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
    ((k₂.gpr (by decide)).trans h12) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega) (by omega)
    (by omega)) fun t ⟨hv, o, k₃⟩ => ?_
  rw [m₂, m₁] at hv o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  have kk := (k₁.trans k₂).trans k₃
  exact ⟨h.step f (all_mut_arr hj) kk (by decide), f, hv, o.word (Or.inr (Nat.le_refl _)) (by omega),
    kk.mono (by simp)⟩

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
    · have := slot_far (w := I.W) hne; omega
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
        ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by simp)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨h12, h8, h10, hsi, hbp, m₁, k₁⟩ => ?_)
  refine WP.mono (subM_ok (h.ws.scr.congr k₁.2.2) hsi h8 h10 ((k₁.gpr (by decide)).trans h15) h12 hbp
    (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega) (by omega) (by omega) pA (by omega))
    fun t ⟨b, _, hv, o', k₂⟩ => ?_
  rw [m₁] at hv o'
  have f := KF.arr1 (I := I) (j := o) o' (Nat.le_refl _) (by omega)
  have kk := k₁.trans k₂
  exact ⟨h.step f (all_mut_arr ho) kk (by decide), f, ⟨b, hv⟩, o'.word (Or.inr (Nat.le_refl _)) (by omega),
    kk.mono (by simp)⟩

/-- `oddMask j`: `rax := ` the mask of `[j]` odd. -/
theorem oddMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) :
    WP isa (.block (oddMask j)) s fun t => t.mem = s.mem ∧ t.gpr .rax = mask (decide (av I s.mem j % 2 = 1)) ∧
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
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
        hs₂.ld (d := slot I.W j) (by omega), mask_low, e0]) rfl) fun t ⟨⟨hm, hax⟩, k₃⟩ =>
    ⟨by rw [hm, m₂, m₁], hax, ((k₂.trans k₃).gpr (by decide)).trans h12, ((k₂.trans k₃).gpr (by decide)).trans h9,
      ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `setOneA j` on a zero array: `[j] := 1` over `W + 2` words. -/
theorem setOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16)
    (hz : wv s.mem I.B (slot I.W j) (I.W + 2) = 0) :
    WP isa (.block (setOneA j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 1 ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  refine WP.mono (setOneA_ok h.ws hj) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot I.W j) (by omega)
  rw [← hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  refine ⟨h.step f (all_mut_arr hj) k (by decide), f, ?_, k⟩
  rw [hm]
  have := wv_put (m := s.mem) (B := I.B) (d := slot I.W j) (N := I.W + 2) (k := 0) (1 : BitVec 64)
    ((wv_eq_zero_iff _ _ _ _).mp hz) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < I.W + 2 by omega)]
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
  refine WP.mono (divmod_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hQ hR hD hT
    dQR dQD dQT dRD dRT dDT) fun t ⟨hdi, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf
  have k' : Keep (List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)) s t :=
    ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
      ⟨hm, by simp [e]⟩), k.2⟩
  exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k' (by decide), f, hv⟩

/-- `inverse u v x₁ x₂ m t` from `v = m`, `x₁ = 1`, `x₂ = 0` and word `W`
of `u` zero: for an odd `m > 1`, `v = gcd(u, m)` and `x₂ u ≡ v (mod m)`,
`x₂ < m`. -/
theorem inverse_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : atop I s.mem iU = 0)
    (hVM : av I s.mem iV = av I s.mem iM) (hX1 : av I s.mem iX₁ = 1) (hX2 : av I s.mem iX₂ = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] s.mem t.mem ∧
      (av I s.mem iM % 2 = 1 → 1 < av I s.mem iM →
        av I t.mem iV = Nat.gcd (av I s.mem iU) (av I s.mem iM) ∧
        ((av I s.mem iM : Nat) : Int) ∣ (av I t.mem iX₂ : Int) * av I s.mem iU - av I t.mem iV ∧
        av I t.mem iX₂ < av I s.mem iM) := by
  refine WP.mono (inverse_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hU hV hX₁
    hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hU0 hVM hX1 hX2)
    fun t ⟨hdi, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.hdr sMo, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  have k' : Keep (List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)) s t :=
    ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
      ⟨hm, by simp [e]⟩), k.2⟩
  refine ⟨h.step f ?_ k' (by decide), f, hv⟩
  simp only [List.all_cons, List.all_nil, Rc.mut, sMo, sFn, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

end VG.Proof.RsaKeyGen.X86_64.Key

end
