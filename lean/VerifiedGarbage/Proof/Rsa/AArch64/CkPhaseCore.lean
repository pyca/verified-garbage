module

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKeyCore
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Rsa.AArch64.CvCheck

/-! ### `Rsa.AArch64.CkState`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.CkHead`, which only this module used -/

section

/-!
# `vg_rsa_check_key` on AArch64: the header

`head` sets up the layout of `W = 2 w + 2` words (`wW k`) for
`w = ⌈k / 8⌉`: `W`, the arrays' bases, the stride and the mask all ones
(`ckHead_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The layout's width for a `k`-byte modulus. -/
abbrev wW (k : Nat) : Nat := 2 * wk k + 2

theorem wide_val {k : Nat} (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + 7#64) >>> 3 + (BitVec.ofNat 64 k + 7#64) >>> 3 + 2#64 = BitVec.ofNat 64 (wW k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, wW, wk]
  omega_arith

/-- `W` into `x12` and its slot. -/
theorem ckWide_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk2 : k ≤ 1024)
    (hZ : 8 * 32 ≤ Z) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block [ldh .x3 Public.sK, .addImm .x .x12 .x3 7, .lsr .x .x12 .x12 3, .add .x .x12 .x12 .x12,
      .addImm .x .x12 .x12 2, sth .x12 sW]) s fun t =>
        (t.gpr .x12 = BitVec.ofNat 64 (wW k) ∧ t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (wW k))) ∧
        Keep [.x3, .x12] s t := by
  have hn := hs.nowrap
  refine WP.keep [.x3, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, hdr_enc (show Public.sK < 32 by decide), hdr_enc (show sW < 32 by decide),
    hs.ld (d := 8 * Public.sK) (by unfold Public.sK sFn; omega_arith), hs.st (d := 8 * sW) (by unfold sW; omega_arith), hK,
    wide_val (show k < 2 ^ 32 by omega_arith)]

/-- `head`: `W`, the arrays' bases, the stride, and the mask all ones. -/
theorem ckHead_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block VG.Impl.Rsa.AArch64.CheckKey.head) s fun t =>
      Ws t B Z (wW k) ∧ word t.mem B (8 * Public.sMask) = mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8)] s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x12] s t := by
  have hn := hs.nowrap
  have hZ16 : slot (wW k) 16 ≤ Z := by unfold slot hdrBytes wW wk; omega_arith
  have h8 := hdr_lt_slot (wW k) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hl8 : slot (wW k) 8 ≤ slot (wW k) 16 := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide)) _
  unfold VG.Impl.Rsa.AArch64.CheckKey.head
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ckWide_ok hs h0 hk2 (by omega_arith) hK) fun t₀ ⟨⟨h12₀, hm₀⟩, k₀⟩ => ?_
  have hs₀ := hs.congr k₀.wr
  have h0₀ : t₀.gpr .x0 = B := (k₀.gpr .x0 (by decide)).trans h0
  rw [WP.block_append_iff]
  refine WP.mono (setBases_ok hs₀ h0₀ h12₀ (by unfold sArr; omega_arith)) fun t₁ ⟨hb₁, ho₁, k₁⟩ => ?_
  have k01 := k₀.trans k₁
  have h12 : t₁.gpr .x12 = BitVec.ofNat 64 (wW k) := (k₁.gpr .x12 (by decide)).trans h12₀
  have hs₁ := hs.congr k01.wr
  have h0₁ : t₁.gpr .x0 = B := (k01.gpr .x0 (by decide)).trans h0
  refine WP.mono (WP.keep [.x3, .x4, .x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = (t₁.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (wW k + 2)))).writeW (off B (8 * Public.sMask)) (mask true)) (by
    brun [h0₁, h12, hdr_enc (show sStride < 32 by decide), hdr_enc (show Public.sMask < 32 by decide),
      hs₁.st (d := 8 * sStride) (by omega_arith), hs₁.st (d := 8 * Public.sMask) (by omega_arith),
      ofNat_add_ofNat, shl_ofNat (show (wW k + 2) * 2 ^ 3 < 2 ^ 64 by simp only [wW, wk]; omega_arith)]
    rw [show (wW k + 2) * 2 ^ 3 = 8 * (wW k + 2) by omega_arith]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨_, hm⟩, k₂⟩ => ?_
  have o1 := writeW_outside t₁.mem B (BitVec.ofNat 64 (8 * (wW k + 2))) (d := 8 * sStride) (by omega_arith)
  have o2 := writeW_outside (t₁.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (wW k + 2)))) B (mask true)
    (d := 8 * Public.sMask) (by omega_arith)
  have o0 := writeW_outside s.mem B (BitVec.ofNat 64 (wW k)) (d := 8 * sW) (by omega_arith)
  rw [← hm₀] at o0
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Public.sMask → word t.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
  have hW₁ : word t₁.mem B (8 * sW) = BitVec.ofNat 64 (wW k) := by
    rw [ho₁.word (by unfold sW sArr; omega_arith) (by omega_arith), hm₀, word_writeW_self]
  refine ⟨⟨hs₁.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans h0₁, ?_, ?_, fun j hj => ?_, hZ16,
    show 2 ≤ wW k by simp only [wW]; omega_arith, show wW k < 2 ^ 24 by simp only [wW, wk]; omega_arith⟩,
    by rw [hm, word_writeW_self], ?_, (k01.trans k₂).mono (by decide)⟩
  · rw [hw sW (by decide) (by decide) (by decide)]; exact hW₁
  · rw [hm, o2.word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega_arith) (by unfold sArr sStride sFn; omega_arith)
      (by unfold sArr Public.sMask sFn; omega_arith)]
    exact hb₁ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, ho₁ x b, o0 x a]

end VG.Proof.Rsa.AArch64

end

end


/-!
# `vg_rsa_check_key` on AArch64: the inputs and what the pieces keep

`CkArgs`: the arguments `entry` leaves in the header, kept by the pieces
(`CkArgs.congr`). `CkS`: what every piece of `main` keeps, from the memory on
entry to `main`: the layout, the arguments, the inputs' bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The arguments in the header: each input's pointer, and the lengths. -/
structure CkArgs (m : Mem) (B : Addr) (k el dl pl ql : Nat) (pN pE pD pP pQ pDp pDq pQi : Addr) : Prop where
  n : word m B (8 * Public.sN) = pN
  k : word m B (8 * Public.sK) = BitVec.ofNat 64 k
  e : word m B (8 * sE) = pE
  el : word m B (8 * sElen) = BitVec.ofNat 64 el
  d : word m B (8 * sD) = pD
  dl : word m B (8 * sDlen) = BitVec.ofNat 64 dl
  p : word m B (8 * sP) = pP
  pl : word m B (8 * sPlen) = BitVec.ofNat 64 pl
  q : word m B (8 * sQ) = pQ
  ql : word m B (8 * sQlen) = BitVec.ofNat 64 ql
  dp : word m B (8 * sDP) = pDp
  dq : word m B (8 * sDQ) = pDq
  qi : word m B (8 * sQI) = pQi

/-- The header slots of `CkArgs`. -/
def ckSlot (i : Nat) : Prop := (16 ≤ i ∧ i < 22) ∨ (23 ≤ i ∧ i < 28) ∨ i = 29 ∨ i = 30

theorem CkArgs.congr {m m' : Mem} {B : Addr} {k el dl pl ql : Nat} {pN pE pD pP pQ pDp pDq pQi : Addr}
    (h : CkArgs m B k el dl pl ql pN pE pD pP pQ pDp pDq pQi)
    (hm : ∀ i, ckSlot i → word m' B (8 * i) = word m B (8 * i)) :
    CkArgs m' B k el dl pl ql pN pE pD pP pQ pDp pDq pQi :=
  ⟨(hm _ (by simp [ckSlot, Public.sN, sFn])).trans h.n, (hm _ (by simp [ckSlot, Public.sK, sFn])).trans h.k,
    (hm _ (by simp [ckSlot, sE, sFn])).trans h.e, (hm _ (by simp [ckSlot, sElen, sFn])).trans h.el,
    (hm _ (by simp [ckSlot, sD, sFn])).trans h.d, (hm _ (by simp [ckSlot, sDlen, sFn])).trans h.dl,
    (hm _ (by simp [ckSlot, sP, sFn])).trans h.p, (hm _ (by simp [ckSlot, sPlen, sFn])).trans h.pl,
    (hm _ (by simp [ckSlot, sQ, sFn])).trans h.q, (hm _ (by simp [ckSlot, sQlen, sFn])).trans h.ql,
    (hm _ (by simp [ckSlot, sDP, sFn])).trans h.dp, (hm _ (by simp [ckSlot, sDQ, sFn])).trans h.dq,
    (hm _ (by simp [ckSlot, sQI, sFn])).trans h.qi⟩

/-- The argument slots, after code that changes only ranges that `Mut`
allows. -/
theorem ckSlot_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, Mut r) :
    ∀ i, ckSlot i → word m' B (8 * i) = word m B (8 * i) := fun i hi => by
  unfold ckSlot at hi
  exact hf.word_eq (fun r hr' => by
    rcases hr r hr' with h | rfl
    · omega_using [hi, h]
    · simp only [Public.sMask, sFn]; omega_using [hi]) (by omega_using [hi])

/-- The inputs of `vg_rsa_check_key` and where they are. -/
structure CkIn where
  B : Addr
  Z : Nat
  k : Nat
  /-- Byte capacity of multiplication operands; full-key checking uses `k`. -/
  cap : Nat := k
  el : Nat
  dl : Nat
  pl : Nat
  ql : Nat
  pN : Addr
  pE : Addr
  pD : Addr
  pP : Addr
  pQ : Addr
  pDp : Addr
  pDq : Addr
  pQi : Addr
  nb : List Byte
  eb : List Byte
  db : List Byte
  pb : List Byte
  qb : List Byte
  dpb : List Byte
  dqb : List Byte
  qib : List Byte
  W : List Region

/-- The bounds on the lengths. -/
structure CkLens (I : CkIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  el1 : 1 ≤ I.el
  el2 : I.el ≤ I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  pl1 : 1 ≤ I.pl
  pl2 : I.pl < I.k
  ql1 : 1 ≤ I.ql
  ql2 : I.ql < I.k
  nl : I.nb.length = I.k
  ebl : I.eb.length = I.el
  dbl : I.db.length = I.dl
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.ql
  dpbl : I.dpb.length = I.pl
  dqbl : I.dqb.length = I.ql
  qibl : I.qib.length = I.pl
  z : 128 * I.k ≤ I.Z
  cap1 : 1 ≤ I.cap
  cap2 : I.cap ≤ I.k
  pcap : I.pl ≤ I.cap
  qcap : I.ql ≤ I.cap
  dcap : I.dl ≤ I.cap
  fit : I.k ≤ 8 * wW I.cap
  /-- `vg_rsa_check_key` multiplies operands of up to `k` bytes. -/
  capk : I.cap = I.k

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure CkS (I : CkIn) (m₀ : Mem) (s : State) : Prop where
  fit : I.k ≤ 8 * wW I.cap
  ws : Ws s I.B I.Z (wW I.cap)
  args : CkArgs s.mem I.B I.k I.el I.dl I.pl I.ql I.pN I.pE I.pD I.pP I.pQ I.pDp I.pDq I.pQi
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  dp : Src s I.B I.Z I.pDp I.dpb
  dq : Src s I.B I.Z I.pDq I.dqb
  qi : Src s I.B I.Z I.pQi I.qib
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W

theorem CkS.step {I : CkIn} {m₀ : Mem} {s t : State} (h : CkS I m₀ s) {rs : List (Nat × Nat)}
    (hf : Frm I.B rs s.mem t.mem) (hm : ∀ r ∈ rs, Mut r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ I.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CkS I m₀ t :=
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf hz
  ⟨h.fit, h.ws.congr hf hm k hr, h.args.congr (ckSlot_frm hf hm), h.n.congrK hi k, h.e.congrK hi k, h.d.congrK hi k,
    h.p.congrK hi k, h.q.congrK hi k, h.dp.congrK hi k, h.dq.congrK hi k, h.qi.congrK hi k, h.inScr.trans hi,
    k.wr.trans h.wr⟩

/-- `CkS` after a piece that changes only array `j`'s first `n` bytes. -/
theorem CkS.arr {I : CkIn} {m₀ : Mem} {s t : State} (h : CkS I m₀ s) {j n : Nat} (hj : j < 16)
    (hn : n ≤ 8 * (wW I.cap + 2)) (ho : Outside I.B (slot (wW I.cap) j) n s.mem t.mem) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CkS I m₀ t :=
  h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; omega_using [hn, this]) k hr

/-- `CkS` and the mask, after a store to the mask's slot. -/
theorem CkS.mask {I : CkIn} {m₀ : Mem} {s t : State} (h : CkS I m₀ s) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off I.B (8 * Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CkS I m₀ t ∧ mword t.mem I.B = v ∧
      ∀ j < 16, wv t.mem I.B (slot (wW I.cap) j) (wW I.cap) = wv s.mem I.B (slot (wW I.cap) j) (wW I.cap) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Public.sMask = 22 := rfl
  have ho := writeW_outside s.mem I.B v (d := 8 * Public.sMask) (by omega_arith)
  rw [← hm] at ho
  refine ⟨h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k hr,
    by rw [hm]; exact word_writeW_self _ _ _ _, fun j hj => ho.wv (Or.inr ?_) (by have := h.ws.sl hj; omega_arith)⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inr rfl
  · rw [List.mem_singleton.mp hr]; simp only [Public.sMask, sFn]; omega_arith
  · have := hdr_lt_slot (wW I.cap) j (show Public.sMask < 32 by decide); omega_arith

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.CkSteps`, which only this module used -/

section

/-!
# `vg_rsa_check_key` on AArch64: the pieces on `CkS`

Each piece of `main` keeps `CkS`; what it does to the arrays' values
(`CkIn.av`, over `W` words) and to the mask, and which arrays it leaves.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The value of array `j` over `W` words. -/
abbrev CkIn.av (I : CkIn) (m : Mem) (j : Nat) : Nat := wv m I.B (slot (wW I.cap) j) (wW I.cap)

/-- The mask after a piece that changes only array `j`. -/
theorem mword_arr {m m' : Mem} {B : Addr} {W j L : Nat} (o : Outside B (slot W j) L m m') :
    mword m' B = mword m B :=
  o.word (Or.inl (by have := hdr_lt_slot W j (show Public.sMask < 32 by decide); omega_arith))
    (by simp only [Public.sMask, sFn]; omega_arith)

theorem CkS.av_out {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {m m' : Mem} {j L : Nat}
    (o : Outside I.B (slot (wW I.cap) j) L m m') (hL : L ≤ 8 * (wW I.cap + 2)) {i : Nat} (hi : i < 16) (hij : i ≠ j) :
    I.av m' i = I.av m i :=
  outside_arr o hL hij (by omega_arith) hi h.ws.hZ h.ws.scr.nowrap

/-- `loadA j`: the bytes `bs` into array `j`. -/
theorem ckLoad_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem I.B (8 * sPtr) = p) (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s I.B I.Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlk : len ≤ I.k) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem j = Spec.Rsa.os2ip bs ∧
      ∀ i < 16, i ≠ j → I.av t.mem i = I.av s.mem i :=
  WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hlen hl1 (by have := h.fit; omega_arith)) fun _ ⟨hv, o, _, _, k⟩ =>
    ⟨h.arr hj (Nat.le_refl _) o k (by decide), mword_arr o, hv, fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `ltA a b`: the mask of `[a] < [b]`. -/
theorem ckLt_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : mword s.mem I.B = mask c) :
    WP isa (seqs (ltA a b)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mask (decide (I.av s.mem a < I.av s.mem b) && c) ∧
      ∀ i < 16, I.av t.mem i = I.av s.mem i :=
  WP.mono (ltA_ok h.ws ha hb hm) fun _ ⟨hmt, k⟩ =>
    let ⟨ht, hw, hv⟩ := h.mask hmt k (by decide)
    ⟨ht, hw, hv⟩

/-- `eqA a b` and `andZero`: the mask of `[a] = [b]`. -/
theorem ckEq_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : mword s.mem I.B = mask c) :
    WP isa (seqs (eqA a b ++ ([.block andZero] : List (Prog isa)))) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mask (decide (I.av s.mem a = I.av s.mem b) && c) ∧
      ∀ i < 16, I.av t.mem i = I.av s.mem i := by
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_)
  have h₁ : CkS I m₀ s₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁.ws (by rw [m₁]; exact hm) hz) fun t ⟨⟨hmt, _⟩, k⟩ => ?_
  obtain ⟨ht, hw, hv⟩ := h₁.mask hmt k (by decide)
  exact ⟨ht, hw, fun i hi => by unfold CkIn.av; rw [hv i hi, m₁]⟩

theorem CkLens.w1 {I : CkIn} (L : CkLens I) : 1 ≤ wk I.cap := by have := L.cap1; simp only [wk]; omega_arith

/-- `mulE`: `[aA] := [aX] e`, `e` the low word of `[aE]`. -/
theorem ckMulE_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    (hX : I.av s.mem aX < 2 ^ (64 * wk I.cap)) :
    WP isa (seqs mulE) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      I.av t.mem aA = I.av s.mem aX * (word s.mem I.B (slot (wW I.cap) aE)).toNat ∧
      ∀ i < 16, i ≠ aA → I.av t.mem i = I.av s.mem i :=
  WP.mono (mulE_ok h.ws L.w1 rfl hX) fun _ ⟨hv, o, k⟩ =>
    ⟨h.arr (by decide) (Nat.le_refl _) o k (by decide), mword_arr o, hv,
      fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `mulPQ`: `[aA] := [aX] [aR]`, for `[aX] < 256^p_len` and `[aR] < 256^q_len`. -/
theorem ckMulPQ_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    (hX : I.av s.mem aX < 256 ^ I.pl) (hR : I.av s.mem aR < 256 ^ I.ql) :
    WP isa (seqs mulPQ) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem aA = I.av s.mem aX * I.av s.mem aR ∧
      ∀ i < 16, i ≠ aA → I.av t.mem i = I.av s.mem i :=
  WP.mono (mulPQ_ok h.ws h.args.pl h.args.ql L.pl1 L.ql1 (by have := L.pcap; simp only [wk]; omega_using [this])
    (by have := L.qcap; simp only [wk]; omega_using [this]) rfl hX rfl hR) fun _ ⟨hv, o, k⟩ =>
    ⟨h.arr (by decide) (Nat.le_refl _) o k (by decide), mword_arr o, hv,
      fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `decA aM`: `[aM] - 1`, for an odd `[aM]`. -/
theorem ckDec_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (.block (decA aM)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aM % 2 = 1 → I.av t.mem aM = I.av s.mem aM - 1) ∧
      ∀ i < 16, i ≠ aM → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  refine WP.mono (decA_ok h.ws (j := aM) (by decide)) fun t ⟨m, k⟩ => ?_
  have o := writeW_outside s.mem I.B (word s.mem I.B (slot (wW I.cap) aM) - 1) (d := slot (wW I.cap) aM) (by omega_arith)
  rw [← m] at o
  refine ⟨h.arr (by decide) (by omega_arith) o k (by decide), mword_arr o, fun ho => ?_,
    fun _ hi hij => h.av_out o (by omega_arith) hi hij⟩
  have w1 := h.ws.w1
  have e3 := wv_low (m := t.mem) (B := I.B) (e := slot (wW I.cap) aM) (w := wW I.cap) (by omega_arith)
  have e2 := wv_low (m := s.mem) (B := I.B) (e := slot (wW I.cap) aM) (w := wW I.cap) (by omega_arith)
  have hw3 : word t.mem I.B (slot (wW I.cap) aM) = word s.mem I.B (slot (wW I.cap) aM) - 1 := by
    rw [m, word_writeW_self]
  have hup : wv t.mem I.B (slot (wW I.cap) aM + 8) (wW I.cap - 1) = wv s.mem I.B (slot (wW I.cap) aM + 8) (wW I.cap - 1) := by
    rw [m]; exact (writeW_outside s.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith)
  unfold CkIn.av at ho ⊢
  rw [e2] at ho ⊢
  have hodd : (word s.mem I.B (slot (wW I.cap) aM)).toNat % 2 = 1 := by omega_arith
  have hsub : (word s.mem I.B (slot (wW I.cap) aM) - 1).toNat = (word s.mem I.B (slot (wW I.cap) aM)).toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_arith)]; rfl
  rw [e3, hup, hw3, hsub]
  omega_arith

/-- `[aOne] := 1`. -/
theorem ckOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (seqs [zeroA aOne, .block (setOneA aOne)]) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem aOne = 1 ∧
      ∀ i < 16, i ≠ aOne → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  have sO := h.ws.sl (j := aOne) (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aOne) (by decide)) fun s₁ ⟨hz, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (setOneA_ok h₁.ws (j := aOne) (by decide)) fun t ⟨m, k⟩ => ?_
  have o := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot (wW I.cap) aOne) (by omega_arith)
  rw [← m] at o
  refine ⟨h₁.arr (by decide) (by omega_arith) o k (by decide), (mword_arr o).trans (mword_arr o₁), ?_,
    fun i hi hij => (h₁.av_out o (by omega_arith) hi hij).trans (h.av_out o₁ (Nat.le_refl _) hi hij)⟩
  have w1 := h.ws.w1
  have hz' : ∀ q < wW I.cap + 2, word s₁.mem I.B (slot (wW I.cap) aOne + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  unfold CkIn.av
  rw [wv_low (by omega_arith), m, word_writeW_self, (writeW_outside s₁.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith),
    wv_zero (n := wW I.cap - 1) fun q hq => by rw [Nat.add_assoc, ← Nat.mul_one 8, ← Nat.mul_add]; exact hz' _ (by omega_arith)]
  rfl

end VG.Proof.Rsa.AArch64

end

end


/-!
# Shared RSA key-validation phases on AArch64

`KS c` tracks `CkS`, the accumulated mask, and the arrays holding `n`, `e`
and 1. The full and CRT checkers share the comparison and multiplication
phases and the arithmetic helpers here.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev CkIn.N (I : CkIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CkIn.E (I : CkIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev CkIn.D (I : CkIn) : Nat := Spec.Rsa.os2ip I.db
abbrev CkIn.P (I : CkIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CkIn.Q (I : CkIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CkIn.DP (I : CkIn) : Nat := Spec.Rsa.os2ip I.dpb
abbrev CkIn.DQ (I : CkIn) : Nat := Spec.Rsa.os2ip I.dqb
abbrev CkIn.QI (I : CkIn) : Nat := Spec.Rsa.os2ip I.qib

/-- What `wordGuard` checks: `16 | k`, `p_len = q_len = k / 2` and `n`'s top
bit. -/
def CkIn.Gd (I : CkIn) : Prop :=
  I.k % 16 = 0 ∧ 2 * I.pl = I.k ∧ I.pl = I.ql ∧ ∃ h : 0 < I.nb.length, 128 ≤ (I.nb[0]'h).toNat

/-- A number of `len ≤ k` bytes fits in `w` words. -/
theorem lt_w {bs : List Byte} {k : Nat} (hl : bs.length ≤ k) : Spec.Rsa.os2ip bs < 2 ^ (64 * wk k) :=
  Nat.lt_of_lt_of_le (os2ip_lt bs) (Nat.le_trans (Nat.pow_le_pow_right (by decide) hl)
    (Nat.le_trans (pow256_le_wk k) (Nat.pow_le_pow_right (by decide) (by simp only [wk]; omega_using []))))

/-- Between the phases. -/
def KS (I : CkIn) (m₀ : Mem) (c : Bool) (s : State) : Prop :=
  CkS I m₀ s ∧ mword s.mem I.B = mask c ∧ I.av s.mem 0 = I.N ∧ I.av s.mem aE = I.E ∧ I.av s.mem aOne = 1

/-- `d < n`. -/
theorem phDN_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sD sDlen ++ ltA aX 0)) s (KS I m₀ (decide (I.D < I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.d hs.args.dl hs.d L.dbl L.dl1 L.dl2) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckLt_ok h₁ (a := aX) (b := 0) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  rw [v₁, o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [ot 0 (by decide), o₁ 0 (by decide) (by decide), hN],
    by rw [ot aE (by decide), o₁ aE (by decide) (by decide), hE], by rw [ot aOne (by decide), o₁ aOne (by decide) (by decide), hO]⟩

/-- `p q = n`. -/
theorem phPQ_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sP sPlen ++ (loadA aR sQ sQlen ++ (mulPQ ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa))))))) s
      (KS I m₀ (decide (I.P * I.Q = I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [mulPQ]) (WP.mono (ckLoad_ok h₁ (j := aR) (by decide)
    (by decide) (by decide) h₁.args.q h₁.args.ql h₁.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  have x₂ : I.av s₂.mem aX = I.P := by rw [o₂ aX (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [mulPQ]) (by simp [eqA]) (WP.mono (ckMulPQ_ok h₂ L
    (by rw [x₂]; have := os2ip_lt I.pb; rw [L.pbl] at this; exact this)
    (by rw [v₂]; have := os2ip_lt I.qb; rw [L.qbl] at this; exact this)) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  refine WP.mono (ckEq_ok h₃ (a := aA) (b := 0) (by decide) (by decide) (m₃.trans (m₂.trans (m₁.trans hm))))
    fun t ⟨ht, mt, ot⟩ => ?_
  have k0 : ∀ i < 16, i ≠ aX → i ≠ aR → i ≠ aA → I.av t.mem i = I.av s.mem i := fun i hi h1 h2 h3 => by
    rw [ot i hi, o₃ i hi h3, o₂ i hi h2, o₁ i hi h1]
  rw [v₃, x₂, v₂, o₃ 0 (by decide) (by decide), o₂ 0 (by decide) (by decide), o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [k0 0 (by decide) (by decide) (by decide) (by decide), hN],
    by rw [k0 aE (by decide) (by decide) (by decide) (by decide), hE],
    by rw [k0 aOne (by decide) (by decide) (by decide) (by decide), hO]⟩

/-- The low word of `[aE]` is `e`, below `2^64`. -/
theorem e_word {I : CkIn} {m : Mem} (hE : I.av m aE = I.E) (hE64 : I.E < 2 ^ 64) :
    (word m I.B (slot (wW I.cap) aE)).toNat = I.E := by
  rw [← wv_mod64 m I.B (slot (wW I.cap) aE) (n := wW I.cap) (by simp only [wW]; omega_using []), show wv m I.B (slot (wW I.cap) aE) (wW I.cap) = I.E
    from hE, Nat.mod_eq_of_lt hE64]

end VG.Proof.Rsa.AArch64
