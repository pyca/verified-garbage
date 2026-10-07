import VerifiedGarbage.Proof.Rsa.AArch64.CkHead
import VerifiedGarbage.Proof.Rsa.AArch64.CvCheck

/-!
# `vg_rsa_check_key` on AArch64: the inputs and what the pieces keep

`CkArgs`: the arguments `entry` leaves in the header, kept by the pieces
(`CkArgs.congr`). `CkS`: what every piece of `main` keeps, from the memory on
entry to `main`: the layout, the arguments, the inputs' bytes.
-/

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
    · omega
    · simp only [Public.sMask, sFn]; omega) (by omega)

/-- The inputs of `vg_rsa_check_key` and where they are. -/
structure CkIn where
  B : Addr
  Z : Nat
  k : Nat
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

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure CkS (I : CkIn) (m₀ : Mem) (s : State) : Prop where
  ws : Ws s I.B I.Z (wW I.k)
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
  ⟨h.ws.congr hf hm k hr, h.args.congr (ckSlot_frm hf hm), h.n.congrK hi k, h.e.congrK hi k, h.d.congrK hi k,
    h.p.congrK hi k, h.q.congrK hi k, h.dp.congrK hi k, h.dq.congrK hi k, h.qi.congrK hi k, h.inScr.trans hi,
    k.wr.trans h.wr⟩

/-- `CkS` after a piece that changes only array `j`'s first `n` bytes. -/
theorem CkS.arr {I : CkIn} {m₀ : Mem} {s t : State} (h : CkS I m₀ s) {j n : Nat} (hj : j < 16)
    (hn : n ≤ 8 * (wW I.k + 2)) (ho : Outside I.B (slot (wW I.k) j) n s.mem t.mem) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CkS I m₀ t :=
  h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; omega) k hr

/-- `CkS` and the mask, after a store to the mask's slot. -/
theorem CkS.mask {I : CkIn} {m₀ : Mem} {s t : State} (h : CkS I m₀ s) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off I.B (8 * Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CkS I m₀ t ∧ mword t.mem I.B = v ∧
      ∀ j < 16, wv t.mem I.B (slot (wW I.k) j) (wW I.k) = wv s.mem I.B (slot (wW I.k) j) (wW I.k) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Public.sMask = 22 := rfl
  have ho := writeW_outside s.mem I.B v (d := 8 * Public.sMask) (by omega_arith)
  rw [← hm] at ho
  refine ⟨h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k hr,
    by rw [hm]; exact word_writeW_self _ _ _ _, fun j hj => ho.wv (Or.inr ?_) (by have := h.ws.sl hj; omega_arith)⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inr rfl
  · rw [List.mem_singleton.mp hr]; simp only [Public.sMask, sFn]; omega_arith
  · have := hdr_lt_slot (wW I.k) j (show Public.sMask < 32 by decide); omega_arith

end VG.Proof.Rsa.AArch64
