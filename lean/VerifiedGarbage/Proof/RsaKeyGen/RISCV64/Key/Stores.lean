module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Init
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: the outputs written out

As PPC64LE's (`Proof/RsaKeyGen/PPC64LE/Key/Stores.lean`): `Fr s0 m s`, what
the stores keep from the memory `m` before them (the working space's bytes,
`CB` for the memory written so far); `storeTo_ok`, one output's bytes,
masked by the slot `X8`; `stores_ok`, all seven (`Outs`) and the status
`2 [X7] + [X8]` in `a0`.
-/

-- separate module: the stores' proofs are not re-checked with every change to the body's

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs storeBytes)
open VG.Impl.RsaKeyGen.RISCV64.Key (mask storeTo stores nArr X7 X8 aN aD aP aQ aDP aDQ aQi)

/-- `mask`: `t4` all ones if the slot `X8` is 1, else 0. -/
theorem kmask_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (bit : slot s.mem B X8 ≤ 1) :
    WP isa (.block mask) s fun t =>
      (t.gpr .t4 = (if decide (slot s.mem B X8 ≠ 0) then BitVec.allOnes 64 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t4, .t5] s t := by
  have hz := h.hdr_le
  have nw := h.nowrap
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hz' : X8 + 8 ≤ Z := by simp only [hdr_eq, X8] at hz ⊢; omega_arith
  brun [mask, h.s11, VG.Proof.Bignum.RISCV64.fin64_exec_li_zero, add_ofNat_zero',
    h.scr.al8 (d := X8) (by omega_arith) (by decide), h.scr.ld (d := X8) (n := 8) hz', show X8 < 2048 by decide]
  exact mask_of_slot _ bit

/-- A write apart from the working space keeps the header's words. -/
theorem out_of_ws {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (ho : Outside O 0 L m m') {x : Addr} (hx : ofs B x < Z) : m' x = m x :=
  ho x (.inr (by
    have := hd x
    simp only [Region.Contains] at this
    simp only [ofs] at hx ⊢
    omega_arith))

/-- A write apart from a region keeps its bytes. -/
theorem zeros_keep {O O' : Addr} {L L' : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨O', L'⟩)
    (hL : L ≤ 2 ^ 64) (ho : Outside O' 0 L' m m') {c : Nat} (hc : c < L) : m' (off O c) = m (off O c) :=
  ho _ (.inr (by have := bytes_past hd hc hL; omega_arith))

theorem CB.a1_ofNat {s0 s : State} {M : Mem} (c : CB s0 M s) : s.gpr .a1 = BitVec.ofNat 64 (pLen s0) := by
  rw [c.a1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- What the stores keep, from the memory `m` before them. -/
structure Fr (s0 : State) (m : Mem) (s : State) : Prop where
  cb : CB s0 s.mem s
  ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr
  scr : ∀ x, ofs (bOf s0) x < zOf s0 → s.mem x = m x

theorem Fr.of_st {s0 s : State} {used : List Nat} (h : St s0 used s) : Fr s0 s.mem s :=
  ⟨{ h.cb with frame := fun _ _ => rfl }, h.ws, fun _ _ => rfl⟩

theorem Fr.of_keep {s0 s t : State} {m : Mem} (h : Fr s0 m s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) (h9 : .s9 ∉ rs := by decide)
    (h10 : .s10 ∉ rs := by decide) (h11 : .s11 ∉ rs := by decide) : Fr s0 m t :=
  ⟨hm ▸ h.cb.of_keep k hm hr, h.ws.of_keep k h9 h10 h11, fun x hx => by rw [hm]; exact h.scr x hx⟩

theorem Fr.of_out {s0 s t : State} {m : Mem} (h : Fr s0 m s) (hp : PreC s0) {rs : List Reg} (k : Keep rs s t)
    {O : Addr} {L : Nat} (ho : Outside O 0 L s.mem t.mem) (hd : (⟨O, L⟩ : Region).Disjoint (sR s0))
    (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : Fr s0 m t := by
  have hz := hp.zk
  refine ⟨{ h.cb.of_keep (t := { t with mem := s.mem }) k rfl hr with
    hdr := fun i hi => ?_, frame := fun _ _ => rfl }, ws, fun x hx => ?_⟩
  · rw [← h.cb.hdr i hi]
    refine Mem.readW_congr fun j hj => out_of_ws hd ho ?_
    have nw := ws.nowrap
    simp only [zOf] at hz nw ⊢
    rw [off_add, ofs_off0 _ (by omega_arith)]
    omega_arith
  · rw [out_of_ws hd ho hx]; exact h.scr x hx

/-- The working space's words are `m`'s. -/
theorem Fr.word {s0 s : State} {m : Mem} (h : Fr s0 m s) {d : Nat} (hd : d + 8 ≤ zOf s0) :
    word s.mem (bOf s0) d = word m (bOf s0) d := by
  have nw := h.ws.nowrap
  refine Mem.readW_congr fun j hj => h.scr _ ?_
  rw [off_add, ofs_off0 _ (by omega_arith)]
  omega_arith

/-- One output: the pointer in `rP`, the length in `rL`, and array `j`'s low
bytes, masked by `b`. -/
theorem storeTo_ok {s0 s : State} {m : Mem} (hp : PreC s0) (h : Fr s0 m s) {rP rL : Reg} (hP1 : rP ≠ .t1)
    (hP4 : rP ≠ .t4) (hP5 : rP ≠ .t5) (hL0 : rL ≠ .t0) (hL1 : rL ≠ .t1) (hL4 : rL ≠ .t4) (hL5 : rL ≠ .t5)
    {O : Addr} (hO : s.gpr rP = O) {L : Nat} (hL : s.gpr rL = BitVec.ofNat 64 L) {b : Bool}
    (hb : slot m (bOf s0) X8 = if b then 1 else 0) (hrw : (⟨O, L⟩ : Region) ∈ s0.wr)
    (hds : (⟨O, L⟩ : Region).Disjoint (sR s0)) (hOw : O.toNat + L ≤ 2 ^ 64) (hL1' : 1 ≤ L)
    (hLw : L ≤ 8 * wOf s0) {j : Nat} (hj : j < nArr) :
    WP isa (.seq (.block mask) (storeBytes j rP rL)) s fun t =>
      Fr s0 m t ∧ (∀ c < L, t.mem (off O c) = if b then m (off (bOf s0) (arr (wOf s0) j + (L - 1 - c))) else 0) ∧
        Outside O 0 L s.mem t.mem ∧ Keep [.t4, .t5, .t0, .t1, .t3] s t := by
  have hz := h.ws.hdr_le
  have hs8 : slot s.mem (bOf s0) X8 = slot m (bOf s0) X8 := by
    simp only [slot]; rw [h.word (by simp only [hdr_eq, X8] at hz ⊢; omega_arith)]
  have hb' : decide (slot s.mem (bOf s0) X8 ≠ 0) = b := by rw [hs8, hb]; cases b <;> rfl
  rw [WP.seq_iff]
  refine WP.mono (kmask_ok h.ws (by rw [hs8, hb]; cases b <;> decide)) fun u ⟨⟨u4, um⟩, ku⟩ => ?_
  rw [hb'] at u4
  have fu : Fr s0 m u := h.of_keep ku um
  refine WP.mono (storeBytes_ok fu.ws hj (by decide) (by rw [ku.gpr (by simp [hP4, hP5])]; exact hO)
    (by rw [ku.gpr (by simp [hL4, hL5])]; exact hL) hL1 hP1 hL0 u4 hL1' hLw
    (fun i hi => by rw [fu.cb.wr]; exact bytes_in hrw (by omega_arith) i hi) (bytes_sep hds (by omega_arith)) hOw)
    fun t ⟨wt, tb, to, kt⟩ => ⟨fu.of_out hp kt to hds wt, fun c hc => ?_, by rw [← um]; exact to,
      (ku.trans kt).mono (by decide)⟩
  rw [tb c hc, um]
  cases b
  · rfl
  · simp only [ite_true]
    have fit := h.ws.arr_fit hj
    have fZ := Nat.le_trans (arr_end hj) h.ws.fits
    have nw := h.ws.nowrap
    simp only [S] at fit fZ
    refine h.scr _ ?_
    rw [ofs_off0 _ (by omega_arith)]
    omega_arith

/-- The outputs `os` (address, length, array) hold the arrays' low bytes in
`m`, most significant first, under `b`. -/
def Outs (s0 : State) (m : Mem) (b : Bool) (t : Mem) (os : List (Addr × Nat × Nat)) : Prop :=
  ∀ o ∈ os, ∀ c < o.2.1, t (off o.1 c) = if b then m (off (bOf s0) (arr (wOf s0) o.2.2 + (o.2.1 - 1 - c))) else 0

theorem Outs.step {s0 : State} {m : Mem} {b : Bool} {t t' : Mem} {os : List (Addr × Nat × Nat)}
    (h : Outs s0 m b t os) {O : Addr} {L : Nat} (o : Outside O 0 L t t')
    (hd : ∀ x ∈ os, (⟨x.1, x.2.1⟩ : Region).Disjoint ⟨O, L⟩ ∧ x.2.1 ≤ 2 ^ 64) : Outs s0 m b t' os := by
  intro x hx c hc
  rw [zeros_keep (hd x hx).1 (hd x hx).2 o hc]
  exact h x hx c hc

theorem Outs.cons {s0 : State} {m : Mem} {b : Bool} {t : Mem} {os : List (Addr × Nat × Nat)}
    (h : Outs s0 m b t os) {O : Addr} {L j : Nat}
    (v : ∀ c < L, t (off O c) = if b then m (off (bOf s0) (arr (wOf s0) j + (L - 1 - c))) else 0) :
    Outs s0 m b t ((O, L, j) :: os) := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact v
  · exact h x hx

/-- The seven outputs, last first. -/
abbrev outList (s0 : State) : List (Addr × Nat × Nat) :=
  [(stackArg s0 4, pLen s0, aQi), (stackArg s0 2, pLen s0, aDQ), (stackArg s0 0, pLen s0, aDP),
    (s0.gpr .a6, pLen s0, aQ), (s0.gpr .a4, pLen s0, aP), (s0.gpr .a2, 2 * pLen s0, aD),
    (s0.gpr .a0, 2 * pLen s0, aN)]

theorem wp_seqs_pair {a b : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (a :: b :: l)) s Q ↔ WP isa (.seq a b) s fun t => WP isa (seqs l) t Q := by
  obtain ⟨c, l, rfl⟩ : ∃ c l', l = c :: l' := by cases l with | nil => exact absurd rfl hl | cons c l => exact ⟨c, l, rfl⟩
  show WP isa (.seq a (.seq b (seqs (c :: l)))) s Q ↔ _
  rw [WP.seq_iff, WP.seq_iff]
  exact ⟨fun h => WP.mono h fun t ht => WP.seq_iff.mp ht, fun h => WP.mono h fun t ht => WP.seq_iff.mpr ht⟩

theorem stores_eq : stores = seqs ([.block [.shift .sll .d .a5 .a1 1], .block mask, storeBytes aN .s0 .a5,
    .block mask, storeBytes aD .s1 .a5, .block mask, storeBytes aP .s2 .a1, .block mask, storeBytes aQ .s3 .a1,
    .block mask, storeBytes aDP .s4 .a1, .block mask, storeBytes aDQ .s5 .a1, .block mask, storeBytes aQi .s6 .a1,
    .block [.load .d .a0 .s11 X7, .shift .sll .d .a0 .a0 1, .load .d .t5 .s11 X8, .add .a0 .a0 .t5]]) := rfl

theorem status_bv (a b : Bool) :
    (BitVec.ofNat 64 (if a then 1 else 0) <<< (1 % 64)) + BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (2 * (if a then 1 else 0) + (if b then 1 else 0)) := by
  cases a <;> cases b <;> decide

theorem twice_bv (L : Nat) : BitVec.ofNat 64 L <<< (1 % 64) = BitVec.ofNat 64 (2 * L) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow]
  omega_arith

/-- `stores`: the seven outputs, masked by `b`, and the status in `a0`. -/
theorem stores_ok {s0 s : State} (hp : PreC s0) (h : Fr s0 s.mem s) {a b : Bool}
    (h7 : slot s.mem (bOf s0) X7 = if a then 1 else 0) (h8 : slot s.mem (bOf s0) X8 = if b then 1 else 0) :
    WP isa stores s fun t => CE s0 t ∧
      t.gpr .a0 = BitVec.ofNat 64 (2 * (if a then 1 else 0) + (if b then 1 else 0)) ∧
      Outs s0 s.mem b t.mem (outList s0) := by
  have hn := hp.hn; have hd := hp.hd; have hq := hp.hq; have hdp := hp.hdp; have hdq := hp.hdq
  have hqi := hp.hqi
  have p512 := hp.p512; have p32 := hp.p32
  have w4 := hp.wOf_eq
  have lN : 2 * pLen s0 ≤ 8 * wOf s0 := by simp only [pLen] at w4 ⊢; omega
  have lP : pLen s0 ≤ 8 * wOf s0 := by simp only [pLen] at w4 ⊢; omega
  have oN : 1 ≤ 2 * pLen s0 := by simp only [pLen]; omega
  have oP : 1 ≤ pLen s0 := by simp only [pLen]; omega
  have bN : 2 * pLen s0 ≤ 2 ^ 64 := by simp only [pLen]; omega
  have bP : pLen s0 ≤ 2 ^ 64 := by simp only [pLen]; omega
  have wN := hp.wn; have wD := hp.wd; have wP := hp.wp; have wQ := hp.wq
  have wDp := hp.wdp; have wDq := hp.wdq; have wQi := hp.wqi
  have mN : (⟨s0.gpr .a0, 2 * pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [nR, hn]
  have mD : (⟨s0.gpr .a2, 2 * pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [dR, hd, hn]
  have mP : (⟨s0.gpr .a4, pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [pR]
  have mQ : (⟨s0.gpr .a6, pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [qR, hq]
  have mDp : (⟨stackArg s0 0, pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [dpR, hdp]
  have mDq : (⟨stackArg s0 2, pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [dqR, hdq]
  have mQi : (⟨stackArg s0 4, pLen s0⟩ : Region) ∈ s0.wr := by rw [hp.hwr]; simp [qiR, hqi]
  have pN := hp.ns; have pD := hp.ds; have pP := hp.ps; have pQ := hp.qs; have pDp := hp.dps
  have pDq := hp.dqs; have pQi := hp.qis
  have nD := hp.nd; have nP := hp.np; have nQ := hp.nq; have nDp := hp.ndp; have nDq := hp.ndq
  have nQi := hp.nqi
  have dP := hp.dp; have dQ := hp.dq; have dDp := hp.ddp; have dDq := hp.ddq; have dQi := hp.dqi
  have pQ' := hp.pq; have pDp' := hp.pdp; have pDq' := hp.pdq; have pQi' := hp.pqi
  have qDp := hp.qdp; have qDq := hp.qdq; have qQi := hp.qqi
  have dpDq := hp.dpdq; have dpQi := hp.dpqi; have dqQi := hp.dqqi
  set_option linter.unusedSimpArgs false in
  simp only [nR, dR, pR, qR, dpR, dqR, qiR, hn, hd, hq, hdp, hdq, hqi] at pN pD pP pQ pDp pDq pQi nD nP nQ nDp
  set_option linter.unusedSimpArgs false in
  simp only [nR, dR, pR, qR, dpR, dqR, qiR, hn, hd, hq, hdp, hdq, hqi] at nDq nQi dP dQ dDp dDq dQi pQ' pDp' pDq'
  set_option linter.unusedSimpArgs false in
  simp only [nR, dR, pR, qR, dpR, dqR, qiR, hn, hd, hq, hdp, hdq, hqi] at pQi' qDp qDq qQi dpDq dpQi dqQi
  rw [hn] at wN
  rw [hd, hn] at wD
  rw [hq] at wQ
  rw [hdp] at wDp
  rw [hdq] at wDq
  rw [hqi] at wQi
  have c := h.cb
  have a1 : s.gpr .a1 = BitVec.ofNat 64 (pLen s0) := c.a1_ofNat
  rw [stores_eq, wp_seqs_cons (List.cons_ne_nil _ _)]
  have b0 : WP isa (.block [.shift .sll .d .a5 .a1 1]) s fun u =>
      (u.gpr .a5 = BitVec.ofNat 64 (2 * pLen s0) ∧ u.mem = s.mem) ∧ Keep [.a5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [a1]
    exact twice_bv _
  refine WP.mono b0 fun u ⟨⟨u5, um⟩, ku⟩ => ?_
  have f0 := h.of_keep ku um
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f0 (rP := .s0) (rL := .a5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f0.cb.rs0 u5 h8 mN pN wN oN lN (j := aN)
    (by decide)) fun t1 ⟨f1, v1, o1, k1⟩ => ?_
  have O1 : Outs s0 s.mem b t1.mem [(s0.gpr .a0, 2 * pLen s0, aN)] :=
    Outs.cons (fun _ h => absurd h (by simp)) v1
  have e1 : t1.gpr .a5 = BitVec.ofNat 64 (2 * pLen s0) := (k1.gpr (by decide)).trans u5
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f1 (rP := .s1) (rL := .a5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f1.cb.s1 e1 h8 mD pD wD oN lN (j := aD)
    (by decide)) fun t2 ⟨f2, v2, o2, k2⟩ => ?_
  have O2 := (O1.step o2 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact ⟨nD, bN⟩)).cons v2
  have a1' : ∀ {t : State}, Fr s0 s.mem t → t.gpr .a1 = BitVec.ofNat 64 (pLen s0) := fun f => f.cb.a1_ofNat
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f2 (rP := .s2) (rL := .a1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f2.cb.s2 (a1' f2) h8 mP pP wP oP lP (j := aP)
    (by decide)) fun t3 ⟨f3, v3, o3, k3⟩ => ?_
  have O3 := (O2.step o3 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨dP, bN⟩, ⟨nP, bN⟩⟩)).cons v3
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f3 (rP := .s3) (rL := .a1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f3.cb.s3 (a1' f3) h8 mQ pQ wQ oP lP (j := aQ)
    (by decide)) fun t4 ⟨f4, v4, o4, k4⟩ => ?_
  have O4 := (O3.step o4 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨pQ', bP⟩, ⟨dQ, bN⟩, ⟨nQ, bN⟩⟩)).cons v4
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f4 (rP := .s4) (rL := .a1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f4.cb.s4 (a1' f4) h8 mDp pDp wDp oP lP
    (j := aDP) (by decide)) fun t5 ⟨f5, v5, o5, k5⟩ => ?_
  have O5 := (O4.step o5 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨qDp, bP⟩, ⟨pDp', bP⟩, ⟨dDp, bN⟩, ⟨nDp, bN⟩⟩)).cons v5
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f5 (rP := .s5) (rL := .a1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f5.cb.s5 (a1' f5) h8 mDq pDq wDq oP lP
    (j := aDQ) (by decide)) fun t6 ⟨f6, v6, o6, k6⟩ => ?_
  have O6 := (O5.step o6 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨dpDq, bP⟩, ⟨qDq, bP⟩, ⟨pDq', bP⟩, ⟨dDq, bN⟩,
      ⟨nDq, bN⟩⟩)).cons v6
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (storeTo_ok hp f6 (rP := .s6) (rL := .a1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) f6.cb.s6 (a1' f6) h8 mQi pQi wQi oP lP
    (j := aQi) (by decide)) fun t7 ⟨f7, v7, o7, k7⟩ => ?_
  have O7 := (O6.step o7 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨dqQi, bP⟩, ⟨dpQi, bP⟩, ⟨qQi, bP⟩, ⟨pQi', bP⟩,
      ⟨dQi, bN⟩, ⟨nQi, bN⟩⟩)).cons v7
  rw [show seqs [.block [.load .d .a0 .s11 X7, .shift .sll .d .a0 .a0 1, .load .d .t5 .s11 X8, .add .a0 .a0 .t5]] =
    .block [.load .d .a0 .s11 X7, .shift .sll .d .a0 .a0 1, .load .d .t5 .s11 X8, .add .a0 .a0 .t5] from rfl]
  have ws7 := f7.ws
  have hz := ws7.hdr_le
  have nw := ws7.nowrap
  have z7 : X7 + 8 ≤ zOf s0 := by simp only [hdr_eq, X7] at hz ⊢; omega_arith
  have z8 : X8 + 8 ≤ zOf s0 := by simp only [hdr_eq, X8] at hz ⊢; omega_arith
  have m7 : word t7.mem (bOf s0) X7 = BitVec.ofNat 64 (if a then 1 else 0) := by
    rw [f7.word z7]; apply BitVec.eq_of_toNat_eq; rw [← h7]; simp only [slot, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
  have m8 : word t7.mem (bOf s0) X8 = BitVec.ofNat 64 (if b then 1 else 0) := by
    rw [f7.word z8]; apply BitVec.eq_of_toNat_eq; rw [← h8]; simp only [slot, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
  have hb4 : WP isa (.block [.load .d .a0 .s11 X7, .shift .sll .d .a0 .a0 1, .load .d .t5 .s11 X8,
      .add .a0 .a0 .t5]) t7 fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 (2 * (if a then 1 else 0) + (if b then 1 else 0)) ∧ t.mem = t7.mem) ∧
        Keep [.a0, .t5] t7 t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ws7.s11, add_ofNat_zero', ws7.scr.al8 (d := X7) (by omega_arith) (by decide),
      ws7.scr.ld (d := X7) (n := 8) z7, show X7 < 2048 by decide, ws7.scr.al8 (d := X8) (by omega_arith) (by decide),
      ws7.scr.ld (d := X8) (n := 8) z8, show X8 < 2048 by decide, m7, m8]
    exact status_bv a b
  refine WP.mono hb4 fun t ⟨⟨t0, tm⟩, kt⟩ => ⟨?_, t0, by rw [tm]; exact O7⟩
  have c7 := f7.cb
  exact ⟨(kt.gpr (by decide)).trans c7.s11, (kt.gpr (by decide)).trans c7.ra, kt.2.1.trans c7.rd,
    kt.2.2.trans c7.wr, fun i hi => by rw [tm]; exact c7.hdr i hi⟩

end VG.Proof.RsaKeyGen.RISCV64.Key
