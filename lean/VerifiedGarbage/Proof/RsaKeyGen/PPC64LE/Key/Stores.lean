module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Base
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Init
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_keygen_key` on PPC64LE: the outputs written out

As `vg_rsa_crt_values`'s (`Proof/Rsa/PPC64LE/CvStores.lean`): `Fr s0 m s`,
what the stores keep from the memory `m` before them; `outStage_ok`, one
output's bytes, masked by the slot `X8`; `stores_ok`, all seven (`Outs`) and
the status `2 [X7] + [X8]` in `r3`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (storeBytes)
open VG.Impl.RsaKeyGen.PPC64LE.Key (mask stores nArr X7 X8 aN aD aP aQ aDP aDQ aQi)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa.PPC64LE.CrtValues (hdrVal past_of_disjoint out_of_disjoint ofNat_slot mv2_ok ofNat_toNat64
  wp_seqs_pair)

/-- What the stores keep, from the memory `m` before them. -/
structure Fr (s0 : State) (m : Mem) (s : State) : Prop where
  pre : keyP.pre s0
  sp : s.sp = s0.sp
  lr : s.lr = s0.lr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  r31 : s.gpr .r31 = kB s0
  scr : ∀ x, ofs (kB s0) x < kZ s0 → s.mem x = m x
  hdr : ∀ i < 14, m.readW (off (kB s0) (8 * i)) 64 = hdrVal s0 i

theorem Fr.of_base {s0 s : State} (h : Base s0 s) : Fr s0 s.mem s :=
  ⟨h.pre, h.sp, h.lr, h.rd, h.wr, h.r31, fun _ _ => rfl, h.hdr⟩

theorem Fr.step {s0 s t : State} {m : Mem} (h : Fr s0 m s) {O : Addr} {L : Nat} (o : Outside O 0 L s.mem t.mem)
    (hs : (⟨O, L⟩ : Region).Disjoint (rS s0)) {rs : List Reg} (k : Keep rs s t)
    (hr : .r31 ∉ rs := by decide) : Fr s0 m t := by
  refine ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ hr).trans h.r31,
    fun x hx => ?_, h.hdr⟩
  rw [out_of_disjoint o hs (x := x) (by simp only [Region.Contains, ofs] at hx ⊢; omega_arith)]; exact h.scr x hx

theorem Fr.of_mem {s0 s t : State} {m : Mem} (h : Fr s0 m s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : .r31 ∉ rs := by decide) : Fr s0 m t :=
  ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ hr).trans h.r31,
    fun x hx => by rw [hm]; exact h.scr x hx, h.hdr⟩

/-- The working space's bytes are `m`'s. -/
theorem Fr.readW {s0 s : State} {m : Mem} (h : Fr s0 m s) {d n : Nat} (hd : d + n / 8 ≤ kZ s0) :
    s.mem.readW (off (kB s0) d) n = m.readW (off (kB s0) d) n := by
  have nw := (kpre h.pre).wS
  refine Mem.readW_congr fun b hb => h.scr _ ?_
  rw [off, Offset.add_add, ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
  omega_arith

/-- The outputs `os` (address, length, array) hold the arrays' low bytes in
`m`, most significant first, under `b`. -/
def Outs (s0 : State) (m : Mem) (b : Bool) (t : Mem) (os : List (Addr × Nat × Nat)) : Prop :=
  ∀ o ∈ os, ∀ c < o.2.1, c < 2 ^ 64 → t (off o.1 c) = if b then m (off (kB s0) (arr (kW s0) o.2.2 + (o.2.1 - 1 - c))) else 0

theorem Outs.step {s0 : State} {m : Mem} {b : Bool} {t t' : Mem} {os : List (Addr × Nat × Nat)}
    (h : Outs s0 m b t os) {O : Addr} {L : Nat} (o : Outside O 0 L t t')
    (hd : ∀ x ∈ os, (⟨O, L⟩ : Region).Disjoint ⟨x.1, x.2.1⟩) : Outs s0 m b t' os := by
  intro x hx c hc hc'
  rw [out_of_disjoint o (hd x hx) (Offset.contains_base _ (by omega_arith) hc')]
  exact h x hx c hc hc'

theorem Outs.cons {s0 : State} {m : Mem} {b : Bool} {t : Mem} {os : List (Addr × Nat × Nat)}
    (h : Outs s0 m b t os) {O : Addr} {L j : Nat}
    (v : ∀ c < L, t (off O c) = if b then m (off (kB s0) (arr (kW s0) j + (L - 1 - c))) else 0) :
    Outs s0 m b t ((O, L, j) :: os) := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact fun c hc _ => v c hc
  · exact h x hx

/-- One output: the pointer in `rP`, the length in `rL`, and array `j`'s low
bytes, masked by `b`. -/
theorem outStage_ok {s0 s : State} {m : Mem} (h : Fr s0 m s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr)
    {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL5 : rL ≠ .r5) {O : Addr} (hO : s.gpr rP = O) {L : Nat}
    (hL : s.gpr rL = BitVec.ofNat 64 L) {b : Bool} (hb : slot m (kB s0) X8 = if b then 1 else 0)
    (hrw : (⟨O, L⟩ : Region) ∈ s0.wr) (hds : (⟨O, L⟩ : Region).Disjoint (rS s0))
    (hOw : O.toNat + L ≤ 2 ^ 64) (hL1 : 1 ≤ L) (hLw : L ≤ 4 * kW s0) {j : Nat} (hj : j < nArr) :
    WP isa (.seq (.block (([.addi .r5 rP 0, .addi .r8 rL 0] : List Instr) ++ mask)) (storeBytes j)) s fun t =>
      Fr s0 m t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
        (∀ c < L, t.mem (off O c) = if b then m (off (kB s0) (arr (kW s0) j + (L - 1 - c))) else 0) ∧
        Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r6, .r8, .r9] s t := by
  have nw := (kpre h.pre).wS
  have hzs := (kpre h.pre).sl
  have hs : Scr s (kB s0) (kZ s0) := hw.scr
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (mv2_ok (s := s) (d₁ := .r5) (d₂ := .r8) hrP hrL hrL5 (by decide))
    fun u' ⟨⟨u5, u8, um⟩, k'⟩ => ?_
  have hsu : Scr u' (kB s0) (kZ s0) := hs.congr k'.wr
  have hm : u'.mem.readW (off (kB s0) X8) 32 = m.readW (off (kB s0) X8) 32 :=
    (h.of_mem k' um).readW (by unfold X8; omega_arith)
  have b2 : WP isa (.block mask) u' fun v =>
      (v.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) ∧ v.gpr .r5 = O ∧
        v.gpr .r8 = BitVec.ofNat 64 L ∧ v.mem = s.mem) ∧ Keep [.r0, .r9] u' v := by
    refine WP.keep _ ?_ (by decide)
    have h31 : u'.gpr .r31 = kB s0 := (k'.gpr _ (by decide)).trans h.r31
    prun [mask, h31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show X8 < 2 ^ 15 by decide),
      hsu.ld (d := X8) (n := 4) (by unfold X8; omega_arith), hm, ofNat_slot _ hb, u5, u8, hO, hL]
    exact um
  refine WP.mono b2 fun v ⟨⟨v9, v5, v8, vm⟩, kv⟩ => ?_
  have kv' : Keep [.r0, .r5, .r8, .r9] s v := (k'.trans kv).mono
  have hwv : Ws v (kB s0) (kZ s0) (kW s0) nArr := hw.of_keep kv'
  have hc : ∀ c < L, (⟨O, L⟩ : Region).Contains (off O c) 1 := fun c hc =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.mono (storeBytes_ok hwv hj (by decide) v5 v8 v9 hL1 hLw
    (fun c hc' => ⟨_, by rw [kv'.wr, h.wr]; exact hrw, hc c hc'⟩)
    (fun c hc' x hx ex => by have := past_of_disjoint hds (hc c hc'); rw [ex] at this; omega_arith) hOw)
    fun t ⟨ht, tb, tout, kt⟩ => ⟨?_, ht, fun c hc' => ?_, by rw [← vm]; exact tout, (kv'.trans kt).mono⟩
  · have fv : Fr s0 m v := h.of_mem kv' vm
    exact fv.step tout hds kt
  · rw [tb c hc', vm]
    cases b
    · rfl
    · simp only [ite_true]
      have := hwv.arr_fit hj
      simp only [S] at this
      refine h.scr _ ?_
      rw [Mont.ofs_off0 _ (by omega_arith)]
      omega_arith

theorem stores_eq : stores = seqs ([.block (([.addi .r5 .r14 0, .addi .r8 .r24 0] : List Instr) ++ mask),
    storeBytes aN, .block (([.addi .r5 .r15 0, .addi .r8 .r24 0] : List Instr) ++ mask), storeBytes aD,
    .block (([.addi .r5 .r16 0, .addi .r8 .r22 0] : List Instr) ++ mask), storeBytes aP,
    .block (([.addi .r5 .r17 0, .addi .r8 .r22 0] : List Instr) ++ mask), storeBytes aQ,
    .block (([.addi .r5 .r18 0, .addi .r8 .r22 0] : List Instr) ++ mask), storeBytes aDP,
    .block (([.addi .r5 .r19 0, .addi .r8 .r22 0] : List Instr) ++ mask), storeBytes aDQ,
    .block (([.addi .r5 .r20 0, .addi .r8 .r22 0] : List Instr) ++ mask), storeBytes aQi,
    .block [.load .w .r3 .r31 X7, .lsl .r3 .r3 1, .load .w .r0 .r31 X8, .add .r3 .r3 .r0]]) := rfl

/-- The seven outputs, last first. -/
abbrev outList (s0 : State) : List (Addr × Nat × Nat) :=
  [(PPC64LE.stackArg s0 4, kL s0, aQi), (PPC64LE.stackArg s0 2, kL s0, aDQ), (PPC64LE.stackArg s0 0, kL s0, aDP),
    (s0.gpr .r9, kL s0, aQ), (s0.gpr .r7, kL s0, aP), (s0.gpr .r5, 2 * kL s0, aD), (s0.gpr .r3, 2 * kL s0, aN)]

theorem status_bv (a b : Bool) :
    (BitVec.ofNat 64 (if a then 1 else 0) <<< 1) + BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (2 * (if a then 1 else 0) + (if b then 1 else 0)) := by
  cases a <;> cases b <;> decide

/-- `stores`: the seven outputs, masked by `b`, and the status in `r3`. -/
theorem stores_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr)
    {a b : Bool} (h7 : slot s.mem (kB s0) X7 = if a then 1 else 0)
    (hb : slot s.mem (kB s0) X8 = if b then 1 else 0) :
    WP isa stores s fun t => Fr s0 s.mem t ∧
      t.gpr .r3 = BitVec.ofNat 64 (2 * (if a then 1 else 0) + (if b then 1 else 0)) ∧
      Outs s0 s.mem b t.mem (outList s0) ∧ Keep [.r0, .r3, .r5, .r6, .r8, .r9] s t := by
  have p := kpre h.pre
  obtain ⟨-, hw16, -, hlw, -⟩ := pre_ws h.pre
  have nl := p.nl
  have dl := p.dl
  have ql := p.ql
  have l1 := p.l1
  have wN := p.wN; have wD := p.wD; have wP := p.wP; have wQ := p.wQ
  have wDp := p.wDp; have wDq := p.wDq; have wQi := p.wQi
  have dpl := p.dpl; have dql := p.dql; have qil := p.qil
  have f0 := Fr.of_base h
  have w24 : s.gpr .r24 = BitVec.ofNat 64 (2 * kL s0) := by rw [ha.r24, ← nl]; exact ofNat_toNat64 _
  have w22 : s.gpr .r22 = BitVec.ofNat 64 (kL s0) := by rw [ha.r22]; exact ofNat_toNat64 _
  have mN : rN s0 ∈ s0.wr := by rw [p.wr]; simp
  have mD : rD s0 ∈ s0.wr := by rw [p.wr]; simp
  have mP : rP s0 ∈ s0.wr := by rw [p.wr]; simp
  have mQ : rQ s0 ∈ s0.wr := by rw [p.wr]; simp
  have mDp : rDp s0 ∈ s0.wr := by rw [p.wr]; simp
  have mDq : rDq s0 ∈ s0.wr := by rw [p.wr]; simp
  have mQi : rQi s0 ∈ s0.wr := by rw [p.wr]; simp
  simp only [rN, rD, rP, rQ, rDp, rDq, rQi, nl, dl, ql, dpl, dql, qil] at mN mD mP mQ mDp mDq mQi
  have pN := p.nS; have pD := p.dS; have pQ := p.qS; have pDp := p.dpS; have pDq := p.dqS; have pQi := p.qiS
  have nD := p.nD; have nP := p.nP; have nQ := p.nQ; have nDp := p.nDp; have nDq := p.nDq; have nQi := p.nQi
  have dP := p.dP; have dQ := p.dQ; have dDp := p.dDp; have dDq := p.dDq; have dQi := p.dQi
  have pQ' := p.pQ; have pDp' := p.pDp; have pDq' := p.pDq; have pQi' := p.pQi
  have qDp := p.qDp; have qDq := p.qDq; have qQi := p.qQi
  have dpDq := p.dpDq; have dpQi := p.dpQi; have dqQi := p.dqQi
  set_option linter.unusedSimpArgs false in
  simp only [rN, rD, rP, rQ, rDp, rDq, rQi, rS, nl, dl, ql, dpl, dql, qil] at pN pD pQ pDp pDq pQi nD nP nQ nDp
  set_option linter.unusedSimpArgs false in
  simp only [rN, rD, rP, rQ, rDp, rDq, rQi, rS, nl, dl, ql, dpl, dql, qil] at nDq nQi dP dQ dDp dDq dQi pQ' pDp'
  set_option linter.unusedSimpArgs false in
  simp only [rN, rD, rP, rQ, rDp, rDq, rQi, rS, nl, dl, ql, dpl, dql, qil] at pDq' pQi' qDp qDq qQi dpDq dpQi
  set_option linter.unusedSimpArgs false in
  simp only [rN, rD, rP, rQ, rDp, rDq, rQi, rS, nl, dl, ql, dpl, dql, qil] at dqQi wD wQ wDp wDq wQi wN
  have pP := p.pS
  rw [stores_eq, wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f0 hw (rP := .r14) (rL := .r24) (by decide) (by decide) (by decide) ha.r14 w24 hb
    mN pN wN (by omega_arith) (by omega_arith) (j := aN) (by decide)) fun t1 ⟨f1, w1, v1, o1, k1⟩ => ?_
  have O1 : Outs s0 s.mem b t1.mem [(s0.gpr .r3, 2 * kL s0, aN)] := Outs.cons (fun _ h => absurd h (by simp)) v1
  have a1 := ha.of_keep k1
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f1 w1 (rP := .r15) (rL := .r24) (by decide) (by decide) (by decide) a1.r15
    (by rw [a1.r24, ← ha.r24]; exact w24) hb mD pD wD (by omega_arith) (by omega_arith) (j := aD) (by decide))
    fun t2 ⟨f2, w2, v2, o2, k2⟩ => ?_
  have O2 := (O1.step o2 (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact nD.symm)).cons v2
  have a2 := a1.of_keep k2
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f2 w2 (rP := .r16) (rL := .r22) (by decide) (by decide) (by decide) a2.r16
    (by rw [a2.r22, ← ha.r22]; exact w22) hb (L := kL s0) mP pP wP (by omega_arith) (by omega_arith) (j := aP) (by decide))
    fun t3 ⟨f3, w3, v3, o3, k3⟩ => ?_
  have O3 := (O2.step o3 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dP.symm, nP.symm⟩)).cons v3
  have a3 := a2.of_keep k3
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f3 w3 (rP := .r17) (rL := .r22) (by decide) (by decide) (by decide) a3.r17
    (by rw [a3.r22, ← ha.r22]; exact w22) hb mQ pQ wQ (by omega_arith) (by omega_arith) (j := aQ) (by decide))
    fun t4 ⟨f4, w4, v4, o4, k4⟩ => ?_
  have O4 := (O3.step o4 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨pQ'.symm, dQ.symm, nQ.symm⟩)).cons v4
  have a4 := a3.of_keep k4
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f4 w4 (rP := .r18) (rL := .r22) (by decide) (by decide) (by decide) a4.r18
    (by rw [a4.r22, ← ha.r22]; exact w22) hb mDp pDp wDp (by omega_arith) (by omega_arith) (j := aDP) (by decide))
    fun t5 ⟨f5, w5, v5, o5, k5⟩ => ?_
  have O5 := (O4.step o5 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨qDp.symm, pDp'.symm, dDp.symm, nDp.symm⟩)).cons v5
  have a5 := a4.of_keep k5
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f5 w5 (rP := .r19) (rL := .r22) (by decide) (by decide) (by decide) a5.r19
    (by rw [a5.r22, ← ha.r22]; exact w22) hb mDq pDq wDq (by omega_arith) (by omega_arith) (j := aDQ) (by decide))
    fun t6 ⟨f6, w6, v6, o6, k6⟩ => ?_
  have O6 := (O5.step o6 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dpDq.symm, qDq.symm, pDq'.symm, dDq.symm, nDq.symm⟩)).cons v6
  have a6 := a5.of_keep k6
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f6 w6 (rP := .r20) (rL := .r22) (by decide) (by decide) (by decide) a6.r20
    (by rw [a6.r22, ← ha.r22]; exact w22) hb mQi pQi wQi (by omega_arith) (by omega_arith) (j := aQi) (by decide))
    fun t7 ⟨f7, w7, v7, o7, k7⟩ => ?_
  have O7 := (O6.step o7 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dqQi.symm, dpQi.symm, qQi.symm, pQi'.symm, dQi.symm, nQi.symm⟩)).cons v7
  rw [show seqs [.block [.load .w .r3 .r31 X7, .lsl .r3 .r3 1, .load .w .r0 .r31 X8, .add .r3 .r3 .r0]] =
    .block [.load .w .r3 .r31 X7, .lsl .r3 .r3 1, .load .w .r0 .r31 X8, .add .r3 .r3 .r0] from rfl]
  have hzs := p.sl
  have hm7 : t7.mem.readW (off (kB s0) X7) 32 = s.mem.readW (off (kB s0) X7) 32 :=
    f7.readW (by unfold X7; omega_arith)
  have hm8 : t7.mem.readW (off (kB s0) X8) 32 = s.mem.readW (off (kB s0) X8) 32 :=
    f7.readW (by unfold X8; omega_arith)
  have hb4 : WP isa (.block [.load .w .r3 .r31 X7, .lsl .r3 .r3 1, .load .w .r0 .r31 X8, .add .r3 .r3 .r0]) t7
      fun t => (t.gpr .r3 = BitVec.ofNat 64 (2 * (if a then 1 else 0) + (if b then 1 else 0)) ∧ t.mem = t7.mem) ∧
        Keep [.r0, .r3] t7 t := by
    refine WP.keep _ ?_ (by decide)
    prun [f7.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show X7 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show X8 < 2 ^ 15 by decide),
      w7.scr.ld (d := X7) (n := 4) (by unfold X7; omega_arith), w7.scr.ld (d := X8) (n := 4) (by unfold X8; omega_arith),
      hm7, hm8, ofNat_slot _ h7, ofNat_slot _ hb]
    exact status_bv a b
  refine WP.mono hb4 fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨f7.of_mem kt tm, t3, by rw [tm]; exact O7, ?_⟩
  exact ((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans kt)).mono

end VG.Proof.RsaKeyGen.PPC64LE.Key
