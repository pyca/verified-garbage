module

import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# `vg_rsa_crt_values` on PPC64LE: the results written out

`Fr s0 m s`: what the stores keep, from the memory `m` before them: the
registers and regions of `Base` and the working space (`m`'s).
`outStage_ok`: one result's bytes, masked; `stores_ok`: all three
and the mask's bit in `r3`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (mask storeBytes stores sMask aDR2 aDR3 nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- What the stores keep, from the memory `m` before them. -/
structure Fr (s0 : State) (m : Mem) (s : State) : Prop where
  pre : cvP.pre s0
  sp : s.sp = s0.sp
  lr : s.lr = s0.lr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  r31 : s.gpr .r31 = cvB s0
  scr : ∀ x, ofs (cvB s0) x < cvZ s0 → s.mem x = m x
  hdr : ∀ i < 14, m.readW (off (cvB s0) (8 * i)) 64 = hdrVal s0 i

theorem Fr.of_base {s0 s : State} (h : Base s0 s) : Fr s0 s.mem s :=
  ⟨h.pre, h.sp, h.lr, h.rd, h.wr, h.r31, fun _ _ => rfl, h.hdr⟩

/-- A byte of a region apart from a range that changed. -/
theorem out_of_disjoint {O : Addr} {L : Nat} {m m' : Mem} (o : Outside O 0 L m m') {r : Region}
    (hd : (⟨O, L⟩ : Region).Disjoint r) {x : Addr} (hx : r.Contains x 1) : m' x = m x := by
  refine o x (Or.inr ?_)
  by_contra hc
  exact hd x (by simp only [Region.Contains, ofs] at hc ⊢; omega_arith) hx

theorem Fr.step {s0 s t : State} {m : Mem} (h : Fr s0 m s) {O : Addr} {L : Nat} (o : Outside O 0 L s.mem t.mem)
    (hs : (⟨O, L⟩ : Region).Disjoint ⟨cvB s0, cvZ s0⟩) {rs : List Reg} (k : Keep rs s t)
    (hr : .r31 ∉ rs := by decide) : Fr s0 m t := by
  refine ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ hr).trans h.r31,
    fun x hx => ?_, h.hdr⟩
  rw [out_of_disjoint o hs (x := x) (by simp only [Region.Contains, ofs] at hx ⊢; omega_arith)]; exact h.scr x hx

theorem Fr.of_mem {s0 s t : State} {m : Mem} (h : Fr s0 m s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : .r31 ∉ rs := by decide) : Fr s0 m t :=
  ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ hr).trans h.r31,
    fun x hx => by rw [hm]; exact h.scr x hx, h.hdr⟩

/-- The working space's bytes are `m`'s. -/
theorem Fr.readW {s0 s : State} {m : Mem} (h : Fr s0 m s) {d n : Nat} (hd : d + n / 8 ≤ cvZ s0) :
    s.mem.readW (off (cvB s0) d) n = m.readW (off (cvB s0) d) n := by
  obtain ⟨-, nw, -, -, -⟩ := pre_scr h.pre
  refine Mem.readW_congr fun b hb => h.scr _ ?_
  rw [off, Offset.add_add, ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
  omega_arith

theorem ofNat_slot (x : BitVec 32) {b : Bool} (h : x.toNat = if b then 1 else 0) :
    x.setWidth 64 = BitVec.ofNat 64 (if b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

/-- One result: the pointer in `rP`, the length in `rL`, and array `j`'s low
bytes, masked by `b`. -/
theorem outStage_ok {s0 s : State} {m : Mem} (h : Fr s0 m s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr)
    {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL5 : rL ≠ .r5) {O : Addr} (hO : s.gpr rP = O) {L : Nat}
    (hL : s.gpr rL = BitVec.ofNat 64 L) {b : Bool} (hb : slot m (cvB s0) sMask = if b then 1 else 0)
    (hrw : (⟨O, L⟩ : Region) ∈ s0.wr) (hds : (⟨O, L⟩ : Region).Disjoint ⟨cvB s0, cvZ s0⟩)
    (hOw : O.toNat + L ≤ 2 ^ 64) (hL1 : 1 ≤ L) (hLw : L ≤ 4 * cvW s0) {j : Nat} (hj : j < nArr) :
    WP isa (.seq (.block (([.addi .r5 rP 0, .addi .r8 rL 0] : List Instr) ++ mask)) (storeBytes j)) s fun t =>
      Fr s0 m t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
        (∀ c < L, t.mem (off O c) = if b then m (off (cvB s0) (arr (cvW s0) j + (L - 1 - c))) else 0) ∧
        Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r6, .r8, .r9] s t := by
  obtain ⟨-, nw, hzs, -, -⟩ := pre_scr h.pre
  have fit := hw.arr_fit hj
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  have hs : Scr s (cvB s0) (cvZ s0) := hw.scr
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (mv2_ok (s := s) (d₁ := .r5) (d₂ := .r8) hrP hrL hrL5 (by decide))
    fun u' ⟨⟨u5, u8, um⟩, k'⟩ => ?_
  have hsu : Scr u' (cvB s0) (cvZ s0) := hs.congr k'.wr
  have hm : u'.mem.readW (off (cvB s0) sMask) 32 = m.readW (off (cvB s0) sMask) 32 :=
    (h.of_mem k' um).readW (by unfold sMask; omega_arith)
  have b2 : WP isa (.block mask) u' fun v =>
      (v.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) ∧ v.gpr .r5 = O ∧
        v.gpr .r8 = BitVec.ofNat 64 L ∧ v.mem = s.mem) ∧ Keep [.r0, .r9] u' v := by
    refine WP.keep _ ?_ (by decide)
    have h31 : u'.gpr .r31 = cvB s0 := (k'.gpr _ (by decide)).trans h.r31
    prun [mask, h31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sMask < 2 ^ 15 by decide),
      hsu.ld (d := sMask) (n := 4) (by unfold sMask; omega_arith), hm, ofNat_slot _ hb, u5, u8, hO, hL]
    exact um
  refine WP.mono b2 fun v ⟨⟨v9, v5, v8, vm⟩, kv⟩ => ?_
  have kv' : Keep [.r0, .r5, .r8, .r9] s v := (k'.trans kv).mono
  have hwv : Ws v (cvB s0) (cvZ s0) (cvW s0) nArr := hw.of_keep kv'
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
      refine h.scr _ ?_
      rw [Mont.ofs_off0 _ (by omega_arith)]
      omega_arith

theorem wp_seqs_pair {a b : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (a :: b :: l)) s Q ↔ WP isa (.seq a b) s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | c :: l', _ =>
    change WP isa (.seq a (.seq b (seqs (c :: l')))) s Q ↔ _
    exact ⟨fun h => WP.seq_iff.mpr (WP.mono (WP.seq_iff.mp h) fun _ hu => WP.seq_iff.mp hu),
      fun h => WP.seq_iff.mpr (WP.mono (WP.seq_iff.mp h) fun _ hu => WP.seq_iff.mpr hu)⟩

/-- `stores`: the three results, masked by the mask's bit `b`, and `b` in `r3`. -/
theorem stores_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {b : Bool}
    (hb : slot s.mem (cvB s0) sMask = if b then 1 else 0) :
    WP isa stores s fun t => Fr s0 s.mem t ∧ t.gpr .r3 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      (∀ c < (PPC64LE.stackArg s0 1).toNat, t.mem (off (s0.gpr .r3) c) =
        if b then s.mem (off (cvB s0) (arr (cvW s0) aDR2 + ((PPC64LE.stackArg s0 1).toNat - 1 - c))) else 0) ∧
      (∀ c < (PPC64LE.stackArg s0 3).toNat, t.mem (off (s0.gpr .r5) c) =
        if b then s.mem (off (cvB s0) (arr (cvW s0) aDR3 + ((PPC64LE.stackArg s0 3).toNat - 1 - c))) else 0) ∧
      (∀ c < (PPC64LE.stackArg s0 1).toNat, t.mem (off (s0.gpr .r7) c) =
        if b then s.mem (off (cvB s0) (arr (cvW s0) 3 + ((PPC64LE.stackArg s0 1).toNat - 1 - c))) else 0) ∧
      Keep [.r0, .r3, .r5, .r6, .r8, .r9] s t := by
  obtain ⟨-, -, hwr, d12, d13, -, -, -, -, d1s, -, d23, -, -, -, -, d2s, -, -, -, -, -, d3s, -, -, -, -, -,
    -, w1, w2, w3, -, -, -, -, -, -, p1, p2, q1, q2, e4, e8, e6, -, -, -⟩ := h.pre
  obtain ⟨-, -, hkw⟩ := pre_ws h.pre |>.2
  rw [e4] at d12 d13 d1s w1
  rw [e6] at d12 d23 d2s w2
  rw [e8] at d13 d23 d3s w3
  have hk2 : (s0.gpr .r10).toNat ≤ 4 * cvW s0 := hkw
  have f0 := Fr.of_base h
  rw [stores, wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f0 hw (rP := .r14) (rL := .r20) (by decide) (by decide) (by decide) ha.r14
    (by rw [ha.r20]; exact ofNat_toNat64 _) hb (by rw [hwr, ← e4]; simp) d1s w1 p1 (by omega_arith) (j := aDR2)
    (by decide)) fun t1 ⟨f1, w1', v1, o1, k1⟩ => ?_
  have a1 := ha.of_keep k1
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f1 w1' (rP := .r15) (rL := .r22) (by decide) (by decide) (by decide) a1.r15
    (by rw [a1.r22]; exact ofNat_toNat64 _) hb (by rw [hwr, ← e6]; simp) d2s w2 q1 (by omega_arith) (j := aDR3)
    (by decide)) fun t2 ⟨f2, w2', v2, o2, k2⟩ => ?_
  have a2 := a1.of_keep k2
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outStage_ok f2 w2' (rP := .r16) (rL := .r20) (by decide) (by decide) (by decide) a2.r16
    (by rw [a2.r20]; exact ofNat_toNat64 _) hb (by rw [hwr, ← e8]; simp) d3s w3 p1 (by omega_arith) (j := 3)
    (by decide)) fun t3 ⟨f3, w3', v3, o3, k3⟩ => ?_
  rw [show seqs [.block [.load .w .r3 .r31 sMask]] = .block [.load .w .r3 .r31 sMask] from rfl]
  obtain ⟨-, nw, hzs, -, -⟩ := pre_scr h.pre
  have hm : t3.mem.readW (off (cvB s0) sMask) 32 = s.mem.readW (off (cvB s0) sMask) 32 :=
    f3.readW (by unfold sMask; omega_arith)
  have hb4 : WP isa (.block [.load .w .r3 .r31 sMask]) t3 fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if b then 1 else 0) ∧ t.mem = t3.mem) ∧ Keep [.r3] t3 t := by
    refine WP.keep _ ?_ (by decide)
    prun [f3.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sMask < 2 ^ 15 by decide),
      w3'.scr.ld (d := sMask) (n := 4) (by unfold sMask; omega_arith), hm, ofNat_slot _ hb]
  refine WP.mono hb4 fun t ⟨⟨t3', tm⟩, kt⟩ => ⟨f3.of_mem kt tm, t3', fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, (((k1.trans k2).trans k3).trans kt).mono⟩
  · have cc : (⟨s0.gpr .r3, (PPC64LE.stackArg s0 1).toNat⟩ : Region).Contains (off (s0.gpr .r3) c) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [tm, out_of_disjoint o3 d13.symm cc, out_of_disjoint o2 d12.symm cc]
    exact v1 c hc
  · have cc : (⟨s0.gpr .r5, (PPC64LE.stackArg s0 3).toNat⟩ : Region).Contains (off (s0.gpr .r5) c) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [tm, out_of_disjoint o3 d23.symm cc]
    exact v2 c hc
  · rw [tm]; exact v3 c hc

end VG.Proof.Rsa.PPC64LE.CrtValues
