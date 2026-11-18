module

-- separate module: builds in parallel with the constant time of the entry and the check (`RdCT1.lean`)
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdTwos
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdGcd
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSquare
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdDiv
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSqrt
import VerifiedGarbage.Proof.Rsa.RecoverRoot
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdEntry
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.BoolNat
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdMulW
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
public import Init.Data.Int.Order
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import VerifiedGarbage.Spec.Rsa
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Rsa.PPC64LE.RdFinish`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: `d e`, and the factors or zeros written out

`prod_ok`: `M = d e` by rows of words (`mulW`). `fail_ok`: zeros to `p` and `q`, and 0 in
`r3`; `stores_ok`: both factors, masked, and the mask returned. `NOk`: a
valid modulus is odd and above 1.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.Recover (fail)

/-- An output region: writable, apart from the working space. -/
structure OutR (s0 : State) (O : Addr) (L : Nat) : Prop where
  wr : (⟨O, L⟩ : Region) ∈ s0.wr
  disj : (⟨O, L⟩ : Region).Disjoint ⟨rvB s0, rvZ s0⟩
  nowrap : O.toNat + L ≤ 2 ^ 64
  l1 : 1 ≤ L
  l2 : L < 2 ^ 32

/-- Memory in the working space is kept by a write outside it. -/
theorem OutR.inside {s0 : State} {O : Addr} {L : Nat} (h : OutR s0 O L) {m m' : Mem} (o : Outside O 0 L m m') :
    ∀ x, ofs (rvB s0) x < rvZ s0 → m' x = m x := fun x hx =>
  CrtValues.out_of_disjoint o h.disj (by simp only [Region.Contains, ofs] at hx ⊢; omega_using [hx])

/-- Zeros to the `L` bytes at `O`, from the pointer in `rP` and the length in `rL`. -/
theorem zeroOut_ok {s0 s : State} (h : RFin s0 s) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0)
    (hrL5 : rL ≠ .r5) {O : Addr} (hO : s.gpr rP = O) {L : Nat} (hL : s.gpr rL = BitVec.ofNat 64 L)
    (ho : OutR s0 O L) :
    WP isa (.seq (.block [.addi .r5 rP 0, .addi .r8 rL 0]) VG.Impl.Rsa.PPC64LE.CrtValues.zeroBytes) s fun t =>
      RFin s0 t ∧ (∀ c < L, t.mem (off O c) = 0) ∧ Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r8] s t := by
  rw [WP.seq_iff]
  refine WP.mono (CrtValues.mv2_ok (s := s) (d₁ := .r5) (d₂ := .r8) hrP hrL hrL5 (by decide))
    fun v ⟨⟨v5, v8, um⟩, kv⟩ => ?_
  refine WP.mono (Keys.zeroBytes_ok (v5.trans hO) (v8.trans hL) ho.l1 ho.l2
    (fun c hc => ⟨_, by rw [kv.wr, h.wr]; exact ho.wr, Offset.contains_base _ (by omega_using [hc]) (by have := ho.nowrap; omega_using [hc, this])⟩)
    ho.nowrap) fun t ⟨tz, tout, kt⟩ => ?_
  have tout' : Outside O 0 L s.mem t.mem := fun x hx => (tout x hx).trans (congrFun um x)
  exact ⟨h.of_out (rs := [.r0, .r5, .r8]) (ho.inside tout') (kv.trans kt).mono, tz, tout', (kv.trans kt).mono⟩

/-- `p` and `q` as outputs. -/
theorem out_p {s0 : State} (h : rvPre s0) : OutR s0 (s0.gpr .r3) (kK s0) := by
  obtain ⟨-, -, hwr, -, -, -, -, ps, -, -, -, -, -, -, -, -, -, -, wp, -, -, -, -, -, ⟨hk, hk'⟩, e4, -⟩ := h
  rw [e4] at ps wp
  exact ⟨by rw [hwr]; simp [e4, kK], ps, wp, by simp only [kK]; omega_using [hk], by simp only [kK]; omega_using [hk']⟩

theorem out_q {s0 : State} (h : rvPre s0) : OutR s0 (s0.gpr .r5) (kK s0) := by
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, qs, -, -, -, -, -, -, wq, -, -, -, -, ⟨hk, hk'⟩, -, e6, -⟩ := h
  rw [e6] at qs wq
  exact ⟨by rw [hwr]; simp [e6, kK], qs, wq, by simp only [kK]; omega_using [hk], by simp only [kK]; omega_using [hk']⟩

theorem pq_disj {s0 : State} (h : rvPre s0) :
    (⟨s0.gpr .r3, kK s0⟩ : Region).Disjoint ⟨s0.gpr .r5, kK s0⟩ := by
  obtain ⟨-, -, -, pq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e4, e6, -⟩ := h
  rw [e4, e6] at pq
  exact pq

/-- `fail`: zeros to `p` and `q`, and 0 in `r3`. -/
theorem fail_ok {s0 s : State} (h : RFin s0 s) (h21 : s.gpr .r21 = s0.gpr .r3) (h23 : s.gpr .r23 = s0.gpr .r5)
    (h25 : s.gpr .r25 = s0.gpr .r8) :
    WP isa fail s fun t => RFin s0 t ∧ t.gpr .r3 = 0 ∧
      (∀ c < kK s0, t.mem (off (s0.gpr .r3) c) = 0) ∧ (∀ c < kK s0, t.mem (off (s0.gpr .r5) c) = 0) ∧
      Keep [.r0, .r3, .r5, .r8] s t := by
  have op := out_p h.pre
  have oq := out_q h.pre
  have dpq := pq_disj h.pre
  rw [fail, CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok h (rP := .r21) (rL := .r25) (by decide) (by decide) (by decide) h21
    (by rw [h25]; exact CrtValues.ofNat_toNat64 _) op) fun t1 ⟨f1, v1, _, k1⟩ => ?_
  rw [CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok f1 (rP := .r23) (rL := .r25) (by decide) (by decide) (by decide)
    (by rw [k1.gpr _ (by decide), h23]) (by rw [k1.gpr _ (by decide), h25]; exact CrtValues.ofNat_toNat64 _) oq)
    fun t2 ⟨f2, v2, o2, k2⟩ => ?_
  rw [show seqs [.block [.li .r3 0]] = .block [.li .r3 0] from rfl]
  have hb : WP isa (.block [.li .r3 0]) t2 fun t => (t.gpr .r3 = 0 ∧ t.mem = t2.mem) ∧ Keep [.r3] t2 t := by
    refine WP.keep _ ?_ (by decide)
    prun []
    rfl
  refine WP.mono hb fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨f2.of_out (fun x _ => congrFun tm x) kt, t3, fun c hc => ?_,
    fun c hc => by rw [tm]; exact v2 c hc, ((k1.trans k2).trans kt).mono⟩
  have cc : (⟨s0.gpr .r3, kK s0⟩ : Region).Contains (off (s0.gpr .r3) c) 1 :=
    Offset.contains_base _ (by omega_using [hc]) (by have := op.nowrap; omega_using [hc, this])
  rw [tm, CrtValues.out_of_disjoint o2 dpq.symm cc]
  exact v1 c hc

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (stores nArr sMask)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (mask storeBytes)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- One factor: the pointer in `rP`, the length in `rL`, and array `j`'s low
bytes, masked by `b`. -/
theorem outR_ok {s0 s : State} (h : RFin s0 s) (hw : Ws s (rvB s0) (rvZ s0) (ww (kK s0)) nArr)
    {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL5 : rL ≠ .r5) {O : Addr} (hO : s.gpr rP = O) {L : Nat}
    (hL : s.gpr rL = BitVec.ofNat 64 L) {b : Bool} (hb : slot s.mem (rvB s0) sMask = b2n b)
    (ho : OutR s0 O L) (hLw : L ≤ 4 * ww (kK s0)) {j : Nat} (hj : j < nArr) :
    WP isa (.seq (.block (([.addi .r5 rP 0, .addi .r8 rL 0] : List Instr) ++ mask)) (storeBytes j)) s fun t =>
      RFin s0 t ∧ Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr ∧
        (∀ x, ofs (rvB s0) x < rvZ s0 → t.mem x = s.mem x) ∧
        (∀ c < L, t.mem (off O c) = if b then s.mem (off (rvB s0) (arr (ww (kK s0)) j + (L - 1 - c))) else 0) ∧
        Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r6, .r8, .r9] s t := by
  have hz : 160 ≤ rvZ s0 := hw.hdr_le
  have fit := hw.arr_fit hj
  have nw := hw.nowrap
  have hS : S (ww (kK s0)) = 4 * (ww (kK s0) + 2) := rfl
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (CrtValues.mv2_ok (s := s) (d₁ := .r5) (d₂ := .r8) hrP hrL hrL5 (by decide))
    fun u' ⟨⟨u5, u8, um⟩, k'⟩ => ?_
  have hwu := hw.of_keep k'
  have b2 : WP isa (.block mask) u' fun v =>
      (v.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) ∧ v.gpr .r5 = O ∧
        v.gpr .r8 = BitVec.ofNat 64 L ∧ v.mem = s.mem) ∧ Keep [.r0, .r9] u' v := by
    refine WP.keep _ ?_ (by decide)
    have hb' : slot u'.mem (rvB s0) VG.Impl.Rsa.PPC64LE.CrtValues.sMask = if b then 1 else 0 := by
      rw [um]; exact hb.trans (by cases b <;> rfl)
    prun [mask, hwu.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide)
        (show VG.Impl.Rsa.PPC64LE.CrtValues.sMask < 2 ^ 15 by decide),
      hwu.scr.ld (d := VG.Impl.Rsa.PPC64LE.CrtValues.sMask) (n := 4)
        (by simp only [VG.Impl.Rsa.PPC64LE.CrtValues.sMask]; omega_arith),
      ld_slot hb', u5, u8, hO, hL]
    exact um
  refine WP.mono b2 fun v ⟨⟨v9, v5, v8, vm⟩, kv⟩ => ?_
  have kv' : Keep [.r0, .r5, .r8, .r9] s v := (k'.trans kv).mono
  have hwv : Ws v (rvB s0) (rvZ s0) (ww (kK s0)) nArr := hw.of_keep kv'
  have hc : ∀ c < L, (⟨O, L⟩ : Region).Contains (off O c) 1 := fun c hc =>
    Offset.contains_base _ (by omega_arith) (by have := ho.nowrap; omega_arith)
  refine WP.mono (Keys.storeBytes_ok hwv hj (by decide) v5 v8 v9 ho.l1 hLw
    (fun c hc' => ⟨_, by rw [kv'.wr, h.wr]; exact ho.wr, hc c hc'⟩)
    (fun c hc' x hx ex => by
      have := CrtValues.past_of_disjoint ho.disj (hc c hc'); rw [ex] at this; omega_arith) ho.nowrap)
    fun t ⟨ht, tb, tout, kt⟩ => ?_
  have tout' : Outside O 0 L s.mem t.mem := by rw [← vm]; exact tout
  have ins := ho.inside tout'
  have K : Keep [.r0, .r5, .r6, .r8, .r9] s t := (kv'.trans kt).mono
  refine ⟨h.of_out ins K, ht, ins, fun c hc' => ?_, tout', K⟩
  rw [tb c hc', vm]

/-- A slot kept by a step that keeps the working space. -/
theorem slot_ins {s0 : State} {m m' : Mem} (ins : ∀ x, ofs (rvB s0) x < rvZ s0 → m' x = m x)
    (nw : (rvB s0).toNat + rvZ s0 ≤ 2 ^ 64) {d : Nat} (hd : d + 4 ≤ rvZ s0) : slot m' (rvB s0) d = slot m (rvB s0) d := by
  simp only [slot, w32]
  refine congrArg BitVec.toNat (Mem.readW_congr fun b hb => ins _ ?_)
  rw [off, VG.Offset.add_add, ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
  omega_arith

/-- `stores`: both factors, masked by `b`, and the mask into `r3`. -/
theorem stores_ok {s0 s : State} (h : RFin s0 s) (hw : Ws s (rvB s0) (rvZ s0) (ww (kK s0)) nArr)
    (h21 : s.gpr .r21 = s0.gpr .r3) (h23 : s.gpr .r23 = s0.gpr .r5) (h25 : s.gpr .r25 = s0.gpr .r8) {b : Bool}
    (hb : slot s.mem (rvB s0) sMask = b2n b) :
    WP isa stores s fun t => RFin s0 t ∧ t.gpr .r3 = BitVec.ofNat 64 (b2n b) ∧
      (∀ c < kK s0, t.mem (off (s0.gpr .r3) c) =
        if b then s.mem (off (rvB s0) (arr (ww (kK s0)) 5 + (kK s0 - 1 - c))) else 0) ∧
      (∀ c < kK s0, t.mem (off (s0.gpr .r5) c) =
        if b then s.mem (off (rvB s0) (arr (ww (kK s0)) 6 + (kK s0 - 1 - c))) else 0) := by
  have z := h.pre
  have op := out_p h.pre
  have oq := out_q h.pre
  have dpq := pq_disj h.pre
  have hk : kK s0 ≤ 4 * ww (kK s0) := by simp only [ww]; omega_arith
  have nw := hw.nowrap
  have hz : 160 ≤ rvZ s0 := hw.hdr_le
  have fit5 := hw.arr_fit (j := 5) (by decide)
  have fit6 := hw.arr_fit (j := 6) (by decide)
  have hS : S (ww (kK s0)) = 4 * (ww (kK s0) + 2) := rfl
  have hL : s.gpr .r25 = BitVec.ofNat 64 (kK s0) := by rw [h25]; exact CrtValues.ofNat_toNat64 _
  rw [stores, CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (outR_ok h hw (rP := .r21) (rL := .r25) (by decide) (by decide) (by decide) h21 hL hb op hk
    (j := 5) (by decide)) fun t1 ⟨f1, w1, ins1, v1, _, k1⟩ => ?_
  rw [CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  have hb1 : slot t1.mem (rvB s0) sMask = b2n b := by
    rw [slot_ins ins1 nw (by simp only [sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask]; omega_arith)]; exact hb
  refine WP.mono (outR_ok f1 w1 (rP := .r23) (rL := .r25) (by decide) (by decide) (by decide)
    (by rw [k1.gpr _ (by decide), h23]) (by rw [k1.gpr _ (by decide)]; exact hL) hb1 oq hk
    (j := 6) (by decide)) fun t2 ⟨f2, w2, ins2, v2, o2, k2⟩ => ?_
  rw [show seqs [Code.block [Instr.load .w .r3 .r31 sMask]] = .block [.load .w .r3 .r31 sMask] from rfl]
  have hb2 : slot t2.mem (rvB s0) sMask = b2n b := by
    rw [slot_ins ins2 nw (by simp only [sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask]; omega_arith)]; exact hb1
  refine WP.mono (WP.keep [.r3] (Q := fun x => x.gpr .r3 = BitVec.ofNat 64 (b2n b) ∧ x.mem = t2.mem)
    (by prun [w2.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sMask < 2 ^ 15 by decide),
      w2.scr.ld (d := sMask) (n := 4) (by simp only [sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask]; omega_arith),
      ld_slot hb2]) (by decide)) fun t ⟨⟨a3, mt⟩, kt⟩ => ?_
  refine ⟨f2.of_out (fun x _ => by rw [mt]) kt, a3, fun c hc => ?_, fun c hc => ?_⟩
  · have cc : (⟨s0.gpr .r3, kK s0⟩ : Region).Contains (off (s0.gpr .r3) c) 1 :=
      Offset.contains_base _ (by omega_arith) (by have := op.nowrap; omega_arith)
    rw [mt, CrtValues.out_of_disjoint o2 dpq.symm cc]
    exact v1 c hc
  · rw [mt, v2 c hc]
    cases b
    · rfl
    · simp only [ite_true]
      refine ins1 _ ?_
      rw [Mont.ofs_off0 _ (by omega_arith)]
      omega_arith

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (loads prod nArr aN aOne aZ wZ wE wD wM)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- A step on arrays below `J` (of `v` digits) keeps what is from array `J` on. -/
theorem keep_far {B : Addr} {v J : Nat} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep B v js ds m m') (hj : ∀ j ∈ js, j < J)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) {d n : Nat} (hd1 : arr v J ≤ d) (hd2 : d + 4 * n ≤ 2 ^ 64) :
    val32 m' B d n = val32 m B d n := by
  refine Outs.val32 k (fun r hr => ?_) hd2
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj', rfl⟩ | ⟨e, he, rfl⟩
  · right
    have := VG.Proof.Rsa.KeyWorkspace.arr_mono (w := v) (show j + 1 ≤ J by have := hj j hj'; omega_arith)
    rw [VG.Proof.Rsa.KeyWorkspace.arr_succ] at this
    dsimp only; omega_arith
  · right; have := hd e he; have : 160 ≤ arr v J := Nat.le_add_right _ _; dsimp only; omega_arith

/-- A step on the `W` view's arrays up to 8 keeps the key arrays from 18 on. -/
theorem keepW_far {s0 : State} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep (rvB s0) (wW (kK s0)) js ds m m') (hj : ∀ j ∈ js, j ≤ 8)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) {d n : Nat} (hd1 : arr (wW (kK s0)) 9 ≤ d) (hd2 : d + 4 * n ≤ 2 ^ 64) :
    val32 m' (rvB s0) d n = val32 m (rvB s0) d n :=
  keep_far k (fun j h => Nat.lt_succ_of_le (hj j h)) hd hd1 hd2

theorem arrW9 (w : Nat) : arr (2 * w + 2) 9 = arr w 18 := by
  simp only [arr, S, KeyWorkspace.hdr]; omega_arith

theorem shl3 (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem os2ip_lt8 (bs : List Byte) : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
  have := VG.Proof.Rsa.lt_of_os2ip bs
  rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this

theorem shr3_ofNat {L : Nat} (hL : L + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((L + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [hL]

/-- The low `2 R` digits of a number below `2^(64 R)` are the number. -/
theorem val32_low_words {m : Mem} {B : Addr} {d W R v : Nat} (hv : val32 m B d W = v) (hvR : v < 2 ^ (64 * R))
    (hR : 2 * R ≤ W) : wordsVal m B d R = v := by
  have e := val32_append m B d (2 * R) (W - 2 * R)
  rw [show 2 * R + (W - 2 * R) = W by omega_using [hR], hv, show 32 * (2 * R) = 64 * R by omega_using []] at e
  rw [wordsVal_eq_val32]
  have := Nat.one_le_two_pow (n := 64 * R)
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * (2 * R)) (W - 2 * R)) with h0 | h0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (64 * R) ≤ 2 ^ (64 * R) * val32 m B (d + 4 * (2 * R)) (W - 2 * R) := Nat.le_mul_of_pos_right _ h0
    omega_using [hvR, e, this]

/-- `prod`: `M = d e` in the array `wM` of the `W` view, by a row of words for each word of `e`. -/
theorem prod_ok {s0 t : State} (h : LdD s0 t) :
    WP isa prod t fun u => Ws u (rvB s0) (rvZ s0) (wW (kK s0)) 16 ∧
      KeyWorkspace.Keep (rvB s0) (wW (kK s0)) [wM] [] t.mem u.mem ∧
      num u.mem (rvB s0) (wW (kK s0)) wM = dV s0 * eV s0 ∧
      num u.mem (rvB s0) (wW (kK s0)) wZ = 0 ∧ Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t u := by
  have z := h.base.sz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, e1, e2, d1, d2,
    -⟩ := id h.base.pre
  have w1 := z.w1; have w2 := z.w2; have kw := z.kw
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  have w16 : Ws t (rvB s0) (rvZ s0) (wW (kK s0)) 16 := h.ws
  have fit : ∀ j < 16, arr (wW (kK s0)) j + S (wW (kK s0)) ≤ 2 ^ 64 := fun j hj => w16.fit64 hj
  unfold prod
  refine WP.seq ?_
  -- `R = ⌈e_len / 8⌉` rows.
  have e27 : t.gpr .r27 = BitVec.ofNat 64 (s0.gpr .r10).toNat := by rw [h.r27, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h27 : Reg.r27 ≠ .r0 := by decide
  have hsh := shr3_ofNat (L := (s0.gpr .r10).toNat) (by omega_arith)
  refine WP.mono (WP.keep [.r4] (Q := fun u => u.gpr .r4 = BitVec.ofNat 64 (((s0.gpr .r10).toNat + 7) / 8) ∧
    u.mem = t.mem) (by prun [e27, exec_addi h27 (show 7 < 2 ^ 15 by decide), hsh]) (by decide))
    fun t2 ⟨⟨a4, m2⟩, k2⟩ => ?_
  have w2' := w16.of_keep k2
  -- The values before the product.
  have nZ : num t2.mem (rvB s0) (wW (kK s0)) wZ = 0 := by
    rw [m2]; exact CrtValues.val32_of_zero fun i hi => h.zW wZ (by decide) i (by omega_arith)
  have nE : num t2.mem (rvB s0) (wW (kK s0)) wE = eV s0 := by rw [m2]; exact h.vE
  have nD : num t2.mem (rvB s0) (wW (kK s0)) wD = dV s0 := by rw [m2]; exact h.vD
  have bD : dV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) := by
    have := os2ip_lt8 (dB s0); simp only [dB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have bE : eV s0 < 2 ^ (8 * (s0.gpr .r10).toNat) := by
    have := os2ip_lt8 (eB s0); simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have fitT : 8 * (PPC64LE.stackArg s0 1).toNat + 8 * (s0.gpr .r10).toNat ≤ 32 * wW (kK s0) - 1 := by
    rw [hW]; omega_arith
  have hR2 : 2 * (((s0.gpr .r10).toNat + 7) / 8) ≤ wW (kK s0) := by rw [hW]; omega_arith
  have bE' : eV s0 < 2 ^ (64 * (((s0.gpr .r10).toNat + 7) / 8)) :=
    Nat.lt_of_lt_of_le bE (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have eW2 : 2 * (wW (kK s0) / 2) = wW (kK s0) := by rw [hW]; omega_using []
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Recover.mulW_ok w2' (by decide) (o := wM) (x := wE) (y := wD)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hW]; omega_using []) a4 (by omega_arith) hR2)
    fun u ⟨wu, ku, val, kru⟩ => ?_
  have hDw : wordsVal t2.mem (rvB s0) (arr (wW (kK s0)) wD) (wW (kK s0) / 2) = dV s0 := by
    rw [wordsVal_eq_val32, eW2]; exact nD
  rw [val32_low_words nE bE' hR2, hDw] at val
  refine ⟨wu, ?_, ?_, ?_, (k2.trans kru).mono (by decide)⟩
  · rw [m2] at ku; exact ku
  · show val32 _ _ _ (wW (kK s0)) = _
    rw [show val32 u.mem (rvB s0) (arr (wW (kK s0)) wM) (wW (kK s0)) =
        wordsVal u.mem (rvB s0) (arr (wW (kK s0)) wM) (wW (kK s0) / 2) by rw [wordsVal_eq_val32, eW2],
      val, show 64 * (wW (kK s0) / 2) = 32 * wW (kK s0) by omega_using [hW],
      Nat.mul_comm, Nat.mod_eq_of_lt]
    calc dV s0 * eV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) * 2 ^ (8 * (s0.gpr .r10).toNat) :=
          Nat.mul_lt_mul'' bD bE
      _ = 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat + 8 * (s0.gpr .r10).toNat) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (32 * wW (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega_using [fitT])
  · rw [ku.num (by decide) (by simp) (fit wZ (by decide))]; exact nZ

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (aN aOne aZ nArr)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The modulus is odd and at least 2. -/
structure NOk (s0 : State) : Prop where
  odd : nV s0 % 2 = 1
  big : 128 ≤ nV s0
  top : 256 ^ (kK s0 - 1) ≤ nV s0

theorem NOk.of_valid {s0 : State} (h : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) : NOk s0 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, Nat.le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ 511 by decide)) h.1.1.2, h.2⟩

end VG.Proof.Rsa.PPC64LE.Recover

end

end

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: correctness

`det_ok`: from `n` (narrow) and `d e` (wide), the stages (`RdTwos.lean` to
`RdSqrt.lean`) leave in arrays 5 and 6 and in `Recover.sMask` the factors
and mask of `RecoverDet.result`, with the quotient and remainder of the second
division where its divisor is positive.

`valid_ok`: for a valid modulus, the loads, `d e`, Appendix C.2 (`det_ok`)
and the stores write the factors of `RecoverDet.result`, which is
`Spec.Rsa.recoverDet`'s (`RecoverDet.model_correct`); `rd_correct`: the code
meets `rdP`'s postcondition (`primesKeyDet`) and the calling convention.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (det sB0 sB1 sLt sExact sC1 sC2 sOk5)
open VG.Spec.Rsa (isqrt)

theorem mask_eq (c0 c1 c2 c3 c4 c5 c6 : Bool) :
    ((((((!c0 && !c1) && c2) && c3) && !c4) && !c5) && c6) = (!(c0 || c1) && c2 && (c3 && !(c4 || c5) && c6)) := by
  revert c0 c1 c2 c3 c4 c5 c6; decide

/-- The root's bit only matters where the earlier checks pass. -/
theorem mask_c6 {x l r k c c' : Bool} (h : l = true → k = true → c' = c) :
    (x && l && (r && k && c')) = (x && l && (r && k && c)) := by
  cases l <;> cases k <;> simp_all

/-- Where the model's earlier checks pass, `X = b² - 4 n` fits the square root's `2 H` words. -/
theorem x_lt {H nb wb n de q : Nat} (three : 3 ≤ n) (hn : n < 2 ^ (64 * H)) (hnb : nb = 64 * H + 64)
    (hw : wb = 2 * nb + 64) (hlt : ltOf nb wb n de = true) (hq : q = dOf nb wb n de / m1Of nb wb n de)
    (h4 : ok4Of nb wb n (bOf nb q) = true) : xOf nb wb n (bOf nb q) < 2 ^ (64 * (2 * H)) := by
  obtain p1 : 8 * 2 ^ (64 * H) ≤ 2 ^ nb := by
    rw [show 8 * 2 ^ (64 * H) = 2 ^ (64 * H + 3) by rw [Nat.pow_add]; omega_using []]
    exact Nat.pow_le_pow_right (by decide) (by omega_using [hnb])
  obtain p3 : 2 ^ nb ≤ 2 ^ wb := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  obtain p2 : 2 ^ nb * 2 ^ nb ≤ 2 ^ wb := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  obtain pM : 2 ^ (64 * H) * 2 ^ (64 * H) = 2 ^ (64 * (2 * H)) := by rw [← Nat.pow_add]; congr 1; omega_using []
  obtain rlt : rOf nb wb n de < n := Nat.mod_lt _ (by omega_using [three])
  obtain dv : dOf nb wb n de = n - rOf nb wb n de := by
    unfold dOf; rw [Nat.mod_eq_of_lt (by omega_using [hn, p1, rlt]), wsub_of_le (by omega_using [hn, p1]) (by omega_using [rlt])]
  obtain mlt : mOf nb wb n de < n := by simpa [ltOf] using hlt
  obtain m1 : m1Of nb wb n de = mOf nb wb n de + 1 := by
    unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf nb wb n de) (by omega_using [hn, p1, mlt]), Nat.mod_eq_of_lt (by omega_using [hn, p1, mlt])]
  obtain qle : q ≤ n := by rw [hq, dv, m1]; exact Nat.le_trans (Nat.div_le_self _ _) (by omega_using [])
  obtain hb : bOf nb q = q + 1 := by unfold bOf; exact Nat.mod_eq_of_lt (by omega_using [hn, p1, qle])
  rw [hb] at h4 ⊢
  obtain blt : q + 1 < 2 ^ nb := by omega_using [hn, p1, qle]
  obtain bb : (q + 1) * (q + 1) < 2 ^ wb := Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' blt blt) p2
  obtain sq : sqOf nb wb (q + 1) = (q + 1) * (q + 1) := by
    unfold sqOf; rw [prod_iter _ _ _ (by omega_using [p3, blt])]; simp only
    rw [Nat.mod_eq_of_lt blt, Nat.mod_eq_of_lt bb]
  obtain f4 : fourN wb n = 4 * n := by
    unfold fourN
    rw [Nat.mod_eq_of_lt (a := 2 * n) (by omega_using [hn, p1, p3]), Nat.mod_eq_of_lt (by omega_using [hn, p1, p3])]; omega_using []
  obtain big : ¬ ((q + 1) * (q + 1) < 4 * n) := by
    unfold ok4Of at h4; rw [sq, f4] at h4; simp at h4; omega_using [h4]
  unfold xOf; rw [sq, f4, wsub_of_le bb (by omega_using [big])]
  obtain e1 : (q + 1) * (q + 1) ≤ (n + 1) * (n + 1) := Nat.mul_self_le_mul_self (by omega_using [qle])
  obtain e2 : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega_using []
  obtain e3 : n * n < 2 ^ (64 * (2 * H)) := pM ▸ Nat.mul_self_lt_mul_self hn
  omega_using [three, hn, hq, pM, rlt, mlt, qle, blt, bb, big, e1, e2, e3]

/-- The bytes of a factor. -/
abbrev outB (b : Bool) (v k : Nat) : List Byte := if b then Spec.Rsa.i2osp v k else List.replicate k 0

theorem nV_lt256 (s0 : State) : nV s0 < 256 ^ kK s0 := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0))
  rwa [VG.Proof.Bignum.bytesAt_length] at this

/-- A valid modulus's top word is not zero. -/
theorem n_top {s0 : State} (top : 256 ^ (kK s0 - 1) ≤ nV s0) : 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) ≤ nV s0 := by
  refine Nat.le_trans ?_ top
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega_using [])

/-- `n` fits its `⌈k / 8⌉` words. -/
theorem n_lt (s0 : State) : nV s0 < 2 ^ (64 * ((kK s0 + 7) / 8)) := by
  refine Nat.lt_of_lt_of_le (nV_lt256 s0) ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega_using [])

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw] {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

/-- Appendix C.2 up to the GCD, the inverse's caller: the state kept. -/
theorem det_gcd_ok (h : DS s0 true A [(true, 0), (true, 3), (false, 32)] V [] s) (z : A true 0 = 0)
    (three : 3 ≤ A false 32) :
    WP isa (seqs [VG.Impl.Rsa.PPC64LE.RecoverDet.deMinus, VG.Impl.Rsa.PPC64LE.RecoverDet.twos,
      VG.Impl.Rsa.PPC64LE.RecoverDet.gcd]) s fun t =>
      ∃ A' V', DS s0 false A' [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)] V' [sB1, sB0] t := by
  have w1 := h.base.sz.w1
  obtain nlo := h.lt (b' := false) (j := 32) (by decide)
  rw [vw_false] at nlo
  simp only [seqs]
  -- `d e - 1`, and the halvings.
  refine WP.seq (WP.mono (deMinus_ok h z) fun s1 ⟨A1, V1, h1, a15, a10, a9, a32, vb0, vb1⟩ => ?_)
  rw [vw_true] at a10 vb1
  refine WP.seq (WP.mono (twos_ok h1 a15 (by rw [a32]; omega_using [three])) fun s2 ⟨A2, V2, h2, e2, b15, b8, b9, b32, b42, wb0, wb1⟩ => ?_)
  rw [a10, a32, vw_true] at e2
  rw [a9] at b9
  rw [a32] at b32
  have tw : twosOut (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) = (A2 true 14, A2 true 13, A2 true 12) :=
    e2.symm
  -- `u` odd, and both below `2^(32 w)`.
  obtain nm1 : wsub (32 * ww (kK s0)) (A false 32) 1 = A false 32 - 1 := wsub_of_le nlo (by omega_using [three])
  obtain xlt : deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)) < 2 ^ (32 * wW (kK s0)) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide)
      (show 32 * ww (kK s0) ≤ 32 * (2 * ww (kK s0) + 2) by omega_using []))
  obtain uodd : A2 true 14 % 2 = 1 := by
    obtain p := (twos_proj (32 * wW (kK s0)) (32 * ww (kK s0)) (A false 32 - 1)
      (deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0))) (deX (32 * wW (kK s0)) (A true 3))
      (deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)))).1
    obtain i := (twos_iter (b := 32 * wW (kK s0)) (N := A false 32 - 1) (k := 32 * ww (kK s0)) (by omega_using [three])
      (by omega_using [nlo]) xlt).1
    rw [nm1] at e2
    have := congrArg Prod.fst e2
    simp only at this
    rw [this, p]; exact i
  obtain bnd := twos_le (32 * wW (kK s0)) (32 * ww (kK s0)) (wsub (32 * ww (kK s0)) (A false 32) 1,
    deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)), deX (32 * wW (kK s0)) (A true 3))
  rw [← e2] at bnd
  simp only at bnd
  obtain ulo : A2 true 14 < 2 ^ (32 * ww (kK s0)) := by omega_using [nlo, nm1, bnd]
  obtain xlo : A2 true 13 < 2 ^ (32 * ww (kK s0)) :=
    Nat.lt_of_le_of_lt bnd.2 (Nat.mod_lt _ (Nat.two_pow_pos _))
  -- The GCD and the product.
  exact WP.mono (gcd_ok h2 uodd ulo xlo b8 b42) fun s3 ⟨A3, V3, h3, _⟩ => ⟨A3, V3, h3⟩

/-- Appendix C.2, from `n` (narrow array 32) and `d e` (wide array 3). -/
theorem det_ok (h : DS s0 true A [(true, 0), (true, 3), (false, 32)] V [] s) (z : A true 0 = 0)
    (three : 3 ≤ A false 32) (top : 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) ≤ A false 32)
    (nlt : A false 32 < 2 ^ (64 * ((kK s0 + 7) / 8))) :
    WP isa det s fun t => ∃ A' V' q rem,
      DS s0 false A' [(false, 5), (false, 6)] V' [VG.Impl.Rsa.PPC64LE.Recover.sMask] t ∧
      (ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) = true →
        0 < m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) →
        q = dOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) /
            m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) ∧
          rem = dOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) %
            m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3)) ∧
      ((okDE (32 * wW (kK s0)) (A true 3) && ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) &&
        (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).1) = true →
        A' false 5 = (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).2.1 ∧
        A' false 6 = (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).2.2) ∧
      V' VG.Impl.Rsa.PPC64LE.Recover.sMask = b2n (okDE (32 * wW (kK s0)) (A true 3) &&
        ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) &&
        (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).1) := by
  have w1 := h.base.sz.w1
  obtain nlo := h.lt (b' := false) (j := 32) (by decide)
  rw [vw_false] at nlo
  unfold det
  simp only [seqs]
  -- `d e - 1`, and the halvings.
  refine WP.seq (WP.mono (deMinus_ok h z) fun s1 ⟨A1, V1, h1, a15, a10, a9, a32, vb0, vb1⟩ => ?_)
  rw [vw_true] at a10 vb1
  refine WP.seq (WP.mono (twos_ok h1 a15 (by rw [a32]; omega_using [three])) fun s2 ⟨A2, V2, h2, e2, b15, b8, b9, b32, b42, wb0, wb1⟩ => ?_)
  rw [a10, a32, vw_true] at e2
  rw [a9] at b9
  rw [a32] at b32
  have tw : twosOut (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) = (A2 true 14, A2 true 13, A2 true 12) :=
    e2.symm
  -- `u` odd, and both below `2^(32 w)`.
  obtain nm1 : wsub (32 * ww (kK s0)) (A false 32) 1 = A false 32 - 1 := wsub_of_le nlo (by omega_using [three])
  obtain xlt : deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)) < 2 ^ (32 * wW (kK s0)) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide)
      (show 32 * ww (kK s0) ≤ 32 * (2 * ww (kK s0) + 2) by omega_using []))
  obtain uodd : A2 true 14 % 2 = 1 := by
    obtain p := (twos_proj (32 * wW (kK s0)) (32 * ww (kK s0)) (A false 32 - 1)
      (deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0))) (deX (32 * wW (kK s0)) (A true 3))
      (deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)))).1
    obtain i := (twos_iter (b := 32 * wW (kK s0)) (N := A false 32 - 1) (k := 32 * ww (kK s0)) (by omega_using [three])
      (by omega_using [nlo]) xlt).1
    rw [nm1] at e2
    have := congrArg Prod.fst e2
    simp only at this
    rw [this, p]; exact i
  obtain bnd := twos_le (32 * wW (kK s0)) (32 * ww (kK s0)) (wsub (32 * ww (kK s0)) (A false 32) 1,
    deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)), deX (32 * wW (kK s0)) (A true 3))
  rw [← e2] at bnd
  simp only at bnd
  obtain ulo : A2 true 14 < 2 ^ (32 * ww (kK s0)) := by omega_using [nlo, nm1, bnd]
  obtain xlo : A2 true 13 < 2 ^ (32 * ww (kK s0)) :=
    Nat.lt_of_le_of_lt bnd.2 (Nat.mod_lt _ (Nat.two_pow_pos _))
  -- The GCD and the product.
  refine WP.seq (WP.mono (gcd_ok h2 uodd ulo xlo b8 b42) fun s3 ⟨A3, V3, h3, g8, g12, g15, g9, g32, gb0, gb1⟩ =>
    ?_)
  refine WP.seq (WP.mono (aProduct_ok h3 (by rw [g15, b15])) fun s4 ⟨A4, V4, h4, p17, p15, p9, p32, pb0, pb1⟩ =>
    ?_)
  rw [g8, g12, vw_true] at p17
  obtain ha : A4 true 17 = aOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) := by
    rw [p17, aOf, tw]
  -- `m`, `r`, and the second division.
  obtain n4 : A4 false 32 = A false 32 := by rw [p32, g32, b32]
  refine WP.seq (WP.mono (divA_ok h4 p15 (by rw [n4]; exact top) (by rw [n4]; exact nlt))
    fun s5 ⟨A5, V5, h5, m5, r5, n5, z5, o5, nn5, vlt, db0, db1⟩ => ?_)
  rw [n4, ha] at m5 r5 vlt
  rw [n4] at n5 nn5
  refine WP.seq (WP.mono (divB_ok h5 z5 (by rw [nn5]; exact nlt)) fun s6 ⟨Q, R, A6, V6, h6, qr, q6, n6, z6, nW6, zz6, o6, nn6, vex, vlt6, eb0,
    eb1⟩ => ?_)
  rw [m5, r5, nn5] at qr
  -- `b`, `b²` and `b² - 4 n`.
  refine WP.seq (WP.mono (square_ok h6 zz6 n6) fun s7 ⟨A7, V7, h7, b7, sq7, z7, o7, nW7, v7⟩ => ?_)
  refine WP.seq (WP.mono (minus4n_ok h7) fun s8 ⟨A8, V8, h8, x8, z8, b8', vc1, vc2, v8⟩ => ?_)
  rw [sq7, nW7, nW6, n5, q6, vw_true] at x8 vc1
  rw [sq7, nW7, nW6, n5, q6, o7, o6, o5, p9, g9, b9, vw_true] at vc2
  rw [b7, q6] at b8'
  -- The square root and the factors.
  refine WP.seq (WP.mono (sqrt_ok h8 (by rw [z8, z7])) fun s9 ⟨A9, V9, h9, y9, b9', z9, vok, v9⟩ => ?_)
  rw [b8'] at b9'
  -- The model's names.
  obtain hnb : 32 * ww (kK s0) = 64 * ((kK s0 + 7) / 8) + 64 := by simp only [ww]; omega_using []
  obtain hwb : 32 * wW (kK s0) = 2 * (32 * ww (kK s0)) + 64 := by simp only [wW]; omega_using []
  obtain xe : A8 true 18 = xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) := by
    rw [x8]; rfl
  rw [xe] at y9 vok
  obtain hqr : ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) = true →
      Q = dOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) /
          m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) ∧
        R = dOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) %
          m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) := by
    intro hl
    obtain hm : aOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) / A false 32 < A false 32 := by
      unfold ltOf mOf at hl; exact of_decide_eq_true hl
    unfold m1Of dOf mOf rOf
    exact qr (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hm)
      (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by omega_using [three])))
  -- Where the earlier checks pass, the root by words is the model's.
  obtain link : ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) = true →
      ok4Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) = true →
      xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) %
          2 ^ (64 * (2 * ((kK s0 + 7) / 8))) =
        xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) ∧
      (rootOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q)).2.2 =
          isqrt (xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q)) ∧
      ((rootOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q)).2.1 = 0 ↔
        isqrt (xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q)) *
          isqrt (xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q)) =
          xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q)) := by
    intro hl h4
    obtain hq := (hqr hl).1
    obtain rb := root_bridge (de := A true 3) (by omega_using [three])
      (by rw [hnb, Nat.pow_add]; have := Nat.two_pow_pos (64 * ((kK s0 + 7) / 8)); omega_using [nlt]) (by omega_using [hwb])
      (by omega_using []) hl hq h4
    exact ⟨Nat.mod_eq_of_lt (x_lt (by omega_using [three]) nlt hnb hwb hl hq h4), rb.1, rb.2.1⟩
  refine WP.mono (factors_ok h9 z9 (c0 := decide (A true 3 < 1)) (c1 := decide (deX (32 * wW (kK s0)) (A true 3) < 1))
    (c2 := ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3))
    (c3 := decide (R = 0))
    (c4 := decide (sqOf (32 * ww (kK s0)) (32 * wW (kK s0)) (bOf (32 * ww (kK s0)) Q) <
      fourN (32 * wW (kK s0)) (A false 32)))
    (c5 := decide (xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) < 1))
    (c6 := decide (isqrt (xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) %
          2 ^ (64 * (2 * ((kK s0 + 7) / 8)))) *
        isqrt (xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) %
          2 ^ (64 * (2 * ((kK s0 + 7) / 8)))) =
        xOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) %
          2 ^ (64 * (2 * ((kK s0 + 7) / 8)))))
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), eb0, db0, pb0, gb0, wb0, vb0])
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), eb1, db1, pb1, gb1, wb1, vb1])
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), vlt6, vlt]; rfl)
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), vex])
    (by rw [v9 _ (by decide), vc1]; rfl)
    (by rw [v9 _ (by decide), vc2]; rfl)
    vok) fun t ⟨A10, V10, h10, p10, q10, m10⟩ => ⟨A10, V10, Q, R, h10, fun hl _ => hqr hl, ?_, ?_⟩
  · intro hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨_, hl⟩, hs⟩ := hm
    obtain h4 : ok4Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (bOf (32 * ww (kK s0)) Q) = true := by
      unfold stage2 at hs; simp only [Bool.and_eq_true] at hs; exact hs.1.2
    obtain ⟨xm, ry, _⟩ := link hl h4
    rw [p10, q10, b9', y9, xm, ← ry]
    exact ⟨rfl, rfl⟩
  · rw [m10, mask_eq, mask_c6 (c := decide ((rootOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32)
      (bOf (32 * ww (kK s0)) Q)).2.1 = 0)) fun hl h4 => by
        obtain ⟨xm, _, rz⟩ := link hl h4
        rw [xm]; exact decide_eq_decide.mpr rz.symm]
    rfl

end



open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet
open VG.Spec.Rsa (recoverDet primesKeyDet)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays after `d e`: zero and `d e` (wide), `n` (narrow). -/
def A0 (s0 : State) : Bool → Nat → Nat :=
  upd (upd (upd (fun _ _ => 0) true 0 0) true 3 (dV s0 * eV s0)) false 32 (nV s0)

/-- After the loads and `d e`. -/
theorem prodD_ok {s0 t : State} (l : LdD s0 t) :
    WP isa VG.Impl.Rsa.PPC64LE.Recover.prod t fun u =>
      DS s0 true (A0 s0) [(true, 0), (true, 3), (false, 32)] (fun _ => 0) [] u := by
  have z := l.base.sz
  have h44 : sv (kK s0) = arr (ww (kK s0)) 44 := z.svw
  have := z.svZ; have := z.nw
  refine WP.mono (prod_ok l) fun u ⟨w2, kk, vM, vZ, k2⟩ => ?_
  obtain fits : arr (vw s0 true) 22 ≤ rvZ s0 := by
    rw [vw_wide, arr_wide]; show arr (ww (kK s0)) 44 ≤ _; omega_arith
  refine ⟨l.base.of_keep (w := wW (kK s0)) kk (fun j hj => ?_) (fun d hd => ?_) k2, ⟨w2.scr, fits, w2.wpos, w2.wle,
    w2.r29, w2.r30, w2.r31⟩, (k2.gpr _ (by decide)).trans l.r21, (k2.gpr _ (by decide)).trans l.r23,
    (k2.gpr _ (by decide)).trans l.r25, fun e he => ?_, by decide, by simp, by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (show VG.Impl.Rsa.PPC64LE.Recover.wM < 16 by decide)) z.svW
  · simp at hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [A0, vw_true]
      show num u.mem _ _ VG.Impl.Rsa.PPC64LE.Recover.wZ = _; rw [vZ]; rd_simp
    · simp only [A0, vw_true]
      show num u.mem _ _ VG.Impl.Rsa.PPC64LE.Recover.wM = _; rw [vM]; rd_simp
    · simp only [A0, vw_false]
      obtain hA9 : arr (wW (kK s0)) 9 = arr (ww (kK s0)) 18 := arrW9 _
      obtain e44 := VG.Proof.Rsa.KeyWorkspace.arr_end (w := ww (kK s0)) (show 32 < 44 by decide)
      simp only [num]
      rw [keepW_far kk (by decide) (by decide)
        (by rw [hA9]; exact VG.Proof.Rsa.KeyWorkspace.arr_mono (by decide)) (by simp only [S] at e44; omega)]
      rd_simp
      exact l.vN

/-- The bounds `RecoverDet.model_correct` needs, from the contract and the modulus. -/
theorem bounds {s0 : State} (h : rdP.pre s0) :
    8 * (nV s0 + 2) ≤ 2 ^ (32 * ww (kK s0)) ∧ dV s0 * eV s0 < 2 ^ (32 * ww (kK s0)) ∧
      2 * (32 * ww (kK s0)) ≤ 32 * wW (kK s0) ∧ (32 * wW (kK s0)) % 2 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, -, e8, -, d2,
    -⟩ := id h
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  obtain h8 : 8 * kK s0 + 64 ≤ 32 * ww (kK s0) := by simp only [ww]; omega_using []
  obtain bD : dV s0 < 2 ^ (8 * kK s0) := by
    have := os2ip_lt8 (dB s0); simp only [dB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [d2, hkK]))
  obtain bE : eV s0 < 2 ^ 64 := by
    have := os2ip_lt8 (eB s0); simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [e8]))
  obtain bN : nV s0 < 2 ^ (8 * kK s0) := by
    have := nV_lt256 s0; rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  obtain p4 : 2 ^ (8 * kK s0 + 4) ≤ 2 ^ (32 * ww (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega_using [h8])
  obtain p64 : 2 ^ (8 * kK s0 + 64) ≤ 2 ^ (32 * ww (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega_using [h8])
  have one : 1 ≤ 2 ^ (8 * kK s0) := Nat.one_le_two_pow
  refine ⟨?_, ?_, by simp only [wW]; omega_using [], by simp only [wW]; omega_using []⟩
  · rw [Nat.pow_add] at p4; omega_using [bN, p4]
  · calc dV s0 * eV s0 < 2 ^ (8 * kK s0) * 2 ^ 64 := Nat.mul_lt_mul'' bD bE
      _ = 2 ^ (8 * kK s0 + 64) := (Nat.pow_add _ _ _).symm
      _ ≤ _ := p64

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw]

/-- For a valid modulus: Appendix C.2's factors, or zeros, written, and the mask returned. -/
theorem valid_ok {s0 t : State} (hd : rdP.pre s0) (e : REnt s0 t)
    (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.valid t fun u => RFin s0 u ∧ ∃ b P Q,
      u.gpr .r3 = BitVec.ofNat 64 (b2n b) ∧
      Spec.Rsa.bytesAt u.mem (s0.gpr .r3) (kK s0) = outB b P (kK s0) ∧
      Spec.Rsa.bytesAt u.mem (s0.gpr .r5) (kK s0) = outB b Q (kK s0) ∧
      recoverDet (nV s0) (eV s0) (dV s0) = (if b then some (P, Q) else none) := by
  obtain hn := NOk.of_valid hmv
  obtain ⟨b8, bde, bw, bwe⟩ := bounds hd
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.valid
  simp only [seqs]
  refine WP.seq (WP.mono (loads_ok e) fun t1 ⟨l1, _⟩ => ?_)
  refine WP.seq (WP.mono (prodD_ok l1) fun t2 h2 => ?_)
  refine WP.seq (WP.mono (det_ok h2 (by simp only [A0]; rd_simp) (by simp only [A0]; rd_simp; have := hn.big; omega_using [this])
      (by simp only [A0]; rd_simp; exact n_top hn.top) (by simp only [A0]; rd_simp; exact n_lt s0))
    fun t3 ⟨A3, V3, q, rem, h3, hdiv, pf, msk⟩ => ?_)
  obtain a3 : A0 s0 true 3 = dV s0 * eV s0 := by simp only [A0]; rd_simp
  obtain a32 : A0 s0 false 32 = nV s0 := by simp only [A0]; rd_simp
  simp only [a3, a32] at hdiv pf msk
  obtain mc0 := model_correct_lt (nb := 32 * ww (kK s0)) (wb := 32 * wW (kK s0)) (q := q) (rem := rem) hn.odd
    (by have := hn.big; omega_using [this]) b8 bde bw bwe hdiv
  unfold result at mc0
  generalize (okDE (32 * wW (kK s0)) (dV s0 * eV s0) && ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (nV s0)
    (dV s0 * eV s0) && (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (nV s0) q rem).1) = b at msk mc0 pf
  obtain mc : (if b then some (A3 false 5, A3 false 6) else none) = recoverDet (nV s0) (eV s0) (dV s0) := by
    cases b
    · exact mc0
    · obtain ⟨e5, e6⟩ := pf rfl; rw [e5, e6]; exact mc0
  obtain sm : slot t3.mem (rvB s0) VG.Impl.Rsa.PPC64LE.Recover.sMask = b2n b := by
    rw [h3.sl _ (by decide)]; exact msk
  have w3 : Ws t3 (rvB s0) (rvZ s0) (ww (kK s0)) VG.Impl.Rsa.PPC64LE.Recover.nArr := h3.ws
  refine WP.mono (stores_ok (h3.base.fin h3.ws.r30) w3 h3.r21 h3.r23 h3.r25 sm) fun u ⟨fu, r3, bp, bq⟩ =>
    ⟨fu, b, A3 false 5, A3 false 6, r3, ?_, ?_, mc.symm⟩
  all_goals
    obtain hk : kK s0 ≤ 4 * ww (kK s0) := by simp only [ww]; omega_using []
    obtain e8 : (2 : Nat) ^ (8 * kK s0) = 256 ^ kK s0 := by rw [Nat.pow_mul]
    obtain nl := nV_lt256 s0
  · cases b
    · exact CrtValues.bytes_zero fun c hc => by rw [bp c hc]; rfl
    · simp only [ite_true] at mc
      obtain pq := recoverDet_mul mc.symm
      obtain v5 := h3.val (b' := false) (j := 5) (by decide)
      rw [vw_false] at v5
      obtain Q1 : 1 ≤ A3 false 6 := by
        rcases Nat.eq_zero_or_pos (A3 false 6) with h0 | h0
        · rw [h0, Nat.mul_zero] at pq; have := hn.big; omega
        · exact h0
      obtain hP : A3 false 5 ≤ nV s0 := by rw [← pq]; exact Nat.le_mul_of_pos_right _ Q1
      rw [CrtValues.bytes_of hk bp, v5, e8, Nat.mod_eq_of_lt (by omega_using [nl, hP])]; rfl
  · cases b
    · exact CrtValues.bytes_zero fun c hc => by rw [bq c hc]; rfl
    · simp only [ite_true] at mc
      obtain pq := recoverDet_mul mc.symm
      obtain v6 := h3.val (b' := false) (j := 6) (by decide)
      rw [vw_false] at v6
      obtain P1 : 1 ≤ A3 false 5 := by
        rcases Nat.eq_zero_or_pos (A3 false 5) with h0 | h0
        · rw [h0, Nat.zero_mul] at pq; have := hn.big; omega
        · exact h0
      obtain hQ : A3 false 6 ≤ nV s0 := by rw [← pq]; exact Nat.le_mul_of_pos_left _ P1
      rw [CrtValues.bytes_of hk bq, v6, e8, Nat.mod_eq_of_lt (by omega_using [nl, hQ])]; rfl

/-- The valid branch up to the GCD, the inverse's caller: the state kept. -/
theorem valid_gcd_ok {s0 t : State} (e : REnt s0 t)
    (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) :
    WP isa (seqs [VG.Impl.Rsa.PPC64LE.Recover.loads, VG.Impl.Rsa.PPC64LE.Recover.prod,
      VG.Impl.Rsa.PPC64LE.RecoverDet.deMinus, VG.Impl.Rsa.PPC64LE.RecoverDet.twos,
      VG.Impl.Rsa.PPC64LE.RecoverDet.gcd]) t fun u =>
      ∃ A V, DS s0 false A [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)] V [sB1, sB0] u := by
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (loads_ok e) fun t1 ⟨l1, _⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  obtain hn := NOk.of_valid hmv
  exact WP.mono (prodD_ok l1) fun t2 h2 => det_gcd_ok h2 (by simp only [A0]; rd_simp)
    (by simp only [A0]; rd_simp; have := hn.big; omega_using [this])

end

/-- `primesKeyDet` of the initial state's bytes. -/
theorem pkd_eq (s0 : State) : primesKeyDet (nB s0) (eB s0) (dB s0) =
    if Spec.Rsa.modulusValid (nV s0) (kK s0) then
      (recoverDet (nV s0) (eV s0) (dV s0)).map fun (p, q) => (Spec.Rsa.i2osp p (kK s0), Spec.Rsa.i2osp q (kK s0))
    else none := by
  obtain hl : (nB s0).length = kK s0 := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold primesKeyDet
  rw [hl]

/-- The postcondition from the factors' bytes and the returned flag. -/
theorem rd_post_of {s0 t : State} {b : Bool} {P Q : Nat}
    (hpk : primesKeyDet (nB s0) (eB s0) (dB s0) =
      if b then some (Spec.Rsa.i2osp P (kK s0), Spec.Rsa.i2osp Q (kK s0)) else none)
    (h3 : t.gpr .r3 = BitVec.ofNat 64 (b2n b))
    (bp : Spec.Rsa.bytesAt t.mem (s0.gpr .r3) (kK s0) = outB b P (kK s0))
    (bq : Spec.Rsa.bytesAt t.mem (s0.gpr .r5) (kK s0) = outB b Q (kK s0)) : rdP.post s0 t := by
  show Spec.Rsa.writtenAll t.mem _ _ _
  rw [hpk]
  cases b
  · refine ⟨by rw [h3]; rfl, fun o ho => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact bp
    · exact bq
  · refine ⟨by rw [h3]; rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [bp, bq]; rfl

/-- The factors not found: zeros and 0. -/
theorem rd_post_none {s0 t : State} (hpk : primesKeyDet (nB s0) (eB s0) (dB s0) = none) (h3 : t.gpr .r3 = 0)
    (vp : ∀ c < kK s0, t.mem (off (s0.gpr .r3) c) = 0) (vq : ∀ c < kK s0, t.mem (off (s0.gpr .r5) c) = 0) :
    rdP.post s0 t :=
  rd_post_of (b := false) (P := 0) (Q := 0) (by rw [hpk]; rfl) (by rw [h3]; rfl) (CrtValues.bytes_zero vp)
    (CrtValues.bytes_zero vq)

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw]

/-- The branch on `n`'s check. -/
theorem branchD_ok {s s2 : State} (hd : rdP.pre s) (b2 : RBase s s2) (a2 : RArgs s s2)
    (e2 : REnt s s2) (hv : s2.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (nV s) (kK s) = true) :
    WP isa (.ite (.zero .d .r0) VG.Impl.Rsa.PPC64LE.RecoverDet.valid VG.Impl.Rsa.PPC64LE.Recover.fail) s2
      fun t => RFin s t ∧ rdP.post s t := by
  refine WP.ite (s2.gpr .r0 == 0) (eval_zero s2 .r0) (fun hz => ?_) (fun hz => ?_)
  · have hmv : Spec.Rsa.modulusValid (nV s) (kK s) = true := hv.mp (beq_iff_eq.mp hz)
    refine WP.mono (valid_ok hd e2 hmv) fun t ⟨ft, b, P, Q, r3, bp, bq, rec⟩ => ⟨ft, rd_post_of ?_ r3 bp bq⟩
    rw [pkd_eq, ite_eq_left hmv, rec]
    cases b <;> rfl
  · have hmv : ¬ Spec.Rsa.modulusValid (nV s) (kK s) = true := fun h' => by
      rw [hv.mpr h'] at hz; exact absurd hz (by decide)
    refine WP.mono (fail_ok (b2.fin e2.r30) a2.r21 a2.r23 a2.r25) fun t ⟨ft, t3, vp, vq, _⟩ =>
      ⟨ft, rd_post_none ?_ t3 vp vq⟩
    rw [pkd_eq, ite_eq_right hmv]

/-- All registers but `r1`, `r2` and `r13`. -/
abbrev rdRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17,
  .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem rd_correct (s : State) (h : rdP.pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.PPC64LE.RecoverDet.code s tr t ∧ abiPreserved s t ∧ rdP.post s t := by
  have hv := rdP_pre h
  show WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.code s fun t => abiPreserved s t ∧ rdP.post s t
  have hw := WP.keep rdRegs (c := VG.Impl.Rsa.PPC64LE.RecoverDet.code) (s := s) (Q := fun t => t.sp = s.sp ∧
    t.lr = s.lr ∧ (∀ r ∈ preserved, r ≠ .r2 → t.gpr r = s.gpr r) ∧ rdP.post s t) ?_ (by decide +kernel)
    (by decide +kernel)
  · refine WP.mono hw fun t ⟨⟨tsp, tlr, hr, post⟩, kt⟩ => ⟨⟨fun r hr' => ?_, tsp, tlr⟩, post⟩
    by_cases e : r = .r2
    · subst e; exact kt.gpr (r := .r2) (by decide)
    · exact hr r hr' e
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.code
  refine WP.seq (WP.mono (entry_ok hv) fun s1 e1 => ?_)
  refine WP.seq (WP.mono (nCheck_ok e1.base e1.args) fun s2 ⟨⟨b2, a2, hv'⟩, m2, k2⟩ => ?_)
  have e2 : REnt s s2 := ⟨b2, a2, (k2.gpr _ (by decide)).trans e1.r29, (k2.gpr _ (by decide)).trans e1.r30,
    m2.trans e1.mem, (e1.keep.trans k2).mono⟩
  rw [show Spec.Rsa.os2ip (nB0 s) = nV s from rfl] at hv'
  refine WP.seq (WP.mono (branchD_ok h b2 a2 e2 hv') fun t ⟨ft, post⟩ => ?_)
  refine WP.mono (restore_ok ft) fun u ⟨⟨⟨u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25, u26, u27,
    u28, u29, u30, u31⟩, um⟩, ku⟩ => ⟨ku.sp.trans ft.sp, ku.lr.trans ft.lr, fun r hr hr2 => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> first | exact absurd rfl hr2 | with_reducible assumption
  · have e3 : u.gpr .r3 = t.gpr .r3 := ku.gpr _ (by decide)
    show Spec.Rsa.writtenAll u.mem _ _ _
    rw [um, e3]
    exact post

end

end VG.Proof.Rsa.PPC64LE.RecDet
