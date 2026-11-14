module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdEntry
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.BoolNat
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdMulW
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
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
