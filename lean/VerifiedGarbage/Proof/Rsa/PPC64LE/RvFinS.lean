module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFail
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFrame
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots

/-!
# `vg_rsa_recover_primes` on PPC64LE: the factors written out

`outR_ok`: one factor, masked by `ok`; `stores_ok`: both, and the mask
returned.
-/

@[expose] public section

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
