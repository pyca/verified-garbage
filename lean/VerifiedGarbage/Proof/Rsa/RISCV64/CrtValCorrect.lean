module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValD
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.CrtValuesMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: correctness

`stores_ok`: `dP` and `dQ` written under the mask and the mask's bit
returned; `valid_ok`: a valid modulus, from the set-up to the stores;
`code_correct`: the function, through `crtKey_masked`
(`Proof/Rsa/CrtValuesMath.lean`), on the registers and the stack (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs storeBytes restore)
open VG.Impl.Rsa.RISCV64.CrtValues (code stores valid arith mask nArr aDR2 aDR3 sMask checks invPart dParts)
open VG.Proof.Rsa.CrtValues (maskOf)

/-- The outputs, as the function leaves them. -/
structure Out (s0 : State) (X₁ X₂ V X R₂ R₃ : Nat) (u : State) : Prop where
  ce : CE s0 u
  dp : Spec.Rsa.bytesAt u.mem (s0.gpr .a0) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (R₂ % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0
  dq : Spec.Rsa.bytesAt u.mem (s0.gpr .a2) (qL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (R₃ % 256 ^ qL s0) (qL s0) else List.replicate (qL s0) 0
  qi : Spec.Rsa.bytesAt u.mem (s0.gpr .a4) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (X % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0
  a0 : (u.gpr .a0).toNat = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0

theorem stores_ok {s0 t : State} (h : PreC s0) {X₁ X₂ V X : Nat} {Mi : Mem} (dd : Dd s0 X₁ X₂ V Mi t)
    (hqi : Spec.Rsa.bytesAt Mi (s0.gpr .a4) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
      Spec.Rsa.i2osp (X % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0) :
    WP isa stores t (Out s0 X₁ X₂ V X (num t.mem (bOf s0) (wOf s0) aDR2) (num t.mem (bOf s0) (wOf s0) aDR3)) := by
  have ⟨w1, w2⟩ := h.w_bounds
  have hz := h.zk
  have ⟨lp, lq⟩ := lt32 h
  have hp1 := h.p1
  have hq1 := h.q1
  have hp2 := h.p2
  have hq2 := h.q2
  have pw : pL s0 ≤ 8 * wOf s0 := by
    show (stackArg s0 1).toNat ≤ 8 * (((s0.gpr .a7).toNat + 7) / 8); omega_arith
  have qw : qL s0 ≤ 8 * wOf s0 := by
    show (stackArg s0 3).toNat ≤ 8 * (((s0.gpr .a7).toNat + 7) / 8); omega_arith
  have ws := dd.ws
  have c := dd.cb
  have bit : slot t.mem (bOf s0) sMask ≤ 1 := by rw [dd.mask]; exact bit_ite
  have Z64 : zOf s0 ≤ 2 ^ 64 := by have := h.ws; simp only [zOf]; omega_arith
  have fitZ : ∀ j < nArr, arr (wOf s0) j + 8 * wOf s0 ≤ zOf s0 := fun j hj => by
    have := Nat.le_trans (arr_end hj) h.fits; simp only [S] at this; omega_arith
  -- The regions of the outputs.
  have wdp : (s0.gpr .a0).toNat + pL s0 ≤ 2 ^ 64 := by have := h.wdp; rw [h.h1] at this; exact this
  have wdq : (s0.gpr .a2).toNat + qL s0 ≤ 2 ^ 64 := by have := h.wdq; rw [h.h3] at this; exact this
  have dpw : (⟨s0.gpr .a0, pL s0⟩ : Region) ∈ s0.wr := by rw [← h.dpR_eq, h.hwr]; simp
  have dqw : (⟨s0.gpr .a2, qL s0⟩ : Region) ∈ s0.wr := by rw [← h.dqR_eq, h.hwr]; simp
  have dps : (⟨s0.gpr .a0, pL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.dpR_eq]; exact h.dps
  have dqs : (⟨s0.gpr .a2, qL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.dqR_eq]; exact h.dqs
  have qis : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.qiR_eq]; exact h.qis
  have dp_dq : (⟨s0.gpr .a0, pL s0⟩ : Region).Disjoint ⟨s0.gpr .a2, qL s0⟩ := by
    rw [← h.dpR_eq, ← h.dqR_eq]; exact h.dpdq
  have qi_dp : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint ⟨s0.gpr .a0, pL s0⟩ := by
    rw [← h.qiR_eq, ← h.dpR_eq]; exact fun a ha hb => h.dpqi a hb ha
  have qi_dq : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint ⟨s0.gpr .a2, qL s0⟩ := by
    rw [← h.qiR_eq, ← h.dqR_eq]; exact fun a ha hb => h.dqqi a hb ha
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mask_ok ws bit) fun t1 ⟨⟨m4, m1⟩, k1⟩ => ?_
  have ws1 := ws.of_keep k1
  have c1 := c.of_keep k1 m1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws1 (j := aDR2) (by decide) (by decide) c1.a2
    (by rw [c1.s4]; exact toNat_ofNat_eq _) (by decide) (by decide) (by decide) m4 hp1 pw
    (fun i hi => by rw [c1.wr]; exact bytes_in dpw (by omega_arith) i hi) (bytes_sep dps (by omega_arith)) wdp)
    fun t2 ⟨ws2, b2, o2, k2⟩ => ?_
  have c2 := c1.of_out k2 o2 dps (by omega_arith)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws2 (j := aDR3) (b := decide (slot t.mem (bOf s0) sMask ≠ 0)) (by decide) (by decide) c2.a3
    (by rw [c2.s6]; exact toNat_ofNat_eq _) (by decide) (by decide) (by decide)
    (by rw [k2.gpr (by decide)]; exact m4) hq1 qw
    (fun i hi => by rw [c2.wr]; exact bytes_in dqw (by omega_arith) i hi) (bytes_sep dqs (by omega_arith)) wdq)
    fun t3 ⟨ws3, b3, o3, k3⟩ => ?_
  have c3 := c2.of_out k3 o3 dqs (by omega_arith)
  have hz3 := ws3.hdr_le
  have nw3 := ws3.nowrap
  have hM : sMask + 8 ≤ zOf s0 := by simp only [hdr_eq, sMask] at hz3 ⊢; omega_arith
  have hb : WP isa (.block [.load .d .a0 .s11 sMask]) t3 fun u =>
      (u.gpr .a0 = word t3.mem (bOf s0) sMask ∧ u.mem = t3.mem) ∧ Keep [.a0] t3 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ws3.s11, add_ofNat_zero', ws3.scr.al8 (d := sMask) (by omega_arith) (by decide),
      ws3.scr.ld (d := sMask) (n := 8) hM, show sMask < 2048 by decide]
  refine WP.mono hb fun u ⟨⟨ua, um⟩, ku⟩ => ?_
  have W1 : ∀ {m : Mem} {d : Nat}, wordsVal m (bOf s0) d 1 = (word m (bOf s0) d).toNat := by
    intro m d; simp [wordsVal]
  have r3 : num t2.mem (bOf s0) (wOf s0) aDR3 = num t.mem (bOf s0) (wOf s0) aDR3 := by
    exact (wordsVal_of_out (d := arr (wOf s0) aDR3) (k := wOf s0) dps o2 (fitZ _ (by decide)) Z64).trans (by rw [m1])
  have sM : slot t3.mem (bOf s0) sMask = slot t.mem (bOf s0) sMask := by
    have e := wordsVal_of_out (d := sMask) (k := 1) dqs o3 (by omega_arith) Z64
    have e2 := wordsVal_of_out (d := sMask) (k := 1) dps o2 (by omega_arith) Z64
    rw [W1, W1] at e e2
    change (word t3.mem (bOf s0) sMask).toNat = (word t.mem (bOf s0) sMask).toNat
    rw [e, e2, m1]
  have keepB : ∀ {O : Addr} {L : Nat}, (⟨O, L⟩ : Region).Disjoint ⟨s0.gpr .a2, qL s0⟩ → L ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt u.mem O L = Spec.Rsa.bytesAt t2.mem O L := fun hd hL => by
    rw [um]; exact bytesAt_congr fun c hc => zeros_keep hd hL o3 hc
  refine ⟨⟨(ku.gpr (by decide)).trans c3.s11, (ku.gpr (by decide)).trans c3.ra, ku.2.1.trans c3.rd,
    ku.2.2.trans c3.wr, fun i hi => by rw [um]; exact c3.hdr i hi⟩, ?_, ?_, ?_, ?_⟩
  · rw [keepB dp_dq (by omega_arith)]
    by_cases hm : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
    · simp only [hm, ↓reduceIte]
      rw [bytes_of_store (m := t1.mem) (B := bOf s0) (w := wOf s0) (j := aDR2) pw (fun c hc => by rw [b2 c hc, dd.mask]; simp [hm]), m1]
    · simp only [hm, ↓reduceIte, Bool.false_eq_true]
      exact bytesAt_zero fun c hc => by rw [b2 c hc, dd.mask]; simp [hm]
  · rw [um]
    by_cases hm : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
    · simp only [hm, ↓reduceIte]
      rw [bytes_of_store (m := t2.mem) (B := bOf s0) (w := wOf s0) (j := aDR3) qw (fun c hc => by rw [b3 c hc, dd.mask]; simp [hm]), r3]
    · simp only [hm, ↓reduceIte, Bool.false_eq_true]
      exact bytesAt_zero fun c hc => by rw [b3 c hc, dd.mask]; simp [hm]
  · rw [keepB qi_dq (by omega_arith), ← hqi]
    refine bytesAt_congr fun c hc => ?_
    rw [zeros_keep qi_dp (by omega_arith) o2 hc, m1]
    exact dd.cb.frame _ (bytes_past qis hc (by omega_arith))
  · rw [ua]
    change slot t3.mem (bOf s0) sMask = _
    rw [sM, dd.mask]

/-- The outputs of a valid modulus, and what the values in them are. -/
def VP (s0 u : State) : Prop :=
  ∃ X₁ X₂ V X R₂ R₃, Out s0 X₁ X₂ V X R₂ R₃ u ∧ (0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0) ∧
    IC s0 V X ∧ (0 < 2 * (Pv s0 / 2) → R₂ = Dv s0 % (2 * (Pv s0 / 2))) ∧
    (0 < 2 * (Qv s0 / 2) → R₃ = Dv s0 % (2 * (Qv s0 / 2)))

theorem valid_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) : WP isa valid s (VP s0) := by
  unfold valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h c) fun t1 ⟨c1, w1, z1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h c1 w1 z1) fun t2 l2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  unfold arith
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (checks_ok h l2) fun t3 ⟨X₁, X₂, ck⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (invPart_ok h ck) fun t4 ⟨V, X, iv⟩ => ?_
  refine WP.mono (dParts_ok h iv) fun t5 dd => ?_
  exact WP.mono (stores_ok h dd iv.qi) fun u o => ⟨X₁, X₂, V, X, _, _, o, iv.x, iv.ic, dd.r2, dd.r3⟩

theorem bytesAt_length (m : Mem) (p : Addr) (L : Nat) : (Spec.Rsa.bytesAt m p L).length = L := by
  simp [Spec.Rsa.bytesAt]

theorem pow256 (L : Nat) : (256 : Nat) ^ L = 2 ^ (8 * L) := by
  rw [Nat.pow_mul]

theorem post_valid {s0 u v : State} (h : PreC s0)
    (hv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) (vp : VP s0 u) (hm : v.mem = u.mem)
    (ha : v.gpr .a0 = u.gpr .a0) : fnPost s0 v := by
  obtain ⟨X₁, X₂, V, X, R₂, R₃, o, hx, ic, r2, r3⟩ := vp
  have e : Mv s0 = 2 * (Pv s0 / 2) + 1 := by simp only [Mv]; omega_arith
  have h2 := ic.vx
  rw [e] at h2
  have K := VG.Proof.Rsa.CrtValues.crtKey_masked (nb := nB s0) (pb := pB s0) (qb := qB s0) (db := dB s0)
    (by rw [bytesAt_length]; exact hv) (by rw [bytesAt_length, bytesAt_length]; exact h.p2)
    (by rw [bytesAt_length, bytesAt_length]; exact h.q2) hx h2 r2 r3
  simp only [bytesAt_length, ← pow256] at K
  unfold fnPost
  rw [K]
  by_cases hk : maskOf (Pv s0) (Qv s0) X₁ X₂ V = true
  · simp only [hk, ↓reduceIte, Option.map_some, Spec.Rsa.writtenAll, List.map_cons, List.map_nil, hm]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]
      simp [hk]
    · rw [o.dp, o.dq, o.qi]
      simp [hk]
  · simp only [hk, ↓reduceIte, Option.map_none, Spec.Rsa.writtenAll, hm, Bool.false_eq_true]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]
      simp [hk]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [o.dp, o.dq, o.qi]
      simp [hk]

theorem post_fail {s0 u v : State} (hv : ¬ Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (hw : Spec.Rsa.writtenAll u.mem (outs s0) ((u.gpr .a0).setWidth 32) none) (hm : v.mem = u.mem)
    (ha : v.gpr .a0 = u.gpr .a0) : fnPost s0 v := by
  unfold fnPost
  have e : Spec.Rsa.crtKey (nB s0) (pB s0) (qB s0) (dB s0) = none := by
    unfold Spec.Rsa.crtKey
    simp only [bytesAt_length]
    rw [ite_eq_right_iff.mpr fun hc => absurd hc.1 hv]
  rw [e, hm, ha]
  exact hw

theorem code_correct (s : State) (hpre : (Spec.Rsa.crtValuesContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := preC_of hpre
  refine WP.mono (WP.rdwr (Q := fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
    fnPost s t) ?_) fun t ⟨⟨hp, hra, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  unfold code
  rw [WP.seq_iff]
  refine WP.mono (entry_ok h) fun e c => ?_
  rw [WP.seq_iff]
  refine WP.mono (nCheck_ok h c) fun t ⟨t0, tm, kt⟩ => ?_
  have ct := c.of_keep kt tm
  rw [WP.seq_iff]
  refine WP.ite _ (Steps.eval_zero t .s0) (fun hz => ?_) (fun hz => ?_)
  · have hz' : t.gpr .s0 = 0 := by simpa using hz
    have hv := t0.mp hz'
    refine WP.mono (valid_ok h ct) fun u vp => ?_
    have o := vp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
    exact WP.mono (restore_ok' h o.ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_valid h hv vp vm va⟩
  · have hz' : t.gpr .s0 ≠ 0 := by simpa using hz
    have hv : ¬ Spec.Rsa.modulusValid (Nv s) (kOf s) = true := fun e => hz' (t0.mpr e)
    refine WP.mono (fail_ok h ct) fun u ⟨ce, hw⟩ => ?_
    exact WP.mono (restore_ok' h ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_fail hv hw vm va⟩

end VG.Proof.Rsa.RISCV64.CrtValues
