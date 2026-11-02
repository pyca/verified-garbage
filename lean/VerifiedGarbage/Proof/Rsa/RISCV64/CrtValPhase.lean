module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValInv
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: the inverse's phase

`invPart_ok`: from the checks of `p q = n` (`Ck`), the inverse modulo `p | 1`
in the working space of the primes' words, the mask of every check in
`sMask`, `qInv` written under it, and the working space of `w` words back,
its arrays from 16 on as they were (`Iv`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs inverse eqS storeBytes andS sOdd sB sC)
open VG.Impl.Rsa.RISCV64.CrtValues (narrow widen invSetup invPart nInv nArr aOne aP aQ aD aDD sE3 sPodd sE1
  sE2 sMask mask)
open VG.Proof.Rsa.CrtValues (maskOf)

/-- After the inverse's phase. -/
structure Iv (s0 : State) (X₁ X₂ V X : Nat) (t : State) : Prop where
  cb : CB s0 t.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  p : num t.mem (bOf s0) (wOf s0) aP = Pv s0
  q : num t.mem (bOf s0) (wOf s0) aQ = Qv s0
  d : num t.mem (bOf s0) (wOf s0) aD = Dv s0
  ddz : word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0
  x : 0 < Pv s0 → X₁ = Nv s0 / Pv s0 ∧ X₂ = Nv s0 % Pv s0
  ic : IC s0 V X
  mask : slot t.mem (bOf s0) sMask = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0
  qi : Spec.Rsa.bytesAt t.mem (s0.gpr .a4) (pL s0) = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then
    Spec.Rsa.i2osp (X % 256 ^ pL s0) (pL s0) else List.replicate (pL s0) 0

theorem mask_prod (P Q X₁ X₂ V : Nat) :
    P % 2 * (if X₁ = Q then 1 else 0) * (if X₂ = 0 then 1 else 0) * (if V = 1 then 1 else 0) =
      if maskOf P Q X₁ X₂ V then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one P with e | e <;>
    by_cases a : X₁ = Q <;> by_cases b : X₂ = 0 <;> by_cases c : V = 1 <;> simp [maskOf, e, a, b, c]

/-- The slots that the inverse's phase writes, in the narrowed working space. -/
abbrev phaseDs : List Nat := [sOdd, sB, sC, sE3, sMask]

theorem invPart_ok {s0 s : State} (h : PreC s0) {X₁ X₂ : Nat} (ck : Ck s0 X₁ X₂ s) :
    WP isa invPart s fun t => ∃ V X, Iv s0 X₁ X₂ V X t := by
  have ⟨b1, b2, b3, b4⟩ := h.wP_bounds
  have ⟨w1, w2⟩ := h.w_bounds
  have hz := h.zk
  have hp1 := h.p1
  have ⟨lp, lq⟩ := lt32 h
  have c := ck.cb
  have fitW : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ck.ws.fit64 hj
  unfold invPart
  rw [wp_seqs_append (by simp) (by simp), wp_seqs_append (by simp) (by unfold invSetup; simp)]
  -- The narrowed working space.
  refine WP.mono (narrow_ok h c ck.ws.s9) fun t1 ⟨⟨u0, u9, u10, u7, um⟩, k1⟩ => ?_
  have c1 := c.of_keep k1 um
  have ws1 : Ws t1 (bOf s0) (zOf s0) (wP s0) nInv :=
    ⟨Scr.of_mem (by rw [c1.wr]; exact h.sR_wr) h.ws h.al,
      Nat.le_trans (arr_wide b2 (by decide : nInv ≤ nArr)) h.fits,
      b1, by omega_arith, u9, u10, c1.s11⟩
  refine WP.mono (invSetup_ok h c1 ws1) fun t2 ⟨c2, ws2, f2, is2, k2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.seq_iff.mp (invCore_ok h c2 ws2 is2 (by rw [k2.gpr (by decide), u7])))
    fun t3 h3 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono h3 fun t4 ⟨c4, ws4, f4, ic4, e4, k4⟩ => ?_
  -- The checks' slots, kept.
  have sl : ∀ e ∈ [sPodd, sE1, sE2], slot t4.mem (bOf s0) e = slot s.mem (bOf s0) e := by
    intro e he
    have h8 : e + 8 ≤ Keys.hdr := by revert e; decide
    rw [f4.slot h8 (by revert e; decide), f2.slot h8 (by simp), um]
  have sp4 := sl sPodd (by simp)
  have se1 := sl sE1 (by simp)
  have se2 := sl sE2 (by simp)
  rw [ck.podd] at sp4
  rw [ck.e1] at se1
  rw [ck.e2] at se2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (maskBlk_ok ws4 (by rw [sp4]; omega_arith) (by rw [se1]; exact bit_ite)
    (by rw [se2]; exact bit_ite) (by rw [e4]; exact bit_ite)) fun t5 ⟨ws5, f5, v5, m5, k5⟩ => ?_
  rw [sp4, se1, se2, e4, mask_prod] at v5
  have c5 := c4.of_frame f5 (by simp) (by decide) (by simp only [hdr_eq, zOf] at hz ⊢; omega_arith) k5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have wqi : (s0.gpr .a4).toNat + pL s0 ≤ 2 ^ 64 := by have := h.wqi; rw [h.h5] at this; exact this
  have qiw : (⟨s0.gpr .a4, pL s0⟩ : Region) ∈ s0.wr := by rw [← h.qiR_eq, h.hwr]; simp
  have qis : (⟨s0.gpr .a4, pL s0⟩ : Region).Disjoint (sR s0) := by rw [← h.qiR_eq]; exact h.qis
  refine WP.mono (storeBytes_ok ws5 (j := 3) (by decide) (by decide) c5.a6
    (by rw [c5.s4]; exact toNat_ofNat_eq _) (by decide) (by decide) (by decide) m5 hp1 b3
    (fun i hi => by rw [c5.wr]; exact bytes_in qiw (by omega_arith) i hi) (bytes_sep qis (by omega_arith)) wqi)
    fun t6 ⟨ws6, by6, o6, k6⟩ => ?_
  have c6 := c5.of_out k6 o6 qis (by omega_arith)
  have s06 : t6.gpr .s0 = BitVec.ofNat 64 (wOf s0) := by
    rw [k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k2.gpr (by decide), u0]
  refine WP.mono (widen_ok s06) fun t ⟨⟨t9, t10, m7⟩, k7⟩ => ?_
  have c7 := c6.of_keep k7 m7
  rw [← m7] at c7
  -- Memory past the narrowed working space, and the slot `sMask`.
  have Fw : Keys.Frame (bOf s0) (wP s0) (List.range nInv) phaseDs s.mem t5.mem := by
    rw [← um]
    exact (f2.mono (by simp) (by simp)).trans ((f4.mono (by simp) (by decide)).trans (f5.mono (by simp) (by decide)))
  have Z64 : zOf s0 ≤ 2 ^ 64 := by have := h.ws; simp only [zOf]; omega_arith
  have past : ∀ {d k : Nat}, arr (wP s0) nInv ≤ d → d + 8 * k ≤ zOf s0 →
      wordsVal t.mem (bOf s0) d k = wordsVal s.mem (bOf s0) d k := fun hd hk => by
    rw [m7, wordsVal_of_out qis o6 hk Z64, wide_at Fw (by decide) hd (by omega_arith)]
  have nW : ∀ j, nInv ≤ j → j < nArr → num t.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j :=
    fun j hj hj' => past (arr_wide b2 hj) (by have := Nat.le_trans (arr_end hj') h.fits; simp only [S] at this; omega_arith)
  have W1 : ∀ {m : Mem} {d : Nat}, wordsVal m (bOf s0) d 1 = (word m (bOf s0) d).toNat := by
    intro m d; simp [wordsVal]
  refine ⟨num t4.mem (bOf s0) (wP s0) 1, num t4.mem (bOf s0) (wP s0) 3, c7,
    ⟨Scr.of_mem (by rw [c7.wr]; exact h.sR_wr) h.ws h.al, h.fits, by omega_arith, by omega_arith, t9, t10, c7.s11⟩,
    by rw [nW aP (by decide) (by decide), ck.p], by rw [nW aQ (by decide) (by decide), ck.q],
    by rw [nW aD (by decide) (by decide), ck.d], ?_, ck.x, ic4, ?_, ?_⟩
  · have e := past (d := arr (wOf s0) aDD + 8 * wOf s0) (k := 1)
      (Nat.le_trans (arr_wide b2 (by decide)) (Nat.le_add_right _ _))
      (by have := Nat.le_trans (arr_end (by decide : aDD < nArr)) h.fits; simp only [S] at this; omega_arith)
    rw [W1, W1] at e
    rw [BitVec.eq_of_toNat_eq e]; exact ck.ddz
  · have e : wordsVal t.mem (bOf s0) sMask 1 = wordsVal t5.mem (bOf s0) sMask 1 := by
      rw [m7, wordsVal_of_out qis o6 (by simp only [zOf, sMask] at hz ⊢; omega_arith) Z64]
    rw [W1, W1] at e
    change (word t.mem (bOf s0) sMask).toNat = _
    rw [e]; exact v5
  · rw [m7]
    by_cases hm : maskOf (Pv s0) (Qv s0) X₁ X₂ (num t4.mem (bOf s0) (wP s0) 1) = true
    · simp only [hm, ↓reduceIte] at v5 ⊢
      have n3 : num t5.mem (bOf s0) (wP s0) 3 = num t4.mem (bOf s0) (wP s0) 3 :=
        f5.num (j := 3) (by simp) (by decide) (ws4.fit64 (by decide))
      rw [bytes_of_store b3 (fun c hc => by rw [by6 c hc, v5]; rfl), n3]
    · simp only [hm, ↓reduceIte, Bool.false_eq_true] at v5 ⊢
      exact bytesAt_zero fun c hc => by rw [by6 c hc, v5]; rfl

end VG.Proof.Rsa.RISCV64.CrtValues
