module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers
public import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvHalfBit
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverHalving
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: `m = 2^t r`

`halfBody_ok`: a halving step, `halveStep` on `([wR], [sTc])`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (halfBody halfBit halving halfInit sBit sTc wR wU wH wM nArr aN aOne aZ)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The invariant of the halvings, from `s1`. -/
structure HInv (B : Addr) (Z v : Nat) (s1 : State) (m i : Nat) (u : State) : Prop where
  ws : Ws u B Z v 16
  keep : KeyWorkspace.Keep B v [wR, wU, wH] [sBit, sTc] s1.mem u.mem
  vR : num u.mem B v wR = (halveStep^[i] (m, 0)).1
  vT : slot u.mem B sTc = (halveStep^[i] (m, 0)).2
  regs : Keep (.r27 :: opRegs) s1 u

theorem halfBody_ok {B : Addr} {Z v : Nat} {s1 : State} {m i : Nat} (hi : i < 2 ^ 31) {u : State}
    (h : HInv B Z v s1 m i u) :
    WP isa halfBody u fun u' => HInv B Z v s1 m (i + 1) u' ∧ u'.gpr .r27 = u.gpr .r27 - BitVec.ofNat 64 1 := by
  have ws := h.ws
  have tb : (halveStep^[i] (m, 0)).2 ≤ i := halve_count_le m i
  unfold halfBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws (o := wU) (a := wR) (by decide) (by decide) (by decide) (by decide))
    fun t1 ⟨w1, k1, v1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok w1 (o := wH) (a := wR) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨w2, k2, v2, r2, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.keep [.r9] (Q := fun x => x.gpr .r9 = 0 ∧ x.mem = t2.mem) (by prun []; rfl) (by decide))
    fun t3 ⟨⟨a9, m3⟩, k3⟩ => ?_
  have w3 := w2.of_keep k3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok w3 (j := wH) (by decide) (by decide) (by rw [a9]; decide)) fun t4 ⟨w4, k4, v4, r4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), halfBit]
  have fit : ∀ j < 16, arr v j + S v ≤ 2 ^ 64 := fun j hj => w4.fit64 hj
  have eR : num t4.mem B v wR = (halveStep^[i] (m, 0)).1 := by
    rw [k4.num (by decide) (by simp) (fit wR (by decide)), m3, k2.num (by decide) (by simp) (fit wR (by decide)),
      k1.num (by decide) (by simp) (fit wR (by decide))]
    exact h.vR
  have eT : slot t4.mem B sTc = (halveStep^[i] (m, 0)).2 := by
    rw [KeyWorkspace.Keep.slot (e := sTc) k4 (by decide) (by simp), m3,
      KeyWorkspace.Keep.slot (e := sTc) k2 (by decide) (by simp), KeyWorkspace.Keep.slot (e := sTc) k1 (by decide)
      (by simp)]
    exact h.vT
  refine bitOf_ok w4 (j := wR) (sl := sBit) (by decide) (by decide) (by decide) fun t5 w5 k5 b5 r5 => ?_
  have eT5 : slot t5.mem B sTc = (halveStep^[i] (m, 0)).2 := by
    rw [KeyWorkspace.Keep.slot (e := sTc) k5 (by decide) (by simp [sBit, sTc])]; exact eT
  have hb5 : slot t5.mem B sBit ≤ 1 := by rw [b5]; omega
  refine WP.mono (halfRest_ok w5 hb5 (by rw [eT5]; omega)) fun t6 ⟨w6, k6, b6, T6, r6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok w6 (o := wR) (a := wU) (b := wH) (sl := sBit) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [b6]; omega)) fun t7 ⟨w7, k7, v7, r7⟩ => ?_
  rw [show seqs [.block [.subi .r27 .r27 1]] = .block [.subi .r27 .r27 1] from rfl]
  refine WP.mono (WP.keep [.r27] (Q := fun x => x.gpr .r27 = t7.gpr .r27 - BitVec.ofNat 64 1 ∧ x.mem = t7.mem)
    (by prun []) (by decide)) fun t8 ⟨⟨a27, m8⟩, k8⟩ => ?_
  have K : Keep (.r27 :: opRegs) u t8 :=
    ((((((((r1.trans r2).trans k3).trans r4).trans r5).trans r6).trans r7).trans k8)).mono
  have e27 : t7.gpr .r27 = u.gpr .r27 := (((((((r1.trans r2).trans k3).trans r4).trans r5).trans r6).trans r7)).gpr _
    (by decide)
  have KK : KeyWorkspace.Keep B v [wR, wU, wH] [sBit, sTc] u.mem t8.mem := by
    rw [m8]
    exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono k1) (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono k2)
      (KeyWorkspace.Keep.trans (by rw [← m3]; exact KeyWorkspace.Keep.mono k4) (KeyWorkspace.Keep.trans
        (KeyWorkspace.Keep.mono k5) (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono k6) (KeyWorkspace.Keep.mono k7)))))
  refine ⟨⟨w7.of_keep k8, h.keep.trans KK, ?_, ?_, (h.regs.trans K).mono⟩, by rw [a27, e27]⟩
  · -- The value.
    rw [m8, v7, Function.iterate_succ_apply', b6, b5, eR]
    have eU : num t6.mem B v wU = (halveStep^[i] (m, 0)).1 := by
      rw [k6.num (by simp) (by simp [sBit, sTc, KeyWorkspace.hdr]) (fit wU (by decide)),
        k5.num (by simp) (by simp [sBit, KeyWorkspace.hdr]) (fit wU (by decide)),
        k4.num (by decide) (by simp) (fit wU (by decide)), m3, k2.num (by decide) (by simp) (fit wU (by decide)), v1]
      exact h.vR
    have eH : num t6.mem B v wH = (halveStep^[i] (m, 0)).1 / 2 := by
      rw [k6.num (by simp) (by simp [sBit, sTc, KeyWorkspace.hdr]) (fit wH (by decide)),
        k5.num (by simp) (by simp [sBit, KeyWorkspace.hdr]) (fit wH (by decide)), v4, a9, m3, v2]
      rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
      rw [k1.num (by decide) (by simp) (fit wR (by decide))]
      rw [h.vR]
    rw [eU, eH]
    generalize halveStep^[i] (m, 0) = st
    unfold halveStep
    rcases Nat.mod_two_eq_zero_or_one st.1 with e | e <;> simp [e]
  · rw [KeyWorkspace.Keep.slot (e := sTc) (by rw [m8]; exact k7) (by decide) (by simp), T6, eT5,
      Function.iterate_succ_apply', b5, eR]
    generalize halveStep^[i] (m, 0) = st
    unfold halveStep
    rcases Nat.mod_two_eq_zero_or_one st.1 with e | e <;> simp [e]

/-- `m = d e - 1`. -/
abbrev mV (s0 : State) : Nat := 2 * (dV s0 * eV s0 / 2)

/-- After the halvings: `m = 2^t r`, `r` in the array `wR` of the `W` view and `t` in `sTc`. -/
structure HalvS (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = BitVec.ofNat 64 (cB s0)
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  zK : ∀ j ∈ [aOne, aZ], ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) j + 4 * i) = 0
  vR : num t.mem (rvB s0) (wW (kK s0)) wR = (Spec.Rsa.splitTwos (mV s0)).2
  vT : slot t.mem (rvB s0) sTc = (Spec.Rsa.splitTwos (mV s0)).1
  odd : dV s0 * eV s0 % 2 = 1
  two : 2 ≤ dV s0 * eV s0

theorem halving_ok {s0 t : State} (h : NumS s0 t) (hgo : t.gpr .r0 = 0) : WP isa halving t (HalvS s0) := by
  have z := h.base.sz
  have w1 := z.w1; have w2 := z.w2; have svW := z.svW; have nw := z.nw; have svZ := z.svZ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, e1, e2, d1, d2,
    -⟩ := id h.base.pre
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  obtain ⟨odd, two⟩ := h.go.mp hgo
  -- `m` below `2^c`.
  have bD : dV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) := by
    have := os2ip_lt8 (dB s0); simp only [dB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have bE : eV s0 < 2 ^ (8 * (s0.gpr .r10).toNat) := by
    have := os2ip_lt8 (eB s0); simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have hm : mV s0 < 2 ^ cB s0 := by
    have : dV s0 * eV s0 < 2 ^ cB s0 :=
      calc dV s0 * eV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) * 2 ^ (8 * (s0.gpr .r10).toNat) :=
            Nat.mul_lt_mul'' bD bE
        _ = 2 ^ cB s0 := by rw [← Nat.pow_add]; congr 1; simp only [cB]; omega
    simp only [mV]; omega
  have hm0 : 0 < mV s0 := by simp only [mV]; omega
  have hc : cB s0 < 2 ^ 31 := by simp only [cB]; omega
  unfold halving
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil VG.Impl.Rsa.PPC64LE.Recover.ctxW]
  refine ctxW_ok h.ws (by omega) (Nat.le_trans svW (Nat.le_trans (Nat.le_add_right _ _) svZ))
    fun t1 w1' m1 k1 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), halfInit, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok w1' (o := wR) (a := wM) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨w2', k2, v2, r2, _⟩ => ?_
  rw [show seqs [.block [.li .r0 0, .store .w .r0 .r31 sTc, .addi .r27 .r26 0]] =
    .block [.li .r0 0, .store .w .r0 .r31 sTc, .addi .r27 .r26 0] from rfl]
  have hz : 160 ≤ rvZ s0 := w2'.hdr_le
  refine WP.mono (WP.keep [.r0, .r27] (Q := fun x => x.mem = t2.mem.writeW (off (rvB s0) sTc) (0 : BitVec 32) ∧
    x.gpr .r27 = t2.gpr .r26)
    (by
      prun [w2'.r31, exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sTc < 2 ^ 15 by decide),
        w2'.scr.st (show sTc + 4 ≤ rvZ s0 by simp only [sTc]; omega), BitVec.add_zero]
      rfl) (by decide)) fun t3 ⟨⟨m3, a27⟩, k3⟩ => ?_
  have w3 := w2'.of_keep k3
  have fitW : ∀ j < 16, arr (wW (kK s0)) j + S (wW (kK s0)) ≤ 2 ^ 64 := fun j hj => w3.fit64 hj
  have kk3 : KeyWorkspace.Keep (rvB s0) (wW (kK s0)) [] [sTc] t2.mem t3.mem := by
    rw [m3]; exact keep_slot _ _ (by simp) (by simp only [sTc]; omega)
  have hW : 2 * ww (kK s0) + 2 = wW (kK s0) := rfl
  rw [hW] at w1' w2' w3 k2 v2
  have i0 : HInv (rvB s0) (rvZ s0) (wW (kK s0)) t3 (mV s0) 0 t3 :=
    ⟨w3, KeyWorkspace.Keep.refl _ _ _ _ _, by
      rw [kk3.num (by simp) (by simp [sTc, KeyWorkspace.hdr]) (fitW wR (by decide)), v2, m1]; exact h.vM,
      by rw [m3, slot_write_self]; rfl, Keep.refl _ _⟩
  have a27' : t3.gpr .r27 = BitVec.ofNat 64 (cB s0) := by
    rw [a27, r2.gpr _ (by decide), k1.gpr _ (by decide)]; exact h.r26
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (wp_countdown (body := halfBody) (cnt := .r27) (N := cB s0) (by omega) (by simp only [cB]; omega)
    (HInv (rvB s0) (rvZ s0) (wW (kK s0)) t3 (mV s0)) (fun i hi u inv _ => halfBody_ok (by omega) inv) i0 a27')
    fun t4 inv => ?_
  rw [show seqs [.block VG.Impl.Rsa.PPC64LE.Recover.ctxw] = .block VG.Impl.Rsa.PPC64LE.Recover.ctxw from rfl,
    ← List.append_nil VG.Impl.Rsa.PPC64LE.Recover.ctxw]
  have ws4 := inv.ws
  rw [← hW] at ws4
  refine ctxw_ok ws4 (by omega) (by rw [← z.svw]; omega) fun t5 w5 m5 k5 => WP.block_nil ?_
  have hd := halve_done hm0 hm
  -- What the steps kept.
  have K : Keep (.r29 :: .r30 :: .r27 :: .r0 :: opRegs) t t5 :=
    (((((k1.trans r2).trans k3).trans inv.regs).trans k5)).mono
  have KK : KeyWorkspace.Keep (rvB s0) (wW (kK s0)) [wR, wU, wH] [sBit, sTc] t.mem t5.mem := by
    rw [m5, ← m1]
    exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono k2) (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk3)
      inv.keep)
  have hA16 : arr (wW (kK s0)) 16 = arr (ww (kK s0)) 32 := arrW16 _
  have far : ∀ d n, arr (ww (kK s0)) 32 ≤ d → d + 4 * n ≤ 2 ^ 64 →
      val32 t5.mem (rvB s0) d n = val32 t.mem (rvB s0) d n := fun d n h1 h2 =>
    keep_far (J := 16) KK (by decide) (by simp [sBit, sTc]) (by rw [hA16]; exact h1) h2
  refine ⟨h.base.of_keep KK (fun j hj => ?_) (fun d hd => ?_) K, w5,
    by rw [K.gpr _ (by decide)]; exact h.r21, by rw [K.gpr _ (by decide)]; exact h.r23,
    by rw [K.gpr _ (by decide)]; exact h.r24, by rw [K.gpr _ (by decide)]; exact h.r25,
    by rw [K.gpr _ (by decide)]; exact h.r26, ?_, ?_, ?_, ?_, odd, two⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end this) svW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  · simp only [num]
    rw [far _ _ (VG.Proof.Rsa.KeyWorkspace.arr_mono (by decide))
      (Nat.le_trans (Nat.add_le_add_left (by simp only [S]; omega) _) (w5.fit64 (j := aN) (by decide)))]
    exact h.vN
  · intro j hj i hi
    have hj' : j = 33 ∨ j = 34 := by simpa [aOne, aZ] using hj
    have f64 := w5.fit64 (j := j) (by simp only [nArr]; omega)
    have := far (arr (ww (kK s0)) j + 4 * i) 1
      (Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_mono (by omega)) (Nat.le_add_right _ _))
      (by simp only [S] at f64; omega)
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact h.zK j hj i hi
  · rw [m5, inv.vR, hd]
  · rw [m5, inv.vT, hd]

end VG.Proof.Rsa.PPC64LE.Recover
