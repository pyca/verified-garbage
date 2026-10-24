module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCtx
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: `y = g^r`

`expBody_ok`: a bit of `r` (from `EI s0 j i` to `EI s0 j (i + 1)`), and
`expLoop_ok`: all `c` of them.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (expBody expLoop mmul mBase mY mG mXm aO nArr iY iG iXm wRc sBit)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A bit of `r`. -/
theorem expBody_ok {s0 u : State} (hn : NOk s0) {j i : Nat} (h : EI s0 j i u) :
    WP isa expBody u fun t => EI s0 j (i + 1) t ∧ t.gpr .r27 = u.gpr .r27 - BitVec.ofNat 64 1 := by
  have c := h.cf
  have z := c.base.sz
  have w1 := z.w1; have w2 := z.w2; have svW := z.svW; have svZ := z.svZ; have svw := z.svw
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => c.ws.fit64 hj
  have f32 : arr (ww (kK s0)) 32 ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_right _ _) (fit 32 (by decide))
  have hn0 : 0 < nV s0 := by have := hn.big; omega
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  unfold expBody
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  -- The bit, and `r`'s copy halved.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine ctxW_ok c.ws (by omega) (Nat.le_trans svW (Nat.le_trans (Nat.le_add_right _ _) svZ))
    fun u1 ws1 m1 k1 => ?_
  rw [← hW] at ws1
  refine bitOf_ok ws1 (j := wRc) (sl := sBit) (by decide) (by decide) (by decide) fun u2 ws2 kk2 b2 k2 => ?_
  refine WP.mono (WP.keep [.r9] (Q := fun x => x.gpr .r9 = 0 ∧ x.mem = u2.mem) (by prun; rfl) (by decide))
    fun u3 ⟨⟨a9, m3⟩, k3⟩ => ?_
  have ws3 := ws2.of_keep k3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok ws3 (j := wRc) (by decide) (by decide) (by rw [a9]; decide))
    fun u4 ⟨ws4, kk4, v4, k4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil VG.Impl.Rsa.PPC64LE.Recover.ctxw]
  rw [hW] at ws4
  refine ctxw_ok ws4 (by omega) (by rw [← svw]; omega) fun u5 ws5 m5 k5 => WP.block_nil ?_
  have kk5 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [30, 31] [sBit] u.mem u5.mem := by
    have a := keepW_key (w := ww (kK s0)) kk2; have b := keepW_key (w := ww (kK s0)) kk4
    rw [m1] at a; rw [m3] at b; rw [m5]
    exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono a (by decide) (by decide))
      (KeyWorkspace.Keep.mono b (by decide) (by decide))
  have K5 : Keep (.r9 :: .r29 :: .r30 :: opRegs) u u5 := ((((k1.trans k2).trans k3).trans k4).trans k5).mono
  have c5 := c.of_keep kk5 (by decide) (by decide) K5 ws5
  have bit : slot u5.mem (rvB s0) sBit = rR s0 / 2 ^ i % 2 := by
    rw [m5, kk4.slot (e := sBit) (by decide) (by simp), m3, b2, m1, ← h.vRc]
  have Rc5 : num u5.mem (rvB s0) (wW (kK s0)) wRc = rR s0 / 2 ^ (i + 1) := by
    rw [m5, v4, a9, m3, kk2.num (by simp) (by decide) (ws2.fit64 (by decide)), m1, h.vRc]
    rw [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl, Nat.mul_zero, Nat.add_zero, Nat.div_div_eq_div_mul,
      Nat.pow_succ]
  have Y5 : num u5.mem (rvB s0) (ww (kK s0)) mY = num u.mem (rvB s0) (ww (kK s0)) mY :=
    kk5.num (by decide) (by decide) (fit mY (by decide))
  have G5 : num u5.mem (rvB s0) (ww (kK s0)) mG = num u.mem (rvB s0) (ww (kK s0)) mG :=
    kk5.num (by decide) (by decide) (fit mG (by decide))
  -- The multiplicand.
  rw [wp_seqs_cons (by simp [mmul])]
  refine WP.mono (sel_ok c5.ws (o := mXm) (a := aO) (b := mG) (sl := sBit) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [bit]; omega)) fun u6 ⟨ws6, kk6, v6, k6⟩ => ?_
  have c6 := c5.of_keep kk6 (by decide) (by simp) k6 ws6
  have X6 : num u6.mem (rvB s0) (ww (kK s0)) mXm =
      if rR s0 / 2 ^ i % 2 = 0 then RR s0 % nV s0 else (j + 2) ^ (2 ^ i) * RR s0 % nV s0 := by
    rw [v6, bit, c5.vO, G5, h.vG]
  have Xl : num u6.mem (rvB s0) (ww (kK s0)) mXm < nV s0 := by rw [X6]; split <;> exact Nat.mod_lt _ hn0
  have Y6 : num u6.mem (rvB s0) (ww (kK s0)) mY = (j + 2) ^ (rR s0 % 2 ^ i) * RR s0 % nV s0 := by
    rw [kk6.num (by decide) (by simp) (fit mY (by decide)), Y5, h.vY]
  have G6 : num u6.mem (rvB s0) (ww (kK s0)) mG = (j + 2) ^ (2 ^ i) * RR s0 % nV s0 := by
    rw [kk6.num (by decide) (by simp) (fit mG (by decide)), G5, h.vG]
  have Yl : num u6.mem (rvB s0) (ww (kK s0)) mY < nV s0 := by rw [Y6]; exact Nat.mod_lt _ hn0
  have Gl : num u6.mem (rvB s0) (ww (kK s0)) mG < nV s0 := by rw [G6]; exact Nat.mod_lt _ hn0
  -- `y` times it.
  rw [wp_seqs_append (by simp [mmul]) (by simp [mmul])]
  refine WP.mono (mmul_ok c6.base c6.ws (o := iY) (a := iY) (b := iXm) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c6.r12 c6.inv
    (by rw [c6.vMN]; change lowV u6.mem s0 mXm < _; rw [low_of_lt Xl]; exact Xl))
    fun u7 ⟨_, ws7, kk7, lt7, eq7, k7⟩ => ?_
  have c7 := c6.of_keep kk7 (by decide) (by simp) k7 ws7
  change num u7.mem (rvB s0) (ww (kK s0)) mY < lowV u6.mem s0 mBase at lt7
  change num u7.mem (rvB s0) (ww (kK s0)) mY * RR s0 % lowV u6.mem s0 mBase =
    lowV u6.mem s0 mY * lowV u6.mem s0 mXm % lowV u6.mem s0 mBase at eq7
  rw [c6.vMN, low_of_lt Yl, low_of_lt Xl] at eq7
  rw [c6.vMN] at lt7
  have G7 : num u7.mem (rvB s0) (ww (kK s0)) mG = num u6.mem (rvB s0) (ww (kK s0)) mG :=
    kk7.num (by decide) (by simp) (fit mG (by decide))
  -- `g^(2^i)` squared.
  rw [wp_seqs_append (by simp [mmul]) (List.cons_ne_nil _ _)]
  refine WP.mono (mmul_ok c7.base c7.ws (o := iG) (a := iG) (b := iG) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c7.r12 c7.inv
    (by rw [c7.vMN]; change lowV u7.mem s0 mG < _; rw [low_of_lt (by rw [G7]; exact Gl), G7]; exact Gl))
    fun u8 ⟨_, ws8, kk8, lt8, eq8, k8⟩ => ?_
  have c8 := c7.of_keep kk8 (by decide) (by simp) k8 ws8
  change num u8.mem (rvB s0) (ww (kK s0)) mG < lowV u7.mem s0 mBase at lt8
  change num u8.mem (rvB s0) (ww (kK s0)) mG * RR s0 % lowV u7.mem s0 mBase =
    lowV u7.mem s0 mG * lowV u7.mem s0 mG % lowV u7.mem s0 mBase at eq8
  rw [c7.vMN, low_of_lt (by rw [G7]; exact Gl), G7] at eq8
  rw [c7.vMN] at lt8
  have Y8 : num u8.mem (rvB s0) (ww (kK s0)) mY = num u7.mem (rvB s0) (ww (kK s0)) mY :=
    kk8.num (by decide) (by simp) (fit mY (by decide))
  obtain ⟨eY, eG⟩ := exp_step hn.coprime Y6 G6 (by rw [X6, G6]) lt7 eq7 lt8 eq8
  -- The count.
  rw [show seqs [Code.block [Instr.subi .r27 .r27 1]] = .block [.subi .r27 .r27 1] from rfl]
  refine WP.mono (WP.keep [.r27] (Q := fun x => x.gpr .r27 = u8.gpr .r27 - BitVec.ofNat 64 1 ∧ x.mem = u8.mem)
    (by prun) (by decide)) fun t ⟨⟨a27, mt⟩, kt⟩ => ?_
  have K8 : Keep mmRegs u5 u8 := ((k6.mono (rs' := mmRegs) (by decide)).trans (k7.trans k8)).mono
  have ct := c8.of_keep (show KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u8.mem t.mem by
    rw [mt]; exact KeyWorkspace.Keep.refl _ _ _ _ _) (by simp) (by simp) kt (c8.ws.of_keep kt)
  refine ⟨⟨ct, ?_, by rw [mt, Y8]; exact eY, by rw [mt]; exact eG, ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), K8.gpr _ (by decide), K5.gpr _ (by decide)]; exact h.r24
  · rw [mt, keepW_num kk8 (j := wRc) (by decide) f32, keepW_num kk7 (j := wRc) (by decide) f32,
      keepW_num kk6 (j := wRc) (by decide) f32]
    exact Rc5
  · rw [a27, K8.gpr _ (by decide), K5.gpr _ (by decide)]

/-- `y = g^r` in Montgomery form, and `r`'s copy 0. -/
theorem expLoop_ok {s0 u : State} (hn : NOk s0) {j : Nat} (h : EI s0 j 0 u)
    (h27 : u.gpr .r27 = BitVec.ofNat 64 (cB s0)) (hc0 : 0 < cB s0) (hc : cB s0 < 2 ^ 31) :
    WP isa expLoop u (EI s0 j (cB s0)) :=
  wp_countdown (body := expBody) (cnt := .r27) (N := cB s0) (by omega) hc0 (EI s0 j)
    (fun _ _ _ e _ => expBody_ok hn e) h h27

end VG.Proof.Rsa.PPC64LE.Recover
