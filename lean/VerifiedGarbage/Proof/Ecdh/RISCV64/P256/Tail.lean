module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Setup
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# ECDH and public keys over P-256 on RISC-V: the multiplication and after

What follows the point's setup in both functions (`tail`): the masks of `d`
in `[1, n-1]` into the flag (`range_ok`), `R = [d]P` by a call of
`vg_p256_mul` (`mul_rv`), `Z^(p-2)` by `pow` (`pow_ok`), and `x = X Z^(p-2)`
out of Montgomery's form (`affine_ok`). The callees' `Keeps` are frames
(`unch_of_mulKeeps`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- What `vg_p256_mul` may write, as ranges of offsets. -/
abbrev mulKW : List (Nat × Nat) := [(512, 96), (608, 448), (128, 32), (1344, 32), (1504, 2 ^ 64)]

theorem unch_of_mulKeeps {base : Addr} {m m' : Mem} (h : MC.Keeps base m m') : Unch base mulKW m m' := by
  intro x hx
  have e := fun w hw => hx w hw
  simp only [mulKW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  have hb : ofs base x < 2 ^ 64 := (x - base).isLt
  have hlt : ofs base x < 1504 := by omega
  have ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ (by show _ < 8192; omega) ?_ ?_
  · simp only [Spec.Weierstrass.Mul.Curve.Own, Spec.Weierstrass.Mul.Curve.slot, Spec.Weierstrass.Mul.Curve.tmpAt,
      Spec.Weierstrass.Mul.Curve.bitsAt, MC, Spec.Weierstrass.Mul.p256, true_and]
    omega
  · simp only [Spec.Weierstrass.Mul.Curve.pAt, Spec.Weierstrass.Mul.Curve.ptBytes, Spec.Weierstrass.Mul.Curve.slot,
      MC, Spec.Weierstrass.Mul.p256]
    omega

/-- What `vg_p256_check_point` may write, as ranges of offsets. -/
abbrev checkKW : List (Nat × Nat) :=
  [(128, 32), (1248, 32), (1376, 32), (1408, 32), (3840, 256), (1152, 32), (1184, 32), (1280, 32), (1440, 32),
    (FL, 8), (8192, 2 ^ 64)]

theorem unch_of_checkKeeps {base : Addr} {m m' : Mem} (h : CC.Keeps base m m') : Unch base checkKW m m' := by
  intro x hx
  have e := fun w hw => hx w hw
  simp only [checkKW, FL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  have hb : ofs base x < 2 ^ 64 := (x - base).isLt
  have hlt : ofs base x < 8192 := by omega
  have ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ hlt ?_ ?_
  · simp only [Spec.Weierstrass.CheckPoint.Curve.Own, Spec.Weierstrass.CheckPoint.Curve.slot, CC,
      Spec.Weierstrass.CheckPoint.p256, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega
  · simp only [Spec.Weierstrass.CheckPoint.Curve.Out, Spec.Weierstrass.CheckPoint.Curve.slot,
      Spec.Weierstrass.CheckPoint.Curve.flagAt, CC, Spec.Weierstrass.CheckPoint.p256,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

/-- The masks of `d < n` and `d ≠ 0` into the flag. -/
theorem range_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeCode p256)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < sv base s MN)) &&&
        maskOf (!decide (sv base s K = 0)) := by
  rw [rangeCode, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := 4) (a := p256.sl K) (m := p256.sl MN) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (zeroMask_ok hw₂ (n := 4) (a := p256.sl K) (by decide) (by decide))
    fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  refine WP.cons (exec_logicImm (by decide)) ?_
  have hw₃' := (hw₂.of_rest r₃).of_kp (Kp.of_upd (Upd.write s₃ .a7 (s₃.gpr .a7 ^^^ BitVec.ofInt 64 (-1))))
  refine WP.mono (andFlag_ok hw₃') fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans
      ((Kp.of_upd (Upd.write s₃ .a7 _)).trans (Kp.of_rest r₄))))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have k₂ : sv base s₂ K = sv base s K := by
      show wordsVal _ _ _ _ = _
      rw [O₂.wordsVal (by decide) (by decide), m₁]
    rw [f₄]
    simp only [State.write, ↓reduceIte]
    rw [m₃, f₂, m₁, g₁, g₃, not_mask]
    simp only [sv] at k₂
    rw [k₂]

/-- The constants `tail` reads. -/
structure TailConsts (base : Addr) (s : State) : Prop where
  mp : sv base s MP = W.p
  mn : sv base s MN = W.n
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  onep : sv base s ONEP = 1 * 2 ^ 256 % W.p
  ap : sv base s AP = W.a * 2 ^ 256 % W.p
  b3p : sv base s B3P = 3 * W.b * 2 ^ 256 % W.p
  expp : sv base s EXPP = W.p - 2

theorem TailConsts.of_unch {base : Addr} {s s' : State} {W' : List (Nat × Nat)} (h : TailConsts base s)
    (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', p256.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p256.sl i) :
    TailConsts base s' := by
  have e : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], sv base s' i = sv base s i := fun i hi =>
    sv_unch U i (hW i hi) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨(e MP (by simp)).trans h.mp, (e MN (by simp)).trans h.mn, (e ZERO (by simp)).trans h.zero,
    (e ONE (by simp)).trans h.one, (e ONEP (by simp)).trans h.onep, (e AP (by simp)).trans h.ap,
    (e B3P (by simp)).trans h.b3p, (e EXPP (by simp)).trans h.expp⟩

theorem powLay : PowLayR (powP p256) 4 where
  acc := by decide
  tmp := by decide
  base := by decide
  one := by decide
  short := by decide
  nbits := by decide
  k1 := by decide
  acc_tmp := by decide
  acc_one := by decide
  base_acc := by decide
  base_tmp := by decide
  bits_w := by decide
  acc8 := by decide
  tmp8 := by decide
  one8 := by decide
  bits8 := by decide

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv base s ACC < W.p) (hone : sv base s ONE = 1) :
    WP isa (affineCoord p256 t o a) s fun s' =>
      Kp s s' ∧ Unch base [(p256.sl t, 32), (own 4, 256), (p256.sl o, 32), (own 4, 256)] s.mem s'.mem ∧
      sv base s' o < W.p ∧
      Fin.ofNat W.p (sv base s' o) = toM W.p (2 ^ 256) (sv base s a) * toM W.p (2 ^ 256) (sv base s ACC) := by
  have hl : ∀ i, i < 44 → p256.sl i + 8 * p256Field.S.k ≤ own p256Field.S.k := fun i hi => by
    show 64 + 32 * i + 32 ≤ 3840 + 0 - 0 + 0; omega
  have hs : ∀ i, i < 44 → p256.sl i < 2048 := fun i hi => by rw [sl_eq]; omega
  have hk4 : p256Field.S.k = 4 := rfl
  rw [affineCoord]
  refine WP.seq (WP.mono (mulCall_ok field_ok hw (o := p256.sl t) (a := p256.sl a) (b := p256.sl ACC) (hl t ht)
    (hl a ha) (hl ACC (by decide)) (hs t ht) (hs a ha) (hs ACC (by decide)) hacc) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  have one₁ : sv base s₁ ONE = 1 := by
    rw [← hone]
    exact sv_unch (C₁.mem : Unch _ _ _ _) ONE (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [sl_eq, ONE]; simp only [ONE, ACC] at htm; omega
      · decide)
  refine WP.mono (mulCall_ok field_ok (hw.of_kp C₁.kp) (o := p256.sl o) (a := p256.sl t) (b := p256.sl ONE)
    (hl o ho) (hl t ht) (hl ONE (by decide)) (hs o ho) (hs t ht) (hs ONE (by decide))
    (by show sv base s₁ ONE < W.p; rw [one₁]; decide)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ⟨C₁.kp.trans C₂.kp,
      Unch.trans (C₁.mem : Unch _ _ _ _) (C₂.mem : Unch _ _ _ _), lt₂, ?_⟩
  have e₂' : sv base s₂ o * 2 ^ 256 % W.p = sv base s₁ t * 1 % W.p := by
    rw [← one₁]; exact e₂
  rw [toM_one_mul unit e₂']
  exact toM_mul unit e₁

end VG.Proof.Ecdh.RISCV64.P256
