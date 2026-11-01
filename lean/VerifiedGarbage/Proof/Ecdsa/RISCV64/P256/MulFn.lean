module

public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Weierstrass.Mul
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's ladder on RISC-V

The facts the proofs of `vg_p256_mul` and its callers share: P-256's field
functions meet the contracts by register (`field_ok`), the ladder's slots
are laid out as `ladder_ok` needs (`lay`), and `mulBody` computes `R = [k]Q`
(`mulBody_ok`): it copies `Q` from `R`'s first two slots to `ACC` and `PT`,
sets `R = O` from zero and one, and runs the ladder, whose invariant is that
`R` represents `[k >>> j]Q` (`step_rep`), given the group law.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-256. -/
abbrev W : Curve := Spec.P256.curve

theorem field_ok : FieldOk p256Field :=
  ⟨P256Field.mul_rv, P256Field.add_rv, P256Field.sub_rv, Impl.Weierstrass.RISCV64.P256Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.P256Field.addFn_noFrames, Impl.Weierstrass.RISCV64.P256Field.subFn_noFrames⟩

instance : NeZero p256Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

theorem lay : LadLayR p256.mulLadder where
  lay := {
    lay := ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ ladSlots p256.mulLadder, ∀ y ∈ ladSlots p256.mulLadder,
      x ≠ y → x + 8 * p256.mulLadder.M.n ≤ y ∨ y + 8 * p256.mulLadder.M.n ≤ x) x hx y hy, by decide, by decide⟩
    a1 := ⟨by decide, by decide⟩
    a2 := ⟨by decide, by decide⟩
    ro := by decide
    rne := by decide
    rdt := by decide
    nbits := by decide
    bits := by decide
    bits_w := by decide }
  al := by decide
  short := by decide
  kal := by decide
  kshort := by decide
  kw := by decide
  nbits := by decide
  nbits' := by decide
  n0 := by decide

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p256.sl i) 4

/-- What `mulBody` writes: the copies' slots, and the ladder's. -/
def mulBW : List (Nat × Nat) :=
  [(p256.sl ACC, 32), (p256.sl PT, 32), (p256.sl RX, 32), (p256.sl RY, 32), (p256.sl RZ, 32)] ++
    ladWx p256.mulLadder

/-- A slot apart from a copy's. -/
theorem sv_out {base : Addr} {m m' : Mem} {o i : Nat} (O : Outside base (p256.sl o) (8 * 4) m m')
    (h : p256.sl i + 32 ≤ p256.sl o ∨ p256.sl o + 32 ≤ p256.sl i) (hi : p256.sl i + 32 ≤ 2 ^ 64) :
    wordsVal m' base (p256.sl i) 4 = wordsVal m base (p256.sl i) 4 :=
  O.wordsVal h hi

/-- The copies of `mulBody`. -/
theorem copies_ok {base : Addr} {s : State} (hw : WsReg s base) :
    WP isa (.block (copy 4 (p256.sl ACC) (p256.sl RX) ++ copy 4 (p256.sl PT) (p256.sl RY) ++
      copy 4 (p256.sl RX) (p256.sl ZERO) ++ copy 4 (p256.sl RY) (p256.sl ONEP) ++
      copy 4 (p256.sl RZ) (p256.sl ZERO))) s fun s₅ =>
      Kc s s₅ ∧ Unch base (mulBW.take 5) s.mem s₅.mem ∧
      sv base s₅ ACC = sv base s RX ∧ sv base s₅ PT = sv base s RY ∧ sv base s₅ RX = sv base s ZERO ∧
      sv base s₅ RY = sv base s ONEP ∧ sv base s₅ RZ = sv base s ZERO ∧
      (∀ i ∈ [ZERO, ONEP, AP, B3P, K], sv base s₅ i = sv base s i) := by
  have hn := hw.nowrap
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := p256.sl ACC) (a := p256.sl RX) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest k₁
  refine WP.block_append (WP.mono (copy_ok 4 hw₁ (o := p256.sl PT) (a := p256.sl RY) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest k₂
  refine WP.block_append (WP.mono (copy_ok 4 hw₂ (o := p256.sl RX) (a := p256.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest k₃
  refine WP.block_append (WP.mono (copy_ok 4 hw₃ (o := p256.sl RY) (a := p256.sl ONEP) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest k₄
  refine WP.mono (copy_ok 4 hw₄ (o := p256.sl RZ) (a := p256.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨x₅, k₅, O₅⟩ => ?_
  have o : ∀ {m m' : Mem} {o i : Nat}, Outside base (p256.sl o) (8 * 4) m m' →
      (p256.sl i + 32 ≤ p256.sl o ∨ p256.sl o + 32 ≤ p256.sl i) → p256.sl i < 4096 →
      wordsVal m' base (p256.sl i) 4 = wordsVal m base (p256.sl i) 4 := fun O h hi =>
    sv_out O h (by omega)
  simp only [sv]
  refine ⟨Kc.of_rest ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((O₁.unch.trans O₂.unch).trans O₃.unch).trans O₄.unch).trans O₅.unch).mono fun w hw => by
      simp only [mulBW, List.take, List.cons_append, List.mem_cons, List.nil_append,
        List.not_mem_nil, or_false] at hw ⊢
      omega
  · rw [o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), x₁]
  · rw [o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), x₂,
      o O₁ (by decide) (by decide)]
  · rw [o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), x₃, o O₂ (by decide) (by decide),
      o O₁ (by decide) (by decide)]
  · rw [o O₅ (by decide) (by decide), x₄, o O₃ (by decide) (by decide), o O₂ (by decide) (by decide),
      o O₁ (by decide) (by decide)]
  · rw [x₅, o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), o O₂ (by decide) (by decide),
      o O₁ (by decide) (by decide)]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rw [o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), o O₁ (by decide) (by decide)]

theorem mul_zero_pt (P : Point W) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- `mulBody`: from `Q` in `R`'s first two slots, zero, one, `a` and `3b`
in their slots, `R` represents `[k]Q`, for the number `k` at `K`'s slot. -/
theorem mulBody_ok (hL : VG.Proof.Weierstrass.Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hz : sv base s ZERO = 0) (hone : sv base s ONEP = 2 ^ 256 % W.p)
    (ha : toM W.p (2 ^ 256) (sv base s AP) = Fin.ofNat W.p W.a)
    (hb : toM W.p (2 ^ 256) (sv base s B3P) = Fin.ofNat W.p (3 * W.b))
    (hap : sv base s AP < W.p) (hbp : sv base s B3P < W.p)
    (hx : sv base s RX < W.p) (hy : sv base s RY < W.p)
    (hon : Spec.Weierstrass.onCurve W
      (.affine (toM W.p (2 ^ 256) (sv base s RX)) (toM W.p (2 ^ 256) (sv base s RY))) = true) :
    WP isa p256.mulBody s fun s' => Kc s s' ∧ Unch base mulBW s.mem s'.mem ∧
      (∀ x ∈ [p256.sl RX, p256.sl RY, p256.sl RZ], wordsVal s'.mem base x 4 < W.p) ∧
      Rep W (tmv W 4 base s' (p256.sl RX)) (tmv W 4 base s' (p256.sl RY)) (tmv W 4 base s' (p256.sl RZ))
        (Spec.Weierstrass.mul (sv base s K)
          (.affine (toM W.p (2 ^ 256) (sv base s RX)) (toM W.p (2 ^ 256) (sv base s RY)))) := by
  have hp0 : 0 < W.p := by decide
  have hone' : 2 ^ 256 % W.p < W.p := Nat.mod_lt _ hp0
  rw [Cfg.mulBody, show p256.n = 4 from rfl]
  refine WP.seq (WP.mono (copies_ok hw) fun s₅ ⟨K₅, U₅, acc₅, pt₅, rx₅, ry₅, rz₅, e₅⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e₅
  obtain ⟨z₅, o₅, a₅, b₅, k₅⟩ := e₅
  have hw₅ := hw.of_kc K₅
  generalize hP : (Point.affine (toM W.p (2 ^ 256) (sv base s RX)) (toM W.p (2 ^ 256) (sv base s RY)) :
    Point W) = P at hon ⊢
  have tone : tmv W 4 base s₅ (p256.sl ONEP) = 1 := by
    show toM _ _ (sv base s₅ ONEP) = 1; rw [o₅, hone]; exact toM_one unit
  have hG : Rep W (tmv W 4 base s₅ (p256.sl ACC)) (tmv W 4 base s₅ (p256.sl PT)) (tmv W 4 base s₅ (p256.sl ONEP)) P := by
    rw [tone, ← hP]
    show Rep W (toM _ _ (sv base s₅ ACC)) (toM _ _ (sv base s₅ PT)) 1 _
    rw [acc₅, pt₅]; exact rep_affine' hL _ _
  have st := step_rep (L := p256.mulLadder) (base := base) (s := s₅) (k := sv base s₅ K) hL hon
    (by show toM _ _ (sv base s₅ AP) = _; rw [a₅]; exact ha)
    (by show toM _ _ (sv base s₅ B3P) = _; rw [b₅]; exact hb) hG
  have hk : sv base s₅ K < 2 ^ 256 := wordsVal_lt _ _ _ 4
  refine WP.mono (ladder_ok (L := p256.mulLadder) (C := W) (F := p256Field) field_ok rfl rfl unit lay hw₅
    (fun x hx => ?_) st ?_) fun s' ⟨Kl, Ul, ltl, ql⟩ => ⟨K₅.trans Kl, (U₅.trans Ul).mono fun w hw => ?_, ltl, ?_⟩
  · simp only [ladR, ladRo, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show sv base s₅ AP < _; rw [a₅]; exact hap
    · show sv base s₅ B3P < _; rw [b₅]; exact hbp
    · show sv base s₅ ACC < _; rw [acc₅]; exact hx
    · show sv base s₅ PT < _; rw [pt₅]; exact hy
    · show sv base s₅ ONEP < _; rw [o₅, hone]; exact hone'
    · show sv base s₅ RX < _; rw [rx₅, hz]; exact hp0
    · show sv base s₅ RY < _; rw [ry₅, hone]; exact hone'
    · show sv base s₅ RZ < _; rw [rz₅, hz]; exact hp0
  · show Rep W (toM W.p (2 ^ 256) (sv base s₅ RX)) (toM W.p (2 ^ 256) (sv base s₅ RY))
      (toM W.p (2 ^ 256) (sv base s₅ RZ)) _
    rw [rx₅, ry₅, rz₅, hz, hone, toM_zero, toM_one unit, show (p256.mulLadder).nbits = 256 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hk, mul_zero_pt]
    exact rep_infinity' hL
  · rwa [show List.take 5 mulBW ++ ladWx p256.mulLadder = mulBW from rfl] at hw
  · rw [Nat.shiftRight_zero, k₅] at ql; exact ql

end VG.Proof.Ecdsa.RISCV64.P256
