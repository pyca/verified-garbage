module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# brainpoolP512r1's ladder on RISC-V

The facts the proofs of `vg_brainpoolp512r1_mul` and its callers share: brainpoolP512r1's field
functions, those modulo any wide modulus (`Proof/Weierstrass/RISCV64/GenWide/Field.lean`)
for its `p` (`p_ok`), meet the contracts by register (`field_ok`), the ladder's slots
are laid out as `ladder_ok` needs (`lay`), and `mulBody` computes `R = [k]Q`
(`mulBody_ok`): it copies `Q` from `R`'s first two slots to `ACC` and `PT`,
sets `R = O` from zero and one, and runs the ladder, whose invariant is that
`R` represents `[k >>> j]Q` (`step_rep`), given the group law.
-/

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- brainpoolP512r1. -/
abbrev W : Curve := Spec.BrainpoolP512r1.curve

private theorem p_ok : GenWide.WideOk Impl.Weierstrass.Mont.brainpoolp512r1p := ⟨by decide, by decide, by decide, by decide⟩

theorem field_ok : FieldOk brainpoolp512r1Field :=
  ⟨GenWide.mul_rv p_ok, GenWide.add_rv p_ok, GenWide.sub_rv p_ok, Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFn_noFrames⟩

instance : NeZero brainpoolp512r1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 8)) := unitMod_pow_two p_odd _

theorem lay : LadLayR brainpoolp512r1.mulLadder where
  lay := {
    lay := ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ ladSlots brainpoolp512r1.mulLadder, ∀ y ∈ ladSlots brainpoolp512r1.mulLadder,
      x ≠ y → x + 8 * brainpoolp512r1.mulLadder.M.n ≤ y ∨ y + 8 * brainpoolp512r1.mulLadder.M.n ≤ x) x hx y hy, by decide, by decide⟩
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
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (brainpoolp512r1.sl i) 8

/-- What `mulBody` writes: the copies' slots, and the ladder's. -/
def mulBW : List (Nat × Nat) :=
  [(brainpoolp512r1.sl ACC, 64), (brainpoolp512r1.sl PT, 64), (brainpoolp512r1.sl RX, 64), (brainpoolp512r1.sl RY, 64), (brainpoolp512r1.sl RZ, 64)] ++
    ladWx brainpoolp512r1.mulLadder

/-- A slot apart from a copy's. -/
theorem sv_out {base : Addr} {m m' : Mem} {o i : Nat} (O : Outside base (brainpoolp512r1.sl o) (8 * 8) m m')
    (h : brainpoolp512r1.sl i + 64 ≤ brainpoolp512r1.sl o ∨ brainpoolp512r1.sl o + 64 ≤ brainpoolp512r1.sl i) (hi : brainpoolp512r1.sl i + 64 ≤ 2 ^ 64) :
    wordsVal m' base (brainpoolp512r1.sl i) 8 = wordsVal m base (brainpoolp512r1.sl i) 8 :=
  O.wordsVal h hi

/-- The copies of `mulBody`. -/
theorem copies_ok {base : Addr} {s : State} (hw : WsReg s base) :
    WP isa (.block (copy 8 (brainpoolp512r1.sl ACC) (brainpoolp512r1.sl RX) ++ copy 8 (brainpoolp512r1.sl PT) (brainpoolp512r1.sl RY) ++
      copy 8 (brainpoolp512r1.sl RX) (brainpoolp512r1.sl ZERO) ++ copy 8 (brainpoolp512r1.sl RY) (brainpoolp512r1.sl ONEP) ++
      copy 8 (brainpoolp512r1.sl RZ) (brainpoolp512r1.sl ZERO))) s fun s₅ =>
      Kc s s₅ ∧ Unch base (mulBW.take 5) s.mem s₅.mem ∧
      sv base s₅ ACC = sv base s RX ∧ sv base s₅ PT = sv base s RY ∧ sv base s₅ RX = sv base s ZERO ∧
      sv base s₅ RY = sv base s ONEP ∧ sv base s₅ RZ = sv base s ZERO ∧
      (∀ i ∈ [ZERO, ONEP, AP, B3P, K], sv base s₅ i = sv base s i) := by
  have hn := hw.nowrap
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 8 hw (o := brainpoolp512r1.sl ACC) (a := brainpoolp512r1.sl RX) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest k₁
  refine WP.block_append (WP.mono (copy_ok 8 hw₁ (o := brainpoolp512r1.sl PT) (a := brainpoolp512r1.sl RY) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest k₂
  refine WP.block_append (WP.mono (copy_ok 8 hw₂ (o := brainpoolp512r1.sl RX) (a := brainpoolp512r1.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest k₃
  refine WP.block_append (WP.mono (copy_ok 8 hw₃ (o := brainpoolp512r1.sl RY) (a := brainpoolp512r1.sl ONEP) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest k₄
  refine WP.mono (copy_ok 8 hw₄ (o := brainpoolp512r1.sl RZ) (a := brainpoolp512r1.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨x₅, k₅, O₅⟩ => ?_
  have o : ∀ {m m' : Mem} {o i : Nat}, Outside base (brainpoolp512r1.sl o) (8 * 8) m m' →
      (brainpoolp512r1.sl i + 64 ≤ brainpoolp512r1.sl o ∨ brainpoolp512r1.sl o + 64 ≤ brainpoolp512r1.sl i) → brainpoolp512r1.sl i < 4096 →
      wordsVal m' base (brainpoolp512r1.sl i) 8 = wordsVal m base (brainpoolp512r1.sl i) 8 := fun O h hi =>
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
    (hz : sv base s ZERO = 0) (hone : sv base s ONEP = 2 ^ 512 % W.p)
    (ha : toM W.p (2 ^ 512) (sv base s AP) = Fin.ofNat W.p W.a)
    (hb : toM W.p (2 ^ 512) (sv base s B3P) = Fin.ofNat W.p (3 * W.b))
    (hap : sv base s AP < W.p) (hbp : sv base s B3P < W.p)
    (hx : sv base s RX < W.p) (hy : sv base s RY < W.p)
    (hon : Spec.Weierstrass.onCurve W
      (.affine (toM W.p (2 ^ 512) (sv base s RX)) (toM W.p (2 ^ 512) (sv base s RY))) = true) :
    WP isa brainpoolp512r1.mulBody s fun s' => Kc s s' ∧ Unch base mulBW s.mem s'.mem ∧
      (∀ x ∈ [brainpoolp512r1.sl RX, brainpoolp512r1.sl RY, brainpoolp512r1.sl RZ], wordsVal s'.mem base x 8 < W.p) ∧
      Rep W (tmv W 8 base s' (brainpoolp512r1.sl RX)) (tmv W 8 base s' (brainpoolp512r1.sl RY)) (tmv W 8 base s' (brainpoolp512r1.sl RZ))
        (Spec.Weierstrass.mul (sv base s K)
          (.affine (toM W.p (2 ^ 512) (sv base s RX)) (toM W.p (2 ^ 512) (sv base s RY)))) := by
  have hp0 : 0 < W.p := by decide
  have hone' : 2 ^ 512 % W.p < W.p := Nat.mod_lt _ hp0
  rw [Cfg.mulBody, show brainpoolp512r1.n = 8 from rfl]
  refine WP.seq (WP.mono (copies_ok hw) fun s₅ ⟨K₅, U₅, acc₅, pt₅, rx₅, ry₅, rz₅, e₅⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e₅
  obtain ⟨z₅, o₅, a₅, b₅, k₅⟩ := e₅
  have hw₅ := hw.of_kc K₅
  generalize hP : (Point.affine (toM W.p (2 ^ 512) (sv base s RX)) (toM W.p (2 ^ 512) (sv base s RY)) :
    Point W) = P at hon ⊢
  have tone : tmv W 8 base s₅ (brainpoolp512r1.sl ONEP) = 1 := by
    show toM _ _ (sv base s₅ ONEP) = 1; rw [o₅, hone]; exact toM_one unit
  have hG : Rep W (tmv W 8 base s₅ (brainpoolp512r1.sl ACC)) (tmv W 8 base s₅ (brainpoolp512r1.sl PT)) (tmv W 8 base s₅ (brainpoolp512r1.sl ONEP)) P := by
    rw [tone, ← hP]
    show Rep W (toM _ _ (sv base s₅ ACC)) (toM _ _ (sv base s₅ PT)) 1 _
    rw [acc₅, pt₅]; exact rep_affine' hL _ _
  have st := step_rep (L := brainpoolp512r1.mulLadder) (base := base) (s := s₅) (k := sv base s₅ K) hL hon
    (by show toM _ _ (sv base s₅ AP) = _; rw [a₅]; exact ha)
    (by show toM _ _ (sv base s₅ B3P) = _; rw [b₅]; exact hb) hG
  have hk : sv base s₅ K < 2 ^ 512 := wordsVal_lt _ _ _ 8
  refine WP.mono (ladder_ok (L := brainpoolp512r1.mulLadder) (C := W) (F := brainpoolp512r1Field) field_ok rfl rfl unit lay hw₅
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
  · show Rep W (toM W.p (2 ^ 512) (sv base s₅ RX)) (toM W.p (2 ^ 512) (sv base s₅ RY))
      (toM W.p (2 ^ 512) (sv base s₅ RZ)) _
    rw [rx₅, ry₅, rz₅, hz, hone, toM_zero, toM_one unit, show (brainpoolp512r1.mulLadder).nbits = 512 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hk, mul_zero_pt]
    exact rep_infinity' hL
  · rwa [show List.take 5 mulBW ++ ladWx brainpoolp512r1.mulLadder = mulBW from rfl] at hw
  · rw [Nat.shiftRight_zero, k₅] at ql; exact ql

end VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
