module

public import VerifiedGarbage.Proof.X25519.Arm.Field
public import VerifiedGarbage.Proof.X25519.Arm.Mul
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: `vg_x25519_umaal`'s multiplication, which builds in parallel with the ladder's
-- proofs and leaves the modules that import `Mul` (Ed25519's) alone.

/-!
# X25519 on 32-bit ARM: multiplication with `umaal`

`mulUAt acc o x y` packs the limbs of `[x]` and `[y]` into eight words each
(`uPack_ok`), computes their 16-word product at `acc` row by row, one `umaal`
a word (`uRow_ok`, the loop invariant `URowInv`: after `i` rows,
`acc[0, i + 8)` holds the words of `x_{<i} · y`), folds it into eight words
and a carry `c ≤ 38` as `lo + 38 hi` (`uFold_ok`), and stores at `o` the
limbs of those words' halves plus `38 c` (`pass` and `tail`), a number
congruent to the product with limbs below `2¹⁶`: `mulU_ok` is `mul_ok`'s
statement for `mulUAt`.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P)

/-! ## Numbers of 32-bit words -/

/-- The number with the words `f 0, …, f (n - 1)` in radix `2³²`. -/
def val32 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => val32 f n + 2 ^ (32 * n) * f n

theorem val32_succ (f : Nat → Nat) (n : Nat) : val32 f (n + 1) = val32 f n + 2 ^ (32 * n) * f n :=
  rfl

theorem val32_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → val32 f n = val32 g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val32_succ, val32_succ, val32_congr (fun k hk => h k (by omega_arith)), h n (by omega_arith)]

theorem val32_zero_fn : ∀ n, val32 (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [val32_succ, val32_zero_fn n]; rfl

theorem val32_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ 32) → val32 f n < 2 ^ (32 * n)
  | 0, _ => Nat.one_pos
  | n + 1, h => by
    have ih := val32_lt (n := n) fun k hk => h k (by omega_arith)
    rw [val32_succ, Nat.mul_succ, Nat.pow_add]
    have h1 : 2 ^ (32 * n) * f n + 2 ^ (32 * n) ≤ 2 ^ (32 * n) * 2 ^ 32 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (h n (by omega_arith))
    omega_arith

theorem val32_append (f : Nat → Nat) (m : Nat) :
    ∀ n, val32 f (m + n) = val32 f m + 2 ^ (32 * m) * val32 (fun k => f (m + k)) n
  | 0 => by simp [val32]
  | n + 1 => by
    rw [← Nat.add_assoc, val32_succ, val32_append f m n, val32_succ, Nat.mul_add (2 ^ (32 * m)),
      ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add 32 m n]
    omega_arith

/-- Sixteen-bit limbs, two to a word. -/
theorem val16_pack (l : Nat → Nat) :
    ∀ n, val16 l (2 * n) = val32 (fun k => l (2 * k) + 65536 * l (2 * k + 1)) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega_arith, val16_succ, val16_succ, val16_pack l n,
      val32_succ, show 16 * (2 * n + 1) = 32 * n + 16 by omega_arith, show 16 * (2 * n) = 32 * n by omega_arith,
      Nat.pow_add, Nat.mul_add, Nat.mul_assoc, show (2 : Nat) ^ 16 = 65536 from rfl]
    omega_arith

/-! ## A row of `umaal`s -/

/-- The carries of the sums `a b_j + t_j`, from none. -/
def mc (a : Nat) (b t : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (a * b j + t j + mc a b t j) / 2 ^ 32

/-- Word `j` of `a b + t`. -/
def mo (a : Nat) (b t : Nat → Nat) (j : Nat) : Nat := (a * b j + t j + mc a b t j) % 2 ^ 32

theorem mc_succ (a : Nat) (b t : Nat → Nat) (j : Nat) :
    mc a b t (j + 1) = (a * b j + t j + mc a b t j) / 2 ^ 32 := rfl

/-- A sum `n m + hi + lo` of words is below `2⁶⁴`. -/
theorem umaal_lt {n m h l : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32) (hh : h < 2 ^ 32) (hl : l < 2 ^ 32) :
    n * m + h + l < 2 ^ 64 := by
  have : n * m ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  omega_arith

theorem mc_lt {a : Nat} {b t : Nat → Nat} {n : Nat} (ha : a < 2 ^ 32) (hb : ∀ j < n, b j < 2 ^ 32)
    (ht : ∀ j < n, t j < 2 ^ 32) : ∀ j ≤ n, mc a b t j < 2 ^ 32
  | 0, _ => (by decide : (0 : Nat) < 2 ^ 32)
  | j + 1, hj => by
    have := mc_lt ha hb ht j (by omega_arith)
    have := umaal_lt ha (hb j (by omega_arith)) this (ht j (by omega_arith))
    rw [mc_succ, Nat.div_lt_iff_lt_mul (by decide)]
    omega_arith

theorem mc_val (a : Nat) (b t : Nat → Nat) :
    ∀ n, val32 (mo a b t) n + 2 ^ (32 * n) * mc a b t n = a * val32 b n + val32 t n
  | 0 => by simp [val32, mc]
  | n + 1 => by
    have ih := mc_val a b t n
    rw [val32_succ, val32_succ, val32_succ, mc_succ, Nat.mul_succ, Nat.pow_add, mo]
    have e : 2 ^ (32 * n) * ((a * b n + t n + mc a b t n) % 2 ^ 32) +
        2 ^ (32 * n) * 2 ^ 32 * ((a * b n + t n + mc a b t n) / 2 ^ 32) =
          2 ^ (32 * n) * (a * b n) + 2 ^ (32 * n) * t n + 2 ^ (32 * n) * mc a b t n := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div, Nat.mul_add, Nat.mul_add]
    rw [Nat.mul_add a, Nat.mul_left_comm a]
    omega_arith

/-- The words after row `i` of a product at `acc`, by the word `a`: those below
`i`, the row's words and its carry. -/
def uRowAcc (acc : Nat → Nat) (a : Nat) (b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 8 then mo a b (fun j => acc (i + j)) (k - i)
  else mc a b (fun j => acc (i + j)) 8

theorem uRow_val {acc x y : Nat → Nat} {i : Nat} (hv : val32 acc (i + 8) = val32 x i * val32 y 8) :
    val32 (uRowAcc acc (x i) y i) (i + 9) = val32 x (i + 1) * val32 y 8 := by
  have e1 : val32 (uRowAcc acc (x i) y i) i = val32 acc i :=
    val32_congr fun k hk => by simp [uRowAcc, hk]
  have e2 : val32 (fun k => uRowAcc acc (x i) y i (i + k)) 9 =
      val32 (mo (x i) y (fun j => acc (i + j))) 8 + 2 ^ 256 * mc (x i) y (fun j => acc (i + j)) 8 := by
    rw [val32_succ, val32_congr (g := mo (x i) y (fun j => acc (i + j))) fun k hk => by
      simp only [uRowAcc, show ¬ i + k < i by omega_arith, show i + k < i + 8 by omega_arith, ite_false, ite_true,
        Nat.add_sub_cancel_left]]
    simp only [uRowAcc, show ¬ i + 8 < i by omega_arith, Nat.lt_irrefl, ite_false]
  have hc := mc_val (x i) y (fun j => acc (i + j)) 8
  rw [show 32 * 8 = 256 from rfl] at hc
  rw [val32_append _ i 9, e1, e2, hc, val32_succ x i, Nat.add_mul, ← hv, val32_append acc i 8,
    Nat.mul_add, Nat.mul_assoc]
  omega_arith

/-! ## `umaal` -/

/-- `s'` is `s` with `lo` and `hi` set to the low and high words of `r`. -/
structure Upd2 (s s' : State) (lo hi : Reg) (r : Nat) : Prop where
  glo : (s'.gpr lo).toNat = r % 2 ^ 32
  ghi : (s'.gpr hi).toNat = r / 2 ^ 32
  other : ∀ q, q ≠ lo → q ≠ hi → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd2.rest {s s' : State} {lo hi : Reg} {r : Nat} (h : Upd2 s s' lo hi r) {ws : List Reg}
    (hl : lo ∈ ws) (hh : hi ∈ ws) : Rest ws s s' :=
  ⟨fun q hq => h.other q (fun e => hq (e ▸ hl)) (fun e => hq (e ▸ hh)), h.rd, h.wr, h.sp⟩

theorem wp_umaal {is : List Instr} {s : State} {Q : State → Prop} {lo hi n m : Reg} (hne : lo ≠ hi)
    (hr : (s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat < 2 ^ 64)
    (k : ∀ s', Upd2 s s' lo hi ((s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.umaal lo hi n m :: is)) s Q := by
  generalize hR : (s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat = R at hr k
  refine WP.cons (s' := (s.setReg lo (BitVec.ofNat 32 R)).setReg hi (BitVec.ofNat 32 (R / 2 ^ 32)))
    (by simp only [exec, hne, ↓reduceIte, hR]) (k _ ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩)
  · simp only [State.setReg, hne, ↓reduceIte, BitVec.toNat_ofNat]
  · simp only [State.setReg, ↓reduceIte, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by decide)]; exact hr)
  · intro q h1 h2; simp only [State.setReg, h1, h2, ↓reduceIte]

/-! ## Packing -/

section
variable {e : Nat} {b : BitVec 32}

theorem uPack_ok {d a : Nat} (hd : d + 32 ≤ 4096) (ha : a + 64 ≤ 4096) (hsep : a + 64 ≤ d ∨ d + 32 ≤ a)
    {s : State} (hc : CtxN e b s) (hl : Lim s.mem (State.addr b) a) :
    WP isa (.block (uPack d a)) s fun s' =>
      Rest [.r3, .r4] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 d, 32⟩] s.mem s'.mem ∧
      ∀ k < 8, wd s'.mem (State.addr b) (d + 4 * k) =
        limb s.mem (State.addr b) a (2 * k) + 65536 * limb s.mem (State.addr b) a (2 * k + 1) := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_arith
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => Rest [.r3, .r4] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 d, 4 * n⟩] s.mem s'.mem ∧
      ∀ k < n, wd s'.mem (State.addr b) (d + 4 * k) =
        limb s.mem (State.addr b) a (2 * k) + 65536 * limb s.mem (State.addr b) a (2 * k + 1))
    (fun k s' hk ⟨hr, hf, ho⟩ => ?_) 8 (Nat.le_refl _) s ⟨Rest.refl _ _, Frame.refl _ _, fun _ h =>
      absurd h (Nat.not_lt_zero _)⟩) fun s' ⟨hr, hf, ho⟩ => ⟨hr, hf, ho⟩
  have hc' : CtxN e b s' := hc.of_rest hr (by decide)
  have hrd : ∀ q, q + 4 ≤ 4096 → (q + 4 ≤ d ∨ d + 4 * k ≤ q) →
      wd s'.mem (State.addr b) q = wd s.mem (State.addr b) q := fun q hq hq' =>
    wd_frame hf fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ hq' (by omega_arith) (by omega_arith)
  simp only [uPackStep]
  refine ldr0_ok hc' (d := a + 8 * k) (by omega_arith) fun t1 v1 => ?_
  refine ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := a + 8 * k + 4)
    (by omega_arith) fun t2 v2 => ?_
  refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun t3 v3 => ?_
  have hc3 : CtxN e b t3 := hc'.of_rest ((v1.rest (ws := [.r3, .r4]) (by decide)).trans
    ((v2.rest (by decide)).trans (v3.rest (by decide)))) (by decide)
  refine str0_ok hc3 (d := d + 4 * k) (by omega_arith) fun t4 v4 => WP.block_nil ?_
  have e0 : (t1.gpr .r3).toNat = limb s.mem (State.addr b) a (2 * k) := by
    rw [v1.gpr]; show wd s'.mem _ _ = wd s.mem _ _
    rw [hrd _ (by omega_arith) (by omega_arith)]; congr 1; omega_arith
  have e1 : (t2.gpr .r4).toNat = limb s.mem (State.addr b) a (2 * k + 1) := by
    rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = wd s.mem _ _
    rw [hrd _ (by omega_arith) (by omega_arith)]; congr 1; omega_arith
  have l0 := hl (2 * k) (by omega_arith)
  have l1 := hl (2 * k + 1) (by omega_arith)
  have e3 : (t3.gpr .r3).toNat =
      limb s.mem (State.addr b) a (2 * k) + 65536 * limb s.mem (State.addr b) a (2 * k + 1) := by
    rw [v3.gpr]
    show (t2.gpr .r3 + t2.gpr .r4 <<< 16).toNat = _
    have es : (t2.gpr .r4 <<< 16).toNat = 65536 * limb s.mem (State.addr b) a (2 * k + 1) := by
      rw [toNat_shl, e1, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
    rw [v2.other .r3 (by decide), toNat_add_lt (by rw [es, e0]; omega_arith), es, e0]
  refine ⟨hr.trans ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
    (v4.rest _)))), ?_, fun j hj => ?_⟩
  · rw [v4.mem, v3.mem, v2.mem, v1.mem]
    refine (hf.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega_arith)
  · rw [v4.mem, v3.mem, v2.mem, v1.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact ho j hj
    · rw [wd_write_self, e3]

/-! ## The rows -/

/-- After `j` words of a row, from `s2`: the carry in `r5` and the row's words
of `a y + t` at `acc + 4 (i + j')`. -/
structure UStepInv (acc i : Nat) (b : BitVec 32) (s2 : State) (a : Nat) (y t : Nat → Nat) (j : Nat)
    (s : State) : Prop where
  rest : Rest [.r2, .r3, .r5] s2 s
  r5 : (s.gpr .r5).toNat = mc a y t j
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 (acc + 4 * i), 4 * j⟩] s2.mem s.mem
  outs : ∀ j' < j, wd s.mem (State.addr b) (acc + 4 * (i + j')) = mo a y t j'

theorem uRowSteps_ok {acc i : Nat} (hA : acc + 128 ≤ 4096) (hi : i < 8) {s2 : State} (hc : CtxN e b s2)
    (h7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i)) {a : Nat} (h1 : (s2.gpr .r1).toNat = a)
    (h5 : s2.gpr .r5 = 0) {y t : Nat → Nat}
    (hy : ∀ j < 8, wd s2.mem (State.addr b) (acc + 96 + 4 * j) = y j)
    (ht : ∀ j < 8, wd s2.mem (State.addr b) (acc + 4 * (i + j)) = t j) :
    WP isa (.block ((List.range 8).flatMap (uRowStep acc))) s2 (UStepInv acc i b s2 a y t 8) := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_arith
  refine wp_range_flatMap (M := isa) (UStepInv acc i b s2 a y t) (fun j s hj h => ?_) 8 (Nat.le_refl _) s2
    ⟨Rest.refl _ _, by rw [h5]; rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hc' : CtxN e b s := hc.of_rest h.rest (by decide)
  have hrd : ∀ q, q + 4 ≤ 4096 → (q + 4 ≤ acc + 4 * i ∨ acc + 4 * i + 4 * j ≤ q) →
      wd s.mem (State.addr b) q = wd s2.mem (State.addr b) q := fun q hq hq' =>
    wd_frame h.frame fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ hq' (by omega_arith) (by omega_arith)
  have e7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [h.rest.gpr _ (by decide), h7]
  simp only [uRowStep]
  refine ldr0_ok hc' (d := acc + 96 + 4 * j) (by omega_arith) fun t1 v1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (acc + 4 * (i + j))) (by omega_arith)
    (by rw [v1.other _ (by decide), e7, ea7 hfit (by omega_arith)]; congr 2; omega_arith)
    (by rw [v1.rd, v1.wr]; exact hc'.inR (by omega_arith)) fun t2 v2 => ?_
  have ey : (t2.gpr .r2).toNat = y j := by
    rw [v2.other _ (by decide), v1.gpr]; show wd s.mem _ _ = _
    rw [hrd _ (by omega_arith) (.inr (by omega_arith)), hy j hj]
  have et : (t2.gpr .r3).toNat = t j := by
    rw [v2.gpr, v1.mem]; show wd s.mem _ _ = _
    rw [hrd _ (by omega_arith) (.inr (by omega_arith)), ht j hj]
  have ea' : (t2.gpr .r1).toNat = a := by
    rw [v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h1]
  have ec : (t2.gpr .r5).toNat = mc a y t j := by
    rw [v2.other _ (by decide), v1.other _ (by decide), h.r5]
  have hb := umaal_lt (t2.gpr .r1).isLt (t2.gpr .r2).isLt (t2.gpr .r5).isLt (t2.gpr .r3).isLt
  refine wp_umaal (by decide) hb fun t3 v3 => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (acc + 4 * (i + j))) (by omega_arith)
    (by rw [v3.other _ (by decide) (by decide), v2.other _ (by decide), v1.other _ (by decide), e7,
      ea7 hfit (by omega_arith)]; congr 2; omega_arith)
    (by rw [v3.wr, v2.wr, v1.wr]; exact hc'.inW (by omega_arith)) fun t4 v4 => WP.block_nil ?_
  rw [ea', ey, ec, et] at v3
  have hm4 : t4.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (acc + 4 * (i + j))) (t3.gpr .r3) := by
    rw [v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans
    ((v3.rest (by decide) (by decide)).trans (v4.rest _)))), ?_, ?_, fun j' hj' => ?_⟩
  · rw [v4.gpr, v3.ghi, mc_succ, Nat.add_right_comm (a * y j)]
  · rw [hm4]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega_arith)
  · rw [hm4]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.outs j' hj'
    · rw [wd_write_self, v3.glo, mo, Nat.add_right_comm (a * y j')]

/-- The loop invariant of the rows of `mulUAt acc o x y` from `s0`, after `i`
rows, for the packed words `x` and `y`. -/
structure URowInv (e acc : Nat) (b : BitVec 32) (x y : Nat → Nat) (s0 : State) (i : Nat) (s : State) :
    Prop where
  ctx : CtxN e b s
  rest : Rest clob s0 s
  r6 : s.gpr .r6 = mask16
  r8 : s.gpr .r8 = 38
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (8 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] s0.mem s.mem
  px : ∀ k < 8, wd s.mem (State.addr b) (acc + 64 + 4 * k) = x k
  py : ∀ k < 8, wd s.mem (State.addr b) (acc + 96 + 4 * k) = y k
  val : val32 (accw acc s.mem (State.addr b)) (i + 8) = val32 x i * val32 y 8

theorem uRow_ok {acc : Nat} (hA : acc + 128 ≤ 4096) {x y : Nat → Nat} {s0 : State} {i : Nat} (hi : i < 8)
    {s : State} (h : URowInv e acc b x y s0 i s) :
    WP isa (.block (uRow acc)) s fun s' =>
      URowInv e acc b x y s0 (i + 1) s' ∧ s'.z = decide (8 - (i + 1) = 0) := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega_arith
  simp only [uRow, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (acc + 64 + 4 * i)) (by omega_arith)
    (by rw [h.r7, ea7 hfit (by omega_arith)]; congr 2; omega_arith) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : CtxN e b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  refine WP.append (uRowSteps_ok (a := x i) (y := y) (t := fun j => accw acc s.mem (State.addr b) (i + j))
    hA hi hc2 e7 (by rw [u2.other _ (by decide), u1.gpr]; exact h.px i hi) u2.gpr
    (fun j hj => by rw [hm2]; exact h.py j hj) (fun j hj => by rw [hm2]; rfl)) fun s3 hp => ?_
  have hc3 : CtxN e b s3 := hc2.of_rest hp.rest (by decide)
  have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (acc + 4 * (i + 8))) (by omega_arith)
    (by rw [e7', ea7 hfit (by omega_arith)]; congr 2; omega_arith) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
  refine WP.block_nil ?_
  have hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s6 :=
    (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
      ((u5.rest (by decide)).trans (u6.rest (by decide)))))
  have hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (acc + 4 * (i + 8))) (s3.gpr .r5) := by
    rw [u6.mem, u5.mem, u4.mem]
  have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (acc + 4 * i), 32⟩] s.mem s3.mem := by
    rw [← hm2]; exact hp.frame
  have hr9 : s6.gpr .r9 = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r9]
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [toNat_imm (by omega_arith), t1]; omega_arith), toNat_imm (by omega_arith),
      toNat_imm (by omega_arith), t1]
    omega_arith
  -- Words outside `[acc, acc + 4 (i + 9))` are as they were.
  have hout : ∀ q, q + 4 ≤ 4096 → (q + 4 ≤ acc + 4 * i ∨ acc + 4 * (i + 9) ≤ q) →
      wd s6.mem (State.addr b) q = wd s.mem (State.addr b) q := by
    intro q hq hq'
    rw [hm6, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact wd_frame hpf fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have hacc : ∀ k < i + 9, accw acc s6.mem (State.addr b) k =
      uRowAcc (accw acc s.mem (State.addr b)) (x i) y i k := by
    intro k hk
    rcases Nat.lt_or_ge k (i + 8) with hk' | hk'
    · rcases Nat.lt_or_ge k i with hki | hki
      · rw [accw, hout _ (by omega_arith) (.inl (by omega_arith))]
        simp only [uRowAcc, hki, ite_true]; rfl
      · rw [accw, hm6, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
          show acc + 4 * k = acc + 4 * (i + (k - i)) by omega_arith, hp.outs (k - i) (by omega_arith)]
        simp only [uRowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
    · rw [accw, show acc + 4 * k = acc + 4 * (i + 8) by omega_arith, hm6, wd_write_self, hp.r5]
      simp only [uRowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 8 by omega_arith, ite_false]
  refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
      (by decide), h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r6],
    by rw [hr6.gpr _ (by decide), h.r8], ?_, hr9, ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e7']
    show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add, Nat.mul_succ]
  · rw [hm6]
    refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [hout _ (by omega_arith) (.inr (by omega_arith))]; exact h.px k hk
  · rw [hout _ (by omega_arith) (.inr (by omega_arith))]; exact h.py k hk
  · rw [show i + 1 + 8 = i + 9 by omega_arith, val32_congr hacc]; exact uRow_val h.val
  · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega_arith)]

/-! ## The fold -/

/-- After `k` words of the fold from `s1`, of the low words `lo` and the high
words `hi`. -/
structure UFoldInv (acc : Nat) (b : BitVec 32) (s1 : State) (lo hi : Nat → Nat) (k : Nat) (s : State) :
    Prop where
  rest : Rest [.r2, .r3, .r5] s1 s
  r5 : (s.gpr .r5).toNat = mc 38 hi lo k
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 acc, 4 * k⟩] s1.mem s.mem
  outs : ∀ j < k, wd s.mem (State.addr b) (acc + 4 * j) = mo 38 hi lo j

/-- The high words of the product at `acc`. -/
abbrev uHi (acc : Nat) (m : Mem) (B : Addr) (k : Nat) : Nat := accw acc m B (8 + k)

theorem uFold_ok {acc : Nat} (hA : acc + 128 ≤ 4096) {s : State} (hc : CtxN e b s) (h8 : s.gpr .r8 = 38) :
    WP isa (.block (uFold acc)) s fun s' =>
      Rest [.r2, .r3, .r5, .r9] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 acc, 32⟩] s.mem s'.mem ∧
      s'.gpr .r5 = 0 ∧ mc 38 (uHi acc s.mem (State.addr b)) (accw acc s.mem (State.addr b)) 8 ≤ 38 ∧
      (s'.gpr .r9).toNat = 38 * mc 38 (uHi acc s.mem (State.addr b)) (accw acc s.mem (State.addr b)) 8 ∧
      ∀ k < 8, wd s'.mem (State.addr b) (acc + 4 * k) =
        mo 38 (uHi acc s.mem (State.addr b)) (accw acc s.mem (State.addr b)) k := by
  have t38 : (38 : BitVec 32).toNat = 38 := rfl
  -- The carry out is at most 38.
  have hcl : mc 38 (uHi acc s.mem (State.addr b)) (accw acc s.mem (State.addr b)) 8 ≤ 38 := by
    have hv := mc_val 38 (uHi acc s.mem (State.addr b)) (accw acc s.mem (State.addr b)) 8
    have h1 := val32_lt (f := uHi acc s.mem (State.addr b)) (n := 8) fun k _ => wd_lt _ _ _
    have h2 := val32_lt (f := accw acc s.mem (State.addr b)) (n := 8) fun k _ => wd_lt _ _ _
    rw [show 32 * 8 = 256 from rfl] at hv h1 h2
    omega_arith
  simp only [uFold, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 : CtxN e b s1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (wp_range_flatMap (M := isa)
    (UFoldInv acc b s1 (accw acc s.mem (State.addr b)) (uHi acc s.mem (State.addr b)))
    (fun k s' hk h => ?_) 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, by rw [u1.gpr]; rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 h2 => ?_
  · have hc' : CtxN e b s' := hc1.of_rest h.rest (by decide)
    have hrd : ∀ q, q + 4 ≤ 4096 → acc + 4 * k ≤ q →
        wd s'.mem (State.addr b) q = wd s.mem (State.addr b) q := fun q hq hq' => by
      rw [wd_frame h.frame fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ (.inr hq') (by omega_arith) (by omega_arith), u1.mem]
    simp only [uFoldStep]
    refine ldr0_ok hc' (d := acc + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := acc + 32 + 4 * k)
      (by omega_arith) fun t2 v2 => ?_
    have el : (t2.gpr .r3).toNat = accw acc s.mem (State.addr b) k := by
      rw [v2.other _ (by decide), v1.gpr]; show wd s'.mem _ _ = _
      rw [hrd _ (by omega_arith) (by omega_arith)]; rfl
    have eh : (t2.gpr .r2).toNat = uHi acc s.mem (State.addr b) k := by
      rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = _
      rw [hrd _ (by omega_arith) (by omega_arith)]; unfold uHi accw; congr 1; omega_arith
    have e8 : (t2.gpr .r8).toNat = 38 := by
      rw [v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), u1.other _ (by decide), h8,
        t38]
    have ec : (t2.gpr .r5).toNat = mc 38 (uHi acc s.mem (State.addr b)) (accw acc s.mem (State.addr b)) k := by
      rw [v2.other _ (by decide), v1.other _ (by decide), h.r5]
    have hb := umaal_lt (t2.gpr .r2).isLt (t2.gpr .r8).isLt (t2.gpr .r5).isLt (t2.gpr .r3).isLt
    refine wp_umaal (by decide) hb fun t3 v3 => ?_
    have hc3 : CtxN e b t3 := hc'.of_rest ((v1.rest (ws := [.r2, .r3, .r5]) (by decide)).trans
      ((v2.rest (by decide)).trans (v3.rest (by decide) (by decide)))) (by decide)
    refine str0_ok hc3 (d := acc + 4 * k) (by omega_arith) fun t4 v4 => WP.block_nil ?_
    rw [eh, e8, ec, el, Nat.mul_comm _ 38] at v3
    have hm4 : t4.mem = s'.mem.writeW (State.addr b + BitVec.ofNat 64 (acc + 4 * k)) (t3.gpr .r3) := by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]
    refine ⟨h.rest.trans ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans
      ((v3.rest (by decide) (by decide)).trans (v4.rest _)))), ?_, ?_, fun j hj => ?_⟩
    · rw [v4.gpr, v3.ghi, mc_succ, Nat.add_right_comm (38 * _)]
    · rw [hm4]
      refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr']
      exact Region.sub_prefix (by omega_arith)
    · rw [hm4]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.outs j hj
      · rw [wd_write_self, v3.glo, mo, Nat.add_right_comm (38 * _)]
  · refine wp_mul fun s3 u3 => wp_mov (op2_imm (by decide)) fun s4 u4 => WP.block_nil ⟨?_, ?_, u4.gpr, hcl, ?_, ?_⟩
    · exact (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
        (u4.rest (by decide))))
    · rw [u4.mem, u3.mem, ← u1.mem]; exact h2.frame
    · have e8 : s2.gpr .r8 = 38 := by rw [h2.rest.gpr _ (by decide), u1.other _ (by decide), h8]
      rw [u4.other _ (by decide), u3.gpr, e8, toNat_mul_lt (by rw [h2.r5, t38]; omega_arith), h2.r5, t38,
        Nat.mul_comm]
    · intro k hk; rw [u4.mem, u3.mem]; exact h2.outs k hk

/-! ## The limbs of the result -/

/-- Half `k % 2` of word `k / 2` of `w`. -/
def uH (w : Nat → Nat) (k : Nat) : Nat := if k % 2 = 0 then w (k / 2) % 65536 else w (k / 2) / 65536

/-- The sums `pass` carries: the halves of `w`, plus `d` in limb 0. -/
def uC (w : Nat → Nat) (d k : Nat) : Nat := if k = 0 then uH w 0 + d else uH w k

theorem uH_lt {w : Nat → Nat} (hw : ∀ k < 8, w k < 2 ^ 32) {k : Nat} (hk : k < 16) : uH w k < 65536 := by
  unfold uH; split
  · exact Nat.mod_lt _ (by decide)
  · rw [Nat.div_lt_iff_lt_mul (by decide)]; exact hw _ (by omega_arith)

theorem val16_uC (w : Nat → Nat) (d : Nat) : val16 (uC w d) 16 = val32 w 8 + d := by
  rw [show uC w d = fun k => if k = 0 then uH w 0 + d else uH w k from rfl, val16_add_head _ _ (by decide),
    show (16 : Nat) = 2 * 8 from rfl, val16_pack]
  congr 1
  refine val32_congr fun k _ => ?_
  simp only [uH, show 2 * k % 2 = 0 by omega_arith, show (2 * k + 1) % 2 ≠ 0 by omega_arith, ite_true, ite_false,
    show 2 * k / 2 = k by omega_arith, show (2 * k + 1) / 2 = k by omega_arith]
  exact Nat.mod_add_div _ _

/-! ## The multiplication -/

/-- Limbs `2k` and `2k + 1` of the element at `a`, as a word. -/
def pk (m : Mem) (B : Addr) (a k : Nat) : Nat := limb m B a (2 * k) + 65536 * limb m B a (2 * k + 1)

theorem V_pk (m : Mem) (B : Addr) (a : Nat) : V m B a = val32 (pk m B a) 8 := val16_pack _ 8

theorem mulUPre_ok {acc : Nat} (hA : acc + 128 ≤ 4096) {x y : Nat} (hx : x + 64 ≤ acc) (hy : y + 64 ≤ acc)
    {s : State} (hc : CtxN e b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (.block (prologue ++ zeroAcc acc ++ uPack (acc + 64) x ++ uPack (acc + 96) y ++
      ([.mov .r7 (.reg .r0), .mov .r9 (.imm 8)] : List Instr))) s
      (URowInv e acc b (pk s.mem (State.addr b) x) (pk s.mem (State.addr b) y) s 0) := by
  simp only [List.append_assoc]
  refine WP.append prologue_ok fun s1 ⟨h6, h8, _, hr1, hm1⟩ => ?_
  have hc1 : CtxN e b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (zeroAcc_ok hA hc1) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : CtxN e b s2 := hc1.of_rest hr2 (by decide)
  -- A word outside a region a frame changes.
  have keep : ∀ {m m' : Mem} {d n q : Nat}, Frame [⟨State.addr b + BitVec.ofNat 64 d, n⟩] m m' →
      d + n ≤ 4096 → q + 4 ≤ 4096 → (q + 4 ≤ d ∨ d + n ≤ q) →
      wd m' (State.addr b) q = wd m (State.addr b) q := fun hf hd hq hq' =>
    wd_frame hf fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ hq' (by omega_arith) (by omega_arith)
  have lx2 : ∀ k < 16, limb s2.mem (State.addr b) x k = limb s.mem (State.addr b) x k := fun k hk => by
    rw [limb, keep hf2 (by omega_arith) (by omega_arith) (.inl (by omega_arith)), hm1]; rfl
  refine WP.append (uPack_ok (d := acc + 64) (a := x) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) hc2
    fun k hk => by rw [lx2 k hk]; exact hlx k hk) fun s3 ⟨hr3, hf3, hp3⟩ => ?_
  have hc3 : CtxN e b s3 := hc2.of_rest hr3 (by decide)
  have ly3 : ∀ k < 16, limb s3.mem (State.addr b) y k = limb s.mem (State.addr b) y k := fun k hk => by
    rw [limb, keep hf3 (by omega_arith) (by omega_arith) (.inl (by omega_arith)),
      keep hf2 (by omega_arith) (by omega_arith) (.inl (by omega_arith)), hm1]; rfl
  refine WP.append (uPack_ok (d := acc + 96) (a := y) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) hc3
    fun k hk => by rw [ly3 k hk]; exact hly k hk) fun s4 ⟨hr4, hf4, hp4⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => wp_mov (op2_imm (by decide)) fun s6 u6 => WP.block_nil ?_
  have hr : Rest clob s s6 :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr4.mono (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s4.mem := by rw [u6.mem, u5.mem]
  have hc4 : CtxN e b s4 := hc3.of_rest hr4 (by decide)
  refine ⟨hc.of_rest hr (by decide), hr, by rw [u6.other _ (by decide),
      u5.other _ (by decide), hr4.gpr _ (by decide), hr3.gpr _ (by decide), hr2.gpr _ (by decide), h6],
    by rw [u6.other _ (by decide), u5.other _ (by decide), hr4.gpr _ (by decide), hr3.gpr _ (by decide),
      hr2.gpr _ (by decide), h8], ?_, u6.gpr, ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, hc4.r0]; exact (BitVec.add_zero b).symm
  · have lift : ∀ {m m' : Mem} {d n : Nat}, Frame [⟨State.addr b + BitVec.ofNat 64 d, n⟩] m m' →
        acc ≤ d → d + n ≤ acc + 128 → Frame [⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m' :=
      fun hf h1 h2 => hf.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr']; exact Offset.sub _ h1 h2⟩
    rw [hm6, ← hm1]
    exact ((lift hf2 (Nat.le_refl _) (by omega_arith)).trans (lift hf3 (by omega_arith) (by omega_arith))).trans
      (lift hf4 (by omega_arith) (by omega_arith))
  · rw [hm6, keep hf4 (by omega_arith) (by omega_arith) (.inl (by omega_arith)), hp3 k hk, pk, lx2 _ (by omega_arith),
      lx2 _ (by omega_arith)]
  · rw [hm6, hp4 k hk, pk, ly3 _ (by omega_arith), ly3 _ (by omega_arith)]
  · rw [val32_congr (g := fun _ => 0) fun k hk => ?_, val32_zero_fn]
    · exact (Nat.zero_mul _).symm
    · rw [accw, hm6, keep hf4 (by omega_arith) (by omega_arith) (.inl (by omega_arith)),
        keep hf3 (by omega_arith) (by omega_arith) (.inl (by omega_arith))]
      exact hz k (by omega_arith)

/-- `mul_ok` for `mulUAt`. -/
theorem mulU_ok {acc : Nat} (hA : acc + 128 ≤ 4096) {o x y : Nat} (ho : o + 64 ≤ acc) (hx : x + 64 ≤ acc)
    (hy : y + 64 ≤ acc) {s : State} (hc : CtxN e b s) (hlx : Lim s.mem (State.addr b) x)
    (hly : Lim s.mem (State.addr b) y) :
    WP isa (mulUAt acc o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  unfold mulUAt
  refine WP.seq (WP.mono (mulUPre_ok hA hx hy hc hlx hly) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := URowInv e acc b (pk s.mem (State.addr b) x) (pk s.mem (State.addr b) y) s 8)
    (WP.loop (M := isa) (fun n s' => ∃ i, n = 8 - i ∧ i < 8 ∧
      URowInv e acc b (pk s.mem (State.addr b) x) (pk s.mem (State.addr b) y) s i s') ?_ 8 s1
      ⟨0, rfl, by decide, h1⟩) fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (uRow_ok hA hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h8 : i + 1 = 8
    · refine .inl ⟨by rw [eval_ne, hz]; simp [h8], ?_⟩
      rw [h8] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_arith, 8 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hr'⟩
  · rw [List.append_assoc]
    refine WP.append (uFold_ok hA h2.ctx h2.r8) fun s3 ⟨hr3, hf3, h53, hcl, h93, hw3⟩ => ?_
    have hc3 : CtxN e b s3 := h2.ctx.of_rest hr3 (by decide)
    -- The folded words, and their carry.
    generalize hlo : accw acc s2.mem (State.addr b) = lo at hcl h93 hw3
    generalize hhi : uHi acc s2.mem (State.addr b) = hi at hcl h93 hw3
    have hwl : ∀ k < 8, mo 38 hi lo k < 2 ^ 32 := fun k _ => Nat.mod_lt _ (by decide)
    have hwv := val32_lt hwl
    rw [show 32 * 8 = 256 from rfl] at hwv
    refine WP.mono (passTail'_ok (c := uC (mo 38 hi lo) (38 * mc 38 hi lo 8)) (by omega_arith)
      (fun k hk => by
        have := uH_lt hwl hk; have := uH_lt hwl (k := 0) (by decide); unfold uC; split
        · omega_arith
        · omega_arith)
      (by rw [val16_uC]; omega_arith) hc3
      (by rw [hr3.gpr _ (by decide), h2.r6]) (by rw [hr3.gpr _ (by decide), h2.r8]) h53 ?_)
      fun s4 ⟨hr4, hf4, hl4, hv4⟩ => ⟨h2.rest.trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
        ?_, hl4, ?_⟩
    · -- The limbs `pass` carries.
      intro k hk s' hp
      have hc' : CtxN e b s' := hc3.of_rest hp.rest (by decide)
      have ew : wd s'.mem (State.addr b) (acc + 4 * (k / 2)) = mo 38 hi lo (k / 2) := by
        rw [wd_pass hc3 hp.frame (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        exact hw3 _ (by omega_arith)
      have e6 : s'.gpr .r6 = mask16 := by rw [hp.rest.gpr _ (by decide), hr3.gpr _ (by decide), h2.r6]
      have e9 : (s'.gpr .r9).toNat = 38 * mc 38 hi lo 8 := by rw [hp.rest.gpr _ (by decide), h93]
      have hwk := hwl (k / 2) (by omega_arith)
      by_cases hk0 : k = 0
      · subst hk0
        simp only [uHalf, Nat.zero_mod, Nat.zero_div, ite_true, List.cons_append, List.nil_append]
        refine ldr0_ok hc' (by omega_arith) fun t1 v1 => wp_dp (op2_reg _ _) fun t2 v2 =>
          wp_dp (op2_reg _ _) fun t3 v3 => WP.block_nil ⟨?_, (v1.rest (by decide)).trans ((v2.rest (by decide)).trans
            (v3.rest (by decide))), by rw [v3.mem, v2.mem, v1.mem]⟩
        have e2 : (t2.gpr .r3).toNat = mo 38 hi lo 0 % 65536 := by
          rw [v2.gpr, v1.other .r6 (by decide), e6]
          show (t1.gpr .r3 &&& mask16).toNat = _
          rw [toNat_and_mask16, v1.gpr]; unfold wd at ew; rw [ew]
        have e9' : (t2.gpr .r9).toNat = 38 * mc 38 hi lo 8 := by
          rw [v2.other _ (by decide), v1.other _ (by decide), e9]
        rw [v3.gpr]
        show (t2.gpr .r3 + t2.gpr .r9).toNat = _
        rw [toNat_add_lt (by rw [e2, e9']; have := Nat.mod_lt (mo 38 hi lo 0) (show 0 < 65536 by decide); omega_arith),
          e2, e9']
        simp [uC, uH]
      · by_cases hk2 : k % 2 = 0
        · simp only [uHalf, hk2, hk0, ite_true, ite_false, List.append_nil]
          refine ldr0_ok hc' (by omega_arith) fun t1 v1 => wp_dp (op2_reg _ _) fun t2 v2 =>
            WP.block_nil ⟨?_, (v1.rest (by decide)).trans (v2.rest (by decide)), by rw [v2.mem, v1.mem]⟩
          rw [v2.gpr, v1.other .r6 (by decide), e6]
          show (t1.gpr .r3 &&& mask16).toNat = _
          rw [toNat_and_mask16, v1.gpr]; unfold wd at ew; rw [ew]
          simp only [uC, uH, hk0, hk2, ite_true, ite_false]
        · simp only [uHalf, hk2, hk0, ite_false, List.append_nil]
          refine ldr0_ok hc' (by omega_arith) fun t1 v1 => wp_mov (op2_lsr (by decide)) fun t2 v2 =>
            WP.block_nil ⟨?_, (v1.rest (by decide)).trans (v2.rest (by decide)), by rw [v2.mem, v1.mem]⟩
          rw [v2.gpr, toNat_shr, v1.gpr]; unfold wd at ew; rw [ew]
          simp only [uC, uH, hk0, hk2, ite_false]
    · -- The frame.
      have hlift : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩]
          s.mem s3.mem :=
        (h2.frame.trans (hf3.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
          rw [List.mem_singleton.mp hr']; exact Region.sub_prefix (by omega_arith)⟩)).sub fun r hr' => by
          rw [List.mem_singleton.mp hr']; exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
            Region.sub_prefix (Nat.le_refl _)⟩
      exact hlift.trans (hf4.sub fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact ⟨_, List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩)
    · -- The value.
      have hmv := mc_val 38 hi lo 8
      rw [show 32 * 8 = 256 from rfl] at hmv
      have hT : val32 (accw acc s2.mem (State.addr b)) 16 = val32 lo 8 + 2 ^ 256 * val32 hi 8 := by
        rw [show (16 : Nat) = 8 + 8 from rfl, val32_append, ← hlo, ← hhi]
      have hv2 := h2.val
      rw [show 8 + 8 = 16 from rfl, hT] at hv2
      rw [hv4, val16_uC, ← fold256, hmv, Nat.add_comm (38 * _), ← fold256, hv2, V_pk, V_pk]

end

end VG.Proof.X25519.Arm
