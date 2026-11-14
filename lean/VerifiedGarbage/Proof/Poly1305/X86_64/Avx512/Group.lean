module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Powers
import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.ModEq
public import VerifiedGarbage.Proof.Poly1305.Horner
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Poly1305.Horner8`, which only this module used -/

section

/-!
# Poly1305: Horner's rule in eight lanes

As `Horner.lean`, with eight lanes: lane `j` holds `V_j`, a group of blocks
`m₀ … m₇` makes it `(V_j + m_j) r⁸`, and the last group `(V_j + m_j) r^(8-j)`,
after which the lanes are summed. With `S = r⁸ V₀ + r⁷ V₁ + … + r V₇`, the
invariant is `S ≡ r⁸ a` for the accumulator `a` of the blocks so far.
-/

@[expose] public section

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

section
variable {r a : Nat} {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
include h0 h1 h2 h3 h4 h5 h6 h7

theorem absorbAll_eight :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * a + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
        r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 [MOD P] := by
  have l : (b0 ++ b1 ++ b2 ++ b3).length % 16 = 0 := by simp [h0, h1, h2, h3]
  rw [show b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 = (b0 ++ b1 ++ b2 ++ b3) ++ (b4 ++ b5 ++ b6 ++ b7) by
    simp only [List.append_assoc], absorbAll_append l]
  refine Nat.ModEq.trans (absorbAll_four h4 h5 h6 h7) ?_
  have hA : _ ≡ _ [MOD P] := absorbAll_four (r := r) (a := a) h0 h1 h2 h3
  refine ((((hA.mul_left (r ^ 4)).add_right _).add_right _).add_right _).add_right _ |>.trans ?_
  rw [show r ^ 4 * (r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 =
    r ^ 8 * a + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 by ring]

end

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes8 (r V0 V1 V2 V3 V4 V5 V6 V7 : Nat) : Nat :=
  r ^ 8 * V0 + r ^ 7 * V1 + r ^ 6 * V2 + r ^ 5 * V3 + r ^ 4 * V4 + r ^ 3 * V5 + r ^ 2 * V6 + r * V7

/-- The weighted values of a group's blocks. -/
abbrev msum8 (r : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : List Byte) : Nat :=
  r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 + r ^ 3 * mv b5 +
    r ^ 2 * mv b6 + r * mv b7

section
variable {r X V0 V1 V2 V3 V4 V5 V6 V7 W0 W1 W2 W3 W4 W5 W6 W7 : Nat}
  {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
  (hS : lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 ≡ r ^ 8 * X [MOD P])
include h0 h1 h2 h3 h4 h5 h6 h7 hS

omit hS in
theorem absorbAll_eight' :
    absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * X + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 [MOD P] := by
  refine (absorbAll_eight h0 h1 h2 h3 h4 h5 h6 h7).trans ?_
  rw [show r ^ 8 * X + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 = r ^ 8 * X + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [msum8]; ring]

/-- A group of eight blocks, each lane multiplied by `r⁸`. -/
theorem horner8_step (e0 : W0 ≡ (V0 + mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 8 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 8 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 8 [MOD P])
    (e4 : W4 ≡ (V4 + mv b4) * r ^ 8 [MOD P]) (e5 : W5 ≡ (V5 + mv b5) * r ^ 8 [MOD P])
    (e6 : W6 ≡ (V6 + mv b6) * r ^ 8 [MOD P]) (e7 : W7 ≡ (V7 + mv b7) * r ^ 8 [MOD P]) :
    lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := (absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7).mul_left (r ^ 8)
  have hL : lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * (lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7) [MOD P] := by
    refine ((((((((e0.mul_left _).add (e1.mul_left _)).add (e2.mul_left _)).add (e3.mul_left _)).add
      (e4.mul_left _)).add (e5.mul_left _)).add (e6.mul_left _)).add (e7.mul_left _)).trans ?_
    rw [show r ^ 8 * ((V0 + mv b0) * r ^ 8) + r ^ 7 * ((V1 + mv b1) * r ^ 8) +
        r ^ 6 * ((V2 + mv b2) * r ^ 8) + r ^ 5 * ((V3 + mv b3) * r ^ 8) + r ^ 4 * ((V4 + mv b4) * r ^ 8) +
        r ^ 3 * ((V5 + mv b5) * r ^ 8) + r ^ 2 * ((V6 + mv b6) * r ^ 8) + r * ((V7 + mv b7) * r ^ 8) =
        r ^ 8 * (lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7) by
      simp only [lanes8, msum8]; ring]
  exact hL.trans (((hS.add_right _).mul_left _).trans hA.symm)

/-- The last group, lane `j` multiplied by `r^(8-j)`, and the lanes summed. -/
theorem horner8_last (e0 : W0 ≡ (V0 + mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 7 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 6 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 5 [MOD P])
    (e4 : W4 ≡ (V4 + mv b4) * r ^ 4 [MOD P]) (e5 : W5 ≡ (V5 + mv b5) * r ^ 3 [MOD P])
    (e6 : W6 ≡ (V6 + mv b6) * r ^ 2 [MOD P]) (e7 : W7 ≡ (V7 + mv b7) * r [MOD P]) :
    W0 + W1 + W2 + W3 + W4 + W5 + W6 + W7 ≡
      absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7
  refine (((((((e0.add e1).add e2).add e3).add e4).add e5).add e6).add e7).trans ?_
  rw [show (V0 + mv b0) * r ^ 8 + (V1 + mv b1) * r ^ 7 + (V2 + mv b2) * r ^ 6 + (V3 + mv b3) * r ^ 5 +
      (V4 + mv b4) * r ^ 4 + (V5 + mv b5) * r ^ 3 + (V6 + mv b6) * r ^ 2 + (V7 + mv b7) * r =
      lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [lanes8, msum8]; ring]
  exact (hS.add_right _).trans hA.symm

end

end VG.Proof.Poly1305

end

end


/-!
# Poly1305 on x86-64 with AVX-512: groups of eight blocks

Each group of eight blocks is added to the quadwords of `H` (block `π k` to
quadword `k`) and multiplied by `r⁸` (Horner's rule in eight lanes,
`Horner8.lean`), whose limbs are in the state (`MemY`); the last group is
multiplied quadword by quadword by `r^(8 - π k)`, after which the sum of the
quadwords is the accumulator.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr ext5 val_congr)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes8 absorbAll)

/-- Block `j` of the group at `rsi`. -/
def blk (s : State) (j : Nat) : List Byte := bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * j)) 16

theorem blk_length (s : State) (j : Nat) : (blk s j).length = 16 := Poly1305.length_bytesAt _ _ _

theorem blk_mv (s : State) (k : Nat) : mv (blk s (pi k)) = blo s k + 2 ^ 64 * bhi s k + 2 ^ 128 := by
  rw [mv, Poly1305.leNum_append, blk, Poly1305.length_bytesAt, Poly1305.leNum_bytesAt_16]
  have e₁ : s.gpr .rsi + BitVec.ofNat 64 (16 * pi k) = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * pi k)) := by
    rw [show 16 * pi k = 8 * (2 * pi k) by omega_using []]
  have e₂ : s.gpr .rsi + BitVec.ofNat 64 (16 * pi k) + 8 =
      s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * pi k + 1)) := by
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      show 16 * pi k + 8 = 8 * (2 * pi k + 1) by omega_using []]
  rw [e₂, e₁]
  simp only [blo, bhi, envOf]
  rfl

/-- The group at `rsi`, block by block. -/
theorem group_bytes (s : State) :
    bytesAt s.mem (s.gpr .rsi) 128 =
      blk s 0 ++ blk s 1 ++ blk s 2 ++ blk s 3 ++ blk s 4 ++ blk s 5 ++ blk s 6 ++ blk s 7 := by
  have e : ∀ n, bytesAt s.mem (s.gpr .rsi) (n + 16) =
      bytesAt s.mem (s.gpr .rsi) n ++ bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 n) 16 :=
    fun n => Poly1305.bytesAt_add _ _ n 16
  rw [(e 112 : bytesAt s.mem (s.gpr .rsi) 128 = _), (e 96 : bytesAt s.mem (s.gpr .rsi) 112 = _),
    (e 80 : bytesAt s.mem (s.gpr .rsi) 96 = _), (e 64 : bytesAt s.mem (s.gpr .rsi) 80 = _),
    (e 48 : bytesAt s.mem (s.gpr .rsi) 64 = _), (e 32 : bytesAt s.mem (s.gpr .rsi) 48 = _),
    (e 16 : bytesAt s.mem (s.gpr .rsi) 32 = _)]
  simp only [blk]
  rw [show BitVec.ofNat 64 (16 * 0) = 0#64 from rfl, BitVec.add_zero]

/-- The value of quadword `k` of `H`. -/
def hval (s : State) (k : Nat) : Nat := Limbs26.val (hv s k)

/-- The lanes of `H` weighted by the powers of `R` of the last group, in the
order of their blocks (block `j` is in quadword `2 j` for `j < 4`, else
`2 (j - 4) + 1`). -/
def wsum (R : Nat) (s : State) : Nat :=
  lanes8 R (hval s 0) (hval s 2) (hval s 4) (hval s 6) (hval s 1) (hval s 3) (hval s 5) (hval s 7)

/-- What holds of the vector registers between groups: `Y` holds the powers
of `R`, and the quadwords of `H` (limbs below `2²⁷`) the accumulator `X`,
after Horner's rule in eight lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : YInv s R
  hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27
  acc : wsum R s ≡ R ^ 8 * X [MOD P]

theorem YInv.of_y {s s' : State} {R : Nat} (h : YInv s R)
    (hy : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) : YInv s' R := by
  have el : ∀ k < 8, yl s' k = yl s k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yl_ge _ _ h)
    fun i hi => by simp only [yl, hy i hi k hk]
  have eh : ∀ k < 8, yh s' k = yh s k := fun k hk => ext5 (fun _ h => yh_ge _ _ h) (fun _ h => yh_ge _ _ h)
    fun i hi => by simp only [yh, hy i hi k hk]
  exact ⟨fun k hk => by rw [el k hk]; exact h.lo k hk, fun k hk => by rw [eh k hk]; exact h.hi k hk,
    fun k hk => by rw [el k hk]; exact h.lob k hk, fun k hk => by rw [eh k hk]; exact h.hib k hk⟩

/-- The multiplier in the state (`mulM`'s) is `R⁸`. -/
structure MemY (R : Nat) (s : State) : Prop where
  m : MemM s
  val : Limbs26.val (mr s) ≡ R ^ 8 [MOD P]

theorem Ctx.of_vec {s s' : State} (h : Ctx s) (hv : vec s s' = s') : Ctx s' := by
  have g := vec_gpr hv
  have rd := vec_rd hv
  have wr := vec_wr hv
  exact ⟨fun i hi => by rw [rd, wr, g]; exact h.ld i hi, fun d h₁ h₂ => by rw [rd, wr, g]; exact h.mb d h₁ h₂⟩

/-- `addGroupM`, then `mulM` by the multiplier in the state: quadword `k`
becomes `(V_k + m_(π k)) · r`. -/
theorem addMulM_ok {s : State} (hc : Ctx s) (hM : MemM s) (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27) :
    WP isa (.block (addGroupM ++ mulM)) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) ∧ (∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * Limbs26.val (mr s) [MOD P] := by
  refine WP.block_append (WP.mono (addGroupM_ok ⟨hM.pad, hc, hb⟩) fun s₁ A => ?_)
  have hm : mr s₁ = mr s := by funext i; simp only [mr, envOf, vec_gpr A.vec, vec_mem A.vec]
  refine WP.mono (mulM_ok ⟨hc.of_vec A.vec, hM.of_mem (by rw [vec_gpr A.vec]) (vec_mem A.vec), A.hb⟩)
    fun s₂ M => ⟨vec_trans A.vec M.vec, fun i hi k hk => by rw [M.y i hi k hk, A.y i hi k hk], M.hb,
      fun k hk => ?_⟩
  simp only [hval]
  rw [val_congr (M.h k hk), blk_mv, ← A.h k hk, hm]
  exact Limbs26.mul_mod _ _

theorem pi_0 : pi 0 = 0 := rfl
theorem pi_1 : pi 1 = 4 := rfl
theorem pi_2 : pi 2 = 1 := rfl
theorem pi_3 : pi 3 = 5 := rfl
theorem pi_4 : pi 4 = 2 := rfl
theorem pi_5 : pi 5 = 6 := rfl
theorem pi_6 : pi 6 = 3 := rfl
theorem pi_7 : pi 7 = 7 := rfl

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hc : Ctx s) (hM : MemY R s) (hI : LaneInv R X s) :
    WP isa (.block (addGroupM ++ mulM)) s fun s' => vec s s' = s' ∧
      LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128)) s' := by
  refine WP.mono (addMulM_ok hc hM.m hI.hb) fun s' ⟨hv', hy, hb, he⟩ => ⟨hv', hI.y.of_y hy, hb, ?_⟩
  have e : ∀ k < 8, hval s' k ≡ (hval s k + mv (blk s (pi k))) * R ^ 8 [MOD P] := fun k hk =>
    (he k hk).trans (Nat.ModEq.mul_left _ hM.val)
  rw [group_bytes]
  have L := blk_length s
  exact Poly1305.horner8_step (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [pi_0] using e 0 (by decide)) (by simpa only [pi_2] using e 2 (by decide))
    (by simpa only [pi_4] using e 4 (by decide)) (by simpa only [pi_6] using e 6 (by decide))
    (by simpa only [pi_1] using e 1 (by decide)) (by simpa only [pi_3] using e 3 (by decide))
    (by simpa only [pi_5] using e 5 (by decide)) (by simpa only [pi_7] using e 7 (by decide))

/-! ## The last group -/

def shY : List Instr := (List.range 5).map fun i => srl (yreg i) (yreg i) 32

theorem last_eq : last = addGroup ++ (shY ++ mul) := rfl

def shS : Sym := (Sym.init.run false shY).get (by decide +kernel)
theorem shS_eq : Sym.init.run false shY = some shS := (Option.some_get _).symm
theorem shS_shape : ∀ i < 5, shS.reg (xi (yreg i)) = .shr (.reg (xi (yreg i))) 32 ∧
    shS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem shY_ok (s : State) :
    WP isa (.block shY) s fun s' => vec s s' = s' ∧ (∀ k < 8, ∀ i < 5, hv s' k i = hv s k i ∧
      yl s' k i = yh s k i) := by
  refine WP.mono (run_ok (by intro h; cases h) shS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv]; rw [h.reg _ k hk, (shS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl, yh]
    rw [h.natw _ hk, (shS_shape i hi).1]
    simp only [Q.natw, envOf_v]
    have := (qz s (yreg i) k).isLt
    omega_using []

/-- The sum of the quadwords, in the order of their blocks. -/
def bsum (s : State) : Nat :=
  hval s 0 + hval s 2 + hval s 4 + hval s 6 + hval s 1 + hval s 3 + hval s 5 + hval s 7

/-- The last group: quadword `k` multiplied by `r^(8 - π k)`, and the sum of
the quadwords is the accumulator. -/
theorem last_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : Ctx s) (hI : LaneInv R X s) :
    WP isa (.block last) s fun s' => vec s s' = s' ∧ (∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      bsum s' ≡ absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128) [MOD P] := by
  rw [last_eq]
  refine WP.block_append (WP.mono (addGroup_ok ⟨hr9, hc, hI.hb⟩) fun s₁ A => ?_)
  have Y₁ := hI.y.of_y A.y
  refine WP.block_append (WP.mono (shY_ok s₁) fun s₂ ⟨v₂, e₂⟩ => ?_)
  have hH : ∀ k < 8, hv s₂ k = hv s₁ k := fun k hk => ext5 (fun _ h => hv_ge _ _ h) (fun _ h => hv_ge _ _ h)
    fun i hi => (e₂ k hk i hi).1
  have hY : ∀ k < 8, yl s₂ k = yh s₁ k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yh_ge _ _ h)
    fun i hi => (e₂ k hk i hi).2
  refine WP.mono (mul_ok ⟨by rw [vec_gpr v₂, vec_gpr A.vec, hr8], fun k hk i hi => by
      rw [hH k hk]; exact A.hb k hk i hi, fun k hk i hi => by rw [hY k hk]; exact Y₁.hib k hk i hi⟩)
    fun s₃ M => ⟨vec_trans (vec_trans A.vec v₂) M.vec, M.hb, ?_⟩
  have e : ∀ k < 8, hval s₃ k ≡ (hval s k + mv (blk s (pi k))) * R ^ (8 - pi k) [MOD P] := by
    intro k hk
    simp only [hval]
    rw [val_congr (M.h k hk), hH k hk, hY k hk, blk_mv, ← A.h k hk]
    exact (Limbs26.mul_mod _ _).trans (Nat.ModEq.mul_left _ (Y₁.hi k hk))
  rw [group_bytes]
  have L := blk_length s
  exact Poly1305.horner8_last (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [pi_0] using e 0 (by decide)) (by simpa only [pi_2] using e 2 (by decide))
    (by simpa only [pi_4] using e 4 (by decide)) (by simpa only [pi_6] using e 6 (by decide))
    (by simpa only [pi_1] using e 1 (by decide)) (by simpa only [pi_3] using e 3 (by decide))
    (by simpa only [pi_5] using e 5 (by decide)) (by simpa only [pi_7, show 8 - 7 = 1 from rfl, pow_one] using e 7 (by decide))

end VG.Proof.Poly1305.X86_64.Avx512
