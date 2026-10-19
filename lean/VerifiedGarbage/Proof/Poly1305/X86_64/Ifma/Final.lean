module

public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Group
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the last group

The last group of eight blocks is added to `H`, and the quadwords folded in
three steps (`Impl/Poly1305/X86_64/Ifma.lean`), after which quadword 0 of `H`
is the accumulator, modulo `p`, with limbs at most `2⁴⁴`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v VKeep pi blk blk_mv blk_length group_bytes pi_0 pi_1 pi_2
  pi_3 pi_4 pi_5 pi_6 pi_7)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv absorbAll)

/-- What the blocks of the end keep: the general-purpose registers but
`rax`, `rcx` and `r9`, memory, MXCSR and the regions. -/
structure GK (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem GK.trans {s₁ s₂ s₃ : State} (h₁ : GK s₁ s₂) (h₂ : GK s₂ s₃) : GK s₁ s₃ :=
  ⟨fun r a c n => by rw [h₂.gpr r a c n, h₁.gpr r a c n], h₂.mem.trans h₁.mem, h₂.mxcsr.trans h₁.mxcsr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem GK.of_vec {s s' : State} (h : vec s s' = s') : GK s s' :=
  ⟨fun r _ _ _ => by rw [vec_gpr h], vec_mem h, by rw [← h]; rfl, vec_rd h, vec_wr h⟩

theorem GK.of_vk {s s' : State} (hk : VKeep s s') (hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) : GK s s' :=
  ⟨hg, hm, hk.mxcsr, hk.rd, hk.wr⟩

theorem GK.ctx {s s' : State} (h : GK s s') (hc : Ctx s) : Ctx s' :=
  Ctx.of_eq hc (h.gpr _ (by decide) (by decide) (by decide)) (h.gpr _ (by decide) (by decide) (by decide))
    h.rd h.wr

theorem GK.consts {s s' : State} (h : GK s s') (hc : Consts s) : Consts s' :=
  hc.of_mem (h.gpr _ (by decide) (by decide) (by decide)) h.mem

theorem one_val : Limbs44.val one = 1 := rfl

/-- The value of `Y` that a block setting it leaves. -/
theorem YSet.yv_val {sel : Nat → Bool} {s s' : State} (h : YSet sel s s') {k : Nat} (hk : k < 8) :
    yval s' k = if sel k then Limbs44.val (fun i => (s.gpr (lg i)).toNat) else 1 := by
  rw [show yval s' k = yv s' k 0 + 2 ^ 44 * yv s' k 1 + 2 ^ 88 * yv s' k 2 from rfl,
    h.y 0 (by decide) k hk, h.y 1 (by decide) k hk, h.y 2 (by decide) k hk]
  split
  · rfl
  · rfl

/-- A block setting `Y` (from limbs `g` in `rax`, `rcx`, `r9`), then `mul`. -/
theorem setMul_ok {seg : List Instr} {sel : Nat → Bool} {s : State}
    (hseg : WP isa (.block seg) s (YSet sel s)) (hc : Ctx s) (hm : Consts s)
    (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) (hg : ∀ i < 3, (s.gpr (lg i)).toNat ≤ 2 ^ 44) :
    WP isa (.block (seg ++ mul)) s fun s' => GK s s' ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
      ∀ k < 8, hval s' k ≡ hval s k * (if sel k then Limbs44.val (fun i => (s.gpr (lg i)).toNat) else 1)
        [MOD P] := by
  refine WP.block_append (WP.mono hseg fun s₁ Y => ?_)
  have eh := hv_of Y.h
  refine WP.mono (mulY_ok (Ctx.of_vec hc Y.vec) (by rw [mb_of_vec Y.vec, hm.mask])
    (fun k hk => by rw [eh k hk]; exact hb k hk) (Y.yb hg) (fun k hk => ⟨Y.s1 hg hk, Y.s2 hg hk⟩))
    fun s₂ ⟨v₂, E₂, b₂, _, _⟩ => ⟨GK.of_vec (vec_trans Y.vec v₂), b₂, fun k hk => ?_⟩
  have e := E₂ k hk
  rw [Y.yv_val hk] at e
  simp only [hval] at e ⊢
  rwa [eh k hk] at e

theorem fold1_eq : ∀ {s s' : State}, (∀ j < 4, ∀ i < 3, hv s' (2 * j) i = hv s (2 * j) i + hv s (2 * j + 1) i) →
    ∀ j < 4, hval s' (2 * j) = hval s (2 * j) + hval s (2 * j + 1) :=
  fun h j hj => hval_add (h j hj)

/-! ## The steps -/

theorem step1_eq : step1 = loadYG (fun i => at_ .rdi (80 + 8 * i)) ++
    ((bc3 ++ zeroOne ++ unpY ++ twenty) ++ mul ++ fold1) := by
  simp only [step1, loadY_eq, mR4_eq, unpY, fold1, List.append_assoc]
theorem step2_eq : step2 = splitG ++ ((bc3 ++ zeroOne ++ shY2 ++ twenty) ++ mul ++ fold2) := by
  simp only [step2, splitRg_eq, shY2, fold2, List.append_assoc]
theorem step3_eq : step3 = loadYG (fun i => at_ .rdi (56 + 8 * i)) ++
    ((bc3 ++ zeroOne ++ shY3 ++ twenty) ++ mul ++ (fold3 ++ (splitG ++ ((bc3 ++ twenty) ++ mul)))) := by
  simp only [step3, loadY_eq, mR2_eq, splitRg_eq, shY3, fold3, List.append_assoc]

/-- The registers and memory the end reads: the state at `rdi` (with `R²`
and `R⁴`), `R` in `r10` and `r11`, the mask in `r8`. -/
structure EndCtx (R : Nat) (s : State) : Prop where
  ctx : Ctx s
  m : MemR (s.gpr .rdi) R s.mem
  r : (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat = R
  r8 : s.gpr .r8 = 0xfffffffffff

theorem EndCtx.of_gk {R : Nat} {s s' : State} (h : EndCtx R s) (hg : GK s s') : EndCtx R s' := by
  have rdi := hg.gpr .rdi (by decide) (by decide) (by decide)
  refine ⟨hg.ctx h.ctx, by rw [rdi, hg.mem]; exact h.m, ?_, ?_⟩
  · rw [hg.gpr .r10 (by decide) (by decide) (by decide), hg.gpr .r11 (by decide) (by decide) (by decide), h.r]
  · rw [hg.gpr .r8 (by decide) (by decide) (by decide), h.r8]

theorem EndCtx.consts {R : Nat} {s : State} (h : EndCtx R s) : Consts s := h.m.consts rfl

/-- `loadYG` of `R^n`'s limbs at `rdi + d`. -/
theorem loadR_val {R n : Nat} {s : State} (d : Nat)
    (hb : ∀ i < 3, (s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64).toNat ≤ 2 ^ 44)
    (hv : Limbs44.val (fun i => (s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64).toNat) ≡ R ^ n [MOD P])
    {s' : State} (hg : ∀ i < 3, s'.gpr (lg i) = s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64) :
    (∀ i < 3, (s'.gpr (lg i)).toNat ≤ 2 ^ 44) ∧
      Limbs44.val (fun i => (s'.gpr (lg i)).toNat) ≡ R ^ n [MOD P] := by
  refine ⟨fun i hi => by rw [hg i hi]; exact hb i hi, ?_⟩
  have e : Limbs44.val (fun i => (s'.gpr (lg i)).toNat) =
      Limbs44.val (fun i => (s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64).toNat) := by
    simp only [Limbs44.val]; rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide)]
  rw [e]; exact hv

theorem region_ok {s : State} (hc : Ctx s) (d : Nat) (h₁ : 56 ≤ d) (h₂ : d + 24 ≤ 120) :
    ∀ i < 3, InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (d + 8 * i)) 8 := fun i hi =>
  hc.mb _ (by omega) (by omega)

/-- Step 1: quadword `2 j` becomes `H_(2j) R⁴ + H_(2j+1)`. -/
theorem step1_ok {R : Nat} {s : State} (hE : EndCtx R s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) :
    WP isa (.block step1) s fun s' => GK s s' ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 45) ∧
      ∀ j < 4, hval s' (2 * j) ≡ hval s (2 * j) * R ^ 4 + hval s (2 * j + 1) [MOD P] := by
  rw [step1_eq]
  refine WP.block_append (WP.mono (loadYG_ok s 80 (region_ok hE.ctx 80 (by decide) (by decide)))
    fun s₁ ⟨g₁, o₁, m₁, k₁⟩ => ?_)
  have G₁ : GK s s₁ := GK.of_vk k₁ o₁ m₁
  obtain ⟨lb, lv⟩ := loadR_val 80 hE.m.r4 hE.m.r4v g₁
  have E₁ := hE.of_gk G₁
  refine WP.block_append (WP.mono (setMul_ok (setY1_ok E₁.ctx E₁.consts) E₁.ctx E₁.consts
    (fun k hk => by rw [VKeep.hv k₁]; exact hb k hk) lb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.mono (fold1_ok b₂) fun s₃ ⟨F, f⟩ => ⟨G₁.trans (G₂.trans (GK.of_vec F.vec)), F.hb, fun j hj => ?_⟩
  have a := e₂ (2 * j) (by omega)
  have b := e₂ (2 * j + 1) (by omega)
  rw [ite_eq_left (by simp)] at a
  rw [ite_eq_right (by simp)] at b
  simp only [hval, VKeep.hv k₁] at a b ⊢
  rw [hval_add (f j hj)]
  exact a.add (b.trans (by rw [Nat.mul_one])) |>.trans (Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ lv))

/-- `splitG`'s limbs of `R`. -/
theorem splitR_val {R : Nat} {s : State} (hE : EndCtx R s) {s' : State}
    (h₁ : s'.gpr .rax = s.gpr .r10 &&& s.gpr .r8)
    (h₂ : s'.gpr .rcx = (s.gpr .r11 <<< 20 ||| s.gpr .r10 >>> 44) &&& s.gpr .r8)
    (h₃ : s'.gpr .r9 = s.gpr .r11 >>> 24) :
    (∀ i < 3, (s'.gpr (lg i)).toNat ≤ 2 ^ 44) ∧ Limbs44.val (fun i => (s'.gpr (lg i)).toNat) = R := by
  obtain ⟨v, b⟩ := split_limbs hE.r8 h₁ h₂ h₃
  exact ⟨b, by rw [v, hE.r]⟩

/-- Step 2: quadword `4 j` becomes `H_(4j) R + H_(4j+2)`. -/
theorem step2_ok {R : Nat} {s : State} (hE : EndCtx R s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) :
    WP isa (.block step2) s fun s' => GK s s' ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 45) ∧
      ∀ j < 2, hval s' (4 * j) ≡ hval s (4 * j) * R + hval s (4 * j + 2) [MOD P] := by
  rw [step2_eq]
  refine WP.block_append (WP.mono (splitG_ok s) fun s₁ ⟨a₁, c₁, n₁, o₁, m₁, k₁⟩ => ?_)
  have G₁ : GK s s₁ := GK.of_vk k₁ o₁ m₁
  obtain ⟨lb, lv⟩ := splitR_val hE a₁ c₁ n₁
  have E₁ := hE.of_gk G₁
  refine WP.block_append (WP.mono (setMul_ok (setY2_ok E₁.ctx E₁.consts) E₁.ctx E₁.consts
    (fun k hk => by rw [VKeep.hv k₁]; exact hb k hk) lb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.mono (fold2_ok b₂) fun s₃ ⟨F, f⟩ => ⟨G₁.trans (G₂.trans (GK.of_vec F.vec)), F.hb, fun j hj => ?_⟩
  have a := e₂ (4 * j) (by omega)
  have b := e₂ (4 * j + 2) (by omega)
  have c₀ : ((fun k => k / 2 % 2 == 0) (4 * j)) = true := by
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have c₂ : ¬((fun k => k / 2 % 2 == 0) (4 * j + 2)) = true := by
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
  rw [ite_eq_left c₀, lv] at a
  rw [ite_eq_right c₂] at b
  simp only [hval, VKeep.hv k₁] at a b ⊢
  rw [hval_add (f j hj)]
  exact a.add (b.trans (by rw [Nat.mul_one]))

/-- Step 3: quadword 0 becomes `(H₀ R² + H₄) R`. -/
theorem step3_ok {R : Nat} {s : State} (hE : EndCtx R s) (hb : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45) :
    WP isa (.block step3) s fun s' => GK s s' ∧ (∀ i < 3, hv s' 0 i ≤ 2 ^ 44) ∧
      hval s' 0 ≡ (hval s 0 * R ^ 2 + hval s 4) * R [MOD P] := by
  rw [step3_eq]
  refine WP.block_append (WP.mono (loadYG_ok s 56 (region_ok hE.ctx 56 (by decide) (by decide)))
    fun s₁ ⟨g₁, o₁, m₁, k₁⟩ => ?_)
  have G₁ : GK s s₁ := GK.of_vk k₁ o₁ m₁
  obtain ⟨lb, lv⟩ := loadR_val 56 hE.m.r2 hE.m.r2v g₁
  have E₁ := hE.of_gk G₁
  refine WP.block_append (WP.mono (setMul_ok (setY3_ok E₁.ctx E₁.consts) E₁.ctx E₁.consts
    (fun k hk => by rw [VKeep.hv k₁]; exact hb k hk) lb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.block_append (WP.mono (fold3_ok b₂) fun s₃ ⟨F, f⟩ => ?_)
  have G₃ : GK s s₃ := G₁.trans (G₂.trans (GK.of_vec F.vec))
  refine WP.block_append (WP.mono (splitG_ok s₃) fun s₄ ⟨a₄, c₄, n₄, o₄, m₄, k₄⟩ => ?_)
  have G₄ : GK s s₄ := G₃.trans (GK.of_vk k₄ o₄ m₄)
  obtain ⟨rb, rv⟩ := splitR_val (hE.of_gk G₃) a₄ c₄ n₄
  have E₄ := hE.of_gk G₄
  refine WP.mono (setMul_ok (setY0_ok s₄) E₄.ctx E₄.consts
    (fun k hk => by rw [VKeep.hv k₄]; exact F.hb k hk) rb) fun s₅ ⟨G₅, b₅, e₅⟩ =>
    ⟨G₄.trans G₅, b₅ 0 (by decide), ?_⟩
  have a := e₂ 0 (by decide)
  have b := e₂ 4 (by decide)
  rw [ite_eq_left (by decide)] at a
  replace a := a.trans (Nat.ModEq.mul_left _ lv)
  rw [ite_eq_right (by decide)] at b
  have c := e₅ 0 (by decide)
  rw [ite_eq_left rfl, rv] at c
  simp only [hval, VKeep.hv k₁, VKeep.hv k₄] at a b c ⊢
  rw [hval_add f] at c
  exact c.trans ((a.add (b.trans (by rw [Nat.mul_one]))).mul_right _)

/-! ## The last group -/

/-- The end's vector code: the last group added, the quadwords folded. -/
theorem last_ok {R X : Nat} {s : State} (hE : EndCtx R s) (hI : LaneInv R X s) :
    WP isa (.block (addGroup ++ step1 ++ step2 ++ step3)) s fun s' => GK s s' ∧
      (∀ i < 3, hv s' 0 i ≤ 2 ^ 44) ∧
      hval s' 0 ≡ absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128) [MOD P] := by
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (addGroup_ok ⟨hE.ctx, hE.consts, hI.hb⟩) fun s₁ A => ?_)
  have G₁ : GK s s₁ := GK.of_vec A.vec
  refine WP.block_append (WP.mono (step1_ok (hE.of_gk G₁) A.hb) fun s₂ ⟨G₂, b₂, e₂⟩ => ?_)
  refine WP.block_append (WP.mono (step2_ok (hE.of_gk (G₁.trans G₂)) b₂) fun s₃ ⟨G₃, b₃, e₃⟩ => ?_)
  refine WP.mono (step3_ok (hE.of_gk ((G₁.trans G₂).trans G₃)) b₃) fun s₄ ⟨G₄, b₄, e₄⟩ =>
    ⟨((G₁.trans G₂).trans G₃).trans G₄, b₄, ?_⟩
  -- The values of the quadwords after the last group is added.
  have U : ∀ k < 8, hval s₁ k = hval s k + mv (blk s (pi k)) := fun k hk => by
    simp only [hval]; rw [A.h k hk, ← blk_mv]
  have W := e₄.trans ((((e₃ 0 (by decide)).mul_right (R ^ 2)).add (e₃ 1 (by decide))).mul_right R)
  have B := fun j hj => e₂ j hj
  have W' := W.trans (((((((B 0 (by decide)).mul_right R).add (B 1 (by decide))).mul_right (R ^ 2)).add
    (((B 2 (by decide)).mul_right R).add (B 3 (by decide)))).mul_right R))
  simp only [Nat.mul_zero, Nat.zero_add, show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl,
    show 2 * 1 = 2 from rfl, U 0 (by decide), U 1 (by decide), U 2 (by decide), U 3 (by decide), U 4 (by decide), U 5 (by decide),
    U 6 (by decide), U 7 (by decide), pi_0, pi_1, pi_2, pi_3, pi_4, pi_5, pi_6, pi_7] at W'
  refine W'.trans ?_
  rw [group_bytes]
  have L := blk_length s
  have H := Poly1305.horner8_last (r := R) (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (Nat.ModEq.refl ((hval s 0 + mv (blk s 0)) * R ^ 8)) (Nat.ModEq.refl ((hval s 2 + mv (blk s 1)) * R ^ 7))
    (Nat.ModEq.refl ((hval s 4 + mv (blk s 2)) * R ^ 6)) (Nat.ModEq.refl ((hval s 6 + mv (blk s 3)) * R ^ 5))
    (Nat.ModEq.refl ((hval s 1 + mv (blk s 4)) * R ^ 4)) (Nat.ModEq.refl ((hval s 3 + mv (blk s 5)) * R ^ 3))
    (Nat.ModEq.refl ((hval s 5 + mv (blk s 6)) * R ^ 2)) (Nat.ModEq.refl ((hval s 7 + mv (blk s 7)) * R))
  refine Nat.ModEq.trans ?_ H
  unfold Nat.ModEq
  congr 1
  ring

end VG.Proof.Poly1305.X86_64.Ifma
