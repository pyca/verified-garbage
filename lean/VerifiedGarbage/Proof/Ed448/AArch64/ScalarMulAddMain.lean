import VerifiedGarbage.Proof.Ed448.AArch64.ScalarColumns
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarMain

/-!
# Ed448 scalar multiply-add on AArch64: the whole function

`vg_ed448_scalar_mul_add` copies `k`, `r` and `s` to the working space,
forms `r + k s` in sixteen words by product scanning, and reduces them with
the loop of `vg_ed448_scalar_reduce`, from a zero remainder. The working
space is written only where the callee-saved registers are saved, the
operands and the product, so the inputs are read unchanged and the saved
registers are restored.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_mul_add(out = x0, r = x1, k = x2, s = x3, scratch = x4)`. -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.gpr .x2, 57⟩, ⟨s.gpr .x3, 57⟩] ∧
    s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x4, 8192⟩] ∧
    (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x3, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  post s t := bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .x1) 57)
    (bytesAt s.mem (s.gpr .x2) 57) (bytesAt s.mem (s.gpr .x3) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4

/-- The loop over the words at `ACC`, with a zero remainder. -/
theorem accInit_ok (s : State) :
    WP isa (.block accInit) s fun t =>
      t.gpr .x1 = s.gpr .x2 + BitVec.ofNat 64 ACC ∧ rem t = 0 ∧ t.gpr .x3 = BitVec.ofNat 64 128 ∧
      Keeps [.x1, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [accInit, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show ACC < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      Ed25519.AArch64.read_x]
  · simp only [rem, rv, R, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem pow256_57 : (256 : Nat) ^ 57 = 2 ^ 456 :=
  calc (256 : Nat) ^ 57 = (2 ^ 8) ^ 57 := rfl
    _ = 2 ^ (8 * 57) := (Nat.pow_mul 2 8 57).symm
    _ = 2 ^ 456 := by rw [show 8 * 57 = 456 from rfl]

/-- The registers `vg_ed448_scalar_mul_add` changes before it restores the
callee-saved ones. -/
def mulAddClob : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

theorem clob_sub : ∀ r ∈ clob, r ∈ mulAddClob := by decide
theorem accInit_sub : ∀ r ∈ [Reg.x1, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11], r ∈ mulAddClob := by
  decide
theorem consts_sub : ∀ r ∈ constRegs, r ∈ mulAddClob := by decide
theorem colX_sub : ∀ r ∈ Reg.x26 :: colX, r ∈ mulAddClob := by decide
theorem operands_sub : ∀ r ∈ [Reg.x2, .x5], r ∈ mulAddClob := by decide

theorem decodeLE_lt456 (m : Mem) (p : Addr) : decodeLE (bytesAt m p 57) < 2 ^ 456 := by
  have h := decodeLE_lt' (bytesAt m p 57)
  rw [bytesAt_length, pow256_57] at h
  exact h

theorem scalarMulAdd_correct {s : State} (hs : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, dr, dk, ds⟩ := hs
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x4 = b := ⟨_, rfl⟩
  rw [hbase] at hw dr dk ds
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hwo : (⟨s.gpr .x0, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hin : ∀ r ∈ [Reg.x1, .x2, .x3], (⟨s.gpr r, 57⟩ : Region) ∈ s.rd ++ s.wr := by
    intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl <;> rw [hr] <;> simp
  rw [scalarMulAdd]
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok .x4 hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  have in₁ : ∀ r ∈ [Reg.x1, .x2, .x3], (⟨s₁.gpr r, 57⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [g₁, rd₁, wr₁]; exact hin
  refine WP.mono (operands_ok (s := s₁) (base := base) (by rw [g₁]; exact hbase) (wr₁ ▸ hws)
    (in₁ _ (by decide)) (in₁ _ (by decide)) (in₁ _ (by decide)) (by rw [g₁]; exact dr)
    (by rw [g₁]; exact dk) (by rw [g₁]; exact ds))
    fun s₂ ⟨vk₂, vr₂, vs₂, one₂, o₂, x2₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  have ek : decodeLE (bytesAt s₁.mem (s₁.gpr .x2) 57) = decodeLE (bytesAt s.mem (s.gpr .x2) 57) := by
    rw [g₁, bytesAt_outside o₁ (by decide) dk (by decide)]
  have er : decodeLE (bytesAt s₁.mem (s₁.gpr .x1) 57) = decodeLE (bytesAt s.mem (s.gpr .x1) 57) := by
    rw [g₁, bytesAt_outside o₁ (by decide) dr (by decide)]
  have es : decodeLE (bytesAt s₁.mem (s₁.gpr .x3) 57) = decodeLE (bytesAt s.mem (s.gpr .x3) 57) := by
    rw [g₁, bytesAt_outside o₁ (by decide) ds (by decide)]
  rw [ek] at vk₂; rw [er] at vr₂; rw [es] at vs₂
  rw [WP.block_append_iff]
  refine WP.mono (product_ok x2₂ (wr₂ ▸ wr₁ ▸ hws) one₂ (vk₂ ▸ decodeLE_lt456 _ _)
    (vr₂ ▸ decodeLE_lt456 _ _) (vs₂ ▸ decodeLE_lt456 _ _))
    fun s₃ ⟨v₃, g₃, z₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  rw [vk₂, vr₂, vs₂] at v₃
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₃) fun s₄ ⟨c₄, k₄⟩ => ?_
  refine WP.mono (accInit_ok s₄) fun s₅ ⟨x1₅, r₅, x3₅, k₅⟩ => ?_
  have c₅ : Consts s₅ := c₄.of_keeps k₅ (by decide)
  have x2₄ : s₄.gpr .x2 = base := (k₄.gpr _ (by decide)).trans ((g₃ _ (by decide)).trans x2₂)
  have m₅ : s₅.mem = s₃.mem := k₅.mem.trans k₄.mem
  have rdw₅ : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [k₅.rd, k₅.wr, k₄.rd, k₄.wr, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]
  apply WP.seq
  have hi : LoopInv 128 s₅ 16 s₅ := by
    refine ⟨by decide, by decide, x3₅, ?_, Keeps.refl _ _⟩
    rw [r₅]; rfl
  refine WP.mono (scalarLoop_ok s₅ c₅ (by decide) hi fun k hk => by
      rw [rdw₅, x1₅, x2₄, Offset.add_add]
      exact ⟨_, List.mem_append_right _ hws, contains_sc (by simp only [ACC]; omega)⟩)
    fun s₆ ⟨v₆, k₆⟩ => ?_
  have x2₆ : s₆.gpr .x2 = base := by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), x2₄]
  have g₆ : ∀ r, r ∉ mulAddClob → s₆.gpr r = s.gpr r := fun r hr' => by
    rw [k₆.gpr r fun h => hr' (clob_sub r h), k₅.gpr r fun h => hr' (accInit_sub r h),
      k₄.gpr r fun h => hr' (consts_sub r h), g₃ r fun h => hr' (colX_sub r h),
      g₂ r fun h => hr' (operands_sub r h), g₁]
  have x0₆ : s₆.gpr .x0 = s.gpr .x0 := g₆ _ (by decide)
  have wr₆ : s₆.wr = s.wr := by rw [k₆.wr, k₅.wr, k₄.wr, wr₃, wr₂, wr₁]
  have sv₆ : Saved base s.gpr s₆.mem := by
    intro p hp
    have hl := (saved_ok p hp).2
    rw [k₆.mem, m₅, Ed25519.AArch64.Outside.word o₃ (by simp only [ACC]; omega) (by omega),
      Ed25519.AArch64.Outside.word o₂ (by simp only [XK]; omega) (by omega)]
    exact sv₁ p hp
  refine WP.mono (finish_ok x2₆ (wr₆ ▸ hws) sv₆ x0₆ (wr₆ ▸ hwo)) fun t ⟨bt, rt, gt, spt⟩ => ?_
  refine ⟨⟨fun r hpres => ?_, spt.trans (k₆.sp.trans (k₅.sp.trans (k₄.sp.trans
    (sp₃.trans (sp₂.trans sp₁)))))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.x19, 0) (by decide)
    · exact rt (.x20, 8) (by decide)
    · exact rt (.x21, 16) (by decide)
    · exact rt (.x22, 24) (by decide)
    · exact rt (.x23, 32) (by decide)
    · exact rt (.x24, 40) (by decide)
    · exact rt (.x25, 48) (by decide)
    · exact rt (.x26, 56) (by decide)
    all_goals rw [gt _ (by decide), g₆ _ (by decide)]
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .x1) 57)
      (bytesAt s.mem (s.gpr .x2) 57) (bytesAt s.mem (s.gpr .x3) 57)
    rw [bt, v₆, x1₅, x2₄, m₅, show (128 : Nat) = 8 * 16 from rfl, decode_mv, v₃]
    rfl

end VG.Proof.Ed448.AArch64
