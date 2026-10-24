module

public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-!
# SM4-GCM on PPC64LE: the entry of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/OneEntry.lean`): `oneEntry off` loads the working
space `W`, the stack argument at `sp + off`, saves our caller's registers
there and keeps the arguments in nonvolatile registers, the tag's address
(`r10`) in `r20` (`one1_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Proof.AesGcm.PPC64LE (Keeps Entered SavedAt savedR save_ok SavedAt.congr)

/-- After the entry of `seal` or `open`, from `s₀`. -/
structure SO1 (W : Addr) (s₀ s₁ : State) : Prop where
  en : Entered s₀ W s₁
  r31 : s₁.gpr .r31 = W
  r30 : s₁.gpr .r30 = W + BitVec.ofNat 64 16
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r24 : s₁.gpr .r24 = s₀.gpr .r4
  r25 : s₁.gpr .r25 = s₀.gpr .r5
  r18 : s₁.gpr .r18 = s₀.gpr .r5
  r21 : s₁.gpr .r21 = s₀.gpr .r6
  r22 : s₁.gpr .r22 = s₀.gpr .r7
  r27 : s₁.gpr .r27 = s₀.gpr .r8
  r23 : s₁.gpr .r23 = s₀.gpr .r9
  r20 : s₁.gpr .r20 = s₀.gpr .r10

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `r12`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 96 ∨ off = 104)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 off]) s₀ fun sA =>
      sA.gpr .r12 = W ∧ (∀ r, r ≠ .r12 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  have ho4 : off % 4 = 0 := by omega
  have ho15 : off < 2 ^ 15 := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.write, Size.bytes,
    hWi, ho4, ho15, Proof.Gcm.PPC64LE.read_8, hWv, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow, ↓reduceIte,
    and_self, implies_true, BitVec.setWidth_eq, BitVec.add_zero]
  exact ⟨trivial, fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem one1_wp {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 96 ∨ off = 104)
    (hW : Covers [⟨W, 2560⟩] s₀.wr) (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block (oneEntry off)) s₀ (SO1 W s₀) := by
  simp only [oneEntry]
  refine WP.block_append (WP.block_append ?_)
  have hA := oneA_ok hoff hWi hWv
  refine WP.mono hA fun sA ⟨a12, gA, kA⟩ => ?_
  refine WP.mono (save_ok (b := .r12) (by decide) (by rw [a12, kA.wr]; exact hW))
    fun s₂ ⟨hg, h31, hk, hsv, hf⟩ => ?_
  rw [a12] at h31 hsv hf
  have e : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r31 → s₂.gpr r = s₀.gpr r := fun r a b c => by rw [hg r a c, gA r b]
  have e3 := e .r3 (by decide) (by decide) (by decide)
  have e4 := e .r4 (by decide) (by decide) (by decide)
  have e5 := e .r5 (by decide) (by decide) (by decide)
  have e6 := e .r6 (by decide) (by decide) (by decide)
  have e7 := e .r7 (by decide) (by decide) (by decide)
  have e8 := e .r8 (by decide) (by decide) (by decide)
  have e9 := e .r9 (by decide) (by decide) (by decide)
  have e10 := e .r10 (by decide) (by decide) (by decide)
  have hB : WP isa (.block ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5,
      mov .r18 .r5, mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10] : List Instr)) s₂
      fun s₁ =>
      s₁.gpr .r31 = W ∧ s₁.gpr .r30 = W + BitVec.ofNat 64 16 ∧ s₁.gpr .r29 = s₀.gpr .r3 ∧
      s₁.gpr .r24 = s₀.gpr .r4 ∧ s₁.gpr .r25 = s₀.gpr .r5 ∧
      s₁.gpr .r18 = s₀.gpr .r5 ∧ s₁.gpr .r21 = s₀.gpr .r6 ∧ s₁.gpr .r22 = s₀.gpr .r7 ∧
      s₁.gpr .r27 = s₀.gpr .r8 ∧ s₁.gpr .r23 = s₀.gpr .r9 ∧ s₁.gpr .r20 = s₀.gpr .r10 ∧
      (∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₁.gpr r = s₂.gpr r) ∧ Keeps s₂ s₁ := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.write, mov, BitVec.or_self, e3, e4, e5,
      e6, e7, e8, e9, e10, h31, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq,
      not_false_eq_true, Nat.reduceLT, Nat.reducePow, ↓reduceIte, and_self]
    and_intros
    all_goals first
      | trivial
      | rfl
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.mono hB fun s₁ ⟨b31, b30, b29, b24, b25, b18, b21, b22, b27, b23, b20, bl, bk⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ⟨bk.rd.trans (hk.rd.trans kA.rd), bk.wr.trans (hk.wr.trans kA.wr),
    bk.sp.trans (hk.sp.trans kA.sp), bk.lr.trans (hk.lr.trans kA.lr)⟩, ?_, ?_⟩,
    b31, b30, b29, b24, b25, b18, b21, b22, b27, b23, b20⟩
  · rw [bl r hr]
    exact e r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  · rw [bk.mem]
    exact hsv.congr (fun p hp => (gA p.1 (by revert hp; revert p; decide)).symm) kA.lr.symm
  · rw [bk.mem, ← kA.mem]; exact hf

/-- After a step that changes no register the entry set but `r12`, `r19` (and `r0`). -/
theorem SO1.keep {W : Addr} {s₀ s₁ s₂ : State} (h1 : SO1 W s₀ s₁)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r19 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 W s₀ s₂ :=
  ⟨⟨fun r hr => by
      rw [hg r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)]
      exact h1.en.low r hr,
    ⟨hk.rd.trans h1.en.keeps.rd, hk.wr.trans h1.en.keeps.wr, hk.sp.trans h1.en.keeps.sp,
      hk.lr.trans h1.en.keeps.lr⟩, hk.mem ▸ h1.en.saved, hk.mem ▸ h1.en.frame⟩,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r31,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r30,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r29,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r24,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r25,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r18,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r21,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r22,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r27,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r23,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r20⟩

end VG.Proof.Sm4Gcm.PPC64LE
