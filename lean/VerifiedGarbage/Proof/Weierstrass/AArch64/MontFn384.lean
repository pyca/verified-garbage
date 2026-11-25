module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-384's Montgomery product and square modulo `p` as functions on AArch64

`mulFn384` and `sqrFn384` (`Impl/Weierstrass/AArch64/Mont.lean`) are
`mulFnS`'s entry and exit (`mulFnOf_ok`) around the product (`prod_ok`) or the
square (`sqr_ok`), the reduction (`reduce_ok`), the conditional subtraction
against `p` in registers (`csubM_ok`) and the store.
-/

@[expose] public section

-- Powers of two up to `2^768` are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)
open VG.Impl.Mont.AArch64 (P384Field.prod P384Field.sqr P384Field.reduce P384Field.rs P384Field.tl P384Field.th)

/-- The registers holding `p`'s words. -/
abbrev ms384 : List Reg := [.x23, .x24, .x25, .x26, .x26, .x26]

theorem fn384_wp {body : List Instr} {s : State} {Q : State → Prop} : WP isa (fn384 body) s Q ↔
    WP isa (.block (zextCode ++ (saveCode 6 ++ (ptrsCode 6 ++ ((zero7 :: body ++ finish384) ++ restoreCode 6))))) s Q := by
  rw [fn384, WP.seq_iff, ← WP.block_append_iff]
  simp only [List.append_assoc, ptrsCode]

/-- The reduction of `T`, its conditional subtraction and the store. -/
theorem finish384_ok {s : State} {po : Addr} (hpo : PtrW s (roF 6) po (8 * 6)) (hz : s.gpr .x7 = 0)
    (hT : regsVal s (P384Field.tl ++ P384Field.th) < 2 ^ 384 * p384) :
    WP isa (.block finish384) s fun t =>
      (∀ r, r ∉ bodyW 6 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside po 0 (8 * 6) s.mem t.mem ∧ wordsVal t.mem po 0 6 < p384 ∧
      wordsVal t.mem po 0 6 * 2 ^ (64 * 6) % p384 = regsVal s (P384Field.tl ++ P384Field.th) % p384 := by
  have hp : P384Field.p = p384 := by decide
  simp only [finish384, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (P384Field.reduce_ok hz (hp ▸ hT)) fun s₁ ⟨⟨V, hV, hlt, hmod⟩, k₁⟩ => ?_
  rw [hp] at hlt hmod
  have z₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (sparseLoad_ok s₁ z₁) fun s₂ ⟨e23, e24, e25, e26, k₂⟩ => ?_
  have hrs : regsVal s₂ P384Field.rs = regsVal s₁ P384Field.rs := P384Field.regsVal_keep k₂ (by decide)
  have hm : regsVal s₂ ms384 = p384 := by
    simp only [regsVal, e23, e24, e25, e26]; decide
  have hV₂ : regsVal s₂ P384Field.rs + 2 ^ (64 * 6) * (s₂.gpr .x13).toNat = V := by
    rw [hrs, k₂.gpr .x13 (by decide)]; exact hV
  rw [WP.block_append_iff]
  refine WP.mono (csubM_ok (n := 6) (ts := P384Field.rs) (ms := ms384) (top := .x13) rfl rfl (by decide) (by decide)
    (by unfold Fresh; decide) (by decide) (by rw [k₂.gpr _ (by decide), z₁]) hm (by decide)
    (by rw [hV₂]; exact hlt)) fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [hV₂] at e₃
  have K : ∀ r, r ∉ bodyW 6 → s₃.gpr r = s.gpr r := fun r hr => by
    have sub₁ : ∀ q ∈ P384Field.redW, q ∈ bodyW 6 := by decide
    have sub₂ : ∀ q ∈ [Reg.x23, .x24, .x25, .x26], q ∈ bodyW 6 := by decide
    have sub₃ : ∀ q ∈ Reg.x2 :: P384Field.rs ++ dRegs 6, q ∈ bodyW 6 := by decide
    rw [k₃.gpr r fun h => hr (sub₃ r h), k₂.gpr r fun h => hr (sub₂ r h), k₁.gpr r fun h => hr (sub₁ r h)]
  have hpo₃ : PtrW s₃ (roF 6) po (8 * 6) :=
    ⟨(K _ (by decide)).trans hpo.reg, by rw [k₃.wr, k₂.wr, k₁.wr]; exact hpo.st, hpo.enc, hpo.nowrap⟩
  refine WP.mono (storesR_ok P384Field.rs hpo₃ (by decide) rfl (by decide)) fun t ⟨e₄, k₄, O₄⟩ => ?_
  rw [e₃] at e₄
  have e₄' : wordsVal t.mem po 0 6 = V % p384 := e₄
  refine ⟨fun r hr => (k₄.gpr r (by simp)).trans (K r hr), by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], by rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp], ?_, ?_, ?_⟩
  · have hmem : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
    rw [← hmem]; exact O₄
  · rw [e₄']; exact Nat.mod_lt _ (by decide)
  · rw [e₄', Nat.mod_mul_mod, hmod]

theorem prod_lt {A B : Nat} (hA : A < 2 ^ 384) (hB : B < p384) : A * B < 2 ^ 384 * p384 := Nat.mul_lt_mul'' hA hB

theorem zero7_ok (s : State) : WP isa (.block [zero7]) s fun t =>
    t.gpr .x7 = 0 ∧ Keeps [.x7] s t := by
  refine WP.mono (movz0_ok s .x7) fun t ⟨e, k⟩ => ⟨e, k⟩

/-- `vg_p384_mul_mod_p`: `[o] = [a] [b] R⁻¹ mod p`, for `[b]` below `p`. -/
theorem mulFn384_ok {W : Nat} {s : State} (hp : Pre 6 W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) 6 < p384) :
    WP isa mulFn384 s fun s' => abiPreserved s s' ∧ Kept 6 (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 < p384 ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 * 2 ^ (64 * 6) % p384 =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 * wordsVal s.mem (s.gpr .x0) (arg s .x3) 6 % p384) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  rw [mulFn384, fn384_wp]
  refine mulFnOf_ok (.inl rfl) (fun _ B => B < p384) (fun A B => A * B) (by decide +kernel) ?_ hp hb
  intro s base size hs pa pb po hpa hpb hpo hB
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₁ ⟨z₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (P384Field.prod_ok (hpa.of_keeps k₁ (by decide)) (hpb.of_keeps k₁ (by decide)) (by decide) (by decide)
    rfl rfl (by decide) (by decide) z₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [k₁.mem] at e₂
  have hpo₂ : PtrW s₂ (roF 6) po (8 * 6) := ⟨by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hpo.reg],
    by rw [k₂.wr, k₁.wr]; exact hpo.st, hpo.enc, hpo.nowrap⟩
  refine WP.mono (finish384_ok hpo₂ (by rw [k₂.gpr _ (by decide), z₁])
    (by rw [e₂]; exact prod_lt (wordsVal_lt ..) hB)) fun t ⟨g, rd, wr, sp, O, lt, md⟩ => ?_
  have hmem : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine ⟨fun r hr => ?_, by rw [rd, k₂.rd, k₁.rd], by rw [wr, k₂.wr, k₁.wr], by rw [sp, k₂.sp, k₁.sp],
    by rw [← hmem]; exact O, lt, by rw [md, e₂]⟩
  have sub : ∀ q ∈ Reg.x7 :: P384Field.prodW, q ∈ bodyW 6 := by decide
  rw [g r hr, k₂.gpr r fun h => hr (sub r (List.mem_cons_of_mem _ h)),
    k₁.gpr r fun h => hr (sub r (by rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..))]

/-- `vg_p384_sqr_mod_p`: `[o] = [a]² R⁻¹ mod p`, for `[a]` below `p`. -/
theorem sqrFn384_ok {W : Nat} {s : State} (hp : Pre 6 W s)
    (ha : wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 < p384) :
    WP isa sqrFn384 s fun s' => abiPreserved s s' ∧ Kept 6 (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 < p384 ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 * 2 ^ (64 * 6) % p384 =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 * wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 % p384) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  rw [sqrFn384, fn384_wp]
  refine mulFnOf_ok (.inl rfl) (fun A _ => A < p384) (fun A _ => A * A) (by decide +kernel) ?_ hp ha
  intro s base size hs pa pb po hpa hpb hpo hA
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₁ ⟨z₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (P384Field.sqr_ok (hpa.of_keeps k₁ (by decide)) (by decide) rfl (by decide) z₁)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [k₁.mem] at e₂
  have hpo₂ : PtrW s₂ (roF 6) po (8 * 6) := ⟨by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hpo.reg],
    by rw [k₂.wr, k₁.wr]; exact hpo.st, hpo.enc, hpo.nowrap⟩
  refine WP.mono (finish384_ok hpo₂ (by rw [k₂.gpr _ (by decide), z₁])
    (by rw [e₂]; exact prod_lt (wordsVal_lt ..) hA)) fun t ⟨g, rd, wr, sp, O, lt, md⟩ => ?_
  have hmem : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine ⟨fun r hr => ?_, by rw [rd, k₂.rd, k₁.rd], by rw [wr, k₂.wr, k₁.wr], by rw [sp, k₂.sp, k₁.sp],
    by rw [← hmem]; exact O, lt, by rw [md, e₂]⟩
  have sub : ∀ q ∈ Reg.x7 :: P384Field.prodW, q ∈ bodyW 6 := by decide
  rw [g r hr, k₂.gpr r fun h => hr (sub r (List.mem_cons_of_mem _ h)),
    k₁.gpr r fun h => hr (sub r (by rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..))]

end VG.Proof.Weierstrass.AArch64.Mont
