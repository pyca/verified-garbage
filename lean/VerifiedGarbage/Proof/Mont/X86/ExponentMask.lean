module
public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Saving and consuming a secret exponent bit -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem negative_lowBit (x : BitVec 32) :
    0 - (x &&& 1) = if x.toNat % 2 = 1 then BitVec.allOnes 32 else 0 := by
  have h : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
  rcases h with h | h
  · have e : x &&& 1 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat, h]
      rfl
    rw [e, h]
    rfl
  · have e : x &&& 1 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat, h]
      rfl
    rw [e, h]
    rfl

theorem exponentMask_ok {s : State} {base : Addr} {size exp mask : Nat}
    (hs : Scr s base size) (he : exp + 4 ≤ size) (hm : mask + 4 ≤ size) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.exponentMask exp mask)) s fun t =>
      Outside base mask 4 s.mem t.mem ∧
      t.mem.readW (off base mask) 32 =
        (if w32 s.mem base exp % 2 = 1 then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.exponentMask
  refine wp_movS (readSrc_sc hs he) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun s₄ u₄ _ => ?_
  have K : Keeps [.eax, .ecx] s s₄ := (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps
  have hs₄ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₄.ea (by omega)) (hs₄.write hm) fun t mt => WP.block_nil ⟨?_, ?_, K.trans (mt.keeps _)⟩
  · rw [mt.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)
  · apply BitVec.eq_of_toNat_eq
    change w32 t.mem base mask = _
    rw [mt.mem, w32_write_self, u₄.gpr, u₃.gpr, u₃.other .ecx (by decide), u₂.gpr,
      u₁.gpr, ite_eq_left rfl, negative_lowBit]

theorem selectProduct_ok {s : State} {base : Addr} {size out product mask : Nat} {M : Mod}
    (hs : Scr s base size) (ho : out + 8 * M.n ≤ size) (hp : product + 8 * M.n ≤ size)
    (hm : mask + 4 ≤ size) (sep : out = product ∨ out + 8 * M.n ≤ product ∨ product + 8 * M.n ≤ out)
    (bit : Bool) (hmask : s.mem.readW (off base mask) 32 = if bit then BitVec.allOnes 32 else 0)
    (hn : 0 < M.n) :
    WP isa (VG.Impl.Mont.X86.Dynamic.selectProduct M out product mask) s fun t =>
      Outside base out (8 * M.n) s.mem t.mem ∧
      wordsVal t.mem base out M.n = wordsVal s.mem base (if bit then product else out) M.n ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.selectProduct
  refine WP.seq (wp_movS (readSrc_sc hs hm) fun s₁ u₁ _ => WP.block_nil ?_)
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have mask₁ : s₁.gpr .ecx = if bit then BitVec.allOnes 32 else 0 := u₁.gpr.trans hmask
  refine WP.mono (selectsW_ok (tmp := product) (n := words M) hs₁ bit mask₁ (by simp only [words]; omega)
    (by simp only [words]; omega) (by simp only [words]; omega) (by simp only [words]; omega)
    (.inl rfl) (by simp only [words]; omega)) fun t ⟨O, V, K⟩ => ?_
  have len : 4 * words M = 8 * M.n := by simp only [words]; omega
  rw [len, u₁.mem] at O
  rw [u₁.mem] at V
  exact ⟨O, by simpa only [wordsVal_eq_val32, words] using V,
    (u₁.keeps.mono (by decide)).trans (K.mono (by decide))⟩

end VG.Proof.Mont.X86.Dynamic
