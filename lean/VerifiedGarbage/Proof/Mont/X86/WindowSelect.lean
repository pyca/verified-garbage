module

public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Impl.Mont.X86.Window
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Reading the window's table entry by a masked scan of the whole table -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem window_mask_small : ∀ a < 32, ∀ j < 32,
    0 - ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 j) - 1) >>> 31 =
      if a = j then BitVec.allOnes 32 else 0 := by
  decide

theorem window_mask (x : BitVec 32) (hx : x.toNat < 32) {j : Nat} (hj : j < 32) :
    0 - ((x ^^^ BitVec.ofNat 32 j) - 1) >>> 31 = if x.toNat = j then BitVec.allOnes 32 else 0 := by
  have e : x = BitVec.ofNat 32 x.toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])
  rw [e, window_mask_small _ hx _ hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

/-- ECX all ones exactly when the window word is `j`. -/
theorem windowMask_ok {s : State} {base : Addr} {size j : Nat} (hs : Scr s base size)
    (hsz : 8 ≤ size) (hw : w32 s.mem base 4 < 32) (hj : j < 32) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.windowMask j)) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ecx = (if w32 s.mem base 4 = j then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.windowMask VG.Impl.Mont.X86.Dynamic.windowOffset
  refine wp_movS (readSrc_sc hs (d := 4) (by omega_arith)) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  refine wp_subS rfl fun s₃ u₃ _ => ?_
  refine wp_shr (by decide) fun s₄ u₄ _ => ?_
  refine wp_movS rfl fun s₅ u₅ _ => ?_
  refine wp_subS rfl fun t u₆ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
    simp only [reduceCtorEq, ↓reduceIte]
    exact window_mask _ hw hj
  · exact (((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen
      u₅.keeps).widen u₆.keeps

/-- Copy `n` 64-bit words. -/
theorem copyWords_ok {s : State} {base : Addr} {bytes n src dst : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hsrc : src + 8 * n ≤ bytes) (hdst : dst + 8 * n ≤ bytes)
    (apart : dst = src ∨ dst + 8 * n ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (VG.Impl.Mont.X86.Dynamic.copyWords n src dst) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base src n ∧
      Outside base dst (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.copyWords
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  refine WP.mono (selectsW_ok (hs.of_keeps U.keeps (by decide)) false U.gpr (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨O, V, K⟩ => ?_
  refine ⟨?_, ?_, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, V, U.mem]
    simp only [ite_self]
  · rw [U.mem] at O
    simpa only [show 4 * (2 * n) = 8 * n by omega_arith] using O

end VG.Proof.Mont.X86.Dynamic
