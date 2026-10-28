module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX

/-! # The arithmetic shift right by 30 at a run-time width

`shr30_ok`: `[dst] = [src] >> 30`, signed, `n + 1` words for an even `n`, with
`InvMemory.shr30`'s statement (`sext32`): `n` words two at a time (`shrWord`,
`InvMemory.shrStep` through pointers), then the top word from the sign.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Weierstrass.X86.Inv (sext32 shr_word32)

variable {is : List Instr} {Q : State → Prop}

/-- One output word through the pointers `ebp` (source) and `edi` (destination). -/
theorem shrWord_ok {s : State} {W : Addr} {Z sp dp d : Nat} (hw : Ws s W Z)
    (ps : PtrAt s W .ebp sp) (pd : PtrAt s W .edi dp) (hs : sp + d + 8 ≤ Z) (hd : dp + d + 4 ≤ Z)
    (k : ∀ u, w32 u.mem W (dp + d) =
        (w32 s.mem W (sp + d) / 2 ^ 30 + 4 * w32 s.mem W (sp + d + 4)) % 2 ^ 32 →
      Keeps [.eax, .ebx] s u → Outside W (dp + d) 4 s.mem u.mem → WP isa (.block is) u Q) :
    WP isa (.block (shrWord d ++ is)) s Q := by
  have hn := hw.nowrap
  simp only [shrWord, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hw ps (d := d) (by omega)) fun s₁ U₁ _ => ?_
  refine wp_movS (readSrc_ptr (hw.of_keeps U₁.keeps) (by rw [PtrAt, U₁.other _ (by decide)]; exact ps)
    (d := d + 4) (by omega)) fun s₂ U₂ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₃ U₃ => ?_
  refine wp_addS rfl fun s₄ U₄ _ => wp_addS rfl fun s₅ U₅ _ => wp_addS rfl fun s₆ U₆ _ => ?_
  have K : Keeps [.eax, .ebx] s s₆ :=
    (((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))).trans
      (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))
  have hw₆ := hw.of_keeps K
  have pd₆ : PtrAt s₆ W .edi dp := by rw [PtrAt, K.1 _ (by decide)]; exact pd
  refine wp_storeS (by simpa using ea_ptr hw₆ pd₆ (d := d) (by omega)) (ws_write hw₆ hd) fun u M => ?_
  have m₆ : s₆.mem = s.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  refine k u ?_ (K.trans (M.keeps _)) (by rw [M.mem, m₆]; exact writeW32_outside _ _ _ (by omega))
  rw [M.mem, w32_write_self, U₆.gpr, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, U₅.gpr, U₄.gpr,
    U₃.other _ (by decide), U₂.gpr, U₂.other _ (by decide), U₁.gpr, U₁.mem]
  exact shr_word32 _ _

/-- One more output word: the shifted number's next word. -/
theorem shr_succ {m₀ m m' : Mem} {W : Addr} {dst src k : Nat}
    (V : val32 m W dst k = val32 m₀ W src (k + 1) / 2 ^ 30 % 2 ^ (32 * k))
    (Wd : w32 m' W (dst + 4 * k) =
      (w32 m₀ W (src + 4 * k) / 2 ^ 30 + 4 * w32 m₀ W (src + 4 * k + 4)) % 2 ^ 32)
    (pre : val32 m' W dst k = val32 m W dst k) :
    val32 m' W dst (k + 1) = val32 m₀ W src (k + 2) / 2 ^ 30 % 2 ^ (32 * (k + 1)) := by
  rw [val32_succ, pre, V, Wd, val32_succ m₀ W src (k + 1), val32_succ m₀ W src k, pow32_succ,
    Nat.mul_comm (2 ^ 32) (2 ^ (32 * k)), show src + 4 * (k + 1) = src + 4 * k + 4 by omega]
  exact (VG.Proof.Weierstrass.X86.Inv.shr_arith32 k _ _ _ (val32_lt _ _ _ _)).symm

/-- After `j` pairs of output words. -/
def ShrInv (s₀ : State) (W : Addr) (sp dp n j : Nat) (t : State) : Prop :=
  Keeps [.eax, .ebx, .ebp, .edi, .esi] s₀ t ∧ PtrAt t W .ebp (sp + 8 * j) ∧ PtrAt t W .edi (dp + 8 * j) ∧
  (t.gpr .esi).toNat = 4 * n - 8 * j ∧ Outside W dp (8 * j) s₀.mem t.mem ∧
  val32 t.mem W dp (2 * j) = val32 s₀.mem W sp (2 * j + 1) / 2 ^ 30 % 2 ^ (32 * (2 * j))

/-- The pairs: `n` output words for an even `n`. -/
theorem shrPairs_ok {s₀ : State} {W : Addr} {Z sp dp n : Nat} (hw : Ws s₀ W Z) (hn : 0 < n) (hev : n % 2 = 0)
    (hs : sp + 4 * (n + 1) ≤ Z) (hd : dp + 4 * (n + 1) ≤ Z) (sep : dp + 4 * (n + 1) ≤ sp ∨ sp + 4 * (n + 1) ≤ dp)
    (ps : PtrAt s₀ W .ebp sp) (pd : PtrAt s₀ W .edi dp) (cnt : (s₀.gpr .esi).toNat = 4 * n) :
    WP isa (.loop (.block (shrWord 0 ++ shrWord 4 ++ [.alu .add .ebp (.imm 8), .alu .add .edi (.imm 8),
      .alu .sub .esi (.imm 8)])) .ne) s₀ (ShrInv s₀ W sp dp n (n / 2)) := by
  have hn' := hw.nowrap
  refine VG.Proof.Bignum.X86.PublicRt.countLoop (N := n / 2) (by omega) _ ?_
    ⟨Keeps.refl _ _, by simpa using ps, by simpa using pd, by simpa using cnt, Outside.refl _ _ _ _,
      by simp [val32, Nat.mod_one]⟩
  rintro j t hj ⟨K, pe, pi, ce, O, V⟩
  have ht := hw.of_keeps K
  simp only [List.append_assoc]
  refine shrWord_ok ht pe pi (d := 0) (by omega) (by omega) fun u₁ W₁ K₁ O₁ => ?_
  have pe₁ : PtrAt u₁ W .ebp (sp + 8 * j) := by rw [PtrAt, K₁.1 _ (by decide)]; exact pe
  have pi₁ : PtrAt u₁ W .edi (dp + 8 * j) := by rw [PtrAt, K₁.1 _ (by decide)]; exact pi
  refine shrWord_ok (ht.of_keeps K₁) pe₁ pi₁ (d := 4) (by omega) (by omega) fun u₂ W₂ K₂ O₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ =>
    VG.Proof.Bignum.X86.CrtRt.wp_subXm rfl fun u U z _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .ebp, .edi, .esi] t u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans ((U₃.keeps.mono (by decide)).trans
      (U₄.keeps.mono (by decide)))).trans (U.keeps.mono (by decide))
  have mu : u.mem = u₂.mem := by rw [U.mem, U₄.mem, U₃.mem]
  -- The source's words, unchanged so far.
  have S : ∀ i, i ≤ n → w32 t.mem W (sp + 4 * i) = w32 s₀.mem W (sp + 4 * i) := fun i hi =>
    O.w32 (by omega) (by omega)
  have S₁ : ∀ i, i ≤ n → w32 u₁.mem W (sp + 4 * i) = w32 t.mem W (sp + 4 * i) := fun i hi =>
    O₁.w32 (by omega) (by omega)
  have esi : (u.gpr .esi).toNat = 4 * n - 8 * (j + 1) := by
    rw [U.gpr, U₄.other _ (by decide), U₃.other _ (by decide), K₂.1 _ (by decide), K₁.1 _ (by decide),
      BitVec.toNat_sub, ce, show (8 : BitVec 32).toNat = 8 from rfl]
    have := (t.gpr .esi).isLt; rw [ce] at this; omega
  refine ⟨⟨K.trans K', ?_, ?_, esi, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, U.other _ (by decide), U₄.other _ (by decide), U₃.gpr, K₂.1 _ (by decide), K₁.1 _ (by decide),
      ptr_add pe, show (8 : BitVec 32).toNat = 8 from rfl]
    congr 2
  · rw [PtrAt, U.other _ (by decide), U₄.gpr, U₃.other _ (by decide), K₂.1 _ (by decide), K₁.1 _ (by decide),
      ptr_add pi, show (8 : BitVec 32).toNat = 8 from rfl]
    congr 2
  · rw [mu]
    exact (O.mono (Nat.le_refl _) (by omega)).trans ((O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega)))
  · -- Two more words of the shifted number.
    rw [mu]
    have V₁ : val32 u₁.mem W dp (2 * j + 1) = val32 s₀.mem W sp (2 * j + 2) / 2 ^ 30 % 2 ^ (32 * (2 * j + 1)) := by
      refine shr_succ V ?_ (O₁.val32 (.inl (by omega)) (by omega))
      rw [show dp + 4 * (2 * j) = dp + 8 * j + 0 by omega, W₁, show sp + 8 * j + 0 = sp + 4 * (2 * j) by omega,
        show sp + 4 * (2 * j) + 4 = sp + 4 * (2 * j + 1) by omega, S (2 * j) (by omega), S (2 * j + 1) (by omega)]
    have V₂ := shr_succ (k := 2 * j + 1) V₁ ?_ (O₂.val32 (.inl (by omega)) (by omega))
    · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, show 2 * j + 1 + 1 + 1 = 2 * j + 1 + 2 by omega]
      exact V₂
    rw [show dp + 4 * (2 * j + 1) = dp + 8 * j + 4 by omega, W₂, show sp + 8 * j + 4 = sp + 4 * (2 * j + 1) by omega,
      show sp + 4 * (2 * j + 1) + 4 = sp + 4 * (2 * j + 2) by omega, S₁ (2 * j + 1) (by omega),
      S₁ (2 * j + 2) (by omega), S (2 * j + 1) (by omega), S (2 * j + 2) (by omega)]
  · rw [z]
    congr 1
    have hz : u.gpr .esi = u₄.gpr .esi - 8 := U.gpr
    rw [← hz]
    by_cases e : j + 1 = n / 2
    · simp only [e, decide_true, beq_iff_eq]
      exact BitVec.eq_of_toNat_eq (by rw [esi]; show _ = 0; omega)
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro z0
      have := congrArg BitVec.toNat z0
      rw [esi] at this
      exact e (by simp at this; omega)

end VG.Proof.Rsa.X86.InvBatchRt
