import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Impl.EcKey.Arm

/-!
# Elliptic curve public keys on 32-bit ARM: the result

`finish` writes `04 ‖ x ‖ y` big-endian to `out` (in `lr`), or zeros, by the
flag's mask, returns the flag's low bit and restores the callee-saved
registers (`pkFinish_ok`): the leading byte by `strb`, the two coordinates
from `out + 1` as the signature's `finish` writes `r ‖ s`, then the
signature's return value and restore.
-/

namespace VG.Proof.EcKey.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm
open VG.Impl.EcKey.Arm (YM Y)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_dp wp_mov wp_strb op2_imm op2_reg dpVal)

variable {c : Cfg}

theorem mask4 (b : Bool) :
    (((4 : BitVec 32) &&& mask32 (b = true)).setWidth 8 : BitVec 8) = if b then 4 else 0 := by
  cases b <;> decide

theorem finish_eq (c : Cfg) : Impl.EcKey.Arm.Cfg.finish c =
    .ldr .r10 wb (c.sl FLAG) :: .mov .r4 (.imm 4) :: .dp .and .r4 .r4 (.reg .r10) :: .strb .r4 .lr 0 ::
    (storeBE c.n .lr 1 (c.sl X) ++ (storeBE c.n .lr (1 + 8 * c.n) (c.sl Y) ++
    (.dp .and .r0 .r10 (.imm 1) :: Cfg.restore))) := by
  simp only [Impl.EcKey.Arm.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- The result, the return value and the callee-saved registers. -/
theorem pkFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hlr : s.gpr .lr = o32) (hofit : o32.toNat + (1 + 16 * c.n) ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, 1 + 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, 1 + 16 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Arm.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) (1 + 16 * c.n) =
        (if b then 4 :: (toBytes (8 * c.n) (sv c base s X) ++ toBytes (8 * c.n) (sv c base s Y))
          else List.replicate (1 + 16 * c.n) 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 (1 + 16 * c.n) s.mem s'.mem := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hsz : size = 4096 := rfl
  have hX := sl_le c h7 (i := X) (by decide)
  have hY := sl_le c h7 (i := Y) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : State.addr o32 = out at hw hd ⊢
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + 8 * c.n ≤ 1 + 16 * c.n →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d : Nat}, d + 8 * c.n ≤ 1 + 16 * c.n →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  have h16 : ∀ rd ∈ Cfg.saved, ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 :=
    fun rd hrd w hw => by
      have := saved_lt rd hrd
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega)
  rw [finish_eq]
  -- The flag and the leading byte.
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (d := c.sl FLAG) (n := 4) (by omega))
    fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have k₃ : Rest [.r4, .r10] s s₃ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
  have hs₃ := hs.of_rest k₃ (by decide)
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hc₃ : s₃.gpr .r10 = mask32 (b = true) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ← flagW, hf]
  have hb₃ : s₃.gpr .lr = o32 := by rw [k₃.gpr _ (by decide), hlr]
  have ha₃ : (s₃.gpr .r4).setWidth 8 = (if b then 4 else 0 : BitVec 8) := by
    rw [u₃.gpr, dpVal, u₂.gpr, u₂.other .r10 (by decide), u₁.gpr, ← flagW, hf]
    exact mask4 b
  refine wp_strb (by decide) (a := off out 0)
    (by rw [hb₃, addr_add (by omega), hout64])
    ⟨_, by rw [k₃.wr]; exact hw, Offset.contains_base out (by omega) (by omega)⟩ fun s₄ m₄ => ?_
  have hs₄ := hs₃.of_rest (m₄.rest []) (by decide)
  have O₄ : Outside out 0 1 s₃.mem s₄.mem := by rw [m₄.mem]; exact writeW8_outside _ _ _ (by omega)
  have L₄ : s₄.mem (out + BitVec.ofNat 64 0) = if b then 4 else 0 := by rw [m₄.mem, writeW8_self, ha₃]
  have U₄ := O₄.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega)))
  have hb₄ : s₄.gpr .lr = o32 := by rw [m₄.gpr, hb₃]
  have hc₄ : s₄.gpr .r10 = mask32 (b = true) := by rw [m₄.gpr, hc₃]
  have x₄ : wordsVal s₄.mem base (c.sl X) c.n = sv c base s X := by
    rw [U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₃]
  -- `x`, from `out + 1`.
  refine VG.Proof.X25519.Arm.WP.append (storeBE_ok hs₄ (dst := .lr) (d := 1) (a := c.sl X) (by decide) b
    hc₄ hX (by rw [hb₄]; omega) (by omega) (fun e he => ⟨_, by rw [m₄.wr, k₃.wr]; exact hw, by
      rw [hb₄, hout64, Offset.add_add]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hb₄, hout64]; exact hdsc hX (by omega))) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [hb₄, hout64, x₄] at e₅
  rw [hb₄, hout64] at O₅
  have hs₅ := hs₄.of_rest k₅ (by decide)
  have U₅ := O₅.unch_far (hscd (d := 1) (by omega))
  have hb₅ : s₅.gpr .lr = o32 := by rw [k₅.gpr _ (by decide), hb₄]
  have hc₅ : s₅.gpr .r10 = mask32 (b = true) := by rw [k₅.gpr _ (by decide), hc₄]
  have y₅ : wordsVal s₅.mem base (c.sl Y) c.n = sv c base s Y := by
    rw [U₅.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₃]
  -- `y`, from `out + 1 + 8 n`.
  refine VG.Proof.X25519.Arm.WP.append (storeBE_ok hs₅ (dst := .lr) (d := 1 + 8 * c.n) (a := c.sl Y) (by decide) b
    hc₅ hY (by rw [hb₅]; omega) (by omega) (fun e he => ⟨_, by rw [k₅.wr, m₄.wr, k₃.wr]; exact hw, by
      rw [hb₅, hout64, Offset.add_add]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hb₅, hout64]; exact hdsc hY (by omega))) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hb₅, hout64, y₅] at e₆
  rw [hb₅, hout64] at O₆
  have hs₆ := hs₅.of_rest k₆ (by decide)
  have U₆ := O₆.unch_far (hscd (d := 1 + 8 * c.n) (by omega))
  have hsv₆ : ∀ rd ∈ Cfg.saved, s₆.mem.readW (off base rd.2) 32 = g rd.1 := fun rd hrd => by
    have := saved_lt rd hrd
    rw [Unch.readW32 U₆ (h16 rd hrd) (by omega), Unch.readW32 U₅ (h16 rd hrd) (by omega),
      Unch.readW32 U₄ (h16 rd hrd) (by omega), hm₃, hsv rd hrd]
  -- The return value and the callee-saved registers.
  refine wp_dp (op2_imm (by decide)) fun s₇ u₇ => ?_
  have hs₇ := hs₆.of_rest (u₇.rest (ws := [.r0]) (by simp)) (by decide)
  have r0₇ : s₇.gpr .r0 = if b then 1 else 0 := by
    rw [u₇.gpr, dpVal, k₆.gpr _ (by decide), hc₅]; exact mask_bit b
  rw [restore_eq]
  refine WP.mono (ldrs_ok hs₇ Cfg.saved (fun p hp => by have := saved_lt p hp; omega) saved_nodup
    (fun p hp => (saved_r12 p hp).1)) fun s' ⟨m', K', V'⟩ => ⟨?_, ?_, fun rd hrd => ?_, ?_, ?_⟩
  · have lead : Spec.Ecdsa.bytesAt s₆.mem out 1 = [if b then 4 else 0] := by
      rw [bytesAt_keep O₆ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
        bytesAt_keep O₅ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
      exact congrArg (· :: []) L₄
    have xs : Spec.Ecdsa.bytesAt s₆.mem (out + BitVec.ofNat 64 1) (8 * c.n) =
        if b then toBytes (8 * c.n) (sv c base s X) else List.replicate (8 * c.n) 0 := by
      rw [bytesAt_keep O₆ (Offset.disjoint out (.inl (Nat.le_refl _)) (by omega) (by omega)) (by omega)
        (by omega), e₅]
    rw [m', u₇.mem, show 1 + 16 * c.n = 1 + (8 * c.n + 8 * c.n) by omega, bytesAt_add, bytesAt_add, lead, xs,
      Offset.add_add, e₆]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · simp only [ite_true]; rfl
  · rw [K'.gpr _ (by decide), r0₇]
  · rw [V' rd hrd, u₇.mem, hsv₆ rd hrd]
  · exact (((k₃.mono (by simp)).trans ((m₄.rest _).trans ((k₅.mono (by simp)).trans (k₆.mono (by simp))))).trans
      ((u₇.rest (by simp)).trans (K'.mono (by decide))))
  · rw [m', u₇.mem, ← hm₃]
    exact ((O₄.mono (Nat.zero_le _) (by omega)).trans ((outside_shift O₅ (by omega)).mono (Nat.zero_le _)
      (by omega))).trans ((outside_shift O₆ (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.EcKey.Arm
