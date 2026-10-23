module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Elliptic curve public keys on PPC64LE: the result

`finish` writes `04 ‖ x ‖ y` big-endian to `out` (in `r14`), or zeros, by the
flag's mask, returns the flag's low bit and restores the callee-saved
registers and `lr` (`pkFinish_ok`): the leading byte by `stb`, the two
coordinates from `out + 1` by `storeBytes`, as on 32-bit ARM
(`Proof/EcKey/Arm/Finish.lean`).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.EcKey.PPC64LE (YM Y)

variable {c : Cfg}

theorem mask4 (b : Bool) :
    (((BitVec.ofNat 64 4 &&& mask64 (b = true)).setWidth 8) : BitVec 8) = if b then 4 else 0 := by
  cases b <;> decide

theorem finish_eq (c : Cfg) : Impl.EcKey.PPC64LE.Cfg.finish c =
    .load .d .r10 wb (c.sl FLAG) :: .li .r4 4 :: .logic .and .r4 .r4 .r10 :: .stb .r4 .r14 0 ::
    (storeBytes c.C.len c.n .r14 1 (c.sl X) ++ (storeBytes c.C.len c.n .r14 (1 + c.C.len) (c.sl Y) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4])))) := by
  simp only [Impl.EcKey.PPC64LE.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

theorem finish_eq' (c : Cfg) : Impl.EcKey.PPC64LE.Cfg.finish c =
    ([.load .d .r10 wb (c.sl FLAG), .li .r4 4, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0] : List Instr) ++
    (storeBytes c.C.len c.n .r14 1 (c.sl X) ++ (storeBytes c.C.len c.n .r14 (1 + c.C.len) (c.sl Y) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4])))) := by
  simp only [Impl.EcKey.PPC64LE.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

theorem toNat_add_of {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt h]

/-- The result, the return value and the callee-saved registers. -/
theorem pkFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    (hwr : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.EcKey.PPC64LE.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s X) ++ toBytes c.C.len (sv c base s Y))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 (1 + 2 * c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn0 := hc.n0
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hX := sl_le c h7 (i := X) (by decide)
  have hY := sl_le c h7 (i := Y) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hin : ∀ {d e m : Nat}, d + e + m ≤ 1 + 2 * c.C.len →
      InRegions s.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m := fun hd' =>
    ⟨_, hwr, by rw [Offset.add_add]; exact Offset.contains_base out hd' (by omega)⟩
  have hin0 : InRegions s.wr (out + BitVec.ofNat 64 0) 1 := by
    have := hin (d := 0) (e := 0) (m := 1) (by omega); rwa [BitVec.add_zero] at this
  -- The flag and the leading byte.
  have lead : WP isa (.block [.load .d .r10 wb (c.sl FLAG), .li .r4 4, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0]) s
      fun t => Kp [.r4, .r10] s t ∧ t.mem = s.mem.writeW (out + BitVec.ofNat 64 0) (if b then 4 else 0 : BitVec 8) ∧
        t.gpr .r10 = (if b then BitVec.allOnes 64 else 0) := by
    refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega)) ?_
    refine wp_step (exec_li (by decide)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (exec_stb (by decide) (by decide) (by simp only [write_gpr, write_wr, reduceCtorEq, ite_false, h14]; exact hin0))
      (WP.block_nil ⟨((Kp.write _ _ (by decide)).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans
        (Kp.store _ _ _), ?_, ?_⟩)
    · simp only [write_gpr, reduceCtorEq, ite_false, ite_true, write_mem, h14]
      rw [show word s.mem base (c.sl FLAG) = mask64 (b = true) from hf, ← mask4]; rfl
    · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]; exact hf
  rw [finish_eq']
  refine wp_append (WP.mono lead fun s₄ ⟨K₄, hm₄, hc₄⟩ => ?_)
  have O₄ : Outside out 0 1 s.mem s₄.mem := by
    rw [hm₄]; exact writeW8_outside s.mem out (d := 0) _ (by omega)
  have L₄ : s₄.mem (out + BitVec.ofNat 64 0) = if b then 4 else 0 := by rw [hm₄, writeW8_self]
  have U₄ := O₄.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega)))
  have hb₄ : s₄.gpr .r14 = out := by rw [K₄.g, h14]
  have x₄ : wordsVal s₄.mem base (c.sl X) c.n = sv c base s X := by
    rw [U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega)]
  have hs₄ := K₄.ws hs
  have h3₄ := K₄.at h3
  -- `x`, from `out + 1`.
  refine wp_append (WP.mono (storeBytes_ok hs₄ h3₄ (dst := .r14) (d := 1) (a := c.sl X) (by decide) (by decide)
    (by decide) (by decide) b hc₄ (by omega) (sl_al c X) (by omega) (by omega) hlhi (by omega)
    (by rw [hb₄, toNat_add_of (by omega)]; omega) (fun e m he => by rw [K₄.wr, hb₄]; exact hin (by omega))
    (by rw [hb₄]; exact hdsc (by omega) (by omega))) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄, x₄] at e₅
  rw [hb₄] at O₅
  have U₅ := O₅.unch_far (hd.symm.sub_right (Offset.sub_base out (d := 1) (n := c.C.len) (by omega)))
  have hb₅ : s₅.gpr .r14 = out := by rw [k₅.g, hb₄]
  have hc₅ : s₅.gpr .r10 = if b then BitVec.allOnes 64 else 0 := by rw [k₅.g, hc₄]
  have y₅ : wordsVal s₅.mem base (c.sl Y) c.n = sv c base s Y := by
    rw [U₅.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega)]
  -- `y`, from `out + 1 + len`.
  refine wp_append (WP.mono (storeBytes_ok (k₅.ws hs₄) (k₅.at h3₄) (dst := .r14) (d := 1 + c.C.len) (a := c.sl Y)
    (by decide) (by decide) (by decide) (by decide) b hc₅ (by omega) (sl_al c Y) (by omega) (by omega) hlhi (by omega)
    (by rw [hb₅, toNat_add_of (by omega)]; omega) (fun e m he => by rw [k₅.wr, K₄.wr, hb₅]; exact hin (by omega))
    (by rw [hb₅]; exact hdsc (by omega) (by omega))) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_)
  rw [hb₅, y₅] at e₆
  rw [hb₅] at O₆
  have U₆ := O₆.unch_far (hd.symm.sub_right (Offset.sub_base out (d := 1 + c.C.len) (n := c.C.len) (by omega)))
  have hsv : ∀ d, d + 8 ≤ 24 → word s₆.mem base d = word s.mem base d := fun d hd' => by
    rw [U₆.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₅.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₄.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega)]
  have hs₆ := k₆.ws (k₅.ws hs₄)
  have h3₆ := k₆.at (k₅.at h3₄)
  -- The return value and the callee-saved registers.
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₆.write _ _).write _ _) ((h3₆.write _).write _) (by omega) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · have lead : Spec.Ecdsa.bytesAt s₆.mem out 1 = [if b then 4 else 0] := by
      rw [bytesAt_keep O₆ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
        bytesAt_keep O₅ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
      exact congrArg (· :: []) L₄
    have xs : Spec.Ecdsa.bytesAt s₆.mem (out + BitVec.ofNat 64 1) c.C.len =
        if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0 := by
      rw [bytesAt_keep O₆ (Offset.disjoint out (.inl (Nat.le_refl _)) (by omega) (by omega)) (by omega)
        (by omega), e₅]
    simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [show 1 + 2 * c.C.len = 1 + (c.C.len + c.C.len) by omega, bytesAt_add, bytesAt_add, lead, xs,
      Offset.add_add, e₆]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · simp only [ite_true]; rfl
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₆.g, k₅.g, hc₄, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₆ :=
      ((K₄.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31])).trans
        (k₅.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))).trans
        (k₆.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₆ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    exact ((O₄.mono (Nat.zero_le _) (by omega)).trans ((outside_shift O₅ (by omega)).mono (Nat.zero_le _)
      (by omega))).trans ((outside_shift O₆ (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.EcKey.PPC64LE
