module

import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Tag
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Elliptic curve public keys on 32-bit ARM: the result

`finish` writes `04 ‖ x ‖ y` big-endian to `out` (in `lr`), or zeros, by the
flag's mask, returns the flag's low bit and restores the callee-saved
registers (`pkFinish_ok`): the leading byte by `strb`, the two coordinates
from `out + 1` as the signature's `finish` writes `r ‖ s`, then the
signature's return value and restore.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (QY)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_dp wp_mov wp_strb op2_imm op2_reg dpVal)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.compressFinish c =
    .ldr .r10 wb (c.sl FLAG) ::
      (Impl.EcKey.Compressed.Arm.compressTag c ++
      (storeBytes c.C.len c.n .lr 1 (c.sl E) ++
      (.dp .and .r0 .r10 (.imm 1) :: Cfg.restore))) := by
  simp only [Impl.EcKey.Compressed.Arm.compressFinish, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The result, the return value and the callee-saved registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hlr : s.gpr .lr = o32) (hofit : o32.toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, 1 + c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, 1 + c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.compressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) (1 + c.C.len) =
        (if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) :: toBytes c.C.len (sv c base s E)
          else List.replicate (1 + c.C.len) 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 (1 + c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hsz : size = 4096 := rfl
  have hX := sl_le c h7 (i := E) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : State.addr o32 = out at hw hd ⊢
  have hdsc : Region.Disjoint ⟨off base (c.sl E), 8 * c.n⟩ ⟨out + BitVec.ofNat 64 1, c.C.len⟩ :=
    (hd.symm.sub_left (Offset.sub_base base hX)).sub_right (Offset.sub_base out (d := 1) (by omega))
  have hscd : Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 1, c.C.len⟩ :=
    hd.symm.sub_right (Offset.sub_base out (d := 1) (by omega))
  have h16 : ∀ rd ∈ Cfg.saved, ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 :=
    fun rd hrd w hw => by
      have := saved_lt rd hrd
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega_arith)
  rw [finish_eq]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (d := c.sl FLAG) (n := 4) (by omega))
    fun s₁ u₁ => ?_
  have k₁ := u₁.rest (ws := [.r10]) (by simp)
  have hs₁ := hs.of_rest k₁ (by decide)
  have hb₁ : s₁.gpr .lr = o32 := (k₁.gpr _ (by decide)).trans hlr
  refine VG.Proof.X25519.Arm.WP.append (tag_ok hs₁ (by omega) hb₁ (by omega)
    (by rw [k₁.wr, hout64]; exact ⟨_, hw, by simpa using Offset.contains_base out (d := 0) (n := 1) (by omega) (by decide)⟩)
    b (by rw [u₁.gpr, ← flagW, hf]) hn0) fun s₄ ⟨L₄, O₄, k₄⟩ => ?_
  rw [hout64] at L₄ O₄
  simp only [sv, u₁.mem] at L₄
  have hs₄ := hs₁.of_rest k₄ (by decide)
  have U₄ := O₄.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega)))
  have hb₄ : s₄.gpr .lr = o32 := (k₄.gpr _ (by decide)).trans hb₁
  have hc₄ : s₄.gpr .r10 = mask32 (b = true) := by rw [k₄.gpr _ (by decide), u₁.gpr, ← flagW, hf]
  have x₄ : wordsVal s₄.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), u₁.mem]
  -- `x`, from `out + 1`.
  refine VG.Proof.X25519.Arm.WP.append (storeBytes_ok hs₄ (dst := .lr) (d := 1) (a := c.sl E) (by decide)
    (by decide) b hc₄ hX (by omega_arith) hlhi (by rw [hb₄]; omega_arith) (by omega_arith) (fun e m he => ⟨_, by rw [k₄.wr, k₁.wr]; exact hw, by
      rw [hb₄, hout64, Offset.add_add]; exact Offset.contains_base out (by omega_arith) (by omega_arith)⟩)
    (by rw [hb₄, hout64]; exact hdsc)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [hb₄, hout64, x₄] at e₅
  rw [hb₄, hout64] at O₅
  have hs₆ := hs₄.of_rest k₅ (by decide)
  have U₅ := O₅.unch_far hscd
  have hsv₆ : ∀ rd ∈ Cfg.saved, s₅.mem.readW (off base rd.2) 32 = g rd.1 := fun rd hrd => by
    have := saved_lt rd hrd
    rw [Unch.readW32 U₅ (h16 rd hrd) (by omega), Unch.readW32 U₄ (h16 rd hrd) (by omega),
      u₁.mem, hsv rd hrd]
  -- The return value and the callee-saved registers.
  refine wp_dp (op2_imm (by decide)) fun s₇ u₇ => ?_
  have hs₇ := hs₆.of_rest (u₇.rest (ws := [.r0]) (by simp)) (by decide)
  have r0₇ : s₇.gpr .r0 = if b then 1 else 0 := by
    rw [u₇.gpr, dpVal, k₅.gpr _ (by decide), hc₄]; exact mask_bit b
  rw [restore_eq]
  refine WP.mono (ldrs_ok hs₇ Cfg.saved (fun p hp => by have := saved_lt p hp; omega_arith) saved_nodup
    (fun p hp => (saved_r12 p hp).1)) fun s' ⟨m', K', V'⟩ => ⟨?_, ?_, fun rd hrd => ?_, ?_, ?_⟩
  · have lead : Spec.Ecdsa.bytesAt s₅.mem out 1 =
        [if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0] := by
      rw [bytesAt_keep O₅ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
      simpa [sv, Spec.Ecdsa.bytesAt] using congrArg (· :: []) L₄
    rw [m', u₇.mem, bytesAt_add, lead, e₅]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · rfl
  · rw [K'.gpr _ (by decide), r0₇]
  · rw [V' rd hrd, u₇.mem, hsv₆ rd hrd]
  · exact (k₁.mono (by simp)).trans ((k₄.mono (by simp)).trans
      ((k₅.mono (by simp)).trans ((u₇.rest (by simp)).trans (K'.mono (by decide)))))
  · rw [m', u₇.mem, ← u₁.mem]
    exact (O₄.mono (Nat.zero_le _) (by omega)).trans
      ((outside_shift O₅ (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.EcKey.Compressed.Arm
