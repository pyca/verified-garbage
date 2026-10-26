module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.TagCheck
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Ecdsa.Generic

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm
open Spec.Weierstrass
open VG.Impl.Mont.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (R2P BP)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm dpVal ea toNat_add_lt toNat_imm)

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (.dp .add .r6 .r1 (.imm 1) ::
    (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (Impl.EcKey.Compressed.Arm.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.Arm.Cfg.checkLtP c (c.sl E)))))) := by
  simp only [Impl.EcKey.Compressed.Arm.decompressPeer, Impl.Ecdh.Arm.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    List.cons_append, List.nil_append]

theorem decompressPeer_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hqfit : (s.gpr .r1).toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hin : (⟨State.addr (s.gpr .r1), 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r1), 1 + c.C.len⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : flagW c base s = BitVec.allOnes 32) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressPeer c)) s fun t =>
      Scr t base size ∧ Rest [.r3, .r4, .r5, .r6, .r7, .r8] s t ∧
      Unch base (slW c [R2P, BP, E, D, FLAG]) s.mem t.mem ∧
      sv c base t R2P = c.R * c.R % c.C.p ∧ sv c base t BP = c.mont c.C.b ∧
      sv c base t E = ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r1) + 1) c.C.len) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (State.addr (s.gpr .r1))).setWidth 32 ∧
      flagW c base t = mask32 ((s.mem (State.addr (s.gpr .r1)) = 2 ∨
        s.mem (State.addr (s.gpr .r1)) = 3) ∧ sv c base t E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hq : Reg.r1 ∉ [Reg.r4, .r6] := by decide
  generalize hq32 : s.gpr .r1 = q32 at hqfit hin hd ⊢
  generalize hq64 : State.addr q32 = qa at hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_arith)).trans (O₂.mono (Nat.zero_le _) (by omega_arith))
  have K₂ : Rest [.r4] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  have K₃ : Rest [.r4, .r6] s s₃ := (K₂.mono (by simp)).trans (u₃.rest (by simp))
  have hs₃ := hs.of_rest K₃ (by decide)
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  have hrw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [K₃.rd, K₃.wr]
  have hb₃ : s₃.gpr .r6 = q32 + BitVec.ofNat 32 1 := by
    rw [u₃.gpr, K₂.gpr _ (by decide), hq32]; rfl
  have ha₃ : State.addr (s₃.gpr .r6) = qa + BitVec.ofNat 64 1 := by
    rw [hb₃, ← hq64]; exact ea (by omega_arith)
  have ht₃ : (s₃.gpr .r6).toNat = q32.toNat + 1 := by
    rw [hb₃, toNat_add_lt (by rw [toNat_imm (by decide)]; omega_arith), toNat_imm (by decide)]
  -- `x`
  refine VG.Proof.X25519.Arm.WP.append (loadBytes_ok hs₃ (src := .r6) (by decide) hE (by omega_arith) (by omega_arith) hlhi
    (fun e he => ⟨_, by rw [hrw₃]; exact hin, by
      rw [ha₃, Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (by rw [ha₃]; exact (hd.sub_left (Offset.sub_base qa (by omega_arith))).sub_right (Offset.sub_base base hE)))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [ha₃, hm₃] at e₄
  rw [hm₃] at O₄
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have K₄ : Rest [.r4, .r6] s s₄ := K₃.trans (k₄.mono (by simp))
  have W₄ : Outside base 0 size s.mem s₄.mem := W₂.trans (O₄.mono (Nat.zero_le _) hE)
  have lead₄ : s₄.mem qa = s.mem qa := by
    have e := keep_of_disjoint' W₄ hd (by decide) (i := 0) (by omega) (by omega)
    simpa only [BitVec.add_zero] using e
  refine VG.Proof.X25519.Arm.WP.append (decompressTag_ok (q := q32) hs₄
    (by rw [K₄.gpr _ (by decide), hq32])
    (by rw [K₄.rd, K₄.wr, hq64]; exact ⟨_, hin, by simpa using Offset.contains_base qa (d := 0) (n := 1) (by omega) (by decide)⟩)
    (by have := sl_le c h7 (i := D) (by decide); omega)) fun s₅ ⟨mask₅, tag₅, k₅, O₅⟩ => ?_
  rw [hq64, lead₄] at mask₅ tag₅
  have hs₅ := hs₄.of_rest k₅ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (andFlag_ok c hs₅ hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_rest k₆ (by decide)
  refine WP.mono (checkLtP_ok c hs₆ hE hM hF) fun t ⟨f₇, k₇, O₇⟩ => ?_
  have U₄ : Unch base (slW c [R2P, BP, E, D]) s.mem s₄.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₄)
  have U₅ := unch_same U₄ (slot_frame (by simp) (by omega) O₅)
  have v₅ {i : Nat} (hi : i < 45) (hw : i ∉ [R2P, BP, E, D]) :
      sv c base s₅ i = sv c base s i := sv_unch U₅ h7 hn hi (apart_slW hw)
  have x₅ : sv c base s₅ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + 1) c.C.len) := by
    change wordsVal s₅.mem base (c.sl E) c.n = _
    rw [sv_out (O₅.mono (Nat.le_refl _) (by omega : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide), e₄]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base qa (d := 1) (by omega))) (by decide) (by omega)
  have flag₅ : flagW c base s₅ = BitVec.allOnes 32 := by
    rw [flagW, ← hf]
    exact Unch.readW32 U₅ (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, E, D])) w hw; omega) (by omega)
  refine ⟨hs₆.of_rest k₇ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (K₄.mono (by simp)).trans ((k₅.mono (by simp)).trans ((k₆.mono (by simp)).trans (k₇.mono (by simp))))
  · exact unch_same (unch_same (slots_widen U₅ (slots' := [R2P, BP, E, D, FLAG]) (by decide)) (slot_frame (by simp) (by omega) O₆)) (slot_frame (by simp) (by omega) O₇)
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide),
      sv_out (O₅.mono (Nat.le_refl _) (by omega : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide),
      sv_out (O₅.mono (Nat.le_refl _) (by omega : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide)]
    exact e₂
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide), x₅]
  · rw [BitVec.eq_of_toNat_eq (O₇.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega)),
      BitVec.eq_of_toNat_eq (O₆.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega))]
    exact tag₅
  · simp only [sv] at *
    rw [f₇, f₆, flag₅, mask₅, BitVec.allOnes_and,
      show wordsVal s₆.mem base (c.sl E) c.n = sv c base s₆ E from rfl,
      show wordsVal s₆.mem base (c.sl MP) c.n = sv c base s₆ MP from rfl]
    simp only [sv]
    simp only [mask32, sv_flag O₆ h0 h7 hn (i := E) (by decide) (by decide),
      sv_flag O₆ h0 h7 hn (i := MP) (by decide) (by decide),
      v₅ (i := MP) (by decide) (by decide), hmp,
      sv_flag O₇ h0 h7 hn (i := E) (by decide) (by decide)]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.Arm
