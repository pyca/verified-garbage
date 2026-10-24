module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
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
# SEC 1 point compression on PPC64LE: the result

`compressFinish` writes `02 + (y mod 2)` and `x` big-endian to `out` (in
`r14`), or zeros, by the flag's mask, returns the flag's low bit and restores
the callee-saved registers and `lr` (`finish_ok`): the tag by `stb`, `x` from
`out + 1` by `storeBytes`, as the public key's `finish`
(`Proof/EcKey/PPC64LE/Finish.lean`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.EcKey.PPC64LE (toNat_add_of)
open VG.Impl.Ecdh.PPC64LE (QY)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.compressFinish c =
    ([.load .d .r10 wb (c.sl FLAG), .load .d .r4 wb (c.sl QY), .li .r5 1, .logic .and .r4 .r4 .r5,
      .addi .r4 .r4 2, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0] : List Instr) ++
    (storeBytes c.C.len c.n .r14 1 (c.sl E) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4]))) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.compressFinish, Impl.EcKey.Compressed.PPC64LE.compressTag,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The tag or zeros, `x` or zeros, the return value and the callee-saved
registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + (1 + c.C.len) ≤ 2 ^ 64)
    (hwr : (⟨out, 1 + c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.compressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + c.C.len) =
        (if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) :: toBytes c.C.len (sv c base s E)
          else List.replicate (1 + c.C.len) 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 (1 + c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn0 := hc.n0
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hE := sl_le c h7 (i := E) (by decide)
  have hQ := sl_le c h7 (i := QY) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  have hin : ∀ {d e m : Nat}, d + e + m ≤ 1 + c.C.len →
      InRegions s.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m := fun hd' =>
    ⟨_, hwr, by rw [Offset.add_add]; exact Offset.contains_base out hd' (by omega)⟩
  have hin0 : InRegions s.wr (out + BitVec.ofNat 64 0) 1 := by
    have := hin (d := 0) (e := 0) (m := 1) (by omega); rwa [BitVec.add_zero] at this
  -- The flag and the tag.
  have lead : WP isa (.block [.load .d .r10 wb (c.sl FLAG), .load .d .r4 wb (c.sl QY), .li .r5 1,
      .logic .and .r4 .r4 .r5, .addi .r4 .r4 2, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0]) s
      fun t => Kp [.r4, .r5, .r10] s t ∧
        t.mem = s.mem.writeW (out + BitVec.ofNat 64 0)
          (if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0 : BitVec 8) ∧
        t.gpr .r10 = (if b then BitVec.allOnes 64 else 0) := by
    refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega)) ?_
    refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) (sl_al c QY) (by omega)) ?_
    refine wp_step (exec_li (by decide)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (exec_addi (by decide) (by decide)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (exec_stb (by decide) (by decide) (by simp only [write_gpr, write_wr, reduceCtorEq, ite_false, h14]; exact hin0))
      (WP.block_nil ⟨?_, ?_, ?_⟩)
    · exact (((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
        (Kp.write _ _ (by decide))).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans
        (Kp.store _ _ _)
    · simp only [write_gpr, reduceCtorEq, ite_false, ite_true, write_mem, h14]
      rw [show word s.mem base (c.sl FLAG) = mask64 (b = true) from hf,
        ← tag_byte s.mem base (c.sl QY) c.n hn0 b]; rfl
    · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]; exact hf
  rw [finish_eq]
  refine wp_append (WP.mono lead fun s₄ ⟨K₄, hm₄, hc₄⟩ => ?_)
  have O₄ : Outside out 0 1 s.mem s₄.mem := by
    rw [hm₄]; exact writeW8_outside s.mem out (d := 0) _ (by omega)
  have L₄ : s₄.mem (out + BitVec.ofNat 64 0) = if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0 := by
    rw [hm₄, writeW8_self]
  have U₄ := O₄.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega)))
  have hb₄ : s₄.gpr .r14 = out := by rw [K₄.g, h14]
  have x₄ : wordsVal s₄.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega)]
  have hs₄ := K₄.ws hs
  have h3₄ := K₄.at h3
  -- `x`, from `out + 1`.
  have hdx : Region.Disjoint ⟨off base (c.sl E), 8 * c.n⟩ ⟨out + BitVec.ofNat 64 1, c.C.len⟩ :=
    (hd.symm.sub_left (Offset.sub_base base (by omega))).sub_right (Offset.sub_base out (by omega))
  refine wp_append (WP.mono (storeBytes_ok hs₄ h3₄ (dst := .r14) (d := 1) (a := c.sl E) (by decide) (by decide)
    (by decide) (by decide) b hc₄ (by omega) (sl_al c E) (by omega) (by omega) hlhi (by omega)
    (by rw [hb₄, toNat_add_of (by omega)]; omega) (fun e m he => by rw [K₄.wr, hb₄]; exact hin (by omega))
    (by rw [hb₄]; exact hdx)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄, x₄] at e₅
  rw [hb₄] at O₅
  have U₅ := O₅.unch_far (hd.symm.sub_right (Offset.sub_base out (d := 1) (n := c.C.len) (by omega)))
  have hsv : ∀ d, d + 8 ≤ 24 → word s₅.mem base d = word s.mem base d := fun d hd' => by
    rw [U₅.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₄.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega)]
  have hs₅ := k₅.ws hs₄
  have h3₅ := k₅.at h3₄
  -- The return value and the callee-saved registers.
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₅.write _ _).write _ _) ((h3₅.write _).write _) (by omega) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · have lead : Spec.Ecdsa.bytesAt s₅.mem out 1 = [if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0] := by
      rw [bytesAt_keep O₅ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
      exact congrArg (· :: []) L₄
    simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [bytesAt_add, lead, e₅]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · simp only [ite_true]; rfl
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₅.g, hc₄, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₅ :=
      (K₄.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31])).trans
        (k₅.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₅ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    exact (O₄.mono (Nat.zero_le _) (by omega)).trans ((outside_shift O₅ (by omega)).mono (Nat.zero_le _)
      (by omega))

end VG.Proof.EcKey.Compressed.PPC64LE
