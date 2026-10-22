module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
import VerifiedGarbage.Proof.EcKey.Compressed.X86.TagCheck
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86 Spec.Weierstrass

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.X86.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (([.mov .ebx (.mem (Cfg.argOp 1)), .alu .add .ebx (.imm 1)] : List Instr) ++
    (loadBytes c.C.len c.n (c.sl E) .ebx ++
    (Impl.EcKey.Compressed.X86.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.X86.Cfg.checkLtP c (c.sl E)))))) := by
  simp only [Impl.EcKey.Compressed.X86.decompressPeer, Impl.Ecdh.X86.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {q32 : BitVec 32}
    (hs : Scr s base size)
    (hq : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd ++ t.wr = s.rd ++ s.wr →
      Outside base 0 size s.mem t.mem → readSrc t (.mem (Cfg.argOp 1)) = some q32)
    (hqfit : q32.toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hin : (⟨q32.setWidth 64, 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q32.setWidth 64, 1 + c.C.len⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : flagW c base s = BitVec.allOnes 32) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressPeer c)) s fun t =>
      Scr t base size ∧ Keeps [.eax, .ebx, .edx] s t ∧
      Unch base (slW c [R2P, BP, E, D, FLAG]) s.mem t.mem ∧
      sv c base t R2P = c.R * c.R % c.C.p ∧ sv c base t BP = c.mont c.C.b ∧
      sv c base t E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q32.setWidth 64 + 1) c.C.len) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (q32.setWidth 64)).setWidth 32 ∧
      flagW c base t = mask32 ((s.mem (q32.setWidth 64) = 2 ∨ s.mem (q32.setWidth 64) = 3) ∧
        sv c base t E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_using [hl8, hlhi, this]
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  generalize hq64 : q32.setWidth 64 = q at hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine WP.block_append (WP.mono (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp3])) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp3])) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_using [hR2])).trans (O₂.mono (Nat.zero_le _) (by omega_using [hB]))
  have k₂' : Keeps [.eax] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine WP.block_append ?_
  refine wp_movS (hq s₂ (k₂'.1 _ (by decide)) (by rw [k₂'.2.1, k₂'.2.2]) W₂) fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => WP.block_nil ?_
  have k₄ : Keeps [.eax, .ebx] s s₄ := ((k₂'.mono (by decide)).widen u₃.keeps).widen u₄.keeps
  have hs₄ := hs.of_keeps k₄ (by decide)
  have hm₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hrw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [k₄.2.1, k₄.2.2]
  have hb₄ : s₄.gpr .ebx = q32 + BitVec.ofNat 32 1 := by rw [u₄.gpr, u₃.gpr]; rfl
  have hb₄' : (s₄.gpr .ebx).setWidth 64 = q + BitVec.ofNat 64 1 := by
    rw [hb₄, ← hq64]; exact addr_eq (by omega_using [hqfit, hl8])
  have hbt₄ : (s₄.gpr .ebx).toNat = q32.toNat + 1 := by
    rw [hb₄, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hqfit, hl8])]
  -- `x`
  refine WP.block_append (WP.mono (loadBytes_ok hs₄ (src := .ebx) (by decide) hE (by omega_using [hqfit, hbt₄]) (by omega_using [hl8]) hlhi
    (fun e he => ⟨_, by rw [hrw₄]; exact hin, by
      rw [hb₄', Offset.add_add]; exact Offset.contains_base q (by omega_using [he]) (by omega_using [hsz, hlhi, hM, he])⟩)
    (by rw [hb₄']; exact (hd.sub_left (Offset.sub_base q (by omega_using []))).sub_right (Offset.sub_base base hE)))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄', hm₄] at e₅
  rw [hm₄] at O₅
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have K₅ : Keeps [.eax, .ebx] s s₅ := k₄.widen k₅
  have W₅ : Outside base 0 size s.mem s₅.mem := W₂.trans (O₅.mono (Nat.zero_le _) hE)
  have lead₅ : s₅.mem q = s.mem q := by
    have e := keep_of_disjoint' W₅ hd (by decide) (i := 0) (by omega) (by omega)
    simpa only [BitVec.add_zero] using e
  refine WP.block_append (WP.mono (decompressTag_ok hs₅
    (hq s₅ (K₅.1 _ (by decide)) (by rw [K₅.2.1, K₅.2.2]) W₅)
    (by rw [hq64, K₅.2.1, K₅.2.2]; exact ⟨_, hin, by simpa using Offset.contains_base q (d := 0) (n := 1) (by omega) (by decide)⟩)
    (by have := sl_le c h7 (i := D) (by decide); omega)) fun s₆ ⟨mask₆, tag₆, k₆, O₆⟩ => ?_)
  rw [hq64, lead₅] at mask₆ tag₆
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  refine WP.block_append (WP.mono (andFlag_ok c hs₆ hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_)
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (checkLtP_ok c hs₇ h0 hE hM hF) fun t ⟨f₈, k₈, O₈⟩ => ?_
  have U₅ : Unch base (slW c [R2P, BP, E, D]) s.mem s₅.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₅)
  have U₆ := unch_same U₅ (slot_frame (by simp) (by omega) O₆)
  have v₆ {i : Nat} (hi : i < 45) (hw : i ∉ [R2P, BP, E, D]) :
      sv c base s₆ i = sv c base s i := sv_unch U₆ h7 hn hi (apart_slW hw)
  have x₆ : sv c base s₆ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q + 1) c.C.len) := by
    change wordsVal s₆.mem base (c.sl E) c.n = _
    rw [sv_out (O₆.mono (Nat.le_refl _) (by omega : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide), e₅]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base q (d := 1) (by omega))) (by decide) (by omega)
  have flag₆ : flagW c base s₆ = BitVec.allOnes 32 := by
    rw [flagW, ← hf]
    exact Unch.readW32 U₆ (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, E, D])) w hw; omega) (by omega)
  refine ⟨hs₇.of_keeps k₈ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (K₅.mono (by decide)).trans ((k₆.mono (by decide)).trans ((k₇.mono (by decide)).trans (k₈.mono (by decide))))
  · exact unch_same (unch_same (slots_widen U₆ (slots' := [R2P, BP, E, D, FLAG]) (by decide)) (slot_frame (by simp) (by omega) O₇)) (slot_frame (by simp) (by omega) O₈)
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide),
      sv_out (O₆.mono (Nat.le_refl _) (by omega : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide),
      sv_out (O₆.mono (Nat.le_refl _) (by omega : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide)]
    exact e₂
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide), x₆]
  · rw [BitVec.eq_of_toNat_eq (O₈.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega)),
      BitVec.eq_of_toNat_eq (O₇.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega))]
    exact tag₆
  · simp only [sv] at *
    rw [f₈, f₇, flag₆, mask₆, BitVec.allOnes_and,
      show wordsVal s₇.mem base (c.sl E) c.n = sv c base s₇ E from rfl,
      show wordsVal s₇.mem base (c.sl MP) c.n = sv c base s₇ MP from rfl]
    simp only [sv]
    simp only [mask32, sv_flag O₇ h0 h7 hn (i := E) (by decide) (by decide),
      sv_flag O₇ h0 h7 hn (i := MP) (by decide) (by decide),
      v₆ (i := MP) (by decide) (by decide), hmp,
      sv_flag O₈ h0 h7 hn (i := E) (by decide) (by decide)]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.X86
