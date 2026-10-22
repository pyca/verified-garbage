module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Tag
import VerifiedGarbage.Proof.EcKey.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Write a compressed point, clear failures, and restore x86 registers -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86 VG.Impl.Mont.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 Spec.Weierstrass

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.X86.compressFinish c =
    .mov .ecx (.mem (sc (c.sl FLAG))) :: .mov .ebx (.mem (Cfg.argOp 0)) ::
    (Impl.EcKey.Compressed.X86.compressTag c ++
    (storeBytes c.C.len c.n .ebx 1 (c.sl E) ++
    (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore))) := by
  simp only [Impl.EcKey.Compressed.X86.compressFinish, List.append_assoc, List.cons_append, List.nil_append]

theorem finish_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {o : BitVec 32} (hout : readSrc s (.mem (Cfg.argOp 0)) = some o)
    (hofit : o.toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hw : (⟨o.setWidth 64, 1 + c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o.setWidth 64, 1 + c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.X86.compressFinish c)) s fun t =>
      Spec.Ecdsa.bytesAt t.mem (o.setWidth 64) (1 + c.C.len) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) ::
          toBytes c.C.len (sv c base s E) else List.replicate (1 + c.C.len) 0) ∧
      t.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, t.gpr rd.1 = g rd.1) ∧
      t.gpr .esp = s.gpr .esp ∧ Outside (o.setWidth 64) 0 (1 + c.C.len) s.mem t.mem := by
  have hsz : size = 8192 := rfl
  have h7 := hc.n10
  have h0 := hc.n0
  have hE := sl_le c h7 (i := E) (by decide)
  have hY := sl_le c h7 (i := Impl.Ecdh.X86.QY) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hn := hs.nowrap
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  rw [finish_eq]
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movS (show readSrc s₁ (.mem (Cfg.argOp 0)) = some o by
    have hea : s₁.ea (Cfg.argOp 0) = s.ea (Cfg.argOp 0) := by
      show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
      rw [u₁.other _ (by decide)]
    rw [← hout]; show s₁.load32 _ = s.load32 _
    rw [State.load32, State.load32, hea, u₁.rd, u₁.wr, u₁.mem]) fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.ebx, .ecx] s s₂ := (u₁.keeps.mono (by simp)).trans (u₂.keeps.mono (by simp))
  have hs₂ := hs.of_keeps K₂ (by decide)
  have hb₂ : s₂.gpr .ebx = o := u₂.gpr
  have hc₂ : s₂.gpr .ecx = mask32 (b = true) := by rw [u₂.other _ (by decide), u₁.gpr, ← flagW, hf]
  have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  refine WP.block_append (WP.mono (tag_ok hs₂ (by omega) hb₂
    (by rw [K₂.2.2]; exact ⟨_, hw, by simpa using Offset.contains_base (o.setWidth 64) (d := 0) (n := 1) (by omega) (by decide)⟩)
    b hc₂ h0) fun s₃ ⟨L₃, O₃, K₃⟩ => ?_)
  simp only [sv, m₂] at L₃
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  have hb₃ : s₃.gpr .ebx = o := (K₃.1 _ (by decide)).trans hb₂
  have hc₃ : s₃.gpr .ecx = mask32 (b = true) := (K₃.1 _ (by decide)).trans hc₂
  have U₃ := O₃.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega)))
  have x₃ : wordsVal s₃.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), m₂]
  refine WP.block_append (WP.mono (storeBytes_ok hs₃ (dst := .ebx) (d := 1) (a := c.sl E)
    (by decide) (by decide) b hc₃ hE (by omega) hlhi (by rw [hb₃]; omega)
    (fun e m he => ⟨_, by rw [K₃.2.2, K₂.2.2]; exact hw, by
      rw [hb₃, Offset.add_add]; exact Offset.contains_base (o.setWidth 64) (by omega) (by omega)⟩)
    (by rw [hb₃]; exact (hd.symm.sub_left (Offset.sub_base base hE)).sub_right (Offset.sub_base (o.setWidth 64) (d := 1) (by omega)))) fun s₄ ⟨e₄, K₄, O₄⟩ => ?_)
  rw [hb₃, x₃] at e₄
  rw [hb₃] at O₄
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  have U₄ := O₄.unch_far (hd.symm.sub_right (Offset.sub_base (o.setWidth 64) (d := 1) (by omega)))
  have hsv₄ : ∀ rd ∈ Cfg.saved, s₄.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hrd
    have := saved_lt rd hrd
    have ap : ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 := by
      intro w hw; obtain rfl := List.mem_singleton.mp hw; exact .inl (by omega)
    rw [Unch.readW32 U₄ ap (by omega), Unch.readW32 U₃ ap (by omega), m₂, hsv rd hrd]
  refine WP.mono (tail_ok hs₄ hsv₄ b (by rw [K₄.1 _ (by decide), hc₃]))
    fun t ⟨mt, ret, saved, others⟩ => ⟨?_, ret, saved, ?_, ?_⟩
  · have lead : Spec.Ecdsa.bytesAt s₄.mem (o.setWidth 64) 1 =
        [if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) else 0] := by
      rw [bytesAt_keep O₄ (Offset.base_disjoint (o.setWidth 64) (by omega) (by omega)) (by omega) (by omega)]
      simpa [Spec.Ecdsa.bytesAt, sv] using congrArg (· :: []) L₃
    rw [mt, bytesAt_add, lead, e₄]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · rfl
  · rw [others _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]
  · rw [mt, ← m₂]
    exact (O₃.mono (Nat.zero_le _) (by omega)).trans ((O₄.shift (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.EcKey.Compressed.X86
