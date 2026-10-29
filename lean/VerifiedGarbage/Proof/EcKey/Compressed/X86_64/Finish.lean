module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.TCB.Code
/-! # Write a compressed point or a completely cleared output -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Tag.lean`, which only this module imported.
section

/-! # The compressed tag store -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem eaRsi (s : State) : s.ea { base := .rsi } = s.gpr .rsi := by
  simp [State.ea]

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.X86_64.QY + 8 ≤ size)
    (hw : InRegions s.wr (s.gpr .rsi) 1) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.compressTag c)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi)
        ((((word s.mem base (c.sl Impl.Ecdh.X86_64.QY) &&& 1) + 2) &&& s.gpr .rcx).setWidth 8) ∧
      KeepRegs [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.compressTag, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, execAlu, Option.map_some, Option.bind_some, State.load64, State.store8,
    ea_sc, eaRsi, hs.rdi, ld_sc hs hy, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    ite_true, ite_false, reduceCtorEq, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass
open Spec.Weierstrass

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.compressFinish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (Impl.EcKey.Compressed.X86_64.compressTag c ++
    (storeBytes c.C.len c.n .rsi 1 (c.sl E) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++ Spill.restoreCode .rdi Cfg.saved))) := by
  simp only [Impl.EcKey.Compressed.X86_64.compressFinish, List.append_assoc]
  rfl

theorem finish_ok {c : Cfg} (hc : BaseCfgOk c) {base out : Addr} {s : State}
    (hs : Scr s base size) (hrsi : s.gpr .rsi = out)
    (hw : (⟨out, c.C.len + 1⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len + 1⟩ ⟨base, size⟩)
    (hfit : out.toNat + c.C.len + 1 ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.compressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (c.C.len + 1) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86_64.QY % 2) ::
          toBytes c.C.len (sv c base s E) else List.replicate (c.C.len + 1) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hE := sl_le c hc.n10 (i := E) (by decide)
  have hY := sl_le c hc.n10 (i := Impl.Ecdh.X86_64.QY) (by decide)
  have hF := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0; have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have htagd : Region.Disjoint ⟨base, size⟩ ⟨out, 1⟩ :=
    hd.symm.sub_right (by simpa using Offset.sub_base out (d := 0) (n := 1) (by omega : 0 + 1 ≤ c.C.len + 1))
  have hxd : Region.Disjoint ⟨base, size⟩ ⟨out + 1, c.C.len⟩ := by
    exact hd.symm.sub_right (Offset.sub_base out (d := 1) (by omega))
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hrsi₁ : s₁.gpr .rsi = out := (k₁.1 _ (by decide)).trans hrsi
  rw [WP.block_append_iff]
  refine WP.mono (tag_ok (c := c) hs₁ (by omega) (by
    rw [hrsi₁, k₁.2.2.2]
    exact ⟨_, hw, by
      simpa using Offset.contains_base out (d := 0) (n := 1)
        (by omega : 0 + 1 ≤ c.C.len + 1) (by decide)⟩)) fun s₂ ⟨m₂, k₂⟩ => ?_
  rw [hrsi₁, e₁, k₁.2.1, hf, tag_byte _ _ _ _ hc.n0 b] at m₂
  have O₂ : Outside out 0 1 s₁.mem s₂.mem := by
    rw [m₂, k₁.2.1]
    simpa only [off, BitVec.add_zero] using
      writeW8_outside s.mem out (d := 0)
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86_64.QY % 2) else 0) (by decide)
  have U₂ := O₂.unch_far htagd
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hrsi₂ : s₂.gpr .rsi = out := (k₂.gpr _ (by decide)).trans hrsi₁
  have hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have x₂ : wordsVal s₂.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      k₁.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .rsi) (d := 1) (a := c.sl E) (by decide) (by decide) b
    hrcx₂ hE (by omega) hc.len_lo hc.len_hi (by
      rw [hrsi₂, Offset.toNat_add_ofNat]
      simp only [show (1 : Nat) % 2 ^ 64 = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega)
    (by
      rw [hrsi₂]
      intro e m hem
      exact ⟨_, by rw [k₂.wr, k₁.2.2.2]; exact hw, by
        rw [Offset.add_add]
        exact Offset.contains_base out (by omega) (by omega)⟩)
    (by
      rw [hrsi₂]
      exact hxd.sub_left (Offset.sub_base base hE))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hrsi₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far hxd
  have hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 :=
    (k₃.gpr _ (by decide)).trans hrcx₂
  have lead : s₃.mem out = if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86_64.QY % 2) else 0 := by
    have hb : Spec.Ecdsa.bytesAt s₃.mem out 1 = Spec.Ecdsa.bytesAt s₂.mem out 1 :=
      bytesAt_keep O₃ (Offset.base_disjoint out (e := 1) (n := c.C.len) (k := 1)
        (by omega) (by omega)) (by omega) (by decide)
    have he : s₃.mem out = s₂.mem out := by simpa [Spec.Ecdsa.bytesAt] using hb
    rw [he, m₂, writeW8_self]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hsv₄ : Spill.Saved s₄.mem base g Cfg.saved := by
    rw [k₄.2.1]
    have h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst w
      decide
    exact Saved.unch (Saved.unch (k₁.2.1 ▸ hsv) h48 U₂) h48 U₃
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₄ (by decide) (fun p hp => ?_)
    (by rw [hs₄.rdi]; exact hsv₄)) fun s₅ ⟨g₅, r₅, m₅, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₄.rdi]
    exact ⟨_, List.mem_append_right _ hs₄.wr, hs₄.contains (by omega) (by decide)⟩
  refine ⟨?_, ?_, g₅⟩
  · rw [m₅, k₄.2.1, show c.C.len + 1 = 1 + c.C.len by omega, bytesAt_add, e₃, x₂]
    have hb : Spec.Ecdsa.bytesAt s₃.mem out 1 = [s₃.mem out] := by simp [Spec.Ecdsa.bytesAt]
    rw [hb, lead]
    cases b <;> simp [Nat.add_comm, List.replicate_succ]
  · rw [r₅ _ (by decide), e₄, hrcx₃, mask_bit]

end VG.Proof.EcKey.Compressed.X86_64
