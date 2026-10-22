module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Tag
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout

/-! # Write a compressed point or a completely cleared output -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass
open Spec.Weierstrass

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.AArch64.compressFinish c =
    ([ld .x3 (c.sl FLAG)] : List Instr) ++
    (Impl.EcKey.Compressed.AArch64.compressTag c ++
    (storeBytes c.C.len c.n .x20 1 (c.sl E) ++
    (Spill.restoreCode .x0 Cfg.saved ++
    ([.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1] : List Instr)))) := by
  simp only [Impl.EcKey.Compressed.AArch64.compressFinish, List.append_assoc]
  rfl

theorem finish_ok {c : Cfg} (hc : BaseCfgOk c) {base out : Addr} {s : State}
    (hs : Scr s base size) (hrsi : s.gpr .x20 = out)
    (hw : (⟨out, c.C.len + 1⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len + 1⟩ ⟨base, size⟩)
    (hfit : out.toNat + c.C.len + 1 ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.compressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (c.C.len + 1) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.AArch64.QY % 2) ::
          toBytes c.C.len (sv c base s E) else List.replicate (c.C.len + 1) 0) ∧
      (s'.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have hn := hs.nowrap
  have := hc.n10
  have hsz : size = 8192 := rfl
  have hE := sl_le c hc.n10 (i := E) (by decide)
  have hY := sl_le c hc.n10 (i := Impl.Ecdh.AArch64.QY) (by decide)
  have hF := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0; have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have htagd : Region.Disjoint ⟨base, size⟩ ⟨out, 1⟩ :=
    hd.symm.sub_right (by simpa using Offset.sub_base out (d := 0) (n := 1) (by omega : 0 + 1 ≤ c.C.len + 1))
  have hxd : Region.Disjoint ⟨base, size⟩ ⟨out + 1, c.C.len⟩ := by
    exact hd.symm.sub_right (Offset.sub_base out (d := 1) (by omega))
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := c.sl FLAG) (by omega) (sl_mod8 c FLAG) .x3) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hrsi₁ : s₁.gpr .x20 = out := (k₁.gpr _ (by decide)).trans hrsi
  rw [WP.block_append_iff]
  refine WP.mono (tag_ok (c := c) hs₁ (by omega) hrsi₁ (by
    rw [k₁.wr]
    exact ⟨_, hw, by
      simpa using Offset.contains_base out (d := 0) (n := 1)
        (by omega : 0 + 1 ≤ c.C.len + 1) (by decide)⟩) b (by rw [e₁, hf]) hc.n0)
      fun s₂ ⟨lead₂, O₂, k₂⟩ => ?_
  simp only [sv, k₁.mem] at lead₂
  have U₂ := O₂.unch_far htagd
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hrsi₂ : s₂.gpr .x20 = out := (k₂.gpr _ (by decide)).trans hrsi₁
  have hrcx₂ : s₂.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have x₂ : wordsVal s₂.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      k₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .x20) (d := 1) (a := c.sl E) (by decide) (by decide) (by decide) b
    hrcx₂ hE (sl_mod8 c E) (by omega) hc.len_lo hc.len_hi (by omega) (by
      rw [hrsi₂, Offset.toNat_add_ofNat]
      simp only [show (1 : Nat) % 2 ^ 64 = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega)
    (by
      rw [hrsi₂]
      intro e m hem
      exact ⟨_, by rw [k₂.wr, k₁.wr]; exact hw, by
        rw [Offset.add_add]
        exact Offset.contains_base out (by omega) (by omega)⟩)
    (by
      rw [hrsi₂]
      exact hxd.sub_left (Offset.sub_base base hE))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hrsi₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far hxd
  have hrcx₃ : s₃.gpr .x3 = if b then BitVec.allOnes 64 else 0 :=
    (k₃.gpr _ (by decide)).trans hrcx₂
  have lead : s₃.mem out = if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.AArch64.QY % 2) else 0 := by
    have hb : Spec.Ecdsa.bytesAt s₃.mem out 1 = Spec.Ecdsa.bytesAt s₂.mem out 1 :=
      bytesAt_keep O₃ (Offset.base_disjoint out (e := 1) (n := c.C.len) (k := 1)
        (by omega) (by omega)) (by omega) (by decide)
    have he : s₃.mem out = s₂.mem out := by simpa [Spec.Ecdsa.bytesAt] using hb
    exact he.trans lead₂
  have hsv₃ : Spill.Saved base g Cfg.saved s₃.mem := by
    have h64 : ∀ w ∈ [(size, 2 ^ 64)], 64 ≤ w.1 := by
      intro w hw
      obtain rfl := List.mem_singleton.mp hw
      decide
    exact Saved.unch (Saved.unch (k₁.mem ▸ hsv) h64 U₂) h64 U₃
  refine Spill.restore_ok hs₃.x0 (by decide) (by decide) (fun p hp => ?_) hsv₃
    fun s₄ R₄ => ?_
  · have := saved_lt p hp
    exact ⟨_, List.mem_append_right _ hs₃.wr, hs₃.contains (by omega) (by decide)⟩
  refine WP.mono (retBit_ok s₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [k₅.mem, R₄.mem, show c.C.len + 1 = 1 + c.C.len by omega, bytesAt_add, e₃, x₂]
    have hb : Spec.Ecdsa.bytesAt s₃.mem out 1 = [s₃.mem out] := by simp [Spec.Ecdsa.bytesAt]
    rw [hb, lead]
    cases b <;> simp [Nat.add_comm, List.replicate_succ]
  · rw [e₅, R₄.other _ (by decide), hrcx₃, mask_bit]
  · intro r hr
    rw [k₅.gpr _ (by revert r; decide)]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R₄.gpr p hp

end VG.Proof.EcKey.Compressed.AArch64
