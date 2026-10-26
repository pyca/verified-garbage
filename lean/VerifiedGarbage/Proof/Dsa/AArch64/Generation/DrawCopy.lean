module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Copy a complete draw's significant suffix, preserving the advanced cursor frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem drawCopy_ok {s : State} {B rp op : Addr} {Z w used len drawBytes : Nat}
    (h : Ws s B Z w) (hlen : len ≤ drawBytes) (hmax : drawBytes < 4096)
    (hp : word s.mem B (8 * kRand) = rp)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (ho : word s.mem B (8 * kOut) = op)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr)
      (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsrc : ∀ i < len, Z ≤ ofs B (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i))
    (hsep : ∀ i < len, ∀ j < len,
      off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i ≠ off op j) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy len drawBytes) s fun t =>
      t.gpr .x0 = B ∧
      (∀ i < len, t.mem (off op i) = s.mem (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i)) ∧
      (∀ a, (∀ i < len, a ≠ off op i) →
        t.mem a = (s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) a) ∧
      Keep [.x0, .x2, .x3, .x9, .x12, .x17] s t := by
  unfold Impl.Dsa.AArch64.Generation.drawCopy
  refine WP.seq (WP.mono (drawCopyArgs_ok h hlen hmax hp hu ho)
    fun u ⟨hu17, hu12, hu2, hu9, hum, ku⟩ => ?_)
  have hur : ∀ i < len, InRegions (u.rd ++ u.wr)
      (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i) 1 := by
    intro i hi; rw [ku.rd, ku.wr]; exact hrd i hi
  have huw : ∀ i < len, InRegions u.wr (off op i) 1 := by
    intro i hi; rw [ku.wr]; exact hwr i hi
  refine WP.seq (WP.mono (random_copyRest_ok hu12 hu2 hu9 (by omega) hur huw hsep)
    fun v ⟨hb, hf, kv⟩ => ?_)
  have hv17 := (kv.gpr .x17 (by decide)).trans hu17
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = v.mem)
    (by brun [hv17]) rfl rfl rfl) fun t ⟨⟨ht0, htm⟩, kt⟩ => ?_
  refine ⟨ht0, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · intro i hi
    rw [htm, hb i hi, hum]
    apply writeW_outside _ B _ (d := 8 * kUsed) (by decide)
    have h256 := h.h256
    have hx := hsrc i hi
    simp only [off] at hx
    exact Or.inr (by simp only [kUsed, sFn]; omega)
  · intro a ha
    rw [htm, hf a ha, hum]

end VG.Proof.Dsa.AArch64.Generation
