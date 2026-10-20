module

public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Initializing the parent DSA workspace without prior scratch contents -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem parent_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block SignVerify.parent) s fun t =>
      Good t B Z outerWords 0 ∧ Outside B 48 80 s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t := by
  unfold SignVerify.parent
  rw [WP.block_append_iff]
  have hwZ : 8 * sW + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hiZ : 8 * sMinv + 8 ≤ Z := Nat.le_trans (by decide) hZ
  refine WP.mono (WP.keep [.x3, .x12] (Q := fun u =>
    u.gpr .x12 = BitVec.ofNat 64 outerWords ∧
    u.mem = (s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 outerWords)).writeW (off B (8 * sMinv)) (0#64)) ?_ rfl rfl rfl)
    fun u ⟨⟨hu12, hum⟩, hku⟩ => ?_
  · brun [hdi, hdr_enc (show sW < 32 by decide), hdr_enc (show sMinv < 32 by decide), hs.st hwZ, hs.st hiZ]
    rfl
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (setBases_ok (hs.congr hku.wr) hudi hu12 (Nat.le_trans (by decide) hZ))
    fun t ⟨htarr, hft, hkt⟩ => ?_
  have hks := hku.trans hkt
  refine ⟨⟨hs.congr hks.wr, (hks.gpr .x0 (by decide)).trans hdi, ⟨?_, ?_, htarr⟩⟩, ?_, hks.mono (by decide)⟩
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * sMinv) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hft.word (Or.inl (by decide)) (by decide), hum, word_writeW_self]
    rfl
  · intro x hx
    rw [hft x (by change ofs B x < 64 ∨ 128 ≤ ofs B x; change ofs B x < 48 ∨ 128 ≤ ofs B x at hx; omega), hum]
    rw [writeW_outside _ B _ (d := 8 * sMinv) (by decide) x
      (by change ofs B x < 56 ∨ 64 ≤ ofs B x; change ofs B x < 48 ∨ 128 ≤ ofs B x at hx; omega)]
    exact writeW_outside _ B _ (d := 8 * sW) (by decide) x
      (by change ofs B x < 48 ∨ 56 ≤ ofs B x; change ofs B x < 48 ∨ 128 ≤ ofs B x at hx; omega)

end VG.Proof.Dsa.AArch64
