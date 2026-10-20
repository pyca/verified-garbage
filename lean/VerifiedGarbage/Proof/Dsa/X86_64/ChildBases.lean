module
public import VerifiedGarbage.Impl.Bignum.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.Rsa.X86_64
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-! # Constructing a child workspace header before loading its modulus -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev childBases : List Instr :=
  ([.store (hdr sW) .r12, .store (hdr Crt.sLink) .rsi] : List Instr) ++ setBases

theorem childBases_ok {s : State} {B parent : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hsi : s.gpr .rsi = parent)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hZ : 136 ≤ Z) :
    WP isa (.block childBases) s fun t =>
      Good t B Z w (word s.mem B (8 * sMinv)) ∧ word t.mem B (8 * Crt.sLink) = parent ∧
      Outside B 48 88 s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  unfold childBases
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem =
    (s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 w)).writeW (off B (8 * Crt.sLink)) parent) ?_ rfl)
    fun u ⟨hum, hku⟩ => ?_
  · xrun [State.ea, hdr, hdrOff, hdi, hsi, h12, hs.st (d := 8 * sW) (Nat.le_trans (by decide) hZ), hs.st (d := 8 * Crt.sLink) hZ]
  have hudi := (hku.gpr (show Reg.rdi ∉ [] by decide)).trans hdi
  have hu12 := (hku.gpr (show Reg.r12 ∉ [] by decide)).trans h12
  refine WP.mono (setBases_ok (hs.congr hku.2.2) hudi hu12 (Nat.le_trans (by decide) hZ))
    fun t ⟨htarr, hft, hkt⟩ => ?_
  have hks := hku.trans hkt
  refine ⟨⟨hs.congr hks.2.2, (hks.gpr (by decide)).trans hdi, ⟨?_, ?_, htarr⟩⟩, ?_, ?_, hks.mono (by decide)⟩
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide)).word (Or.inl (by decide)) (by decide),
      (writeW_outside _ B _ (d := 8 * sW) (by decide)).word (Or.inr (by decide)) (by decide)]
  · rw [hft.word (Or.inr (by decide)) (by decide), hum, word_writeW_self]
  · intro x hx
    rw [hft x (by change ofs B x < 64 ∨ 128 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega), hum]
    rw [writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide) x
      (by change ofs B x < 128 ∨ 136 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega)]
    exact writeW_outside _ B _ (d := 8 * sW) (by decide) x
      (by change ofs B x < 48 ∨ 56 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega)

end VG.Proof.Dsa.X86_64
