module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFinishRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWide
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState

import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulus
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # Exact CRT product-plus-residue reconstruction -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtRecombineValue.lean`, which only this module imported.
section

/-! # The padded CRT residue fits the addition loop's input width -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem val32_prefix_of_eq {m : Mem} {base : Addr} {d n k value : Nat}
    (h : val32 m base d (n + k) = value) (fit : value < 2 ^ (32 * n)) :
    val32 m base d n = value := by
  have eq := congrArg (fun x => x % 2 ^ (32 * n)) h
  rw [val32_append] at eq
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_eq_of_lt (val32_lt m base d n), Nat.mod_eq_of_lt fit] using eq

theorem crt_paddedResidue_low {m before : Mem} {base : Addr} {d w o : Nat}
    (h : val32 m base d (4 * w + 2) = numAt before base w o) :
    val32 m base d (4 * w) = numAt before base w o := by
  apply val32_prefix_of_eq h
  rw [numAt_native]
  exact Nat.lt_of_lt_of_le (val32_lt before base (arrAt w o) (2 * w))
    (Nat.pow_le_pow_right (by decide) (by omega))

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtFinishInput (base : BitVec 32) (size len w o d : Nat) (s : State) : Prop where
  padding : CrtPadInput base size len w d s
  row : RowCtx s base size o d (4 * w)
  outputFits : o + 4 * (4 * w + 2) ≤ size
  separate : o + 4 * (4 * w + 2) ≤ d
  output : s.mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 o
  sumFits : val32 s.mem (State.addr base) o (4 * w + 2) + numAt s.mem (State.addr base) w 1 < 2 ^ (32 * (4 * w + 2))

theorem crt_finishPad_ready (s : State) {base : BitVec 32} {size len w o d : Nat}
    (h : CrtFinishInput base size len w o d s) :
    WP isa (padModulus 1) s fun t => CrtAddWideInput base size o d w t ∧
      val32 t.mem (State.addr base) o (4 * w + 2) = val32 s.mem (State.addr base) o (4 * w + 2) ∧
      val32 t.mem (State.addr base) d (4 * w) = numAt s.mem (State.addr base) w 1 ∧
      Outside (State.addr base) d (4 * (4 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have p := h.padding
  have small := p.layout.size
  have nowrap := p.workspace.nowrap
  have sep := p.separate
  have fits := p.fits
  refine WP.mono (crt_padModulus_ok s p 1) ?_
  rintro u ⟨padded, outside, ptrU, restU⟩
  have low := crt_paddedResidue_low padded
  have product := outside.val32 (d := o) (k := 4 * w + 2) (Or.inl h.separate) (by have := h.outputFits; omega)
  have frame := outside_workspace outside p.fits
  have count := p.layout.nativeCount p.main
  have ready : CrtAddWideInput base size o d w u := by
    refine ⟨p.workspace.congr restU.wr, by omega,
      ⟨h.row.nowrap, h.row.outFits, h.row.inFits, h.row.separate, by rw [restU.wr]; exact h.row.writable⟩,
      ?_, h.outputFits, ptrU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hw := p.layout.width ▸ p.layout.layout.1; omega
    · rw [outside_read32 outside (d := 48) (by omega) (by decide)]; exact count
    · rw [outside_read32 outside (d := 232) (by omega) (by decide)]; exact h.output
    · rw [outside_read32 outside (d := 240) (by omega) (by decide)]; exact p.link
    · rw [product, low]; exact h.sumFits
    · rw [restU.rd, restU.wr, restU.sp]; exact p.stackRead
    · rw [restU.sp]; exact p.stackSep
    · exact saved_base_kept frame p.stackSep p.saved restU.sp
  exact ⟨ready, product, low, outside, frame, restU⟩

theorem crt_finishRecombine_ok (s : State) {base : BitVec 32} {size len w o d : Nat}
    (h : CrtFinishInput base size len w o d s) :
    WP isa finishRecombine s fun t =>
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) o (4 * w + 2) + numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(d, 4 * (4 * w + 2)), (o, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [finishRecombine, WP.seq_iff]
  refine WP.mono (crt_finishPad_ready s h) ?_
  rintro u ⟨ready, product, low, outside, frame, restU⟩
  refine WP.mono (crt_addWide_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [product, low] at value
  exact ⟨value, (Outs.of_outside outside (by simp)).trans (Outs.of_outside outsideT (by simp)),
    frame.trans frameT, ptrT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
