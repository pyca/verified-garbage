module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.Copy

/-! # Direct selection of a public exponentiation-table digit -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Registers for a direct selection, without changing memory. -/
theorem selectHead_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hv : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block selectHead) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rsi = off P (slot wx (8 + v)) ∧
      t.gpr .rbx = off P (slot wx Crt.aT) ∧ t.mem = s.mem ∧
      Keep [.r12, .rax, .rdx, .rsi, .rbx] s t := by
  refine WP.mono (WP.keep [.r12, .rax, .rdx, .rsi, .rbx] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rsi = off P (slot wx (8 + v)) ∧
    t.gpr .rbx = off P (slot wx Crt.aT) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold selectHead
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sW) (by decide),
    hc.ld (i := Crt.sNib) (by decide), hc.ld (i := Crt.sTab) (by decide),
    hc.ld (i := sArr Crt.aT) (by decide), hc.good.hdr.hw, hc.good.hdr.harr Crt.aT (by decide), ht, hv,
    execImul]
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  simp only [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
    off, BitVec.add_assoc]
  congr 2
  unfold slot hdrBytes
  grind

/-- Copy the selected table entry; only the destination array changes. -/
theorem select_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa select s fun t => CExpCtx t P wx minv X Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + v)) wx ∧
      Outside P (slot wx Crt.aT) (8 * wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hE := ent_le wx hv
  have hE0 := slot_mono wx (show 8 ≤ 8 + v by omega)
  have hsep := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  have hz := hc.scrT.nowrap
  unfold select
  refine WP.seq (WP.mono (selectHead_ok hc ht hn) fun u ⟨h12, hsi, hbx, hm, hk⟩ => ?_)
  have hs := hc.scrT.congr hk.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega) (by omega) (by omega)
    (fun i hi => hs.ld (by omega)) (fun i hi => hs.st (by omega))
    (fun i hi b hb => by rw [ofs_off P (by omega)]; omega)) fun t ⟨hval, _, hf, hkt⟩ => ?_
  rw [hm] at hf hval
  have k := (hk.trans hkt).mono (show ∀ r ∈ [.r12, .rax, .rdx, .rsi, .rbx] ++ [.rax, .r14], r ∈ mmRegs by decide)
  exact ⟨hc.of_win (Frm.of_outside (hf.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega) (by omega)) (by simp [crtWinRanges])) k.2.2 (k.gpr (by decide)), hval, hf, k⟩

end VG.Proof.Dsa.X86_64.PublicPower
