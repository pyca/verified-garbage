module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepareFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.GcdIsOne
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LAtLeastTwo
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad

/-! # Prepare the private exponent using only a two-word inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL aE aU aV aOne kEv kFlag kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (OddPrepared exponentRanges exponentTemps
  exponent_preserves_e exponent_preserves_num exponent_temps_inverse exponent_temps_keep
  exponent_temps_preserves_num exponent_mask_coefficient InverseLayout inverse_end_le)

theorem dOddPrepare_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dOddPrepare s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧
      OddPrepared B n (val32 s.mem B kEv 2) (num s.mem B n aL) t ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let e := val32 s.mem B kEv 2
  let L := num s.mem B n aL
  have e3 : 3 ≤ e := large
  have eo : e % 2 = 1 := odd
  have e64 : e < 2 ^ 64 := val32_lt s.mem B kEv 2
  have re : L % e < e := Nat.mod_lt _ (by omega)
  unfold dOddPrepare seqs
  refine WP.seq (WP.mono (arrayDivision_ok h (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [loaded]; exact Nat.zero_lt_of_lt large)) fun u ⟨hu, Ou, Q, R, Ku⟩ => ?_)
  rw [loaded] at Q R
  change num u.mem B n aU = L / e at Q
  change num u.mem B n aV = L % e at R
  have divisionFrame := exponent_division_frame Ou
  have Eu : val32 u.mem B kEv 2 = e := exponent_preserves_e divisionFrame
  have remainderBound : val32 u.mem B (arr n aV) n < 2 ^ 64 := by
    change num u.mem B n aV < 2 ^ 64
    rw [R]
    exact Nat.lt_trans re e64
  have remainderLow : val32 u.mem B (arr n aV) 2 = L % e :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width remainderBound).trans R
  have layout : InverseLayout Z 2 (arr n aV) kEv := by
    have fit := hu.arr_fit (j := aV) (by decide)
    have head := hu.hdr_le
    refine ⟨?_, ?_, Or.inr (inverse_end_le width (by decide)), Or.inl (by decide)⟩
    · unfold S at fit
      omega
    · unfold kEv hdr at *
      omega
  refine WP.seq (WP.mono (inverseFrom_ok (w := .exponent)
    (src := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV) (mo := .fixed kEv)
    hu (by decide) (by decide) layout
    (by change val32 u.mem B kEv 2 % 2 = 1; rw [Eu]; exact eo) (by change 1 < val32 u.mem B kEv 2; rw [Eu]; omega)) fun v ⟨hv, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  change num v.mem B 2 1 = Nat.gcd (val32 u.mem B (arr n aV) 2) (val32 u.mem B kEv 2) at gcd
  change (val32 u.mem B kEv 2 : Int) ∣ (num v.mem B 2 3 : Int) * val32 u.mem B (arr n aV) 2 - num v.mem B 2 1 at congruence
  rw [remainderLow, Eu] at gcd congruence
  rw [gcd] at congruence
  change num v.mem B 2 3 < val32 u.mem B kEv 2 at boundX
  rw [Eu] at boundX
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have inverseFrame : OutsS B (s.gpr .esp) (exponentTemps n) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => exponent_temps_inverse width) Ov
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .exponent) hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  simp only [Width.words] at Ow
  change slot w.mem B kFlag = (if num v.mem B 2 1 = 1 then 1 else 0) at flag
  rw [gcd] at flag
  have coefficientW : num w.mem B 2 3 = num v.mem B 2 3 :=
    Ow.num (by decide) (by decide) (by simpa only [kw_words hv.width, Width.words] using
      (hv.runtime (w := .exponent) (by decide)).ws.fit64 (j := 3) (by decide))
  have compareFrame : Outs B (exponentTemps n) v.mem w.mem :=
    exponent_temps_keep width (by decide) (by decide) Ow
  have prefixFrame : OutsS B (s.gpr .esp) (exponentRanges n) s.mem w.mem :=
    (OutsS.of_outs divisionFrame).trans ((inverseFrame.trans (OutsS.of_outs compareFrame)).mono
      (fun r hr => List.mem_append_left _ hr))
  have Lw : num w.mem B n aL = L :=
    h.read_num (by decide) prefixFrame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have bit : slot w.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (lAtLeastTwo_ok hw bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  have maskFrame : Outs B (exponentTemps n) w.mem t.mem :=
    exponent_temps_keep (Nat.le_refl n) (by decide) (by decide) Ot
  have tailFrame := (inverseFrame.trans (OutsS.of_outs compareFrame)).trans (OutsS.of_outs maskFrame)
  have frame : OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem :=
    (OutsS.of_outs divisionFrame).trans (tailFrame.mono (fun r hr => List.mem_append_left _ hr))
  have coefficientT : num t.mem B 2 3 = num v.mem B 2 3 :=
    (exponent_mask_coefficient Ot).trans coefficientW
  have finalMask : slot t.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0) := by
    by_cases G : Nat.gcd (L % e) e = 1 <;> simpa [Lw, flag, G] using mask
  have tailOld : OutsS B (s.gpr .esp) (exponentTemps n) u.mem t.mem := tailFrame
  refine ⟨ht, frame, ⟨h.read_val32 (by decide) frame exponent_preserves_e, ?_, ?_, ?_, ?_, ?_, ?_, finalMask⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · exact h.read_num (by decide) frame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  · exact (h.read_num (by decide) tailOld (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)))).trans Q
  · exact (h.read_num (by decide) tailOld (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)))).trans R
  · rw [h.read_num (by decide) frame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide))), one]
  · rw [coefficientT]
    exact boundX
  · rw [coefficientT]
    exact congruence

end VG.Proof.RsaKeyGen.X86.KeyRuntime
