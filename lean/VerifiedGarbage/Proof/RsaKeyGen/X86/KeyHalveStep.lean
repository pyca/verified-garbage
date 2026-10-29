module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyPrimes
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyHalf
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # A native step of the shared LCM halving algorithm -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyHalf.lean`, which only this module imported.
section

/-! # Conditional halving for the native RSA LCM schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem halfIf_ok {s : State} {B : Addr} {Z n j : Nat}
    (h : Ws s B Z n 32) (hj : j < 31) (bit : slot s.mem B kFlag ≤ 1) :
    WP isa (halfIf n j) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aHalf, j] [] s.mem t.mem ∧
      num t.mem B n j = (if slot s.mem B kFlag = 0 then num s.mem B n j else num s.mem B n j / 2) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  have fj := h.fit64 (j := j) (by omega)
  unfold halfIf seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by omega)) fun u ⟨hu, Ou, copied, Ku, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  have hv := hu.rest V.keeps
  have zero : (v.gpr .ebx).toNat ≤ 1 := by rw [V.gpr]; decide
  refine WP.seq (WP.mono (half_ok hv (by decide) zero) fun w ⟨hw, Ow, halved, Kw⟩ => ?_)
  have ev : (v.gpr .ebx).toNat = 0 := by rw [V.gpr]; rfl
  rw [V.mem, ev, Nat.mul_zero, Nat.add_zero, copied] at halved
  have valueU : num u.mem B n j = num s.mem B n j :=
    Ou.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aHalf; omega) (by simp) fj
  have valueW : num w.mem B n j = num s.mem B n j := by
    rw [Ow.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aHalf; omega) (by simp) fj,
      V.mem, valueU]
  have flagW : slot w.mem B kFlag = slot s.mem B kFlag := by
    rw [Ow.slot hf (by simp), V.mem, Ou.slot hf (by simp)]
  refine WP.mono (sel_ok hw (by omega) (by omega) (by decide) hf (by rw [flagW]; exact bit))
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  have middle : Keep B n [aHalf] [] u.mem w.mem := by rw [V.mem] at Ow; exact Ow
  exact ⟨ht, (Ou.trans middle).join Ot (js := [aHalf, j]) (ds := []),
    by rw [selected, flagW, valueW, halved],
    (Ku.mono (by decide)).trans ((V.keeps.mono (by decide)).trans
      ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def triple (m : Mem) (B : Addr) (n : Nat) : Nat × Nat × Nat :=
  (num m B n aU, num m B n aV, num m B n aPhi)

def halveArrays : List Nat := [aHalf, aU, aV, aPhi]

theorem halveStep_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (Impl.RsaKeyGen.X86.Key.halveStep n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n halveArrays [kFlag] s.mem t.mem ∧
      triple t.mem B n = VG.Proof.RsaKeyGen.halveStep (triple s.mem B n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  have fu := h.fit64 (j := aU) (by decide)
  have fv := h.fit64 (j := aV) (by decide)
  have ff := h.fit64 (j := aPhi) (by decide)
  unfold Impl.RsaKeyGen.X86.Key.halveStep VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (bothEven_ok h) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have Uu : num u.mem B n aU = num s.mem B n aU := Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fu
  have Vu : num u.mem B n aV = num s.mem B n aV := Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fv
  have Fu : num u.mem B n aPhi = num s.mem B n aPhi := Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) ff
  have bitU : slot u.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.seq (WP.mono (halfIf_ok hu (by decide) bitU) fun v ⟨hv, Ov, halfU, Kv⟩ => ?_)
  have Vv : num v.mem B n aV = num s.mem B n aV := by rw [Ov.num (by decide) (by simp) fv, Vu]
  have Fv : num v.mem B n aPhi = num s.mem B n aPhi := by rw [Ov.num (by decide) (by simp) ff, Fu]
  have flagV : slot v.mem B kFlag = slot u.mem B kFlag := Ov.slot hf (by simp)
  have bitV : slot v.mem B kFlag ≤ 1 := by rw [flagV]; exact bitU
  refine WP.seq (WP.mono (halfIf_ok hv (by decide) bitV) fun w ⟨hw, Ow, halfV, Kw⟩ => ?_)
  have Uw : num w.mem B n aU = num v.mem B n aU := Ow.num (by decide) (by simp) fu
  have Fw : num w.mem B n aPhi = num s.mem B n aPhi := by rw [Ow.num (by decide) (by simp) ff, Fv]
  have flagW : slot w.mem B kFlag = slot u.mem B kFlag := by rw [Ow.slot hf (by simp), flagV]
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [flagW]; exact bitU
  refine WP.mono (halfIf_ok hw (by decide) bitW) fun t ⟨ht, Ot, halfF, Kt⟩ => ?_
  have Ut : num t.mem B n aU = num v.mem B n aU := by rw [Ot.num (by decide) (by simp) fu, Uw]
  have Vt : num t.mem B n aV = num w.mem B n aV := Ot.num (by decide) (by simp) fv
  refine ⟨ht, (((Ou.join Ov (js := halveArrays) (ds := [kFlag])
    (by simp) (by simp) (by simp [halveArrays]) (by simp)).join Ow
    (js := halveArrays) (ds := [kFlag]) (by simp) (by simp) (by simp [halveArrays]) (by simp)).join Ot
    (js := halveArrays) (ds := [kFlag]) (by simp) (by simp) (by simp [halveArrays]) (by simp)), ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans Kt))⟩
  · unfold triple
    rw [Ut, Vt, halfU, halfV, halfF, flagV, flagW, Uu, Vv, Fw, flag]
    unfold VG.Proof.RsaKeyGen.halveStep
    by_cases p : num s.mem B n aU % 2 = 0 ∧ num s.mem B n aV % 2 = 0
    · simp [p]
    · simp [p]

end VG.Proof.RsaKeyGen.X86.Key
