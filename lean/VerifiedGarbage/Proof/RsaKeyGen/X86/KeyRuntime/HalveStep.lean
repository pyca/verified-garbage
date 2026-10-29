module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
/-! # A native step of the shared LCM halving algorithm -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Even.lean`, which only this module imported.
section

/-! # Common parity at a public runtime width -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (aU aV kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem bothEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block bothEven) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag =
        (if num s.mem B n aU % 2 = 0 ∧ num s.mem B n aV % 2 = 0 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have fu := h.arr_fit (j := aU) (by decide)
  have fv := h.arr_fit (j := aV) (by decide)
  have nowrap := h.old.workspace.nowrap
  unfold bothEven
  refine h.ptr_ok (arr aU) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fu; omega)
    fun u Ku mu Pu => ?_
  have hu := h.keep Ku (by rw [mu]; exact Outside.refl _ _ _ _)
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr hu.full.rt Pu (d := 0)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fu; omega))
    fun v V _ => ?_
  have Kv : Keeps [.eax, .ecx, .edx] s v := (Ku.mono (by decide)).trans (V.keeps.mono (by decide))
  have mv : v.mem = s.mem := V.mem.trans mu
  have hv := h.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.ptr_ok (arr aV) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fv; omega)
    fun w Kw mw Pw => ?_
  have hw := hv.keep Kw (by rw [mw]; exact Outside.refl _ _ _ _)
  refine wp_orS (VG.Proof.Mont.X86.Rt.readSrc_ptr hw.full.rt Pw (d := 0)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fv; omega))
    fun x X => ?_
  refine wp_logicS (.inl rfl) rfl fun y Y => wp_logicS (.inr rfl) rfl fun z Zf => ?_
  have K : Keeps [.eax, .ecx, .edx] s z := (Kv.trans (Kw.mono (by decide))).trans
    ((X.keeps.mono (by decide)).trans ((Y.keeps.mono (by decide)).trans (Zf.keeps.mono (by decide))))
  have memory : z.mem = s.mem := Zf.mem.trans (Y.mem.trans (X.mem.trans (mw.trans mv)))
  have hz := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have value : z.gpr .ecx =
      ((s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n aU)) 32 |||
        s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n aV)) 32) &&& (1 : BitVec 32)) ^^^ 1 := by
    rw [Zf.gpr, Y.gpr, X.gpr, Kw.1 _ (by decide), V.gpr, mw, V.mem, mu,
      Nat.add_zero, arr, offset_array, Width.words, arr, offset_array, Width.words]
    rfl
  refine WP.mono (store_slot hz (d := kFlag) (by decide) .ecx) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, value, VG.Proof.RsaKeyGen.X86.Key.even_bit,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity _ _ h.wpos aU,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity _ _ h.wpos aV]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Half.lean`, which only this module imported.
section

/-! # Conditional halving for the native RSA LCM schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag aPa aQa aPm aQm aPhi aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem halfIf_ok {s : State} {B : Addr} {Z n j : Nat}
    (h : Ws s B Z n 32) (hj : j < 31) (bit : slot s.mem B kFlag ≤ 1) :
    WP isa (halfIf j) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aHalf, j] [] s.mem t.mem ∧
      num t.mem B n j = (if slot s.mem B kFlag = 0 then num s.mem B n j else num s.mem B n j / 2) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  have fj := h.fit64 (j := j) (by omega)
  unfold halfIf seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by omega) (by unfold aHalf; omega)) fun u ⟨hu, Ou, copied, Ku, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  have hv := hu.keep V.keeps (by rw [V.mem]; exact Outside.refl _ _ _ _)
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
  refine WP.mono (sel_ok hw (by omega) (by omega) (by decide) hf (by rw [flagW]; exact bit) (by right; unfold aHalf; omega))
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  have middle : Keep B n [aHalf] [] u.mem w.mem := by rw [V.mem] at Ow; exact Ow
  exact ⟨ht, (Ou.trans middle).join Ot (js := [aHalf, j]) (ds := []),
    by rw [selected, flagW, valueW, halved],
    (Ku.mono (by decide)).trans ((V.keeps.mono (by decide)).trans
      ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV aPhi aPm aQm aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def triple (m : Mem) (B : Addr) (n : Nat) : Nat × Nat × Nat :=
  (num m B n aU, num m B n aV, num m B n aPhi)

def halveArrays : List Nat := [aHalf, aU, aV, aPhi]

theorem halveStep_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (Impl.RsaKeyGen.X86.KeyRuntime.halveStep) s fun t =>
      Ws t B Z n 32 ∧ Keep B n halveArrays [kFlag] s.mem t.mem ∧
      triple t.mem B n = VG.Proof.RsaKeyGen.halveStep (triple s.mem B n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  have fu := h.fit64 (j := aU) (by decide)
  have fv := h.fit64 (j := aV) (by decide)
  have ff := h.fit64 (j := aPhi) (by decide)
  unfold Impl.RsaKeyGen.X86.KeyRuntime.halveStep VG.Impl.Rsa.X86.Keys.seqs
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

end VG.Proof.RsaKeyGen.X86.KeyRuntime
