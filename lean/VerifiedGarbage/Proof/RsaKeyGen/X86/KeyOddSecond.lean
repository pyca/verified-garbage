module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFlag
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeySelect

/-! # Canonicalize the LCM factors by a masked parity swap -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem oddSecond_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (oddSecond n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aU, aV] [kFlag] s.mem t.mem ∧
      num t.mem B n aU = (if num s.mem B n aV % 2 = 0 then num s.mem B n aV else num s.mem B n aU) ∧
      num t.mem B n aV = (if num s.mem B n aV % 2 = 0 then num s.mem B n aU else num s.mem B n aV) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  have fu := h.fit64 (j := aU) (by decide)
  have fv := h.fit64 (j := aV) (by decide)
  have ft := h.fit64 (j := aT1) (by decide)
  unfold oddSecond seqs
  refine WP.seq (WP.mono (evenFlag_ok h (by decide)) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have Uu : num u.mem B n aU = num s.mem B n aU :=
    Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fu
  have Vu : num u.mem B n aV = num s.mem B n aV :=
    Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fv
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide)) fun v ⟨hv, Ov, copied, Kv, _⟩ => ?_)
  have Uv : num v.mem B n aU = num s.mem B n aU := by rw [Ov.num (by decide) (by simp) fu, Uu]
  have Vv : num v.mem B n aV = num s.mem B n aV := by rw [Ov.num (by decide) (by simp) fv, Vu]
  have Tv : num v.mem B n aT1 = num s.mem B n aU := copied.trans Uu
  have flagV : slot v.mem B kFlag = slot u.mem B kFlag := Ov.slot hf (by simp)
  have bitV : slot v.mem B kFlag ≤ 1 := by rw [flagV, flag]; split <;> omega
  refine WP.seq (WP.mono (sel_ok hv (by decide) (by decide) (by decide) hf bitV)
    fun w ⟨hw, Ow, selectedU, Kw⟩ => ?_)
  have Vw : num w.mem B n aV = num s.mem B n aV := by rw [Ow.num (by decide) (by simp) fv, Vv]
  have Tw : num w.mem B n aT1 = num s.mem B n aU := by rw [Ow.num (by decide) (by simp) ft, Tv]
  have flagW : slot w.mem B kFlag = slot u.mem B kFlag := by rw [Ow.slot hf (by simp), flagV]
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [flagW, flag]; split <;> omega
  refine WP.mono (sel_ok hw (by decide) (by decide) (by decide) hf bitW)
    fun t ⟨ht, Ot, selectedV, Kt⟩ => ?_
  have U : num t.mem B n aU = if slot u.mem B kFlag = 0 then num s.mem B n aU else num s.mem B n aV := by
    rw [Ot.num (by decide) (by simp) fu, selectedU, flagV, Uv, Vv]
  have V : num t.mem B n aV = if slot u.mem B kFlag = 0 then num s.mem B n aV else num s.mem B n aU := by
    rw [selectedV, flagW, Vw, Tw]
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aU, aV]) (ds := [kFlag])).join Ow
    (js := [aT1, aU, aV]) (ds := [kFlag])).join Ot
    (js := [aT1, aU, aV]) (ds := [kFlag])), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans Kt))⟩
  · rw [U, flag]
    by_cases p : num s.mem B n aV % 2 = 0 <;> simp [p]
  · rw [V, flag]
    by_cases p : num s.mem B n aV % 2 = 0 <;> simp [p]

end VG.Proof.RsaKeyGen.X86.Key
