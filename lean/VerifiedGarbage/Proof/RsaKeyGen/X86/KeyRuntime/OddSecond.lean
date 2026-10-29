module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.Omega
/-! # Canonicalize the LCM factors by a masked parity swap -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/EvenFlag.lean`, which only this module imported.
section

/-! # Negating the runtime parity bit uses the existing header frame -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem evenFlag_ok {s : State} {B : Addr} {Z n input : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) :
    WP isa (evenFlag input) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 0 then 1 else 0) ∧
      Keeps [.eax, .edx] s t := by
  unfold evenFlag
  refine WP.seq (WP.mono (bitOf_ok h hi (by decide)) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  refine wp_movS (readSrc_sc hu.old.workspace (d := kFlag) (by have := hu.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; unfold kFlag; omega))
    fun v V _ => wp_logicS (.inr rfl) rfl fun w W => ?_
  have K : Keeps [.eax, .edx] u w := (V.keeps.trans W.keeps).mono (by decide)
  have memory : w.mem = u.mem := W.mem.trans V.mem
  have hw := hu.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  refine WP.mono (store_slot hw (d := kFlag) (by decide) .eax) fun t ⟨ht, Ot, result, Kt⟩ => ?_
  rw [memory] at Ot
  refine ⟨ht, Ou.trans Ot, ?_, Ku.trans (K.trans (Kt.mono (by decide)))⟩
  rw [result, W.gpr, V.gpr]
  have bit : (u.mem.readW (off B kFlag) 32).toNat ≤ 1 := by
    change slot u.mem B kFlag ≤ 1
    rw [flag]; omega
  change (u.mem.readW (off B kFlag) 32 ^^^ (1 : BitVec 32)).toNat = _
  rw [VG.Proof.Rsa.KeyBits32.bv_xor_bits bit (by decide)]
  change (slot u.mem B kFlag + 1) % 2 = _
  rw [flag]
  have remainder := Nat.mod_lt (num s.mem B n input) (by decide : 0 < 2)
  split <;> omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag aU aV)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem oddSecond_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa oddSecond s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aU, aV] [kFlag] s.mem t.mem ∧
      num t.mem B n aU = (if num s.mem B n aV % 2 = 0 then num s.mem B n aV else num s.mem B n aU) ∧
      num t.mem B n aV = (if num s.mem B n aV % 2 = 0 then num s.mem B n aU else num s.mem B n aV) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
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
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide) (by decide)) fun v ⟨hv, Ov, copied, Kv, _⟩ => ?_)
  have Uv : num v.mem B n aU = num s.mem B n aU := by rw [Ov.num (by decide) (by simp) fu, Uu]
  have Vv : num v.mem B n aV = num s.mem B n aV := by rw [Ov.num (by decide) (by simp) fv, Vu]
  have Tv : num v.mem B n aT1 = num s.mem B n aU := copied.trans Uu
  have flagV : slot v.mem B kFlag = slot u.mem B kFlag := Ov.slot hf (by simp)
  have bitV : slot v.mem B kFlag ≤ 1 := by rw [flagV, flag]; split <;> omega
  refine WP.seq (WP.mono (sel_ok hv (by decide) (by decide) (by decide) hf bitV (by decide))
    fun w ⟨hw, Ow, selectedU, Kw⟩ => ?_)
  have Vw : num w.mem B n aV = num s.mem B n aV := by rw [Ow.num (by decide) (by simp) fv, Vv]
  have Tw : num w.mem B n aT1 = num s.mem B n aU := by rw [Ow.num (by decide) (by simp) ft, Tv]
  have flagW : slot w.mem B kFlag = slot u.mem B kFlag := by rw [Ow.slot hf (by simp), flagV]
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [flagW, flag]; split <;> omega
  refine WP.mono (sel_ok hw (by decide) (by decide) (by decide) hf bitW (by decide))
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

end VG.Proof.RsaKeyGen.X86.KeyRuntime
