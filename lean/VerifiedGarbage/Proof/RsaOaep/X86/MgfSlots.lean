module

public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP on x86: `mgfXor`'s slots

`Sl`: the slots of `mgfXor`'s parameters (`src`, `dst` and their lengths),
which `dbArgs` and `seedArgs` set; what `mgfXor` writes misses them
(`mgfW_slot`, `sl_keep`) and the bytes of `EM` outside `dst` (`mgfW_byte`);
and `mgf_vp`'s parameters from them (`mpOf`), as on ARMv7.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (oCW oSt oDig oEm oRsa frameBytes sCtr sDone)

section
variable {L : Lay} {scr : BitVec 32} (g : OHash)

/-- The slots of `mgfXor`'s parameters. -/
abbrev Sl (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (m : Mem) : Prop :=
  m.readW (L.fr sSrc) 32 = scr + BitVec.ofNat 32 so ∧ m.readW (L.fr sSrcLen) 32 = BitVec.ofNat 32 sl ∧
    m.readW (L.fr sDst) 32 = scr + BitVec.ofNat 32 dOff ∧ m.readW (L.fr sDstLen) 32 = BitVec.ofNat 32 dl

/-- A slot other than the counter's and the bytes masked misses what
`mgfXor` writes. -/
theorem mgfW_slot (hg : Geo L scr) {dOff dl d : Nat} (hfd : dOff + dl ≤ oBuf) (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d) : ∀ r ∈ mgfW g L scr dOff dl, (slotR L d).Disjoint r := by
  have := g.S_le; have := g.Wb_le; have := g.F_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hF : d + 4 ≤ L.F + 16 := by rw [hg.F]; unfold frameBytes at hd ⊢; omega
  intro r hr
  simp only [mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.slot ok (by oomega) hF
  · exact hg.slot ok (by oomega) hF
  · exact hg.slot ok (by oomega) hF
  · exact hg.slot ok (by oomega) hF
  · exact Lay.fr_low (by unfold frameBytes at hd; omega) (by have := ok.BC; have := L.B.isLt; omega)
  · exact hg.slot ok (by oomega) hF
  · exact slotSep hd (by decide) (by unfold sCtr sDone at *; omega)
  · exact slotSep hd (by decide) (by unfold sCtr sDone at *; omega)

/-- A byte of `EM`'s place, outside `dst`, misses what `mgfXor` writes. -/
theorem mgfW_byte (hg : Geo L scr) {dOff dl o : Nat} (hfd : dOff + dl ≤ oBuf) (ho0 : oEm ≤ o) (ho : o < oRsa)
    (hx : o + 1 ≤ dOff ∨ dOff + dl ≤ o) : ∀ r ∈ mgfW g L scr dOff dl, (sR scr o 1).Disjoint r := by
  have := g.S_le; have := g.Wb_le; have := g.F_le
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact hg.low ok (by oomega)
  · exact Geo.sep hx (by oomega) (by oomega)
  · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
  · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

theorem sl_keep (hg : Geo L scr) {so sl dOff dl : Nat} (hfd : dOff + dl ≤ oBuf) {m m' : Mem}
    (hf : Frame (mgfW g L scr dOff dl) m m') (hs : Sl L scr so sl dOff dl m) : Sl L scr so sl dOff dl m' :=
  ⟨slot_keep hf (mgfW_slot g hg hfd (by decide) (by decide)) hs.1,
    slot_keep hf (mgfW_slot g hg hfd (by decide) (by decide)) hs.2.1,
    slot_keep hf (mgfW_slot g hg hfd (by decide) (by decide)) hs.2.2.1,
    slot_keep hf (mgfW_slot g hg hfd (by decide) (by decide)) hs.2.2.2⟩

/-- `mgfXor`'s parameters, from the slots and what the caller keeps. -/
theorem mpOf (hg : Geo L scr) {so sl dOff dl : Nat} (sl0 : 0 < sl) (dl0 : 0 < dl) (so0 : oEm ≤ so)
    (do0 : oEm ≤ dOff) (fs : so + sl ≤ oBuf) (fd : dOff + dl ≤ oBuf) (sep : so + sl ≤ dOff ∨ dOff + dl ≤ so)
    {seed : State → List Byte} (sd : ∀ σ, (seed σ).length = sl) {X : State → Mem → Prop}
    (hX : ∀ σ m m', X σ m → Frame (mgfW g L scr dOff dl) m m' → X σ m') :
    MP g L scr so sl dOff dl seed (fun σ m => X σ m ∧ Sl L scr so sl dOff dl m) :=
  ⟨hg, sl0, dl0, so0, do0, fs, fd, sep, sd, fun σ m m' ⟨hx, hs⟩ hf => ⟨hX σ m m' hx hf, sl_keep g hg fd hf hs⟩,
    fun _ _ h => h.2.1, fun _ _ h => h.2.2.1, fun _ _ h => h.2.2.2.1, fun _ _ h => h.2.2.2.2⟩

end

end VG.Proof.RsaOaep.X86
