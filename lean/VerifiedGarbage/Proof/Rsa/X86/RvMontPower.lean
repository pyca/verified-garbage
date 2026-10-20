module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontFrame
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Rsa.X86.RvMontClear

/-! # Computing Montgomery R squared inside the recovery workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys


theorem setupR2_ok {g : Geo} {m : Nat} {s : State} (h : MR g m s)
    (hm : 1 < m) (hn : g.n ≤ 128) :
    WP isa (setupR2 g.n) s fun t => MR g m t ∧
      Keep g.B g.w (montWrites mR2) [] s.mem t.mem ∧ Keeps opRegs s t ∧
      num t.mem g.B g.w mR2 = 2 ^ (128 * g.n) % m := by
  have positive := h.positive
  unfold setupR2
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.powerTwo_ok h.ws.workspace h.modulusReady
    (mont_layout h.ws (by decide : MontIndex mR2) (by decide) (by decide))
    (mont_bytes_sep (by decide : mR2 ≠ mBase)) hm (by omega) (by omega))
    fun u ⟨value, _, _, frame, r⟩ => ?_)
  have keep := mont_frame frame
  have ru : Keeps opRegs s u := r.mono (by decide)
  have hu := h.keep keep (by decide) ru
  refine WP.mono (clrTop_ok hu.ws (by decide : mR2 < nArr)) fun t ⟨_, kt, vt, rt⟩ => ?_
  exact ⟨hu.keep kt (by decide) (rt.mono (by decide)),
    keep.trans (kt.mono (by simp [montWrites]) (by simp)), ru.trans (rt.mono (by decide)), vt.trans value⟩

end VG.Proof.Rsa.X86.Recover
