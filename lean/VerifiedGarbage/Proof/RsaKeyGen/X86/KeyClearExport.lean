module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportState
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Clear the output-mask zero array independently of inverse scratch contents -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Impl.Mont.X86.Dynamic

theorem clearExport_ok {E : Environment} {s : State} (h : Input E s) (bit : slot s.mem E.base kOk ≤ 1) :
    WP isa (zerosW (VG.Impl.Rsa.X86.Keys.slot E.n aZero) (E.n + 2)) s fun t =>
      ExportState E t ∧ Keeps [.eax, .ebp, .edx] s t := by
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  refine WP.mono (zerosW_ok h.ws.workspace (by omega) fits) fun t ⟨O, zero, K⟩ => ?_
  change Outside E.base (arr E.n aZero) (S E.n) s.mem t.mem at O
  change val32 t.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  have clear : Keep E.base E.n [aZero] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O) (by unfold S; omega) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  have input : Input E t := h.keep (h.ws.rest K) K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega))
  have lowZero : num t.mem E.base E.n aZero = 0 := by
    have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using H
  exact ⟨⟨input, lowZero, by rw [header kOk (by decide)]; exact bit⟩, K⟩

end VG.Proof.RsaKeyGen.X86.Key
