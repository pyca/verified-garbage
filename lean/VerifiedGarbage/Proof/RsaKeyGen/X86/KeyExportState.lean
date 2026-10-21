module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap

/-! # Each masked output retains the header, zero array and validity bit for the next port -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure ExportState (E : Environment) (s : State) : Prop where
  input : Input E s
  zero : num s.mem E.base E.n aZero = 0
  bit : slot s.mem E.base kOk ≤ 1

theorem ExportState.port_ok {E : Environment} {s : State} (h : ExportState E s) {i : Nat} (hi : i < 7) :
    WP isa (writePort E.n i) s fun t =>
      ExportState E t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let accept := decide (slot s.mem E.base kOk = 1)
  have mask : slot s.mem E.base kOk = if accept then 1 else 0 := by
    unfold accept
    split <;> have := h.bit <;> simp_all <;> omega
  refine WP.mono (writePort_ok h.input.outputs hi h.zero accept mask)
    fun t ⟨ht, _, _, header, other, K⟩ => ?_
  change ∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d at header
  have input : Input E t := h.input.keep ht.ws K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega))
  have zero := (other aZero (by decide) (outputIndex_zero hi)).trans h.zero
  have bit : slot t.mem E.base kOk ≤ 1 := by
    rw [header kOk (by decide)]
    exact h.bit
  exact ⟨⟨input, zero, bit⟩, K⟩

end VG.Proof.RsaKeyGen.X86.Key
