module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SetWord
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Mont.Words32

/-! Workspace word initialization preserves the shared runtime arithmetic arguments. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem runtime_word {L : Lay} {s : State} {base : Addr} {bytes len count d value : Nat}
    (h : RtWs L s base bytes len count) (fit : d + 4 ≤ bytes) :
    WP isa (.block (setHeader d value)) s fun t =>
      RtWs L t base bytes len count ∧ t.mem = s.mem.writeW (off base d) (BitVec.ofNat 32 value) ∧
      Outside base d 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (set_word h.ws.workspace fit) fun t ⟨memory, _, K⟩ => ?_
  have outside : Outside base d 4 s.mem t.mem := by
    rw [memory]
    exact writeW32_outside _ _ _ (by have := h.ws.workspace.nowrap; omega)
  exact ⟨h.keep K (by decide) (by decide) (outside.mono (by omega) (by omega)), memory, outside, K⟩

end VG.Proof.Dsa.X86.Generation
