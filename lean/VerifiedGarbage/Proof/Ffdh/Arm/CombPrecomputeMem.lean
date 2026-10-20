module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst

/-! Silent public argument preparation retains the builder state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem Memory.of_mem {p : Inputs} {sp : BitVec 32} {s t : State} {rs : List Reg}
    (h : Memory p sp s) (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base) :
    Memory p sp t := by
  refine ⟨h.context.of_mem mem rest ptr,h.ready.of_mem mem rest ptr,h.calls.after rest,
    rest.sp.trans h.fixed,h.output.after rest,h.workspaceSeparate,h.domainSeparate,h.localSeparate,
    h.callSeparate,?_,?_⟩
  · rw [mem]; exact h.bitsSaved
  · rw [mem]; exact h.rowsSaved

theorem Core.of_mem {p : Inputs} {sp : BitVec 32} {s t : State} {rs : List Reg}
    (h : Core p sp s) (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base) : Core p sp t := by
  refine ⟨h.memory.of_mem mem rest ptr,?_,h.odd,?_,?_⟩ <;> rw [mem]
  exacts [h.modulus,h.r2,h.one]

theorem Power5.of_mem {p : Inputs} {s t : State} {exponent : Nat}
    (h : Power5 p exponent s) (mem : t.mem = s.mem) : Power5 p exponent t := by
  change _ = _
  rw [mem]
  exact h

end VG.Proof.Ffdh.Arm.CombBuilder
