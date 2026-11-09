module
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers

import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! One checkpoint batch advances the exact scalar-multiplication invariant. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem PowersKeep.of_keeps {base : Addr} {o n : Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : PowersKeep base o n s t := by
  refine ⟨fun r hb hs hr => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hb h
    · exact hs h
    · exact hr h
  · rw [h.2.1]; exact TableFrame.refl _ _ _ _

theorem PowersKeep.of_rbx {base : Addr} {o n : Nat} {s t : State} (h : RbxKeep base s t) :
    PowersKeep base o n s t := ⟨fun r hb _ hr => h.gpr r hr hb, h.rd, h.wr, TableFrame.workspace h.mem⟩

theorem header_env {base : Addr} {m m' : Mem} (h : Outside base 56 8 m m') : env m' base = env m base := by
  funext i
  exact Outside_F h (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.X86_64
