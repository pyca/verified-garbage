module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym

/-!
# Poly1305 on x86-64 with AVX-512: what integer instructions keep

`VKeep`: the vector registers (all 512 bits of each), MXCSR and the regions,
which a block of integer instructions leaves as they were, and the tactic
that closes what `simp` leaves of such a block.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64

/-- What a block of integer instructions leaves as it was: the vector
registers, MXCSR and the regions. -/
structure VKeep (s s' : State) : Prop where
  xmm : s'.xmm = s.xmm
  ymmHi : s'.ymmHi = s.ymmHi
  zmmHi : s'.zmmHi = s.zmmHi
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VKeep.qz_eq {s s' : State} (h : VKeep s s') (r : XReg) (k : Nat) : qz s' r k = qz s r k := by
  unfold qz State.zlane State.lane; rw [h.xmm, h.ymmHi, h.zmmHi]

theorem VKeep.trans {s₁ s₂ s₃ : State} (h₁ : VKeep s₁ s₂) (h₂ : VKeep s₂ s₃) : VKeep s₁ s₃ :=
  ⟨h₂.xmm.trans h₁.xmm, h₂.ymmHi.trans h₁.ymmHi, h₂.zmmHi.trans h₁.zmmHi, h₂.mxcsr.trans h₁.mxcsr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem se40 : BitVec.signExtend 64 (BitVec.ofNat 32 40) = 40 := by decide
theorem se128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
theorem se7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide

/-- Closes what `simp` leaves of a block of integer instructions. -/
macro "finish_gpr8" : tactic => `(tactic| plain_simp_names (
                   all_goals repeat' first | apply And.intro | apply VKeep.mk
                   all_goals first | trivial | rfl | (intros; simp [*])))

end VG.Proof.Poly1305.X86_64.Avx512
