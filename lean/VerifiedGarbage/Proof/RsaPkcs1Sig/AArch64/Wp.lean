import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# RSA signatures on AArch64: the instructions on the stack

Weakest-precondition rules, in the continuation style of
`Proof/MlKem/AArch64/Wp.lean`, for the instructions that address the stack
(`addSp`, `ldrSp`) and for `mov` (`addImm` of 0), and what a block of the
callers' code keeps.
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo only_write write_x_gpr)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.sp + BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, h]) k

theorem wp_ldrSp {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8)
    (k : ∀ s', Only [t] s s' → s'.gpr t = s.mem.readW (s.sp + BitVec.ofNat 64 off) 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by
    simp only [exec, ho, and_self, ite_true, State.load, hin, Option.map_some, Mem.readW]) k

theorem wp_mov {d n : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n 0 :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s' h e => k s' h (by rw [e]; exact BitVec.add_zero _)

end

end VG.Proof.RsaPkcs1Sig.AArch64
