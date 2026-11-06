module

import VerifiedGarbage.Proof.Ed25519.X86_64.PointSelect
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulateLoop
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit

/-! Merged from `Proof.Ed25519.X86_64.PointAccumulate`. -/

@[expose] public section

section
/-! One masked point addition, with all memory indices public. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off mask Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem Keep.of_table {base : Addr} {s t : State}
    (h : TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith))

theorem Keep.bit {base : Addr} {s t : State} (h : Keep base s t) (i : Nat) (hi : i < 512) :
    t.mem (off base (768 + i)) = s.mem (off base (768 + i)) :=
  h.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)

end VG.Proof.Ed25519.X86_64
end

/-! The descending-bit loop follows the specification exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

theorem accumulateDec_ok (s : State) (n : Nat)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s t := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hc, e, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.Ed25519.X86_64
