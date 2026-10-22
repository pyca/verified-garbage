module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The entropy availability comparison is exact and cannot underflow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessAvailable
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessAvailable

theorem codeAt_ok {s : State} {base : Addr} {size D remaining used : Nat}
    (S : Scr s base size) (head : 256 ≤ size) (width : D < 2 ^ 32)
    (length : w32 s.mem base 32 = remaining) (consumed : w32 s.mem base 152 = used)
    (bound : used ≤ remaining) :
    WP isa (.block (codeAt D)) s fun t =>
      t.cf = some (decide (remaining - used < D)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold codeAt
  refine wp_movS (readSrc_sc S (by omega)) fun a A _ => ?_
  have Sa := S.of_keeps A.keeps (by decide)
  refine wp_subS (readSrc_sc Sa (d := 152) (by omega)) fun b B _ => ?_
  have value : (b.gpr .eax).toNat = remaining - used := by
    rw [B.gpr, A.gpr, A.mem, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change w32 s.mem base 152 ≤ w32 s.mem base 32; rw [length, consumed]; exact bound)]
    change w32 s.mem base 32 - w32 s.mem base 152 = _
    rw [length, consumed]
  refine wp_cmpi fun t T carry _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans (T.keeps _)⟩
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt width] at carry
  exact carry

theorem code_ok {s : State} {base : Addr} {size w remaining used : Nat}
    (S : Scr s base size) (head : 256 ≤ size) (width : 8 * w < 2 ^ 32)
    (length : w32 s.mem base 32 = remaining) (consumed : w32 s.mem base 152 = used)
    (bound : used ≤ remaining) :
    WP isa (.block (code w)) s fun t =>
      t.cf = some (decide (remaining - used < 8 * w)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t :=
  codeAt_ok S head width length consumed bound

end VG.Proof.RsaKeyGen.X86.WitnessAvailable
