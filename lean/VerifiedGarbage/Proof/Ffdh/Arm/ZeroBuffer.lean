module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.TCB.Arm.Isa

/-! Whole-range effects of native byte clearing, including final pointer positions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem zeroBuffer_ok (advance : Bool) (s : State) {src dst : BitVec 32} {n : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32) (destFits : dst.toNat + n ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) n) (zero : s.gpr .r2 = 0)
    (source : s.gpr .r1 = src) (dest : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (.loop (.block (if advance then VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep
      else VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep)) .ne) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      t.gpr .r0 = dst + BitVec.ofNat 32 n ∧ t.gpr .r1 = src + BitVec.ofNat 32 (if advance then n else 0) ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  refine WP.mono (zeroBytes_ok advance s (maskCtx_of_region s fits destFits write) positive zero source dest count) ?_
  intro t inv
  refine ⟨?_, inv.dest, inv.source, ?_, inv.rest⟩
  · calc
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = (List.range n).map (fun _ => (0 : Byte)) := by
        unfold Spec.Rsa.bytesAt
        apply List.map_congr_left
        intro j hj
        have hj' : j < n := List.mem_range.mp hj
        have value := inv.zeroed j hj'
        rw [addr_add (by omega)] at value
        exact value
      _ = List.replicate n 0 := by simp only [List.map_const', List.length_range]
  · intro a ha
    apply inv.outside a
    intro j hj he
    apply ha ⟨State.addr dst, n⟩ (by simp)
    rw [he, addr_add (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Ffdh.Arm
