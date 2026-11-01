module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TablePointer
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TableWrites
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize exactly the table prefix the FFDH small-prime sieve uses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

def TableData (base : BitVec 32) (n : Nat) (m : Mem) : Prop :=
  ∀ i < 1024, w32 m (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i) = VG.Impl.RsaKeyGen.tabEntry i

theorem tableWrite_ok {s : State} {base : BitVec 32} {size n : Nat}
    (space : Workspace s base size) (bound : n ≤ 1024)
    (fit : arrAt ((n + 7) / 8) 34 + 4096 ≤ size)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12#32)) 4)
    (savedBase : s.mem.readW (State.addr s.sp) 32 = base)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s fun t =>
      TableData base n t.mem ∧
      Frame [⟨off (State.addr base) (arrAt ((n + 7) / 8) 34), 4096⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r7, .r11] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite, WP.block_append_iff]
  refine WP.mono (tablePointer_ok s base n bound readBase readWidth savedBase savedWidth) ?_
  rintro u ⟨⟨ptr, memory⟩, rest⟩
  refine WP.mono (tableWrites_ok (space.congr rest.wr) ptr 1024 (by decide) fit) ?_
  rintro t ⟨values, outside, keep⟩
  rw [memory] at outside
  exact ⟨values, VG.Proof.Bignum.outside_frame outside (by have := space.nowrap; omega),
    (rest.mono (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
