module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticAllocated
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset

/-! The reusable argument frame leaves every staged arithmetic number intact. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Ws num arr S)

theorem ArithmeticSetup.num_keep {s t : State} {base : Addr} {bytes len count j : Nat}
    (H : ArithmeticSetup s t) (ws : Ws s base bytes (kw len) count)
    (apart : Region.Disjoint (below (s.gpr .esp) 16) ⟨base, bytes⟩) (index : j < count) :
    num t.mem base (kw len) j = num s.mem base (kw len) j := by
  have fit := ws.arr_fit index
  have nowrap := ws.workspace.nowrap
  have words := ws.wle
  change val32 t.mem base (arr (kw len) j) (kw len) = val32 s.mem base (arr (kw len) j) (kw len)
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  apply congrArg BitVec.toNat
  apply H.frame.read (r := ⟨base, bytes⟩) (Offset.contains_base _ (by unfold S at fit; omega) (by omega)) ?_ (by omega)
  intro region hr
  rw [List.mem_singleton.mp hr]
  exact apart.symm

end VG.Proof.Dsa.X86.Generation
