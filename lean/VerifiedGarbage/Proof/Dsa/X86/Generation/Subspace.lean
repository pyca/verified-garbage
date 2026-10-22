module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Permissions
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega

/-! Use a bounded part of the generation scratch as an existing workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem workspace_slice {s t : State} {base : Addr} {bytes offset size : Nat}
    (scr : Scr s base bytes) (fit : offset + size ≤ bytes) (offsetLt : offset < bytes)
    (pointer : t.gpr .edi = s.gpr .edi + BitVec.ofNat 32 offset)
    (stack : t.gpr .esp = s.gpr .esp)
    (write : (⟨off base offset, size⟩ : Region) ∈ t.wr) :
    Scr t (off base offset) size := by
  have nw := scr.nowrap
  have offset64 : offset < 2 ^ 64 := by omega
  have baseOffset : (off base offset).toNat = base.toNat + offset := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt offset64, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, write, by rw [baseOffset]; omega, ?_⟩
  · rw [pointer]
    exact scr.ea offsetLt
  · rw [stack]
    have original := scr.stk
    simp only [StkOk] at original ⊢
    rw [baseOffset]
    omega

theorem workspace_slice_covers {s : State} {base : Addr} {bytes offset size : Nat}
    (scr : Scr s base bytes) (fit : offset + size ≤ bytes) :
    Covers [⟨off base offset, size⟩] s.wr := by
  apply Covers.of_sub
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨⟨base, bytes⟩, scr.wr, offset, rfl, fit⟩

theorem workspace_prefix {s : State} {base : Addr} {bytes size : Nat}
    (scr : Scr s base bytes) (fit : size ≤ bytes) :
    Scr (s.withRegions s.rd [⟨base, size⟩]) base size := by
  refine ⟨scr.edi, List.mem_singleton_self _, by have := scr.nowrap; omega, ?_⟩
  have stack := scr.stk
  change StkOk (s.gpr .esp) base size
  simp only [StkOk] at stack ⊢
  omega

theorem workspace_prefix_covers {s : State} {base : Addr} {bytes size : Nat}
    (scr : Scr s base bytes) (fit : size ≤ bytes) : Covers [⟨base, size⟩] s.wr := by
  apply Covers.of_sub
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨⟨base, bytes⟩, scr.wr, 0, by simp, by simpa only [Nat.zero_add] using fit⟩

theorem workspace_pointer_fits {s : State} {base : Addr} {bytes offset size : Nat}
    (scr : Scr s base bytes) (fit : offset + size ≤ bytes) (positive : 0 < size) :
    (s.gpr .edi + BitVec.ofNat 32 offset).toNat + size ≤ 2 ^ 32 := by
  have nowrap := scr.nowrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, scr.edi_toNat,
    Nat.mod_eq_of_lt (by omega : offset < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  omega

end VG.Proof.Dsa.X86.Generation
