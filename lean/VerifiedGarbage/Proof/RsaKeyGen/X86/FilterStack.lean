module

import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack

/-! # Private native frames for candidate filters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FilterStack
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem allocated_scratch {base : Addr} {size bytes : Nat} {s : State} (S : Scr s base size)
    (fit : bytes + 20 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + bytes + 20 ≤ (s.gpr .esp).toNat) :
    Scr (allocFrame bytes s) base size := by
  refine ⟨?_, List.mem_cons_of_mem _ S.wr, S.nowrap, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide)]; exact S.edi
  · change 20 ≤ (s.gpr .esp - BitVec.ofNat 32 bytes).toNat ∧
      ((s.gpr .esp - BitVec.ofNat 32 bytes).toNat ≤ base.toNat ∨
        base.toNat + size + 20 ≤ (s.gpr .esp - BitVec.ofNat 32 bytes).toNat)
    rw [sub_toNat (by omega)]
    rcases separate with h | h <;> constructor <;> omega

theorem allocated_workspace {s : State} {bytes : Nat} (fit : bytes ≤ (s.gpr .esp).toNat) :
    Ws (allocFrame bytes s) ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64) bytes := by
  refine ⟨List.mem_cons_self, ?_⟩
  rw [BitVec.toNat_setWidth, sub_toNat fit, Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]
  have := (s.gpr .esp).isLt
  omega

theorem allocated_context {s : State} (fit : 20 ≤ (s.gpr .esp).toNat) :
    Sieve.StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
  ⟨allocated_workspace fit, allocFrame_esp _ _⟩

theorem allocated_apart {base : Addr} {size bytes : Nat} {s : State}
    (fit : bytes ≤ (s.gpr .esp).toNat) (nowrap : base.toNat + size ≤ 2 ^ 32)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + bytes ≤ (s.gpr .esp).toNat) :
    (⟨base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ := by
  have natEq : ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat = (s.gpr .esp).toNat - bytes := by
    rw [BitVec.toNat_setWidth, sub_toNat fit, Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]
  rcases separate with h | h
  · apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat + bytes ≤ base.toNat
      rw [natEq]; omega
    · exact Nat.le_trans nowrap (by decide)
  · apply Offset.disjoint_of_le
    · change base.toNat + size ≤ ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat
      rw [natEq]; omega
    · change ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64).toNat + bytes ≤ 2 ^ 64
      rw [natEq]; have := (s.gpr .esp).isLt; omega

theorem freed_keeps {s t : State} {bytes : Nat} {rs : List Reg}
    (K : Keeps rs (allocFrame bytes s) t) (sp : .esp ∉ rs) : Keeps rs s (freed bytes t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r mem
    by_cases h : r = .esp
    · subst r
      rw [freed_esp, K.1 .esp sp, allocFrame_esp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ h, K.1 r mem, allocFrame_gpr _ _ h]
  · rw [freed_rd, K.2.1, allocFrame_rd]
  · rw [freed_wr, K.2.2, allocFrame_wr]; rfl

end VG.Proof.RsaKeyGen.X86.FilterStack
