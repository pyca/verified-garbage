module

public import VerifiedGarbage.Impl.Rc2.X86_64.Lookup
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! # Correctness of baseline x86-64 RC2 lookup steps -/

@[expose] public section

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem byte_imm (b : Byte) : (b.setWidth 32).signExtend 64 = b.setWidth 64 := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp
  · simp [BitVec.msb_setWidth]

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 32 i).signExtend 64 = (BitVec.ofNat 8 i).setWidth 64 := by
  have h : BitVec.ofNat 32 i = (BitVec.ofNat 8 i).setWidth 32 := by bv_omega
  rw [h, byte_imm]

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (Int.ofNat i) = BitVec.ofNat 64 i := by
  rfl

theorem maskIndex (x : BitVec 64) :
    x &&& 63 = (x.setWidth 6).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 6 - 1) = x.toNat % 64 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

end VG.Proof.Rc2.X86_64
