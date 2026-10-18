module

public import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # The initial recovery validity test -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Rsa.KeyBits32

theorem KS.skipTest_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (hb : sBit ∈ ls)
    (bit : V sBit ≤ 1) (borrow : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block skipTest) s fun t => KS g s0 A live AW liveW V ls t ∧
      t.zf = some (decide (V sBit = 1 ∧ (s.gpr .ebx).toNat = 1)) := by
  unfold skipTest
  refine wp_movS (h.readSlot hb) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inl rfl) rfl fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : v.gpr .eax = BitVec.ofNat 32 (if V sBit = 1 ∧ (s.gpr .ebx).toNat = 1 then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [D.gpr, ite_eq_left rfl, U.gpr, U.other .ebx (by decide),
      bv_and_bits (by rw [BitVec.toNat_ofNat]; omega) borrow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : V sBit < 2 ^ 32)]
    split <;> rfl
  refine wp_cmpS rfl fun t T Z => WP.block_nil ⟨hv.of_rest (T.keeps []) (by simp) T.mem, ?_⟩
  rw [Z, value]
  by_cases cond : V sBit = 1 ∧ (s.gpr .ebx).toNat = 1 <;> simp [cond]

end VG.Proof.Rsa.X86.Recover
