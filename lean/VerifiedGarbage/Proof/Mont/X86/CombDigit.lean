module

import VerifiedGarbage.Proof.Mont.X86.CombDigitControl
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Mont.X86.CombPower
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Mont.X86.CombTooth

/-! The five fixed-position comb bits form a bounded table index. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.FixedBaseComb (bit bit_lt)

def partialDigit (d x : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => partialDigit d x j + bit x ((j+1)*d-1)*2^j

theorem partialDigit_lt (d x j : Nat) : partialDigit d x j<2^j := by
  induction j with
  | zero => exact Nat.zero_lt_one
  | succ j ih =>
    have h := Nat.mul_le_mul_right (2^j) (show bit x ((j+1)*d-1)≤1 from by have := bit_lt x ((j+1)*d-1); omega)
    simp only [Nat.one_mul] at h
    rw [partialDigit,Nat.pow_succ]; omega

/-- Zero padding and repeated shifts expose the original exponent's comb row. -/
theorem partialDigit_shifted (bits x width row : Nat)
    (hr : row<Spec.Rsa.FixedBaseComb.rows bits) (hw : 5*Spec.Rsa.FixedBaseComb.rows bits≤width) :
    partialDigit (Spec.Rsa.FixedBaseComb.rows bits)
      ((x*2^(Spec.Rsa.FixedBaseComb.rows bits-1-row))%2^width) 5 =
      VG.Proof.Rsa.FixedBaseComb.digit bits x row := by
  simp only [partialDigit]
  rw [VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 0 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 1 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 2 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 3 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 4 hr (by decide) hw]
  simp only [VG.Proof.Rsa.FixedBaseComb.digit,Nat.zero_mul,Nat.add_zero,Nat.one_mul,
    Nat.pow_zero,Nat.mul_one,Nat.zero_add]
  omega

theorem digitParts_ok {s : State} {base : Addr} {size o k d : Nat}
    (hs : Scr s base size) (ho : o+4*k≤size) (hd : 0<d) (cover : 5*d≤32*k)
    (B : s.gpr .ebx=0) : ∀ j, j≤5 →
    WP isa (.block ((List.range j).flatMap (fun j =>
      toothRead o ((j+1)*d-1) ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
      ([.alu .or .ebx (.reg .eax)] : List Instr)))) s fun t =>
      t.mem=s.mem ∧ (t.gpr .ebx).toNat=partialDigit d (val32 s.mem base o k) j ∧ Keeps [.eax,.ebx] s t
  | 0, _ => WP.block_nil ⟨rfl,by rw [B]; rfl,Keeps.refl _ _⟩
  | j+1, hj => by
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    refine WP.block_append (WP.mono (digitParts_ok hs ho hd cover B j (by omega)) fun u ⟨M,V,K⟩ => ?_)
    have hu := hs.of_keeps K (by decide)
    have position : (j+1)*d-1<32*k := by
      have := Nat.mul_le_mul_right d hj
      have := Nat.mul_le_mul_right d (show 1≤j+1 by omega)
      simp only [Nat.one_mul] at this
      omega
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (toothRead_ok hu ho position) fun v ⟨Mv,Vv,Kv⟩ => ?_)
    have Bv : (v.gpr .ebx).toNat=partialDigit d (val32 s.mem base o k) j := by
      rw [Kv.1 .ebx (by decide),V]
    rw [M] at Vv
    exact WP.mono (addBit_ok (by omega) (bit_lt _ _) (partialDigit_lt _ _ _) Vv Bv)
      fun t ⟨Mt,Vt,Kt⟩ => ⟨Mt.trans (Mv.trans M),Vt,(K.trans (Kv.mono (by decide))).trans Kt⟩

theorem digit_ok {s : State} {base : Addr} {size o k d : Nat}
    (hs : Scr s base size) (ho : o+4*k≤size) (hd : 0<d) (cover : 5*d≤32*k) (hw : 8≤size) :
    WP isa (VG.Impl.Mont.X86.Comb.digit o d) s fun t =>
      Outside base 4 4 s.mem t.mem ∧
      w32 t.mem base 4=partialDigit d (val32 s.mem base o k) 5 ∧ Keeps [.eax,.ebx] s t := by
  unfold VG.Impl.Mont.X86.Comb.digit VG.Impl.Mont.X86.Dynamic.windowOffset
  simp only [List.cons_append,List.nil_append]
  refine wp_movS rfl fun u U _ => ?_
  refine WP.block_append (WP.mono (digitParts_ok (hs.of_keeps U.keeps (by decide)) ho hd cover U.gpr 5 (by decide))
    fun v ⟨M,V,K⟩ => ?_)
  have Kv : Keeps [.eax,.ebx] s v := (U.keeps.mono (by decide)).trans K
  have hv := hs.of_keeps Kv (by decide)
  refine wp_storeS (hv.ea (by omega)) (hv.write hw) fun t T => WP.block_nil ⟨?_,?_,Kv.trans (T.keeps _)⟩
  · rw [T.mem,M,U.mem]; exact writeW32_outside _ _ _ (by decide)
  · rw [T.mem,w32_write_self,V,U.mem]

end VG.Proof.Mont.X86.Comb
