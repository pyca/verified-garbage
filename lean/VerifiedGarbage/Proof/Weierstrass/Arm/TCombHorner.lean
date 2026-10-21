module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The ARM comb decodes bits using the same Horner invariant as x86. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm

structure RegOnly (rs : List Reg) (s t : State) : Prop where
  keep : Rest rs s t
  mem : t.mem=s.mem

theorem hornerAt_ok (K : TCombCfg) {v : Nat → Nat} (hv : ∀ i,v i≤1) :
    ∀ k d s, k<32 → K.L.bits%4096+d+k ≤ 4096 →
    (∀ i<k,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+d+i))) 1 ∧
      s.mem (State.addr (s.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+d+i))) = BitVec.ofNat 8 (v (d+i))) →
    WP isa (.block (K.hornerAt d k)) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (hornerVal v d k) ∧ RegOnly [.r5,.r9] s t
  | 0,d,s,_,_,_ => by
    unfold TCombCfg.hornerAt
    exact wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
      ⟨u.gpr,⟨u.rest (by simp),u.mem⟩⟩
  | k+1,d,s,hk,ho,hb => by
    rw [TCombCfg.hornerAt]
    refine VG.Proof.X25519.Arm.WP.append
      (hornerAt_ok K hv k (d+1) s (by omega) (by omega) (fun i hi => by
        rw [show K.L.bits%4096+(d+1)+i=K.L.bits%4096+d+(i+1) by omega,
          show d+1+i=d+(i+1) by omega]
        exact hb (i+1) (by omega))) fun s₁ ⟨v₁,k₁⟩ => ?_
    refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
    have ptr₂ : s₂.gpr .r4=s.gpr .r4 := by
      rw [u₂.other .r4 (by decide),k₁.keep.gpr .r4 (by decide)]
    have mem₂ : s₂.mem=s.mem := u₂.mem.trans k₁.mem
    have rd₂ : s₂.rd ++ s₂.wr=s.rd ++ s.wr := by rw [u₂.rd,u₂.wr,k₁.keep.rd,k₁.keep.wr]
    have h0 := hb 0 (by omega)
    simp only [Nat.add_zero] at h0
    refine wp_ldrb (by omega) rfl (by rw [ptr₂,rd₂]; exact h0.1) fun s₃ u₃ =>
      wp_dp (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
    refine ⟨?_,⟨k₁.keep.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))),
      by rw [u₄.mem,u₃.mem,mem₂]⟩⟩
    · rw [u₄.gpr,dpVal,u₃.other .r9 (by decide),u₂.gpr,dpVal,v₁,u₃.gpr,ptr₂,mem₂,h0.2]
      have hn := hornerVal_lt hv (d+1) k
      have hvd := hv d
      have hp : 2^k < 2^31 := Nat.pow_lt_pow_right (by decide) (by omega)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.toNat_setWidth,hornerVal]
      rw [Nat.mod_eq_of_lt (by omega : hornerVal v (d+1) k<2^32),
        Nat.mod_eq_of_lt (by omega : v d<2^8),Nat.mod_eq_of_lt (by omega : v d<2^32)]
      omega

end VG.Proof.Weierstrass.Arm.TComb
