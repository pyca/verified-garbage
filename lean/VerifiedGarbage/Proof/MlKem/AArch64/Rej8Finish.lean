module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Preserve the accepted prefix and report bounded sampling success -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def fix : Prog isa := .ite (.zero .x .x4) (.block [])
  (.block [.movz .x .x13 0 0,.str .w .x13 .x3 0])

theorem fix_ok {aP : Addr} {s₀ s : State} {L : List Zq}
    (hina : ∀i<256,InRegions s₀.wr (coeffAddr aP i) 4)
    (h : Scalar.Acc aP s₀ L s) : WP isa fix s fun u =>
      Scalar.Acc aP s₀ L u ∧ Keep [.x13] s u := by
  have hl := h.len
  refine WP.ite (s.gpr .x4 == 0) (eval_zero _ _) (fun _ => wp_nil ⟨h,Keep.refl _ _⟩) (fun hz => ?_)
  rw [eq_zero_iff,decide_eq_false_iff_not,h.x4] at hz
  have hlt : L.length<256 := by omega
  refine wp_movz fun a ha ea => wp_strw (a := coeffAddr aP L.length) (by decide)
    (by rw [ha.gpr .x3 (by decide),h.x3,ptr_zero])
    (by rw [ha.wr,h.wr]; exact hina _ hlt) fun u hu => wp_nil ?_
  have hk := (ha.keep.trans hu.keep).mono (rs' := [.x13]) (by decide)
  have hm : u.mem=s.mem.writeW (coeffAddr aP L.length) (0 : BitVec 32) := by
    rw [hu.mem,ea,ha.mem]
    rfl
  refine ⟨⟨hk.rd.trans h.rd,hk.wr.trans h.wr,hk.sp.trans h.sp,h.len,
    by rw [hk.get .x3,h.x3],by rw [hk.get .x4,h.x4],by rw [hk.get .x9,h.x9],?_,?_⟩,hk⟩
  · rw [hm]; exact h.coeffs.reject hlt 0
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hlt)

structure Post (initial : List Zq) (N : Nat) (B : Nat → Byte) (aP : Addr) (s₀ u : State) : Prop where
  acc : Scalar.Acc aP s₀ (Scalar.LA initial B N) u
  keep : Keep (.x0::Scalar.lRegs) s₀ u
  status : (u.gpr .x0).toNat=if (Scalar.LA initial B N).length=256 then 1 else 0

theorem loop_ok {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : Env N B bP aP s₀) (hN : 0<N) (hm : N%4=0)
    (h : Scalar.Inv initial N B bP aP s₀ 0 s) (hc : Constants s) :
    WP isa Impl.MlKem.AArch64.Rej8.rejLoop s (Post initial N B aP s₀) := by
  refine WP.seq (WP.mono (iters_ok hp hN hm h hc) fun a ha => ?_)
  refine WP.seq (WP.mono (fix_ok hp.ina ha.acc) fun b ⟨hb,hk⟩ => ?_)
  refine wp_subImm (by decide) fun c hc ec => wp_lsr (by decide) fun u hu eu => wp_nil ?_
  have k := hc.keep.trans hu.keep
  refine ⟨Scalar.acc_keep hb k (hu.mem.trans hc.mem),
    ((ha.keep.trans hk).trans k).mono (by decide),?_⟩
  have hl := hb.len
  rw [eu,toNat_lsr,ec,BitVec.toNat_sub,hb.x4]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

end VG.Proof.MlKem.AArch64.Rej8
