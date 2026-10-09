import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)

theorem two_ret {S : Nat} (hS : S<2^64) : RetPub (rejNTT2Contract abi S) Two.code := by
  intro x y tx ty x' y' ⟨hx,hy,hpub⟩ ex ey
  have px := pre_two (pre_stack (Nat.zero_le S) hS hx)
  have py := pre_two (pre_stack (Nat.zero_le S) hS hy)
  have pub : Pub 2 x y := by
    sig_pub [rejNTT2Contract,rejNTT2Sig,abi,argRegs] at hpub
    obtain ⟨hsp,hb,h0,h1,h2⟩ := hpub
    exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
  refine ⟨two_ct _ _ _ _ _ _ px py pub ex ey,?_⟩
  obtain ⟨_,u,eu,hu⟩ := two_ok px
  obtain ⟨_,v,ev,hv⟩ := two_ok py
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  have he : (∀k<2,(prefixRow x k 1008).length=256) ↔ ∀k<2,(prefixRow y k 1008).length=256 := by
    constructor
    · intro h k hk; rw [←pub.prefix hk]; exact h k hk
    · intro h k hk; rw [pub.prefix hk]; exact h k hk
  rw [hu.status,hv.status]
  by_cases h : ∀k<2,(prefixRow x k 1008).length=256
  · simp only [ite_eq_left h,ite_eq_left (he.mp h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hy=>h (he.mpr hy))]

theorem rej2At_trRet {S : Nat} (hS : S<2^64)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej2Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 68 = bytesAt y.mem (pa y seed) 68 ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet (callee hS) (two_ret hS) (rej2_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej2_pre Lx hc h1, ?_, ?_, (rej2_cov Lx hc).1, (rej2_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej2_pre Ly hc h2
  · sig_pub [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
