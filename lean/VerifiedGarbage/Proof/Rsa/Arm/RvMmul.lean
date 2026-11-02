module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMM
public import VerifiedGarbage.Proof.Rsa.Arm.RvKS
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Rsa.Arm.RvViews
import VerifiedGarbage.Proof.Bignum.Arm.MontSelected
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_recover_primes` on ARMv7: a Montgomery product on a stage

`mmul o a b`: frame word 0 into `r0`, the selected Montgomery operation, the context of the key
working space again and the top words of the result's array cleared. From a
stage whose arrays `mBase + a` and `mBase + b` hold numbers below `n`, the
result's array holds the number `T < n` with `T R ≡ [a] [b] (mod n)`, given
(`mmul_vp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- Montgomery multiplication's number of array `i` through a step that does
not write the key array `mBase + i`. -/
theorem numAt_keep {P : RP} (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) {js ds : List Nat} {m m' : Mem}
    (k : Keep P.B P.w js ds m m') {i : Nat} (hi : mBase + i < nArr) (hjs : ∀ j ∈ js, j ≠ mBase + i)
    (hds : ∀ d ∈ ds, d + 4 ≤ hdr) : numAt m' (State.addr P.M0) P.w6 i = numAt m (State.addr P.M0) P.w6 i := by
  rw [numAt_val32 sz hf, numAt_val32 sz hf]
  have hS : S P.w = 4 * (P.w + 2) := rfl
  have ww : P.w = 2 * P.w6 + 2 := rfl
  have fi := fitZ_w sz hi
  have hZ := Z_64 sz
  refine k.val32 (fun r hr => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d', hd', rfl⟩
  · have := arr_disj (w := P.w) (hjs j hj); dsimp only; omega
  · have := hds d' hd'; have : hdr ≤ arr P.w (mBase + i) := Nat.le_add_right _ _; dsimp only; omega

/-- After the product, before the context: the stage but `r8`, the result's
array, and its two top words. -/
structure AfterM (P : RP) (σ : State) (o T : Nat) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat)
    (liveW : List Nat) (V : Nat → Nat) (ls : List Nat) (t : State) : Prop where
  bs : Bs P σ t
  mm : MM P t
  cnt : t.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w
  arrs : ∀ j ∈ live, j ≠ mBase + o → num t.mem P.B P.w j = A j
  arrsW : Arrs t.mem P.B P.W AW liveW
  sl : ∀ d ∈ ls, slot t.mem P.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  liveW_lt : ∀ j ∈ liveW, j < 22
  ls_ok : ∀ d ∈ ls, SlotOk d
  val : val32 t.mem (State.addr P.B) (arr P.w (mBase + o)) (2 * P.w6) = T

/-- The indices of Montgomery products. -/
abbrev MIdx (o a b : Nat) : Prop :=
  (o = 1 ∨ o = 5 ∨ o = 6 ∨ o = 7) ∧ (a = 1 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7) ∧
    (b = 1 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7)

theorem MIdx.operand {o a b : Nat} (h : MIdx o a b) : Operand o ∧ Operand a ∧ Operand b := by
  obtain ⟨ho, ha, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] <;> omega

/-- The product, from `r0 = M0`. -/
theorem montOp_after {P : RP} {σ s : State} {o a b T : Nat} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (ptr : s.gpr .r0 = P.M0) (hi : MIdx o a b)
    (hodd : P.n % 2 = 1) (ha : mBase + a ∈ live) (hb : mBase + b ∈ live)
    (hav : A (mBase + a) < P.n) (hbv : A (mBase + b) < P.n)
    (hT : T < P.n) (hTv : T * 2 ^ (64 * P.w6) % P.n = A (mBase + a) * A (mBase + b) % P.n)
    (hl2 : mBase + 2 ∉ live) (hl3 : mBase + 3 ∉ live)
    (hlW : ∀ j ∈ liveW, j ≠ (mBase + 2) / 2 ∧ j ≠ (mBase + o) / 2) :
    WP isa (VG.Impl.Bignum.Arm.selectedMontOp o a b) s (AfterM P σ o T A live AW liveW V ls) := by
  have pre := h.bs.pre
  have sz := pre.sizes
  have hf := pre.fS
  have hn2 : P.n < 2 ^ (64 * P.w6) := by
    have := hm.mr.modulus
    rw [← hm.n0, numAt_val32 sz hf]
    have := val32_lt (m := s.mem) (base := State.addr P.B) (d := arr P.w (mBase + 0)) (k := 2 * P.w6)
    rw [show 32 * (2 * P.w6) = 64 * P.w6 by omega] at this
    exact this
  have opd := hi.operand
  have eA : numAt s.mem (State.addr P.M0) P.w6 a = A (mBase + a) := by
    rw [numAt_eq sz hf (by rw [h.arrs _ ha]; omega), h.arrs _ ha]
  have eB : numAt s.mem (State.addr P.M0) P.w6 b = A (mBase + b) := by
    rw [numAt_eq sz hf (by rw [h.arrs _ hb]; omega), h.arrs _ hb]
  have ho0 : o ≠ 0 := by have := hi.1; omega
  refine WP.mono (selectedMontOp_ok s (hm.mr.ready ptr) opd.1 opd.2.1 opd.2.2 ho0 (by rw [eB, hm.n0]; exact hbv))
    fun t ⟨ar, m0, lt, v, keeps, frame, rest⟩ => ?_
  have k := keep_of_mont sz hf keeps frame
  have fS : Frame [P.rS] s.mem t.mem := frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨P.rS, List.mem_singleton_self _, ?_⟩
    rw [show State.addr P.M0 = State.addr P.B + BitVec.ofNat 64 P.oM from M0_addr sz hf]
    exact Offset.sub_base _ (by rw [sz.endM]; exact Nat.le_trans (arr_mono (by decide)) sz.fits)
  refine ⟨h.bs.of_frame fS rest.sp rest.rd rest.wr, ⟨ArithmeticReady.mr ar, m0.trans hm.n0⟩, ?_, ?_, ?_, ?_, h.live_lt,
    h.liveW_lt, h.ls_ok, ?_⟩
  · refine (BitVec.eq_of_toNat_eq ?_).trans h.cnt
    exact k.slot (e := 16) (by decide) (by simp)
  · intro j hj hjo
    rw [k.num (fun i hi e => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact hl2 (e ▸ hj)
      · exact hl3 (e ▸ hj)
      · exact hjo e.symm) (by simp) (fit_w sz (h.live_lt j hj))]
    exact h.arrs j hj
  · exact h.arrsW.keepOf k.toW (fun j hj i hi => by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
      have := hlW j hj
      rcases hi with rfl | rfl | rfl
      · exact this.1.symm
      · exact fun e => this.1 (by rw [← e]; rfl)
      · exact this.2.symm) (by simp) fun j hj => fit_W sz (h.liveW_lt j hj)
  · exact h.sl_keep k (by simp)
  · rw [← numAt_val32 sz hf]
    have hR : Nat.Coprime (2 ^ (64 * P.w6)) P.n := VG.Proof.Bignum.coprime_pow2 hodd _
    rw [hm.n0] at lt v
    rw [eA, eB] at v
    exact VG.Proof.Rsa.mont_inj hR lt hT (v.trans hTv.symm)

end VG.Proof.Rsa.Arm.Recover
