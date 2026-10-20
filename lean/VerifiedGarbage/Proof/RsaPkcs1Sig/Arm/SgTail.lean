module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: after the call

The result kept in `r3` while `EM` is overwritten with zeros (`wipeArgs_wp`,
`wipe_wp`), and returned (`fin_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The signature, and the result in `r`. -/
def SR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∃ em, enc P σ = some em ∧ Spec.Rsa.writtenOutcome m (State.addr P.out) P.K r
    (Spec.Rsa.privateChecked P.nB P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ))

/-- Before the wipe of `EM`. -/
def R3 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ SR P σ s.mem (s.gpr .r3) ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧
    s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `EM` wiped. -/
def R4 (P : EP) (σ s : State) : Prop := S P σ s ∧ SR P σ s.mem (s.gpr .r3)

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.writtenOutcome m a K r o) :
    Spec.Rsa.writtenOutcome m' a K r o := by
  cases o with
  | ok y => exact ⟨h.1, hb.trans h.2⟩
  | invalid => exact ⟨h.1, hb.trans h.2⟩
  | fault => exact ⟨h.1, hb.trans h.2⟩

theorem wipeArgs_wp {σ s : State} (h : R2 P σ s) : WP isa (.block wipeArgs) s (R3 P σ) := by
  obtain ⟨hs, sr⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun t2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := ((hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r3]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun t5 u5 => WP.block_nil ⟨⟨hs.1, s4.of_rest (u5.rest (ws := [.r2])
    (by simp)) u5.mem⟩, ?_, ?_, ?_, u5.gpr⟩
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
    exact sr
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.other _ (by decide), u1.gpr, hs.2.sp,
      BitVec.add_zero]
  · rw [u5.other _ (by decide), u4.gpr]; rfl

theorem wipe_wp {σ s : State} (h : R3 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (R4 P σ) := by
  obtain ⟨hs, sr, r0, lr, -⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have e := inpA P hs.1
  have fit := ok.fit
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.B + BitVec.ofNat 32 oEM) (n := P.K)
    (by have := hs.1.k64; omega) (by omega) (by
      rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega),
        BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega)
    (by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega)) r0 lr)
    fun t ⟨_, fr, rest⟩ => ?_
  rw [e] at fr
  have st : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega) fr
    rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, ?_⟩
  have hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K :=
    bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega)).symm)
      (by omega)
  obtain ⟨em, he, w⟩ := sr
  rw [rest.gpr .r3 (by decide)]
  exact ⟨em, he, writtenOutcome_congr hb w⟩

theorem fin_wp {σ s : State} (h : R4 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (Fin P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩, by
    obtain ⟨em, he, w⟩ := h.2
    rw [Res, signId_some h.1.1 he, u.mem, u.gpr]
    exact w⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg
