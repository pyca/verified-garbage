module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.EncodeTaint
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp

/-! ### `RsaPkcs1Sig.Arm.SgTail`, which only this module used -/

section

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
    (by have := hs.1.k64; omega_using [this]) (by omega_using [hK]) (by
      rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega_using [fit]),
        BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega_using [hK, fit])
    (by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK])) r0 lr)
    fun t ⟨_, fr, rest⟩ => ?_
  rw [e] at fr
  have st : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK]) fr
    rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, ?_⟩
  have hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K :=
    bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega_using [hK])).symm)
      (by omega_using [hK])
  obtain ⟨em, he, w⟩ := sr
  rw [rest.gpr .r3 (by decide)]
  exact ⟨em, he, writtenOutcome_congr hb w⟩

theorem fin_wp {σ s : State} (h : R4 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (Fin P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩, by
    obtain ⟨em, he, w⟩ := h.2
    rw [Res, signId_some h.1.1 he, u.mem, u.gpr]
    exact w⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg

end

end


/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`Fin`), and two runs with the same public data leak the same trace. The
branch on the encoding's success agrees in two runs: it depends only on the
hash function's number and the lengths (`enc_isNone`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem encArgs_vp : VP (S P) (.block encArgs) (E1 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => encArgs_wp h

theorem encode_vp : VP (E1 P) Impl.RsaPkcs1Sig.Arm.encode (E2 P) :=
  VP.taint [.r0, .r1, .r2, .r3, .lr] encode_taint (fun _ _ _ _ h₁ h₂ r hr => by
    obtain ⟨-, a0, a1, a2, a3, a4⟩ := h₁
    obtain ⟨-, b0, b1, b2, b3, b4⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
    · rw [a4, b4]) fun _ _ h => encode_wp h

theorem cmp_vp : VP (E2 P) (.block [.cmp .r3 (.imm 0)]) (E3 P) :=
  VP.taint [.r3] cmp_taint (fun σ₁ σ₂ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [encR_r3 h₁.2, encR_r3 h₂.2]
    exact congrArg (fun b : Bool => if b = true then (0 : BitVec 32) else 1) (enc_isNone P σ₁ σ₂))
    fun _ _ h => cmp_wp h

theorem fail_vp : VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some true)
    (.seq (.block zeroArgs) (.seq Impl.Bignum.Arm.maskBytes (.block ret0))) (Fin P) :=
  (VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => zeroArgs_wp h).seq
  ((VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => zero_wp h).seq
  (VP.taint [] ret0_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => ret0_wp h))

theorem callArgs_vp : VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some false) (.block (callArgs P.pc)) (R1 P) :=
  VP.stk (code := (callArgs P.pc).tail) (by generalize P.pc = b; cases b <;> decide)
    (by generalize P.pc = b; cases b <;> decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => callArgs_wp (r0_of h)

theorem wipeArgs_vp : VP (R2 P) (.block wipeArgs) (R3 P) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => wipeArgs_wp h

theorem wipe_vp : VP (R3 P) Impl.Bignum.Arm.maskBytes (R4 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => wipe_wp h

theorem fin_vp : VP (R4 P) (.block [.mov .r0 (.reg .r3)]) (Fin P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem rest_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some false)
      (rest P.pc (privN P.pc v) (privC P.pc v)) (Fin P) :=
  callArgs_vp.seq ((call_vpG v).seq (wipeArgs_vp.seq (wipe_vp.seq fin_vp)))

theorem body_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S P) (body P.pc (privN P.pc v) (privC P.pc v)) (Fin P) :=
  encArgs_vp.seq (encode_vp.seq (cmp_vp.seq (VP.ite (fun σ₁ σ₂ _ _ h₁ h₂ => by
    rw [Proof.X25519.Arm.eval_eq, Proof.X25519.Arm.eval_eq, h₁.2, h₂.2, enc_isNone P σ₁ σ₂]) fail_vp (rest_vp v))))

end VG.Proof.RsaPkcs1Sig.Arm.Sg
