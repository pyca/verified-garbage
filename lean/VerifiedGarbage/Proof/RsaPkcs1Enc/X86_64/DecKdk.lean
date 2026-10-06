import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecMac

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `KDK = HMAC(DH, C)`

The key derivation key of draft-irtf-cfrg-rsa-guidance-10 §7.2 step 3.1,
from `DH` and the ciphertext `C` (`kdkMac_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

theorem kdkUpdArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block kdkUpdArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = BitVec.ofNat 64 64 ∧ t'.gpr .rdx = stackArg s 3 ∧ (t'.gpr .rcx).toNat = kOf s ∧
      t'.gpr .r8 = scA s sWork := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block kdkUpdArgs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = BitVec.ofNat 64 64 ∧ t'.gpr .rdx = stackArg s 3 ∧
    (t'.gpr .rcx).toNat = kOf s ∧ t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [kdkUpdArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hs.ld (d := oIn) (by decide), hs.ld (d := oK) (by decide), hc.slots.sScr, hc.slots.sIn, hc.slots.sK, scA_zero,
    sx (d := sWork) (by decide)]

theorem kdkFinArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block kdkFinArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = scA s sOuter ∧ t'.gpr .rdx = BitVec.ofNat 64 (64 + kOf s) ∧ t'.gpr .rcx = scA s sKDK ∧
      t'.gpr .r8 = scA s sWork := by
  have hs := hc.frm hp
  have hk2 := hp.k2
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block kdkFinArgs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = scA s sOuter ∧ t'.gpr .rdx = BitVec.ofNat 64 (64 + kOf s) ∧
    t'.gpr .rcx = scA s sKDK ∧ t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [kdkFinArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hs.ld (d := oK) (by decide), hc.slots.sScr, hc.slots.sK, scA_zero, sx (d := sOuter) (by decide),
    sx (d := sKDK) (by decide), sx (d := sWork) (by decide)]
  rw [show BitVec.signExtend 64 (64 : BitVec 32) = (64 : BitVec 64) from by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kOf, show (64 : BitVec 64).toNat = 64 from rfl]
  omega


/-- After `kdkMac`: `KDK` at `scratch + sKDK`. -/
structure KD (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = Spec.RsaPkcs1Enc.kdk (kOf s) (dB s) (cB s)

/-- The ciphertext, in a state of `Ctx`. -/
theorem Ctx.c {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    Spec.Rsa.bytesAt t.mem (stackArg s 3) (kOf s) = cB s := by
  have hl := hp.hil
  have hw := hp.wI
  show _ = Spec.Rsa.bytesAt s.mem (stackArg s 3) (kOf s)
  rw [show kOf s = (stackArg s 4).toNat from hl.symm]
  exact bytes_of_frame hc.mem hp.dKi hp.dOi hp.dMi hp.dis.symm (by omega)

theorem kdkMac_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : HD s R EM t) :
    WP isa (kdkMac (HH v)) t (KD s R EM) := by
  have hk2 := hp.k2
  have hl := hp.hil
  have hw := hp.wI
  have hkk : kOf s ≤ 1024 := hk2
  obtain ⟨h1, -⟩ := scr_len hp
  have hC : (⟨stackArg s 3, kOf s⟩ : Region) = ⟨stackArg s 3, (stackArg s 4).toNat⟩ := by rw [hl]
  refine mac_front hp h.ctx (kOff := sDH) (by decide) (by decide) (fun _ hc => kdkUpdArgs_run hp hc)
    (Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hC, hp.hrd]; simp))
    (fun a n han => by
      rw [hC]
      exact hp.dis.sub_right (sub_trans (scSub (by unfold sMsg at han; unfold scrBytes; omega))
        (Region.sub_prefix h1)))
    (by rw [hC]; exact hp.dKi.sub_left (below_sub s (by decide))) (by omega) fun t₁ h₁ => ?_
  refine WP.seq (WP.mono (kdkFinArgs_run hp h₁.ctx) fun t₂ ⟨hc₂, hm₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂⟩ => ?_)
  have h₂ : MacMid v s R EM (Spec.Rsa.bytesAt t.mem (scA s sDH) 32) (Spec.Rsa.bytesAt t.mem (stackArg s 3) (kOf s))
      t t₂ := ⟨hc₂, (by rw [hm₂]; exact h₁.inner), (by rw [hm₂]; exact h₁.outer), (by rw [KeepHi, hm₂]; exact h₁.keep), (by rw [FrmKeep, hm₂]; exact h₁.frm)⟩
  refine WP.mono (mac_fin hp h₂ (dOff := sKDK) (by decide) (by decide) (blen _ _ _) hdi₂ hsi₂
    (by rw [hdx₂, blen]) hcx₂ h8₂ (by rw [blen]; omega)) fun t₃ ⟨hc₃, hb₃, _⟩ => ⟨hc₃, ?_⟩
  rw [hb₃, h.dh, h.ctx.c hp]
  rfl

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
