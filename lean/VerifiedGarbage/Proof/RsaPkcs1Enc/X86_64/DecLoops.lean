import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPrf

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `CL` and `AM`

The candidate lengths `CL = IRPRF(KDK, "length", 256)` (`clLoop_step`) and
the alternative message `AM = IRPRF(KDK, "message", k)` (`amLoop_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- The key derivation key of the entry state. -/
abbrev kdkOf (s : State) : List Byte := Spec.RsaPkcs1Enc.kdk (kOf s) (dB s) (cB s)

theorem clInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block clInit) t fun t' => Ctx s R EM t' ∧ word t'.mem (fb s) oI = BitVec.ofNat 64 0 ∧
      word t'.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s) ∧ KeepHi s [] t.mem t'.mem := by
  have hs := hc.frm hp
  have hk2 := hp.k2
  refine (WP.keep [.rax] (c := .block clInit) (Q := fun t' =>
    t'.mem = (t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 0)).writeW (off (fb s) oNB)
      (BitVec.ofNat 64 (nbOf s))) ?_ rfl).mono fun t' ⟨hm, k⟩ => ?_
  · xrun [clInit, ea_sp, hc.rsp, hs.ld (d := oK) (by decide), hs.st (d := oI) (by decide),
      hs.st (d := oNB) (by decide), word_ww _ _ _ (show oK + 8 ≤ oI ∨ oI + 8 ≤ oK by decide) (by decide) (by decide),
      hc.slots.sK]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow,
      show (BitVec.signExtend 64 (31 : BitVec 32)).toNat = 31 from rfl]
    unfold nbOf kOf; omega
  · have hfw : Frame [⟨off (fb s) oI, 16⟩] t.mem t'.mem := by
      rw [hm]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains (fb s) (d := oI) (n := 8) (e := oI) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains (fb s) (d := oNB) (n := 8) (e := oI) (k := 16) (by decide)
          (by decide) (by decide))
    refine ⟨hc.step hp k.2.1 k.2.2 (k.cs (by decide)) hfw fun r hr => by
        rw [List.mem_singleton.mp hr]; exact .inr (.inr fun _ h => h), ?_, ?_, ?_⟩
    · rw [hm, word_ww _ _ _ (by decide) (by decide) (by decide)]; exact word_writeW_self _ _ _ _
    · rw [hm]; exact word_writeW_self _ _ _ _
    · rw [hm]; exact (keepHi_of_slot hp (by decide) _).trans (keepHi_of_slot hp (by decide) _)


/-- After `clLoop`: `CL` at `scratch + sCL`. -/
structure CLd (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256
  key : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kdkOf s
  sNB : word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s)

theorem kdk_len {s : State} {m : Mem} (h : Spec.Rsa.bytesAt m (scA s sKDK) 32 = kdkOf s) : (kdkOf s).length = 32 := by
  rw [← h, blen]

theorem clLoop_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : KD s R EM t) :
    WP isa (clLoop (HH v)) t (CLd s R EM) := by
  refine WP.seq (WP.mono (clInit_run hp h.ctx) fun t₁ ⟨hc₁, hI₁, hNB₁, kh₁⟩ => ?_)
  have hk₁ : Spec.Rsa.bytesAt t₁.mem (scA s sKDK) 32 = kdkOf s := by
    rw [kh₁ _ _ (by decide) (by decide) (by simp)]; exact h.kdk
  refine WP.mono (prf_loop (v := v) hp (msg := msgCL) (L := 10) (N := 8) (dst := sCL) rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (kdk_len hk₁) msgCL_len
    (fun _ _ hc hi hdi hax _ => msgCL_run hp hc (by omega) hdi hax)
    (fun _ _ hc hi hI _ => incr8_ok hp hc hi hI) (pinv0 hc₁ hI₁ hNB₁ hk₁)) fun t₂ h₂ => ⟨h₂.ctx, ?_, h₂.key, h₂.sNB⟩
  have hb := h₂.blk
  rw [irprf_eq, show (256 + 31) / 32 = 8 from rfl]
  refine Eq.trans hb (List.take_of_length_le ?_).symm
  rw [← hb, blen]


theorem amInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp oI) .rax]) t fun t' => Ctx s R EM t' ∧
      word t'.mem (fb s) oI = BitVec.ofNat 64 0 ∧ word t'.mem (fb s) oNB = word t.mem (fb s) oNB ∧
      KeepHi s [] t.mem t'.mem := by
  have hs := hc.frm hp
  refine (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 0)) ?_ rfl).mono
    fun t' ⟨hm, k⟩ => ?_
  · xrun [ea_sp, hc.rsp, hs.st (d := oI) (by decide)]
    rfl
  · have hfw : Frame [⟨off (fb s) oI, 8⟩] t.mem t'.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hc.step hp k.2.1 k.2.2 (k.cs (by decide)) hfw fun r hr => by
        rw [List.mem_singleton.mp hr]; exact .inr (.inr (Region.sub_prefix (by decide))), ?_, ?_, ?_⟩
    · rw [hm]; exact word_writeW_self _ _ _ _
    · rw [hm]; exact word_ww _ _ _ (by decide) (by decide) (by decide)
    · rw [hm]; exact keepHi_of_slot hp (by decide) _

/-- After `amLoop`: `AM` at `scratch + sAM`, and `CL` still at `scratch + sCL`. -/
structure AMd (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (kOf s) =
    Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)

theorem amLoop_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : CLd s R EM t) :
    WP isa (amLoop (HH v)) t (AMd s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hk64 : 64 ≤ kOf s := hk1
  have hnb : nbOf s ≤ 32 := by unfold nbOf; omega
  have hnb0 : 0 < nbOf s := by unfold nbOf; omega
  refine WP.seq (WP.mono (amInit_run hp h.ctx) fun t₁ ⟨hc₁, hI₁, hNB₁, kh₁⟩ => ?_)
  have hk₁ : Spec.Rsa.bytesAt t₁.mem (scA s sKDK) 32 = kdkOf s := by
    rw [kh₁ _ _ (by decide) (by decide) (by simp)]; exact h.key
  have hcl₁ : Spec.Rsa.bytesAt t₁.mem (scA s sCL) 256 =
      Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256 := by
    rw [kh₁ _ _ (by decide) (by decide) (by simp)]; exact h.cl
  refine WP.mono (prf_loop (v := v) hp (msg := msgAM (kOf s)) (L := 11) (N := nbOf s) (dst := sAM) rfl (by decide)
    (by decide) (by unfold sAM scrBytes; omega) hnb0 hnb (kdk_len hk₁) (msgAM_len _)
    (fun _ _ hc hi hdi hax h9 => msgAM_run hp hc (by omega) hdi hax h9)
    (fun _ _ hc hi hI hNB => incrNB_ok hp hc hi hI hNB) (pinv0 hc₁ hI₁ (hNB₁.trans h.sNB) hk₁))
    fun t₂ h₂ => ⟨h₂.ctx, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide) (by simp; unfold sCL sMsg sAM; omega)]; exact hcl₁
  · have hb := h₂.blk
    rw [irprf_eq, show (kOf s + 31) / 32 = nbOf s from rfl]
    have hl : (List.flatMap (fun j => Spec.Hmac.hmac Spec.Hmac.sha256 (kdkOf s) (msgAM (kOf s) j))
        (List.range (nbOf s))).length = 32 * nbOf s := by rw [← hb, blen]
    rw [show (32 * nbOf s) = kOf s + (32 * nbOf s - kOf s) by unfold nbOf; omega, bytesAt_add] at hb
    have := congrArg (List.take (kOf s)) hb
    rw [List.take_left' (blen _ _ _)] at this
    exact this

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
