import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry (`cryptEntry_ok`),
the text (`streamText_ok`) and the exit, for any message the state
represents (`streamText_run`): encrypting appends the ciphertext it writes
(`streamEncrypt_wp`), decrypting the ciphertext it reads (`streamDecrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, for the message
the state represents, with ciphertext `c₀` so far. -/
theorem streamText_run (v : GcmImpl) (enc : Bool) {s : State} (hp : Proof.AesGcm.streamCryptPre s)
    {iv a c₀ : List Byte} (hA : s.gpr .rcx = BitVec.ofNat 64 a.length) (hT : (s.gpr .r8).toNat = c₀.length) :
    WP isa (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block restore))) s fun s' =>
      gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c₀ →
        StreamRepr s'.mem (s.gpr .rdx) ciph h iv a
          (c₀ ++ ctext enc ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) ∧
        bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
          xorKs ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) := by
  have C := CryptCtx.of hp
  have hR := C.rounds
  have hP : c₀.length < 2 ^ 64 := hT ▸ (s.gpr .r8).isLt
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx R = ciph
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (by decide))), ← hH, ctxH_eq]
  have hc₁ : ciphOf s₁.mem Ctx R = ciph := by rw [ciph_frame E.frame dCE hR, ← hciph]; rfl
  have K : SCtx Ctx St W SP R H D n s₁.mem := ⟨L, hRo, hH₁, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24⟩
  have eS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [entryR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  have hyA : StreamRepr s.mem St ciph H iv a c₀ → Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀) :=
    fun hy => by
      rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hy
      exact abs_frame E.frame (eS (by decide)) hy.2.1
  have hyC : StreamRepr s.mem St ciph H iv a c₀ → Ctr s₁.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₁.mem Ctx R) icb
      c₀.length := fun hy => by
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hicb] at hy
    rw [hc₁]
    exact ctr_frame E.frame (eS (by decide)) hy.2.2
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (streamText_ok v K enc E.env rfl (C.data.of_eq E.rd E.wr) E.rbp hP (E.alen.trans hA) htl
    E.dat E.len hyA hyC) fun s₂ ⟨he₂, rd₂, wr₂, f₂, hq⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.ok.w C.t_w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hy => ?_⟩
  rw [hicb]
  have hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide)))
    (by have := C.data.ok.lt; omega)
  obtain ⟨qa, qc, qo⟩ := hq hy
  simp only [hc₁, hd₁] at qa qc qo
  refine ⟨?_, by rw [hm]; exact qo⟩
  have hj := hy
  rw [Proof.Gcm.streamRepr_iff] at hj ⊢
  rw [ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, hicb, List.length_append, length_ctext, length_bytesAt]
  refine ⟨?_, qa, qc⟩
  rw [← hj.1]
  have e : St = St + BitVec.ofNat 64 0 := (BitVec.add_zero St).symm
  rw [blockAt_frame f₂ (j0_stFrame L C.data.ok.st C.t_s), e]
  exact blockAt_frame E.frame (eS (by decide))

/-- `vg_aes_gcm_stream_encrypt`. -/
theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamEncryptX86_64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  have run : ∀ {iv a p : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
          let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat = c.drop p.length) := fun {iv a p} hA hT =>
    WP.mono (streamText_run v true hp (iv := iv) (c₀ := gctr (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (inc32 (Spec.Gcm.j0 (ctxH s.mem (s.gpr .rdi)) iv)) p) hA (by rw [hT, Proof.Gcm.length_gctr]))
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, ↓reduceIte, Proof.Gcm.length_gctr] at h₁ h₂
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (p := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a p hr hA hT => hq (iv, a, p) ⟨hA, hT⟩ hr⟩

/-- `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamDecryptX86_64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  have run : ∀ {iv a c : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
          let c' := c ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
              (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := fun {iv a c} hA hT =>
    WP.mono (streamText_run v false hp (iv := iv) (c₀ := c) hA hT)
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, Bool.false_eq_true, ↓reduceIte] at h₁
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (c := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => hq (iv, a, c) ⟨hA, hT⟩ hr⟩

end VG.Proof.AesGcm.X86_64
