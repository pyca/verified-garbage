module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified
public import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamInitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamAadCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
public import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinishCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt

/-! ### `AesGcm.X86_64.Verified`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.StreamRun`, which this module and modules that import it used -/

section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry (`cryptEntry_ok`),
the text (`streamText_ok`) and the exit, for any message the state
represents (`streamText_run`): encrypting appends the ciphertext it writes
(`streamEncrypt_wp`), decrypting the ciphertext it reads (`streamDecrypt_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, for the message
the state represents, with ciphertext `c₀` so far. -/
theorem streamText_run (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (enc : Bool) {s : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s) (hok : M.ok s.mem (s.gpr .rdi))
    {iv a c₀ : List Byte} (hA : s.gpr .rcx = BitVec.ofNat 64 a.length) (hT : (s.gpr .r8).toNat = c₀.length) :
    WP isa (.seq (.block cryptEntry) (.seq (streamText (v.withBlk B) enc) (.block restore))) s fun s' =>
      gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c₀ →
        StreamRepr s'.mem (s.gpr .rdx) ciph h iv a
          (c₀ ++ ctext enc ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) ∧
        bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
          xorKs ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) := by
  have C := CryptCtx.of hp M.ge
  have X := CtxExt.ofCrypt hp hok
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
  have K : SCtx M Ctx St W SP R H D n s₁.mem := ⟨L, hRo, hH₁, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24, X.w, X.cs, X.cw,
    X.cd, X.ct, M.frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))) X.w X.ok⟩
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
  refine WP.seq (WP.mono (streamText_ok v B K enc E.env rfl (C.data.of_eq E.rd E.wr) (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP (E.alen.trans hA) htl
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
    (by have := C.data.ok.lt; omega_using [hn])
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

/-- `vg_aes_gcm_stream_encrypt`, for a key context of kind `M`. -/
theorem streamEncryptM_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.streamEncryptX86_64M M).pre s) :
    WP isa (streamEncrypt (v.withBlk B)) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  have run : ∀ {iv a p : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      WP isa (streamEncrypt (v.withBlk B)) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
          let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat = c.drop p.length) := fun {iv a p} hA hT =>
    WP.mono (streamText_run v B true hp.1 hp.2 (iv := iv) (c₀ := gctr (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (inc32 (Spec.Gcm.j0 (ctxH s.mem (s.gpr .rdi)) iv)) p) hA (by rw [hT, Proof.Gcm.length_gctr]))
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

/-- `vg_aes_gcm_stream_decrypt`, for a key context of kind `M`. -/
theorem streamDecryptM_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.streamDecryptX86_64M M).pre s) :
    WP isa (streamDecrypt (v.withBlk B)) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  have run : ∀ {iv a c : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      WP isa (streamDecrypt (v.withBlk B)) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
          let c' := c ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
              (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := fun {iv a c} hA hT =>
    WP.mono (streamText_run v B false hp.1 hp.2 (iv := iv) (c₀ := c) hA hT)
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

/-- `vg_aes_gcm_stream_encrypt`. -/
theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamEncryptX86_64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' :=
  streamEncryptM_wp v v.blkB ⟨hp, trivial⟩

/-- `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamDecryptX86_64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' :=
  streamDecryptM_wp v v.blkB ⟨hp, trivial⟩

end VG.Proof.AesGcm.X86_64

end

end

/-! ### `AesGcm.X86_64.StreamAad`, which only this module used -/

section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The additional data absorbed
into GHASH (`absorb 16`), for any additional data so far of the length
`aad_len` gives modulo 16 (`streamAad_run`), and so for all of them
(`streamAad_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The regions `vg_aes_gcm_stream_aad` writes. -/
abbrev aadFrame (St W SP : Addr) (N : Nat := 2560) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 32⟩, ⟨W, N⟩, below SP 8]

/-- One run, for additional data so far `x` (of `aad_len` bytes modulo 16). -/
theorem streamAad_run (v : GcmImpl) {N gs : Nat} [G : GhFits v N gs] {s : State}
    (hp : (Proof.AesGcm.streamAadX86_64 N).pre s)
    {x : List Byte} (hx : x.length % 16 = (s.gpr .rdx).toNat % 16) (hN : 176 ≤ N) (hN' : N < 2 ^ 64) :
    WP isa (streamAad v.callees) s fun s' => gprPreserved s s' ∧
      Frame (aadFrame (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) N) s.mem s'.mem ∧
      (Absorbed s.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .rdi)) x →
        Absorbed s'.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .rdi)) (x ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)) := by
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_ds, d_dw, d_sw, r_s, r_w, k_c, k_d, k_s, k_w, wc, wd, ws, ww⟩ := hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hD : s.gpr .rcx = D at *
  generalize hW : s.gpr .r9 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hn : (s.gpr .r8).toNat = n at *
  have L : Lay Ctx St W SP N := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w hN hN'
  have pW : Covers [⟨W, N⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .r9 hW pW (by omega_using [hN])
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rcx),
        .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧
      s₂.gpr .rbp = BitVec.ofNat 64 n ∧ s₂.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hand := and15 (s.gpr .rdx)
    rw [imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hD]
    · simp [gpr_setReg, hg₁, ← hn]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg₁, hand, hx]
    · simp [gpr_setReg, gpr_arithFlags, hg₁, hSP]
    all_goals rfl
  have he₂ : Env Ctx St W SP s₂ N := ⟨h13, h14, h15, hg₂, by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
    · exact pW⟩
  have dsv : ∀ r ∈ [savedR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact d_dw.sub_right (Lay.wSub L.le)
  have hdata : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [hm₂]; exact bytesAt_frame f₁ dsv (by omega_using [hn])
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [hm₂, ctxH_eq, blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) L.le]
  have rdD : Covers [⟨D, n⟩] (s₂.rd ++ s₂.wr) := by
    rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hai : AbsIn Ctx St W SP 16 (ctxH s.mem Ctx) x D n s₂ N :=
    ⟨he₂, h12, hbp, hbx, ⟨rdD, by have := (s.gpr .r8).isLt; omega_using [hn], wd, d_ds, d_dw, k_d⟩, hH⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (absorb_ok v L (yo := 16) (.inr rfl) hai) fun s₃ ho => ?_)
  have he₃ := ho.env
  have hsv₃ : SavedAt s₃.mem W s := (hm₂ ▸ hsv₁).frame ho.frame (saved_absFrame L G.fit (.inr rfl))
  obtain ⟨s₄, run₄, hsv, hother, hm₄, hrd₄, hwr₄⟩ := restore_ok s₃ he₃.r15 (covers_left he₃.perm.w) hsv₃ (by omega_using [hN])
  refine WP.of_runBlock ⟨s₄, run₄, ⟨?_, ?_⟩, ?_, fun ha => ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.rbx, 128) (by simp [saved])
    · exact hsv (.rbp, 136) (by simp [saved])
    · rw [hother .rsp (by simp [saved]), he₃.rsp, hSP]
    · exact hsv (.r12, 144) (by simp [saved])
    · exact hsv (.r13, 152) (by simp [saved])
    · exact hsv (.r14, 160) (by simp [saved])
    · exact hsv (.r15, 168) (by simp [saved])
  · rw [hm₄, hSP, ret_kept ho.frame (fun r hr => ?_), hm₂, ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub L.le)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Lay.stSub (by decide))
      · exact r_s.sub_right (Lay.stSub (by decide))
      · exact Lay.gh_of_w G.fit r_w
      · exact ret_below SP
  · rw [hm₄]
    refine ((f₁.sub fun r hr => ?_).trans (hm₂ ▸ ho.frame.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub L.le⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.ghSub G.fit⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · have dS : ∀ r ∈ [savedR W], ∀ d k, d + k ≤ 80 → (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
      intro r hr d k hk
      simp only [List.mem_singleton] at hr; subst hr
      exact (d_sw.sub_left (Lay.stSub hk)).sub_right (Lay.wSub L.le)
    have ha₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH s.mem Ctx) x := by
      rw [hm₂]
      refine ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide)) (bytesAt_frame f₁
        (fun r hr => dS r hr 32 (x.length % 16) (by omega_using [])) (by omega_using []))
    rw [hm₄, ← hdata]
    exact ho.abs ha₂

/-- `vg_aes_gcm_stream_aad`. -/
theorem streamAad_wp (v : GcmImpl) {N gs : Nat} [G : GhFits v N gs] {s : State}
    (hp : (Proof.AesGcm.streamAadX86_64 N).pre s) (hN : 176 ≤ N := by decide) (hN' : N < 2 ^ 64 := by decide) :
    WP isa (streamAad v.callees) s fun s' => gprPreserved s s' ∧ (Proof.AesGcm.streamAadX86_64 N).post s s' := by
  have h₀ := streamAad_run v hp (x := List.replicate ((s.gpr .rdx).toNat % 16) 0) (by simp) hN hN'
  have h := WP.forall_det (P := fun a : List Byte => a.length % 16 = (s.gpr .rdx).toNat % 16)
    (R := fun s' => gprPreserved s s' ∧ Frame (aadFrame (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) N) s.mem s'.mem)
    (WP.mono h₀ fun _ h => ⟨h.1, h.2.1⟩) fun a ha => WP.mono (streamAad_run v hp ha hN hN') fun _ h => h.2.2
  refine WP.mono h fun s' ⟨⟨hg, hf⟩, hq⟩ => ⟨hg, fun ciph iv a hr hl => ?_⟩
  have hp' := hp
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp'
  obtain ⟨-, -, -, -, -, -, d_sw, -, -, -, -, k_s, -, -, -, ws, -⟩ := hp'
  generalize s.gpr .rsi = St at *
  have dS : ∀ d k, (d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ aadFrame St (s.gpr .r9) (s.gpr .rsp) N,
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega_using [hk]) (by omega_using [hk]) (by omega_using [])
    · exact d_sw.sub_left (Lay.stSub (by omega_using [hk]))
    · exact (k_s.sub_right (Lay.stSub (by omega_using [hk]))).symm
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rw [← hj]; simpa using blockAt_frame hf (dS 0 16 (.inl (by decide)))
  · rw [Proof.Gcm.ghashInput_nil] at ha ⊢
    refine hq a ?_ ha
    rw [hl, toNat_mod16]
  · exact hc.congr (blockAt_frame hf (dS 48 16 (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame hf (dS 64 16 (.inr ⟨by decide, by decide⟩)))

end VG.Proof.AesGcm.X86_64

end

end

/-! ### `AesGcm.X86_64.StreamInit`, which only this module used -/

section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. `J₀`, the accumulator and the
first counter block, from `j0` (`streamInit_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

/-- `vg_aes_gcm_stream_init`. -/
theorem streamInit_wp (v : GcmImpl) {N gs : Nat} [G : GhFits v N gs] {s : State}
    (hp : (Proof.AesGcm.streamInitX86_64 N).pre s) (hN : 224 ≤ N := by decide) (hN' : N < 2 ^ 64 := by decide) :
    WP isa (streamInit v.callees) s fun s' => gprPreserved s s' ∧ (Proof.AesGcm.streamInitX86_64 N).post s s' := by
  simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp ⊢
  obtain ⟨hrd, hwr, d_cs, d_cw, d_ns, d_nw, d_sw, r_s, r_w, k_c, k_n, k_s, k_w, wc, wn, ws, ww⟩ := hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hSt : s.gpr .rcx = St at *
  generalize hW : s.gpr .r8 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hn : (s.gpr .rdx).toNat = n at *
  have L : Lay Ctx St W SP N := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w (by omega_using [hN]) hN'
  have pW : Covers [⟨W, N⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .r8 hW pW (by omega_using [hN])
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi),
        .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = Np ∧
      s₂.gpr .rbp = BitVec.ofNat 64 n ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hNp]
    · simp [gpr_setReg, hg₁, ← hn]
    · simp [gpr_setReg, hg₁, hSP]
    all_goals rfl
  have he₂ : Env Ctx St W SP s₂ N := ⟨h13, h14, h15, hg₂, by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
    · exact pW⟩
  have rdN : Covers [⟨Np, n⟩] (s₂.rd ++ s₂.wr) := by
    rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hiv : bytesAt s₂.mem Np n = bytesAt s.mem Np n := by
    rw [hm₂]; exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_nw.sub_right (Lay.wSub L.le)) (by omega_using [hn])
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [hm₂, ctxH_eq, blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) L.le]
  have hji : J0In Ctx St W SP (ctxH s.mem Ctx) Np n s₂ N :=
    ⟨he₂, hH, h12, hbp, ⟨rdN, by have := (s.gpr .rdx).isLt; omega_using [hn], wn, d_ns, d_nw, k_n⟩⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (j0_ok v L hji hN) fun s₃ ho => ?_)
  have he₃ := ho.env
  have hret : s₃.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept ho.frame (fun r hr => ?_), hm₂, ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub L.le)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact r_s
      · exact r_w.sub_right (Lay.wSub L.le)
      · exact r_w.sub_right (Lay.wSub (Lay.leN hN))
      · exact Lay.gh_of_w G.fit r_w
      · exact ret_below SP
  refine WP.mono (exit_ok he₃.r15 (by rw [he₃.rsp, hSP]) (covers_left he₃.perm.w)
    ((hm₂ ▸ hsv₁).frame ho.frame (saved_j0Frame L hN G.fit)) (by rw [hSP, hret]) (by omega_using [hN])) fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ciph => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, ← hiv]
  refine ⟨ho.j0, Proof.Gcm.absorbed_nil _ ho.y, ho.cb, fun h => absurd rfl h⟩

end VG.Proof.AesGcm.X86_64

end

end


/-!
# AES-GCM on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key_scratch` and
`vg_ghash`), a state satisfying each precondition, and the shared contracts
of `Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`; with 8 bytes of stack, for the return address
of a call: the functions called make no calls, and 24 for those that call
`vg_aes_gcm_encrypt_blocks` or `vg_aes_gcm_decrypt_blocks` with an argument
on the stack).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`
(here, not in `Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String :=
  (v.ctr.features ++ v.gh.features ++ (v.stitch.map (·.features)).getD []).dedup

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

section
variable (v : GcmImpl)

theorem init_mx : (init v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_spSafe : (init v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_correct (s : State) (hs : Proof.AesGcm.initX86_64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

theorem streamInit_mx : (streamInit v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_spSafe : (streamInit v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_correct {N gs : Nat} [G : GhFits v N gs] (s : State) (hs : (Proof.AesGcm.streamInitX86_64 N).pre s)
    (hN : 224 ≤ N := by decide) (hN' : N < 2 ^ 64 := by decide) :
    ∃ t s', Exec isa (streamInit v.callees) s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.streamInitX86_64 N).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamInit_wp v hs hN hN'
  exact ⟨t, s', he, abiPreserved_of_exec (streamInit_mx v) he hg, hp⟩

theorem streamAad_mx : (streamAad v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_spSafe : (streamAad v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_correct {N gs : Nat} [G : GhFits v N gs] (s : State) (hs : (Proof.AesGcm.streamAadX86_64 N).pre s)
    (hN : 176 ≤ N := by decide) (hN' : N < 2 ^ 64 := by decide) :
    ∃ t s', Exec isa (streamAad v.callees) s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.streamAadX86_64 N).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamAad_wp v hs hN hN'
  exact ⟨t, s', he, abiPreserved_of_exec (streamAad_mx v) he hg, hp⟩

theorem streamEncrypt_mx : (streamEncrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mxB v v.stitch
  have d := decryptBlocks_mxB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_spSafe : (streamEncrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafeB v v.stitch
  have d := decryptBlocks_spSafeB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_correct (s : State) (hs : Proof.AesGcm.streamEncryptX86_64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncrypt_mx v) he hg, hp⟩

theorem streamDecrypt_mx : (streamDecrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mxB v v.stitch
  have d := decryptBlocks_mxB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_spSafe : (streamDecrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafeB v v.stitch
  have d := decryptBlocks_spSafeB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_correct (s : State) (hs : Proof.AesGcm.streamDecryptX86_64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecrypt_mx v) he hg, hp⟩

theorem streamFinish_mx : (streamFinish v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamFinish_spSafe : (streamFinish v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamFinish_correct {N gs : Nat} [G : GhFits v N gs] (T : TagCall v N) (hN : 208 ≤ N) (hN' : N < 2 ^ 64) (s : State)
    (hs : (Proof.AesGcm.streamFinishX86_64 N).pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.streamFinishX86_64 N).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamFinish_wp v T hN hN' hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamFinish_mx v) he hg, hp⟩

theorem streamVerify_mx : (streamVerify v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamVerify_spSafe : (streamVerify v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamVerify_correct {N gs : Nat} [G : GhFits v N gs] (T : TagCall v N) (hN : 272 ≤ N) (hN' : N < 2 ^ 64) (s : State)
    (hs : (Proof.AesGcm.streamVerifyX86_64 N).pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.streamVerifyX86_64 N).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamVerify_wp v T hN hN' hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamVerify_mx v) he hg, hp⟩

theorem seal_mx : («seal» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mxB v v.stitch
  have d := decryptBlocks_mxB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafeB v v.stitch
  have d := decryptBlocks_spSafeB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_correct (s : State) (hs : Proof.AesGcm.sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_mx : («open» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mxB v v.stitch
  have d := decryptBlocks_mxB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafeB v v.stitch
  have d := decryptBlocks_spSafeB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_correct (s : State) (hs : Proof.AesGcm.openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

end

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified (v : GcmImpl) :
    Verified X86_64.target (init v.callees) (Proof.AesGcm.initScratchContract X86_64.abi 8) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, Proof.AesGcm.initX86_64, Proof.AesGcm.initPreL, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSat] using initSat)

/-- `init_correct`, over callees that need no working space. -/
theorem initF_correct (v : GcmImpl) (fk : KeyFree v.key.fn.code) (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (s : State) (hs : Proof.AesGcm.initX86_64F.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v fk fc hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying `vg_aes_gcm_init`'s precondition, with 176 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x3000, 176⟩] }

theorem initF_verified (v : GcmImpl) (fk : KeyFree v.key.fn.code) (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target (init v.callees) (Proof.AesGcm.initScratchContractF X86_64.abi 8) :=
  Verified.of_correct (initF_correct v fk fc) (initF_ct v fk fc) (by
    sig_implies [Proof.AesGcm.initScratchContractF, Proof.AesGcm.initScratchSigF, Spec.Gcm.initPre, Spec.Gcm.initPost,
      Proof.AesGcm.initX86_64F, Proof.AesGcm.initX86_64, Proof.AesGcm.initPreF, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSatF, initSat] using initSatF)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamInit_verified (v : GcmImpl) :
    Verified X86_64.target (streamInit v.callees) (Proof.AesGcm.streamInitScratchContract X86_64.abi 8) :=
  Verified.of_correct (fun s hs => streamInit_correct v (N := 2560) s hs) (streamInit_ct v (N := 2560)) (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, Proof.AesGcm.streamInitX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [siSat] using siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x2000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamAad_verified (v : GcmImpl) :
    Verified X86_64.target (streamAad v.callees) (Proof.AesGcm.streamAadScratchContract X86_64.abi 8) :=
  Verified.of_correct (fun s hs => streamAad_correct v (N := 2560) s hs) (streamAad_ct v (N := 2560)) (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, Proof.AesGcm.streamAadX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [saSat] using saSat)

/-- `siSat`, with `k` words of working space. -/
def siSatK (k : Nat) : State := { siSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 8 * k⟩] }

/-- `saSat`, with `k` words of working space. -/
def saSatK (k : Nat) : State := { saSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 8 * k⟩] }

/-! ### `stream_init` and `stream_aad` with only the working space they use

The bytes they use themselves (`stream_init` `[0, 224)`, `stream_aad`
`[0, 176)`) and, if their `vg_ghash` touches its working space, its 256
bytes at 512 (`GhFits`): 768 bytes over `vg_ghash` (`_verified96`), and
over `vg_ghash_pclmul` and `vg_ghash_vpclmul` 224 (`streamInit_verified28`)
and 176 (`streamAad_verified22`), for the instances that
`vg_aes_gcm_seal_gather_prepared` does not call. -/

/-- `streamInitScratchSig`, with `scratch: *mut [u64; k]`. -/
def streamInitScratchSigK (k : Nat) : Sig where
  params := [("ctx", .array false .u64 32), ("nonce", .slice false .u8 "nonce_len"),
    ("state", .array true .u64 10), ("scratch", .array true .u64 k)]

/-- `Spec.Gcm.streamInitContract`, whatever `scratch` is (of `k` words). -/
def streamInitScratchContractK (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (streamInitScratchSigK k).contract A
    (post := fun ctx nonce nonceLen state _scratch => Spec.Gcm.streamInitPost A.ptrBits ctx nonce nonceLen state)
    (writeArgs := true) (stack := stack)

/-- `streamAadScratchSig`, with `scratch: *mut [u64; k]`. -/
def streamAadScratchSigK (k : Nat) : Sig where
  params := [("ctx", .array false .u64 32), ("state", .array true .u64 10),
    ("aad_len", .int .u64 true), ("data", .slice false .u8 "len"), ("scratch", .array true .u64 k)]

/-- `Spec.Gcm.streamAadContract`, whatever `scratch` is (of `k` words). -/
def streamAadScratchContractK (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (streamAadScratchSigK k).contract A
    (post := fun ctx state aadLen data len _scratch => Spec.Gcm.streamAadPost A.ptrBits ctx state aadLen data len)
    (writeArgs := true) (stack := stack)

theorem streamInit_verified96 (v : GcmImpl) :
    Verified X86_64.target (streamInit v.callees) (streamInitScratchContractK 96 X86_64.abi 8) :=
  Verified.of_correct (fun s hs => streamInit_correct v (N := 768) (G := GhFits.base v (by decide)) s hs)
    (streamInit_ct v (N := 768) (G := GhFits.base v (by decide))) (by
    sig_implies [streamInitScratchContractK, streamInitScratchSigK, Spec.Gcm.streamInitPost,
      Proof.AesGcm.streamInitX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [siSatK] using siSatK 96)

theorem streamAad_verified96 (v : GcmImpl) :
    Verified X86_64.target (streamAad v.callees) (streamAadScratchContractK 96 X86_64.abi 8) :=
  Verified.of_correct (fun s hs => streamAad_correct v (N := 768) (G := GhFits.base v (by decide)) s hs)
    (streamAad_ct v (N := 768) (G := GhFits.base v (by decide))) (by
    sig_implies [streamAadScratchContractK, streamAadScratchSigK, Spec.Gcm.streamAadPost,
      Proof.AesGcm.streamAadX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [saSatK] using saSatK 96)

theorem streamInit_verified28 (v : GcmImpl) (f : GhashFree v.gh.fn.code) :
    Verified X86_64.target (streamInit v.callees) (streamInitScratchContractK 28 X86_64.abi 8) :=
  Verified.of_correct (fun s hs => streamInit_correct v (N := 224) (G := GhFits.free v f 224) s hs)
    (streamInit_ct v (N := 224) (G := GhFits.free v f 224)) (by
    sig_implies [streamInitScratchContractK, streamInitScratchSigK, Spec.Gcm.streamInitPost,
      Proof.AesGcm.streamInitX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [siSatK] using siSatK 28)

theorem streamAad_verified22 (v : GcmImpl) (f : GhashFree v.gh.fn.code) :
    Verified X86_64.target (streamAad v.callees) (streamAadScratchContractK 22 X86_64.abi 8) :=
  Verified.of_correct (fun s hs => streamAad_correct v (N := 176) (G := GhFits.free v f 176) s hs)
    (streamAad_ct v (N := 176) (G := GhFits.free v f 176)) (by
    sig_implies [streamAadScratchContractK, streamAadScratchSigK, Spec.Gcm.streamAadPost,
      Proof.AesGcm.streamAadX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [saSatK] using saSatK 22)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no data, and `scratch` at 0). -/
def crSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamEncrypt v.callees) (Proof.AesGcm.streamEncryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamDecrypt v.callees) (Proof.AesGcm.streamDecryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition (with `work` at 0). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0, 2560⟩]

theorem streamFinish_verified (v : GcmImpl) :
    Verified X86_64.target (streamFinish v.callees) (Proof.AesGcm.streamFinishScratchContract X86_64.abi 8) :=
  Verified.of_correct (streamFinish_correct v (TagCall.base v) (by decide) (by decide))
    (streamFinish_ct v (TagCall.base v) (by decide) (by decide)) (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig, Spec.Gcm.streamFinishPre,
      Proof.AesGcm.streamFinishRoundsPost, Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSat] using finSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def verSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamVerify_verified (v : GcmImpl) :
    Verified X86_64.target (streamVerify v.callees) (Proof.AesGcm.streamVerifyScratchContract X86_64.abi 8) :=
  Verified.of_correct (streamVerify_correct v (TagCall.base v) (by decide) (by decide))
    (streamVerify_ct v (TagCall.base v) (by decide) (by decide)) (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig, Spec.Gcm.streamVerifyPre,
      Proof.AesGcm.streamVerifyRoundsPost, Proof.AesGcm.streamVerifyX86_64, Proof.AesGcm.verifyPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSat] using verSat)

/-! ### `stream_finish` and `stream_verify` with only the working space they use

Over an implementation of `vg_aes_ctr32` that needs no working space of its
own (`TagCall.free`): the bytes they use themselves (`finish` `[0, 208)`,
`verify` `[0, 272)`) and, if their `vg_ghash` touches its working space,
its 256 bytes at 512 (`GhFits`): 768 bytes over `vg_ghash` (`_verified96`),
and over `vg_ghash_pclmul` and `vg_ghash_vpclmul` 208
(`streamFinish_verified26`) and 272 (`streamVerify_verified34`). -/

/-- `finSat`, with `k` words of working space. -/
def finSatK (k : Nat) : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0, 8 * k⟩] }

/-- `verSat`, with `k` words of working space. -/
def verSatK (k : Nat) : State := { verSat with wr := [⟨0x3000, 80⟩, ⟨0, 8 * k⟩] }

/-- `Proof.AesGcm.streamFinishScratchSig`, with `work: *mut [u64; k]`. -/
def streamFinishScratchSigK (k : Nat) : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("tag", .array true .u8 16), ("work", .array true .u64 k)]

/-- `Proof.AesGcm.streamFinishRoundsContract`, whatever `work` is (of `k` words). -/
def streamFinishScratchContractK (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (streamFinishScratchSigK k).contract A
    (pre := fun ctx rounds state aadLen textLen tag _work =>
      Spec.Gcm.streamFinishPre A.ptrBits ctx rounds state aadLen textLen tag)
    (post := fun ctx rounds state aadLen textLen tag _work =>
      Proof.AesGcm.streamFinishRoundsPost A.ptrBits ctx rounds state aadLen textLen tag)
    (writeArgs := true) (stack := stack)

/-- `Proof.AesGcm.streamVerifyScratchSig`, with `work: *mut [u64; k]`. -/
def streamVerifyScratchSigK (k : Nat) : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("tag", .slice false .u8 "tag_len"), ("work", .array true .u64 k)]
  ret := some .u32

/-- `Proof.AesGcm.streamVerifyRoundsContract`, whatever `work` is (of `k` words). -/
def streamVerifyScratchContractK (k : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (streamVerifyScratchSigK k).contract A
    (pre := fun ctx rounds state aadLen textLen tag tagLen _work =>
      Spec.Gcm.streamVerifyPre A.ptrBits ctx rounds state aadLen textLen tag tagLen)
    (post := fun ctx rounds state aadLen textLen tag tagLen _work =>
      Proof.AesGcm.streamVerifyRoundsPost A.ptrBits ctx rounds state aadLen textLen tag tagLen)
    (writeArgs := true) (stack := stack)

theorem streamFinish_verified96 (v : GcmImpl) (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target (streamFinish v.callees) (streamFinishScratchContractK 96 X86_64.abi 8) :=
  Verified.of_correct
    (streamFinish_correct v (G := GhFits.base v (N := 768) (by decide)) (TagCall.free v f 768) (by decide) (by decide))
    (streamFinish_ct v (G := GhFits.base v (N := 768) (by decide)) (TagCall.free v f 768) (by decide) (by decide)) (by
    sig_implies [streamFinishScratchContractK, streamFinishScratchSigK, Spec.Gcm.streamFinishPre,
      Proof.AesGcm.streamFinishRoundsPost, Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSatK] using finSatK 96)

theorem streamVerify_verified96 (v : GcmImpl) (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target (streamVerify v.callees) (streamVerifyScratchContractK 96 X86_64.abi 8) :=
  Verified.of_correct
    (streamVerify_correct v (G := GhFits.base v (N := 768) (by decide)) (TagCall.free v f 768) (by decide) (by decide))
    (streamVerify_ct v (G := GhFits.base v (N := 768) (by decide)) (TagCall.free v f 768) (by decide) (by decide)) (by
    sig_implies [streamVerifyScratchContractK, streamVerifyScratchSigK, Spec.Gcm.streamVerifyPre,
      Proof.AesGcm.streamVerifyRoundsPost, Proof.AesGcm.streamVerifyX86_64, Proof.AesGcm.verifyPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSatK] using verSatK 96)

theorem streamFinish_verified26 (v : GcmImpl) (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (g : GhashFree v.gh.fn.code) :
    Verified X86_64.target (streamFinish v.callees) (streamFinishScratchContractK 26 X86_64.abi 8) :=
  Verified.of_correct
    (streamFinish_correct v (G := GhFits.free v g 208) (TagCall.free v f 208) (by decide) (by decide))
    (streamFinish_ct v (G := GhFits.free v g 208) (TagCall.free v f 208) (by decide) (by decide)) (by
    sig_implies [streamFinishScratchContractK, streamFinishScratchSigK, Spec.Gcm.streamFinishPre,
      Proof.AesGcm.streamFinishRoundsPost, Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSatK] using finSatK 26)

theorem streamVerify_verified34 (v : GcmImpl) (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    (g : GhashFree v.gh.fn.code) :
    Verified X86_64.target (streamVerify v.callees) (streamVerifyScratchContractK 34 X86_64.abi 8) :=
  Verified.of_correct
    (streamVerify_correct v (G := GhFits.free v g 272) (TagCall.free v f 272) (by decide) (by decide))
    (streamVerify_ct v (G := GhFits.free v g 272) (TagCall.free v f 272) (by decide) (by decide)) (by
    sig_implies [streamVerifyScratchContractK, streamVerifyScratchSigK, Spec.Gcm.streamVerifyPre,
      Proof.AesGcm.streamVerifyRoundsPost, Proof.AesGcm.streamVerifyX86_64, Proof.AesGcm.verifyPre, X86_64.abi, Proof.AesGcm.arg,
      Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSatK] using verSatK 34)

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or data, `tag` at
`0x3000` and `work` at 0). -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 2560⟩]

/-- `sealX86_64`, from the scratch contract. -/
theorem sealCode_implies :
    Proof.AesGcm.sealX86_64.Implies (Proof.AesGcm.sealScratchContract X86_64.abi 24) := by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost,
      Proof.AesGcm.sealX86_64, Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using sealSat

/-- `vg_aes_gcm_seal`'s contract, for any code that does what it says. -/
theorem sealCode_verified {c : Prog isa}
    (hc : ∀ s, Proof.AesGcm.sealX86_64.pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s')
    (hct : ConstantTime isa Proof.AesGcm.sealX86_64.pre Proof.AesGcm.sealX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.sealScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct sealCode_implies

theorem seal_verified (v : GcmImpl) :
    Verified X86_64.target («seal» v.callees) (Proof.AesGcm.sealScratchContract X86_64.abi 24) :=
  sealCode_verified (seal_correct v) (seal_ct v)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data, data or tag, and
`work` at 0). -/
def openSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds: `openX86_64` from the scratch contract. -/
theorem openCode_implies :
    Proof.AesGcm.openX86_64.Implies (Proof.AesGcm.openScratchContract X86_64.abi 24) :=
    { pre := by sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
        sig_simp [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [openSat] using openSat }

/-- `vg_aes_gcm_open`'s contract, for any code that does what it says. -/
theorem openCode_verified {c : Prog isa}
    (hc : ∀ s, Proof.AesGcm.openX86_64.pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s')
    (hct : ConstantTime isa Proof.AesGcm.openX86_64.pre Proof.AesGcm.openX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.openScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct openCode_implies

theorem open_verified (v : GcmImpl) :
    Verified X86_64.target («open» v.callees) (Proof.AesGcm.openScratchContract X86_64.abi 24) :=
  openCode_verified (open_correct v) (open_ct v)

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM on x86-64, with its working space on the stack

`init`, `stream_init` and `stream_aad` run their code, proved with the
working space as an argument (`Verified.lean`), in a frame of 2568 bytes that
allocates it (`Verified.stackScratchKept`): the 2560 bytes of working space, and
8 more to keep `rsp` aligned. Their own calls use 8 bytes below it, the
return address, as `vg_aes_expand_key_scratch`, `vg_aes_ctr32` and `vg_ghash` use no
stack (`KeyImpl.noStack`, `Ctr32Impl.noStack`, `GhashImpl.noStack`).

The working space of the others is their last argument, passed on the stack
after the six argument registers and their other stack arguments: their
frames (`Verified.stackArgScratchKept`) also hold a copy of those, 2584 bytes for
`stream_encrypt` and `stream_decrypt` (one), 2576 for `stream_finish` (none),
2584 for `stream_verify` (one), 2600 for `seal` (three) and 2608 for `open`
(four, and a leak, whether it succeeds, which reads only its buffers:
`openLeak_local`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

variable (v : GcmImpl)

theorem init_xdepth : (init v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamInit_xdepth : (streamInit v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamAad_xdepth : (streamAad v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem initFrameSatF_pre : ∃ s, (Spec.Gcm.initContract X86_64.abi 192).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.callees))
      (Spec.Gcm.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

/-- `init_framed`, over callees that need no working space: a frame of the
176 bytes `init` writes itself. -/
theorem initF_framed (fk : KeyFree v.key.fn.code) (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 184 .rcx (init v.callees))
      (Spec.Gcm.initContract X86_64.abi 192) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 22)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 184) (initF_verified v fk fc) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSatF_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { siSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86_64.abi, X86_64.argRegs] [streamInitFrameSat, siSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (streamInit v.callees))
      (Spec.Gcm.streamInitContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (streamInit_verified v) (by decide) (by decide) (by decide)
    (streamInit_spSafe v) (streamInit_xdepth v) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { saSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86_64.abi, X86_64.argRegs] [streamAadFrameSat, saSat] using streamAadFrameSat

theorem streamAad_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (streamAad v.callees))
      (Spec.Gcm.streamAadContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (streamAad_verified v) (by decide) (by decide) (by decide)
    (streamAad_spSafe v) (streamAad_xdepth v) streamAadFrameSat_pre

/-- `vg_aes_gcm_stream_init` in a frame of only the 768 bytes of working
space it uses over `vg_ghash` (`streamInit_verified96`). -/
theorem streamInitFrameSat96_pre : ∃ s, (Spec.Gcm.streamInitContract X86_64.abi 784).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86_64.abi, X86_64.argRegs] [streamInitFrameSat, siSat] using streamInitFrameSat

theorem streamInit_framed96 :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 776 .r8 (streamInit v.callees))
      (Spec.Gcm.streamInitContract X86_64.abi 784) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Gcm.streamInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 776) (streamInit_verified96 v) (by decide) (by decide) (by decide)
    (streamInit_spSafe v) (streamInit_xdepth v) streamInitFrameSat96_pre

/-- `vg_aes_gcm_stream_aad` in a frame of the 768 bytes it uses over `vg_ghash`. -/
theorem streamAadFrameSat96_pre : ∃ s, (Spec.Gcm.streamAadContract X86_64.abi 784).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86_64.abi, X86_64.argRegs] [streamAadFrameSat, saSat] using streamAadFrameSat

theorem streamAad_framed96 :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 776 .r9 (streamAad v.callees))
      (Spec.Gcm.streamAadContract X86_64.abi 784) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Gcm.streamAadPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 776) (streamAad_verified96 v) (by decide) (by decide) (by decide)
    (streamAad_spSafe v) (streamAad_xdepth v) streamAadFrameSat96_pre

/-- `vg_aes_gcm_stream_init` in a frame of only the 224 bytes it uses over a
`vg_ghash` that needs no working space (`streamInit_verified28`). -/
theorem streamInitFrameSat28_pre : ∃ s, (Spec.Gcm.streamInitContract X86_64.abi 240).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86_64.abi, X86_64.argRegs] [streamInitFrameSat, siSat] using streamInitFrameSat

theorem streamInit_framed28 (f : GhashFree v.gh.fn.code) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 232 .r8 (streamInit v.callees))
      (Spec.Gcm.streamInitContract X86_64.abi 240) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Spec.Gcm.streamInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 232) (streamInit_verified28 v f) (by decide) (by decide) (by decide)
    (streamInit_spSafe v) (streamInit_xdepth v) streamInitFrameSat28_pre

/-- `vg_aes_gcm_stream_aad` in a frame of the 176 bytes it uses over a
`vg_ghash` that needs no working space. -/
theorem streamAadFrameSat22_pre : ∃ s, (Spec.Gcm.streamAadContract X86_64.abi 192).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86_64.abi, X86_64.argRegs] [streamAadFrameSat, saSat] using streamAadFrameSat

theorem streamAad_framed22 (f : GhashFree v.gh.fn.code) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 184 .r9 (streamAad v.callees))
      (Spec.Gcm.streamAadContract X86_64.abi 192) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Spec.Gcm.streamAadPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 184) (streamAad_verified22 v f) (by decide) (by decide) (by decide)
    (streamAad_spSafe v) (streamAad_xdepth v) streamAadFrameSat22_pre

theorem streamEncrypt_xdepth : (streamEncrypt v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepthB v v.stitch
  have d := decryptBlocks_xdepthB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem streamDecrypt_xdepth : (streamDecrypt v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepthB v v.stitch
  have d := decryptBlocks_xdepthB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space: `len`, their one
stack argument, at `0x8008`. -/
def crFrameSat : State :=
  { crSat with rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt v.callees))
      (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncrypt_verified v) (by decide) (by decide) (by decide)
    (streamEncrypt_spSafe v) (streamEncrypt_xdepth v) (streamTextPre_local _) (streamEncryptPost_local _)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.streamDecryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt v.callees))
      (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecrypt_verified v) (by decide) (by decide) (by decide)
    (streamDecrypt_spSafe v) (streamDecrypt_xdepth v) (streamTextPre_local _) (streamDecryptPost_local _)
    streamDecryptFrameSat_pre

theorem streamFinish_xdepth : (streamFinish v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify,
    ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail,
    crypt, tag, j0hash, j0, firstFlush, finTag, tagLenOk, recv, cmp, tagOut, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamVerify_xdepth : (streamVerify v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify,
    ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail,
    crypt, tag, j0hash, j0, firstFlush, finTag, tagLenOk, recv, cmp, tagOut, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem seal_xdepth : («seal» v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepthB v v.stitch
  have d := decryptBlocks_xdepthB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, oneUndo, tagLenOk, recv, cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem open_xdepth : («open» v.callees).x86_64Depth ≤ 24 := by
  have e := encryptBlocks_xdepthB v v.stitch
  have d := decryptBlocks_xdepthB v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, oneUndo, tagLenOk, recv, cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract X86_64.abi 2584).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (streamFinish v.callees))
      (Proof.AesGcm.streamFinishRoundsContract X86_64.abi 2584) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2576) (streamFinish_verified v) (by decide) (by decide) (by decide)
    (streamFinish_spSafe v) (streamFinish_xdepth v) (streamFinishPre_local _)
    (streamFinishPost_local _) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State :=
  { verSat with rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract X86_64.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamVerify v.callees))
      (Proof.AesGcm.streamVerifyRoundsContract X86_64.abi 2592) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2584) (streamVerify_verified v) (by decide) (by decide) (by decide)
    (streamVerify_spSafe v) (streamVerify_xdepth v) (streamVerifyPre_local _)
    (streamVerifyPost_local _) verFrameSat_pre

/-- `vg_aes_gcm_stream_finish` over an implementation of `vg_aes_ctr32` that
needs no working space, in a frame of only the 768 bytes it uses
(`streamFinish_verified96`). -/
theorem finFrameSat96_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract X86_64.abi 792).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed96 (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamFinish v.callees))
      (Proof.AesGcm.streamFinishRoundsContract X86_64.abi 792) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 96) (pre := Spec.Gcm.streamFinishPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 784) (streamFinish_verified96 v f) (by decide) (by decide) (by decide)
    (streamFinish_spSafe v) (streamFinish_xdepth v) (streamFinishPre_local _)
    (streamFinishPost_local _) finFrameSat96_pre

/-- `vg_aes_gcm_stream_verify` over an implementation of `vg_aes_ctr32` that
needs no working space, in a frame of the 768 bytes it uses. -/
theorem verFrameSat96_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract X86_64.abi 800).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed96 (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 792 1 (streamVerify v.callees))
      (Proof.AesGcm.streamVerifyRoundsContract X86_64.abi 800) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 96) (pre := Spec.Gcm.streamVerifyPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 792) (streamVerify_verified96 v f) (by decide) (by decide) (by decide)
    (streamVerify_spSafe v) (streamVerify_xdepth v) (streamVerifyPre_local _)
    (streamVerifyPost_local _) verFrameSat96_pre

/-- `vg_aes_gcm_stream_finish` over implementations of `vg_aes_ctr32` and
`vg_ghash` that need no working space, in a frame of the 208 bytes it uses
itself (`streamFinish_verified26`). -/
theorem finFrameSat26_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract X86_64.abi 232).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed26 (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (g : GhashFree v.gh.fn.code) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 224 0 (streamFinish v.callees))
      (Proof.AesGcm.streamFinishRoundsContract X86_64.abi 232) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 26) (pre := Spec.Gcm.streamFinishPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 224) (streamFinish_verified26 v f g) (by decide) (by decide) (by decide)
    (streamFinish_spSafe v) (streamFinish_xdepth v) (streamFinishPre_local _)
    (streamFinishPost_local _) finFrameSat26_pre

/-- `vg_aes_gcm_stream_verify` over implementations of `vg_aes_ctr32` and
`vg_ghash` that need no working space, in a frame of the 272 bytes it uses
itself (`streamVerify_verified34`). -/
theorem verFrameSat34_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract X86_64.abi 304).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed34 (f : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) (g : GhashFree v.gh.fn.code) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 296 1 (streamVerify v.callees))
      (Proof.AesGcm.streamVerifyRoundsContract X86_64.abi 304) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 34) (pre := Spec.Gcm.streamVerifyPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 296) (streamVerify_verified34 v f g) (by decide) (by decide) (by decide)
    (streamVerify_spSafe v) (streamVerify_xdepth v) (streamVerifyPre_local _)
    (streamVerifyPost_local _) verFrameSat34_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcm.sealRoundsContract X86_64.abi 2624).pre s := by
  implies_sat [Proof.AesGcm.sealRoundsContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

/-- `vg_aes_gcm_seal` in its frame, for any code that meets the contract
within it. -/
theorem sealCode_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.sealScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 c)
      (Proof.AesGcm.sealRoundsContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) hv (by decide) (by decide) (by decide)
    hsp hxd (sealPre_local _) (sealPost_local _) sealFrameSat_pre

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («seal» v.callees))
      (Proof.AesGcm.sealRoundsContract X86_64.abi 2624) :=
  sealCode_framed (seal_verified v) (seal_spSafe v) (seal_xdepth v)

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcm.openRoundsContract X86_64.abi 2632).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost,
    Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using openFrameSat

/-- `vg_aes_gcm_open` in its frame, for any code that meets the contract
within it. -/
theorem openCode_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.openScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 c)
      (Proof.AesGcm.openRoundsContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) hv
    (by decide) (by decide) (by decide) hsp hxd (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callees))
      (Proof.AesGcm.openRoundsContract X86_64.abi 2632) :=
  openCode_framed (open_verified v) (open_spSafe v) (open_xdepth v)

end VG.Proof.AesGcm.X86_64
