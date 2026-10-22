module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256

/-!
# The x86 RSA padding functions: their calls of SHA-256 and HMAC-SHA-256

SHA-256's streaming `init`, `update` and `finalize` and HMAC-SHA-256's
`init` and `finalize`, made with one backend `v` (`Backend.F`), each called
in a frame of its arguments (`Proof/Pbkdf2/Stream/X86/Hash.lean`,
`Proof/Pbkdf2/Whole/X86/Calls.lean`), as a stage `VP` of a function: from
states whose arguments each stage fixes, with the same `esp` in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs UpdArgs FinArgs After init_frame upd_frame fin_frame init_rel
  upd_rel fin_rel upd6 fin5)
open VG.Proof.Pbkdf2.Whole.X86 (HiArgs HfArgs hi_frame hf_frame hi_rel hf_rel hi5 hf6 sha256OKF)

/-- SHA-256's streaming functions with the backend `v`, verified. -/
abbrev hk (v : Backend) : Proof.Pbkdf2.Stream.X86.HashOK v.F.H := (sha256OKF v).hH

variable {F G : State → State → Prop} (v : Backend) {sp : BitVec 32}

namespace VP

/-- SHA-256's `init` of the state at `st` (in `edi`). -/
theorem shaInit {st : BitVec 32} (hA : ∀ σ s, F σ s → InitArgs (H := v.F.H) s .edi st ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s', After s [⟨st.setWidth 64, 96⟩] s' →
      Spec.Sha256.Repr s'.mem (st.setWidth 64) [] → G σ s') :
    VP F (.frame (.push [.edi]) (.call v.F.H.initN v.F.H.initC) (.pop .eax 1)) G :=
  of_ct (fun _ _ => init_rel (hk v) (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => init_frame (hk v) (hA σ s h).1 (hG σ s h)

/-- SHA-256's `update` of the state at `st` (in `edi`), at the count `c`
(in `esi`), with `len` bytes at `d` and the working space at `sc`. -/
theorem shaUpd {st d sc c : BitVec 32} {len : Nat}
    (hA : ∀ σ s, F σ s → UpdArgs (hk v) s .esi .edi st d sc c len ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s', After s [⟨st.setWidth 64, 96⟩, ⟨sc.setWidth 64, 160⟩] s' →
      (∀ m, Spec.Sha256.Repr s.mem (st.setWidth 64) m → (0 : BitVec 32) ++ c = BitVec.ofNat 64 m.length →
        Spec.Sha256.Repr s'.mem (st.setWidth 64) (m ++ Spec.Sha256.bytesAt s.mem (d.setWidth 64) len)) → G σ s') :
    VP F (.frame (.push (upd6 .esi .edi)) (.call v.F.H.updN v.F.H.updC) (.pop .eax 6)) G :=
  of_ct (fun _ _ => upd_rel (hk v) (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => upd_frame (hk v) (hA σ s h).1 (hG σ s h)

/-- SHA-256's `finalize` of the state at `st` (in `edi`), at the count
`hi ++ lo`, to `o`, with the working space at `sc`. -/
theorem shaFin {st o sc lo hi : BitVec 32}
    (hA : ∀ σ s, F σ s → FinArgs (hk v) s .edi st o sc lo hi ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s', After s [⟨st.setWidth 64, 96⟩, ⟨o.setWidth 64, 32⟩, ⟨sc.setWidth 64, 160⟩] s' →
      (∀ m, Spec.Sha256.Repr s.mem (st.setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt s'.mem (o.setWidth 64) 32 = Spec.Sha256.hash m) → G σ s') :
    VP F (.frame (.push (fin5 .edi)) (.call v.F.H.finN v.F.H.finC) (.pop .eax 5)) G :=
  of_ct (fun _ _ => fin_rel (hk v) (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => fin_frame (hk v) (hA σ s h).1 fun s' ha hp => hG σ s h s' ha fun m hr hl hc => by
      have := hp m hr hl hc
      rwa [List.take_of_length_le (by simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]; exact Nat.le_refl _)] at this

/-- HMAC's `init` of the states at `inn` and `ou` with `kl` bytes of key at
`k`, and the working space at `sc`. -/
theorem macInit {inn ou k sc : BitVec 32} {kl : Nat}
    (hA : ∀ σ s, F σ s → HiArgs (hk v).SH 104 s inn ou k sc kl ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s',
      Proof.Pbkdf2.Whole.X86.After s [⟨inn.setWidth 64, 96⟩, ⟨ou.setWidth 64, 96⟩, ⟨sc.setWidth 64, 832⟩] s' →
      Spec.Sha256.Repr s'.mem (inn.setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt s.mem (k.setWidth 64) kl)) Spec.Hmac.ipad) →
      Spec.Sha256.Repr s'.mem (ou.setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt s.mem (k.setWidth 64) kl)) Spec.Hmac.opad) → G σ s') :
    VP F (.frame (.push hi5) (.call v.F.hiN v.F.hiC) (.pop .eax 5)) G :=
  of_ct (fun _ _ => hi_rel (sha256OKF v).hi (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => hi_frame (sha256OKF v).hi (sha256OKF v).hiSp (sha256OKF v).hiSU (hA σ s h).1 (hG σ s h)

/-- HMAC's `finalize` of the states at `inn` and `ou`, at the count
`hi ++ lo`, to `o`, with the working space at `sc`. -/
theorem macFin {inn ou lo hi o sc : BitVec 32}
    (hA : ∀ σ s, F σ s → HfArgs (hk v).SH 104 s inn ou lo hi o sc ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s',
      Proof.Pbkdf2.Whole.X86.After s [⟨inn.setWidth 64, 96⟩, ⟨o.setWidth 64, 32⟩, ⟨sc.setWidth 64, 832⟩] s' →
      (∀ k0 text, k0.length = 64 → k0.length + text.length < 2 ^ 64 →
        Spec.Sha256.Repr s.mem (inn.setWidth 64) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text) →
        hi ++ lo = BitVec.ofNat 64 (64 + text.length) →
        Spec.Sha256.Repr s.mem (ou.setWidth 64) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) →
        Spec.Sha256.bytesAt s'.mem (o.setWidth 64) 32 = Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 text) → G σ s') :
    VP F (.frame (.push hf6) (.call v.F.hfN v.F.hfC) (.pop .eax 6)) G :=
  of_ct (fun _ _ => hf_rel (sha256OKF v).hf (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => hf_frame (S := (hk v).SH) (Wf := 104) Hmac.Generic.Common.sha256_repr (by show 96 ≤ 2 ^ 64; decide) (sha256OKF v).hf (sha256OKF v).hfSp
      (sha256OKF v).hfSU (hA σ s h).1 (hG σ s h)

end VP

end VG.Proof.RsaPkcs1Sig.X86
