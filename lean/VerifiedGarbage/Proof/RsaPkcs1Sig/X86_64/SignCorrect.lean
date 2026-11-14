module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# `vg_rsa_pkcs1_sign` on x86-64: correctness

The encoding into `EM`, then zeros to `out` if it fails, or the private
operation on `EM` and zeros to `EM` (`afterEnc_ok`); the whole function
(`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (test0_ok freed)

theorem writtenOutcome_of {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out n = Spec.Rsa.bytesAt m out n) (h : Spec.Rsa.writtenOutcome m out n r o) :
    Spec.Rsa.writtenOutcome m' out n r o := by
  cases o <;> exact ⟨h.1, hb.trans h.2⟩

/-- The result of the private operation on the encoding `o`, or `invalid`. -/
def privOut (s : State) : Option (List Byte) → Spec.Rsa.Outcome
  | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) em
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
  | none => .invalid

/-- What the call of the private operation on `EM` (`em`, in `t`) gives:
`out` holds its result. -/
def CallOut (s t : State) (em : List Byte) (u : State) : Prop :=
  EnvC s u ∧
    Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32) (privOut s (some em)) ∧
    (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10

/-- After the encoding, whose result is `o`, with the arguments `args` of
the call `call` (`hcall`). -/
theorem afterEncWith_ok {args : List Instr} {privName : String} {priv : Prog isa} {s t₁ t₂ : State} (hp : PreS s)
    (he₁ : Env s t₁) (h8₁ : t₁.gpr .r8 = off (fb s) oEM) (hK₂ : Keep clob t₁ t₂) {o : Option (List Byte)}
    (hlen : ∀ em, o = some em → em.length = (s.gpr .rcx).toNat) (hpost : EOut t₁ t₂ o)
    (hcall : ∀ t em, Env s t → Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (s.gpr .rcx).toNat = em →
      WP isa (.block args) t fun u => WP isa (.call privName priv) u (CallOut s t em)) :
    WP isa (afterEncWith args privName priv) t₂ fun u => EnvC s u ∧
      Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32)
        (privOut s o) ∧
      (∀ r ∈ calleeSaved, u.gpr r = t₂.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t₂.mxcsr.extractLsb' 6 10 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  unfold afterEncWith
  refine WP.seq (WP.mono_mx (by decide) (test0_ok t₂) fun t₃ ⟨hs₃, hz₃⟩ hmx₃ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₂⟩ := hpost
    have he₃ : Env s t₃ := he₁.regs (by rw [hs₃.1, hK₂.gpr (by decide)]) (hs₃.2.1.trans hm₂)
      (hs₃.2.2.1.trans hK₂.2.1) (hs₃.2.2.2.trans hK₂.2.2)
    refine WP.ite true (by simp [eval, hz₃, hax]) (fun _ => ?_) (by simp)
    refine WP.mono_mx (by decide) (WP.keep [.rdi, .rsi, .r8, .r10, .rax] (zeroSlots_ok hp he₃) (by decide))
      fun u ⟨⟨heu, hax', hout⟩, ku⟩ hmx => ⟨heu.core, ⟨hax', hout⟩, fun r hr => ?_, by rw [hmx, hmx₃]⟩
    rw [ku.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
      hs₃.1]
  | some em =>
    obtain ⟨hax, hm₂⟩ := hpost
    have hl : em.length = (s.gpr .rcx).toNat := hlen em rfl
    have he₂ : Env s t₂ := Env.of he₁ hp (hK₂.gpr (by decide)) hK₂.2.1 hK₂.2.2 (hm₂ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₁, hl], .inr (Nat.le_refl _),
        by unfold oEM frameBytes; omega_using [hk2]⟩
    have he₃ : Env s t₃ := he₂.regs (by rw [hs₃.1]) hs₃.2.1 hs₃.2.2.1 hs₃.2.2.2
    have hEM : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM) (s.gpr .rcx).toNat = em := by
      have h₂ := bytesAt_writeBytes t₁.mem (off (fb s) oEM) em (by omega_using [hl])
      rw [hl] at h₂
      rw [hs₃.2.1, hm₂, h8₁, h₂]
    refine WP.ite false (by simp [eval, hz₃, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (hcall t₃ em he₃ hEM) fun t₄ h₄ => WP.seq (WP.mono h₄
      fun t₅ ⟨he₅, hout₅, hcs₅, hmx₅⟩ => ?_))
    refine WP.mono_mx (by decide) (WP.keep [.r11, .rdx, .r10] (wipe_ok hp he₅) (by decide))
      fun u ⟨⟨heu, haxu, hbytes⟩, ku⟩ hmxu => ⟨heu, ?_, fun r hr => ?_, ?_⟩
    · rw [haxu]; exact writtenOutcome_of hbytes hout₅
    · rw [ku.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        hcs₅ r hr, hs₃.1]
    · rw [hmxu, hmx₅, hmx₃]

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (freed frameBytes s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (freed frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreS s) {m : Mem} (h : Frame [stkR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := sigStack) (d := 0) (k := 8)
      (by unfold sigStack; omega_using [])
    simpa only [stkR, kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem signId_eq (nB eB pB qB dPB dQB qInvB : List Byte) (x : BitVec 32) (H : List Byte) :
    Spec.RsaPkcs1Sig.signId nB eB pB qB dPB dQB qInvB x.toNat H =
      match encodeId x H nB.length with
      | some em => Spec.Rsa.privateChecked nB eB em pB qB dPB dQB qInvB
      | none => .invalid := by
  unfold Spec.RsaPkcs1Sig.signId encodeId Spec.RsaPkcs1Sig.sign
  cases Spec.RsaPkcs1Sig.Hash.ofId x.toNat <;> rfl

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em : List Byte}
    (h : encodeId x H k = some em) : em.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- The function, with the code `ae` after the encoding, which does what
`afterEnc_ok` says (`hae`). -/
theorem codeWith_ok {ae : Prog isa} {s : State} (hp : PreS s)
    (hae : ∀ {t₁ t₂ : State}, Env s t₁ → t₁.gpr .r8 = off (fb s) oEM → Keep clob t₁ t₂ → ∀ {o : Option (List Byte)},
      (∀ em, o = some em → em.length = (s.gpr .rcx).toNat) → EOut t₁ t₂ o →
      WP isa ae t₂ fun u => EnvC s u ∧
        Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32) (privOut s o) ∧
        (∀ r ∈ calleeSaved, u.gpr r = t₂.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t₂.mxcsr.extractLsb' 6 10) :
    WP isa (.frame (.alloc frameBytes) (.seq (.block (slotStores ++ encArgs)) (.seq encode ae)) (.free frameBytes)) s
      fun s' => abiPreserved s s' ∧ sigContract.post s s' := by
  have hk2 := hp.k2
  refine wp_alloc (by have := hp.sp1; unfold sigStack at this; unfold frameBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono_mx (by decide) (head_ok hp) fun t₁ ⟨he₁, h8₁, hcx₁, hdx₁, hsi₁, h9₁, hcs₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (encode_ok (encPre hp he₁ h8₁ hcx₁ hdx₁ hsi₁ h9₁))
    fun t₂ ⟨hK₂, hout₂⟩ hmx₂ => ?_)
  refine WP.mono (hae he₁ h8₁ hK₂ (fun em h' => encodeId_length h') hout₂)
    fun u ⟨heu, hwu, hcsu, hmxu⟩ => ⟨heu.rsp, by rw [heu.wr]; rfl, ⟨fun r hr => ?_, ret_frame hp heu.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show u.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [heu.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else u.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcsu r hr, hK₂.gpr (by simp [calleeSaved, clob] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all),
        hcs₁ r hr hr']
  · show u.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmxu, hmx₂, hmx₁]; rfl
  · show Spec.Rsa.writtenOutcome u.mem _ _ _ _
    have hH : Spec.Rsa.bytesAt t₁.mem (t₁.gpr .rsi) (t₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat := by
      rw [hsi₁, h9₁]
      exact bytes_of_frame he₁.mem hp.dKd hp.dOd hp.dds.symm (by have := hp.wD; omega_using [])
    rw [signId_eq, bytesAt_length, ← hH]
    exact hwu

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
