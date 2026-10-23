module

import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTText
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTText
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments, which it keeps in registers the pieces
preserve (`DI`); then `crypt` (`crypt_ct`) and `textAbsorb`
(`textAbsorb_ct`), in either order, from the invariants their correctness
gives; then the exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- After the entry: the arguments kept, `len` (`N`) bytes at `data` (`D`),
after `aad_len` (`A`) bytes of additional data and `text_len` (`T`) of
text, and `R` rounds. -/
def DI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r20 = D ∧ V .r19 = N ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r28 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ Env V sp s ∧ DataW c st w s D N.toNat

/-- Before `crypt`, with the arguments kept. -/
def CI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r20 = D ∧ V .r19 = N ∧ V .r22 = A ∧ V .r23 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn V sp R icb P D N.toNat s

theorem cryptEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) (.block cryptEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptEntryArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) (.block (cryptEntry ++ textArgs)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r19, .r20, .r23])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

/-- The entry. -/
theorem sc_DI {s₀ : State} (h : streamCryptPre s₀) :
    WP isa (.block cryptEntry) s₀ (DI (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r10) s₀.sp (s₀.gpr .r8)
      (s₀.gpr .r4).toNat (s₀.gpr .r9) (s₀.gpr .r6) (s₀.gpr .r7)) :=
  WP.mono (sc1_wp (sc_W h)) fun s₁ h1 => ⟨s₁.gpr, h1.r29, h1.r30, h1.r31, h1.r20, h1.r19, h1.r22, h1.r23,
    by rw [h1.r28, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.2.2.2.2.2.2.2.2.2.2.2.2, sc_env h h1,
    sc_dataW h h1.en.keeps.wr⟩

section
variable {c st w sp D : Addr} {R : Nat} {N A T : BitVec 64}

theorem di_ta {s : State} (h : DI c st w sp D R N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, _, _, he, hd⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem ci_cr {s : State} (h : CI c st w sp D R N A T s) : CrI c st w sp R D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci⟩

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .r31 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

/-- The arguments of `crypt`. -/
theorem di_textArgs {s : State} (h : DI c st w sp D R N A T s) :
    WP isa (.block textArgs) s (CI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], h28, hR, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr⟩

variable (L : Lay c st w)
include L

theorem ci_crypt {s : State} (h : CI c st w sp D R N A T s) : WP isa crypt s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci⟩ := h
  refine WP.mono (WP.with_rdwr (crypt_ok (L.v h29 h30 h31) ci)) fun s' ⟨co, rd, wr, _⟩ =>
    ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr
  rw [h30, h31] at this
  exact this

theorem di_textAbsorb {s : State} (h : DI c st w sp D R N A T s) :
    WP isa textAbsorb s (DI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono (WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, _⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, ta.env,
      hd.of_eq rd wr⟩

theorem ta_textAbsorb {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .r31 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

/-- The invariant of the entry, from the public arguments of `σ`. -/
abbrev SCI (σ : State) (s : State) : Prop :=
  streamCryptPre s ∧ s.gpr .r3 = σ.gpr .r3 ∧ s.gpr .r4 = σ.gpr .r4 ∧ s.gpr .r5 = σ.gpr .r5 ∧
    s.gpr .r6 = σ.gpr .r6 ∧ s.gpr .r7 = σ.gpr .r7 ∧ s.gpr .r8 = σ.gpr .r8 ∧ s.gpr .r9 = σ.gpr .r9 ∧
    s.gpr .r10 = σ.gpr .r10 ∧ s.sp = σ.sp

theorem sci_of {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂) (hq : streamCryptPub σ₁ σ₂) :
    SCI σ₁ σ₁ ∧ SCI σ₁ σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  exact ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm⟩⟩

theorem sci_DI {σ s : State} (h : SCI σ s) :
    WP isa (.block cryptEntry) s (DI (σ.gpr .r3) (σ.gpr .r5) (σ.gpr .r10) σ.sp (σ.gpr .r8)
      (σ.gpr .r4).toNat (σ.gpr .r9) (σ.gpr .r6) (σ.gpr .r7)) := by
  obtain ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ := h
  have := sc_DI hs
  rw [e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
  exact this

theorem streamEncrypt_ct :
    ConstantTime isa streamEncryptPPC64LE.pre streamEncryptPPC64LE.pub streamEncrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := CI (σ₁.gpr .r3) (σ₁.gpr .r5) (σ₁.gpr .r10) σ₁.sp (σ₁.gpr .r8) (σ₁.gpr .r4).toNat
    (σ₁.gpr .r9) (σ₁.gpr .r6) (σ₁.gpr .r7)) ?_
    (fun s h => WP.block_append (WP.mono (sci_DI h) fun _ h' => di_textArgs h')) ?_
  · obtain ⟨_, hc⟩ := cryptEntryArgs_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r10) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecrypt_ct :
    ConstantTime isa streamDecryptPPC64LE.pre streamDecryptPPC64LE.pub streamDecrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := DI (σ₁.gpr .r3) (σ₁.gpr .r5) (σ₁.gpr .r10) σ₁.sp (σ₁.gpr .r8) (σ₁.gpr .r4).toNat
    (σ₁.gpr .r9) (σ₁.gpr .r6) (σ₁.gpr .r7)) ?_ (fun s h => sci_DI h) ?_
  · obtain ⟨_, hc⟩ := cryptEntry_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => di_ta h) (fun _ h => di_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => di_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, _, _, e₁, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, _, _, e₂, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r10) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

end VG.Proof.AesGcm.PPC64LE
