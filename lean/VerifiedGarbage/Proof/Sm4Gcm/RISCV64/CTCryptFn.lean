module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTCryptFn.lean`): the entry by the taint analysis
from the public arguments, which it keeps in registers the pieces preserve
(`DI`); then `crypt` (`crypt_ct`) and `textAbsorb` (`textAbsorb_ct`), in
either order, from the invariants their correctness gives; then the exit
from `W`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (textArgs textAbsorb restore)
open VG.Proof.AesGcm.RISCV64 (CT ct_of CT.taintEq Env Lay DataW TA textAbsorb_ct textAbsorb_ok textArgs_ok
  restore_taint)

/-- After the entry: the arguments kept, `len` (`N`) bytes at `data` (`D`),
after `aad_len` (`A`) bytes of additional data and `text_len` (`T`) of
text. -/
def DI (c st w sp D : Addr) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s ∧ Big V sp ∧ (below sp 3232).Disjoint ⟨D, N.toNat⟩ ∧ DataW c st w s D N.toNat

/-- Before `crypt`, with the arguments kept. -/
def CI (c st w sp D : Addr) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧ V .s11 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn V sp icb P D N.toNat s

theorem cryptEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block cryptEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptEntryArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block (cryptEntry ++ textArgs)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s11])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

/-- The entry. -/
theorem sc_DI {s₀ : State} (h : streamCryptPre s₀) :
    WP isa (.block cryptEntry) s₀ (DI (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀.sp (s₀.gpr .a4)
      (s₀.gpr .a5) (s₀.gpr .a2) (s₀.gpr .a3)) :=
  WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8, h1.s10, h1.s11,
    sc_env h h1, sc_big h h1.s2 h1.s1 h1.s0, sc_bd h, sc_dataW h h1.en.keeps.wr h1.en.keeps.sp⟩

section
variable {c st w sp D : Addr} {N A T : BitVec 64}

theorem di_ta {s : State} (h : DI c st w sp D N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, he, _, _, hd⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem ci_cr {s : State} (h : CI c st w sp D N A T s) : CrI c st w sp D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci⟩

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .s0 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

/-- The arguments of `crypt`. -/
theorem di_textArgs {s : State} (h : DI c st w sp D N A T s) :
    WP isa (.block textArgs) s (CI c st w sp D N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hb, hbd, hd⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], hb, hbd, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr hk.sp⟩

variable (L : Lay c st w)
include L

theorem ci_crypt {s : State} (h : CI c st w sp D N A T s) : WP isa crypt s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci⟩ := h
  refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (crypt_ok (L.v h29 h30 h31) ci)) fun s' ⟨co, rd, wr, sp'⟩ =>
    ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr sp'
  rw [h30, h31] at this
  exact this

theorem di_textAbsorb {s : State} (h : DI c st w sp D N A T s) :
    WP isa textAbsorb s (DI c st w sp D N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hb, hbd, hd⟩ := h
  refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, sp'⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, ta.env, hb, hbd,
      hd.of_eq rd wr sp'⟩

theorem ta_textAbsorb {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

/-- The invariant of the entry, from the public arguments of `σ`. -/
abbrev SCI (σ : State) (s : State) : Prop :=
  streamCryptPre s ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧ s.gpr .a2 = σ.gpr .a2 ∧
    s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧ s.gpr .a6 = σ.gpr .a6 ∧
    s.sp = σ.sp

theorem sci_of {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂) (hq : streamCryptPub σ₁ σ₂) :
    SCI σ₁ σ₁ ∧ SCI σ₁ σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  exact ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, qsp.symm⟩⟩

theorem sci_DI {σ s : State} (h : SCI σ s) :
    WP isa (.block cryptEntry) s (DI (σ.gpr .a0) (σ.gpr .a1) (σ.gpr .a6) σ.sp (σ.gpr .a4)
      (σ.gpr .a5) (σ.gpr .a2) (σ.gpr .a3)) := by
  obtain ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ := h
  have := sc_DI hs
  rw [e3, e4, e5, e6, e7, e8, e9, esp] at this
  exact this

theorem streamEncrypt_ct :
    ConstantTime isa streamEncryptRISCV64.pre streamEncryptRISCV64.pub streamEncrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := CI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a4)
    (σ₁.gpr .a5) (σ₁.gpr .a2) (σ₁.gpr .a3)) ?_
    (fun s h => WP.block_append (WP.mono (sci_DI h) fun _ h' => di_textArgs h')) ?_
  · obtain ⟨_, hc⟩ := cryptEntryArgs_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecrypt_ct :
    ConstantTime isa streamDecryptRISCV64.pre streamDecryptRISCV64.pub streamDecrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := DI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a4)
    (σ₁.gpr .a5) (σ₁.gpr .a2) (σ₁.gpr .a3)) ?_ (fun s h => sci_DI h) ?_
  · obtain ⟨_, hc⟩ := cryptEntry_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => di_ta h) (fun _ h => di_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => di_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, e₁, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, e₂, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64
