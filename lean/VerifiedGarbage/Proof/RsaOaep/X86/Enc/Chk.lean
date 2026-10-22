module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Base
public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: the checks

As on ARMv7 (`Proof/RsaOaep/Arm/EncChk.lean`): `chk_vp`: `scratch` into
`ebp`, and the flags of whether the message fits (`fits`), from the lengths
alone. `fail_vp`: when it does not, zeros to `out` and 0 returned, as
`encrypt` (`Proof.RsaOaep.encrypt_none`) says.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa arg ld mi zeroLoop)

variable (h g : OHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.H.D P σ ∧ (P.lay h.H.D).St σ s

/-- The label, the message and the seed, as they are in the run from `σ`. -/
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.lab.setWidth 64) P.ll
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.msg.setWidth 64) P.ml
abbrev seedB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.seed.setWidth 64) h.H.D

/-- Whether the message fits. -/
abbrev fits (P : EP) : Prop := 2 * h.H.D + 2 + P.ml ≤ P.K

/-- What the function writes to `out` and returns. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r (Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ)
      (seedB h P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h g P σ s.mem (s.gpr .eax)

theorem enc_arg {j : Nat} (hj : j < 15) {D : Nat} {P : EP} : j < ((P.lay D).argv).length := by simp; omega

/-- An argument's place may be read. -/
theorem argR {D : Nat} {P : EP} {σ t : State} (hg : Geo (P.lay D) P.scr) (ct : Ctx (P.lay D) P.scr σ t) {j : Nat}
    (hj : j < 15) : InRegions (t.rd ++ t.wr) (VG.X86.addr (P.lay D).B (Impl.RsaPkcs1Sig.X86.argOff frameBytes j)) 4 := by
  rw [hg.aArg ct.st.ok j (enc_arg hj), ct.st.rd, ct.st.wr]; exact ct.st.ok.arg_read (enc_arg hj)

/-- The flags of the checks: zero exactly when `c + ml ≤ K`. -/
theorem chk_z {K c ml : Nat} (hK : K < 2 ^ 32) (hc : c < 2 ^ 32) (hml : ml < 2 ^ 32) :
    let x := (if decide ((BitVec.ofNat 32 K).toNat < (BitVec.ofNat 32 c).toNat) = true then BitVec.allOnes 32 else 0) |||
      (if decide ((BitVec.ofNat 32 K - BitVec.ofNat 32 c).toNat < (BitVec.ofNat 32 ml).toNat) = true then
        BitVec.allOnes 32 else 0)
    (x &&& x == 0) = decide (c + ml ≤ K) := by
  intro x
  rw [BitVec.and_self]
  simp only [x, toNat_ofNat_lt hK, toNat_ofNat_lt hc, toNat_ofNat_lt hml]
  by_cases hcK : K < c
  · have h1 : decide (c + ml ≤ K) = false := decide_eq_false (by omega)
    rw [decide_eq_true hcK, h1]
    simp
  · rw [decide_eq_false hcK, sub_ofNat (by omega), toNat_ofNat_lt (by omega)]
    by_cases e : K - c < ml
    · rw [decide_eq_true e, decide_eq_false (by omega)]; simp
    · rw [decide_eq_false e, decide_eq_true (by omega)]; simp

/-! ## The checks -/

/-- After `encChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ s.zf = some (decide (fits h P))

theorem chk_vp (P : EP) : VP (S h P) (.block (encChk h.H)) (C0 h P) := by
  refine VP.taint [.esp] h.certs.encChk (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD := h.D_le
  have hK := hi.k1024
  simp only [encChk, ld, Impl.RsaPkcs1Sig.X86.stk]
  refine hs.wp_arg (enc_arg (j := 11) (by decide)) (by decide) fun t1 s1 u1 => ?_
  have c1 : Ctx (P.lay h.H.D) P.scr σ t1 := ⟨s1, by rw [u1.gpr]; rfl⟩
  refine c1.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine wp_subi fun t3 u3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => ?_
  have c4 : Ctx (P.lay h.H.D) P.scr σ t4 := (c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
  refine wp_cmpm (B := (P.lay h.H.D).B) (by rw [c4.st.sp])
    (by rw [hg.aArg ok 9 (enc_arg (by decide)), c4.st.rd, c4.st.wr]; exact c4.st.ok.arg_read (enc_arg (by decide)))
    fun t5 f5 cf5 _ => wp_sbb_self cf5 fun t6 u6 => ?_
  refine wp_or fun t7 u7 => wp_test fun t8 f8 z8 => WP.block_nil ⟨Ctx.fupd (((c4.fupd f5).upd u6 (by decide)
    (by decide)).upd u7 (by decide) (by decide)) f8, hi, ?_⟩
  rw [z8]
  have e2 : t2.gpr .eax = BitVec.ofNat 32 P.K := by rw [u2.gpr]; rfl
  have e3 : t3.gpr .eax = BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 2) := by rw [u3.gpr, e2]
  have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  rw [u4.other _ (by decide), e3, m4, hg.aArg ok 9 (enc_arg (by decide)), hs.arg (enc_arg (by decide))] at u6
  rw [u7.gpr, u6.other _ (by decide), u6.gpr, f5.gpr, u4.gpr, e2]
  exact congrArg some (chk_z (by omega) (by omega) hi.ml32)

/-! ## A message that does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

theorem msgB_length (P : EP) (σ : State) : (msgB P σ).length = P.ml := RsaPkcs1Sig.bytesAt_len _ _ _

/-- `out` zeros and 0, the specification's result. -/
abbrev F1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ ¬ fits h P ∧ s.gpr .esi = P.out ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

abbrev F2 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ ¬ fits h P ∧
    Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = List.replicate P.K 0

theorem fail_vp (P : EP) : VP (fun σ s => C0 h P σ s ∧ isa.eval .ne s = some true) encFail (Fin h g P) := by
  show VP _ (.seq (.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0]) (.seq zeroLoop (.block [mi .eax 0]))) _
  refine VP.seq (G := F1 h P) (VP.taint [.esp] encFailArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
    fun σ s ⟨⟨hc, hi, z⟩, e⟩ => ?_) (VP.seq (G := F2 h P) ?_ ?_)
  · have hf : ¬ fits h P := fun hfits => by
      simp only [eval, z, decide_eq_true hfits] at e
      exact absurd e (by decide)
    have hg := hi.geo
    simp only [ld, mi]
    refine hc.wp_arg hg (enc_arg (j := 0) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t2 c2 u2 => wp_movi fun t3 u3 =>
        WP.block_nil ⟨c2.upd u3 (by decide) (by decide), hi, hf, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u3.other, u2.other, u1.gpr]; rfl
    · simp (disch := decide) only [u3.other, u2.gpr]; rfl
    · rw [u3.gpr]; rfl
  · by_cases hP : ∃ σ, In h.H.D P σ
    swap
    · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
    obtain ⟨σ₀, hi₀⟩ := hP
    have hK := hi₀.k1024
    have hfo := hi₀.ok.fits P.OUT (by simp)
    simp only [BitVec.toNat_setWidth] at hfo
    rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at hfo
    have wb : WBuf (P.lay h.H.D) P.out P.K := ⟨hfo, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩
    refine (zero_vp (scr := P.scr) wb (by have := hi₀.k64; omega)
      (Inv := fun σ _ => In h.H.D P σ ∧ ¬ fits h P) fun _ _ _ hi _ => hi).mono
      (fun σ s ⟨hc, hi, hf, si, cx, ax⟩ => ⟨hc, ⟨hi, hf⟩, si, cx, ax⟩) fun σ s ⟨hc, ⟨hi, hf⟩, hz⟩ => ?_
    refine ⟨hc, hi, hf, ?_⟩
    apply List.ext_getElem (by simp [RsaPkcs1Sig.bytesAt_len])
    intro i h₁ h₂
    rw [RsaPkcs1Sig.bytesAt_len] at h₁
    rw [List.getElem_replicate, ← hz i h₁, ← RsaPkcs1Sig.bytesAt_getD (m := s.mem) (p := P.out.setWidth 64) h₁ 0,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [RsaPkcs1Sig.bytesAt_len]; exact h₁)]; rfl
  · refine VP.taint [.esp] ret0_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp]) fun σ s ⟨hc, hi, hf, hz⟩ => ?_
    simp only [mi]
    refine wp_movi fun t u => WP.block_nil ⟨⟨hi, hc.st.upd u (by decide)⟩, fun _ => ?_⟩
    have en : Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) = none :=
      Proof.RsaOaep.encrypt_none (by rw [nB_length hi, msgB_length, h.glen]; simp only [fits] at hf; omega)
    rw [en, u.gpr, u.mem]
    exact ⟨rfl, hz⟩

end VG.Proof.RsaOaep.X86.Enc
