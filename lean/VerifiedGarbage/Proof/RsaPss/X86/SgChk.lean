module

public import VerifiedGarbage.Proof.RsaPss.X86.SgBase
public import VerifiedGarbage.Proof.RsaPss.X86.Params
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on x86: the checks

`scratch` into `ebp` and the arguments of `params`, then the encoding's
parameters and whether everything fits (`chk_vp`): the modulus' first byte
not zero, and `lo + hLen + 2 + sLen ≤ k`; if not, zeros to `out` and 0
returned (`fail_vp`), the result the specification gives (`sign_invalid`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo` and whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev fits (P : EP) : Prop := n0 P ≠ 0 ∧ lo P + h.D + 2 + P.sl ≤ P.K

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.p.setWidth 64) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.q.setWidth 64) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dp.setWidth 64) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dq.setWidth 64) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.qinv.setWidth 64) P.pl
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D
abbrev saltB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.salt.setWidth 64) P.sl

/-- The result. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (P.out.setWidth 64) P.K r
    (Spec.RsaPss.sign h.G h.G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h P σ s.mem (s.gpr .eax)

/-- The modulus' first byte, in a state of the body. -/
theorem n0_at {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) :
    s.mem (addr P.n 0) = n0 P ∧ InRegions (s.rd ++ s.wr) (addr P.n 0) 1 := by
  have hK := hi.k64
  have a : addr P.n 0 = P.n.setWidth 64 := by simp [addr]
  rw [a]
  refine ⟨?_, ⟨P.N, by rw [hs.rd, hi.ok.rd]; simp, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩⟩
  have e : Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB
  show s.mem (P.n.setWidth 64) = P.nB.getD 0 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD (by omega), BitVec.add_zero]

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧ s.zf = some (decide (fits h P))

/-- After `signChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .esi = P.n ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
    s.gpr .edx = BitVec.ofNat 32 P.sl

theorem chk_vp (P : EP) : VP (S h P) (.block (signChk ++ params h.H)) (C1 h P) := by
  refine VP.block_append (G := C0 h P) (VP.taint [.esp] signChk_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_)
    (VP.taint _ h.certs.params (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, si, cx, dx⟩ => ?_)
  · have hl : ∀ j, j < 21 → j < ((P.lay h.D).argv).length := fun j hj => by simp; omega
    simp only [signChk, ld]
    refine hs.wp_arg (hl 19 (by decide)) (by decide) fun t1 s1 u1 => ?_
    refine s1.wp_arg (hl 2 (by decide)) (by decide) fun t2 s2 u2 => ?_
    refine s2.wp_arg (hl 3 (by decide)) (by decide) fun t3 s3 u3 => ?_
    refine s3.wp_arg (hl 18 (by decide)) (by decide) fun t4 s4 u4 => WP.block_nil ?_
    refine ⟨⟨s4, by simp (disch := decide) only [u4.other, u3.other, u2.other, u1.gpr]; rfl⟩, hi, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr]; rfl
    · simp (disch := decide) only [u4.other, u3.gpr]; rfl
    · rw [u4.gpr]; rfl
  · obtain ⟨c₁, -, a1, b1, d1⟩ := h₁
    obtain ⟨c₂, -, a2, b2, d2⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [c₁.st.sp, c₂.st.sp]
    · rw [c₁.ebp, c₂.ebp]
    · rw [a1, a2]
    · rw [b1, b2]
    · rw [d1, d2]
  have hg := hi.geo
  have hK := hi.k1024
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  rw [← si] at hn nb
  refine WP.mono (params_wp h.H hg hc rfl hn cx dx) fun t ⟨m, rd, wr, sp, bp, z⟩ => ?_
  rw [nb] at m z
  have fr : Frame [slotR (P.lay h.D) sLo, slotR (P.lay h.D) sC, slotR (P.lay h.D) sDb] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, hi, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (by show _ ≤ frameBytes; decide)⟩
  · rw [m, Lay.readW_fr_other (d := sC) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sLo) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sLo) (e := sC) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, loW_byte]
  · rw [m, Mem.readW_writeW_self32]
  · rw [z, failW_z hK (show h.H.D ≤ 64 from hD) hi.sl32]

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

/-- The specification refuses what does not fit. -/
theorem sign_invalid {P : EP} {σ : State} (hi : In h.D P σ) (hf : ¬ fits h P) :
    Spec.RsaPss.sign h.G h.G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ)
      (saltB P σ) = .invalid := by
  have hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hn0 : n0 P = b := by simp [n0, hbr]
  unfold fits lo at hf
  rw [hn0] at hf
  rw [hbr]
  by_cases hb : b = 0
  · subst hb
    exact RsaPss.sign_zero h.G ..
  · refine RsaPss.sign_long h.G _ _ _ _ _ _ _ _ ?_
    have e1 := lo_eq hb rest
    have e2 := RsaPss.emLength_eq rest hb
    have gl : h.G.len = h.D := h.glen
    rw [gl, RsaPkcs1Sig.bytesAt_len]
    rw [hbr, List.length_cons] at hl
    rw [List.length_cons] at e1
    split at e2 <;> split at e1 <;> split at hf <;> simp only [hb, ne_eq, not_false_eq_true, true_and] at hf <;>
      omega

/-- `out` zeros and 0, the specification's result. -/
abbrev F1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ ¬ fits h P ∧ s.gpr .esi = P.out ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

abbrev F2 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ ¬ fits h P ∧ Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = List.replicate P.K 0

theorem fail_vp (P : EP) : VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (signFail) (Fin h P) := by
  show VP _ (.seq (.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0]) (.seq zeroLoop (.block [mi .eax 0]))) _
  refine VP.seq (G := F1 h P) (VP.taint [.esp] failArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
    fun σ s ⟨⟨hc, hi, _, _, _, z⟩, e⟩ => ?_) (VP.seq (G := F2 h P) ?_ ?_)
  · have hf : ¬ fits h P := fun hfits => by
      simp only [eval, z, decide_eq_true hfits] at e
      exact absurd e (by decide)
    have hg := hi.geo
    have hl : ∀ j, j < 21 → j < ((P.lay h.D).argv).length := fun j hj => by simp; omega
    simp only [ld, mi]
    refine hc.wp_arg hg (hl 0 (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_arg hg (hl 3 (by decide)) (by decide) (by decide) fun t2 c2 u2 => wp_movi fun t3 u3 =>
        WP.block_nil ⟨c2.upd u3 (by decide) (by decide), hi, hf, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u3.other, u2.other, u1.gpr]; rfl
    · simp (disch := decide) only [u3.other, u2.gpr]; rfl
    · rw [u3.gpr]; rfl
  · by_cases hP : ∃ σ, In h.D P σ
    swap
    · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
    obtain ⟨σ₀, hi₀⟩ := hP
    have hK := hi₀.k1024
    have hfo := hi₀.ok.fits P.OUT (by simp)
    simp only [BitVec.toNat_setWidth] at hfo
    rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at hfo
    have wb : WBuf (P.lay h.D) P.out P.K := ⟨hfo, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩
    refine (zero_vp (scr := P.scr) wb (by have := hi₀.k64; omega)
      (Inv := fun σ _ => In h.D P σ ∧ ¬ fits h P) fun _ _ _ hi _ => hi).mono
      (fun σ s ⟨hc, hi, hf, si, cx, ax⟩ => ⟨hc, ⟨hi, hf⟩, si, cx, ax⟩) fun σ s ⟨hc, ⟨hi, hf⟩, hz⟩ => ?_
    refine ⟨hc, hi, hf, ?_⟩
    apply List.ext_getElem (by simp [RsaPkcs1Sig.bytesAt_len])
    intro i h₁ h₂
    rw [RsaPkcs1Sig.bytesAt_len] at h₁
    rw [List.getElem_replicate, ← hz i h₁, ← RsaPkcs1Sig.bytesAt_getD (m := s.mem) (p := P.out.setWidth 64) h₁ 0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [RsaPkcs1Sig.bytesAt_len]; exact h₁)]; rfl
  · refine VP.taint [.esp, .ebp] ret0_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.st.sp, h₂.1.st.sp]
      · rw [h₁.1.ebp, h₂.1.ebp]) fun σ s ⟨hc, hi, hf, hz⟩ => ?_
    simp only [mi]
    refine wp_movi fun t u => WP.block_nil ⟨⟨hi, hc.st.upd u (by decide)⟩, ?_⟩
    rw [Res, sign_invalid h hi hf, u.gpr, u.mem]
    exact ⟨rfl, hz⟩

end VG.Proof.RsaPss.X86.Sg
