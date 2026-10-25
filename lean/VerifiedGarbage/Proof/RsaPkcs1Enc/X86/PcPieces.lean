module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcBuild
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcTaint
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Precomputed
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: `EM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcPieces.lean`): `0x00 ‖ 0x02`
(`head_vp`), `PS` copied with the mask of a zero byte (`psLoop_vp`), the
separator and the mask to its slot (`sep_vp`), and `M` (`msgCopy_vp`):
`EM`, in the frame (`G6`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- `PS` with `k` of its bytes left: `EM`'s first `2 + (pl - k)` bytes. -/
def PsI (P : EP) (k : Nat) (σ s : State) : Prop :=
  S P σ s ∧ k ≤ P.pl ∧ s.gpr .edi = P.B + BitVec.ofNat 32 (oEM + (2 + (P.pl - k))) ∧
    s.gpr .esi = P.ps + BitVec.ofNat 32 (P.pl - k) ∧ s.gpr .ecx = BitVec.ofNat 32 k ∧
    s.gpr .ebx = zm (Spec.Rsa.bytesAt σ.mem (P.ps.setWidth 64) (P.pl - k)) ∧ EMok P σ s (2 + (P.pl - k))

/-- The zero mask in its slot. -/
abbrev Zs (P : EP) (σ s : State) : Prop := s.mem.readW (P.lay.fr oZ) 32 = zm (psB P σ)

/-- Before `M`, and whether it is empty. -/
def G5 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .ebx = P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) ∧ s.gpr .esi = P.msg ∧
    s.gpr .ecx = BitVec.ofNat 32 P.ml ∧ Zs P σ s ∧ EMok P σ s (3 + P.pl) ∧ s.zf = some (decide (P.ml = 0))

/-- `EM` written. -/
def G6 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ EMok P σ s P.K

theorem off_add (B : BitVec 32) (a b c : Nat) (h : a + b = c) :
    B + BitVec.ofNat 32 a + BitVec.ofNat 32 b = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, h]

theorem sp_agree {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp], s₁.gpr r = s₂.gpr r := fun _ _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).2.sp, (hF _ _ h₂).2.sp]

theorem head_vp : VP (S P) (.block head) (PsI P P.pl) :=
  VP.taint [.esp] head_taint (sp_agree fun _ _ h => h) fun σ s hs => by
    have hk := hs.1.k64
    simp only [head]
    refine wp_mov fun t1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    have s2 : S P σ t2 := ⟨hs.1, (hs.2.upd u1 (by decide)).upd u2 (by decide)⟩
    have di2 : t2.gpr .edi = P.B + BitVec.ofNat 32 oEM := by rw [u2.gpr, u1.gpr, hs.2.sp]
    refine s2.2.wp_arg (j := 8) (r := .esi) (by simp) (by decide) fun t3 st3 u3 => ?_
    refine st3.wp_arg (j := 9) (r := .ecx) (by simp) (by decide) fun t4 st4 u4 => ?_
    refine wp_movi fun t5 u5 => ?_
    have s5 : S P σ t5 := ⟨hs.1, st4.upd u5 (by decide)⟩
    have di5 : t5.gpr .edi = P.B + BitVec.ofNat 32 oEM := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), di2]
    refine wp_st8EM s5 (off := 0) (n := 0) (by omega_arith) (by rw [di5]; exact off_add _ _ _ _ rfl) fun t6 s6 g6 m6 => ?_
    refine wp_movi fun t7 u7 => ?_
    have s7 : S P σ t7 := ⟨hs.1, s6.2.upd u7 (by decide)⟩
    refine wp_st8EM s7 (off := 1) (n := 1) (by omega_arith)
      (by rw [u7.other _ (by decide), g6, di5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]) fun t8 s8 g8 m8 => ?_
    refine wp_addi fun t9 u9 => ?_
    refine wp_movi fun t10 u10 => WP.block_nil ?_
    have st10 := (s8.2.upd u9 (by decide)).upd u10 (by decide)
    refine ⟨⟨hs.1, st10⟩, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u10.other _ (by decide), u9.gpr, g8, u7.other _ (by decide), g6, di5, Nat.sub_self]
      exact off_add _ _ _ _ rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), g8, u7.other _ (by decide), g6,
        u5.other _ (by decide), u4.other _ (by decide), u3.gpr, Nat.sub_self]; simp
    · rw [u10.other _ (by decide), u9.other _ (by decide), g8, u7.other _ (by decide), g6,
        u5.other _ (by decide), u4.gpr]; rfl
    · rw [u10.gpr, Nat.sub_self]; rfl
    · rw [Nat.sub_self]
      have e6 := EMok.store (EMok.zero (P := P) (σ := σ) (s := t5)) (by decide) (m := t6.mem)
        (by rw [m6, show Reg8.al.reg = .eax from rfl, u5.gpr]; rfl)
      have e8 := EMok.store (n := 1) (s := t7) (fun i hi => by rw [u7.mem]; exact e6 i hi) (by decide)
        (m := t8.mem) (by rw [m8, show Reg8.al.reg = .eax from rfl, u7.gpr]; rfl)
      intro i hi
      rw [u10.mem, u9.mem]
      exact e8 i hi

/-- One byte of `PS`, `n + 1` of them left. -/
theorem psBody_vp (n : Nat) : VP (PsI P (n + 1)) (.block psBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → PsI P 0 σ s) ∧ (0 < n → PsI P n σ s) := by
  refine VP.taint [.esi, .edi, .ecx] psBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  obtain ⟨hs, hk, di, si, cx, bx, em⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  have hfp := hs.1.ok.fits P.PS (by simp)
  simp only [BitVec.toNat_setWidth] at hfp
  rw [Nat.mod_eq_of_lt (by have := P.ps.isLt; omega_arith)] at hfp
  have hbyte : s.mem (P.ps.setWidth 64 + BitVec.ofNat 64 (P.pl - (n + 1))) =
      σ.mem (P.ps.setWidth 64 + BitVec.ofNat 64 (P.pl - (n + 1))) := by
    have := congrArg (fun l => l.getD (P.pl - (n + 1)) 0) (hs.2.ro (R := P.PS) (by simp))
    simp only at this
    rwa [Proof.RsaPkcs1Sig.bytesAt_getD (by omega_arith), Proof.RsaPkcs1Sig.bytesAt_getD (by omega_arith)] at this
  simp only [psBody]
  refine wp_movzx8 (a := P.ps.setWidth 64 + BitVec.ofNat 64 (P.pl - (n + 1)))
    (by show s.ea ⟨.esi, 0⟩ = _
        rw [ea_at, si, addr, BitVec.add_zero]; exact addr_eq (by omega_arith))
    ⟨P.PS, hs.2.inRo (by simp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun t1 u1 => ?_
  have s1 : S P σ t1 := ⟨hs.1, hs.2.upd u1 (by decide)⟩
  refine wp_st8EM s1 (off := 0) (n := 2 + (P.pl - (n + 1))) (by omega_arith)
    (by rw [u1.other _ (by decide), di, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_subi fun t3 u3 c3 _ => ?_
  refine wp_sbb_self c3 fun t4 u4 => ?_
  refine wp_or fun t5 u5 => ?_
  refine wp_addi fun t6 u6 => ?_
  refine wp_addi fun t7 u7 => ?_
  refine wp_subi fun t8 u8 _ z8 => WP.block_nil ?_
  have st8 := ((((((s2.2.upd u3 (by decide)).upd u4 (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd
    u7 (by decide)).upd u8 (by decide))
  have cx7 : t7.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other]
    rw [g2, u1.other _ (by decide), cx]
  have inv : PsI P n σ t8 := by
    refine ⟨⟨hs.1, st8⟩, by omega_arith, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u8.other, u7.gpr, u6.other, u5.other, u4.other, u3.other]
      rw [g2, u1.other _ (by decide), di]
      exact off_add _ _ 1 _ (by omega_arith)
    · simp (disch := decide) only [u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other]
      rw [g2, u1.other _ (by decide), si]
      exact off_add _ _ 1 _ (by omega_arith)
    · rw [u8.gpr, cx7]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega_arith)
    · simp (disch := decide) only [u8.other, u7.other, u6.other, u5.gpr, u4.gpr, u3.other, u4.other]
      simp only [g2]
      rw [u1.other _ (by decide), bx, u1.gpr, hbyte,
        show P.pl - n = P.pl - (n + 1) + 1 by omega_arith, bytesAt_succ, zm_snoc]
    · rw [show 2 + (P.pl - n) = 2 + (P.pl - (n + 1)) + 1 by omega_arith]
      have e := EMok.store em (by omega_arith) (m := t2.mem) (by
        rw [m2, show Reg8.al.reg = .eax from rfl, u1.gpr, u1.mem, setWidth_byte, hbyte,
          enc_getD_ps P σ (by omega_arith)])
      intro i hi
      rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
      exact e i hi
  refine ⟨?_, fun h0 => h0 ▸ inv, fun _ => inv⟩
  show eval .ne t8 = _
  rw [cx7, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
    Offset.ofNat_sub_ofNat (d := 1) (by omega_arith)] at z8
  have : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
    by_cases h0 : n = 0
    · subst h0; rfl
    · have : BitVec.ofNat 32 n ≠ 0 := fun e => h0 (by
        have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this; exact this)
      rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h0]
  rw [this] at z8
  simp only [eval, z8]
  by_cases h0 : n = 0 <;> simp [h0] <;> omega_arith

theorem psLoop_vp : VP (PsI P P.pl) psLoop (PsI P 0) := by
  refine (VP.loop (I := fun m => PsI P m) psBody_vp (P.pl - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have := h.1.1.pl8
  rw [show P.pl - 1 + 1 = P.pl by omega_arith]; exact h

theorem sep_wp {σ s : State} (h : PsI P 0 σ s) : WP isa (.block sep) s (G5 P σ) := by
  obtain ⟨hs, -, di, -, -, bx, em⟩ := h
  have hpl := hs.1.em_len
  have hK := hs.1.k1024
  have hml := hs.1.mlK
  rw [Nat.sub_zero] at di bx em
  simp only [sep]
  refine wp_movi fun t1 u1 => ?_
  have s1 : S P σ t1 := ⟨hs.1, hs.2.upd u1 (by decide)⟩
  refine wp_st8EM s1 (off := 0) (n := 2 + P.pl) (by omega_arith)
    (by rw [u1.other _ (by decide), di, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_addi fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.2.upd u3 (by decide)
  refine s3.wp_strFr (d := oZ) (by show oZ + 4 ≤ frameBytes; decide) fun t4 s4 m4 => ?_
  refine wp_mov fun t5 u5 => ?_
  have s5 := s4.upd u5 (by decide)
  refine s5.wp_arg (j := 6) (r := .esi) (by simp) (by decide) fun t6 s6 u6 => ?_
  refine s6.wp_arg (j := 7) (r := .ecx) (by simp) (by decide) fun t7 s7 u7 => ?_
  refine wp_cmpi fun t8 u8 _ z8 => WP.block_nil ?_
  have s8 := s7.fupd u8
  have mm : t8.mem = t3.mem.writeW (P.lay.fr oZ) (t3.gpr .ebx) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, m4.mem]
  have em3 : EMok P σ t3 (3 + P.pl) := by
    have e := EMok.store (em.of_mem u1.mem) (by omega_arith) (m := t2.mem) (by
      rw [m2, show Reg8.al.reg = .eax from rfl, u1.gpr, enc_getD_sep]; rfl)
    intro i hi
    rw [u3.mem]
    exact e i (by omega_arith)
  refine ⟨⟨hs.1, s8⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u8.gpr, u7.other _ (by decide), u6.other _ (by decide), u5.gpr, m4.gpr, u3.gpr, g2,
      u1.other _ (by decide), di]
    exact off_add _ _ 1 _ (by omega_arith)
  · rw [u8.gpr, u7.other _ (by decide), u6.gpr]; rfl
  · rw [u8.gpr, u7.gpr]; rfl
  · rw [Zs, mm, Mem.readW_writeW_self32, u3.other _ (by decide), g2, u1.other _ (by decide), bx]
  · refine EMok.frame em3 (rs := [⟨P.lay.fr oZ, 4⟩]) ?_ fun i hi r hr => ?_
    · rw [mm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM, oZ]; omega_arith) (by simp only [oEM]; omega_arith) (by simp only [oZ]; omega_arith)
  · rw [z8, u7.gpr]
    simp only [EP.argv, List.getD_cons_succ, List.getD_cons_zero]
    have e := ofNat_beq_zero (k := P.ml) (by omega_arith)
    exact congrArg some ((congrArg (· == (0 : BitVec 32)) (BitVec.sub_zero (BitVec.ofNat 32 P.ml))).trans e)

theorem sep_vp : VP (PsI P 0) (.block sep) (G5 P) :=
  VP.taint [.esp, .edi] sep_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.2.sp, h₂.1.2.sp]
      · rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => sep_wp h

theorem copy_wp {σ s : State} (h : G5 P σ s) (h0 : P.ml ≠ 0) :
    WP isa Impl.Bignum.X86.copyBytes s (G6 P σ) := by
  obtain ⟨hs, bx, si, cx, zs, em, -⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  have hfm := hs.1.ok.fits P.MSG (by simp)
  simp only [BitVec.toNat_setWidth] at hfm
  rw [Nat.mod_eq_of_lt (by have := P.msg.isLt; omega_arith)] at hfm
  have hfit := hs.2.ok.fit
  have hF : oEM + (3 + P.pl) + P.ml ≤ P.lay.F := by
    show _ ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith
  have hA : P.lay.F + 20 + P.lay.A = frameBytes + 20 + 56 := rfl
  have hb : P.B.toNat + (frameBytes + 20 + 56) ≤ 2 ^ 32 := by rw [← hA]; omega_arith
  have hoff : oEM + (3 + P.pl) < 2 ^ 32 := by simp only [oEM]; omega_arith
  have hdn : (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))).toNat = P.B.toNat + (oEM + (3 + P.pl)) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
    exact Nat.mod_eq_of_lt (by simp only [oEM, frameBytes] at hb ⊢; omega_arith)
  have hdj : ∀ j ≤ P.ml, Proof.Bignum.X86.byteAddr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) + BitVec.ofNat 32 j) =
      P.lay.fr (oEM + (3 + P.pl) + j) := fun j hj => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hs.2.ok.addrB (by rw [hA]; simp only [oEM, frameBytes]; omega_arith)
  have hdst : Proof.Bignum.X86.byteAddr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) =
      P.lay.fr (oEM + (3 + P.pl)) := by
    have := hdj 0 (Nat.zero_le _); rwa [BitVec.add_zero, Nat.add_zero] at this
  have ctx := Proof.Bignum.X86.copyCtx_of_regions s P.msg (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) (n := P.ml)
    (by omega_arith) hfm (by rw [hdn]; simp only [oEM, frameBytes] at hb ⊢; omega_arith)
    ⟨P.MSG, hs.2.inRo (by simp), Region.contains_self _ _⟩
    (by rw [hdst]; exact hs.2.inFr hF)
    (by rw [hdst]; exact (hs.2.ok.stk_fr (R := P.MSG) (Or.inl (by simp))
      (by show _ ≤ frameBytes + 16; simp only [oEM, frameBytes]; omega_arith)).symm)
  refine WP.mono (Proof.Bignum.X86.copyBytes_ok s ctx (Nat.pos_of_ne_zero h0) si bx cx) fun t ht => ?_
  have fr := ht.frame (by rw [hdn]; simp only [oEM, frameBytes] at hb ⊢; omega_arith)
  rw [hdst] at fr
  have st : P.lay.St σ t := hs.2.frameW hF fr ht.rest.2.1 ht.rest.2.2 (ht.rest.1 .esp (by decide))
  refine ⟨⟨hs.1, st⟩, ?_, fun i hi => ?_⟩
  · rw [Zs, fr.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM, oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by simp only [oEM]; omega_arith))
      (by decide)]
    exact zs
  · rcases (by omega_arith : i < 3 + P.pl ∨ 3 + P.pl ≤ i) with hi' | hi'
    · rw [frame_byte1 fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.fr_sep (by omega_arith) (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith))]
      exact em i hi'
    · obtain ⟨j, rfl⟩ : ∃ j, i = 3 + P.pl + j := ⟨i - (3 + P.pl), by omega_arith⟩
      have hj : j < P.ml := by omega_arith
      rw [show oEM + (3 + P.pl + j) = oEM + (3 + P.pl) + j by omega_arith, ← hdj j (Nat.le_of_lt hj), ht.copied j hj,
        enc_getD_msg P σ hj]
      have := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.MSG) (by simp))
      simp only at this
      rw [Proof.RsaPkcs1Sig.bytesAt_getD hj, Proof.RsaPkcs1Sig.bytesAt_getD hj] at this
      simp only [Proof.Bignum.X86.byteAddr]
      rw [show (P.msg + BitVec.ofNat 32 j).setWidth 64 = P.msg.setWidth 64 + BitVec.ofNat 64 j from
        addr_eq (by omega_arith)]
      exact this

theorem msgCopy_vp : VP (G5 P) msgCopy (G6 P) := by
  refine VP.ite (fun _ _ h => ⟨_, h.2.2.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by
      show _ = _; simp only [eval]; rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2])
    (VP.block_nil fun σ s ⟨h, he⟩ => ?_)
    (VP.taint [.esi, .ebx, .ecx] copy_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1.2.2.1, h₂.1.2.2.1]
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]) fun σ s ⟨h, he⟩ => copy_wp h fun h0 => by
        have := h.2.2.2.2.2.2; simp only [eval] at he; rw [he, h0] at this; simp at this)
  obtain ⟨hs, -, -, -, zs, em, z⟩ := h
  simp only [eval] at he
  rw [he] at z
  have h0 : P.ml = 0 := by simpa using z.symm
  exact ⟨hs, zs, em.mono (by have := hs.1.em_len; omega_arith)⟩

end VG.Proof.RsaPkcs1Enc.X86.Pc
