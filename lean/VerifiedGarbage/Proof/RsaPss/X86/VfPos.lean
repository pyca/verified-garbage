module

public import VerifiedGarbage.Proof.RsaPss.X86.VfScan
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the scan's result

As on ARMv7 (`Proof/RsaPss/Arm/VfPos.lean`): `scratch` into `ebp` again;
`acc` takes in that `DB`'s first nonzero byte is `0x01` and, if a salt length
is expected, that the salt after it has that length (`acc2`); then the flags
of `any_salt_len = 0` (`pos_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- The index of `DB`'s first nonzero byte, 0 if none. -/
abbrev pzF (P : EP) (τ : State) : Nat := pzJ h P τ (dbN h P)

/-- `acc` after the scan. -/
abbrev acc2 (P : EP) (τ : State) : BitVec 32 :=
  ((accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32))) ||| nfJ h P τ (dbN h P) >>> 31) |||
    ((BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^ BitVec.ofNat 32 P.slt) &&& (anyW P - 1))

/-- What the paths after the scan keep. -/
abbrev K2 (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    (∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
    m.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzF h P τ) ∧
    m.readW ((P.lay h.D).fr sAcc) 32 = acc2 h P τ

theorem anyW_z (P : EP) : (anyW P &&& anyW P == 0) = decide (P.any = 0) := by
  by_cases e : P.any = 0
  · rw [anyW, ite_eq_left e, decide_eq_true e]; rfl
  · rw [anyW, ite_eq_right e, decide_eq_false e]; rfl

/-- `acc` to its slot, and the flags of `any_salt_len = 0`. -/
theorem pos_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s) (.block posChk)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.zf = some (decide (P.any = 0))) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp] posChk_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.sp, h₂.1.sp])
    fun τ s ⟨hs, hx, hf, hp⟩ => ?_
  have hi := hx.1.1
  simp only [posChk, ld, st, Impl.RsaPkcs1Sig.X86.stk]
  refine hs.wp_arg (vf_arg h (j := 9) (by decide)) (by decide) fun t1 s1 u1 => ?_
  have c1 : Ctx (P.lay h.D) P.scr τ t1 := ⟨s1, by rw [u1.gpr]; rfl⟩
  refine c1.wp_slot hg (d := sAcc) (by decide) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine c2.wp_slot hg (d := sVal) (by decide) (by decide) (by decide) fun t3 c3 u3 => ?_
  refine wp_xorI fun t4 u4 => wp_or fun t5 u5 => wp_shr (by decide) fun t6 u6 _ => wp_or fun t7 u7 => ?_
  have c7 : Ctx (P.lay h.D) P.scr τ t7 :=
    (((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7
      (by decide) (by decide)
  refine c7.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t8 c8 u8 => ?_
  refine wp_subm (B := (P.lay h.D).B) (by rw [c8.st.sp])
    (by rw [hg.aFr ok sPos (by decide)]; exact c8.rFr hg sPos (by decide)) fun t9 u9 => ?_
  refine wp_subi fun t10 u10 _ _ => ?_
  have c10 : Ctx (P.lay h.D) P.scr τ t10 := (c8.upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide)
  refine wp_xorm (B := (P.lay h.D).B) (by rw [c10.st.sp]) (by rw [hg.aArg ok 7 (by simp)]; exact
      (by rw [c10.st.rd, c10.st.wr]; exact c10.st.ok.arg_read (vf_arg h (by decide)))) fun t11 u11 => ?_
  have c11 : Ctx (P.lay h.D) P.scr τ t11 := c10.upd u11 (by decide) (by decide)
  refine c11.wp_slot hg (d := sAny) (by decide) (by decide) (by decide) fun t12 c12 u12 => ?_
  refine wp_subi fun t13 u13 _ _ => wp_and fun t14 u14 => wp_or fun t15 u15 => ?_
  have c15 : Ctx (P.lay h.D) P.scr τ t15 :=
    ((c12.upd u13 (by decide) (by decide)).upd u14 (by decide) (by decide)).upd u15 (by decide) (by decide)
  refine c15.wp_st hg (d := sAcc) (by decide) fun t16 c16 m16 => ?_
  refine c16.wp_slot hg (d := sAny) (by decide) (by decide) (by decide) fun t17 c17 u17 => ?_
  refine wp_test fun t18 f18 z18 => WP.block_nil ?_
  -- The memory before the store, and `acc`.
  have m15 : t15.mem = s.mem := by
    rw [u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem,
      u3.mem, u2.mem, u1.mem]
  have va : t15.gpr .eax = acc2 h P τ := by
    have e7 : t7.gpr .eax = (accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32))) |||
        nfJ h P τ (dbN h P) >>> 31 := by
      simp (disch := decide) only [u7.gpr, u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
        u2.gpr, u2.other, u1.other]
      rw [u2.mem, u1.mem, hx.1.2.2.2, hp.val, hp.ebx]
    have e14 : t14.gpr .edx = (BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^
        BitVec.ofNat 32 P.slt) &&& (anyW P - 1) := by
      simp (disch := decide) only [u14.gpr, u13.gpr, u13.other, u12.gpr, u12.other, u11.gpr, u10.gpr, u9.gpr,
        u8.gpr]
      rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem,
        hg.aFr ok sPos (by decide), hp.pos, hx.1.2.2.1.2.2.1, hx.1.2.2.1.2.2.2, hg.aArg ok 7 (by simp),
        hs.arg (vf_arg h (by decide))]
      rfl
    rw [u15.gpr, e14, u14.other .eax (by decide), u13.other .eax (by decide), u12.other .eax (by decide),
      u11.other .eax (by decide), u10.other .eax (by decide), u9.other .eax (by decide), u8.other .eax (by decide),
      e7]
  have mm : t18.mem = s.mem.writeW ((P.lay h.D).fr sAcc) (acc2 h P τ) := by
    rw [f18.mem, u17.mem, m16.mem, m15, va]
  have fr : Frame [slotR (P.lay h.D) sAcc] s.mem t18.mem := by rw [mm]; exact slot_frame _ _ _ _
  have kk : ∀ d, d + 4 ≤ frameBytes → (d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) →
      t18.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 := fun d hd hd' => by
    rw [mm, Lay.readW_fr_other _ _ _ hd' (by unfold frameBytes at hd; omega) (by decide)]
  have kb : ∀ o, o + 1 ≤ oRsa → t18.mem (sa P.scr o) = s.mem (sa P.scr o) := fun o ho =>
    fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := o) (n := 1) (by omega) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  refine ⟨⟨c17.fupd f18, hi, hf, ⟨by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.1,
      by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.2.1, by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.2.2.1,
      by rw [kk _ (by decide) (by decide)]; exact hx.1.2.2.1.2.2.2⟩,
    fun i hi' => by rw [kb _ (by omega)]; exact hx.2.1 i hi',
    fun i hi' => by rw [kb _ (by omega)]; exact hx.2.2 i hi',
    by rw [kk _ (by decide) (by decide)]; exact hp.pos, by rw [mm, Mem.readW_writeW_self32]⟩, ?_⟩
  rw [z18, u17.gpr, m16.mem, m15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
    hx.1.2.2.1.2.2.2, anyW_z]

end VG.Proof.RsaPss.X86.Vf
