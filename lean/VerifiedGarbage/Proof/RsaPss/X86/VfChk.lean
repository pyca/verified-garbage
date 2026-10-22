module

public import VerifiedGarbage.Proof.RsaPss.X86.VfBase
public import VerifiedGarbage.Proof.RsaPss.X86.Params
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the checks

As on ARMv7 (`Proof/RsaPss/Arm/VfChk.lean`): `scratch` into `ebp`,
`[any_salt_len ≠ 0]` to its slot and the expected salt length `sLen`
(`salt_len`, or 0 if any) for `params`, then the encoding's parameters and
whether everything fits (`chk_vp`): the modulus' first byte not zero, and
`lo + hLen + 2 + sLen ≤ k`; if not, 0 (`fail_vp`), as the specification
answers (`verify_false`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo`, the salt length the checks take, and
whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev eLen (P : EP) : Nat := if P.any = 0 then P.slt else 0
abbrev fits (P : EP) : Prop := n0 P ≠ 0 ∧ lo P + h.D + 2 + eLen P ≤ P.K

/-- The salt length verification expects. -/
abbrev sLenO (P : EP) : Option Nat := if P.any = 0 then some P.slt else none

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D
abbrev sigB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.sig.setWidth 64) P.K

/-- The result. -/
abbrev Res (P : EP) (σ : State) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    r = if Spec.RsaPss.verify h.G h.G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) then 1 else 0

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h P σ (s.gpr .eax)

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

/-- `[any_salt_len ≠ 0]`, in its slot. -/
abbrev anyW (P : EP) : BitVec 32 := if P.any = 0 then 0 else 1

/-- After `verifyChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .esi = P.n ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
    s.gpr .edx = BitVec.ofNat 32 (eLen P) ∧ s.mem.readW ((P.lay h.D).fr sAny) 32 = anyW P

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sAny) 32 = anyW P ∧ s.zf = some (decide (fits h P))

theorem any_lt (a : BitVec 32) : decide ((0 : BitVec 32).toNat < a.toNat) = !decide (a = 0) := by
  by_cases e : a = 0
  · subst e; rfl
  · have : a.toNat ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    show decide (0 < a.toNat) = _
    simp only [e, decide_false, Bool.not_false]
    exact decide_eq_true (by omega)

theorem and_mask (x : BitVec 32) (c : Bool) :
    x &&& ((if c then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) = if c then 0 else x := by
  cases c
  · show x &&& (0#32 ^^^ BitVec.allOnes 32) = x
    rw [BitVec.zero_xor, BitVec.and_allOnes]
  · show x &&& (BitVec.allOnes 32 ^^^ BitVec.allOnes 32) = 0
    rw [BitVec.xor_self, BitVec.and_zero]; rfl

theorem mask_and1 (c : Bool) : (if c then BitVec.allOnes 32 else 0) &&& 1 = if c then 1 else 0 := by
  cases c <;> rfl

theorem chk_vp (P : EP) : VP (S h P) (.block (verifyChk ++ params h.H)) (C1 h P) := by
  refine VP.block_append (G := C0 h P) (VP.taint [.esp] verifyChk_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_)
    (VP.taint _ h.certs.params (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, si, cx, dx, sa⟩ => ?_)
  · have hl : ∀ j, j < 13 → j < ((P.lay h.D).argv).length := fun j hj => by simp; omega
    have hg := hi.geo
    simp only [verifyChk, ld, st, mi]
    refine hs.wp_arg (hl 9 (by decide)) (by decide) fun t1 s1 u1 => ?_
    have c1 : Ctx (P.lay h.D) P.scr σ t1 := ⟨s1, by rw [u1.gpr]; rfl⟩
    refine c1.wp_arg hg (hl 7 (by decide)) (by decide) (by decide) fun t2 c2 u2 => ?_
    refine c2.wp_arg hg (hl 8 (by decide)) (by decide) (by decide) fun t3 c3 u3 => ?_
    refine wp_movi fun t4 u4 => wp_cmp fun t5 f5 cf5 _ => wp_sbb_self cf5 fun t6 u6 => ?_
    have c6 := ((c3.upd u4 (by decide) (by decide)).fupd f5).upd u6 (by decide) (by decide)
    refine wp_mov fun t7 u7 => wp_andi fun t8 u8 => ?_
    have c8 := (c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)
    refine c8.wp_st hg (d := sAny) (by decide) fun t9 c9 m9 => ?_
    refine wp_xorI fun t10 u10 => wp_and fun t11 u11 => ?_
    have c11 := (c9.upd u10 (by decide) (by decide)).upd u11 (by decide) (by decide)
    refine c11.wp_arg hg (hl 0 (by decide)) (by decide) (by decide) fun t12 c12 u12 => ?_
    refine c12.wp_arg hg (hl 1 (by decide)) (by decide) (by decide) fun t13 c13 u13 => WP.block_nil ?_
    have e8 : t3.gpr .edi = P.any := by rw [u3.gpr]; rfl
    have e4 : t4.gpr .edi = P.any := by rw [u4.other _ (by decide), e8]
    have e5 : t4.gpr .eax = 0 := by rw [u4.gpr]; rfl
    rw [e5, e4, any_lt] at u6
    refine ⟨c13, hi, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u13.other, u12.gpr]; rfl
    · rw [u13.gpr]; rfl
    · simp (disch := decide) only [u13.other, u12.other, u11.gpr, u10.gpr, u10.other, f5.gpr, u6.gpr,
        u6.other, u7.other, u8.other, m9.gpr, u4.other, u3.other, u2.gpr]
      rw [and_mask]
      by_cases e : P.any = 0
      · rw [ite_eq_right (c := (!decide (P.any = 0)) = true) (fun h' => by
          rw [decide_eq_true e] at h'; exact absurd h' (by decide))]
        show _ = BitVec.ofNat 32 (if P.any = 0 then P.slt else 0)
        rw [ite_eq_left e]; rfl
      · rw [ite_eq_left (c := (!decide (P.any = 0)) = true) (by rw [decide_eq_false e]; rfl)]
        show _ = BitVec.ofNat 32 (if P.any = 0 then P.slt else 0)
        rw [ite_eq_right e]; rfl
    · rw [u13.mem, u12.mem, u11.mem, u10.mem, m9.mem, Mem.readW_writeW_self32]
      simp (disch := decide) only [u8.gpr, u7.gpr, u6.gpr]
      rw [mask_and1]
      by_cases e : P.any = 0
      · rw [ite_eq_right (c := (!decide (P.any = 0)) = true) (fun h' => by
          rw [decide_eq_true e] at h'; exact absurd h' (by decide))]
        show _ = if P.any = 0 then 0 else 1
        rw [ite_eq_left e]
      · rw [ite_eq_left (c := (!decide (P.any = 0)) = true) (by rw [decide_eq_false e]; rfl)]
        show _ = if P.any = 0 then 0 else 1
        rw [ite_eq_right e]
  · obtain ⟨c₁, -, a1, b1, d1, -⟩ := h₁
    obtain ⟨c₂, -, a2, b2, d2, -⟩ := h₂
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
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  rw [← si] at hn nb
  refine WP.mono (params_wp h.H hg hc rfl hn cx dx) fun t ⟨m, rd, wr, sp, bp, z⟩ => ?_
  rw [nb] at m z
  have fr : Frame [slotR (P.lay h.D) sLo, slotR (P.lay h.D) sC, slotR (P.lay h.D) sDb] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (by show _ ≤ frameBytes; decide)⟩
  · rw [m, Lay.readW_fr_other (d := sC) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sLo) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sLo) (e := sC) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, loW_byte]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sAny) (e := sDb) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sAny) (e := sC) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sAny) (e := sLo) _ _ _ (by decide) (by decide) (by decide), sa]
  · rw [z, failW_z hK (show h.H.D ≤ 64 from hD) (by unfold eLen; have := hi.slt32; split <;> omega)]

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

/-- `emLen = k - lo`, for a modulus whose first byte is not zero. -/
theorem emLen_eq {P : EP} {b : Byte} {rest : List Byte} (hbr : P.nB = b :: rest) (hl : rest.length + 1 = P.K)
    (hbt : b.toNat ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = P.K - lo P := by
  have hb0 : b ≠ 0 := fun e => hbt (by rw [e]; rfl)
  have e2 := RsaPss.emLength_eq rest hb0
  have hn0 : n0 P = b := by simp [n0, hbr]
  unfold lo; rw [hn0]
  by_cases hb1 : b.toNat = 1
  · rw [ite_eq_left hb1] at e2; rw [ite_eq_left (by omega)]; all_goals omega
  · rw [ite_eq_right hb1] at e2; rw [ite_eq_right (by have := b.isLt; omega)]; all_goals omega

/-- The specification refuses what does not fit. -/
theorem verify_false {P : EP} {σ : State} (hi : In h.D P σ) (hf : ¬ fits h P) :
    Spec.RsaPss.verify h.G h.G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) = false := by
  have hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hn0 : n0 P = b := by simp [n0, hbr]
  rw [hbr]
  by_cases hb : b.toNat = 0
  · have : b = 0 := BitVec.eq_of_toNat_eq hb
    subst this
    exact RsaPss.verify_zero h.G ..
  · rw [hbr, List.length_cons] at hl
    have hem := emLen_eq hbr hl hb
    refine RsaPss.verify_short h.G _ _ _ ?_
    have gl : h.G.len = h.D := h.glen
    have hs : (sLenO P).getD 0 = eLen P := by unfold sLenO eLen; split <;> rfl
    rw [hem, gl, hs]
    unfold fits at hf
    rw [hn0] at hf
    have hb0 : b ≠ 0 := fun e => hb (by rw [e]; rfl)
    have : lo P ≤ 1 := by unfold lo; split <;> omega
    simp only [ne_eq, hb0, not_false_eq_true, true_and] at hf
    omega

theorem fail_vp (P : EP) : VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (.block [mi .eax 0]) (Fin h P) := by
  refine VP.taint [.esp, .ebp] ret0_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
      · rw [h₁.1.1.ebp, h₂.1.1.ebp]) fun σ s ⟨⟨hc, hi, _, _, _, _, z⟩, e⟩ => ?_
  have hf : ¬ fits h P := fun hfits => by
    simp only [eval, z, decide_eq_true hfits] at e
    exact absurd e (by decide)
  simp only [mi]
  refine wp_movi fun t u => WP.block_nil ⟨⟨hi, hc.st.upd u (by decide)⟩, fun _ => ?_⟩
  rw [u.gpr, verify_false h hi hf]
  rfl

end VG.Proof.RsaPss.X86.Vf
