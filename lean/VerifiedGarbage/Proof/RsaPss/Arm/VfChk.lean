module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfBase
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.Params
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.VfBase
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import VerifiedGarbage.Proof.RsaPss.Arm.Params
meta import VerifiedGarbage.Proof.RsaPss.VerifyCases
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the checks

`scratch` to its slot and the arguments of `params` (`chk_vp`); the
encoding's parameters, `[any_salt_len ≠ 0]` and whether everything fits
(`par_vp`): the modulus' first byte not zero, and `lo + hLen + 2 + sLen ≤ k`
for the expected salt length `sLen` (0 if any); if not, 0 (`fail_vp`), as the
specification answers (`verify_false`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo`, the salt length the checks take, and
whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev eLen (P : EP) : Nat := if P.any = 0 then P.slt else 0
abbrev fits (P : EP) : Prop := (n0 P).toNat ≠ 0 ∧ lo P + h.D + 2 + eLen P ≤ P.K

/-- The salt length verification expects. -/
abbrev sLenO (P : EP) : Option Nat := if P.any = 0 then some P.slt else none

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D
abbrev sigB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.sig) P.K

/-- The result. -/
abbrev Res (P : EP) (σ : State) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    r = if Spec.RsaPss.verify h.G h.G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) then 1 else 0

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h P σ (s.gpr .r0)

theorem arg_lt {j : Nat} (hj : j < 13) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega

/-- An argument: its place, readable, and its value. -/
theorem argAt {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat} (hj : j < 13) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = P.argv.getD j 0 := by
  have hl : j < (P.lay D).argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 36; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {D : Nat} {P : EP} {σ : State} (hi : In D P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = (P.lay D).fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 36; unfold frameBytes at hd ⊢; omega)

/-- After `verifyChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .r0 = P.n ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧
    s.gpr .r2 = BitVec.ofNat 32 P.slt ∧ s.gpr .r10 = P.any ∧ s.gpr .r11 = BitVec.ofNat 32 (h.D + 1) ∧
    s.gpr .r12 = P.B

theorem chk_vp (P : EP) : VP (S h P) (.block (verifyChk h.H)) (C0 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  obtain ⟨a9, r9, v9⟩ := argAt hi hs (j := 9) (by decide)
  obtain ⟨a0, r0, v0⟩ := argAt hi hs (j := 0) (by decide)
  obtain ⟨a1, r1, v1⟩ := argAt hi hs (j := 1) (by decide)
  obtain ⟨a7, r7, v7⟩ := argAt hi hs (j := 7) (by decide)
  obtain ⟨a8, r8, v8⟩ := argAt hi hs (j := 8) (by decide)
  have k : ∀ (j : Nat) (v : BitVec 32), j < 13 →
      (s.mem.writeW ((P.lay h.D).fr sS) v).readW ((P.lay h.D).fr (arg j)) 32 = s.mem.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun j v hj => Lay.readW_fr_other _ _ _ (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sS; split <;> omega) (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by decide)
  have hw : WP isa (.block (verifyChk h.H)) s fun t => t.mem = s.mem.writeW ((P.lay h.D).fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.n ∧ t.gpr .r1 = BitVec.ofNat 32 P.K ∧
      t.gpr .r2 = BitVec.ofNat 32 P.slt ∧ t.gpr .r10 = P.any ∧ t.gpr .r11 = BitVec.ofNat 32 (h.D + 1) ∧
      t.gpr .r12 = P.B := by
    prun [verifyChk, sp0, ld, st, mw, hs.sp, a9, r9, v9, a0, r0, v0, a1, r1, v1, a7, r7, v7, a8, r8, v8,
      k 0 _ (by decide), k 1 _ (by decide), k 7 _ (by decide), k 8 _ (by decide),
      slotAt hi (d := sS) (by decide), hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide), arg_lt,
      movw_val (show dig h.H + 1 < 2 ^ 16 by show h.D + 1 < 2 ^ 16; omega)]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, t2, t10, t11, t12⟩ => ⟨⟨?_, ?_⟩, hi, t0, t1, t2, t10, t11, t12⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## The parameters, and whether everything fits -/

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sAny) 32 = (if P.any = 0 then 0 else 1) ∧ s.z = decide (fits h P)

theorem par_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r2, .r10, .r11, .r12])
    (.block (params ++ expLen ++ saltFits)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The modulus' first byte, in a state of the body. -/
theorem n0_at {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) :
    s.mem (State.addr P.n) = n0 P ∧ InRegions (s.rd ++ s.wr) (State.addr P.n) 1 := by
  have hK := hi.k64
  refine ⟨?_, ⟨P.N, by rw [hs.rd, hi.ok.rd]; simp, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩⟩
  have e : Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB
  show s.mem (State.addr P.n) = P.nB.getD 0 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD (by omega), BitVec.add_zero]

theorem par_vp (P : EP) : VP (C0 h P) (.block (params ++ expLen ++ saltFits)) (C1 h P) := by
  refine VP.taint _ par_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, r0, r1, r2, r10, r11, r12⟩ => ?_
  · obtain ⟨-, -, a0, a1, a2, a10, a11, a12⟩ := h₁
    obtain ⟨-, -, b0, b1, b2, b10, b11, b12⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a10, b10]
    · rw [a11, b11]
    · rw [a12, b12]
  have hg := hi.geo
  have hK := hi.k1024
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (params_wp hg hc (K := P.K) (D := h.D) r0 hn r1 r11 r12)
    fun t ⟨m, rd, wr, sp, t8, t9, t2, t10, t12⟩ => ?_)
  rw [nb] at m t8 t9
  have fr1 : Frame [slotR (P.lay h.D) sC, slotR (P.lay h.D) sLo, slotR (P.lay h.D) sDb] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  have hct : Ctx (P.lay h.D) P.scr σ t := hc.write fr1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)) rd wr sp
  refine WP.block_append (WP.mono (expLen_wp hg hct (by rw [t12, r12]))
    fun u ⟨mu, rdu, wru, spu, u2, u8, u9⟩ => ?_)
  refine WP.mono (saltFits_wp u) fun w ⟨mw', rdw, wrw, spw, z⟩ => ?_
  have fr2 : Frame [slotR (P.lay h.D) sAny] t.mem w.mem := by rw [mw', mu]; exact slot_frame _ _ _ _
  refine ⟨hct.write fr2 (fun r hr => ?_) (fun r hr => ?_) (rdw.trans rdu) (wrw.trans wru) (spw.trans spu), hi,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · rw [mw', mu, t10, r10, slot_ww _ _ (by decide) (by decide) (by decide), m,
      slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [mw', mu, t10, r10, slot_ww _ _ (by decide) (by decide) (by decide), m,
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, loW_byte]
  · rw [mw', mu, t10, r10, slot_ww _ _ (by decide) (by decide) (by decide), m, Mem.readW_writeW_self32]
  · rw [mw', mu, t10, r10, Mem.readW_writeW_self32]
  · have e2 : w.z = ((t.gpr .r8 ||| (t.gpr .r9 - BitVec.ofNat 32 (eLen P)) >>> 31 |||
        BitVec.ofNat 32 (eLen P) >>> 31) - 0 == 0) := by
      rw [z, u8, u9, u2, t10, r10, t2, r2]
      unfold eLen
      split <;> rfl
    rw [e2, t8, t9, dbW_byte, setWidth_byte]
    exact fits_z (n0 P).isLt hK hD (by unfold eLen; have := hi.slt32; split <;> omega) (by split <;> omega)

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.Arm.bytesAt_length]

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
    have : lo P ≤ 1 := by unfold lo; split <;> omega
    omega

theorem ret0_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [])
    (.block [mw .r0 0]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem fail_vp (P : EP) : VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (.block [mw .r0 0]) (Fin h P) := by
  refine VP.taint [] ret0_cert (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil)
    fun σ s ⟨⟨hc, hi, _, _, _, _, z⟩, e⟩ => ?_
  have hf : ¬ fits h P := fun hfits => by
    rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hfits] at e
    exact absurd e (by decide)
  have hw : WP isa (.block [mw .r0 0]) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = 0 := by
    prun [mw]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0⟩ => ⟨⟨hi, hc.st.regs rd wr sp m⟩, fun _ => ?_⟩
  rw [t0, verify_false h hi hf]
  rfl

end VG.Proof.RsaPss.Arm.Vf
