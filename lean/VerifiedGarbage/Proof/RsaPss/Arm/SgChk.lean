module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgBase
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.Params
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.SgBase
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import VerifiedGarbage.Proof.RsaPss.Arm.Params
meta import VerifiedGarbage.Proof.RsaPss.SignCases
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
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
# RSASSA-PSS signing on ARMv7: the checks

`scratch` to its slot and the arguments of `params` (`chk_vp`); the
encoding's parameters and whether everything fits (`par_vp`): the modulus'
first byte not zero, and `lo + hLen + 2 + sLen ≤ k`; if not, zeros to
`out` and 0 returned (`fail_vp`), the result the specification gives
(`sign_invalid`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo` and whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev fits (P : EP) : Prop := (n0 P).toNat ≠ 0 ∧ lo P + h.D + 2 + P.sl ≤ P.K

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dp) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dq) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qinv) P.pl
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D
abbrev saltB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.salt) P.sl

/-- The result. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (State.addr P.out) P.K r
    (Spec.RsaPss.sign h.G h.G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h P σ s.mem (s.gpr .r0)

/-- The arguments' places are immediates. -/
theorem arg_lt {j : Nat} (hj : j < 21) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega

/-- An argument: its place, readable, and its value. -/
theorem argAt {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat} (hj : j < 21) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = P.argv.getD j 0 := by
  have hl : j < (P.lay D).argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 68; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {D : Nat} {P : EP} {σ : State} (hi : In D P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = (P.lay D).fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 68; unfold frameBytes at hd ⊢; omega)

/-- After `signChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .r0 = P.n ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧
    s.gpr .r2 = BitVec.ofNat 32 P.sl ∧ s.gpr .r11 = BitVec.ofNat 32 (h.D + 1) ∧ s.gpr .r12 = P.B

theorem chk_vp (P : EP) : VP (S h P) (.block (signChk h.H)) (C0 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  have hK := hi.k1024
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  obtain ⟨a19, r19, v19⟩ := argAt hi hs (j := 19) (by decide)
  obtain ⟨a2, r2, v2⟩ := argAt hi hs (j := 2) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hs (j := 3) (by decide)
  obtain ⟨a18, r18, v18⟩ := argAt hi hs (j := 18) (by decide)
  have k : ∀ (j : Nat) (v : BitVec 32), j < 21 → 4 ≤ arg j →
      (s.mem.writeW ((P.lay h.D).fr sS) v).readW ((P.lay h.D).fr (arg j)) 32 = s.mem.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun j v hj hj' => Lay.readW_fr_other _ _ _ (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sS; split <;> omega) (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by decide)
  have hw : WP isa (.block (signChk h.H)) s fun t => t.mem = s.mem.writeW ((P.lay h.D).fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.n ∧ t.gpr .r1 = BitVec.ofNat 32 P.K ∧
      t.gpr .r2 = BitVec.ofNat 32 P.sl ∧ t.gpr .r11 = BitVec.ofNat 32 (h.D + 1) ∧ t.gpr .r12 = P.B := by
    prun [signChk, sp0, ld, st, mw, hs.sp, a19, r19, v19, a2, r2, v2, a3, r3, v3, a18, r18, v18,
      k 2 _ (by decide) (by decide), k 3 _ (by decide) (by decide), k 18 _ (by decide) (by decide),
      slotAt hi (d := sS) (by decide), hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide), arg_lt,
      movw_val (show dig h.H + 1 < 2 ^ 16 by show h.D + 1 < 2 ^ 16; omega)]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, t2, t11, t12⟩ => ⟨⟨?_, ?_⟩, hi, t0, t1, t2, t11, t12⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## The parameters, and whether everything fits -/

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧ s.z = decide (fits h P)

theorem par_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r2, .r11, .r12])
    (.block (params ++ saltFits)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The modulus' first byte, in a state of the body. -/
theorem n0_at {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) :
    s.mem (State.addr P.n) = n0 P ∧ InRegions (s.rd ++ s.wr) (State.addr P.n) 1 := by
  have hK := hi.k64
  refine ⟨?_, ⟨P.N, by rw [hs.rd, hi.ok.rd]; simp, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩⟩
  have e : Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB
  show s.mem (State.addr P.n) = P.nB.getD 0 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD (by omega), BitVec.add_zero]

theorem par_vp (P : EP) : VP (C0 h P) (.block (params ++ saltFits)) (C1 h P) := by
  refine VP.taint _ par_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, r0, r1, r2, r11, r12⟩ => ?_
  · obtain ⟨-, -, a0, a1, a2, a11, a12⟩ := h₁
    obtain ⟨-, -, b0, b1, b2, b11, b12⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a11, b11]
    · rw [a12, b12]
  have hg := hi.geo
  have hK := hi.k1024
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  refine WP.block_append (WP.mono (params_wp hg hc (K := P.K) (D := h.D) r0 hn r1 r11 r12)
    fun t ⟨m, rd, wr, sp, t8, t9, t2, _, _⟩ => ?_)
  refine WP.mono (saltFits_wp t) fun u ⟨mu, rdu, wru, spu, z⟩ => ?_
  rw [nb] at m t8 t9
  have fr : Frame [slotR (P.lay h.D) sC, slotR (P.lay h.D) sLo, slotR (P.lay h.D) sDb] s.mem u.mem := by
    rw [mu, m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) (rdu.trans rd) (wru.trans wr) (spu.trans sp), hi, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [mu, m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [mu, m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, loW_byte]
  · rw [mu, m, Mem.readW_writeW_self32]
  · rw [z, t8, t9, t2, r2, dbW_byte, setWidth_byte]
    exact fits_z (n0 P).isLt hK hD hi.sl32 (by split <;> omega)

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.Arm.bytesAt_length]

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
  by_cases hb : b.toNat = 0
  · have : b = 0 := BitVec.eq_of_toNat_eq hb
    subst this
    exact RsaPss.sign_zero h.G ..
  · have hb0 : b ≠ 0 := fun e => hb (by rw [e]; rfl)
    refine RsaPss.sign_long h.G _ _ _ _ _ _ _ _ ?_
    have e1 := lo_eq hb0 rest
    have e2 := RsaPss.emLength_eq rest hb0
    have gl : h.G.len = h.D := h.glen
    rw [gl, RsaPkcs1Sig.Arm.bytesAt_length]
    rw [hbr, List.length_cons] at hl
    rw [List.length_cons] at e1
    split at e2 <;> split at e1 <;> split at hf <;> omega

/-- `out` zeros and 0, the specification's result. -/
abbrev F1 (P : EP) (σ s : State) : Prop :=
  S h P σ s ∧ ¬ fits h P ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

abbrev F2 (P : EP) (σ s : State) : Prop :=
  S h P σ s ∧ ¬ fits h P ∧ Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K = List.replicate P.K 0

theorem ret0_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [])
    (.block [mw .r0 0]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem fail_vp (P : EP) : VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (signFail) (Fin h P) := by
  show VP _ (.seq (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) (.seq Impl.Bignum.Arm.maskBytes
    (.block [mw .r0 0]))) _
  refine VP.seq (G := F1 h P) (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
    fun σ s ⟨⟨hc, hi, _, _, _, z⟩, e⟩ => ?_) (VP.seq (G := F2 h P) ?_ ?_)
  · have hf : ¬ fits h P := fun hfits => by
      rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hfits] at e
      exact absurd e (by decide)
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
    have hw : WP isa (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) s fun t => t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .lr = BitVec.ofNat 32 P.K ∧
        t.gpr .r2 = 0 := by
      prun [sp0, ld, mw, hc.st.sp, a0, r0, v0, a3, r3, v3, arg_lt]
      exact ⟨rfl, rfl⟩
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, tl, t2⟩ => ⟨⟨hi, hc.st.regs rd wr sp m⟩, hf, t0, tl, t2⟩
  · refine VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
      by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩) fun σ s ⟨hs, hf, r0, lr, r2⟩ => ?_
    have ok := hs.1.ok
    have hfo := ok.fits P.OUT (by simp)
    simp only [Proof.X25519.Arm.addr_toNat] at hfo
    have hK := hs.1.k1024
    refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.K) (by have := hs.1.k64; omega) (by omega)
      hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
    have st : (P.lay h.D).St σ t := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rst.rd rst.wr rst.sp
    refine ⟨⟨hs.1, st⟩, hf, ?_⟩
    rw [hb, r2]
    apply List.ext_getElem (by simp [RsaPkcs1Sig.Arm.bytesAt_length])
    intro i h₁ h₂
    simp
  · refine VP.taint [] ret0_cert (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun σ s ⟨hs, hf, hz⟩ => ?_
    have hw : WP isa (.block [mw .r0 0]) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = 0 := by
      prun [mw]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, t0⟩ => ⟨⟨hs.1, hs.2.regs rd wr sp m⟩, ?_⟩
    rw [Res, sign_invalid h hs.1 hf, t0, m]
    exact ⟨rfl, hz⟩

end VG.Proof.RsaPss.Arm.Sg
