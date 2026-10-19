module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfCall
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.VfCall
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: after the call

The pieces after the call are proven over the state `τ` the call leaves
(`VQ.reidx`), so that `EM`'s bytes are those of `τ` (`emv`). `acc` (`accW`):
`EM`'s last byte `⊕ 0xbc`, its first if `lo = 1`, and the top bits of
`maskedDB`'s first byte (`acc_vp`); then `DB = maskedDB ⊕ MGF1(H, dbLen)`
with its top bits cleared (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (andByte add_ofNat_sub_one away3_scr away3_slot away3_ctW Away3)

variable (h : PssHash)

/-- A state of a body is one the body may start from. -/
theorem St.ok_self {L : Lay} {σ s : State} (hs : L.St σ s) : L.Ok s :=
  { sp := hs.sp, rd := hs.rd.trans hs.ok.rd, wr := hs.wr.trans hs.ok.wr, B56 := hs.ok.B56, fit := hs.ok.fit,
    F8 := hs.ok.F8, nargs := hs.ok.nargs, A4 := hs.ok.A4, stk := hs.ok.stk, wro := hs.ok.wro, wrw := hs.ok.wrw,
    fits := hs.ok.fits, args := fun _ hj => hs.arg hj }

theorem In.self {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) : In h.D P s :=
  { ok := St.ok_self hs, kv := hi.kv, el1 := hi.el1, elK := hi.elK, glK := hi.glK, scrK := hi.scrK, rlK := hi.rlK,
    slt32 := hi.slt32, scl32 := hi.scl32, nB := (hs.ro (R := P.N) (by simp)).trans hi.nB,
    eB := (hs.ro (R := P.E) (by simp)).trans hi.eB, pw := (hs.ro_words (R := P.PRE) (by simp) rfl).trans hi.pw }

/-- `EM`'s bytes, as the call leaves them. -/
abbrev emv (P : EP) (τ : State) (i : Nat) : Byte := τ.mem (sa P.scr (oEm + i))

/-- `acc`. -/
abbrev accW (P : EP) (τ : State) : BitVec 32 :=
  ((emv P τ (P.K - 1)).setWidth 32 ^^^ 0xbc ||| (emv P τ 0).setWidth 32 &&& (0 - BitVec.ofNat 32 (lo P))) |||
    (emv P τ (lo P)).setWidth 32 &&& (cW ((n0 P).setWidth 32) ^^^ 0xFF)

/-- After the call, over the state `τ` it leaves. -/
abbrev W0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ In h.D P τ ∧ fits h P ∧ Bm h P s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i

theorem w0_self {P : EP} {σ s : State} (hv : V2 h P σ s) : W0 h P s s := by
  obtain ⟨⟨hc, hi, hf, hb⟩, -⟩ := hv
  have hi' := In.self h hi hc.st
  exact ⟨⟨⟨hi'.ok, hc.st.sp, rfl, rfl, Frame.refl _ _⟩, hc.slotS⟩, hi', hf, hb, fun _ _ => rfl⟩

/-- What `acc` keeps. -/
abbrev Ka (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ m.readW ((P.lay h.D).fr sAcc) 32 = accW P τ

theorem acc0_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r4, .r5, .r6, .r7, .r12])
    (.block acc0) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The bounds of the encoding when everything fits. -/
theorem fitB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ eLen P + 1 ≤ dbN h P ∧ lo P + dbN h P + h.D + 1 = P.K ∧ P.K ≤ 1024 ∧ h.D ≤ 64 ∧ 0 < h.D ∧
      64 ≤ P.K := by
  have := hf.2
  have := hi.k1024
  have := hi.k64
  have := h.D_le
  have := h.N_le
  have := h.D_pos
  have : lo P ≤ 1 := by unfold lo; split <;> omega
  refine ⟨this, ?_, ?_, hi.k1024, by omega, h.D_pos, hi.k64⟩ <;> unfold dbN <;> omega

/-- `acc`, to its slot. -/
theorem acc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (W0 h P) (.seq (.block accSet) (.block acc0))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun τ s => W0 h P τ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      s.gpr .r7 = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) ∧ s.gpr .r4 = BitVec.ofNat 32 (lo P) ∧
      s.gpr .r6 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r5 = cW ((n0 P).setWidth 32) ∧ s.gpr .r12 = P.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hi, hf', hb, he⟩ => ?_)
    (VP.taint _ acc0_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hi, hf', hb, he⟩, r0, r7, r4, r6, r5, r12⟩ => ?_)
  · obtain ⟨a1, ra1, va1⟩ := argAt hi hc.st (j := 1) (by decide)
    replace va1 : s.mem.readW ((P.lay h.D).fr (arg 1)) 32 = BitVec.ofNat 32 P.K := va1
    have hw : WP isa (.block accSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r7 = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) ∧
        t.gpr .r4 = BitVec.ofNat 32 (lo P) ∧ t.gpr .r6 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
        t.gpr .r5 = cW ((n0 P).setWidth 32) ∧ t.gpr .r12 = P.B := by
      prun [accSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a1, ra1, va1, arg_lt, hb.1, hb.2.1,
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        add_ofNat_sub_one (x := P.scr) (a := oEm + P.K) (by omega)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t7, t4, t6, t5, t12⟩ =>
      ⟨⟨hc.regs rd wr sp m, hi, hf', m ▸ hb, m ▸ he⟩, t0, t7, t4, t6, t5, t12⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2]
  · have aK : State.addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) = sa P.scr (oEm + (P.K - 1)) := by
      rw [hg.addr (by omega)]; congr 2; omega
    have a0 : State.addr (P.scr + BitVec.ofNat 32 oEm) = sa P.scr (oEm + 0) := hg.addr (by omega)
    have al : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega)
    have rK : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + (P.K - 1))) 1 := hg.rd hc.st (by omega)
    have r0' : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + 0)) 1 := hg.rd hc.st (by omega)
    have rl : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    have hw : WP isa (.block acc0) s fun t => t.mem = s.mem.writeW ((P.lay h.D).fr sAcc) (accW P τ) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [acc0, mw, st, r0, r7, r4, r6, r5, r12, aK, a0, al, rK, r0', rl, he _ (show P.K - 1 < P.K by omega),
        he 0 (by omega), he (lo P) (by omega), slotAt hi (d := sAcc) (by decide),
        hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide), dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR (P.lay h.D) sAcc] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
    obtain ⟨σ', ok⟩ := hg.ok
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨hi, hf', ?_, by rw [m, Mem.readW_writeW_self32]⟩,
      fun i hi' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
    · rw [m]
      exact ⟨by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.1,
        by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.2.1,
        by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.1,
        by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.2⟩
    · rw [← he i hi']
      exact fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hg.slot ok (o := oEm + i) (n := 1) (d := sAcc) (k := 4) (by omega) (by rw [hg.F]; decide)).symm _
          (Region.contains_self _ _)

/-- `H`, as the call leaves it. -/
abbrev seedV (P : EP) (τ : State) : List Byte := (List.range h.D).map fun i => emv P τ (lo P + dbN h P + i)

/-- The mask. -/
abbrev mkV (P : EP) (τ : State) : List Byte := Spec.Mgf1.mgf1 h.G (seedV h P τ) (dbN h P)

/-- `DB`, unmasked, with its top bits cleared. -/
abbrev dbF (P : EP) (τ : State) (i : Nat) : Byte :=
  if i = 0 then (emv P τ (lo P) ^^^ (mkV h P τ).getD 0 0) &&& (cW ((n0 P).setWidth 32)).setWidth 8
  else emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0

/-- After the unmasking. -/
abbrev U0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
    (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- `DB = maskedDB ⊕ MGF1(H, dbLen)`, its top bits cleared. -/
theorem unmask_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i)
      (.seq (.seq (mgfXor h.H) (.block topSet)) (.block topAnd)) (U0 h P) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  have hB := h.B_le
  have mp : MP h (P.lay h.D) P.scr (lo P) (dbN h P) (seedV h P) (Ka h P) := by
    refine ⟨hg, by omega, by omega, fun τ => by simp, fun τ m m' ⟨hi, hf', hb, ha⟩ hf'' => ⟨hi, hf', ?_⟩,
      fun τ m hk => hk.2.2.1.2.1, fun τ m hk => hk.2.2.1.2.2.1⟩
    have away : ∀ r ∈ mgfW h (P.lay h.D) P.scr (lo P) (dbN h P), Away3 (P.lay h.D) r ∧
        (slotR (P.lay h.D) sAny).Disjoint r ∧ (slotR (P.lay h.D) sAcc).Disjoint r := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨away3_ctW h hg (by omega) r hr, ctW_slot h hg (by omega) (by decide) (by decide) r hr,
          ctW_slot h hg (by omega) (by decide) (by decide) r hr⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨away3_scr hg (by omega), hg.slot ok (by omega) (by rw [hg.F]; decide),
            hg.slot ok (by omega) (by rw [hg.F]; decide)⟩
        all_goals exact ⟨away3_slot (by decide) (by decide), slotSep (by decide) (by decide) (by decide),
          slotSep (by decide) (by decide) (by decide)⟩
    refine ⟨⟨slot_keep hf'' (fun r hr => (away r hr).1.1) hb.1, slot_keep hf'' (fun r hr => (away r hr).1.2.1) hb.2.1,
      slot_keep hf'' (fun r hr => (away r hr).1.2.2) hb.2.2.1, slot_keep hf'' (fun r hr => (away r hr).2.1) hb.2.2.2⟩,
      slot_keep hf'' (fun r hr => (away r hr).2.2) ha⟩
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r1 = cW ((n0 P).setWidth 32))
    ((mgf_vp h mp (dbv := fun τ i => emv P τ (lo P + i))).mono (fun τ s ⟨hc, hk, he⟩ => ⟨hc, hk,
      fun i hi => by rw [Nat.add_assoc]; exact he _ (by omega),
      fun i hi => by rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega)]; simp [hi, Nat.add_assoc]⟩)
      (fun _ _ h => h) |>.seq
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hd, hh⟩ => ?_))
    (VP.taint _ Sg.topAnd_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hk, hd, hh⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block topSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = cW ((n0 P).setWidth 32) := by
      prun [topSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.2.2.1.1,
        hk.2.2.1.2.1, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd, m ▸ hh⟩, r0, r1⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega)
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega)
    have hw : WP isa (.block topAnd) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P))
          (s.mem (sa P.scr (oEm + lo P)) &&& (cW ((n0 P).setWidth 32)).setWidth 8) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [topAnd, r0, r1, ad, rd, wd, dpVal, andByte]
    refine WP.mono hw fun t ⟨m, rd', wr', sp'⟩ => ?_
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    have kk : ∀ d, d + 4 ≤ frameBytes → t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
      fun d hd => by
        rw [slot_keep (v := s.mem.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega)
            (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)) rfl]
    have hb' : Bm h P t.mem := ⟨by rw [kk _ (by decide)]; exact hk.2.2.1.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.1,
      by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.2⟩
    have ha' : t.mem.readW ((P.lay h.D).fr sAcc) 32 = accW P τ := by rw [kk _ (by decide)]; exact hk.2.2.2
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', ⟨hk.1, hk.2.1, hb', ha'⟩,
      fun i hi => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega) (by rw [hg.F]; decide)
    · rw [m, sa_write P.scr _ _ (by omega) (by omega)]
      unfold dbF
      by_cases e : i = 0
      · subst e
        rw [ite_eq_left (by omega), ite_eq_left rfl, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega),
          Nat.add_zero]
      · rw [ite_eq_right (by omega), ite_eq_right e, hd i hi]
    · rw [m, sa_write P.scr _ _ (by omega) (by omega), ite_eq_right (by omega), hh i hi]

end VG.Proof.RsaPss.Arm.Vf
