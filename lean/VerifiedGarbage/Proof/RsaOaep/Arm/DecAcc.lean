module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecUnmask
public import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaOaep.Arm.DecUnmask
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP decryption on ARMv7: `EM`'s first byte and `lHash`

`cmpS_vp`: `compareBytes` of two ranges of our part of `scratch` leaves in
`r2` a byte, zero exactly when they are equal. `acc_vp`: the accumulator
`acc` (in its slot) is a byte, zero exactly when `EM`'s first byte is zero
and `lHash' = lHash`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Bignum.Arm (CompareCtx CompareInv compareBody_ok)
open VG.Proof.X25519.Arm (dpVal)

/-- A byte or'ed with the xor of two bytes is a byte. -/
theorem or_xor_lt {x : BitVec 32} (hx : x.toNat < 256) (a b : Byte) :
    (x ||| (a.setWidth 32 ^^^ b.setWidth 32)).toNat < 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have ha : a.toNat % 2 ^ 32 < 2 ^ 8 := by have := a.isLt; omega
  have hb : b.toNat % 2 ^ 32 < 2 ^ 8 := by have := b.isLt; omega
  exact Nat.or_lt_two_pow (n := 8) hx (Nat.xor_lt_two_pow ha hb)

/-- `compareBytes`, with `r2` a byte. -/
theorem cmp_ok (s : State) {a b : BitVec 32} {n : Nat} (ctx : CompareCtx s a b n) (hn : 0 < n)
    (ha : s.gpr .r0 = a) (hb : s.gpr .r1 = b) (hc : s.gpr .lr = BitVec.ofNat 32 n) (hz : s.gpr .r2 = 0) :
    WP isa Impl.Bignum.Arm.compareBytes s fun t => CompareInv s a b n n t ∧ (t.gpr .r2).toNat < 256 := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ CompareInv s a b n i t ∧ (t.gpr .r2).toNat < 256
  unfold Impl.Bignum.Arm.compareBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi, hr⟩ := h
    have ra := ctx.readA i (by omega)
    have rb := ctx.readB i (by omega)
    rw [← hi.rest.rd, ← hi.rest.wr] at ra rb
    refine WP.mono (WP.and (compareBody_ok ctx hi (by omega))
      (VG.Proof.Bignum.Arm.compareByteStep_ok t _ _ (by rw [hi.first]; simp) (by rw [hi.second]; simp) ra rb)) ?_
    rintro u ⟨⟨hu, zero⟩, ⟨-, -, -, acc, -⟩⟩
    have hb' : (u.gpr .r2).toNat < 256 := by rw [acc]; exact or_xor_lt hr _ _
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu, hb'⟩
      change some (!u.z) = some false
      simp only [zero, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu, hb'⟩
      change some (!u.z) = some true
      simp only [zero, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_, by rw [hz]; decide⟩
    exact ⟨by omega, by simpa using ha, by simpa using hb, by simpa using hc,
      by simp [hz], rfl, VG.Proof.X25519.Arm.Rest.refl _ _⟩

variable {L : Lay} {scr : BitVec 32}

/-- `compareBytes` of the `n` bytes at `a` and at `b` in our part of `scratch`. -/
theorem cmpS_vp (hg : Geo L scr) {a b n : Nat} (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa) (hn : 0 < n)
    {X : State → Mem → Prop} {f f' : State → Nat → Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 a ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 b ∧ s.gpr .lr = BitVec.ofNat 32 n ∧ s.gpr .r2 = 0 ∧
        (∀ i < n, s.mem (sa scr (a + i)) = f σ i) ∧ ∀ i < n, s.mem (sa scr (b + i)) = f' σ i)
      Impl.Bignum.Arm.compareBytes
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ (s.gpr .r2).toNat < 256 ∧
        (s.gpr .r2 = 0 ↔ ∀ i < n, f σ i = f' σ i)) := by
  have fa := fitS hg (o := a) (n := n) ha
  have fb := fitS hg (o := b) (n := n) hb
  refine VP.ct VG.Proof.Bignum.Arm.compareBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2.1, h₂.2.2.2.1], by rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]⟩)
    fun σ s ⟨hc, hx, r0, r1, lr, r2, hf, hf'⟩ => ?_
  have ctx : CompareCtx s (scr + BitVec.ofNat 32 a) (scr + BitVec.ofNat 32 b) n :=
    ⟨by unfold oRsa at ha; omega,
      fun i hi => by rw [byte32 fa hi, hg.byteAt_scr (by omega)]; exact hg.rd hc.st (by omega),
      fun i hi => by rw [byte32 fb hi, hg.byteAt_scr (by omega)]; exact hg.rd hc.st (by omega)⟩
  refine WP.mono (cmp_ok s ctx hn r0 r1 lr r2) fun t ⟨inv, bnd⟩ => ?_
  refine ⟨hc.regs inv.rest.rd inv.rest.wr inv.rest.sp inv.mem, by rw [inv.mem]; exact hx, bnd, ?_⟩
  rw [inv.equal]
  refine forall_congr' fun i => imp_congr_right fun hi' => ?_
  rw [byte32 fa hi', byte32 fb hi', hg.byteAt_scr (by omega), hg.byteAt_scr (by omega), hf i hi', hf' i hi']

variable (h g : OHash)

/-- What the checks keep: `X1` and `EM` unmasked. -/
abbrev Y (P : EP) (σ : State) (m : Mem) : Prop := X1 h P σ m ∧ ∀ x < P.K, m (sa P.scr x) = V5 h g P σ x

/-- `EM`'s first byte is zero and `lHash' = lHash`. -/
abbrev hdOk (P : EP) (σ : State) : Prop :=
  V P σ 0 = 0 ∧ ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0

/-- After the checks of `EM`'s first byte and `lHash'`. -/
abbrev A1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ ∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧ a.toNat < 256 ∧
    (a = 0 ↔ hdOk h g P σ)

theorem accPut_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block accPut) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem byte_or_lt {x : BitVec 32} (hx : x.toNat < 256) (b : Byte) : (x ||| b.setWidth 32).toNat < 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_setWidth]
  exact Nat.or_lt_two_pow (n := 8) hx (by have := b.isLt; omega)

theorem setWidth_byte_eq_zero (b : Byte) : b.setWidth 32 = 0 ↔ b = 0 := by
  constructor
  · intro e; have := congrArg (BitVec.setWidth 8) e; simpa using this
  · rintro rfl; rfl

theorem acc_vp (P : EP) :
    VP (U5 h g P)
      (.seq (.block (cmpSet h.H)) (.seq Impl.Bignum.Arm.compareBytes (.seq (.block accSet)
        (.seq (.block accPut) (.block accSave)))))
      (A1 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1, hs.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  -- The comparison's registers.
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 oLh ∧
      s.gpr .lr = BitVec.ofNat 32 h.H.D ∧ s.gpr .r2 = 0 ∧
      (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = V5 h g P σ (1 + h.H.D + i)) ∧
      ∀ i < h.H.D, s.mem (sa P.scr (oLh + i)) = (lhB h P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hx, he⟩ => ?_) ?_
  · have hw : WP isa (.block (cmpSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧
        t.gpr .r1 = P.scr + BitVec.ofNat 32 oLh ∧ t.gpr .lr = BitVec.ofNat 32 h.H.D ∧ t.gpr .r2 = 0 := by
      prun [cmpSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show oLh < 2 ^ 16 by decide),
        movw_val (show h.H.D < 2 ^ 16 by omega)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ => ⟨hc.regs rd wr sp m, m ▸ ⟨hx, he⟩, r0, r1, lr, r2,
      fun i hi => ?_, fun i hi => by rw [m]; exact hx.2.1 i hi⟩
    rw [m, show oEm + 1 + h.H.D + i = 1 + h.H.D + i by oomega]; exact he _ (by omega)
  refine VP.seq (cmpS_vp hg (a := oEm + 1 + h.H.D) (b := oLh) (n := h.H.D) (by oomega) (by oomega) hD0
    (X := Y h g P) (f := fun σ i => V5 h g P σ (1 + h.H.D + i)) (f' := fun σ i => (lhB h P σ).getD i 0)) ?_
  -- `EM`'s first byte.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ (s.gpr .r2).toNat < 256 ∧
      (s.gpr .r2 = 0 ↔ ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s hs => ?_) ?_
  · have hc := hs.1
    have hw : WP isa (.block accSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r2 = s.gpr .r2 := by
      prun [accSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oEm < 2 ^ 16 by decide)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hs.2.1, r2 ▸ hs.2.2.1, r2 ▸ hs.2.2.2⟩, r0⟩
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ (s.gpr .r2).toNat < 256 ∧
      (s.gpr .r2 = 0 ↔ hdOk h g P σ))
    (VP.taint _ accPut_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hy, hb, he⟩, r0⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁.2, h₂.2]
  · have s0 : sa P.scr 0 = State.addr P.scr := by simp [sa]
    have a0 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr := (hg.addr (by oomega)).trans s0
    have rd0 : InRegions (s.rd ++ s.wr) (State.addr P.scr) 1 := s0 ▸ hg.rd hc.st (by oomega)
    have hw : WP isa (.block accPut) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r2 = s.gpr .r2 ||| (s.mem (sa P.scr 0)).setWidth 32 := by
      rw [s0]
      prun [accPut, r0, a0, rd0, dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r2⟩ => ⟨hc.regs rd wr sp m, m ▸ hy, ?_, ?_⟩
    · rw [r2]; exact byte_or_lt hb _
    · rw [r2, or_eq_zero32, he, setWidth_byte_eq_zero, hy.1.2.2]
      exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  -- `acc` to its slot.
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hy, hb, he⟩ => ?_
  have hi := hy.1.1.1
  have hw : WP isa (.block accSave) s fun t => t.mem = s.mem.writeW (P.lay.fr sAcc) (s.gpr .r2) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [accSave, sp0, st, hc.st.sp, slotAt hi (d := sAcc) (by decide),
      hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR P.lay sAcc] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hy.1.1.keep h fr fun r hr => ?_,
    hy.1.2.1.keep h fr fun r hr => ?_, ?_⟩, em_keep fr (fun r hr => ?_) (by omega) hy.2⟩,
    s.gpr .r2, by rw [m, Mem.readW_writeW_self32], hb, he⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
  · rw [← hy.1.2.2]
    have e := em_keep (n := 1) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm) (by decide)
      (f := fun _ => s.mem (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)
    exact e
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

end VG.Proof.RsaOaep.Arm.Dec
