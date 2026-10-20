module
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecShift

import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.Arm.DecSpec
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP decryption on ARMv7: the output

`ok` (`okW`), all ones exactly when the private-key operation succeeded and
every check passed; the buffer's first `k` bytes to `out`, ANDed with `ok`;
`*msg_len := (t - idx - 1) ∧ ok`; and the result `(ok ∧ 1) ∨ ((r = 2) ? 2 :
0)` (`out_vp`): what `decrypt` says (`decOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc sPos)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Masks -/

section
variable {L : Lay} {scr : BitVec 32}

/-- `maskBytes`: the `n` bytes at `p`, whatever they are in the run from `σ`
(`f σ`), ANDed with the low byte of `w σ`. -/
theorem mask_vp {p : BitVec 32} {n : Nat} (hb : WBuf L p n) (hn : 0 < n)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame [⟨State.addr p, n⟩] m m' → Inv σ m')
    {f : State → Nat → Byte} {w : State → BitVec 32} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = p ∧ s.gpr .r2 = w σ ∧ s.gpr .lr = BitVec.ofNat 32 n ∧
        ∀ i < n, s.mem (byteAt p i) = f σ i)
      Impl.Bignum.Arm.maskBytes
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < n, s.mem (byteAt p i) = f σ i &&& (w σ).setWidth 8) := by
  have fit := hb.fit
  refine VP.ct VG.Proof.Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]⟩) fun σ s ⟨hc, hi, r0, r2, lr, hf⟩ => ?_
  have ctx : VG.Proof.Bignum.Arm.MaskCtx s p n :=
    ⟨hb.n32, fun i hi => by rw [byte32 fit hi]; exact (hb.rbuf).inR hc.st hi,
      fun i hi => by rw [byte32 fit hi]; exact hb.inW hc.st hi,
      fun i hi j hj e => byteAt_inj fit hi hj (by rwa [byte32 fit hi, byte32 fit hj] at e)⟩
  refine WP.mono (VG.Proof.Bignum.Arm.maskBytes_ok s ctx hn r0 lr) fun t inv => ?_
  have fr : Frame [⟨State.addr p, n⟩] s.mem t.mem := frame_of_outside fit inv.outside
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) inv.rest.rd inv.rest.wr inv.rest.sp, hI σ _ _ hi fr,
    fun i hi' => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨R, hR, hc'⟩ := hb.w
    refine ⟨R, ?_, fun a ha => hc'.byte ?_⟩
    · rcases List.mem_cons.mp hR with rfl | hR
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hR)
    · simp only [Region.Contains] at ha; omega
  · simp only [List.mem_singleton] at hr; subst hr; exact hb.slot
  · rw [← byte32 fit hi', inv.masked i hi', r2, byte32 fit hi', hf i hi']

end

theorem and_maskOf (b : Byte) (c : Prop) [Decidable c] : b &&& (maskOf c).setWidth 8 = if c then b else 0 := by
  unfold maskOf
  by_cases hc : c
  · rw [ifp hc, ifp hc]; exact BitVec.and_allOnes
  · rw [ifn hc, ifn hc]; exact BitVec.and_zero

theorem pred_top {a : BitVec 32} (ha : a.toNat < 2 ^ 31) : (a - 1) >>> 31 = if a = 0 then 1 else 0 := by
  by_cases h0 : a = 0
  · subst h0; decide
  · rw [ifn h0]
    have : a.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp
    omega

theorem r_top (o : Spec.Rsa.Outcome) : ((rOf o ^^^ 1) - 1) >>> 31 = if rOf o = 1 then 1 else 0 := by
  cases o <;> simp only [rOf] <;> decide

theorem faultV_r (o : Spec.Rsa.Outcome) : faultV (rOf o) = if rOf o = 2 then 2 else 0 := by
  rw [faultV_rOf]; cases o <;> simp [rOf]

theorem maskOf_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : maskOf p = maskOf q := by
  unfold maskOf
  by_cases hp : p
  · rw [ifp hp, ifp (h.mp hp)]
  · rw [ifn hp, ifn fun hq => hp (h.mpr hq)]

theorem okV_eq (o : Spec.Rsa.Outcome) {a : BitVec 32} (ha : a.toNat < 2 ^ 31) :
    0#32 - ((((rOf o ^^^ 1) - 1) >>> 31) &&& ((a - 1) >>> 31)) = maskOf (rOf o = 1 ∧ a = 0) := by
  rw [r_top, pred_top ha]
  unfold maskOf
  by_cases h1 : rOf o = 1 <;> by_cases h2 : a = 0
  · rw [ifp h1, ifp h2, ifp ⟨h1, h2⟩]; decide
  · rw [ifp h1, ifn h2, ifn fun e => h2 e.2]; decide
  · rw [ifn h1, ifp h2, ifn fun e => h1 e.1]; decide
  · rw [ifn h1, ifn h2, ifn fun e => h1 e.1]; decide

variable (h g : OHash)

/-- Every check passed, and the operation succeeded. -/
abbrev okP (P : EP) (σ : State) : Prop := rV P σ = 1 ∧ allOk h g P σ
abbrev okW (P : EP) (σ : State) : BitVec 32 := maskOf (okP h g P σ)

/-- The message's length, or zero. -/
abbrev mlV (P : EP) (σ : State) : Nat := if okP h g P σ then P.K - (2 * h.H.D + 2) - idx h g P σ else 0

/-- What the output keeps: `K0`, `idx` and `ok` in their slots. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  K0 h P σ m ∧ m.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ) ∧
    m.readW (P.lay.fr sOk) 32 = okW h g P σ

theorem Ko.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hk : Ko h g P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, (slotR P.lay sRes).Disjoint r ∧ (slotR P.lay sPos).Disjoint r ∧ (slotR P.lay sOk).Disjoint r) :
    Ko h g P σ m' :=
  ⟨hk.1.keep h hf fun r hr => (ha r hr).1, slot_keep hf (fun r hr => (ha r hr).2.1) hk.2.1,
    slot_keep hf (fun r hr => (ha r hr).2.2) hk.2.2⟩

theorem ko_out {P : EP} {σ : State} (hi : In P σ) :
    ∀ r ∈ [P.OUT], (slotR P.lay sRes).Disjoint r ∧ (slotR P.lay sPos).Disjoint r ∧ (slotR P.lay sOk).Disjoint r :=
  fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨out_slot hi (by decide), out_slot hi (by decide), out_slot hi (by decide)⟩

/-- After `ok`: `out` from the buffer. -/
abbrev O1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧ ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ)

theorem okMask_vp (P : EP) : VP (SF h g P) (.block okMask) (O1 h g P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hx, ⟨a, ha, hab, hae⟩, hp⟩, hb⟩ => ?_
  have hi := hx.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hok : 0#32 - ((((rV P σ ^^^ 1) - 1) >>> 31) &&& ((a - 1) >>> 31)) = okW h g P σ := by
    rw [okV_eq (oc P σ) (by omega)]
    exact maskOf_congr (and_congr_right fun _ => hae)
  have hw : WP isa (.block okMask) s fun t => t.mem = s.mem.writeW (P.lay.fr sOk) (okW h g P σ) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [okMask, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hx.1.2.2.1, ha, sRes_lt, sOk_lt,
      movw_val (show 0 < 2 ^ 16 by decide), dpVal, hok]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR P.lay sOk] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨hx.1.keep h fr fun r hr => ?_,
    slot_keep fr (fun r hr => ?_) hp, by rw [m, Mem.readW_writeW_self32]⟩, sbytes_keep fr (fun r hr => ?_) (by oomega) hb⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

/-- After the copy: `out` holds the buffer's first `k` bytes. -/
abbrev O2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧ ∀ i < P.K, s.mem (byteAt P.out i) = Bp h g P σ (i + aV h g P σ)

theorem outCopy_vp (P : EP) : VP (O1 h g P) (.seq (.block outSet) Impl.Bignum.Arm.copyBytes) (O2 h g P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hK' := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r1 = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧
      ∀ i < P.K, s.mem (byteAt (P.scr + BitVec.ofNat 32 oBuf) i) = Bp h g P σ (i + aV h g P σ))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hb⟩ => ?_) ?_
  · have hi := hk.1.1
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v0 : s.mem.readW (P.lay.fr (arg 0)) 32 = P.out := v0
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block outSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.out ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 oBuf ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [outSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a0, r0, v0, a4, r4, v4, arg_lt,
        movw_val (show oBuf < 2 ^ 16 by decide)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, tl⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, t0, t1, tl, fun i hi' => ?_⟩
    rw [m, hg.byteAt_scr (by oomega)]; exact hb i (by omega)
  have sO : Region.Disjoint (sR P.scr oBuf P.K) P.OUT := by
    have hs := hi₀.slK
    unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
    have hf := ok.fits P.SCR (by simp)
    simp only [Proof.X25519.Arm.addr_toNat] at hf
    have d : P.OUT.Disjoint P.SCR := by
      have := ok.wrw
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at this
      exact this.1.2
    exact (d.sub_right (Offset.sub_base _ (by oomega))).symm
  refine (copy_vp (out_wbuf hi₀) (hg.rbuf (o := oBuf) (n := P.K) (by oomega) (by omega))
    (by rw [hg.addr (by oomega)]; exact sO) (by omega) (Inv := Ko h g P)
    (f := fun σ i => Bp h g P σ (i + aV h g P σ)) fun σ m m' hk hf => hk.keep h g hf (ko_out hk.1.1)).mono
    (fun σ s ⟨⟨hc, hk⟩, r0, r1, lr, hb⟩ => ⟨hc, hk, r0, r1, lr, hb⟩) fun σ s hh => hh

/-- After the mask: `out` holds the message, or zeros. -/
abbrev O3 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    ∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0

theorem outMask_vp (P : EP) : VP (O2 h g P) (.seq (.block outMask) Impl.Bignum.Arm.maskBytes) (O3 h g P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r2 = okW h g P σ ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧
      ∀ i < P.K, s.mem (byteAt P.out i) = Bp h g P σ (i + aV h g P σ))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hb⟩ => ?_) ?_
  · have hi := hk.1.1
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v0 : s.mem.readW (P.lay.fr (arg 0)) 32 = P.out := v0
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block outMask) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.out ∧ t.gpr .r2 = okW h g P σ ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [outMask, sp0, ld, hc.st.sp, hc.aFr hg, hc.rFr hg, a0, r0, v0, a4, r4, v4, arg_lt, hk.2.2, sOk_lt]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t2, tl⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, t0, t2, tl, m ▸ hb⟩
  refine (mask_vp (out_wbuf hi₀) (by omega) (Inv := Ko h g P)
    (fun σ m m' hk hf => hk.keep h g hf (ko_out hk.1.1)) (f := fun σ i => Bp h g P σ (i + aV h g P σ))
    (w := okW h g P)).mono (fun σ s ⟨⟨hc, hk⟩, r0, r2, lr, hb⟩ => ⟨hc, hk, r0, r2, lr, hb⟩)
    fun σ s ⟨hc, hk, hb⟩ => ⟨hc, hk, fun i hi => by rw [hb i hi, and_maskOf]⟩

end VG.Proof.RsaOaep.Arm.Dec
