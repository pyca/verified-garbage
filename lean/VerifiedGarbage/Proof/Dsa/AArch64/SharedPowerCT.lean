module
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedPartsCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedBody
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.SharedCombine
import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
import VerifiedGarbage.Proof.Dsa.AArch64.SharedTable
import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedPartsCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBody
meta import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.Frame
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCombine
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedTable
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # g^x and the mask of g^q = 1: correct, and constant time in x

One run through the body's steps (`power_steps`) gives both: what the body
computes (`power_ok`), and, after each step, what the next step's
constant-time lemma starts from (`power_ct`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The public data: the call's (the secret exponent's pointer and length,
the base's, the workspace, the modulus), the public exponent's pointer and
its bytes, of the secret exponent's length, and a width of whole 64-byte
tiles. -/
structure SPub extends PowerCallPublic where
  qp : Addr
  qb : List Byte
  qlen : qb.length = bytes.len
  wide : 8 ≤ bytes.x.wx
  tiles : bytes.x.wx % 8 = 0

/-- The digits' public data. -/
abbrev SPub.g (p : SPub) : GPub := ⟨p.x, p.bytes.ptr, p.qp, p.qb⟩

/-- The body's steps: after each, what the next step's constant-time lemma
starts from, and then the rest of the run. -/
theorem power_steps (M : Mont) (p : SPub) {s : State}
    (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv)
    (hn : wv s.mem (off p.x.B p.x.o) (slot p.x.wx aN) p.x.wx = p.modulus)
    (hinv : ((word s.mem (off p.x.B p.x.o) (slot p.x.wx aN)).toNat * p.minv.toNat + 1) % 2 ^ 64 = 0)
    {bb xb : List Byte}
    (hb : word s.mem p.x.B (8 * arg) = p.base)
    (hblen : word s.mem p.x.B (8 * argLen) = BitVec.ofNat 64 bb.length) (hbl : bb.length = p.baseLen)
    (hbs : Src s p.x.B p.x.Z p.base bb)
    (he : word s.mem p.x.B (8 * arg2) = p.bytes.ptr)
    (helen : word s.mem p.x.B (8 * arg2Len) = BitVec.ofNat 64 xb.length) (hxl : xb.length = p.bytes.len)
    (hes : Src s p.x.B p.x.Z p.bytes.ptr xb)
    (hq : word s.mem p.x.B Field.q.offset = p.qp) (hqs : Src s p.x.B p.x.Z p.qp p.qb)
    {K : State → Prop} (hK : ∀ t,
      SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
      wv t.mem (off p.x.B p.x.o) (slot p.x.wx aY) p.x.wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE xb) p.modulus ∧
      word t.mem (off p.x.B p.x.o) (8 * Crt.sMaskX) =
        mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE p.qb) p.modulus = 1)) ∧
      ModCtx t (off p.x.B p.x.o) (slot p.x.wx 8) p.x.wx p.minv p.modulus ∧
      Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem ∧ Keep mmRegs s t → K t) :
    WP isa (Arithmetic.constants M.mm) s fun u => PowerCallPrepared p.toPowerCallPublic u ∧
      WP isa (Arithmetic.load aX arg argLen) u fun v => Reduced [aR2, aOne] p.toPowerPublic.product v ∧
      WP isa (Arithmetic.encodePower M.mm) v fun e => XCtx p.x e ∧
      WP isa (seqs tableInit) e fun t₁ => (∃ minv, SubCtx t₁ p.x.B p.x.Z p.x.o p.x.w p.x.wx minv) ∧
      WP isa (.block SharedPower.expInit) t₁ fun t₂ => (0 < p.g.groups ∧ GInv p.g 0 t₂) ∧
      WP isa (digits M.mm) t₂ fun t₃ => CombPre 8 p.x t₃ ∧
      WP isa (combine M.mm 8) t₃ fun t₄ => OrdPre p.x t₄ ∧
      WP isa orderCheck t₄ fun t₅ => CombPre 0 p.x t₅ ∧
      WP isa (combine M.mm 0) t₅ fun t₆ => FGood (off p.x.B p.x.o) p.x.wx t₆ ∧
      WP isa (seqs (Crt.copyArr aY Crt.aT)) t₆ K := by
  obtain ⟨⟨⟨⟨⟨B, Z, o, w, wx⟩, xp, len⟩, minv, m, hw2, hwx, hw30, hm, hodd⟩, base, baseLen, hw48, hb1', hbw',
    he1', he2'⟩, qp, qb, hql', hw8, hd⟩ := p
  dsimp only at hc hn hinv hb hblen hbl hbs he helen hxl hes hq hqs hK hw2 hwx hw30 hw48 hb1' hbw' he1' he2' hql' hw8 hd
  have hb1 : 1 ≤ bb.length := hbl ▸ hb1'
  have hbw : (bb.length + 7) / 8 ≤ wx := hbl ▸ hbw'
  have he1 : 1 ≤ xb.length := hxl ▸ he1'
  have he2 : xb.length ≤ 1024 := hxl ▸ he2'
  have hql : qb.length = xb.length := hql'.trans hxl.symm
  have hw' : wx < 2 ^ 30 := by omega_arith
  have hm0 : 0 < m := by omega_arith
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * wx)
  have hlo := hc.lo
  have hhi := hc.hi
  have hBn := hc.scr.nowrap
  have h384 : 384 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have hqo : Field.q.offset = 264 := rfl
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have field {t : State} (hf : Frm (off B o) (workRanges wx) s.mem t.mem) :
      word t.mem B Field.q.offset = qp :=
    (hf.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega_arith) (by omega_arith)
      (by omega_arith)).trans hq
  -- The constants, the base and its Montgomery form.
  refine WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv) fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_
  refine ⟨⟨⟨hcu, hmu, bb, xb, (work_parent hc hfu (by decide)).trans hb,
    (work_parent hc hfu (by decide)).trans hblen, (work_parent hc hfu (by decide)).trans he,
    (work_parent hc hfu (by decide)).trans helen, hbl, hxl, work_source hc hfu hku hbs,
    work_source hc hfu hku hes⟩, huone, hur2⟩, ?_⟩
  refine WP.mono (VG.Proof.Dsa.AArch64.load_ok hcu hw2 hwx hw30 (by decide) (by decide) (by decide)
    ((work_parent hc hfu (by decide)).trans hb) ((work_parent hc hfu (by decide)).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega_arith) hbw) fun v ⟨hcv, hvbase, hfv, hkv⟩ => ?_
  have hfa : Arrays (off B o) wx [aX] u.mem v.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hfv (Nat.le_refl _) (Nat.le_refl _)
  have hz := hcu.good.scr.nowrap
  have vn := (hfa.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  have vi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by omega_arith)]
    exact hmu.inverse
  have vone := (hfa.wv_of_not_mem (show aOne < 8 by decide) (by decide) hz).trans huone
  have vr2 : wv v.mem (off B o) (slot wx aR2) wx = (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [(hfa.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur2, ← Nat.pow_add,
      show 64 * wx + 64 * wx = 128 * wx by omega_arith]
  refine ⟨⟨⟨hcv.good, vn, vi⟩, fun j hj => ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [vr2]; exact Nat.mod_lt _ hm0
    · dsimp only [PowerPublic.product]
      rw [vone]; exact hm
  refine WP.mono (encodePower_ok M ⟨hcv.good, vn, vi⟩ (Nat.le_refl _) hw2 (by omega_arith) hm hodd hvbase vr2 vone)
    fun e ⟨hme, hex, hey, heone, hfe, hke⟩ => ?_
  have hce := arrays_context hcv hfe (by decide) hke
  have hfE : Frm (off B o) (workRanges wx) s.mem e.mem :=
    (hfu.trans (arrays_work hfa (by decide))).trans (arrays_work hfe (by decide))
  have hkE : Keep mmRegs s e := ((hku.trans hkv).trans hke).mono (by decide)
  have cE : CExpCtx e (off B o) wx minv m (wv e.mem (off B o) (slot wx Crt.aXc) wx) :=
    ⟨hme.good, hce.scrT, hme.modulus, hme.inverse, rfl⟩
  refine ⟨⟨minv, m, _, cE, by rw [hex]; exact Nat.mod_lt _ hm0, hw2, hw'⟩, ?_⟩
  -- The buckets' start.
  refine WP.mono (tableInit_ok (g := Spec.Rsa.os2ip bb)
    (ex := Spec.Rsa.os2ip xb) (eq := Spec.Rsa.os2ip qb) cE hw2 hw'
    (by rw [hey]; exact Nat.mod_lt _ hm0) (by rw [hey, Nat.mod_mod])
    (by rw [hex]; exact Nat.mod_lt _ hm0) (by rw [hex, Nat.mod_mod]; rfl))
    fun t₁ ⟨hD₁, harr₁, hhdr₁, hf₁, hk₁⟩ => ?_
  have hF₁ := hfE.trans hf₁
  have hK₁ : Keep mmRegs s t₁ := (hkE.trans hk₁).mono (by decide)
  have hc₁ : SubCtx t₁ B Z o w wx minv := hc.of_frmT hF₁ (workRanges_ok wx) hK₁.wr (hK₁.gpr .x0 (by decide))
  refine ⟨⟨minv, hc₁⟩, ?_⟩
  -- The exponents.
  refine WP.mono (expInit_ok hc₁ (xp := xp) (qp := qp) (L := xb.length)
    ((work_parent hc hF₁ (by decide)).trans he) ((work_parent hc hF₁ (by decide)).trans helen) (field hF₁))
    fun t₂ ⟨hm₂, hk₂⟩ => ?_
  have o₂ : Outside (off B o) 136 120 t₁.mem t₂.mem := by
    rw [hm₂]
    exact ((fn_outside _ _ _ (by decide) (by decide)).trans (fn_outside _ _ _ (by decide) (by decide))).trans
      (fn_outside _ _ _ (by decide) (by decide))
  have hF₂ := hF₁.trans (fn_work o₂)
  have hK₂ : Keep mmRegs s t₂ := (hK₁.trans hk₂).mono (by decide)
  have hD₂ := hD₁.of_fn o₂ (by
    rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]) hk₂.wr (hk₂.gpr .x0 (by decide))
  have hn₂ := hD₂.ctx.scrT.nowrap
  have hc₂ : SubCtx t₂ B Z o w wx minv := hc.of_frmT hF₂ (workRanges_ok wx) hK₂.wr (hK₂.gpr .x0 (by decide))
  have sx := work_source hc hF₂ hK₂ hes
  have sq := work_source hc hF₂ hK₂ hqs
  have hx : Exps t₂ (off B o) wx xp qp xb qb :=
    ⟨sx.rd, sx.val, src_out hc₂ sx, sq.rd, sq.val, src_out hc₂ sq, hql⟩
  have G0 : GroupsInv t₂ (off B o) wx minv m (Spec.Rsa.os2ip bb) xp qp xb qb 0 0 t₂ :=
    ⟨hD₂, by rw [Nat.pow_zero, Nat.div_one, Nat.mul_zero, Nat.sub_zero, pre_len],
      by rw [Nat.pow_zero, Nat.div_one, Nat.mul_zero, Nat.sub_zero, ← hql, pre_len],
      by rw [hm₂, word_writeW_self, Nat.mul_zero, Nat.sub_zero],
      by rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
      by rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
      fun _ _ _ _ _ _ _ => rfl, Frm.refl _ _ _, Keep.refl _ _⟩
  refine ⟨⟨show 0 < (qb.length + 2) / 3 by omega_arith, t₂, minv, m, Spec.Rsa.os2ip bb, xb, 0, G0, hx, hw8, hw', hd,
    hR, by omega_arith⟩, ?_⟩
  refine WP.mono (digits_ok M hw8 hw' hd hR hx he1 (by omega_arith) G0) fun t₃ ⟨k, hG⟩ => ?_
  have hL0 : xb.length - 3 * ((xb.length + 2) / 3) = 0 := by omega_arith
  have hxk : Spec.Rsa.os2ip xb / 8 ^ k = 0 := by rw [hG.xr, hL0, pre_zero]
  have hqk : Spec.Rsa.os2ip qb / 8 ^ k = 0 := by rw [hG.qr, hL0, pre_zero]
  have hone₃ : wv t₃.mem (off B o) (slot wx aOne) wx = 1 := by
    rw [hG.arr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      fn_arr o₂ hn₂ (by decide), harr₁ _ (by decide)]
    exact heone
  -- `g^q`, and whether it is 1.
  have lt₃ : ∀ d < 8, d ≠ 0 → wv t₃.mem (off B o) (slot wx (8 + (8 + d))) wx < m :=
    fun d hd' _ => hG.dig.lt (8 + d) (by omega_arith)
  refine ⟨⟨minv, m, _, Spec.Rsa.os2ip bb, bexp (Spec.Rsa.os2ip qb) k, hG.dig.ctx, hw2, hw', hR, hm, hG.dig.tab,
    lt₃, fun d hd' hd0 => hG.dig.qs d hd' hd0, hone₃⟩, ?_⟩
  refine WP.mono (combine_ok M (b0 := 8) (b := bexp (Spec.Rsa.os2ip qb) k) (g := Spec.Rsa.os2ip bb)
    hG.dig.ctx hw2 hw' hR hm (Or.inr rfl) hG.dig.tab lt₃
    (fun d hd' hd0 => hG.dig.qs d hd' hd0) hone₃) fun t₄ ⟨hc₄, hT₄, c₄⟩ => ?_
  rw [bexp_sum_all hqk] at hT₄
  refine ⟨⟨minv, m, _, hc₄, hw2, hw'⟩, ?_⟩
  refine WP.mono (orderCheck_ok hc₄ hw2 hw') fun t₅ ⟨hc₅, hmask₅, hent₅, harr₅, hhdr₅, hf₅, hk₅⟩ => ?_
  -- `g^x`.
  have tab₅ := (hhdr₅ _ (by decide) (by decide)).trans
    ((c₄.hdr _ (by decide) (by decide) (by decide)).trans hG.dig.tab)
  have lt₅ : ∀ d < 8, d ≠ 0 → wv t₅.mem (off B o) (slot wx (8 + (0 + d))) wx < m := fun d hd' _ => by
    rw [Nat.zero_add, hent₅ d (by omega_arith), c₄.ent d (by omega_arith)]
    exact hG.dig.lt d (by omega_arith)
  have xs₅ : ∀ d < 8, d ≠ 0 → wv t₅.mem (off B o) (slot wx (8 + (0 + d))) wx % m =
      Spec.Rsa.os2ip bb ^ bexp (Spec.Rsa.os2ip xb) k d * 2 ^ (64 * wx) % m := fun d hd' _ => by
    rw [Nat.zero_add, hent₅ d (by omega_arith), c₄.ent d (by omega_arith)]
    exact hG.dig.xs d hd'
  have one₅ := (harr₅ _ (by decide) (by decide)).trans
    ((c₄.arr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hone₃)
  refine ⟨⟨minv, m, _, Spec.Rsa.os2ip bb, bexp (Spec.Rsa.os2ip xb) k, hc₅, hw2, hw', hR, hm, tab₅, lt₅, xs₅,
    one₅⟩, ?_⟩
  refine WP.mono (combine_ok M (b0 := 0) (b := bexp (Spec.Rsa.os2ip xb) k) (g := Spec.Rsa.os2ip bb)
    hc₅ hw2 hw' hR hm (Or.inl rfl) tab₅ lt₅ xs₅ one₅) fun t₆ ⟨hc₆, hT₆, c₆⟩ => ?_
  rw [bexp_sum_all hxk] at hT₆
  refine ⟨⟨minv, hc₆.good⟩, ?_⟩
  refine WP.mono (copyArr_ok hc₆.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := Crt.aT)
    (by decide) (by decide) (by decide)) fun t ⟨hY, oY, kY⟩ => hK t ?_
  have aY7 : Arrays (off B o) wx [aY] t₆.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) oY (Nat.le_refl _) (by omega_arith)
  have hct := ctx_of_arrays hc₆ aY7 (by decide) (by decide) kY.wr (kY.gpr .x0 (by decide))
  have hF : Frm (off B o) (workRanges wx) s.mem t.mem :=
    hF₂.trans (hG.frm.trans (c₄.frm.trans (hf₅.trans (c₆.frm.trans (arrays_work aY7 (by decide))))))
  have hK' : Keep mmRegs s t :=
    (((((hK₂.trans hG.keep).trans c₄.keep).trans hk₅).trans c₆.keep).trans kY).mono (by decide)
  refine ⟨hc.of_frmT hF (workRanges_ok wx) hK'.wr (hK'.gpr .x0 (by decide)), ?_, ?_,
    ⟨hct.good, hct.n, hct.inv⟩, hF, hK'⟩
  · rw [hY, hT₆, VG.Proof.Dsa.powMod_eq]
    rfl
  · rw [aY7.hslot (by decide), c₆.hdr _ (by decide) (by decide) (by decide), hmask₅, hT₄,
      VG.Proof.Dsa.powMod_eq]
    rfl

/-- `Y := g^x mod m` and the mask of `g^q mod m = 1` into `sMaskX`, in the
workspace of the modulus `m`: for `g` and `x` the call's operands, and `q`
the domain's, of `x`'s length. -/
theorem power_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw8 : 8 ≤ wx) (hw48 : wx ≤ 48) (hd : wx % 8 = 0) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {base xp qp : Addr} {bb xb qb : List Byte}
    (hb : word s.mem B (8 * arg) = base) (hblen : word s.mem B (8 * argLen) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z base bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (he : word s.mem B (8 * arg2) = xp) (helen : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 xb.length)
    (hes : Src s B Z xp xb) (he1 : 1 ≤ xb.length) (he2 : xb.length ≤ 1024)
    (hq : word s.mem B Field.q.offset = qp) (hqs : Src s B Z qp qb) (hql : qb.length = xb.length) :
    WP isa (power M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE xb) m ∧
      word t.mem (off B o) (8 * Crt.sMaskX) =
        mask (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE qb) m = 1)) ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have h := power_steps M
    { bytes := ⟨⟨B, Z, o, w, wx⟩, xp, xb.length⟩, minv := minv, modulus := m, lower := (show 2 ≤ wx by omega_arith),
      fits := hwx,
      upper := hw30, greater := hm, odd := hodd, base := base, baseLen := bb.length, width48 := hw48,
      basePositive := hb1, baseFits := hbw, expPositive := he1, expLimit := he2, qp := qp, qb := qb, qlen := hql,
      wide := hw8, tiles := hd } hc hn hinv hb hblen rfl hbs he helen rfl hes hq hqs fun _ h => h
  rw [power_eq]
  refine wp_seqs_append (by simp) (by simp [tableInit]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono h fun _ h => WP.seq (WP.mono h.2 fun _ h => WP.mono h.2 fun _ h => ?_))
  refine wp_seqs_append (by simp [tableInit]) (by simp) (WP.mono h.2 fun _ h => ?_)
  refine wp_seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  exact WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h =>
    WP.seq (WP.mono h.2 fun _ h => WP.mono h.2 fun _ h => h.2))))

/-! ## Constant time -/

/-- The body's hypotheses: the call's, and the domain's `q`. -/
def SPre (p : SPub) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ word s.mem p.x.B Field.q.offset = p.qp ∧ Src s p.x.B p.x.Z p.qp p.qb

/-- The body leaks the same in runs with the same workspace, pointers,
lengths, modulus and public exponent, whatever the base and the secret
exponent. -/
theorem power_ct (M : Mont) : RelCT isa (Two SPre) (power M.mm) (fun _ _ => True) := by
  rw [power_eq]
  refine RelCT.seqs_append (by simp) (by simp [tableInit]) ?_
  simp only [seqs]
  refine RelCT.seq (RelCT.seq (two_post (two_map (fun p : SPub => p.toPowerPublic.product)
      (fun p s h => ⟨h.1.2.1, p.width48, p.greater, p.odd⟩) (constants_ct M))
    fun p s ⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hq, hqs⟩ =>
      power_steps M p hc hm.modulus hm.inverse hp hl hbl hb hep hel helen he hq hqs (K := fun _ => True)
        fun _ _ => trivial)
    (RelCT.seq (two_post (two_map (fun p : SPub => (⟨p.x, p.base, p.baseLen⟩ : BPub)) (fun p s h => ?_)
        (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
      fun _ _ h => h.2)
    (two_post (two_map (fun p : SPub => p.toPowerPublic.product) (fun _ _ h => h.1) (encodePower_ct M))
      fun _ _ h => h.2))) ?_
  · obtain ⟨⟨⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩, _⟩, _⟩ := h
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega_using [hbw, hw48]
  refine RelCT.seqs_append (by simp [tableInit]) (by simp) (RelCT.seq (two_post
    (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) tableInit_ct) fun _ _ h => h.2) ?_)
  refine RelCT.seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  refine RelCT.seq (R := Two fun (p : SPub) s => FGood (off p.x.B p.x.o) p.x.wx s ∧
      WP isa (seqs (Crt.copyArr aY Crt.aT)) s fun _ => True)
    (RelCT.seq (two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) expInit_ct)
      fun _ _ h => h.2) ?_) ?last
  refine RelCT.seq (two_post (two_map (fun p : SPub => p.g) (fun _ _ h => h.1) (digits_ct M))
    fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) (combine_ct M (Or.inr rfl)))
    fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) orderCheck_ct)
    fun _ _ h => h.2) ?_
  exact two_post (two_map (fun p : SPub => p.x) (fun _ _ h => h.1) (combine_ct M (Or.inl rfl)))
    fun _ _ h => h.2
  case last =>
    exact two_map (fun p : SPub => p.x.ws) (fun _ _ h => h.1.goodW)
      (copyArr_ct (o := aY) (a := Crt.aT) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64.SharedPower
