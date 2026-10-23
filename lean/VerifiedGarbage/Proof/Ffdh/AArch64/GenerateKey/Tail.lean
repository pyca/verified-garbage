module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Range
import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Stages
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Stages
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_ffdh_generate_key` on AArch64: the public value

With the scalar in range: `R² mod p`, the bound's scan again for the
scalar's significant octets, `y = g^x mod p` and its range flag (`T1` …
`T6`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- With the scalar in range, in the inner workspace. -/
def T0 (p : GkP) (rb : List Byte) (t : State) : Prop := (∃ mi, In (p.D₁ rb) mi t) ∧ Ok p rb ∧ p.pv = true

theorem g8_t0 {p : GkP} {rb : List Byte} {t : State} (h : G8 p rb t) (he : isa.eval (.zero .x .x9) t = some false) :
    T0 p rb t := by
  have hpv : p.pv = true := by
    rw [g8_eval h] at he
    by_contra hc
    simp [bit, hc] at he
  obtain ⟨⟨mi, hI, -⟩, ho⟩ := h
  exact ⟨⟨mi, hI⟩, ho, hpv⟩

/-- After `R² mod p`. -/
def T1 (p : GkP) (rb : List Byte) (t : State) : Prop := (∃ mi, Md (p.D₁ rb) mi t) ∧ Ok p rb ∧ p.pv = true

theorem t0_t1 (M : Mont) (p : GkP) (rb : List Byte) (t : State) (h : T0 p rb t) :
    WP isa (seqs (r2Steps M.mm)) t fun u => T1 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, ho⟩ := h
  exact WP.mono (hI.r2 M) fun u ⟨⟨hu, _⟩, k⟩ => ⟨⟨⟨mi, hu⟩, ho⟩, k⟩

/-- Back in the outer workspace, with `R² mod p`. -/
def T2 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₁ rb) mi t ∧ R2f (p.D₁ rb) t) ∧ Ok p rb ∧ p.pv = true

theorem t1_t2 (p : GkP) (rb : List Byte) (t : State) (h : T1 p rb t) :
    WP isa (.block [leave]) t fun u => T2 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hM⟩, ho⟩ := h
  exact WP.mono (leave_ok hM.2.1.sub) fun u ⟨⟨h0, hm⟩, k⟩ =>
    ⟨⟨⟨mi, hM.inn.pa hm k h0, hM.r2f.mem hm⟩, ho⟩, k.mono (by decide)⟩

/-- After the bound's scan. -/
def T3 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₁ rb) mi t ∧ R2f (p.D₁ rb) t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - (p.D₁ rb).bl)) ∧
    Ok p rb ∧ p.pv = true

theorem t2_t3 (p : GkP) (rb : List Byte) (t : State) (h : T2 p rb t) :
    WP isa (seqs GenerateKey.bound) t fun u => T3 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR⟩, ho⟩ := h
  refine WP.mono hP.bound fun u ⟨⟨hu, _, hEl, _, f⟩, k⟩ => ⟨⟨⟨mi, hu, hR.hdr hP.1 f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sEp, sEl, sFn] <;> omega), hEl⟩, ho⟩, k⟩

/-- The exponent's pointer into `sEp`. -/
theorem epBlk_ok {t : State} {B xp : Addr} {k bl : Nat} (h0 : t.gpr .x0 = B)
    (hK : word t.mem B (8 * sK) = BitVec.ofNat 64 k) (hL : word t.mem B (8 * sEl) = BitVec.ofNat 64 (k - bl))
    (hX : word t.mem B (8 * sX) = xp) (hbl : bl ≤ k) (hk : k < 2 ^ 32)
    (hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8) (hw : InRegions t.wr (off B (8 * sEp)) 8) :
    WP isa (.block [ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, .add .x .x3 .x2 .x11,
        sth .x3 sEp]) t fun u =>
      (u.mem = t.mem.writeW (off B (8 * sEp)) (xp + BitVec.ofNat 64 bl)) ∧ Keep [.x2, .x3, .x10, .x11] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, hdr_enc (show sK < 32 by decide), hdr_enc (show sEl < 32 by decide), hdr_enc (show sX < 32 by decide),
    hdr_enc (show sEp < 32 by decide), hl sK (by decide), hl sEl (by decide), hl sX (by decide), hw, hK, hL, hX]
  have e : BitVec.ofNat 64 k - BitVec.ofNat 64 (k - bl) = BitVec.ofNat 64 bl := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e]

/-- In the inner workspace, with the scalar's significant octets in `sEp`,
`sEl`. -/
def T4 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D₁ rb) mi t ∧ word t.mem p.B (8 * sEp) = p.xp + BitVec.ofNat 64 (p.D₁ rb).bl ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - (p.D₁ rb).bl)) ∧ Ok p rb ∧ p.pv = true

theorem t3_t4 (p : GkP) (rb : List Byte) (t : State) (h : T3 p rb t) :
    WP isa (.block [ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, .add .x .x3 .x2 .x11,
        sth .x3 sEp, enter]) t fun u => T4 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, hL⟩, ho⟩ := h
  have hb := hP.1
  have hO := hP.outer
  have hs := hP.2.2.2.2.1
  have hbl : (p.D₁ rb).bl < p.k := hb.bl_lt
  have hk2 : p.k ≤ 1024 := hb.k2
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hEl8 : 8 * sEl + 8 ≤ 256 := by decide
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap
  have hEp8 : 8 * sEp + 8 ≤ p.Z := by have : 8 * sEp + 8 ≤ 256 := (by decide); omega
  rw [show [ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, .add .x .x3 .x2 .x11, sth .x3 sEp, enter] =
    [ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, .add .x .x3 .x2 .x11, sth .x3 sEp] ++ [enter]
    from rfl, WP.block_append_iff]
  refine WP.mono (epBlk_ok (k := p.k) (bl := (p.D₁ rb).bl) hO.x0 (hs.get (i := sK) (v := BitVec.ofNat 64 p.k) (by simp))
    hL (hs.get (i := sX) (v := p.xp) (by simp [GkP.D₀])) (by omega) (by omega) (fun i hi => hO.ld hi)
    (hO.scr.st hEp8)) fun u ⟨hm, k⟩ => ?_
  have o := writeW_outside t.mem p.B (d := 8 * sEp) (p.xp + BitVec.ofNat 64 (p.D₁ rb).bl) (by omega)
  have hm' : u.mem = t.mem.writeW (off p.B (8 * sEp)) (p.xp + BitVec.ofNat 64 (p.D₁ rb).bl) := hm
  rw [← hm'] at o
  have f : Frm p.B [(8 * sEp, 8)] t.mem u.mem := Frm.of_outside o (List.mem_singleton.mpr rfl)
  have hP' : Pa (p.D₁ rb) mi u := hP.hdrW f (fun r hr => by rw [List.mem_singleton.mp hr]; decide)
    (fun r hr => by rw [List.mem_singleton.mp hr]; decide) (fun r hr => by rw [List.mem_singleton.mp hr]; decide) k
    ((k.gpr .x0 (by decide)).trans hP.2.2.2.2.2.2)
  have hR' : R2f (p.D₁ rb) u := hR.hdr hb f (fun r hr => by rw [List.mem_singleton.mp hr]; decide)
  have hEp : word u.mem p.B (8 * sEp) = p.xp + BitVec.ofNat 64 (p.D₁ rb).bl := by
    rw [hm']; exact word_writeW_self _ _ _ _
  have hEl : word u.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - (p.D₁ rb).bl) := by
    rw [f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; decide) (by omega)]; exact hL
  refine WP.mono hP'.enterM fun v ⟨⟨hI, hmv⟩, k'⟩ => ⟨⟨⟨mi, hI.md (hR'.mem hmv), by rw [hmv]; exact hEp,
    by rw [hmv]; exact hEl⟩, ho⟩, keep_trans (k.mono (by decide)) k'⟩

/-- `y = g^x mod p`. -/
abbrev GkP.y (p : GkP) (rb : List Byte) : Nat := (p.D₁ rb).G ^ p.X rb % (p.D₁ rb).P

/-- After `y = g^x mod p`, in `aY`. -/
def T5 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aY) (p.D₁ rb).w = p.y rb) ∧ Ok p rb ∧ p.pv = true

/-- The exponent's octets. -/
theorem t4_exp {p : GkP} {rb : List Byte} {mi : BitVec 64} {t : State} (hM : Md (p.D₁ rb) mi t) (ho : Ok p rb) :
    Src t p.B p.Z (p.xp + BitVec.ofNat 64 (p.D₁ rb).bl) ((p.xo rb).drop (p.D₁ rb).bl) ∧
      ((p.xo rb).drop (p.D₁ rb).bl).length = p.k - (p.D₁ rb).bl ∧
      Spec.Rsa.os2ip ((p.xo rb).drop (p.D₁ rb).bl) = p.X rb := by
  have hb := hM.1
  have hx : Src t p.B p.Z p.xp (p.xo rb) := hb.srcs (p.xp, p.xo rb) (by simp)
  have hxl := xo_length p rb hb.bl_lt ho
  exact ⟨hx.drop _, by rw [List.length_drop, hxl], KeyScalar.os2ip_cut_drop _ _ _⟩

theorem t4_pre (p : GkP) (rb : List Byte) (t : State) (h : T4 p rb t) :
    PS0 sG sK sEp sEl ((p.D₁ rb).pw (p.dp + BitVec.ofNat 64 p.k) p.k (p.xp + BitVec.ofNat 64 (p.D₁ rb).bl)
      (p.k - (p.D₁ rb).bl)) t := by
  obtain ⟨⟨mi, hM, hEp, hEl⟩, ho, -⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  obtain ⟨hsrc, hl, -⟩ := t4_exp hM ho
  have hbl : (p.D₁ rb).bl < p.k := hb.bl_lt
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have := hM.ps0 (bp := sG) (bl := sK) (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D₁ rb).dp + BitVec.ofNat 64 (p.D₁ rb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega) (by rw [hb.glen])
    hEp (by rw [hl]; exact hEl) hsrc (by rw [hl]; omega) (by rw [hl]; omega)
  rw [hb.glen, hl] at this
  exact this

theorem t4_t5 (W : Window) (M : Mont) (S : Selector) (p : GkP) (rb : List Byte) (t : State) (h : T4 p rb t) :
    WP isa (seqs (pow W.code S.code M.mm sG sK sEp sEl)) t fun u => T5 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hEp, hEl⟩, ho⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  obtain ⟨hsrc, hl, hv⟩ := t4_exp hM ho.1
  have hbl : (p.D₁ rb).bl < p.k := hb.bl_lt
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D₁ rb).dp + BitVec.ofNat 64 (p.D₁ rb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega) (by rw [hb.glen])
    hEp (by rw [hl]; exact hEl) hsrc (by rw [hl]; omega) (by rw [hl]; omega))
    fun u ⟨hu, hY, _, k⟩ => ⟨⟨⟨mi, hu, by rw [hY, hv]⟩, ho⟩, k⟩

/-- `R² mod p` after a change of other parts of the inner workspace. -/
theorem R2f.frmIn {D : FD} {t u : State} (h : R2f D t) (hb : Base D t) {rs : List (Nat × Nat)}
    (hf : Frm (off D.B (inner D.w)) rs t.mem u.mem)
    (hr : ∀ r ∈ rs, slot D.w aR2 + 8 * D.w ≤ r.1 ∨ r.1 + r.2 ≤ slot D.w aR2) : R2f D u := by
  have hroom := hb.room
  have sR := slot_le (w := D.w) (show aR2 < 8 by decide)
  have e : wv u.mem (off D.B (inner D.w)) (slot D.w aR2) D.w = wv t.mem (off D.B (inner D.w)) (slot D.w aR2) D.w :=
    hf.wv_eq hr (by have := hb.scr.nowrap; unfold tabBytes32 at hroom; omega)
  unfold R2f; rw [e]; exact h

/-- y's flag: `1 < y < p − 1`, as the code compares. -/
abbrev GkP.fl (p : GkP) (rb : List Byte) : Prop := 1 < p.y rb ∧ 2 * (p.y rb / 2) + 1 < (p.D₁ rb).P

/-- After y's range. -/
def T6 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ R2f (p.D₁ rb) t ∧ word t.mem (p.G rb) (8 * sF) = bit (p.fl rb) ∧
    wv t.mem (p.G rb) (slot (p.D₁ rb).w aY) (p.D₁ rb).w = p.y rb) ∧ Ok p rb ∧ p.pv = true

theorem t5_t6 (p : GkP) (rb : List Byte) (t : State) (h : T5 p rb t) :
    WP isa (seqs (range aY)) t fun u => T6 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hY⟩, ho⟩ := h
  have hI := hM.inn
  have hb := hI.1
  have hG := hI.2.1.good.scr.nowrap
  refine WP.mono (hI.range (show aY < 8 by decide) (by decide)) fun u ⟨⟨hu, h9, hF, f⟩, k⟩ => ?_
  have sY := slot_le (w := (p.D₁ rb).w) (show aY < 8 by decide)
  have hY0 := hdr_lt_slot (p.D₁ rb).w aY (show sF < 32 by decide)
  have sT := slot_sep (w := (p.D₁ rb).w) (show aTmp ≠ aY by decide)
  have sR := slot_sep (w := (p.D₁ rb).w) (show aTmp ≠ aR2 by decide)
  have hR0 := hdr_lt_slot (p.D₁ rb).w aR2 (show sF < 32 by decide)
  refine ⟨⟨⟨mi, hu, R2f.frmIn hM.r2f hb f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega), by rw [hF, h9, hY], ?_⟩, ho⟩, k⟩
  rw [f.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)]
  exact hY

/-- The block before `storeBE`, in the inner workspace `G` of the outer one `B`. -/
theorem yBlk_ok {t : State} {G B : Addr} {w k : Nat} {a yp : BitVec 64} (h0 : t.gpr .x0 = G)
    (hW : word t.mem G (8 * sW) = BitVec.ofNat 64 w) (hA : word t.mem G (8 * sArr aY) = a)
    (hL : word t.mem G (8 * Crt.sLink) = B) (hO : word t.mem B (8 * sY) = yp)
    (hK : word t.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hlG : ∀ i < 32, InRegions (t.rd ++ t.wr) (off G (8 * i)) 8)
    (hlB : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8) :
    WP isa (.block [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink, Crt.ldw .x1 .x5 sY, Crt.ldw .x9 .x5 sK,
        .add .x .x1 .x1 .x9, movi .x7 0, .subImm .x .x15 .x7 1]) t fun u =>
      (u.gpr .x8 = a ∧ u.gpr .x1 = yp + BitVec.ofNat 64 k ∧ u.gpr .x9 = BitVec.ofNat 64 k ∧ u.gpr .x15 = mask true ∧
        u.mem = t.mem) ∧ Keep [.x1, .x5, .x7, .x8, .x9, .x12, .x15] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [Crt.ldw, h0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aY < 8 by decide)),
    hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show sY < 32 by decide),
    hdr_enc (show sK < 32 by decide), hlG sW (by decide),
    hlG (sArr aY) (sArr_lt (show aY < 8 by decide)), hlG Crt.sLink (by decide),
    hlB sY (by decide), hlB sK (by decide), hW, hA, hL, hO, hK]

/-- `storeBE`'s operands. -/
def T7 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ R2f (p.D₁ rb) t ∧ word t.mem (p.G rb) (8 * sF) = bit (p.fl rb) ∧
    wv t.mem (p.G rb) (slot (p.D₁ rb).w aY) (p.D₁ rb).w = p.y rb) ∧
  t.gpr .x8 = off (p.G rb) (slot (p.D₁ rb).w aY) ∧ t.gpr .x1 = p.yp + BitVec.ofNat 64 p.k ∧
  t.gpr .x9 = BitVec.ofNat 64 p.k ∧ t.gpr .x15 = mask true ∧ Ok p rb ∧ p.pv = true

/-- The block before `storeBE`. -/
abbrev yBlk : List Instr :=
  [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink, Crt.ldw .x1 .x5 sY, Crt.ldw .x9 .x5 sK,
    .add .x .x1 .x1 .x9, movi .x7 0, .subImm .x .x15 .x7 1]

theorem t6_t7 (p : GkP) (rb : List Byte) (t : State) (h : T6 p rb t) :
    WP isa (.block yBlk) t fun u => T7 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hR, hF, hY⟩, ho⟩ := h
  have hc := hI.2.1
  have hs := hI.2.2.2.2.1
  refine WP.mono (yBlk_ok hc.x0 hc.hdr.hw (hc.hdr.harr aY (by decide)) hc.link
    (hs.get (i := sY) (v := p.yp) (by simp [GkP.D₀]))
    (hs.get (i := sK) (v := BitVec.ofNat 64 (p.D₁ rb).k) (by simp)) hI.hlG hI.hlB)
    fun u ⟨⟨h8, h1, h9, h15, hm⟩, k⟩ => ⟨⟨⟨mi, hI.keep hm k (by decide), hR.mem hm, by rw [hm]; exact hF,
      by rw [hm]; exact hY⟩, h8, h1, h9, h15, ho⟩, k.mono (by decide)⟩

/-- y's octets. -/
abbrev GkP.yo (p : GkP) (rb : List Byte) : List Byte := Spec.Rsa.i2osp (p.y rb) p.k

/-- The run's data, with the scalar's and y's octets inputs. -/
abbrev GkP.D₂ (p : GkP) (rb : List Byte) : FD := (p.D₁ rb).withSrcs [(p.xp, p.xo rb), (p.yp, p.yo rb)]

/-- After `storeBE`: y in `y`. -/
def T8 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₂ rb) mi t ∧ R2f (p.D₂ rb) t ∧ word t.mem (p.G rb) (8 * sF) = bit (p.fl rb)) ∧
    Ok p rb ∧ p.pv = true

theorem t7_t8 (p : GkP) (rb : List Byte) (t : State) (h : T7 p rb t) (hd : Dst p t) :
    WP isa storeBE t fun u => T8 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hR, hF, hY⟩, h8, h1, h9, h15, ho, hpv⟩ := h
  obtain ⟨-, ⟨gXY, -, -, gYD, nX, nY, nD, -⟩, -⟩ := id ho
  have hb := hI.1
  have hn := hb.scr.nowrap
  have hroom := hb.room
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have ew' : 8 * (p.D₁ rb).w ≤ p.k + 7 ∧ p.k ≤ 8 * (p.D₁ rb).w := hb.ew
  have hsY := slot_le (w := (p.D₁ rb).w) (show aY < 8 by decide)
  have hiZ : inner (p.D₁ rb).w + slot (p.D₁ rb).w 8 ≤ (p.D₁ rb).Z := by unfold tabBytes32 at hroom; omega
  have h8' : t.gpr .x8 = off (p.D₁ rb).B (inner (p.D₁ rb).w + slot (p.D₁ rb).w aY) := by rw [h8, off_off]
  refine WP.mono (storeBE_ok (c := true) (w := (p.D₁ rb).w) hb.scr h8' h1 h9 h15 (by omega) (by omega)
    rfl (by omega) (fun j hj => (hd j hj).2.1) (fun j hj => (hd j hj).2.2)) fun u ⟨hb', hfr, hwr, hrd, k⟩ => ?_
  have hout : Outside p.B p.Z (2 ^ 64) t.mem u.mem := outside_of_frame (fun j hj => (hd j hj).2.2) hfr
  have hxl := xo_length p rb hb.bl_lt ho
  have hx : Src t p.B p.Z p.xp (p.xo rb) := hb.srcs (p.xp, p.xo rb) (by simp)
  have hF8 := hdr_lt_slot (p.D₁ rb).w 8 (show sF < 32 by decide)
  have hyl : (p.yo rb).length = p.k := by simp [GkP.yo, Spec.Rsa.i2osp]
  have hI' : In (p.D₂ rb) mi u := hI.out hout hrd hwr (k.gpr .x0 (by decide))
    (fun i hi => hfr _ fun j hj => (ne_of_disj gYD nY nD hj (by
      have e : p.dom.length = p.dl := hb.doml
      have hi' : i < p.dom.length := hi
      omega)).symm)
    (ss := [(p.xp, p.xo rb), (p.yp, p.yo rb)]) (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨fun i hi => by rw [hrd, hwr]; exact hx.rd i hi, fun i hi => by
          rw [hfr _ fun j hj => ne_of_disj gXY nX nY (by rw [hxl] at hi; exact hi) hj]; exact hx.val i hi, hx.out⟩
      · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
        · rw [hyl] at hi
          have := (hd i hi).2.1
          rw [← hwr] at this
          obtain ⟨r, hr', hc⟩ := this
          exact ⟨r, List.mem_append_right _ hr', hc⟩
        · rw [hyl] at hi
          have e := congrArg (fun l => l[i]?) hb'
          simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, ite_true] at e
          rw [← wv_off, hY] at e
          rw [List.getElem?_eq_getElem (by rw [hyl]; exact hi)] at e
          exact Option.some.inj e
        · rw [hyl] at hi; exact (hd i hi).2.2)
  refine ⟨⟨⟨mi, hI', R2f.out (D := p.D₁ rb) hR hb hout, ?_⟩, ho, hpv⟩, k.mono (by decide)⟩
  have hout' : Outside (p.D₁ rb).B (p.D₁ rb).Z (2 ^ 64) t.mem u.mem := hout
  rw [GkP.G, word_off, hout'.word (Or.inl (by omega)) (by omega), ← word_off]; exact hF

/-- The inner header's `sF` into `x9`. -/
theorem ldF9_ok {t : State} {G : Addr} {f : BitVec 64} (h0 : t.gpr .x0 = G) (hF : word t.mem G (8 * sF) = f)
    (hl : InRegions (t.rd ++ t.wr) (off G (8 * sF)) 8) :
    WP isa (.block [ldh .x9 sF]) t fun u => (u.gpr .x9 = f ∧ u.mem = t.mem) ∧ Keep [.x9] t u :=
  WP.keep [.x9] (by brun [h0, hdr_enc (show sF < 32 by decide), hl, hF]) (by decide) (by decide) (by decide +kernel)

/-- `x9` into the outer header's `sF`. -/
theorem stF9_ok {t : State} {B : Addr} (h0 : t.gpr .x0 = B) (hw : InRegions t.wr (off B (8 * sF)) 8) :
    WP isa (.block [sth .x9 sF]) t fun u => u.mem = t.mem.writeW (off B (8 * sF)) (t.gpr .x9) ∧ Keep [] t u :=
  WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off B (8 * sF)) (t.gpr .x9))
    (by brun [h0, hdr_enc (show sF < 32 by decide), hw]) rfl rfl rfl

/-- The outer `Pa` after a store to the outer `sF`. -/
theorem _root_.VG.Proof.Ffdh.AArch64.Pa.stF {D : FD} {mi : BitVec 64} {t u : State} (h : Pa D mi t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off D.B (8 * sF)) v) {rs : List Reg} (k : Keep rs t u) (h0 : .x0 ∉ rs) :
    Pa D mi u ∧ Frm D.B [(8 * sF, 8)] t.mem u.mem := by
  have hn := h.1.scr.nowrap
  have hZ := h.1.hZ
  have o := writeW_outside t.mem D.B (d := 8 * sF) v (by have : 8 * sF + 8 ≤ 256 := (by decide); omega)
  rw [← hm] at o
  have f : Frm D.B [(8 * sF, 8)] t.mem u.mem := Frm.of_outside o (List.mem_singleton.mpr rfl)
  exact ⟨h.hdrW f (fun r hr => by rw [List.mem_singleton.mp hr]; decide)
    (fun r hr => by rw [List.mem_singleton.mp hr]; decide) (fun r hr => by rw [List.mem_singleton.mp hr]; decide) k
    ((k.gpr .x0 h0).trans h.2.2.2.2.2.2), f⟩

/-- Back in the outer workspace, with y's flag in its `sF`. -/
def T9 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₂ rb) mi t ∧ R2f (p.D₂ rb) t ∧ word t.mem p.B (8 * sF) = bit (p.fl rb)) ∧ Ok p rb ∧ p.pv = true

theorem t8_t9 (p : GkP) (rb : List Byte) (t : State) (h : T8 p rb t) :
    WP isa (.block [ldh .x9 sF, leave, sth .x9 sF]) t fun u => T9 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hR, hF⟩, ho⟩ := h
  have hb := hI.1
  rw [show [ldh .x9 sF, leave, sth .x9 sF] = [ldh .x9 sF] ++ ([leave] ++ [sth .x9 sF]) from rfl,
    WP.block_append_iff]
  refine WP.mono (ldF9_ok hI.2.1.x0 hF (hI.hlG sF (by decide))) fun t₁ ⟨⟨h9, hm₁⟩, k₁⟩ => ?_
  have hI₁ := hI.keep hm₁ k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (leave_ok hI₁.2.1) fun t₂ ⟨⟨h0₂, hm₂⟩, k₂⟩ => ?_
  have hP₂ : Pa (p.D₂ rb) mi t₂ := hI₁.pa hm₂ k₂ h0₂
  have h9₂ : t₂.gpr .x9 = bit (p.fl rb) := (k₂.gpr .x9 (by decide)).trans h9
  have hn := hb.scr.nowrap
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hF8 : 8 * sF + 8 ≤ 256 := by decide
  refine WP.mono (stF9_ok hP₂.2.2.2.2.2.2 (hP₂.outer.scr.st (show 8 * sF + 8 ≤ p.Z by omega))) fun u ⟨hm, k⟩ => ?_
  obtain ⟨hP', f⟩ := hP₂.stF hm k (by decide)
  refine ⟨⟨⟨mi, hP', R2f.hdr (hR.mem (hm₂.trans hm₁)) hP₂.1 f (fun r hr => by
      rw [List.mem_singleton.mp hr]; decide), by rw [hm, ← h9₂]; exact word_writeW_self _ _ _ _⟩, ho⟩,
    keep_trans (k₁.mono (by decide)) (keep_trans (k₂.mono (by decide)) (k.mono (by decide)))⟩

/-- After the test of the domain's length. -/
def T10 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₂ rb) mi t ∧ R2f (p.D₂ rb) t ∧ word t.mem p.B (8 * sF) = bit (p.fl rb) ∧
    t.gpr .x3 = BitVec.ofNat 64 (p.dl - 2 * p.k)) ∧ Ok p rb ∧ p.pv = true

theorem t9_t10 (p : GkP) (rb : List Byte) (t : State) (h : T9 p rb t) :
    WP isa (.block qTest) t fun u => T10 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, hF⟩, ho⟩ := h
  exact WP.mono hP.qtest fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨⟨mi, hP.keep hm k (by decide), hR.mem hm, by rw [hm]; exact hF, h3⟩,
    ho⟩, k.mono (by decide)⟩

theorem t10_eval {p : GkP} {rb : List Byte} {t : State} (h : T10 p rb t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) := by
  obtain ⟨⟨_, _, _, _, h3⟩, _⟩ := h
  rw [eval_zero, h3]

/-- y's subgroup check, as the code computes it. -/
abbrev GkP.qc (p : GkP) (rb : List Byte) : Prop := p.y rb ^ Spec.Rsa.os2ip (p.D₁ rb).qb % (p.D₁ rb).P = 1

/-- The flag of the key: y's range and, with q, its subgroup. -/
abbrev GkP.F (p : GkP) (rb : List Byte) : Prop := p.fl rb ∧ (p.dl = 3 * p.k → p.qc rb)

/-- The flag in the outer `sF`. -/
def T11 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₂ rb) mi t ∧ word t.mem p.B (8 * sF) = bit (p.F rb)) ∧ Ok p rb ∧ p.pv = true

theorem t10_t11n (p : GkP) (rb : List Byte) (t : State) (h : T10 p rb t)
    (he : isa.eval (.zero .x .x3) t = some true) : WP isa (.block []) t fun u => T11 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, -, hF, h3⟩, ho⟩ := h
  have h2 := hP.1.noq (by rw [eval_zero, h3] at he; simpa using he)
  have hk1 := hP.1.k1
  refine WP.block_nil ⟨⟨⟨mi, hP, ?_⟩, ho⟩, Keep.refl _ _⟩
  rw [hF]
  exact VG.Proof.Ffdh.AArch64.bit_iff ⟨fun h => ⟨h, fun e => absurd (e.symm.trans h2) (by
    simp at hk1 ⊢; omega)⟩, fun h => h.1⟩

/-- After q's scan. -/
def Q1 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₂ rb) mi t ∧ R2f (p.D₂ rb) t ∧ word t.mem p.B (8 * sF) = bit (p.fl rb) ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D₁ rb).qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead (p.D₁ rb).qb)) ∧
    Ok p rb ∧ p.pv = true ∧ p.dl = 3 * p.k

theorem t10_q1 (p : GkP) (rb : List Byte) (t : State) (h : T10 p rb t) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (scan sQ)) t fun u => Q1 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, hF, -⟩, ho⟩ := h
  have hb := hP.1
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap
  refine WP.mono (hP.scan hq) fun u ⟨⟨⟨hP', hEp, hEl⟩, f⟩, k⟩ => ?_
  have f' : Frm p.B [(8 * sEp, 8), (8 * sEl, 8)] t.mem u.mem := f
  refine ⟨⟨⟨mi, hP', hR.hdr hb f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sEp, sEl, sFn] <;> omega), ?_, hEp, hEl⟩, ho.1, ho.2, hq⟩, k⟩
  rw [f'.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sEp, sEl, sF, sFn] <;> omega) (by simp only [sF, sFn]; omega)]
  exact hF

/-- In the inner workspace again. -/
def Q2 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D₂ rb) mi t ∧ word t.mem p.B (8 * sF) = bit (p.fl rb) ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D₁ rb).qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead (p.D₁ rb).qb)) ∧
    Ok p rb ∧ p.pv = true ∧ p.dl = 3 * p.k

theorem q1_q2 (p : GkP) (rb : List Byte) (t : State) (h : Q1 p rb t) :
    WP isa (.block [enter]) t fun u => Q2 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, hF, hEp, hEl⟩, rest⟩ := h
  exact WP.mono hP.enterM fun v ⟨⟨hI, hm⟩, k⟩ => ⟨⟨⟨mi, hI.md (hR.mem hm), by rw [hm]; exact hF, by rw [hm]; exact hEp,
    by rw [hm]; exact hEl⟩, rest⟩, k⟩

theorem yo_facts {p : GkP} {rb : List Byte} {t : State} (hb : Base (p.D₂ rb) t) (hm : (p.D₂ rb).mv = true) :
    (p.yo rb).length = p.k ∧ Spec.Rsa.os2ip (p.yo rb) = p.y rb ∧ Src t p.B p.Z p.yp (p.yo rb) := by
  obtain ⟨-, h1, -⟩ := valid_facts hm hb.k1
  have hP := VG.Proof.Bignum.os2ip_lt ((p.D₂ rb).dom.take (p.D₂ rb).k)
  rw [hb.plen] at hP
  have hy : p.y rb < (p.D₁ rb).P := Nat.mod_lt _ (by have : 1 < (p.D₁ rb).P := h1; omega)
  have hP' : (p.D₁ rb).P < 256 ^ p.k := hP
  refine ⟨by simp [GkP.yo, Spec.Rsa.i2osp], ?_, hb.srcs (p.yp, p.yo rb) (by simp)⟩
  rw [VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt (by omega)]

/-- `y^q mod p` in `aY`. -/
def Q3 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D₂ rb) mi t ∧ word t.mem p.B (8 * sF) = bit (p.fl rb) ∧
    wv t.mem (p.G rb) (slot (p.D₁ rb).w aY) (p.D₁ rb).w = p.y rb ^ Spec.Rsa.os2ip (p.D₁ rb).qb % (p.D₁ rb).P) ∧
    Ok p rb ∧ p.pv = true ∧ p.dl = 3 * p.k

/-- q's octets from its first nonzero one. -/
theorem qe_facts' {D : FD} {t : State} (hb : Base D t) (hq : D.dl = 3 * D.k) :
    (D.qb.drop (lead D.qb)).length = D.k - lead D.qb ∧ 1 ≤ (D.qb.drop (lead D.qb)).length ∧
      (D.qb.drop (lead D.qb)).length ≤ D.k ∧ Spec.Rsa.os2ip (D.qb.drop (lead D.qb)) = Spec.Rsa.os2ip D.qb ∧
      Src t D.B D.Z (off (D.dp + BitVec.ofNat 64 (2 * D.k)) (lead D.qb)) (D.qb.drop (lead D.qb)) := by
  have hl := hb.qlen hq
  have := hb.k1
  have hne : D.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega
  have hlead := lead_lt hne
  refine ⟨by rw [List.length_drop, hl], by rw [List.length_drop]; omega, by rw [List.length_drop]; omega,
    os2ip_drop_lead _, hb.qsrc.drop _⟩

theorem q2_pre (p : GkP) (rb : List Byte) (t : State) (h : Q2 p rb t) :
    PS0 sY sK sEp sEl ((p.D₂ rb).pw p.yp p.k (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D₁ rb).qb))
      (p.k - lead (p.D₁ rb).qb)) t := by
  obtain ⟨⟨mi, hM, -, hEp, hEl⟩, -, -, hq⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  obtain ⟨hyl, -, hy⟩ := yo_facts hb hM.2.2.2.2
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts' hb hq
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have hk2' : (p.D₂ rb).k ≤ 1024 := hb.k2
  have := hM.ps0 (bp := sY) (bl := sK) (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [GkP.D₀])) (by rw [hyl]; exact hs.get (i := sK) (by simp)) hy
    (by rw [hyl]; omega) (by rw [hyl]; simp) hEp (by rw [hl]; exact hEl) hsrc h1 (by omega)
  rw [hyl, hl] at this
  exact this

theorem q2_q3 (W : Window) (M : Mont) (S : Selector) (p : GkP) (rb : List Byte) (t : State) (h : Q2 p rb t) :
    WP isa (seqs (pow W.code S.code M.mm sY sK sEp sEl)) t fun u => Q3 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hF, hEp, hEl⟩, ho, hpv, hq⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  obtain ⟨hyl, hyv, hy⟩ := yo_facts hb hM.2.2.2.2
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts' hb hq
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have hk2' : (p.D₂ rb).k ≤ 1024 := hb.k2
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [GkP.D₀])) (by rw [hyl]; exact hs.get (i := sK) (by simp)) hy
    (by rw [hyl]; omega) (by rw [hyl]; simp) hEp (by rw [hl]; exact hEl) hsrc h1 (by omega))
    fun u ⟨hM', hY, hw, k⟩ => ⟨⟨⟨mi, hM', (hw sF (by decide)).trans hF, by rw [hY, hQ, hyv]⟩, ho, hpv, hq⟩, k⟩

/-- After y's subgroup check. -/
def Q4 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₂ rb) mi t ∧ word t.mem p.B (8 * sF) = bit (p.fl rb) ∧ t.gpr .x9 = bit (p.qc rb)) ∧
    Ok p rb ∧ p.pv = true ∧ p.dl = 3 * p.k

theorem q3_q4 (p : GkP) (rb : List Byte) (t : State) (h : Q3 p rb t) :
    WP isa (seqs (isOne aY)) t fun u => Q4 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hF, hY⟩, rest⟩ := h
  have hI := hM.inn
  have ew := hI.1.ew
  have hk1 : 64 ≤ (p.D₂ rb).k := hI.1.k1
  have hk2 : (p.D₂ rb).k ≤ 1024 := hI.1.k2
  refine WP.mono (eqArr_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D₂ rb).w by omega)
    (show (p.D₂ rb).w < 2 ^ 31 by omega) (show aY < 8 by decide) (show aOne < 8 by decide))
    fun u ⟨h9, hm, k⟩ => ⟨⟨⟨mi, hI.keep hm k (by decide), by rw [hm]; exact hF, ?_⟩, rest⟩, k.mono (by decide)⟩
  rw [h9, hY, hI.2.2.1.one]

/-- The flags and'ed into the outer `sF`. -/
theorem andF_blk {t : State} {B : Addr} {f : BitVec 64} (h0 : t.gpr .x0 = B) (hF : word t.mem B (8 * sF) = f)
    (hl : InRegions (t.rd ++ t.wr) (off B (8 * sF)) 8) (hw : InRegions t.wr (off B (8 * sF)) 8) :
    WP isa (.block [ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]) t fun u =>
      u.mem = t.mem.writeW (off B (8 * sF)) (t.gpr .x9 &&& f) ∧ Keep [.x3, .x9] t u :=
  WP.keep _ (Q := fun u => u.mem = t.mem.writeW (off B (8 * sF)) (t.gpr .x9 &&& f))
    (by brun [h0, hdr_enc (show sF < 32 by decide), hl, hw, hF]) (by decide) (by decide) (by decide +kernel)

theorem q4_t11 (p : GkP) (rb : List Byte) (t : State) (h : Q4 p rb t) :
    WP isa (.block [leave, ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]) t fun u => T11 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hF, h9⟩, ho, hpv, hq⟩ := h
  have hb := hI.1
  have hn := hb.scr.nowrap
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hF8 : 8 * sF + 8 ≤ 256 := by decide
  rw [show [leave, ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF] = [leave] ++
    [ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF] from rfl, WP.block_append_iff]
  refine WP.mono (leave_ok hI.2.1) fun t₁ ⟨⟨h0₁, hm₁⟩, k₁⟩ => ?_
  have hP₁ : Pa (p.D₂ rb) mi t₁ := hI.pa hm₁ k₁ h0₁
  have hO := hP₁.outer
  refine WP.mono (andF_blk (f := bit (p.fl rb)) hO.x0 (by rw [hm₁]; exact hF) (hO.ld (by decide))
    (hO.scr.st (show 8 * sF + 8 ≤ p.Z by omega))) fun u ⟨hm, k⟩ => ?_
  obtain ⟨hP', -⟩ := hP₁.stF hm k (by decide)
  refine ⟨⟨⟨mi, hP', ?_⟩, ho, hpv⟩, keep_trans (k₁.mono (by decide)) (k.mono (by decide))⟩
  have hm' : u.mem = t₁.mem.writeW (off p.B (8 * sF)) (t₁.gpr .x9 &&& bit (p.fl rb)) := hm
  rw [hm', word_writeW_self, (k₁.gpr .x9 (by decide)).trans h9, VG.Proof.Ffdh.AArch64.bit_and]
  exact VG.Proof.Ffdh.AArch64.bit_iff ⟨fun ⟨a, b⟩ => ⟨b, fun _ => a⟩, fun ⟨a, b⟩ => ⟨b hq, a⟩⟩

theorem t10_t11q (W : Window) (M : Mont) (S : Selector) (p : GkP) (rb : List Byte) (t : State) (h : T10 p rb t)
    (he : isa.eval (.zero .x .x3) t = some false) :
    WP isa (seqs (scan sQ ++ ([.block [enter]] : List (Prog isa)) ++ pow W.code S.code M.mm sY sK sEp sEl ++ isOne aY ++
      ([.block [leave, ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]] : List (Prog isa)))) t fun u => T11 p rb u ∧ KX t u := by
  have hq := h.1.choose_spec.1.1.q (by rw [t10_eval h] at he; simpa using he)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_seqs_append (by simp [scan]) (by simp) (WP.mono (t10_q1 p rb t h hq) fun u ⟨hu, k₁⟩ =>
    wp_seqs_cons (by simp [pow]) (WP.mono (q1_q2 p rb u hu) fun v ⟨hv, k₂⟩ =>
      wp_seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (WP.mono (q2_q3 W M S p rb v hv) fun w' ⟨hw, k₃⟩ =>
        wp_seqs_append (by simp [isOne, eqArr]) (by simp) (WP.mono (q3_q4 p rb w' hw) fun x ⟨hx, k₄⟩ => by
          rw [seqs_one]
          exact WP.mono (q4_t11 p rb x hx) fun y ⟨hy, k₅⟩ =>
            ⟨hy, keep_trans (keep_trans k₁ k₂) (keep_trans k₃ (keep_trans k₄ k₅))⟩))))

end VG.Proof.Ffdh.AArch64.GenerateKey
