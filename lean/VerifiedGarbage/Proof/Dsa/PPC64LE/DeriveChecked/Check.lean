module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Check
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Basic
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA on PPC64LE: the check of a domain that was checked before

`rangeElem_ok`: `rangeElem`, `checkElem` without `elemOrder`, loads a number
into the P space's array 4 and leaves `r0 = 0` exactly when it is above 1
and below p. `checkDomain_ok`: `checkDomain rest fail` runs `rest` exactly
when the domain passes `checkParams`'s checks but `g^q mod p = 1`
(`DomainOk`), leaving what `checkParams` leaves (`Checked`); else `fail`.
A domain that passes `ParamsOk` passes `DomainOk`
(`ParamsOk.domainOk`), so for one known to pass the result is
`checkParams_ok`'s.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The domain passes `checkDomain`'s checks: `ParamsOk` without
`g^q mod p = 1`. -/
def DomainOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  VG.Proof.Dsa.shapeValid (pOf m L key) (qOf m L key) ∧
    (1 < gOf m L key ∧ gOf m L key < pOf m L key) ∧ (pOf m L key - 1) % qOf m L key = 0

theorem ParamsOk.domainOk {m : Mem} {L : Lay} {key : Addr} (h : ParamsOk m L key) : DomainOk m L key :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- `rangeElem`, in the P space with p in array 0: the `p_len` octets at `E`
(`r12`, `p_len` in `r6`) into array 4, and `r0 = 0` exactly when their
number `e` has `1 < e < p`. Arrays 0 and 8 are kept. -/
theorem rangeElem_ok {s : State} {L : Lay} {E : Addr} {p : Nat} (hL : L.Ok) (hin : InP s L)
    (he : Src s L E L.pl) (h12 : s.gpr .r12 = E) (h6 : s.gpr .r6 = BitVec.ofNat 64 L.pl)
    (hp0 : arrP s.mem L 0 = p) (hz0 : word s.mem L.S (slot L.wp 0 + 8 * L.wp) = 0) :
    WP isa Derive.rangeElem s fun t =>
      (InP t L ∧ arrP t.mem L 0 = p ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 24 = arrP s.mem L 24 ∧
        (t.gpr .r0 = 0 ↔ (1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) < p)) ∧
        PBody L s.mem t.mem) ∧
        Keep elemRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e3 := slot_eq L.wp 3; have e4 := slot_eq L.wp 4
  have e8 := slot_eq L.wp 8; have e24 := slot_eq L.wp 24; have e28 := slot_eq L.wp 28
  have en := hin.env
  unfold Derive.rangeElem
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (by decide) h12 h6 (by omega_arith) (by omega_arith) he.rd
    (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx (by omega_arith)))) fun s₁ ⟨⟨v4, top4, o1, a10⟩, k1⟩ => ?_)
  have en1 := env_keep10 en k1 (by decide) a10
  have pb1 : PBody L s.mem s₁.mem := o1.mono (by omega_arith) (by omega_arith)
  have p1 : arr s₁.mem L.S L.wp 0 = p := by rw [arr, Outside.val32 o1 (by omega_arith) (by omega_arith)]; exact hp0
  refine WP.mono (elemRange_ok en1 top4) fun s₂ ⟨⟨r0i, _, o2, en2⟩, k2⟩ => ?_
  have pb2 : PBody L s₁.mem s₂.mem := o2.mono (by omega_arith) (by omega_arith)
  have p2 : arr s₂.mem L.S L.wp 0 = p := by rw [arr, Outside.val32 o2 (by omega_arith) (by omega_arith)]; exact p1
  have z2 : word s₂.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 := by
    rw [Outside.word o2 (by omega_arith) (by omega_arith), Outside.word o1 (by omega_arith) (by omega_arith)]; exact hz0
  have r2 : arrP s₂.mem L 24 = arrP s.mem L 24 := by
    show val32 s₂.mem L.S (slot L.wp 24) (2 * L.wp) = _
    rw [Outside.val32 o2 (by omega_arith) (by omega_arith), Outside.val32 o1 (by omega_arith) (by omega_arith)]
  have x1 : arr s₁.mem L.S L.wp 4 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) := v4
  rw [x1, p1] at r0i
  have k12 := k1.trans k2
  exact ⟨⟨⟨en2, (k12.gpr .r21 (by decide)).trans hin.h21, (k12.gpr .r23 (by decide)).trans hin.h23⟩, p2, z2, r2,
    r0i, pb1.trans pb2⟩, k12.mono (by decide)⟩

theorem checkDomain_ok {s : State} {L : Lay} {key sig dig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig dig)
    (h2 : s.gpr .r2 = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (2 * L.pl + L.ql))
    (hrest : ∀ t, DomainOk s.mem L key → Checked s t L key sig dig d → Body L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ DomainOk s.mem L key → Body L s.mem t.mem → Regs t L key sig dig → ScrL t L →
      Keep ckRegs s t → WP isa fail t Q) :
    WP isa (Derive.checkDomain rest fail) s Q := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hw := hL.wp_ge
  generalize hP : pOf s.mem L key = p
  generalize hQ' : qOf s.mem L key = q
  generalize hG : gOf s.mem L key = g
  have vals : ∀ {m : Mem}, Body L s.mem m → pOf m L key = p ∧ qOf m L key = q ∧ gOf m L key = g := fun hm => by
    obtain ⟨a, b, c⟩ := params_kept hk (Kept.ofBody hL hm).out
    exact ⟨a.trans hP, b.trans hQ', c.trans hG⟩
  have hDom : DomainOk s.mem L key ↔ VG.Proof.Dsa.shapeValid p q ∧ (1 < g ∧ g < p) ∧ (p - 1) % q = 0 := by
    rw [DomainOk, hP, hQ', hG]
  unfold Derive.checkDomain
  refine sizes_ok hL hr h2 hk hd (fun t₁ hSz m₁ r2₁ k₁ => ?_) (fun t₁ hn m₁ k₁ hr₁ =>
    hfail t₁ (fun hK => hn hK.1.1) (by rw [m₁]; exact Body.refl _ _) hr₁
      (hs.congr k₁.wr) (k₁.mono (by decide)))
  simp only [SizesOk] at hSz
  rw [hP, hQ'] at hSz
  rw [hQ'] at r2₁
  have hqb : Spec.Dsa.bitLength q / 8 < 2 ^ 16 := by
    unfold Spec.Dsa.supportedSizes at hSz; simp only [Nat.reducePow]; omega_arith
  have K₁ : Body L s.mem t₁.mem := by rw [m₁]; exact Body.refl _ _
  have hs₁ : ScrL t₁ L := hs.congr k₁.wr
  have hr₁ : Regs t₁ L key sig dig :=
    Regs.of_pack hL ((k₁.gpr .r21 (by decide)).trans hr.r21) ((k₁.gpr .r27 (by decide)).trans hr.r27)
      ((k₁.gpr .r28 (by decide)).trans hr.r28) ((k₁.gpr .r26 (by decide)).trans hr.r26) r2₁ hqb hd
  refine odds_ok hL hr₁ (hk.keep k₁.rd k₁.wr) (fun t₂ hpo hqo m₂ k₂ => ?_)
    (fun t₂ hn m₂ k₂ => hfail t₂ (fun hK => hn (by
        obtain ⟨ep, eq, -⟩ := vals K₁
        rw [ep, eq]; have := (hDom.mp hK).1; exact ⟨this.2.2, this.2.1⟩))
      (by rw [m₂]; exact K₁) (hr₁.keep k₂) (hs₁.congr k₂.wr)
      ((k₁.trans k₂).mono (by decide)))
  obtain ⟨ep₁, eq₁, -⟩ := vals K₁
  rw [ep₁] at hpo
  rw [eq₁] at hqo
  have B := VG.Proof.Dsa.supported_bounds hSz
  have K₂ : Body L s.mem t₂.mem := by rw [m₂]; exact K₁
  have k₁₂ := k₁.trans k₂
  have hs₂ : ScrL t₂ L := hs.congr k₁₂.wr
  have hr₂ := hr₁.keep k₂
  have hk₂ := hk.keep k₁₂.rd k₁₂.wr
  -- `p mod q = 1`.
  refine WP.seq (WP.mono (pModQ_ok hL hs₂ hr₂ hk₂ (by rw [(vals K₂).2.1]; omega_arith))
    fun t₃ ⟨⟨iq₃, q0₃, qtop₃, r0₃, qb₃⟩, k₃⟩ => ?_)
  rw [(vals K₂).1, (vals K₂).2.1] at r0₃
  rw [(vals K₂).2.1] at q0₃
  have B₃ : Body L t₂.mem t₃.mem := qb₃.body hL
  have K₃ := K₂.trans B₃
  have k₁₃ := k₁₂.trans k₃
  have hs₃ : ScrL t₃ L := hs.congr k₁₃.wr
  have hr₃ := hr₂.keep k₃
  refine WP.ite (t₃.gpr .r0 == 0) (eval_zero _ _) (fun hb₃ => ?_) (fun hb₃ => hfail t₃ (fun hK => by
      have := (hDom.mp hK).2.2
      rw [pmod_iff (by omega_arith) (by omega_arith)] at this
      exact absurd (r0₃.mpr this) (by simpa using hb₃)) K₃ hr₃ hs₃ (k₁₃.mono (by decide)))
  have pm : p % q = 1 := r0₃.mp (by simpa using hb₃)
  -- The P space.
  refine WP.seq (WP.mono (setupP_ok hL hs₃ hr₃ (hk.keep k₁₃.rd k₁₃.wr)
      (by rw [(vals K₃).1]; omega_arith) (by rw [(vals K₃).1]; exact hpo)) fun t₄ ⟨⟨ip₄, p0₄, ptop₄, p8₄, pb₄⟩, k₄⟩ => ?_)
  rw [(vals K₃).1] at p0₄ p8₄
  have B₄ : Body L t₃.mem t₄.mem := pb₄.body hL
  have K₄ := K₃.trans B₄
  have k₁₄ := k₁₃.trans k₄
  have hr₄ := hr₃.keep k₄
  have hk₄ := hk.keep k₁₄.rd k₁₄.wr
  -- g's range.
  refine WP.seq (WP.seq (WP.mono (ptrG_ok hr₄) fun t₅ ⟨⟨a12, a6, m₅⟩, k₅⟩ => ?_))
  have ip₅ := ip₄.keep k₅ (by decide)
  have K₅ : Body L s.mem t₅.mem := by rw [m₅]; exact K₄
  have hk₅ := hk₄.keep k₅.rd k₅.wr
  have hr₅ := hr₄.keep k₅
  refine WP.mono (rangeElem_ok (p := p) hL ip₅ (hk₅.sub (o := L.pl + L.ql) (k := L.pl) (by omega_arith)) a12 a6
      (by rw [m₅]; exact p0₄) (by rw [m₅]; exact ptop₄))
    fun t₆ ⟨⟨ip₆, p0₆, ptop₆, p8₆, r0₆, pb₆⟩, k₆⟩ => ?_
  have eg : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₅.mem (off key (L.pl + L.ql)) L.pl) = g := (vals K₅).2.2
  rw [eg] at r0₆
  have K₆ := K₅.trans (pb₆.body hL)
  have k₁₆ := (k₁₄.trans k₅).trans k₆
  have hs₆ : ScrL t₆ L := hs.congr k₁₆.wr
  have hr₆ := hr₅.keep k₆
  refine WP.ite (t₆.gpr .r0 == 0) (eval_zero _ _) (fun hb₆ => ?_) (fun hb₆ => hfail t₆ (fun hK => by
      have H := hDom.mp hK
      exact absurd (r0₆.mpr H.2.1) (by simpa using hb₆)) K₆ hr₆ hs₆
      (k₁₆.mono (by decide)))
  have hg := r0₆.mp (by simpa using hb₆)
  -- `rest`.
  have hok : DomainOk s.mem L key := hDom.mpr ⟨⟨hSz, hqo, hpo⟩, hg,
    (pmod_iff (by omega_arith) (by omega_arith)).mpr pm⟩
  rw [m₅] at pb₆
  have k₂₆ := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆)
  refine hrest t₆ hok ⟨ip₆, hs₆, hr₆, ?_, ptop₆, ?_, ?_, ?_, ?_⟩ K₆ (k₁₆.mono (by decide))
  · rw [hP]; exact p0₆
  · rw [p8₆, m₅, hP]; exact p8₄
  · rw [hQ', (pb₄.trans pb₆).arrQ hL 0 (by decide)]; exact q0₃
  · rw [(pb₄.trans pb₆).qtop hL]; exact qtop₃
  · rw [hQ', k₂₆.gpr .r2 (by decide)]; exact r2₁

end VG.Proof.Dsa.PPC64LE
