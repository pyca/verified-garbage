module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA signing on PPC64LE: the check of the key, within the body

`checkKeyB_ok`: `checkKey_ok` (`CheckKey.lean`) with the finer facts its
proof finds: memory changes only past `scratch`'s header (`Body`), which
keeps the header's word `hOut`, where signing keeps `out`; and `fail` runs
with the lengths still in `r2` (`Regs`, `sizesR_ok`), which signing's
`zeroOut` reads.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)
open VG.Proof.Bignum (slot)

/-- `sizes_ok`, with `Regs` for `fail`. -/
theorem sizesR_ok {s : State} {L : Lay} {key sig dig : Addr} {d : Nat} {Q : State → Prop} {rest fail : Prog isa}
    (hL : L.Ok) (hr : Regs s L key sig dig) (h2 : s.gpr .r2 = pack L.pl L.ql 0 d)
    (hk : Src s L key (3 * L.pl + L.ql)) (hd : d < 2 ^ 16)
    (hrest : ∀ t, SizesOk s.mem L key → t.mem = s.mem →
      t.gpr .r2 = pack L.pl L.ql (Spec.Dsa.bitLength (qOf s.mem L key) / 8) d →
      Keep sizesRegs s t → WP isa rest t Q)
    (hfail : ∀ t, ¬ SizesOk s.mem L key → t.mem = s.mem → Keep sizesRegs s t → Regs t L key sig dig →
      WP isa fail t Q) :
    WP isa (sizes rest fail) s Q := by
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have hql := hL.ql
  have hnw := hL.nowrap
  have fp := significant_fits (Spec.Rsa.bytesAt s.mem key L.pl)
  have fq := significant_fits (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
  rw [bytesAt_length] at fp fq
  have hSz : SizesOk s.mem L key ↔
      128 ≤ (significant (Spec.Rsa.bytesAt s.mem key L.pl)).2.toNat ∧
        128 ≤ (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).2.toNat ∧
        Spec.Dsa.supportedSizes (8 * (significant (Spec.Rsa.bytesAt s.mem key L.pl)).1)
          (8 * (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1) :=
    Proof.Dsa.supported_scans _ _
  unfold sizes andThen
  -- p's octets
  refine WP.seq (WP.seq (WP.mono (ptrP_ok hr) fun t₁ ⟨⟨a12, a6, am⟩, k1⟩ =>
    WP.mono (bytesBits_ok a12 a6 (by omega) (by omega) fun i hi => by
      rw [k1.rd, k1.wr]; exact hk.rd i (by omega)) fun t₂ ⟨⟨b16, b0, bm⟩, k2⟩ => ?_))
  rw [am] at b16 b0
  have m2 : t₂.mem = s.mem := by rw [bm, am]
  refine WP.ite _ (eval_zero _ _) (fun hz => ?ok) (fun hz => ?bad)
  case bad =>
    refine hfail t₂ (fun h => ?_) m2 (k1.trans k2).mono (hr.keep (k1.trans k2))
    rw [b0.mpr (hSz.mp h).1] at hz
    exact absurd hz (by decide)
  have hp := b0.mp (beq_iff_eq.mp hz)
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun t =>
    t.gpr .r24 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem key L.pl)).1 ∧ t.mem = t₂.mem)
    (by prun [b16, BitVec.add_zero]) (by decide)) fun t₃ ⟨⟨c24, cm⟩, k3⟩ => ?_)
  have kA := (k1.trans k2).trans k3
  have hr₃ : Regs t₃ L key sig dig := hr.keep kA
  -- q's octets
  refine WP.seq (WP.seq (WP.mono (ptrQ_ok hr₃) fun t₄ ⟨⟨d12, d6, dm⟩, k4⟩ =>
    WP.mono (bytesBits_ok d12 d6 (by omega) (by omega) fun i hi => by
      rw [k4.rd, k4.wr, kA.rd, kA.wr]; exact (hk.sub (o := L.pl) (k := L.ql) (by omega)).rd i hi)
      fun t₅ ⟨⟨e16, e0, em⟩, k5⟩ => ?_))
  rw [dm, cm, m2] at e16 e0
  have m5 : t₅.mem = s.mem := by rw [em, dm, cm, m2]
  have kB := (kA.trans k4).trans k5
  refine WP.ite _ (eval_zero _ _) (fun hz' => ?ok2) (fun hz' => ?bad2)
  case bad2 =>
    refine hfail t₅ (fun h => ?_) m5 kB.mono (hr.keep kB)
    rw [e0.mpr (hSz.mp h).2.1] at hz'
    exact absurd hz' (by decide)
  have hq := e0.mp (beq_iff_eq.mp hz')
  have hqb : (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1 < 2 ^ 16 := by
    simp only [Nat.reducePow]; omega
  have h2₅ : t₅.gpr .r2 = pack L.pl L.ql 0 d := (kB.gpr _ (by decide)).trans h2
  refine WP.seq (WP.mono (WP.keep [.r25, .r0, .r2] (Q := fun t =>
    t.gpr .r25 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1 ∧
      t.gpr .r2 = pack L.pl L.ql (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1 d ∧
      t.mem = s.mem)
    (by prun [e16, h2₅, m5, BitVec.add_zero, pack_add hqb]) (by decide)) fun t₆ ⟨⟨f25, f2, fm⟩, k6⟩ => ?_)
  -- the pair
  have g24 : t₆.gpr .r24 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem key L.pl)).1 :=
    (((k4.trans k5).trans k6).gpr _ (by decide)).trans c24
  refine WP.seq (WP.mono (pairs_ok g24 f25 (by omega) (by omega)) fun t₇ ⟨⟨g0, gm⟩, k7⟩ => ?_)
  have kC := (kB.trans k6).trans k7
  have m7 := gm.trans fm
  refine WP.ite _ (eval_zero _ _) (fun hz'' => ?_) (fun hz'' => ?_)
  · have hok : SizesOk s.mem L key := hSz.mpr ⟨hp, hq, g0.mp (beq_iff_eq.mp hz'')⟩
    have hb : Spec.Dsa.bitLength (qOf s.mem L key) / 8 =
        (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1 := by
      rw [show qOf s.mem L key = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql) from rfl,
        Proof.Dsa.subgroup_scan_width (p := Spec.Rsa.bytesAt s.mem key L.pl) hok]
      omega
    exact hrest t₇ hok m7 (by rw [k7.gpr _ (by decide), f2, hb]) kC.mono
  · refine hfail t₇ (fun h => ?_) m7 kC.mono (Regs.of_pack hL ((kC.gpr _ (by decide)).trans hr.r21)
      ((kC.gpr _ (by decide)).trans hr.r27) ((kC.gpr _ (by decide)).trans hr.r28)
      ((kC.gpr _ (by decide)).trans hr.r26) ((k7.gpr _ (by decide)).trans f2) hqb hd)
    rw [g0.mpr (hSz.mp h).2.2] at hz''
    exact absurd hz'' (by decide)

theorem checkKeyB_ok {s : State} {L : Lay} {key sig dig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig dig)
    (h2 : s.gpr .r2 = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, KeyOk s.mem L key → Checked s t L key sig dig d → Body L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ KeyOk s.mem L key → Body L s.mem t.mem → Regs t L key sig dig → ScrL t L →
      Keep ckRegs s t → WP isa fail t Q) :
    WP isa (checkKey rest fail) s Q := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hw := hL.wp_ge
  generalize hP : pOf s.mem L key = p
  generalize hQ' : qOf s.mem L key = q
  generalize hG : gOf s.mem L key = g
  generalize hY : yOf s.mem L key = y
  have vals : ∀ {m : Mem}, Body L s.mem m → pOf m L key = p ∧ qOf m L key = q ∧ gOf m L key = g ∧
      yOf m L key = y := fun hm => by
    obtain ⟨a, b, c, d⟩ := key_kept hk (Kept.ofBody hL hm).out
    exact ⟨a.trans hP, b.trans hQ', c.trans hG, d.trans hY⟩
  have hKey : KeyOk s.mem L key ↔ VG.Proof.Dsa.shapeValid p q ∧ VG.Proof.Dsa.publicChecks p q g y := by
    rw [KeyOk, hP, hQ', hG, hY]
  unfold checkKey
  refine sizesR_ok hL hr h2 hk hd (fun t₁ hSz m₁ r2₁ k₁ => ?_) (fun t₁ hn m₁ k₁ hr₁ =>
    hfail t₁ (fun hK => hn hK.1.1) (by rw [m₁]; exact Body.refl _ _) hr₁
      (hs.congr k₁.wr) (k₁.mono (by decide)))
  simp only [SizesOk] at hSz
  rw [hP, hQ'] at hSz
  rw [hQ'] at r2₁
  have hqb : Spec.Dsa.bitLength q / 8 < 2 ^ 16 := by
    unfold Spec.Dsa.supportedSizes at hSz; simp only [Nat.reducePow]; omega
  have K₁ : Body L s.mem t₁.mem := by rw [m₁]; exact Body.refl _ _
  have hs₁ : ScrL t₁ L := hs.congr k₁.wr
  have hr₁ : Regs t₁ L key sig dig :=
    Regs.of_pack hL ((k₁.gpr .r21 (by decide)).trans hr.r21) ((k₁.gpr .r27 (by decide)).trans hr.r27)
      ((k₁.gpr .r28 (by decide)).trans hr.r28) ((k₁.gpr .r26 (by decide)).trans hr.r26) r2₁ hqb hd
  refine odds_ok hL hr₁ (hk.keep k₁.rd k₁.wr) (fun t₂ hpo hqo m₂ k₂ => ?_)
    (fun t₂ hn m₂ k₂ => hfail t₂ (fun hK => hn (by
        obtain ⟨ep, eq, -, -⟩ := vals K₁
        rw [ep, eq]; have := (hKey.mp hK).1; exact ⟨this.2.2, this.2.1⟩))
      (by rw [m₂]; exact K₁) (hr₁.keep k₂) (hs₁.congr k₂.wr)
      ((k₁.trans k₂).mono (by decide)))
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := vals K₁
  rw [ep₁] at hpo
  rw [eq₁] at hqo
  have B := VG.Proof.Dsa.supported_bounds hSz
  have K₂ : Body L s.mem t₂.mem := by rw [m₂]; exact K₁
  have k₁₂ := k₁.trans k₂
  have hs₂ : ScrL t₂ L := hs.congr k₁₂.wr
  have hr₂ := hr₁.keep k₂
  have hk₂ := hk.keep k₁₂.rd k₁₂.wr
  -- `p mod q = 1`.
  refine WP.seq (WP.mono (pModQ_ok hL hs₂ hr₂ hk₂ (by rw [(vals K₂).2.1]; omega))
    fun t₃ ⟨⟨iq₃, q0₃, qtop₃, r0₃, qb₃⟩, k₃⟩ => ?_)
  rw [(vals K₂).1, (vals K₂).2.1] at r0₃
  rw [(vals K₂).2.1] at q0₃
  have B₃ : Body L t₂.mem t₃.mem := qb₃.body hL
  have K₃ := K₂.trans B₃
  have k₁₃ := k₁₂.trans k₃
  have hs₃ : ScrL t₃ L := hs.congr k₁₃.wr
  have hr₃ := hr₂.keep k₃
  have h21₃ : t₃.gpr .r21 = L.S := iq₃.h21
  refine WP.ite (t₃.gpr .r0 == 0) (eval_zero _ _) (fun hb₃ => ?_) (fun hb₃ => hfail t₃ (fun hK => by
      have := (hKey.mp hK).2.2.1
      rw [pmod_iff (by omega) (by omega)] at this
      exact absurd (r0₃.mpr this) (by simpa using hb₃)) K₃ hr₃ hs₃ (k₁₃.mono (by decide)))
  have pm : p % q = 1 := r0₃.mp (by simpa using hb₃)
  -- The P space.
  refine WP.seq (WP.mono (setupP_ok hL hs₃ hr₃ (hk.keep k₁₃.rd k₁₃.wr)
      (by rw [(vals K₃).1]; omega)) fun t₄ ⟨⟨ip₄, p0₄, ptop₄, p8₄, pb₄⟩, k₄⟩ => ?_)
  rw [(vals K₃).1] at p0₄ p8₄
  have B₄ : Body L t₃.mem t₄.mem := pb₄.body hL
  have K₄ := K₃.trans B₄
  have k₁₄ := k₁₃.trans k₄
  have hs₄ : ScrL t₄ L := hs.congr k₁₄.wr
  have hr₄ := hr₃.keep k₄
  have hk₄ := hk.keep k₁₄.rd k₁₄.wr
  -- g.
  refine WP.seq (WP.seq (WP.mono (ptrG_ok hr₄) fun t₅ ⟨⟨a12, a6, m₅⟩, k₅⟩ => ?_))
  have ip₅ := ip₄.keep k₅ (by decide)
  have K₅ : Body L s.mem t₅.mem := by rw [m₅]; exact K₄
  have hk₅ := hk₄.keep k₅.rd k₅.wr
  have hr₅ := hr₄.keep k₅
  refine WP.mono (checkElem_ok hL hr₅ ip₅ hk₅
      (hk₅.sub (o := L.pl + L.ql) (k := L.pl) (by omega)) a12 a6 (by rw [m₅]; exact p0₄)
      (by rw [m₅]; exact ptop₄) (by omega) hpo (by rw [m₅]; exact p8₄))
    fun t₆ ⟨⟨ip₆, p0₆, ptop₆, p8₆, r0₆, pb₆⟩, k₆⟩ => ?_
  have eg : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₅.mem (off key (L.pl + L.ql)) L.pl) = g := (vals K₅).2.2.1
  rw [eg, (vals K₅).2.1] at r0₆
  have K₆ := K₅.trans (pb₆.body hL)
  have k₁₆ := (k₁₄.trans k₅).trans k₆
  have hs₆ : ScrL t₆ L := hs.congr k₁₆.wr
  have hr₆ := hr₅.keep k₆
  refine WP.ite (t₆.gpr .r0 == 0) (eval_zero _ _) (fun hb₆ => ?_) (fun hb₆ => hfail t₆ (fun hK => by
      have H := (hKey.mp hK).2
      exact absurd (r0₆.mpr ⟨H.1.1.1, H.1.1.2, H.2.2.1⟩) (by simpa using hb₆)) K₆ hr₆ hs₆
      (k₁₆.mono (by decide)))
  have hg := r0₆.mp (by simpa using hb₆)
  -- y.
  refine WP.seq (WP.seq (WP.mono (ptrY_ok hr₆) fun t₇ ⟨⟨b12, b6, m₇⟩, k₇⟩ => ?_))
  have ip₇ := ip₆.keep k₇ (by decide)
  have K₇ : Body L s.mem t₇.mem := by rw [m₇]; exact K₆
  have hk₇ := hk.keep (k₁₆.trans k₇).rd (k₁₆.trans k₇).wr
  have hr₇ := hr₆.keep k₇
  refine WP.mono (checkElem_ok hL hr₇ ip₇ hk₇
      (hk₇.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)) b12 b6 (by rw [m₇]; exact p0₆)
      (by rw [m₇]; exact ptop₆) (by omega) hpo (by rw [m₇, p8₆, m₅]; exact p8₄))
    fun t₈ ⟨⟨ip₈, p0₈, ptop₈, p8₈, r0₈, pb₈⟩, k₈⟩ => ?_
  have ey : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₇.mem (off key (2 * L.pl + L.ql)) L.pl) = y :=
    (vals K₇).2.2.2
  rw [ey, (vals K₇).2.1] at r0₈
  have K₈ := K₇.trans (pb₈.body hL)
  have k₁₈ := (k₁₆.trans k₇).trans k₈
  refine WP.ite (t₈.gpr .r0 == 0) (eval_zero _ _) (fun hb₈ => ?_) (fun hb₈ => hfail t₈ (fun hK => by
      have H := (hKey.mp hK).2
      exact absurd (r0₈.mpr ⟨H.1.2.1, H.1.2.2, H.2.2.2⟩) (by simpa using hb₈)) K₈ (hr₇.keep k₈)
      (hs.congr k₁₈.wr) (k₁₈.mono (by decide)))
  have hy := r0₈.mp (by simpa using hb₈)
  -- `rest`.
  have hok : KeyOk s.mem L key := hKey.mpr ⟨⟨hSz, hqo, hpo⟩,
    ⟨⟨hg.1, hg.2.1⟩, hy.1, hy.2.1⟩, (pmod_iff (by omega) (by omega)).mpr pm, hg.2.2, hy.2.2⟩
  have pb₆₈ : PBody L t₄.mem t₈.mem := by rw [m₅] at pb₆; rw [m₇] at pb₈; exact (pb₆.trans pb₈)
  have k₂₈ := (((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈
  refine hrest t₈ hok ⟨ip₈, hs.congr k₁₈.wr, hr₇.keep k₈, ?_, ptop₈, ?_, ?_, ?_, ?_⟩ K₈ (k₁₈.mono (by decide))
  · rw [hP]; exact p0₈
  · rw [p8₈, m₇, p8₆, m₅, hP]; exact p8₄
  · rw [hQ', (pb₄.trans pb₆₈).arrQ hL 0 (by decide)]; exact q0₃
  · rw [(pb₄.trans pb₆₈).qtop hL]; exact qtop₃
  · rw [hQ', k₂₈.gpr .r2 (by decide)]; exact r2₁

end VG.Proof.Dsa.PPC64LE
