module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA on PPC64LE: the check of the key's public part

`checkKey_ok`: `checkKey rest fail` runs `rest` exactly when the key's
public part passes the specification's checks (`KeyOk`: `shapeValid` and
`publicChecks`, `Proof/Dsa/Accepted.lean`), in the P space with p and
`R² mod p` in its arrays 0 and 8, q in the Q space's array 0, and q's
significant octets in `r2` (`Checked`); else `fail`. Memory changes only in
`scratch`, apart from the saved registers (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The key's public part passes the specification's checks. -/
def KeyOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  VG.Proof.Dsa.shapeValid (pOf m L key) (qOf m L key) ∧
    VG.Proof.Dsa.publicChecks (pOf m L key) (qOf m L key) (gOf m L key) (yOf m L key)

/-- Memory changed only in `scratch`, apart from the saved registers. -/
structure Kept (L : Lay) (m m' : Mem) : Prop where
  out : Outside L.S 0 L.Z m m'
  sav : ∀ i < 19, word m' L.S (saveOff i) = word m L.S (saveOff i)

theorem Kept.refl (L : Lay) (m : Mem) : Kept L m m := ⟨Outside.refl _ _ _ _, fun _ _ => rfl⟩

theorem Kept.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : Kept L m₁ m₂) (h₂ : Kept L m₂ m₃) : Kept L m₁ m₃ :=
  ⟨h₁.out.trans h₂.out, fun i hi => (h₂.sav i hi).trans (h₁.sav i hi)⟩

theorem Kept.ofBody {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Body L m m') : Kept L m m' :=
  ⟨h.mono (Nat.zero_le _) (by have := hL.z256; omega), fun i hi =>
    Outside.word h (Or.inl (by simp only [saveOff]; omega))
      (by have := hL.nowrap; have := hL.z256; simp only [saveOff]; omega)⟩

/-- A buffer apart from `scratch`, kept. -/
theorem Src.kept {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {m m' : Mem}
    (hk : Outside L.S 0 L.Z m m') :
    Spec.Rsa.bytesAt m' D n = Spec.Rsa.bytesAt m D n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hk _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  by_contra hc
  exact h.sep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

/-- The key's values, kept. -/
theorem key_kept {s : State} {L : Lay} {key : Addr} (hk : Src s L key (3 * L.pl + L.ql)) {m m' : Mem}
    (h : Outside L.S 0 L.Z m m') :
    pOf m' L key = pOf m L key ∧ qOf m' L key = qOf m L key ∧ gOf m' L key = gOf m L key ∧
      yOf m' L key = yOf m L key := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := (hk.sub (o := 0) (k := L.pl) (by omega)).kept h
    simp only [off, BitVec.add_zero] at e
    simp only [pOf]; rw [e]
  · simp only [qOf]; rw [(hk.sub (o := L.pl) (k := L.ql) (by omega)).kept h]
  · simp only [gOf]; rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega)).kept h]
  · simp only [yOf]; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).kept h]


/-- `p ≡ 1 (mod q)`, as the code checks it. -/
theorem pmod_iff {p q : Nat} (hp : 1 ≤ p) (hq : 2 ≤ q) : (p - 1) % q = 0 ↔ p % q = 1 := by
  have h := Nat.div_add_mod p q
  have hr := Nat.mod_lt p (show 0 < q by omega)
  generalize p / q = a at h
  generalize p % q = r at h hr ⊢
  subst h
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rcases a with _ | b
    · simp only [Nat.mul_zero, Nat.add_zero] at hp; omega
    · rw [show q * (b + 1) + 0 - 1 = (q - 1) + q * b by rw [Nat.mul_succ]; omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [show q * a + r - 1 = (r - 1) + q * a by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A change in the P space's arrays keeps the Q space. -/
theorem PBody.keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  have h256 : 256 ≤ L.qOff := by rw [hL.qOff_eq]; omega
  have hlt := (x - L.S).isLt
  have hlt' := (x - L.Q).isLt
  refine h x (Or.inr ?_)
  simp only [ofs, Lay.Q, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega)] at hx
  by_cases hd : L.qOff ≤ (x - L.S).toNat
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hx; omega

theorem PBody.arrQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') (j : Nat) (hj : j < 28) :
    arrQ m' L j = arrQ m L j :=
  Outside.val32 (h.keepQ hL) (by have := slot_lt (w := 4) hj; simp only [Lay.slot_eq] at this ⊢; omega)
    (by have := slot_lt (w := 4) hj; simp only [Lay.slot_eq] at this ⊢; omega)

theorem PBody.qtop {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') :
    word m' L.Q (slot 4 0 + 32) = word m L.Q (slot 4 0 + 32) :=
  Outside.word (h.keepQ hL) (by decide) (by decide)

/-- What the check leaves for `rest`, from the entry state `s` (`r2` holding
`pack p_len q_len 0 d`). -/
structure Checked (s t : State) (L : Lay) (key sig dig : Addr) (d : Nat) : Prop where
  inp : InP t L
  scr : ScrL t L
  regs : Regs t L key sig dig
  p0 : arrP t.mem L 0 = pOf s.mem L key
  ptop : word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0
  p8 : arrP t.mem L 8 = 2 ^ (128 * L.wp) % pOf s.mem L key
  q0 : arrQ t.mem L 0 = qOf s.mem L key
  qtop : word t.mem L.Q (slot 4 0 + 32) = 0
  r2 : t.gpr .r2 = pack L.pl L.ql (Spec.Dsa.bitLength (qOf s.mem L key) / 8) d

/-- The registers `checkKey` writes. -/
def ckRegs : List Reg := sizesRegs ++ pModQRegs ++ setupPRegs ++ elemRegs

theorem checkKey_ok {s : State} {L : Lay} {key sig dig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig dig)
    (h2 : s.gpr .r2 = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, KeyOk s.mem L key → Checked s t L key sig dig d → Kept L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ KeyOk s.mem L key → Kept L s.mem t.mem → t.gpr .r21 = L.S → ScrL t L →
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
  have vals : ∀ {m : Mem}, Kept L s.mem m → pOf m L key = p ∧ qOf m L key = q ∧ gOf m L key = g ∧
      yOf m L key = y := fun hm => by
    obtain ⟨a, b, c, d⟩ := key_kept hk hm.out
    exact ⟨a.trans hP, b.trans hQ', c.trans hG, d.trans hY⟩
  have hKey : KeyOk s.mem L key ↔ VG.Proof.Dsa.shapeValid p q ∧ VG.Proof.Dsa.publicChecks p q g y := by
    rw [KeyOk, hP, hQ', hG, hY]
  unfold checkKey
  refine sizes_ok hL hr h2 hk (fun t₁ hSz m₁ r2₁ k₁ => ?_) (fun t₁ hn m₁ k₁ =>
    hfail t₁ (fun hK => hn hK.1.1) (by rw [m₁]; exact Kept.refl _ _) ((k₁.gpr .r21 (by decide)).trans hr.r21)
      (hs.congr k₁.wr) (k₁.mono (by decide)))
  simp only [SizesOk] at hSz
  rw [hP, hQ'] at hSz
  rw [hQ'] at r2₁
  have hqb : Spec.Dsa.bitLength q / 8 < 2 ^ 16 := by
    unfold Spec.Dsa.supportedSizes at hSz; simp only [Nat.reducePow]; omega
  have K₁ : Kept L s.mem t₁.mem := by rw [m₁]; exact Kept.refl _ _
  have hs₁ : ScrL t₁ L := hs.congr k₁.wr
  have hr₁ : Regs t₁ L key sig dig :=
    Regs.of_pack hL ((k₁.gpr .r21 (by decide)).trans hr.r21) ((k₁.gpr .r27 (by decide)).trans hr.r27)
      ((k₁.gpr .r28 (by decide)).trans hr.r28) ((k₁.gpr .r26 (by decide)).trans hr.r26) r2₁ hqb hd
  refine odds_ok hL hr₁ (hk.keep k₁.rd k₁.wr) (fun t₂ hpo hqo m₂ k₂ => ?_)
    (fun t₂ hn m₂ k₂ => hfail t₂ (fun hK => hn (by
        obtain ⟨ep, eq, -, -⟩ := vals K₁
        rw [ep, eq]; have := (hKey.mp hK).1; exact ⟨this.2.2, this.2.1⟩))
      (by rw [m₂]; exact K₁) ((k₂.gpr .r21 (by decide)).trans hr₁.r21) (hs₁.congr k₂.wr)
      ((k₁.trans k₂).mono (by decide)))
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := vals K₁
  rw [ep₁] at hpo
  rw [eq₁] at hqo
  have B := VG.Proof.Dsa.supported_bounds hSz
  have K₂ : Kept L s.mem t₂.mem := by rw [m₂]; exact K₁
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
  have K₃ := K₂.trans (Kept.ofBody hL B₃)
  have k₁₃ := k₁₂.trans k₃
  have hs₃ : ScrL t₃ L := hs.congr k₁₃.wr
  have hr₃ := hr₂.keep k₃
  have h21₃ : t₃.gpr .r21 = L.S := iq₃.h21
  refine WP.ite (t₃.gpr .r0 == 0) (eval_zero _ _) (fun hb₃ => ?_) (fun hb₃ => hfail t₃ (fun hK => by
      have := (hKey.mp hK).2.2.1
      rw [pmod_iff (by omega) (by omega)] at this
      exact absurd (r0₃.mpr this) (by simpa using hb₃)) K₃ h21₃ hs₃ (k₁₃.mono (by decide)))
  have pm : p % q = 1 := r0₃.mp (by simpa using hb₃)
  -- The P space.
  refine WP.seq (WP.mono (setupP_ok hL hs₃ hr₃ (hk.keep k₁₃.rd k₁₃.wr)
      (by rw [(vals K₃).1]; omega)) fun t₄ ⟨⟨ip₄, p0₄, ptop₄, p8₄, pb₄⟩, k₄⟩ => ?_)
  rw [(vals K₃).1] at p0₄ p8₄
  have B₄ : Body L t₃.mem t₄.mem := pb₄.body hL
  have K₄ := K₃.trans (Kept.ofBody hL B₄)
  have k₁₄ := k₁₃.trans k₄
  have hs₄ : ScrL t₄ L := hs.congr k₁₄.wr
  have hr₄ := hr₃.keep k₄
  have hk₄ := hk.keep k₁₄.rd k₁₄.wr
  -- g.
  refine WP.seq (WP.seq (WP.mono (ptrG_ok hr₄) fun t₅ ⟨⟨a12, a6, m₅⟩, k₅⟩ => ?_))
  have ip₅ := ip₄.keep k₅ (by decide)
  have K₅ : Kept L s.mem t₅.mem := by rw [m₅]; exact K₄
  have hk₅ := hk₄.keep k₅.rd k₅.wr
  have hr₅ := hr₄.keep k₅
  refine WP.mono (checkElem_ok hL hr₅ ip₅ hk₅
      (hk₅.sub (o := L.pl + L.ql) (k := L.pl) (by omega)) a12 a6 (by rw [m₅]; exact p0₄)
      (by rw [m₅]; exact ptop₄) (by omega) hpo (by rw [m₅]; exact p8₄))
    fun t₆ ⟨⟨ip₆, p0₆, ptop₆, p8₆, r0₆, pb₆⟩, k₆⟩ => ?_
  have eg : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₅.mem (off key (L.pl + L.ql)) L.pl) = g := (vals K₅).2.2.1
  rw [eg, (vals K₅).2.1] at r0₆
  have K₆ := K₅.trans (Kept.ofBody hL (pb₆.body hL))
  have k₁₆ := (k₁₄.trans k₅).trans k₆
  have hs₆ : ScrL t₆ L := hs.congr k₁₆.wr
  have hr₆ := hr₅.keep k₆
  refine WP.ite (t₆.gpr .r0 == 0) (eval_zero _ _) (fun hb₆ => ?_) (fun hb₆ => hfail t₆ (fun hK => by
      have H := (hKey.mp hK).2
      exact absurd (r0₆.mpr ⟨H.1.1.1, H.1.1.2, H.2.2.1⟩) (by simpa using hb₆)) K₆ ip₆.h21 hs₆
      (k₁₆.mono (by decide)))
  have hg := r0₆.mp (by simpa using hb₆)
  -- y.
  refine WP.seq (WP.seq (WP.mono (ptrY_ok hr₆) fun t₇ ⟨⟨b12, b6, m₇⟩, k₇⟩ => ?_))
  have ip₇ := ip₆.keep k₇ (by decide)
  have K₇ : Kept L s.mem t₇.mem := by rw [m₇]; exact K₆
  have hk₇ := hk.keep (k₁₆.trans k₇).rd (k₁₆.trans k₇).wr
  have hr₇ := hr₆.keep k₇
  refine WP.mono (checkElem_ok hL hr₇ ip₇ hk₇
      (hk₇.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)) b12 b6 (by rw [m₇]; exact p0₆)
      (by rw [m₇]; exact ptop₆) (by omega) hpo (by rw [m₇, p8₆, m₅]; exact p8₄))
    fun t₈ ⟨⟨ip₈, p0₈, ptop₈, p8₈, r0₈, pb₈⟩, k₈⟩ => ?_
  have ey : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₇.mem (off key (2 * L.pl + L.ql)) L.pl) = y :=
    (vals K₇).2.2.2
  rw [ey, (vals K₇).2.1] at r0₈
  have K₈ := K₇.trans (Kept.ofBody hL (pb₈.body hL))
  have k₁₈ := (k₁₆.trans k₇).trans k₈
  refine WP.ite (t₈.gpr .r0 == 0) (eval_zero _ _) (fun hb₈ => ?_) (fun hb₈ => hfail t₈ (fun hK => by
      have H := (hKey.mp hK).2
      exact absurd (r0₈.mpr ⟨H.1.2.1, H.1.2.2, H.2.2.2⟩) (by simpa using hb₈)) K₈ ip₈.h21
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
