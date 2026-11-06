module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: the check of the domain and of the key's public part

As on PPC64LE (`Proof/Dsa/PPC64LE/CheckKey.lean`).
`checkParams_ok`: `checkParams rest fail` runs `rest` exactly when the domain
p||q||g passes the specification's checks (`ParamsOk`), in the P space with
p, `-p⁻¹ mod 2⁶⁴` and `R² mod p` in its array 0, `t1` and array 24, q in the
Q space's array 0, and q's significant octets in the header's lengths
(`Checked`); else `fail`. `checkKey_ok`: `checkKey rest fail`, which checks y
after it, the same for the key's public part (`KeyOk`). Memory changes only
in the header's lengths and past `scratch`'s header (`Kept`), which keeps
the saved registers.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)

/-- The domain passes the specification's checks: `shapeValid` and
`parametersValid`'s algebra (`publicChecks` without y's). -/
def ParamsOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  VG.Proof.Dsa.shapeValid (pOf m L key) (qOf m L key) ∧
    (1 < gOf m L key ∧ gOf m L key < pOf m L key) ∧ (pOf m L key - 1) % qOf m L key = 0 ∧
      gOf m L key ^ qOf m L key % pOf m L key = 1

instance (m : Mem) (L : Lay) (key : Addr) : Decidable (ParamsOk m L key) := by
  unfold ParamsOk
  infer_instance

/-- The key's public part passes the specification's checks. -/
def KeyOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  VG.Proof.Dsa.shapeValid (pOf m L key) (qOf m L key) ∧
    VG.Proof.Dsa.publicChecks (pOf m L key) (qOf m L key) (gOf m L key) (yOf m L key)

/-- Memory changed only in `scratch`'s header word `hLens` and past its
header. -/
def Kept (L : Lay) (m m' : Mem) : Prop :=
  ∀ x, (ofs L.S x < hLens ∨ (hLens + 8 ≤ ofs L.S x ∧ ofs L.S x < 256) ∨ L.Z ≤ ofs L.S x) → m' x = m x

theorem Kept.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : Kept L m₁ m₂) (h₂ : Kept L m₂ m₃) : Kept L m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Kept.ofHdr {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hLens 8 m m') : Kept L m m' :=
  fun x hx => h x (by have := hL.z256; simp only [hLens] at hx ⊢; omega)

theorem Kept.ofBody {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Body L m m') : Kept L m m' :=
  fun x hx => h x (by have := hL.z256; simp only [hLens] at hx; omega)

/-- Memory outside `scratch`, kept. -/
theorem Kept.out {L : Lay} {m m' : Mem} (h : Kept L m m') : Outside L.S 0 L.Z m m' :=
  fun x hx => h x (Or.inr (Or.inr (by omega)))

/-- A word of the header but `hLens`, kept: the mask, the digest's address
and the saved registers. -/
theorem Kept.word {L : Lay} {m m' : Mem} (h : Kept L m m') {d : Nat}
    (hd : d + 8 ≤ hLens ∨ (hLens + 8 ≤ d ∧ d + 8 ≤ 256)) : word m' L.S d = word m L.S d :=
  (Mem.readW_congr fun i hi =>
    (h _ (by rw [ofs_off L.S (by simp only [hLens] at hd; omega)]; simp only [hLens] at hd ⊢; omega)).symm).symm

/-- The domain's values, kept. -/
theorem params_kept {s : State} {L : Lay} {key : Addr} (hk : Src s L key (2 * L.pl + L.ql)) {m m' : Mem}
    (h : Kept L m m') :
    pOf m' L key = pOf m L key ∧ qOf m' L key = qOf m L key ∧ gOf m' L key = gOf m L key := by
  have o := h.out
  refine ⟨?_, ?_, ?_⟩
  · simp only [pOf]; rw [(hk.take (k := L.pl) (by omega)).bytes o (by omega)]
  · simp only [qOf]; rw [(hk.sub (o := L.pl) (k := L.ql) (by omega)).bytes o (by omega)]
  · simp only [gOf]; rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega)).bytes o (by omega)]

/-- y, kept. -/
theorem y_kept {s : State} {L : Lay} {key : Addr} (hk : Src s L key (3 * L.pl + L.ql)) {m m' : Mem}
    (h : Kept L m m') : yOf m' L key = yOf m L key := by
  simp only [yOf]; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).bytes h.out (by omega)]

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
  rw [Offset.toNat_sub_add x L.S (by omega_arith)] at hx
  by_cases hd : L.qOff ≤ (x - L.S).toNat
  · omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)] at hx; omega_arith

theorem PBody.arrQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') : arrQ m' L 0 = arrQ m L 0 :=
  (h.keepQ hL).wordsVal (Or.inl (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega)

theorem PBody.qtop {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') :
    word m' L.Q (slot L.wq 0 + 8 * L.wq) = word m L.Q (slot L.wq 0 + 8 * L.wq) :=
  (h.keepQ hL).word (Or.inl (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega)

/-- What the check leaves for `rest`, from the entry state `s` (the
header's lengths `pack p_len q_len 0 d`). -/
structure Checked (s t : State) (L : Lay) (key sig : Addr) (d : Nat) : Prop where
  inp : InP t L
  scr : ScrL t L
  regs : Regs t L key sig
  p0 : arrP t.mem L 0 = pOf s.mem L key
  ptop : word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0
  inv : ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  p24 : arrP t.mem L 24 = 2 ^ (128 * L.wp) % pOf s.mem L key
  q0 : arrQ t.mem L 0 = qOf s.mem L key
  qtop : word t.mem L.Q (slot L.wq 0 + 8 * L.wq) = 0
  lens : word t.mem L.S hLens = pack L.pl L.ql (Spec.Dsa.bitLength (qOf s.mem L key) / 8) d

/-- `Checked` through `checkElem`. -/
theorem Checked.elem {s t u : State} {L : Lay} {key sig : Addr} {d : Nat} (hL : L.Ok)
    (hc : Checked s t L key sig d) {rs : List Reg} (k : Keep rs t u) (hrs : ∀ r ∈ regsRegs, r ∉ rs)
    (ht1 : u.gpr .t1 = t.gpr .t1) (hin : InP u L)
    (o : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) t.mem u.mem) : Checked s u L key sig d := by
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e24 := e 24
  have hqZ : L.qOff ≤ L.Z := by have := hbuf; simp only [Lay.bOff] at this; omega
  have hb := p_arrays_body hL o
  have pb : PBody L t.mem u.mem := PBody.of o (by omega) (by simp only [Lay.qOff, Lay.slot_eq]; omega)
  refine ⟨hin, hc.scr.congr k.2.2, hc.regs.keep k hb hrs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [arrP, o.wordsVal (by omega) (by omega_arith)]; exact hc.p0
  · rw [o.word (by omega) (by omega_arith)]; exact hc.ptop
  · rw [o.word (by omega) (by omega_arith), ht1]; exact hc.inv
  · rw [arrP, o.wordsVal (by omega) (by omega_arith)]; exact hc.p24
  · rw [pb.arrQ hL]; exact hc.q0
  · rw [pb.qtop hL]; exact hc.qtop
  · rw [hb.word (by decide)]; exact hc.lens

theorem keepPre {rs rs' : List Reg} {s t : State} (k : Keep rs s t) : Keep (rs ++ rs') s t :=
  k.mono fun _ h => List.mem_append_left _ h

/-- The registers `checkParams` writes. -/
def cpRegs : List Reg := sizesRegs ++ oddsRegs ++ pModQRegs ++ setupPRegs ++ ptrRegs ++ elemRegs

/-- The registers `checkKey` writes. -/
def ckRegs : List Reg := cpRegs ++ ptrRegs ++ elemRegs

/-- `KeyOk` is `ParamsOk` and y's checks. -/
theorem keyOk_iff {m : Mem} {L : Lay} {key : Addr} :
    KeyOk m L key ↔ ParamsOk m L key ∧ (1 < yOf m L key ∧ yOf m L key < pOf m L key) ∧
      yOf m L key ^ qOf m L key % pOf m L key = 1 := by
  simp only [KeyOk, ParamsOk, VG.Proof.Dsa.publicChecks]
  constructor
  · rintro ⟨sh, ⟨g, y⟩, d, gq, yq⟩
    exact ⟨⟨sh, g, d, gq⟩, y, yq⟩
  · rintro ⟨⟨sh, g, d, gq⟩, y, yq⟩
    exact ⟨sh, ⟨g, y⟩, d, gq, yq⟩

theorem checkParams_ok {s : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (2 * L.pl + L.ql))
    (hrest : ∀ t, ParamsOk s.mem L key → Checked s t L key sig d → Kept L s.mem t.mem → Keep cpRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ ParamsOk s.mem L key → Kept L s.mem t.mem → Regs t L key sig → ScrL t L →
      Keep cpRegs s t → WP isa fail t Q) :
    WP isa (checkParams rest fail) s Q := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  generalize hP : pOf s.mem L key = p
  generalize hQ' : qOf s.mem L key = q
  generalize hG : gOf s.mem L key = g
  have vals : ∀ {m : Mem}, Kept L s.mem m → pOf m L key = p ∧ qOf m L key = q ∧ gOf m L key = g := fun hm => by
    obtain ⟨a, b, c⟩ := params_kept hk hm
    exact ⟨a.trans hP, b.trans hQ', c.trans hG⟩
  have hPar : ParamsOk s.mem L key ↔ VG.Proof.Dsa.shapeValid p q ∧
      (1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1 := by
    rw [ParamsOk, hP, hQ', hG]
  unfold checkParams
  refine sizes_ok hL hs hr hlen hk hd (fun t₁ hSz o₁ w₁ k₁ hr₁ => ?_) (fun t₁ hn o₁ k₁ hr₁ =>
    hfail t₁ (fun hK => hn hK.1.1) (Kept.ofHdr hL o₁) hr₁ (hs.congr k₁.2.2) (keepPre (keepPre (keepPre (keepPre (keepPre k₁))))))
  simp only [SizesOk] at hSz
  rw [hP, hQ'] at hSz
  rw [hQ'] at w₁
  have K₁ : Kept L s.mem t₁.mem := Kept.ofHdr hL o₁
  have hs₁ : ScrL t₁ L := hs.congr k₁.2.2
  have hk₁ := hk.keep k₁.2.1 k₁.2.2
  refine odds_ok hL hs₁ hr₁ hk₁ (fun t₂ hpo hqo m₂ k₂ => ?_)
    (fun t₂ hn m₂ k₂ => hfail t₂ (fun hK => hn (by
        obtain ⟨ep, eq, -⟩ := vals K₁
        rw [ep, eq]; have := (hPar.mp hK).1; exact ⟨this.2.2, this.2.1⟩))
      (by rw [m₂]; exact K₁) (hr₁.keepM k₂ m₂) (hs₁.congr k₂.2.2) (keepPre (keepPre (keepPre (keepPre (k₁.trans k₂))))))
  obtain ⟨ep₁, eq₁, -⟩ := vals K₁
  rw [ep₁] at hpo
  rw [eq₁] at hqo
  have B := VG.Proof.Dsa.supported_bounds hSz
  have K₂ : Kept L s.mem t₂.mem := by rw [m₂]; exact K₁
  have k₁₂ := k₁.trans k₂
  have hs₂ : ScrL t₂ L := hs.congr k₁₂.2.2
  have hr₂ := hr₁.keepM k₂ m₂
  have hk₂ := hk.keep k₁₂.2.1 k₁₂.2.2
  have w₂ : word t₂.mem L.S hLens = pack L.pl L.ql (Spec.Dsa.bitLength q / 8) d := by rw [m₂]; exact w₁
  -- `p mod q = 1`.
  refine WP.seq (WP.mono (pModQ_ok hL hs₂ hr₂ hk₂ (by rw [(vals K₂).2.1]; omega))
    fun t₃ ⟨⟨iq₃, q0₃, qtop₃, r0₃, qb₃⟩, k₃⟩ => ?_)
  rw [(vals K₂).1, (vals K₂).2.1] at r0₃
  rw [(vals K₂).2.1] at q0₃
  have B₃ : Body L t₂.mem t₃.mem := qb₃.body hL
  have K₃ := K₂.trans (Kept.ofBody hL B₃)
  have k₁₃ := k₁₂.trans k₃
  have hs₃ : ScrL t₃ L := hs.congr k₁₃.2.2
  have hr₃ := hr₂.keep k₃ B₃
  have w₃ : word t₃.mem L.S hLens = pack L.pl L.ql (Spec.Dsa.bitLength q / 8) d := by rw [B₃.word (by decide)]; exact w₂
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb₃ => ?_) (fun hb₃ => hfail t₃ (fun hK => by
      have := (hPar.mp hK).2.2.1
      rw [pmod_iff (by omega) (by omega)] at this
      rw [r0₃.mpr this] at hb₃
      exact absurd hb₃ (by decide)) K₃ hr₃ hs₃ (keepPre (keepPre (keepPre k₁₃))))
  have pm : p % q = 1 := r0₃.mp (beq_iff_eq.mp hb₃)
  -- The P space.
  refine WP.seq (WP.mono (setupP_ok hL hs₃ hr₃ (hk.keep k₁₃.2.1 k₁₃.2.2)
      (by rw [(vals K₃).1]; omega) (by rw [(vals K₃).1]; exact hpo))
    fun t₄ ⟨⟨ip₄, p0₄, ptop₄, inv₄, _, p24₄, pb₄⟩, k₄⟩ => ?_)
  rw [(vals K₃).1] at p0₄ p24₄
  have B₄ : Body L t₃.mem t₄.mem := pb₄.body hL
  have K₄ := K₃.trans (Kept.ofBody hL B₄)
  have k₁₄ := k₁₃.trans k₄
  have hs₄ : ScrL t₄ L := hs.congr k₁₄.2.2
  have hr₄ := hr₃.keep k₄ B₄
  have hk₄ := hk.keep k₁₄.2.1 k₁₄.2.2
  -- `Checked` before g's check.
  have C₄ : Checked s t₄ L key sig d := ⟨ip₄, hs₄, hr₄, (by rw [hP]; exact p0₄), ptop₄, inv₄,
    (by rw [hP]; exact p24₄), (by rw [pb₄.arrQ hL, hQ']; exact q0₃), (by rw [pb₄.qtop hL]; exact qtop₃),
    (by rw [B₄.word (by decide), hQ']; exact w₃)⟩
  -- g.
  refine WP.seq (WP.seq (WP.mono (ptrG_ok hs₄ hL hr₄) fun t₅ ⟨⟨a7, a8, m₅⟩, k₅⟩ => ?_))
  have K₅ : Kept L s.mem t₅.mem := by rw [m₅]; exact K₄
  have hk₅ := hk₄.keep k₅.2.1 k₅.2.2
  have C₅ : Checked s t₅ L key sig d := C₄.elem hL k₅ (by decide) (k₅.gpr (by decide)) (ip₄.keep k₅)
    (by rw [m₅]; exact Outside.refl _ _ _ _)
  refine WP.mono (checkElem_ok hL C₅.scr C₅.regs C₅.inp hk₅
      (hk₅.sub (o := L.pl + L.ql) (k := L.pl) (by omega)) a7 a8 (C₅.p0.trans hP) (by omega) hpo C₅.inv
      (by rw [C₅.p24, hP]))
    fun t₆ ⟨⟨ip₆, r0₆, o₆, t1₆⟩, k₆⟩ => ?_
  have eg : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₅.mem (off key (L.pl + L.ql)) L.pl) = g := (vals K₅).2.2
  rw [eg, (vals K₅).2.1] at r0₆
  have C₆ : Checked s t₆ L key sig d := C₅.elem hL k₆ (by decide) t1₆ ip₆ o₆
  have K₆ := K₅.trans (Kept.ofBody hL (p_arrays_body hL o₆))
  have k₁₆ := (k₁₄.trans k₅).trans k₆
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb₆ => ?_) (fun hb₆ => hfail t₆ (fun hK => by
      have H := hPar.mp hK
      rw [r0₆.mpr ⟨H.2.1.1, H.2.1.2, H.2.2.2⟩] at hb₆
      exact absurd hb₆ (by decide)) K₆ C₆.regs C₆.scr k₁₆)
  have hg := r0₆.mp (beq_iff_eq.mp hb₆)
  -- `rest`.
  have hok : ParamsOk s.mem L key := hPar.mpr ⟨⟨hSz, hqo, hpo⟩, ⟨hg.1, hg.2.1⟩,
    (pmod_iff (by omega) (by omega)).mpr pm, hg.2.2⟩
  exact hrest t₆ hok C₆ K₆ k₁₆

theorem checkKey_ok {s : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, KeyOk s.mem L key → Checked s t L key sig d → Kept L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ KeyOk s.mem L key → Kept L s.mem t.mem → Regs t L key sig → ScrL t L →
      Keep ckRegs s t → WP isa fail t Q) :
    WP isa (checkKey rest fail) s Q := by
  unfold checkKey
  refine checkParams_ok hL hs hr hlen hd (hk.take (by omega)) (fun t hP hc hb kc => ?_)
    (fun t hn hb hrt hst kc => hfail t (fun hK => hn (keyOk_iff.mp hK).1) hb hrt hst (keepPre (keepPre kc)))
  have hpo : pOf s.mem L key % 2 = 1 := hP.1.2.2
  have hp2 : 2 ≤ pOf s.mem L key := (VG.Proof.Dsa.supported_bounds hP.1.1).1
  unfold andThen
  refine WP.seq (WP.seq (WP.mono (ptrY_ok hc.scr hL hc.regs) fun t₇ ⟨⟨b7, b8, m₇⟩, k₇⟩ => ?_))
  have k₀₇ := kc.trans k₇
  have hk₇ := hk.keep k₀₇.2.1 k₀₇.2.2
  have C₇ : Checked s t₇ L key sig d := hc.elem hL k₇ (by decide) (k₇.gpr (by decide)) (hc.inp.keep k₇)
    (by rw [m₇]; exact Outside.refl _ _ _ _)
  refine WP.mono (checkElem_ok hL C₇.scr C₇.regs C₇.inp (hk₇.take (by omega))
      (hk₇.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)) b7 b8 C₇.p0 hp2 hpo C₇.inv C₇.p24)
    fun t₈ ⟨⟨ip₈, r0₈, o₈, t1₈⟩, k₈⟩ => ?_
  have K₇ : Kept L s.mem t₇.mem := by rw [m₇]; exact hb
  have eq₇ := (params_kept (hk.take (by omega)) K₇).2.1
  have ey : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₇.mem (off key (2 * L.pl + L.ql)) L.pl) = yOf s.mem L key :=
    y_kept hk K₇
  rw [ey, eq₇] at r0₈
  have C₈ : Checked s t₈ L key sig d := C₇.elem hL k₈ (by decide) t1₈ ip₈ o₈
  have K₈ := K₇.trans (Kept.ofBody hL (p_arrays_body hL o₈))
  have k₀₈ := k₀₇.trans k₈
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb₈ => ?_) (fun hb₈ => hfail t₈ (fun hK => by
      have H := (keyOk_iff.mp hK).2
      rw [r0₈.mpr ⟨H.1.1, H.1.2, H.2⟩] at hb₈
      exact absurd hb₈ (by decide)) K₈ C₈.regs C₈.scr k₀₈)
  have hy := r0₈.mp (beq_iff_eq.mp hb₈)
  exact hrest t₈ (keyOk_iff.mpr ⟨hP, ⟨hy.1, hy.2.1⟩, hy.2.2⟩) C₈ K₈ k₀₈

end VG.Proof.Dsa.RISCV64
