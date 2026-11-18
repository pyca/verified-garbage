module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ECDH on PPC64LE: the windows, then the power, for every curve

What `Proof/Ecdh/PPC64LE/<Curve>/Verified.lean` needs of a curve whose
`[d]P` is by windows (`Proof/Ecdsa/PPC64LE/WindowAll.lean`), once for every
configuration:

* `Win.pow_ok`: a multiplication that writes what the windows write
  (`WAll.mulW`) and leaves `R` reduced and representing `[k]P`, then
  `Z^(p-2)` by its addition chain, leave what ECDH's last stage needs
  (`LadPost`), as `ladPowWith_ok` (`Proof/Ecdsa/PPC64LE/LadPow.lean`) is
  for the ladder's ranges: the windows' ranges are apart from the slots the
  ladder does not write, the flag and the table of `n - 2`;
* `Win.mulPowOk`: the windows of a kit from `R = O` (`WAll.Kit.mulP`) meet
  `MulPowOk`, for `b`'s constant at ECDH's slot (`a = -3`) or `3 b` at the
  signature's (any `a`), and a scalar of no more bits than the windows'.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.Win

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE

variable {c : Cfg}

/-- A slot the ladder does not write is apart from what the windows write. -/
theorem apart_mulW (h7 : c.n < 10) (E : Nat) {i : Nat} (hi : i < 45) (hr : i ∉ ACC :: PT :: ladIx) :
    ∀ w ∈ WAll.mulW c E, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  have hi' := (by decide : ∀ i < 45, i ∉ ACC :: PT :: ladIx → i < 14 ∨ 29 ≤ i) i hi hr
  have ho := sl_below_own c h7 hi
  rw [Proof.Ecdsa.PPC64LE.own_eq] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hi' with h | h
  · have := sl_lt c h
    rw [sl_eq c 14] at this
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega_using [this, ho]
  · have : c.sl 29 ≤ c.sl i := by
      rw [sl_eq, sl_eq]
      have := Nat.mul_le_mul_left (8 * c.n) h
      omega_using [this]
    rw [sl_eq c 29] at this
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega_using [this, ho]

/-- A multiplication on the windows' ranges that leaves `R` reduced and
representing `[k]P`, then `Z^(p-2)`. -/
theorem pow_ok (hc : CfgOk c) {E : Nat} (hWs : ∀ w ∈ WAll.mulW c E, w.1 + w.2 ≤ size) {s₀ : State} {base : Addr}
    {s : State} (S : Keep c s₀ base s) {k : Nat} {P : Point c.C} {generator : Prog isa}
    (hMul : WP isa generator s fun s' => Rk powClob s s' ∧ Unch base (WAll.mulW c E) s.mem s'.mem ∧
      WAll.PtOk c base s' (Window.Cfg.rPt c) (mul k P))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', LadPost c s₀ base k P s s' → WP isa rest s' Q) :
    WP isa (.seq generator (.seq c.invP rest)) s Q := by
  have h7 := hc.n10
  have n1 := hc.n0
  have hn := S.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono hMul fun s₅ ⟨K₅, U₅, R₅⟩ => ?_)
  have hW₅ : FixedOk c (WAll.mulW c E) := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [sl_eq c 12]
    rcases hw with rfl | rfl | rfl <;> exact Or.inr (by simp only; omega_using [h7])
  have K₅' : Keep c s₀ base s₅ := S.step h7 K₅ (hU := U₅) (hW := hW₅) (hWs := hWs)
  have e₅ : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s₅ i = sv c base s i := fun hi hr =>
    sv_unch U₅ h7 hn hi (apart_mulW h7 E hi hr)
  have tA₅ : ∀ t < 64 * c.n, ∀ w ∈ WAll.mulW c E,
      bitsAt c.n 2 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 2 + t := by
    intro t ht w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [bitsAt_eq]
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega_using [ht, h7]
  have lx₅ : sv c base s₅ RX < c.C.p := R₅.x
  have ly₅ : sv c base s₅ RY < c.C.p := R₅.y
  have lz₅ : sv c base s₅ RZ < c.C.p := R₅.z
  refine WP.seq (WP.mono (chainPow_ok (P := c.chainP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc)
    (chainLayP hc) hpR K₅'.ws lz₅ hc.chainP) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [chainWP_eq] at U₆
  have K₆' : Keep c s₀ base s₆ := K₅'.step h7 K₆ (hU := U₆) (hW := fixedOk_chainW h7) (hWs := chainW_le h7)
  have e₆ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₆ i = sv c base s₅ i := fun hi hr ht =>
    sv_unch U₆ h7 hn hi (apart_chainW h7 hi hr ht)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have apF₅ : ∀ w ∈ WAll.mulW c E, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_mulW h7 E (i := FLAG) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_using [h, n1])
    · exact Or.inr h
  have apF₆ : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl DX, 9 * (8 * c.n)), (Mont.own c.n, 64 * c.n)],
      c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_chainW h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_using [h, n1])
    · exact Or.inr h
  have tR : ∀ i ∈ [RX, RY, RZ], Point.tmv c.C c.n base s₆ (c.sl i) = Point.tmv c.C c.n base s₅ (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₆ i) = toM _ _ (sv c base s₅ i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₆ (by decide) (by decide) (by decide)]
  refine ⟨K₆', fun hi hl => ?_,
    by rw [flagW, U₆.word apF₆ (by omega_using [hF, hn]), U₅.word apF₅ (by omega_using [hF, hn]), ← flagW], ?_,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact R₅.rep,
    by rw [e₆ (by decide) (by decide) (by decide)]; exact lx₅,
    by rw [e₆ (by decide) (by decide) (by decide)]; exact ly₅,
    by rw [e₆ (by decide) (by decide) (by decide)]; exact lz₅, lt₆, ?_⟩
  · rw [e₆ hi (by intro h; subst h; simp at hl)
      ((by decide : ∀ i < 45, i ∉ ACC :: PT :: ladIx → i < DX ∨ T2 < i) _ hi hl), e₅ hi hl]
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_chainW h7 2 t),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tA₅ t ht)]
  · rw [tR RZ (by simp)]; exact v₆

/-- The windows' ranges are in the working space. -/
theorem mulW_le (K : WAll.Kit c) : ∀ w ∈ WAll.mulW c K.E, w.1 + w.2 ≤ size := by
  have h7 := K.ok.n10
  have tf := K.tf
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> (simp only [size]; omega_using [h7, tf])

/-- The windows of a kit from `R = O`, then the addition chain, meet
`MulPowOk`: for `b` at ECDH's slot or `3 b` at the signature's, as the kit's
arithmetic reads it, and a scalar of no more bits than the windows'. -/
theorem mulPowOk (K : WAll.Kit c) (hb : (K.bs = BP ∧ K.bK = c.C.b) ∨ (K.bs = B3P ∧ K.bK = 3 * c.C.b))
    (hnw : 8 * c.C.len ≤ K.wb * K.nw) (hL : Law c.C) (s₀ : State) : MulPowOk c s₀ K.mulP := by
  intro base s S hrx hry hrz _ ht₀ _ hbp P hP hG hlx hly rest Q h
  have F' := S.fixed
  have hkc : WAll.KC c K.bs K.bK base s := by
    refine ⟨F'.ap, ?_, F'.zero, F'.onep⟩
    rcases hb with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e, e']; exact hbp
    · rw [e, e']; exact F'.b3p
  exact pow_ok K.ok (mulW_le K) S (WAll.mul_ok K hL ⟨S.ws, hkc,
    ⟨hG, hlx, hly, lt_of_eq_of_lt F'.onep (Nat.mod_lt _ (WAll.p0 c))⟩, hP, fun t ht => ht₀ t ht,
    Nat.lt_of_lt_of_le (ofBytes_bytesAt_lt _ _ _) (Nat.pow_le_pow_right (by decide) hnw)⟩) h

end VG.Proof.Ecdh.PPC64LE.Win
