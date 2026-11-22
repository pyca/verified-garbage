module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.CallOf
import VerifiedGarbage.Proof.Mont.PPC64LE.Row

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
* `Win.mulPowOk`: the windows of a kit from `R = O` (`WAll.Kit.mulP`), as
  the function both ECDH and verification call (`Cfg.winCall`, `mulCall_ok`), meet
  `MulPowOk`, for `b`'s constant at ECDH's slot (`a = -3`) or `3 b` at the
  signature's (any `a`), and a scalar of no more bits than the windows'.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.Win

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont

variable {c : Cfg}

/-- What the windows' function writes: the windows' ranges, and where it
keeps `r31` and `lr` (`Cfg.winFn`, past the numbered slots). -/
abbrev mulWS (c : Cfg) (E : Nat) : List (Nat × Nat) := (c.sl nslots, 16) :: WAll.mulW c E

/-- A slot the ladder does not write is apart from what the windows write. -/
theorem apart_mulW (h7 : c.n < 10) (E : Nat) {i : Nat} (hi : i < 45) (hr : i ∉ ACC :: PT :: ladIx) :
    ∀ w ∈ mulWS c E, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact .inl (sl_lt c hi)
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

/-- The windows of a kit as a function (`Cfg.winCall`): `mul_ok`, with `r31`
and `lr` kept at `c.sl 45` around them. -/
theorem mulCall_ok (K : WAll.Kit c) (hL : Law c.C) {base : Addr} {s : State} {Q : Point c.C} {k : Nat}
    (hp : WAll.MPre K base s Q k) :
    WP isa (c.winCall K.mulP) s fun s' => Rk powClob s s' ∧ Unch base (mulWS c K.E) s.mem s'.mem ∧
      WAll.PtOk c base s' (Window.Cfg.rPt c) (mul k Q) := by
  have h7 := K.ok.n10
  obtain hown := save_le_own (c := c) h7
  obtain h45 := sl_eq c 45
  obtain hO8 := own_eq c.n
  have hn := hp.ws.nowrap
  obtain hu : WsReg s.callEntry base :=
    ⟨by rw [State.callEntry_gpr _ (by decide)]; exact hp.ws.r3, by rw [State.callEntry_wr]; exact hp.ws.wr, hn⟩
  refine WP.callOf ?_
  rw [Cfg.winFn]
  -- `r31` and `lr` saved.
  refine WP.seq (WP.mono (saves_ok h7 hu) fun s₂ ⟨K₂, m₂⟩ => ?_)
  obtain hw₂ := hu.of_kp K₂
  obtain O₂ : Unch base [(c.sl 45, 16)] s.mem s₂.mem := by
    rw [m₂, State.callEntry_mem]
    refine ((writeW_outside s.mem base (s.callEntry.gpr .r31) (d := c.sl 45) (by omega_arith)).unch.trans
      (writeW_outside _ base s.callEntry.lr (d := c.sl 45 + 8) (by omega_arith)).unch).cover fun w hw => ?_
    refine ⟨(c.sl 45, 16), List.mem_singleton_self _, ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl <;> exact ⟨by dsimp only; omega_arith, by dsimp only; omega_arith⟩
  obtain e₂ : ∀ {i}, i < 45 → wordsVal s₂.mem base (c.sl i) c.n = wordsVal s.mem base (c.sl i) c.n := fun hi =>
    O₂.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact .inl (sl_lt c hi)) (by have := sl_le c h7 hi; omega_arith)
  obtain hp₂ : WAll.MPre K base s₂ Q k := by
    refine ⟨hw₂, hp.kc.of_eq fun d hd => ?_, hp.g.of_eq ?_ ?_ ?_, hp.on, WAll.Bits.of_unch (WAll.n_le K.ok) hp.bits O₂ ?_, hp.lt⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      have hbs : K.bs < 45 := by rcases K.bs_cases with h | h <;> rw [h] <;> decide
      rcases hd with rfl | rfl | rfl | rfl
      · exact e₂ (i := 6) (by decide)
      · exact e₂ hbs
      · exact e₂ (i := 3) (by decide)
      · exact e₂ (i := 5) (by decide)
    · exact e₂ (i := Impl.Ecdh.PPC64LE.PX) (by decide)
    · exact e₂ (i := Impl.Ecdh.PPC64LE.PY) (by decide)
    · exact e₂ (i := ONEP) (by decide)
    · intro w hw; rw [List.mem_singleton.mp hw]; exact .inl (by dsimp only; omega_arith)
  -- The windows.
  refine WP.seq (WP.mono (WAll.mul_ok K hL hp₂) fun s₃ ⟨K₃, U₃, R₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rk K₃
  obtain apS : ∀ {d : Nat}, c.sl 45 ≤ d → d + 8 ≤ c.sl 45 + 16 → ∀ w ∈ WAll.mulW c K.E, d + 8 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
    intro d h1 h2 w hw
    have tf := K.tf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega_arith
  obtain w31 : word s₃.mem base (c.sl 45) = s.gpr .r31 := by
    rw [U₃.word (apS (Nat.le_refl _) (by omega_arith)) (by omega_arith), m₂,
      word_writeW_ne _ (by omega_arith) (by omega_arith) (by omega_arith), word_writeW_self,
      State.callEntry_gpr _ (by decide)]
  obtain wlr : word s₃.mem base (c.sl 45 + 8) = s.callEntry.lr := by
    rw [U₃.word (apS (by omega_arith) (by omega_arith)) (by omega_arith), m₂, word_writeW_self]
  -- `lr` and `r31` restored.
  refine WP.mono (loads_ok h7 hw₃) fun s₄ ⟨m₄, lr₄, r31₄, K₄⟩ => ⟨by rw [lr₄, wlr], ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [K₄.rd, K₃.rd, K₂.rd]; rfl, by rw [K₄.wr, K₃.wr, K₂.wr]; rfl,
      by rw [K₄.sp, K₃.sp, K₂.sp]; rfl⟩
    have h0 : r ∉ [Reg.r0, .r31] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    have hl : r ∉ linkRegs := fun h => hr (by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide)
    rw [K₄.gpr r h0, K₃.gpr r hr, K₂.gpr r (fun h => h0 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; exact .inl h)), State.callEntry_gpr _ hl]
  · rw [m₄]
    exact ((show Unch base [(c.sl 45, 16)] s.mem s₂.mem from O₂).trans U₃).mono fun w hw => by
      simp only [mulWS, nslots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      exact hw
  · exact R₃.of_eq (by rw [m₄]) (by rw [m₄]) (by rw [m₄])

/-- A multiplication on the windows' ranges that leaves `R` reduced and
representing `[k]P`, then `Z^(p-2)`. -/
theorem pow_ok (hc : CfgOk c) {E : Nat} (hWs : ∀ w ∈ mulWS c E, w.1 + w.2 ≤ size) {s₀ : State} {base : Addr}
    {s : State} (S : Keep c s₀ base s) {k : Nat} {P : Point c.C} {generator : Prog isa}
    (hMul : WP isa generator s fun s' => Rk powClob s s' ∧ Unch base (mulWS c E) s.mem s'.mem ∧
      WAll.PtOk c base s' (Window.Cfg.rPt c) (mul k P))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', LadPost c s₀ base k P s s' → WP isa rest s' Q) :
    WP isa (.seq generator (.seq c.invP rest)) s Q := by
  have h7 := hc.n10
  have n1 := hc.n0
  have hn := S.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono hMul fun s₅ ⟨K₅, U₅, R₅⟩ => ?_)
  have hW₅ : FixedOk c (mulWS c E) := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [sl_eq c 12]
    rcases hw with rfl | rfl | rfl | rfl <;> exact Or.inr (by simp only [sl_eq, nslots]; omega_using [h7])
  have K₅' : Keep c s₀ base s₅ := S.step h7 K₅ (hU := U₅) (hW := hW₅) (hWs := hWs)
  have e₅ : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s₅ i = sv c base s i := fun hi hr =>
    sv_unch U₅ h7 hn hi (apart_mulW h7 E hi hr)
  have tA₅ : ∀ t < 64 * c.n, ∀ w ∈ mulWS c E,
      bitsAt c.n 2 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 2 + t := by
    intro t ht w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [bitsAt_eq]
    rcases hw with rfl | rfl | rfl | rfl <;> simp only [sl_eq, nslots] <;> omega_using [ht, h7]
  have lx₅ : sv c base s₅ RX < c.C.p := R₅.x
  have ly₅ : sv c base s₅ RY < c.C.p := R₅.y
  have lz₅ : sv c base s₅ RZ < c.C.p := R₅.z
  refine WP.seq (WP.mono (chainCallC_ok h7 chainWP_eq (i := RZ) rfl (by decide) (P := c.chainP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc)
    (chainLayP hc) hpR K₅'.ws lz₅ hc.chainP) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  have K₆' : Keep c s₀ base s₆ := K₅'.step h7 K₆ (hU := U₆) (hW := fixedOk_chainWS h7) (hWs := chainWS_le h7)
  have e₆ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₆ i = sv c base s₅ i := fun hi hr ht =>
    sv_unch U₆ h7 hn hi (apart_chainWS h7 hi hr ht)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have apF₅ : ∀ w ∈ mulWS c E, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_mulW h7 E (i := FLAG) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_using [h, n1])
    · exact Or.inr h
  have apF₆ : ∀ w ∈ chainWS c,
      c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_chainWS h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
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
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_chainWS h7 2 t),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tA₅ t ht)]
  · rw [tR RZ (by simp)]; exact v₆

/-- The windows' ranges, and where their function keeps `r31` and `lr`,
are in the working space. -/
theorem mulW_le (K : WAll.Kit c) : ∀ w ∈ mulWS c K.E, w.1 + w.2 ≤ size := by
  have h7 := K.ok.n10
  have tf := K.tf
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> (simp only [size, sl_eq, nslots]; omega_using [h7, tf])

/-- The windows of a kit from `R = O`, then the addition chain, meet
`MulPowOk`: for `b` at ECDH's slot or `3 b` at the signature's, as the kit's
arithmetic reads it, and a scalar of no more bits than the windows'. -/
theorem mulPowOk (K : WAll.Kit c) (hb : (K.bs = BP ∧ K.bK = c.C.b) ∨ (K.bs = B3P ∧ K.bK = 3 * c.C.b))
    (hnw : 8 * c.C.len ≤ K.wb * K.nw) (hL : Law c.C) (s₀ : State) : MulPowOk c s₀ (c.winCall K.mulP) := by
  intro base s S hrx hry hrz _ ht₀ _ hbp P hP hG hlx hly rest Q h
  have F' := S.fixed
  have hkc : WAll.KC c K.bs K.bK base s := by
    refine ⟨F'.ap, ?_, F'.zero, F'.onep⟩
    rcases hb with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e, e']; exact hbp
    · rw [e, e']; exact F'.b3p
  exact pow_ok K.ok (mulW_le K) S (mulCall_ok K hL ⟨S.ws, hkc,
    ⟨hG, hlx, hly, lt_of_eq_of_lt F'.onep (Nat.mod_lt _ (WAll.p0 c))⟩, hP, fun t ht => ht₀ t ht,
    Nat.lt_of_lt_of_le (ofBytes_bytesAt_lt _ _ _) (Nat.pow_le_pow_right (by decide) hnw)⟩) h

end VG.Proof.Ecdh.PPC64LE.Win
