import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish

/-!
# ECDSA on 32-bit ARM: the setup and the tables of bits

The first stage of `Cfg.sign` (`stage₁`): the setup and the tables of bits
of `k`, `p - 2` and `n - 2`, and what the later stages share. None of it
needs the group law, which only the proofs of the results (`Main.lean`)
import.
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)

variable {c : Cfg} {A : Args}

/-- The arguments' numbers. -/
abbrev kv (c : Cfg) (A : Args) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.k) (8 * c.n))
abbrev dv (c : Cfg) (A : Args) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.d) (8 * c.n))
abbrev ev (c : Cfg) (A : Args) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.e) (8 * c.n))

/-- The registers the stages may change. -/
abbrev work : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem clob_work : ∀ r ∈ clob, r ∈ work := by decide
theorem powClob_work : ∀ r ∈ powClob, r ∈ work := by decide

/-- What the stages keep: the working space and `scratch`, `sp`, the
regions, `out` in `lr`, the constants and the saved registers; they write
only in `scratch`. -/
structure Keep (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  rest : Rest (.lr :: work) s₀ s
  lr : s.gpr .lr = s₀.gpr .r0
  fixed : Fixed c base s₀.gpr s.mem
  whole : Unch base [(0, 8192)] s₀.mem s.mem

/-- After the setup and the tables. -/
structure St₁ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  flag : flagW c base s = BitVec.allOnes 32
  t₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if (kv c A s₀).testBit t then 1 else 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  /-- The argument registers, which the setup and the tables leave. -/
  args : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s.gpr r = s₀.gpr r

/-- The setup, then the three tables. -/
theorem stage₁ (hc : CfgOk c) {s₀ : State} (hp : SetupPre c A s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, St₁ c A s₀ (scBase A s₀) s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith A)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  refine WP.seq (WP.mono (setup_ok hc hp) fun s₁ P => ?_)
  have hn := P.scr.nowrap
  have hc' : ∀ ix ∈ c.consts, sv c (scBase A s₀) s₁ ix.1 = ix.2 := P.consts
  have fx : Fixed c (scBase A s₀) s₀.gpr s₁.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved⟩
  -- The table of `k`.
  refine WP.seq (WP.mono (tbl_bits_ok hc P.scr P.far (i := K) (j := 0) (by decide) (by decide))
    fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  have hs₂ := P.scr.of_rest k₂ (by decide)
  have hf₂ := P.far.of_rest k₂
  have u₂ := O₂.unch
  have v₂ : ∀ {i}, i < 45 → sv c (scBase A s₀) s₂ i = sv c (scBase A s₀) s₁ i := fun hi =>
    sv_unch u₂ h7 hn hi (apart_tbl hi 0)
  -- The table of `p - 2`.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs₂ hf₂ (i := EXPP) (j := 1) (by decide) (by decide))
    fun s₃ ⟨b₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_rest k₃ (by decide)
  have hf₃ := hf₂.of_rest k₃
  have u₃ := O₃.unch
  have v₃ : ∀ {i}, i < 45 → sv c (scBase A s₀) s₃ i = sv c (scBase A s₀) s₁ i := fun hi =>
    (sv_unch u₃ h7 hn hi (apart_tbl hi 1)).trans (v₂ hi)
  -- The table of `n - 2`.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs₃ hf₃ (i := EXPN) (j := 2) (by decide) (by decide))
    fun s₄ ⟨b₄, k₄, O₄⟩ => h s₄ ?_)
  have u₄ := O₄.unch
  have v₄ : ∀ {i}, i < 45 → sv c (scBase A s₀) s₄ i = sv c (scBase A s₀) s₁ i := fun hi =>
    (sv_unch u₄ h7 hn hi (apart_tbl hi 2)).trans (v₃ hi)
  have hk : (kv c A s₀) = sv c (scBase A s₀) s₁ K := P.k.symm
  have hp2 : c.C.p - 2 = sv c (scBase A s₀) s₁ EXPP := (hc' (EXPP, c.C.p - 2) (by simp [Cfg.consts])).symm
  have hn2 : c.C.n - 2 = sv c (scBase A s₀) s₁ EXPN := (hc' (EXPN, c.C.n - 2) (by simp [Cfg.consts])).symm
  have K₂₄ : Rest work s₁ s₄ :=
    (k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  have A₂₄ : Rest [.r4, .r5, .r7, .r11] s₁ s₄ := k₂.trans (k₃.trans k₄)
  refine ⟨⟨hs₃.of_rest k₄ (by decide), hf₃.of_rest k₄, (P.keep.mono (by decide)).trans (K₂₄.mono (by simp)),
    by rw [K₂₄.gpr _ (by decide), P.lr], ?_, ?_⟩,
    by rw [v₄ (by decide), P.k], by rw [v₄ (by decide), P.d], by rw [v₄ (by decide), P.e],
    by rw [v₄ (by decide)]; exact hc' (RX, 0) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RZ, 0) (by simp [Cfg.consts]), ?_, ?_, ?_, ?_, ?_⟩
  · exact (fx.unch h7 hn (fixedOk_tbl 0) u₂ |>.unch h7 hn (fixedOk_tbl 1) u₃).unch h7 hn (fixedOk_tbl 2) u₄
  · intro x hx
    have hx' : 8192 ≤ ofs (scBase A s₀) x := by have := hx _ (List.mem_singleton_self _); omega
    rw [O₄ x (Or.inr (by have := bitsAt_le c h7 (j := 2) (by decide); omega)),
      O₃ x (Or.inr (by have := bitsAt_le c h7 (j := 1) (by decide); omega)),
      O₂ x (Or.inr (by have := bitsAt_le c h7 (j := 0) (by decide); omega)),
      P.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact Or.inr (by dsimp only [size]; omega)]
  · have hF := sl_le c h7 (i := FLAG) (by decide)
    have ap : ∀ j, ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
      fun j w hw => by
        rw [List.mem_singleton.mp hw]
        have := sl_below_bits c (i := FLAG) (by decide) j 0
        exact Or.inl (by dsimp only; omega)
    rw [flagW, Unch.readW32 u₄ (ap 2) (by omega), Unch.readW32 u₃ (ap 1) (by omega),
      Unch.readW32 u₂ (ap 0) (by omega), ← flagW, P.flag]
  · intro t ht
    rw [tbl_unch u₄ h7 (j := 0) (by decide) ht (tbl_apart_tbl (by decide) ht),
      tbl_unch u₃ h7 (j := 0) (by decide) ht (tbl_apart_tbl (by decide) ht), b₂ t ht, hk]
  · intro t ht
    rw [tbl_unch u₄ h7 (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht), b₃ t ht, hp2,
      ← v₂ (by decide)]
  · intro t ht
    rw [b₄ t ht, hn2, ← v₃ (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [A₂₄.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      P.keep.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]

theorem toM_cmont (hc : CfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

theorem mul_zero_pt (P : Point c.C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

theorem ladWx_eq (c : Cfg) : ladWx c.ladderCfg c.wk = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] ++ [(c.wk, accLen c.MP')] := rfl

theorem powWxP_eq (c : Cfg) : powWx c.powP c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, accLen c.MP')] := rfl
theorem powWxN_eq (c : Cfg) : powWx c.powN c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, accLen c.MN')] := rfl

theorem accLen_MP' (c : Cfg) : accLen c.MP' = 32 * c.n + 8 := accLen_eq _
theorem accLen_MN' (c : Cfg) : accLen c.MN' = 32 * c.n + 8 := accLen_eq _

/-- The flag word apart from numbered slots and the accumulator. -/
theorem flag_unch {base : Addr} {l : List Nat} {m m' : Mem}
    (hu : Unch base (slW c l ++ [(c.wk, 32 * c.n + 8)]) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega)
  rcases List.mem_append.mp hw with hw | hw
  · rcases apart_slW (c := c) hl w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  · rcases apart_wk (c := c) (i := FLAG) (by decide) w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h

/-- A stage writes in `scratch` only. -/
theorem whole_of' {base : Addr} {W : List (Nat × Nat)} {m₀ m m' : Mem} (h₀ : Unch base [(0, 8192)] m₀ m)
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) : Unch base [(0, 8192)] m₀ m' := fun x hx => by
  have h := hx (0, 8192) (List.mem_singleton_self _)
  have hx' : 8192 ≤ ofs base x := by dsimp only at h; omega
  rw [hu x (fun w hw => Or.inr (by have := hW w hw; omega)), h₀ x hx]

/-- A stage writes in the working space only. -/
theorem whole_of {base : Addr} {W : List (Nat × Nat)} {m₀ m m' : Mem} (h₀ : Unch base [(0, 8192)] m₀ m)
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, 8192)] m₀ m' :=
  whole_of' h₀ hu fun w hw => by have := hW w hw; dsimp only [size] at this; omega

/-- A hash of `8 n` bytes is its number. -/
theorem hashToInt_eq (hc : CfgOk c) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q (8 * c.n)) =
      ofBytes (Spec.Ecdsa.bytesAt m q (8 * c.n)) := by
  have := hc.hash
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt,
    show 8 * (8 * c.n) ≤ Spec.Ecdsa.nBits c.C by omega, ite_true]

end VG.Proof.Ecdsa.Arm
