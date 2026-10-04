import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Finish

/-!
# ECDSA on x86 (32-bit): the setup and the tables of bits

The first stage of `Cfg.sign` (`stage₁`): the setup and the tables of bits
of `k`, `p - 2` and `n - 2`, and what the later stages share. None of it
needs the group law, which only the proofs of the results (`Main.lean`)
import.
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The arguments' numbers. -/
abbrev kv (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 3) (8 * c.n))
abbrev dv (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) (8 * c.n))
abbrev ev (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (8 * c.n))

/-- What the stages keep: the working space, `esp`, the regions, the
constants and the saved registers. -/
structure Keep (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fixed : Fixed c base s₀.gpr s.mem
  whole : Unch base [(0, size)] s₀.mem s.mem

/-- After the setup and the tables. -/
structure St₁ (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c s₀
  d : sv c base s D = dv c s₀
  e : sv c base s E = ev c s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  flag : flagW c base s = BitVec.allOnes 32
  t₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if (kv c s₀).testBit t then 1 else 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  gpr : ∀ r, r ∉ [.eax, .ebx, .edx, .esi, .edi] → s.gpr r = s₀.gpr r

/-- The setup, then the three tables. -/
theorem stage₁ (hc : CfgOk c) {s₀ : State} (hp : SetupPre c s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, St₁ c s₀ (ptr s₀ 4) s → WP isa rest s Q) :
    WP isa (.seq (.block c.setup) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n7
  refine WP.seq (WP.mono (setup_ok hc hp) fun s₁ P => ?_)
  have hn := P.scr.nowrap
  have hc' : ∀ ix ∈ c.consts, sv c (ptr s₀ 4) s₁ ix.1 = ix.2 := P.consts
  have fx : Fixed c (ptr s₀ 4) s₀.gpr s₁.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved⟩
  have hsep : ∀ {i : Nat}, i < 45 → ∀ j, c.sl i + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + 64 * c.n ≤ c.sl i :=
    fun hi j => Or.inl (by have := sl_below_bits c hi j 0; omega)
  have hsz : ∀ {j}, j < 3 → bitsAt c.n j + 64 * c.n ≤ size := fun hj => bitsAt_le c h7 hj
  -- The table of `k`.
  refine WP.seq (WP.mono (bits_ok P.scr h0 (sl_le c h7 (i := K) (by decide)) (hsz (j := 0) (by decide))
    (hsep (i := K) (by decide) 0)) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  have hs₂ := P.scr.of_keeps k₂ (by decide)
  have u₂ := O₂.unch
  have v₂ : ∀ {i}, i < 45 → sv c (ptr s₀ 4) s₂ i = sv c (ptr s₀ 4) s₁ i := fun hi =>
    sv_unch u₂ h7 hn hi (apart_tbl hi 0)
  -- The table of `p - 2`.
  refine WP.seq (WP.mono (bits_ok hs₂ h0 (sl_le c h7 (i := EXPP) (by decide)) (hsz (j := 1) (by decide))
    (hsep (i := EXPP) (by decide) 1)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have u₃ := O₃.unch
  have v₃ : ∀ {i}, i < 45 → sv c (ptr s₀ 4) s₃ i = sv c (ptr s₀ 4) s₁ i := fun hi =>
    (sv_unch u₃ h7 hn hi (apart_tbl hi 1)).trans (v₂ hi)
  -- The table of `n - 2`.
  refine WP.seq (WP.mono (bits_ok hs₃ h0 (sl_le c h7 (i := EXPN) (by decide)) (hsz (j := 2) (by decide))
    (hsep (i := EXPN) (by decide) 2)) fun s₄ ⟨b₄, k₄, O₄⟩ => h s₄ ?_)
  have u₄ := O₄.unch
  have v₄ : ∀ {i}, i < 45 → sv c (ptr s₀ 4) s₄ i = sv c (ptr s₀ 4) s₁ i := fun hi =>
    (sv_unch u₄ h7 hn hi (apart_tbl hi 2)).trans (v₃ hi)
  have hk : (kv c s₀) = sv c (ptr s₀ 4) s₁ K := P.k.symm
  have hp2 : c.C.p - 2 = sv c (ptr s₀ 4) s₁ EXPP := (hc' (EXPP, c.C.p - 2) (by simp [Cfg.consts])).symm
  have hn2 : c.C.n - 2 = sv c (ptr s₀ 4) s₁ EXPN := (hc' (EXPN, c.C.n - 2) (by simp [Cfg.consts])).symm
  have K₄ : Keeps [.eax, .ebx, .edx, .esi, .edi] s₀ s₄ :=
    (((P.keep.mono (by decide)).widen k₂).widen k₃).widen k₄
  refine ⟨⟨hs₃.of_keeps k₄ (by decide), K₄.1 _ (by decide), K₄.2.1, K₄.2.2, ?_, ?_⟩,
    by rw [v₄ (by decide), P.k], by rw [v₄ (by decide), P.d], by rw [v₄ (by decide), P.e],
    by rw [v₄ (by decide)]; exact hc' (RX, 0) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RZ, 0) (by simp [Cfg.consts]), ?_, ?_, ?_, ?_, K₄.1⟩
  · exact (fx.unch h7 hn (fixedOk_tbl 0) u₂ |>.unch h7 hn (fixedOk_tbl 1) u₃).unch h7 hn (fixedOk_tbl 2) u₄
  · intro x hx
    have hx' : size ≤ ofs (ptr s₀ 4) x := by have := hx _ (List.mem_singleton_self _); omega
    rw [O₄ x (Or.inr (by have := bitsAt_le c h7 (j := 2) (by decide); omega)),
      O₃ x (Or.inr (by have := bitsAt_le c h7 (j := 1) (by decide); omega)),
      O₂ x (Or.inr (by have := bitsAt_le c h7 (j := 0) (by decide); omega)),
      P.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact Or.inr (by omega)]
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

theorem toM_cmont (hc : CfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

theorem mul_zero_pt (P : Point c.C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

theorem ladWx_eq (c : Cfg) : ladWx c.ladderCfg c.wk = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] ++ [(c.wk, accLen c.MP')] := rfl

theorem powWxP_eq (c : Cfg) : powWx c.powP c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, accLen c.MP')] := rfl
theorem powWxN_eq (c : Cfg) : powWx c.powN c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, accLen c.MN')] := rfl

theorem accLen_MP' (c : Cfg) : accLen c.MP' = 16 * c.n + 4 := accLen_eq _
theorem accLen_MN' (c : Cfg) : accLen c.MN' = 16 * c.n + 4 := accLen_eq _

/-- The flag word apart from numbered slots and the accumulator. -/
theorem flag_unch {base : Addr} {l : List Nat} {m m' : Mem}
    (hu : Unch base (slW c l ++ [(c.wk, 16 * c.n + 4)]) m m')
    (h7 : c.n < 7) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
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

/-- A stage writes in the working space only. -/
theorem whole_of {base : Addr} {W : List (Nat × Nat)} {m₀ m m' : Mem} (h₀ : Unch base [(0, size)] m₀ m)
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, size)] m₀ m' := fun x hx => by
  have h := hx (0, size) (List.mem_singleton_self _)
  have hx' : size ≤ ofs base x := by dsimp only at h; omega
  rw [hu x (fun w hw => Or.inr (by have := hW w hw; omega)), h₀ x hx]

/-- A hash of `8 n` bytes is its number. -/
theorem hashToInt_eq (hc : CfgOk c) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q (8 * c.n)) =
      ofBytes (Spec.Ecdsa.bytesAt m q (8 * c.n)) := by
  have := hc.hash
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt,
    show 8 * (8 * c.n) ≤ Spec.Ecdsa.nBits c.C by omega, ite_true]

end VG.Proof.Ecdsa.X86
