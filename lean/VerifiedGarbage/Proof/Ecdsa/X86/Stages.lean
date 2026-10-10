import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays

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

variable {c : Cfg} {A : Args}

/-- The arguments' numbers, as the setup reads them (the slot `A.hs`
shifted). -/
abbrev kv (c : Cfg) (A : Args) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.k) c.C.len) >>> shAt c A.hs K
abbrev dv (c : Cfg) (A : Args) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.d) c.C.len) >>> shAt c A.hs D
abbrev ev (c : Cfg) (A : Args) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.e) c.C.len) >>> shAt c A.hs E

theorem kv_eq {s₀ : State} (h : shAt c A.hs K = 0) :
    kv c A s₀ = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.k) c.C.len) := by
  show _ >>> _ = _; rw [h, Nat.shiftRight_zero]

theorem dv_eq {s₀ : State} (h : shAt c A.hs D = 0) :
    dv c A s₀ = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.d) c.C.len) := by
  show _ >>> _ = _; rw [h, Nat.shiftRight_zero]

/-- What the stages keep: the working space, `esp`, the regions, the
constants and the saved registers; and they change memory only in the
writable regions and the stack below `esp` that the calls use. -/
structure Keep (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fixed : Fixed c base s₀.gpr s.mem
  whole : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s.mem
  sp_lo : c.stk ≤ (s₀.gpr .esp).toNat

/-- Code that keeps `esp` and uses at most `c.stk` bytes of stack changes
memory only where the stages may. -/
theorem Keep.withSp {s₀ : State} {base : Addr} {s : State} (hK : Keep c s₀ base s) {code : Prog isa}
    (hsp : SpOk code c.stk) {Q : State → Prop}
    (h : WP isa code s fun s' => Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem → Q s') :
    WP isa code s Q :=
  WP.mono (WP.spFrame hsp (by rw [hK.esp]; exact hK.sp_lo) h) fun s' ⟨q, f⟩ =>
    q (hK.whole.trans (by rw [hK.wr, hK.esp] at f; exact f))

/-- The argument holding the working space, for the ladder's calls of the
point functions, after code that changed memory only where the stages may. -/
theorem Keep.ladArg {s₀ s : State} (K : Keep c s₀ (ptr s₀ A.sc) s) (hp : SetupPre c A s₀)
    (hd : ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk], Region.Disjoint ⟨argAddr s₀ A.sc, 4⟩ r)
    (h28 : 28 ≤ c.stk) : Point.LadArg s (ptr s₀ A.sc) A.ao := by
  have hsc : A.sc ∈ A.idx := List.mem_cons_self
  have hv : s.mem.readW (argAddr s₀ A.sc) 32 = arg s₀ A.sc :=
    K.whole.readW (Region.contains_self _ _) hd (by decide)
  have he : s.gpr .edi = arg s₀ A.sc := by
    have := congrArg (BitVec.setWidth 32) K.scr.edi
    simpa only [ptr, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using this
  refine Point.LadArg.of h28 (by rw [K.esp]; exact hp.sp_lo)
    (by rw [K.esp]; have := hp.sp_fit _ hsc; simp only [Args.ao]; omega) K.scr.nowrap
    (by rw [K.esp]; exact hp.stk_sc) (by rw [K.esp, K.rd, K.wr]; exact hp.arg_in _ hsc)
    (by rw [K.esp, he]; exact hv) (by rw [K.esp]; exact hp.arg_sc _ hsc)

/-- A change only in `[q, q + n)`, one of the regions `L`. -/
theorem frame_of_outside {L : List Region} {q : Addr} {n : Nat} {m m' : Mem}
    (ho : Outside q 0 n m m') (hin : (⟨q, n⟩ : Region) ∈ L) : Frame L m m' := fun x hx => by
  have := hx _ hin; simp only [Region.Contains] at this
  exact ho x (Or.inr (by simp only [ofs]; omega))

/-- Numbered slots are in the working space. -/
theorem slW_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact sl_le c h7 (hl i hi)

theorem flag_le (h0 : 0 < c.n) (h7 : c.n < 10) : ∀ w ∈ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_le c h7 (i := FLAG) (by decide)
  dsimp only
  omega

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
  gpr : ∀ r, r ∉ [.eax, .ebx, .edx, .esi, .edi] → s.gpr r = s₀.gpr r
  /-- The setup and the tables write only the working space. -/
  ws : Outside base 0 size s₀.mem s.mem
  /-- The argument holding the working space, for the ladder's calls of the
  point functions. -/
  arg : 28 ≤ c.stk → Point.LadArg s base A.ao

/-- The setup, then the three tables. -/
theorem stage₁ (hc : CfgOk c) {s₀ : State} (hp : SetupPre c A s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, St₁ c A s₀ (ptr s₀ A.sc) s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith A)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  refine WP.seq (WP.mono (setup_ok hc hp) fun s₁ P => ?_)
  have hn := P.scr.nowrap
  have hc' : ∀ ix ∈ c.consts, sv c (ptr s₀ A.sc) s₁ ix.1 = ix.2 := P.consts
  have fx : Fixed c (ptr s₀ A.sc) s₀.gpr s₁.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved, P.table⟩
  have hsep : ∀ {i : Nat}, i < 45 → ∀ j, c.sl i + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + 64 * c.n ≤ c.sl i :=
    fun hi j => Or.inl (by have := sl_below_bits c hi j 0; omega)
  have hsz : ∀ {j}, j < 3 → bitsAt c.n j + 64 * c.n ≤ size := fun hj => bitsAt_le c h7 hj
  -- The table of `k`.
  refine WP.seq (WP.mono (bits_ok P.scr h0 (sl_le c h7 (i := K) (by decide)) (hsz (j := 0) (by decide))
    (hsep (i := K) (by decide) 0)) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  have hs₂ := P.scr.of_keeps k₂ (by decide)
  have u₂ := O₂.unch
  have v₂ : ∀ {i}, i < 45 → sv c (ptr s₀ A.sc) s₂ i = sv c (ptr s₀ A.sc) s₁ i := fun hi =>
    sv_unch u₂ h7 hn hi (apart_tbl hi 0)
  -- The table of `p - 2`.
  refine WP.seq (WP.mono (bits_ok hs₂ h0 (sl_le c h7 (i := EXPP) (by decide)) (hsz (j := 1) (by decide))
    (hsep (i := EXPP) (by decide) 1)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have u₃ := O₃.unch
  have v₃ : ∀ {i}, i < 45 → sv c (ptr s₀ A.sc) s₃ i = sv c (ptr s₀ A.sc) s₁ i := fun hi =>
    (sv_unch u₃ h7 hn hi (apart_tbl hi 1)).trans (v₂ hi)
  -- The table of `n - 2`.
  refine WP.seq (WP.mono (bits_ok hs₃ h0 (sl_le c h7 (i := EXPN) (by decide)) (hsz (j := 2) (by decide))
    (hsep (i := EXPN) (by decide) 2)) fun s₄ ⟨b₄, k₄, O₄⟩ => h s₄ ?_)
  have u₄ := O₄.unch
  have v₄ : ∀ {i}, i < 45 → sv c (ptr s₀ A.sc) s₄ i = sv c (ptr s₀ A.sc) s₁ i := fun hi =>
    (sv_unch u₄ h7 hn hi (apart_tbl hi 2)).trans (v₃ hi)
  have hk : (kv c A s₀) = sv c (ptr s₀ A.sc) s₁ K := P.k.symm
  have hp2 : c.C.p - 2 = sv c (ptr s₀ A.sc) s₁ EXPP := (hc' (EXPP, c.C.p - 2) (by simp [Cfg.consts])).symm
  have hn2 : c.C.n - 2 = sv c (ptr s₀ A.sc) s₁ EXPN := (hc' (EXPN, c.C.n - 2) (by simp [Cfg.consts])).symm
  have K₄ : Keeps [.eax, .ebx, .edx, .esi, .edi] s₀ s₄ :=
    (((P.keep.mono (by decide)).widen k₂).widen k₃).widen k₄
  have hws : Outside (ptr s₀ A.sc) 0 size s₀.mem s₄.mem := fun x hx => by
    rw [O₄ x (Or.inr (by have := bitsAt_le c h7 (j := 2) (by decide); omega)),
      O₃ x (Or.inr (by have := bitsAt_le c h7 (j := 1) (by decide); omega)),
      O₂ x (Or.inr (by have := bitsAt_le c h7 (j := 0) (by decide); omega)),
      P.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact Or.inr (by omega)]
  refine ⟨⟨hs₃.of_keeps k₄ (by decide), K₄.1 _ (by decide), K₄.2.1, K₄.2.2, ?_,
    frame_of_outside hws (List.mem_append_left _ hp.wr), hp.sp_lo⟩,
    by rw [v₄ (by decide), P.k], by rw [v₄ (by decide), P.d], by rw [v₄ (by decide), P.e],
    by rw [v₄ (by decide)]; exact hc' (RX, 0) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RZ, 0) (by simp [Cfg.consts]), ?_, ?_, ?_, ?_, K₄.1, hws, ?_⟩
  · exact (fx.unch h7 hn (fixedOk_tbl 0) u₂ |>.unch h7 hn (fixedOk_tbl 1) u₃).unch h7 hn (fixedOk_tbl 2) u₄
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
  · intro h28
    have esp₄ : s₄.gpr .esp = s₀.gpr .esp := K₄.1 _ (by decide)
    have hsc : A.sc ∈ A.idx := List.mem_cons_self
    have hs₄ := hs₃.of_keeps k₄ (by decide)
    have hv : s₄.mem.readW (argAddr s₀ A.sc) 32 = arg s₀ A.sc :=
      (frame_of_outside hws (List.mem_singleton_self _)).readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.arg_sc _ hsc) (by decide)
    have he : s₄.gpr .edi = arg s₀ A.sc := by
      have := congrArg (BitVec.setWidth 32) hs₄.edi
      simpa only [ptr, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using this
    refine Point.LadArg.of h28 (by rw [esp₄]; exact hp.sp_lo)
      (by rw [esp₄]; have := hp.sp_fit _ hsc; simp only [Args.ao]; omega) hn (by rw [esp₄]; exact hp.stk_sc)
      (by rw [esp₄, K₄.2.1, K₄.2.2]; exact hp.arg_in _ hsc) (by rw [esp₄, he]; exact hv)
      (by rw [esp₄]; exact hp.arg_sc _ hsc)

theorem toM_cmont (hc : CfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

theorem mul_zero_pt (P : Point c.C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

theorem ladWx_eq (c : Cfg) : ladWx c.ladderCfg c.wk = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] ++ wkW c := rfl

theorem powWxP_eq (c : Cfg) : powWx c.powP c.wk = slW c [ACC, PT, TMP] ++ wkW c := rfl
theorem powWxN_eq (c : Cfg) : powWx c.powN c.wk = slW c [ACC, PT, TMP] ++ wkW c := rfl

theorem accLen_MP' (c : Cfg) : accLen c.MP' = 16 * c.n + 4 := accLen_eq _
theorem accLen_MN' (c : Cfg) : accLen c.MN' = 16 * c.n + 4 := accLen_eq _

/-- The flag word apart from numbered slots and the accumulator. -/
theorem flag_unch {base : Addr} {l : List Nat} {m m' : Mem}
    (hu : Unch base (slW c l ++ wkW c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega)
  rcases List.mem_append.mp hw with hw | hw
  · rcases apart_slW (c := c) hl w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  · rcases apart_wk (c := c) (i := FLAG) (by decide) (hn := h7) w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h

/-- A change within the working space, one of the regions `L`. -/
theorem frame_of_unch {L : List Region} {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) (hin : (⟨base, size⟩ : Region) ∈ L) :
    Frame L m m' := fun x hx => by
  have hx' : size ≤ ofs base x := by
    have := hx _ hin; simp only [Region.Contains] at this; simp only [ofs]; omega
  exact hu x (fun w hw => Or.inr (by have := hW w hw; omega))

/-- A stage writes in the working space only. -/
theorem whole_of {L : List Region} {base : Addr} {W : List (Nat × Nat)} {m₀ m m' : Mem} (h₀ : Frame L m₀ m)
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) (hin : (⟨base, size⟩ : Region) ∈ L) :
    Frame L m₀ m' :=
  h₀.trans (frame_of_unch hu hW hin)

/-- A hash of `len` bytes is its number without the bits that are not
`e`'s. -/
theorem hashToInt_eq (c : Cfg) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q c.C.len) =
      ofBytes (Spec.Ecdsa.bytesAt m q c.C.len) >>> c.sh := by
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt, Cfg.sh]
  split
  · rw [show 8 * c.C.len - Spec.Ecdsa.nBits c.C = 0 by omega, Nat.shiftRight_zero]
  · rfl

end VG.Proof.Ecdsa.X86
