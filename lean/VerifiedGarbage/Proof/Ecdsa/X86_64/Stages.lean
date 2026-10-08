import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# ECDSA on x86-64: the setup and the tables of bits

The first stage of `Cfg.sign` (`stage₁`), which ECDH and the public key run
too: the setup and the tables of bits of `k`, `p - 2` and `n - 2`, and what
the later stages share. None of it needs the group law, which only the
proofs of the results (`Main.lean`) import.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

/-- The arguments' numbers. -/
abbrev kv (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rcx) c.C.len)
abbrev dv (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) c.C.len)
abbrev ev (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) c.C.len) >>> c.sh

/-- What the stages keep: the working space, `out` in `rsi`, the regions,
the constants and the saved registers. -/
structure Keep (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  rsi : s.gpr .rsi = s₀.gpr .rdi
  wr : s.wr = s₀.wr
  fixed : Fixed c base s₀.gpr s.mem

/-- After the setup and the tables. -/
structure St₁ (c : Cfg) (hs : Option Nat) (s₀ : State) (base : Addr) (s : State) : Prop
    extends Keep c s₀ base s where
  k : sv c base s K = kv c s₀
  d : sv c base s D = dv c s₀ >>> shAt c hs D
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) c.C.len) >>> shAt c hs E
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64
  t₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if (kv c s₀).testBit t then 1 else 0
  /-- The bits of `p - 2`, which only the power for more than nine words reads
  (for nine, the second table holds the products' temporary area). -/
  t₁ : ¬ c.n ≤ 9 → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) =
    if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  gpr : ∀ r, r ∉ [.rax, .rdi, .r14, .rsi, .rdx, .rbx] → s.gpr r = s₀.gpr r
  unch : Unch base [(0, size)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  syms : s.syms = s₀.syms

/-- The setup, then the three tables. -/
theorem stage₁ (hc : BaseCfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {s₀ : State} (hp : SetupPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, St₁ c hs s₀ (s₀.gpr .r8) s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith hs)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  refine WP.seq (WP.mono_syms (setup_ok hc hhs hp) fun s₁ P sy₁ => ?_)
  have hn := P.scr.nowrap
  have hc' : ∀ ix ∈ c.consts, sv c (s₀.gpr .r8) s₁ ix.1 = ix.2 := P.consts
  have fx : Fixed c (s₀.gpr .r8) s₀.gpr s₁.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved⟩
  have hsep : ∀ {i : Nat}, i < 45 → i ≠ TMP → ∀ j,
      c.sl i + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + 64 * c.n ≤ c.sl i :=
    fun hi hit j => Or.inl (by have := sl_below_bits c hi j 0 (.inl hit); omega)
  have hsz : ∀ {j}, j < 3 → bitsAt c.n j + 64 * c.n ≤ size := fun hj => bitsAt_le c h7 hj
  -- The table of `k`.
  refine WP.seq (WP.mono_syms (bits_ok P.scr h0 (by omega) (sl_le c h7 (i := K) (by decide)) (hsz (j := 0)
    (by decide)) (hsep (i := K) (by decide) (by decide) 0)) fun s₂ ⟨b₂, k₂, O₂⟩ sy₂ => ?_)
  have hs₂ := P.scr.of_keepRegs k₂ (by decide)
  have u₂ := O₂.unch
  have v₂ : ∀ {i}, i < 45 → i ≠ TMP → sv c (s₀.gpr .r8) s₂ i = sv c (s₀.gpr .r8) s₁ i := fun hi hit =>
    sv_unch u₂ h7 hn hi (apart_tbl hi 0 (.inl hit))
  -- The table of `p - 2`.
  refine WP.seq (WP.mono_syms (bits_ok hs₂ h0 (by omega) (sl_le c h7 (i := EXPP) (by decide)) (hsz (j := 1)
    (by decide)) (hsep (i := EXPP) (by decide) (by decide) 1)) fun s₃ ⟨b₃, k₃, O₃⟩ sy₃ => ?_)
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have u₃ := O₃.unch
  have v₃ : ∀ {i}, i < 45 → i ≠ TMP → sv c (s₀.gpr .r8) s₃ i = sv c (s₀.gpr .r8) s₁ i := fun hi hit =>
    (sv_unch u₃ h7 hn hi (apart_tbl hi 1 (.inl hit))).trans (v₂ hi hit)
  -- The table of `n - 2`.
  refine WP.seq (WP.mono_syms (bits_ok hs₃ h0 (by omega) (sl_le c h7 (i := EXPN) (by decide)) (hsz (j := 2)
    (by decide)) (hsep (i := EXPN) (by decide) (by decide) 2)) fun s₄ ⟨b₄, k₄, O₄⟩ sy₄ => h s₄ ?_)
  have u₄ := O₄.unch
  have v₄ : ∀ {i}, i < 45 → i ≠ TMP → sv c (s₀.gpr .r8) s₄ i = sv c (s₀.gpr .r8) s₁ i := fun hi hit =>
    (sv_unch u₄ h7 hn hi (apart_tbl hi 2 (.inl hit))).trans (v₃ hi hit)
  have hk : (kv c s₀) = sv c (s₀.gpr .r8) s₁ K := P.k.symm
  have hp2 : c.C.p - 2 = sv c (s₀.gpr .r8) s₁ EXPP := (hc' (EXPP, c.C.p - 2) (by simp [Cfg.consts])).symm
  have hn2 : c.C.n - 2 = sv c (s₀.gpr .r8) s₁ EXPN := (hc' (EXPN, c.C.n - 2) (by simp [Cfg.consts])).symm
  refine ⟨⟨hs₃.of_keepRegs k₄ (by decide), ?_, by rw [k₄.wr, k₃.wr, k₂.wr, P.keep.wr], ?_⟩,
    by rw [v₄ (by decide) (by decide), P.k], by rw [v₄ (by decide) (by decide), P.d], by rw [v₄ (by decide) (by decide), P.e],
    by rw [v₄ (by decide) (by decide)]; exact hc' (RX, 0) (by simp [Cfg.consts]),
    by rw [v₄ (by decide) (by decide)]; exact hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    by rw [v₄ (by decide) (by decide)]; exact hc' (RZ, 0) (by simp [Cfg.consts]), ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [k₄.rd, k₃.rd, k₂.rd, P.keep.rd], by rw [sy₄, sy₃, sy₂, sy₁]⟩
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), P.rsi]
  · exact (fx.unch h7 hn (fixedOk_tbl 0) u₂ |>.unch h7 hn (fixedOk_tbl 1) u₃).unch h7 hn (fixedOk_tbl 2) u₄
  · have hF := sl_le c h7 (i := FLAG) (by decide)
    have ap : ∀ j, ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
      fun j w hw => by
        rw [List.mem_singleton.mp hw]
        have := sl_below_bits c (i := FLAG) (by decide) j 0
        exact Or.inl (by dsimp only; omega)
    rw [u₄.word (ap 2) (by omega), u₃.word (ap 1) (by omega), u₂.word (ap 0) (by omega), P.flag]
  · intro t ht
    rw [tbl_unch u₄ h7 hn (j := 0) (by decide) ht (tbl_apart_tbl (by decide) ht),
      tbl_unch u₃ h7 hn (j := 0) (by decide) ht (tbl_apart_tbl (by decide) ht), b₂ t ht, hk]
  · intro _ t ht
    rw [tbl_unch u₄ h7 hn (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht), b₃ t ht, hp2,
      ← v₂ (by decide) (by decide)]
  · intro t ht
    rw [b₄ t ht, hn2, ← v₃ (by decide) (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₄.gpr r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      k₃.gpr r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2]), k₂.gpr r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      P.keep.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]
  · intro x hx
    have hx' : size ≤ ofs (s₀.gpr .r8) x := by have := hx _ (List.mem_singleton_self _); omega
    rw [O₄ x (Or.inr (by have := bitsAt_le c h7 (j := 2) (by decide); omega)),
      O₃ x (Or.inr (by have := bitsAt_le c h7 (j := 1) (by decide); omega)),
      O₂ x (Or.inr (by have := bitsAt_le c h7 (j := 0) (by decide); omega)),
      P.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact Or.inr (by omega)]

theorem toM_cmont (hc : BaseCfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

theorem mul_zero_pt (P : Point c.C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

theorem rdi_not_powClob (n : Nat) : Reg.rdi ∉ powClob n := fun h =>
  (List.mem_cons.mp h).elim (fun h => absurd h (by decide)) (rdi_not_clob n)

theorem ladW_eq (c : Cfg) : ladW c.ladderCfg = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] := rfl

theorem powWP_eq (c : Cfg) : powW c.powP = slW c [ACC, PT, TMP] := rfl
theorem powWN_eq (c : Cfg) : powW c.powN = slW c [ACC, PT, TMP] := rfl

/-- The flag word apart from numbered slots. -/
theorem flag_unch {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (slW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) (hl : FLAG ∉ l) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_slW (c := c) hl w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- A hash of `len` bytes is its number shifted right by the bits that are
not `e`'s. -/
theorem hashToInt_eq (c : Cfg) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q c.C.len) =
      ofBytes (Spec.Ecdsa.bytesAt m q c.C.len) >>> c.sh := by
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt, Cfg.sh]
  split
  · rw [show 8 * c.C.len - Spec.Ecdsa.nBits c.C = 0 by omega, Nat.shiftRight_zero]
  · rfl

end VG.Proof.Ecdsa.X86_64
