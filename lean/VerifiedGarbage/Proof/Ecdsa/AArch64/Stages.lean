import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# ECDSA on AArch64: the setup and the tables of bits

The first stage of `Cfg.sign` (`stage₁`), which ECDH and the public key run
too: the setup and the table of bits of `k`, and what
the later stages share. None of it needs the group law, which only the
proofs of the results (`Main.lean`) import.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The arguments' numbers. -/
abbrev kv (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x3) (8 * c.n))
abbrev dv (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) (8 * c.n))
abbrev ev (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (8 * c.n))

/-- What the stages keep: the working space, `out` in `x20`, the regions,
the constants and the saved registers. -/
structure Keep (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  x20 : s.gpr .x20 = s₀.gpr .x0
  wr : s.wr = s₀.wr
  fixed : Fixed c base s₀.gpr s.mem

/-- After the setup and the table. -/
structure St₁ (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c s₀
  d : sv c base s D = dv c s₀
  e : sv c base s E = ev c s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64
  t₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if (kv c s₀).testBit t then 1 else 0
  syms : s.syms = s₀.syms
  gpr : ∀ r, r ∉ [.x0, .x1, .x2, .x5, .x16, .x17, .x19, .x20] → s.gpr r = s₀.gpr r
  unch : Unch base [(0, size)] s₀.mem s.mem
  rd : s.rd = s₀.rd

/-- The setup, then the table. -/
theorem stage₁ (hc : CfgOk c) {s₀ : State} (hp : SetupPre c s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, St₁ c s₀ (s₀.gpr .x4) s → WP isa rest s Q) :
    WP isa (.seq (.block c.setup) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) rest)) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  refine WP.seq (WP.mono_syms (setup_ok hc hp) fun s₁ P sy₁ => ?_)
  have hn := P.scr.nowrap
  have hc' : ∀ ix ∈ c.consts, sv c (s₀.gpr .x4) s₁ ix.1 = ix.2 := P.consts
  have fx : Fixed c (s₀.gpr .x4) s₀.gpr s₁.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (BM, c.mont c.C.b) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved⟩
  have hsep : ∀ {i : Nat}, i < 45 → ∀ j, c.sl i + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + 64 * c.n ≤ c.sl i :=
    fun hi j => Or.inl (by have := sl_below_bits c hi j 0; omega)
  have hS : size = 8192 := rfl
  have hsz' : ∀ {j}, j < 3 → bitsAt c.n j + 64 * c.n ≤ 4096 := fun hj => bitsAt_le c h7 hj
  have hsz : ∀ {j}, j < 3 → bitsAt c.n j + 64 * c.n ≤ size := fun hj => by have := hsz' hj; omega
  have h4k : ∀ {i}, i < 45 → c.sl i < 4096 := fun hi => by
    have := sl_below_bits c hi 0 0; have := hsz' (j := 0) (by decide); omega
  -- The table of `k`.
  refine WP.seq (WP.mono_syms (bits_ok P.scr h0 (by omega) (sl_le c h7 (i := K) (by decide)) (hsz (j := 0)
    (by decide)) (h4k (by decide)) (hsz' (by decide)) (hsep (i := K) (by decide) 0)) fun s₂ ⟨b₂, k₂, O₂⟩ sy₂ => h s₂ ?_)
  have u₂ := O₂.unch
  have v₂ : ∀ {i}, i < 45 → sv c (s₀.gpr .x4) s₂ i = sv c (s₀.gpr .x4) s₁ i := fun hi =>
    sv_unch u₂ h7 hn hi (apart_tbl hi 0)
  have hk : (kv c s₀) = sv c (s₀.gpr .x4) s₁ K := P.k.symm
  have hs₂ := P.scr.of_keepRegs k₂ (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have ap : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi w hw => by
      rw [List.mem_singleton.mp hw]
      have := sl_below_bits c hi 0 0
      have : 1 ≤ c.n := h0
      exact Or.inl (by dsimp only; omega)
  refine ⟨⟨hs₂, ?_, by rw [k₂.wr, P.keep.wr], ?_⟩,
    by rw [v₂ (by decide), P.k], by rw [v₂ (by decide), P.d], by rw [v₂ (by decide), P.e],
    by rw [v₂ (by decide)]; exact hc' (RX, 0) (by simp [Cfg.consts]),
    by rw [v₂ (by decide)]; exact hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    by rw [v₂ (by decide)]; exact hc' (RZ, 0) (by simp [Cfg.consts]), ?_, ?_, ?_, ?_, ?_,
    by rw [k₂.rd, P.keep.rd]⟩
  · rw [k₂.gpr _ (by decide), P.x20]
  · exact fx.unch h7 hn (fixedOk_tbl 0) u₂
  · rw [u₂.word (ap (i := FLAG) (by decide)) (by omega), P.flag]
  · intro t ht
    rw [b₂ t ht, hk]
  · rw [sy₂, sy₁]
  · intro r hr
    have sub : ∀ {l : List Reg}, (∀ q ∈ l, q ∈ [Reg.x0, .x1, .x2, .x5, .x16, .x17, .x19, .x20]) → r ∉ l :=
      fun hl h => hr (hl _ h)
    rw [k₂.gpr r (sub (by decide)), P.keep.gpr r (sub (by decide))]
  · intro x hx
    have hx' : size ≤ ofs (s₀.gpr .x4) x := by have := hx _ (List.mem_singleton_self _); omega
    rw [O₂ x (Or.inr (by have := bitsAt0_le c h7; omega)),
      P.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact Or.inr (by omega)]

theorem toM_cmont (hc : CfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

theorem mul_zero_pt (P : Point c.C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

theorem x0_not_powClob {n : Nat} (_hn : n < 10) : Reg.x0 ∉ powClob n := fun h =>
  (List.mem_cons.mp h).elim (fun h => absurd h (by decide)) (x0_not_clob n)


/-- The flag word apart from numbered slots. -/
theorem flag_unch {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (slW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) (hl : FLAG ∉ l) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_slW (c := c) hl w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- A hash of `8 n` bytes is its number. -/
theorem hashToInt_eq (hc : CfgOk c) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q (8 * c.n)) =
      ofBytes (Spec.Ecdsa.bytesAt m q (8 * c.n)) := by
  have := hc.hash
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt,
    show 8 * (8 * c.n) ≤ Spec.Ecdsa.nBits c.C by omega, ite_true]

end VG.Proof.Ecdsa.AArch64
