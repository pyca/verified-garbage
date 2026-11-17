module

import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Spec.X25519

/-! ### `Weierstrass.Arm.Rep`, which this module and modules that import it used -/

section

/-!
# Short Weierstrass curves on 32-bit ARM: the ladder computes `[k]P`

The invariant of the group law for `ladder_ok`: `R` represents `[k >>> j]P`,
for the point `P` that `G` represents, which an iteration keeps
(`step_rep'`, by `ladder_step'`) when the slots of `a` and `3b` hold the
curve's, also with the formulas for `a = 0` when the curve's `a` is zero and
`G`'s `Z` one.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass Spec.Weierstrass

theorem step_rep' {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P)
    {a0 : Bool} (h0 : a0 = true → (Fin.ofNat C.p C.a : Fe C) = 0 ∧ tmv C L.M.n base s L.G.z = 1) :
    Step L C base s k (fun j X Y Z => Rep C X Y Z (mul (k >>> j) P)) a0 := by
  intro j _ X Y Z X2 Y2 Z2 X3 Y3 Z3 hQ h2 h3
  rw [ha, hb] at h2 h3
  exact ladder_step' hC hP h0 hG hQ h2 h3

end VG.Proof.Weierstrass.Arm

end

end

/-! ### `Ecdsa.Arm.MulFn`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Arm.Stages`, which this module and modules that import it used -/

section

/-!
# ECDSA on 32-bit ARM: the setup and the tables of bits

The first stage of `Cfg.sign` (`stage₁`): the setup and the tables of bits
of `k`, `p - 2` and `n - 2`, and what the later stages share. None of it
needs the group law, which only the proofs of the results (`Main.lean`)
import.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)

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

/-- The registers the stages may change. -/
abbrev work : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem callClob_work : ∀ r ∈ Mont.callClob, r ∈ work := by decide
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
  obtain fx : Fixed c (scBase A s₀) s₀.gpr s₁.mem :=
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
  obtain hs₂ := P.scr.of_rest k₂ (by decide)
  obtain hf₂ := P.far.of_rest k₂
  have u₂ := O₂.unch
  obtain v₂ : ∀ {i}, i < 45 → sv c (scBase A s₀) s₂ i = sv c (scBase A s₀) s₁ i := fun hi =>
    sv_unch u₂ h7 hn hi (apart_tbl h7 hi 0)
  -- The table of `p - 2`.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs₂ hf₂ (i := EXPP) (j := 1) (by decide) (by decide))
    fun s₃ ⟨b₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  obtain hf₃ := hf₂.of_rest k₃
  have u₃ := O₃.unch
  obtain v₃ : ∀ {i}, i < 45 → sv c (scBase A s₀) s₃ i = sv c (scBase A s₀) s₁ i := fun hi =>
    (sv_unch u₃ h7 hn hi (apart_tbl h7 hi 1)).trans (v₂ hi)
  -- The table of `n - 2`.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs₃ hf₃ (i := EXPN) (j := 2) (by decide) (by decide))
    fun s₄ ⟨b₄, k₄, O₄⟩ => h s₄ ?_)
  have u₄ := O₄.unch
  obtain v₄ : ∀ {i}, i < 45 → sv c (scBase A s₀) s₄ i = sv c (scBase A s₀) s₁ i := fun hi =>
    (sv_unch u₄ h7 hn hi (apart_tbl h7 hi 2)).trans (v₃ hi)
  have hk : (kv c A s₀) = sv c (scBase A s₀) s₁ K := P.k.symm
  obtain hp2 : c.C.p - 2 = sv c (scBase A s₀) s₁ EXPP := (hc' (EXPP, c.C.p - 2) (by simp [Cfg.consts])).symm
  obtain hn2 : c.C.n - 2 = sv c (scBase A s₀) s₁ EXPN := (hc' (EXPN, c.C.n - 2) (by simp [Cfg.consts])).symm
  obtain K₂₄ : Rest work s₁ s₄ :=
    (k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  obtain A₂₄ : Rest [.r4, .r5, .r7, .r11] s₁ s₄ := k₂.trans (k₃.trans k₄)
  refine ⟨⟨hs₃.of_rest k₄ (by decide), hf₃.of_rest k₄, (P.keep.mono (by decide)).trans (K₂₄.mono (by simp)),
    by rw [K₂₄.gpr _ (by decide), P.lr], ?_, ?_⟩,
    by rw [v₄ (by decide), P.k], by rw [v₄ (by decide), P.d], by rw [v₄ (by decide), P.e],
    by rw [v₄ (by decide)]; exact hc' (RX, 0) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    by rw [v₄ (by decide)]; exact hc' (RZ, 0) (by simp [Cfg.consts]), ?_, ?_, ?_, ?_, ?_⟩
  · exact (fx.unch h7 hn (fixedOk_tbl h7 0) u₂ |>.unch h7 hn (fixedOk_tbl h7 1) u₃).unch h7 hn (fixedOk_tbl h7 2) u₄
  · intro x hx
    obtain hx' : 8192 ≤ ofs (scBase A s₀) x := by have := hx _ (List.mem_singleton_self _); omega_arith
    rw [O₄ x (Or.inr (by have := bitsAt_le c h7 (j := 2) (by decide); omega_arith)),
      O₃ x (Or.inr (by have := bitsAt_le c h7 (j := 1) (by decide); omega_arith)),
      O₂ x (Or.inr (by have := bitsAt_le c h7 (j := 0) (by decide); omega_arith)),
      P.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact Or.inr (by dsimp only [size]; omega_arith)]
  · have hF := sl_le c h7 (i := FLAG) (by decide)
    obtain ap : ∀ j, ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
      fun j w hw => by
        rw [List.mem_singleton.mp hw]
        have := sl_below_bits c hc.n10 (i := FLAG) (by decide) j 0
        exact Or.inl (by dsimp only; omega_arith)
    rw [flagW, Unch.readW32 u₄ (ap 2) (by omega_arith), Unch.readW32 u₃ (ap 1) (by omega_arith),
      Unch.readW32 u₂ (ap 0) (by omega_arith), ← flagW, P.flag]
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
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] ++ [(c.wk, 64 * c.n)] := rfl

theorem powWxP_eq (c : Cfg) : powWx c.powP c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, 64 * c.n)] := rfl
theorem powWxN_eq (c : Cfg) : powWx c.powN c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, 64 * c.n)] := rfl


/-- The flag word apart from numbered slots and the accumulator. -/
theorem flag_unch {base : Addr} {l : List Nat} {m m' : Mem}
    (hu : Unch base (slW c l ++ [(c.wk, 64 * c.n)]) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega_arith)
  rcases List.mem_append.mp hw with hw | hw
  · rcases apart_slW (c := c) hl w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  · rcases apart_wk (c := c) h7 (i := FLAG) (by decide) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h

/-- A stage writes in `scratch` only. -/
theorem whole_of' {base : Addr} {W : List (Nat × Nat)} {m₀ m m' : Mem} (h₀ : Unch base [(0, 8192)] m₀ m)
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) : Unch base [(0, 8192)] m₀ m' := fun x hx => by
  obtain h := hx (0, 8192) (List.mem_singleton_self _)
  obtain hx' : 8192 ≤ ofs base x := by dsimp only at h; omega_arith
  rw [hu x (fun w hw => Or.inr (by have := hW w hw; omega_arith)), h₀ x hx]

/-- A stage writes in the working space only. -/
theorem whole_of {base : Addr} {W : List (Nat × Nat)} {m₀ m m' : Mem} (h₀ : Unch base [(0, 8192)] m₀ m)
    (hu : Unch base W m m') (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, 8192)] m₀ m' :=
  whole_of' h₀ hu fun w hw => by have := hW w hw; dsimp only [size] at this; omega_arith

/-- A hash of `len` bytes is its number without the bits that are not
`e`'s. -/
theorem hashToInt_eq (c : Cfg) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q c.C.len) =
      ofBytes (Spec.Ecdsa.bytesAt m q c.C.len) >>> c.sh := by
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt, Cfg.sh]
  split
  · rw [show 8 * c.C.len - Spec.Ecdsa.nBits c.C = 0 by omega_arith, Nat.shiftRight_zero]
  · rfl

end VG.Proof.Ecdsa.Arm

end

end

/-!
# `vg_<curve>_mul` on 32-bit ARM: correctness

`mulBody` (`Impl/Ecdsa/Arm.lean`) makes the table of the bits of the number
at `K`'s slot, copies `Q` from `R`'s first two slots to `ACC` and `PT`, sets
`R = O` from zero and one, and runs the ladder of `ladderP` from the point
at `ACC`, `PT`, `ONEP` (`mulLadder`). For any invariant `Q` of the ladder
from the point at `RX`, `RY`, `ONEP` (`Step` of `rLadder`, which the copies
carry to `mulLadder`'s point) that accepts `O`, `Q 0` accepts what `R` holds
at the end, and the body writes only what the ladder writes, `ACC`, `PT`
and the table of bits (`mulBody_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)

variable {c : Cfg}

/-! ## The ladder's layout -/

/-- The ladder from the point at `px`, `py`, `ONEP`: the one whose invariants
the caller of `mulAt` states. -/
abbrev pLadder (c : Cfg) (px py : Nat) : LadderCfg := { c.ladderCfg with G := c.pt px py ONEP }


/-- The ladder from the point at `RX`, `RY`, `ONEP`: the one whose
invariants a caller states, which `mulBody`'s copies carry to `mulLadder`. -/
abbrev rLadder (c : Cfg) : LadderCfg := { c.ladderCfg with G := c.pt RX RY ONEP }

/-- What the point's slots must be for the ladder from them: numbered slots,
neither the modulus's nor the temporary area, and none the ladder writes. -/
def PtSlots (px py : Nat) : Prop :=
  ∀ i ∈ [px, py], i < 45 ∧ i ≠ MP ∧ i ≠ TMP ∧ i ∉ [T0, T1, T2, T3, T4, T5, TX, TY, TZ] ∧
    i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ]

instance (px py : Nat) : Decidable (PtSlots px py) := by unfold PtSlots; infer_instance

theorem pLadSlots_eq (c : Cfg) (px py : Nat) : ladSlots (pLadder c px py) = [AP, B3P, px, py, ONEP, RX, RY, RZ,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ].map c.sl := rfl

/-- What every slot of the ladder's satisfies, given `PtSlots`. -/
theorem ptSlots_all {px py : Nat} (hp : PtSlots px py) {P : Nat → Prop}
    (hc : ∀ i ∈ [AP, B3P, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ], P i)
    (hpq : ∀ i ∈ [px, py], P i) :
    ∀ i ∈ [AP, B3P, px, py, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ], P i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> first | exact hc _ (by decide) | exact hpq _ (by simp)

theorem pLadLay (hc : CfgOk c) {px py : Nat} (hp : PtSlots px py) : LadLay (pLadder c px py) size 8192 := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, px, py, ONEP]) rfl rfl (by decide) ?_, ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 8 * c.C.len by have := hc.len8; omega_arith,
      show 8 * c.C.len < 2 ^ 16 by have := hc.len_hi; omega_arith⟩,
    (by have := bitsAt_le c h7 (j := 0) (by decide); have := hc.len_hi;
        change bitsAt c.n 0 + 8 * c.C.len ≤ 8192; omega_arith), ?_⟩
  · exact lay_map hc rfl rfl rfl (ptSlots_all hp (by decide) fun i hi => ⟨(hp i hi).1, (hp i hi).2.1, (hp i hi).2.2.1⟩)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h <;> subst h <;>
      first | decide | exact (hp _ (by simp)).2.2.2.1
  · refine map_sl_disj hn (l₁ := [AP, B3P, px, py, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ]) ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h <;> subst h <;>
      first | decide | exact (hp _ (by simp)).2.2.2.2
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      obtain hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c hc.n10 (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c hc.n10 (i := TMP) (by decide) 0 0)

theorem pLadWk (hc : CfgOk c) {px py : Nat} (hp : PtSlots px py) : LadWk (pLadder c px py) size c.wk where
  le := wk_le c hc.n10 rfl
  sl := by
    rw [pLadSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_below_wk c hc.n10 (ptSlots_all hp (P := (· < 45)) (by decide) (fun i hi => (hp i hi).1) i hi)
  mo := sl_below_wk c hc.n10 (i := MP) (by decide)
  tmp := sl_below_wk c hc.n10 (i := TMP) (by decide)
  bits := wk_below_bits c hc.n10 rfl 0

theorem pLadPt {px py : Nat} (hp : PtSlots px py) (h6 : c.n ≤ 6) :
    VG.Proof.Weierstrass.Arm.Point.LadPt (pLadder c px py) where
  sl := by
    rw [pLadSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_below_pt h6 (ptSlots_all hp (P := (· < 45)) (by decide) (fun i hi => (hp i hi).1) i hi)
  mo := sl_below_pt h6 (i := MP) (by decide)

theorem mulLadLay (hc : CfgOk c) : LadLay c.mulLadder size 8192 := pLadLay (px := ACC) (py := PT) hc (by decide)
theorem mulLadWk (hc : CfgOk c) : LadWk c.mulLadder size c.wk := pLadWk (px := ACC) (py := PT) hc (by decide)
theorem mulLadPt (h6 : c.n ≤ 6) : VG.Proof.Weierstrass.Arm.Point.LadPt c.mulLadder :=
  pLadPt (px := ACC) (py := PT) (by decide) h6

/-- The ladder writes what the signature's does. -/
theorem mulLadWp_eq (c : Cfg) :
    VG.Proof.Weierstrass.Arm.Point.ladWp c.mulLadder c.wk = VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk :=
  rfl

/-! ## The body -/

/-- What `mulBody` writes besides the ladder: `ACC`, `PT` and the table of
the bits of `k`. -/
abbrev mulBX (c : Cfg) : List (Nat × Nat) := slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n)]

/-- What `mulBody` writes. -/
abbrev mulBW (c : Cfg) : List (Nat × Nat) :=
  VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk ++ mulBX c

/-- `Step` depends only on what the slots of `a`, `3b` and the point hold. -/
theorem step_congr {L L' : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hb : L'.nbits = L.nbits)
    (ha : tmv C L'.M.n base s' L'.S.a = tmv C L.M.n base s L.S.a)
    (h3 : tmv C L'.M.n base s' L'.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L'.M.n base s' L'.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L'.M.n base s' L'.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L'.M.n base s' L'.G.z = tmv C L.M.n base s L.G.z)
    (h : Step L C base s k Q) : Step L' C base s' k Q := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'
  rw [ha, h3] at h2 h3'
  rw [hx, hy, hz] at h3'
  exact h j (hb ▸ hj) X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'

/-- `mulBody`: for any invariant `Q` of the ladder from the point at `RX`,
`RY`, `ONEP` (`rLadder`) that accepts `O` (as zero and one hold it), for
the scalar at `K`'s slot, `Q 0` accepts what `R` holds at the end; only
`powClob` and `mulBW` change. -/
theorem mulBody_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (rLadder c) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulBody s fun s' => Rest powClob s s' ∧ Unch base (mulBW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs hf (i := K) (j := 0) (by decide) (by decide))
    fun s₁ ⟨T₁, K₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_rest K₁ (by decide)
  obtain hf₁ := hf.of_rest K₁
  obtain e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    O₁.wordsVal (Or.inl (sl_below_bits c h7 hi 0 0)) (by have := sl_le c h7 hi; omega_arith)
  -- The copies.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := ACC) (a := RX) (by decide) (by decide) (by decide))
    fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := PT) (a := RY) (by decide) (by decide) (by decide))
    fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₃ (o := RX) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₄ (o := RY) (a := ONEP) (by decide) (by decide) (by decide))
    fun s₅ ⟨x₅, k₅, O₅⟩ => ?_)
  obtain hs₅ := hs₄.of_rest k₅ (by decide)
  refine WP.mono (copySl_ok hc hs₅ (o := RZ) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₆ ⟨x₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_rest k₆ (by decide)
  obtain K₁₆ : Rest powClob s s₆ :=
    (K₁.mono (by simp [powClob, clob])).trans
      ((k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆)))).mono (by simp [powClob, clob]))
  obtain hf₆ := hf.of_rest K₁₆
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij =>
    O.wordsVal (sl_apart c hij) (by have := sl_le c h7 hi; omega_arith)
  -- What the copies leave, in terms of `s`.
  obtain e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, RX, RY, RZ] → sv c base s₆ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [o O₆ hi hl.2.2.2.2, o O₅ hi hl.2.2.2.1, o O₄ hi hl.2.2.1, o O₃ hi hl.2.1, o O₂ hi hl.1, e₁ hi]
  obtain acc₆ : sv c base s₆ ACC = sv c base s RX := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), x₂, e₁ (by decide)]
  obtain pt₆ : sv c base s₆ PT = sv c base s RY := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), x₃,
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain rx₆ : sv c base s₆ RX = sv c base s ZERO := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), x₄, o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain ry₆ : sv c base s₆ RY = sv c base s ONEP := by
    rw [o O₆ (by decide) (by decide), x₅, o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain rz₆ : sv c base s₆ RZ = sv c base s ZERO := by
    rw [x₆, o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain U₁₆ : Unch base (mulBX c ++ slW c [RX, RY, RZ]) s.mem s₆.mem := by
    have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    refine this.mono fun w hw => ?_
    simp only [slW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.map_cons,
      List.map_nil] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  obtain T₆ : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    obtain U : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem := by
      have := O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch)))
      exact this.mono fun w hw => by simpa using hw
    rw [tbl_unch U h7 (j := 0) (by decide) ht (tbl_apart_slW h7 (by decide) 0 t), T₁ t ht]
  obtain M₆ : ModOkW c.MP' size c.C.p s₆.mem base := by
    refine modP_of hc ?_
    show sv c base s₆ MP = c.C.p
    rw [e₆ (by decide) (by decide)]; exact hM.val
  obtain tv : ∀ {i j : Nat}, sv c base s₆ i = sv c base s j →
      tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
    show toM _ _ (sv c base s₆ _) = toM _ _ (sv c base s _); rw [h]
  obtain hstep₆ : Step c.mulLadder c.C base s₆ (sv c base s K) Q :=
    step_congr (L := rLadder c) (L' := c.mulLadder) rfl (tv (e₆ (by decide) (by decide))) (tv (e₆ (by decide) (by decide))) (tv acc₆)
      (tv pt₆) (tv (e₆ (by decide) (by decide))) hstep
  obtain hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, ACC, PT, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₆ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e₆ (by decide) (by decide)]; exact hap
    · rw [e₆ (by decide) (by decide)]; exact hb3
    · rw [acc₆]; exact hqx
    · rw [pt₆]; exact hqy
    · rw [e₆ (by decide) (by decide)]; exact hone
    · rw [rx₆]; exact hzero
    · rw [ry₆]; exact hone
    · rw [rz₆]; exact hzero
  obtain hR : Q c.mulLadder.nbits (tmv c.C c.n base s₆ c.mulLadder.R.x) (tmv c.C c.n base s₆ c.mulLadder.R.y)
      (tmv c.C c.n base s₆ c.mulLadder.R.z) := by
    show Q _ (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY)) (tmv c.C c.n base s₆ (c.sl RZ))
    rw [tv rx₆, tv ry₆, tv rz₆]; exact hO
  refine WP.mono (VG.Proof.Weierstrass.Arm.Point.ladderP_ok (L := c.mulLadder) (a0 := false) (u := c.umaal) (mulLadLay hc) (mulLadWk hc)
    hc.fp mulLadPt hpR (bitsAt_lt hc (j := 0) (by decide)) hs₆ hf₆ M₆ hlt nofun hstep₆ hR
    (fun t ht => T₆ t (Nat.lt_of_lt_of_le ht (scalarBits_le hc))) (scalarBits_enc hc))
    fun s₇ ⟨K₇, U₇, M₇, L₇, R₇⟩ => ⟨K₁₆.trans K₇, ?_, M₇, L₇, R₇⟩
  rw [mulLadWp_eq] at U₇
  refine (U₁₆.trans U₇).mono fun w hw => ?_
  simp only [mulBW, List.mem_append] at hw ⊢
  rcases hw with (hw | hw) | hw
  · exact .inr hw
  · refine .inl ?_
    rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq]
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    obtain ⟨i, hi, rfl⟩ := hw
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, by
      rcases hi with rfl | rfl | rfl <;> simp, rfl⟩))
  · exact .inl hw

end VG.Proof.Ecdsa.Arm

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_reg)

variable {c : Cfg}

/-! ## The function -/

/-- Where `vg_<curve>_mul` keeps the callee-saved registers. -/
abbrev mulSW (c : Cfg) : List (Nat × Nat) := [(c.sl nslots, 36)]

/-- What `vg_<curve>_mul` writes. -/
abbrev mulFW (c : Cfg) : List (Nat × Nat) := mulBW c ++ mulSW c

theorem mulSaved_eq (c : Cfg) : c.mulSaved = [(.r4, c.sl 45), (.r5, c.sl 45 + 4), (.r6, c.sl 45 + 8),
    (.r7, c.sl 45 + 12), (.r8, c.sl 45 + 16), (.r9, c.sl 45 + 20),
    (.r11, c.sl 45 + 28), (.lr, c.sl 45 + 32)] := rfl

/-- The registers' words lie past the numbered slots, below the field
arithmetic's own working space and the point functions' slots. -/
theorem save_le_wk (h7 : c.n < 10) : c.sl 45 + 36 ≤ c.wk := by
  rw [sl_eq, wk_eq]; omega_arith

theorem save_le_oAt (h6 : c.n ≤ 6) : c.sl 45 + 36 ≤ Impl.Weierstrass.Point.oAt c.n := by
  rw [sl_eq]
  simp only [Impl.Weierstrass.Point.oAt, Impl.Weierstrass.Point.pAt, Impl.Weierstrass.Point.qAt,
    Impl.Weierstrass.Point.aAt, Impl.Weierstrass.Point.b3At, Impl.Weierstrass.Point.ownAt,
    Impl.Weierstrass.Point.elemBytes, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]
  omega_arith

/-- The registers' words are apart from what the body writes. -/
theorem save_apart (h7 : c.n < 10) : ∀ w ∈ mulBW c, c.sl 45 + 36 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl 45 := by
  intro w hw
  obtain hwk := save_le_wk (c := c) h7
  simp only [mulBW, mulBX, List.mem_append, VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq] at hw
  rcases hw with ((hw | hw) | hw) | (hw | hw)
  · simp only [slW, List.mem_map] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    have : i < 45 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact .inr (sl_lt c this)
  · rw [List.mem_singleton.mp hw]; exact .inl hwk
  · unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
    split at hw
    · rw [List.mem_singleton.mp hw]; exact .inl (save_le_oAt ‹_›)
    · simp at hw
  · simp only [slW, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    rcases hi with rfl | rfl
    · exact .inr (sl_lt c (by decide))
    · exact .inr (sl_lt c (by decide))
  · rw [List.mem_singleton.mp hw, bitsAt_eq]; left; rw [wk_eq] at hwk; dsimp only; omega_arith

/-- The callee-saved registers' words, by register. -/
theorem mulSaved_bounds (h7 : c.n < 10) : ∀ p ∈ c.mulSaved, p.2 + 4 ≤ size := by
  have := save_le_wk (c := c) h7
  have := wk_le c h7 (M := c.MP') rfl
  rw [mulSaved_eq]; intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem mulSaved_pairwise (c : Cfg) :
    c.mulSaved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  rw [mulSaved_eq]; simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
  generalize c.sl 45 = x
  omega_using []

theorem mulSaved_regs (c : Cfg) : (c.mulSaved.map Prod.fst).Nodup ∧ ∀ p ∈ c.mulSaved, p.1 ≠ .r12 := by
  rw [mulSaved_eq]
  refine ⟨by simp only [List.map_cons, List.map_nil]; decide, fun p hp => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- `vg_<curve>_mul`, from the working space at `r0` (`base`), its `8192`
bytes the only memory it may access, and what `mulBody_ok` needs of them:
it returns with the callee-saved registers and `sp` kept and `r12 = ws`,
having changed only `mulFW`, with `Q 0` accepting what `R` holds. -/
theorem mulFn_ok (hc : CfgOk c) {s : State} {base : Addr} (hb : State.addr (s.gpr .r0) = base)
    (hwr : s.wr = [⟨base, 8192⟩]) (hfit : base.toNat + 8192 ≤ 2 ^ 32)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (rLadder c) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulFn s fun s' => abiPreserved s s' ∧ s'.gpr .r12 = s.gpr .r0 ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Unch base (mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  obtain hsv := save_le_wk (c := c) h7
  have hsz : size = 4096 := rfl
  rw [Cfg.mulFn]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => ?_)
  obtain hs₁ : Scr s₁ base size := ⟨by rw [u₁.gpr]; exact hb, ⟨8192, by decide, by decide,
    by rw [u₁.wr, hwr]; simp⟩, by omega_using [hfit, hsz], by decide⟩
  obtain hf₁ : Far s₁ base 8192 := ⟨by rw [u₁.wr, hwr]; simp, hfit⟩
  refine WP.mono (strs_ok hs₁ c.mulSaved (mulSaved_bounds h7) (mulSaved_pairwise c))
    fun s₂₀ ⟨K₂₀, O₂₀, V₂₀⟩ => ?_
  refine WP.seq (wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_)
  obtain K₂ : Rest [.lr] s₁ s₂ := (K₂₀.mono fun _ h => absurd h List.not_mem_nil).trans (u₂.rest (by simp))
  obtain O₂ : Outs base (c.mulSaved.map fun p => (p.2, 4)) s₁.mem s₂.mem := by rw [u₂.mem]; exact O₂₀
  obtain V₂ : ∀ p ∈ c.mulSaved, s₂.mem.readW (off base p.2) 32 = s₁.gpr p.1 := fun p hp => by
    rw [u₂.mem]; exact V₂₀ p hp
  obtain l₂ : s₂.gpr .lr = s.gpr .r10 := by rw [u₂.gpr, K₂₀.gpr _ (by simp), u₁.other _ (by decide)]
  obtain hs₂ := hs₁.of_rest K₂ (by decide)
  obtain hf₂ := hf₁.of_rest K₂
  obtain e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi => by
    have := sl_lt c (j := 45) hi
    have := sl_le c h7 hi
    refine (VG.Proof.Weierstrass.Arm.Outs.wordsVal O₂ (fun r hr => ?_) (by omega_arith)).trans ?_
    · rw [mulSaved_eq] at hr
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> left <;> dsimp only <;> omega_arith
    · rw [u₁.mem]
  obtain tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  obtain hstep₂ : Step (rLadder c) c.C base s₂ (sv c base s₂ K) Q := by
    rw [e₂ (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide))
      (tv (by decide)) hstep
  obtain hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
      (tmv c.C c.n base s₂ (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  refine WP.seq (WP.mono (mulBody_ok hc hs₂ hf₂ (modP_of hc (by
      show sv c base s₂ MP = _; rw [e₂ (by decide)]; exact hmp))
    (by rw [e₂ (by decide)]; exact hap) (by rw [e₂ (by decide)]; exact hb3)
    (by rw [e₂ (by decide)]; exact hone) (by rw [e₂ (by decide)]; exact hzero)
    (by rw [e₂ (by decide)]; exact hqx) (by rw [e₂ (by decide)]; exact hqy) hstep₂ hO₂)
    fun s₃₀ ⟨K₃, U₃₀, M₃, L₃₀, R₃₀⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_)
  obtain l₃ : s₃.gpr .r10 = s.gpr .r10 := by rw [u₃.gpr, K₃.gpr _ (by decide), l₂]
  obtain U₃ : Unch base (mulBW c) s₂.mem s₃.mem := by rw [u₃.mem]; exact U₃₀
  obtain L₃ : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s₃.mem base x c.n < c.C.p := by
    rw [u₃.mem]; exact L₃₀
  obtain R₃ : Q 0 (tmv c.C c.n base s₃ (c.sl RX)) (tmv c.C c.n base s₃ (c.sl RY))
      (tmv c.C c.n base s₃ (c.sl RZ)) := by
    show Q 0 (toM _ _ (wordsVal s₃.mem _ _ _)) (toM _ _ (wordsVal s₃.mem _ _ _)) (toM _ _ (wordsVal s₃.mem _ _ _))
    rw [u₃.mem]; exact R₃₀
  obtain hs₃ := (hs₂.of_rest K₃ (by decide)).of_rest (u₃.rest (ws := [.r10]) (by simp)) (by decide)
  refine WP.mono (ldrs_ok hs₃ c.mulSaved (mulSaved_bounds h7) (mulSaved_regs c).1 (mulSaved_regs c).2)
    fun s₄ ⟨M₄, K₄, V₄⟩ => ?_
  -- The words of the registers, kept by the body.
  obtain kept : ∀ p ∈ c.mulSaved, s₃.mem.readW (off base p.2) 32 = s₂.mem.readW (off base p.2) 32 := by
    intro p hp
    refine VG.Proof.Weierstrass.Arm.Unch.readW32 U₃ (fun w hw => ?_) (by have := mulSaved_bounds h7 p hp; omega_arith)
    obtain hp' : c.sl 45 ≤ p.2 ∧ p.2 + 4 ≤ c.sl 45 + 36 := by
      rw [mulSaved_eq] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
    rcases save_apart h7 w hw with h | h <;> [exact .inl (by omega_arith); exact .inr (by omega_arith)]
  refine ⟨⟨fun r hr => ?_, by rw [K₄.sp, u₃.sp, K₃.sp, K₂.sp, u₁.sp]⟩, ?_,
    by rw [K₄.rd, u₃.rd, K₃.rd, K₂.rd, u₁.rd], by rw [K₄.wr, u₃.wr, K₃.wr, K₂.wr, u₁.wr], ?_, ?_, ?_⟩
  · by_cases h10 : r = .r10
    · subst h10
      rw [K₄.gpr _ (by simp only [mulSaved_eq, List.map_cons, List.map_nil]; decide), l₃]
    obtain hp : ∃ d, (r, d) ∈ c.mulSaved := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [mulSaved_eq]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl h10 |
        exact ⟨_, by repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)⟩
    obtain ⟨d, hd⟩ := hp
    rw [V₄ _ hd, kept _ hd, V₂ _ hd, u₁.other _ (by
      intro h; subst h; simp [preserved] at hr)]
  · rw [K₄.gpr _ (by simp only [mulSaved_eq, List.map_cons, List.map_nil]; decide), u₃.other _ (by decide),
      K₃.gpr _ (by decide), K₂.gpr _ (by decide), u₁.gpr]
  · rw [M₄]
    have := (VG.Proof.Weierstrass.Arm.Outs.unch O₂).trans U₃
    rw [u₁.mem] at this
    refine this.cover fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rw [mulSaved_eq] at hw
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      refine ⟨(c.sl nslots, 36), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by dsimp only [nslots]; omega_arith, by dsimp only [nslots]; omega_arith⟩
    · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
  · rw [M₄]; exact L₃
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [M₄]; exact R₃

/-! ## The call -/

/-- A call of `vg_<curve>_mul` on the point at `px`, `py`, from the working
space at `r12`: for any invariant `Q` of the ladder from that point that
accepts `O`, `Q 0` accepts what `R` holds after it; only `r0`–`r4`, `r10`,
`R`'s first two slots and `mulFW` change. -/
theorem mulAt_ok (hc : CfgOk c) (C : Impl.Weierstrass.Mul.Curve) (hnf : c.mulFn.noFrames = true)
    {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    {px py : Nat} (hpx : px < 45) (hpy : py < 45) (hpxr : px ∉ [RX, RY]) (hpyr : py ∉ [RX, RY])
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s px < c.C.p) (hqy : sv c base s py < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (pLadder c px py) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa (c.mulAt C px py) s fun s' => Rest [.r10, .r0, .r1, .r2, .r3, .r4] s s' ∧
      Unch base (slW c [RX, RY] ++ mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hpxr hpyr
  rw [Cfg.mulAt]
  -- The copies and the moves before the call.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok hc hs (o := RX) (a := px) (by decide) hpx
    (Ne.symm hpxr.1)) fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_rest k₁ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := RY) (a := py) (by decide) hpy
    (Ne.symm hpyr.2)) fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  obtain k₄ : Rest [.r10, .r0, .r4] s s₄ :=
    (k₁.mono (by simp)).trans ((k₂.mono (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp))))
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain hs₄ := hs.of_rest k₄ (by decide)
  obtain hf₄ := hf.of_rest k₄
  obtain g10 : s₄.gpr .r10 = s.gpr .lr := by
    rw [u₄.other _ (by decide), u₃.gpr, k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  obtain g0 : s₄.gpr .r0 = s.gpr .r12 := by
    rw [u₄.gpr, u₃.other _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij =>
    O.wordsVal (sl_apart c hij) (by have := sl_le c h7 hi; omega_arith)
  obtain e₄ : ∀ {i}, i < 45 → i ≠ RX → i ≠ RY → sv c base s₄ i = sv c base s i := fun hi h1 h2 => by
    show wordsVal s₄.mem _ _ _ = _; rw [m₄]; exact (o O₂ hi h2).trans (o O₁ hi h1)
  obtain rx₄ : sv c base s₄ RX = sv c base s px := by
    show wordsVal s₄.mem _ _ _ = _; rw [m₄]; exact (o O₂ (by decide) (by decide)).trans x₁
  obtain ry₄ : sv c base s₄ RY = sv c base s py := by
    show wordsVal s₄.mem _ _ _ = _; rw [m₄]; exact x₂.trans (o O₁ hpy hpyr.1)
  obtain tv : ∀ {i j}, sv c base s₄ i = sv c base s j → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl j) :=
    fun h => by show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _); rw [h]
  obtain hstep₄ : Step (rLadder c) c.C base s₄ (sv c base s₄ K) Q := by
    rw [e₄ (by decide) (by decide) (by decide)]
    exact step_congr (L := pLadder c px py) rfl (tv (e₄ (by decide) (by decide) (by decide)))
      (tv (e₄ (by decide) (by decide) (by decide))) (tv rx₄) (tv ry₄)
      (tv (e₄ (by decide) (by decide) (by decide))) hstep
  obtain hO₄ : Q c.ladderCfg.nbits (tmv c.C c.n base s₄ (c.sl ZERO)) (tmv c.C c.n base s₄ (c.sl ONEP))
      (tmv c.C c.n base s₄ (c.sl ZERO)) := by
    rw [tv (e₄ (i := ZERO) (by decide) (by decide) (by decide)), tv (e₄ (i := ONEP) (by decide) (by decide) (by decide))]
    exact hO
  obtain hcov : Covers [⟨base, 8192⟩] s₄.wr := by
    obtain h := hf₄.write (d := 0) (n := 8192) (by omega_using [])
    simp only [off, BitVec.add_zero] at h
    exact Covers.one h
  obtain e0 : ∀ t : State, t.gpr .r0 = s.gpr .r12 → State.addr (t.gpr .r0) = base := fun t h => by
    rw [h]; exact hs.wb
  refine WP.seq (WP.callCalls (k := ⟨fun t => t.wr = [⟨base, 8192⟩] ∧ t.gpr .r0 = s.gpr .r12 ∧
        t.mem = s₄.mem,
      fun t t' => t'.gpr .r12 = t.gpr .r0 ∧ Unch base (mulFW c) t.mem t'.mem ∧
        (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal t'.mem base x c.n < c.C.p) ∧
        Q 0 (tmv c.C c.n base t' (c.sl RX)) (tmv c.C c.n base t' (c.sl RY)) (tmv c.C c.n base t' (c.sl RZ)),
      fun _ _ => True⟩)
    (fun t ⟨hw, h0, hm⟩ => by
      obtain hb := e0 t h0
      obtain sv_t : ∀ i, sv c base t i = sv c base s₄ i := fun i => by
        show wordsVal t.mem _ _ _ = wordsVal s₄.mem _ _ _; rw [hm]
      obtain tm_t : ∀ i, tmv c.C c.n base t (c.sl i) = tmv c.C c.n base s₄ (c.sl i) := fun i => by
        show toM _ _ (sv c base t i) = toM _ _ (sv c base s₄ i); rw [sv_t]
      obtain ⟨tr, t', he, A, R12, -, -, U, L, R⟩ := mulFn_ok hc hb hw hf.nowrap
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hmp)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hap)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hb3)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hone)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hzero)
        (by rw [sv_t, rx₄]; exact hqx) (by rw [sv_t, ry₄]; exact hqy)
        (by rw [sv_t]; exact step_congr rfl (tm_t _) (tm_t _) (tm_t _) (tm_t _) (tm_t _) hstep₄)
        (by rw [tm_t, tm_t]; exact hO₄)
      exact ⟨tr, t', he, A, R12, U, L, R⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨by rw [State.withRegions_wr],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0],
      by rw [State.withRegions_mem, State.callEntry_mem]⟩
    (Covers.right hcov) hcov ?_ hnf)
  intro s₇ r₇ w₇ p₇ _ hp₇ _ ⟨R, U, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at R U L E
  rw [State.callEntry_gpr _ (by decide), g0] at R
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have hm : s₈.mem = s₇.mem := u₈.mem
  refine ⟨⟨fun r hr => ?_, by rw [u₈.rd, r₇, k₄.rd], by rw [u₈.wr, w₇, k₄.wr],
    by rw [u₈.sp, p₇, k₄.sp]⟩, ?_, by rw [hm]; exact L, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h10, h0, h1, h2, h3, h4⟩ := hr
    by_cases hlr : r = .lr
    · subst hlr
      rw [u₈.gpr, hp₇ _ (by decide) (by decide), g10]
    by_cases h12 : r = .r12
    · subst h12
      rw [u₈.other _ (by decide), R]
    obtain hpres : r ∈ preserved := by revert h10 h0 h1 h2 h3 h4 h12 hlr; cases r <;> decide
    rw [u₈.other _ hlr, hp₇ r hpres hlr, k₄.gpr r (by simp [h10, h0, h4])]
  · rw [hm]
    obtain U₂ : Unch base (slW c [RX, RY]) s.mem s₂.mem := by
      have := O₁.unch.trans O₂.unch
      exact this.mono fun w hw => by simpa using hw
    rw [m₄] at U
    simpa only [List.append_assoc] using U₂.trans U
  · show Q 0 (toM _ _ (wordsVal s₈.mem _ _ _)) (toM _ _ (wordsVal s₈.mem _ _ _)) (toM _ _ (wordsVal s₈.mem _ _ _))
    rw [hm]; exact E

/-! ## What `vg_<curve>_mul` writes besides the ladder -/

/-- `ACC`, `PT` (its copy of `Q`), the table of `k`'s bits and the words past
the numbered slots where it keeps the callee-saved registers. -/
abbrev genX (c : Cfg) : List (Nat × Nat) := slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n), (c.sl nslots, 36)]

theorem apart_genX (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hl : i ∉ [ACC, PT]) :
    ∀ w ∈ genX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hl) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (Nat.le_trans (sl_below_bits c h7 hi 0 0) (Nat.le_add_right _ _))
  · exact Or.inl (sl_lt c (j := nslots) hi)

theorem tbl_apart_genX (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ genX c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW h7 (by decide) j t) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact tbl_apart_tbl hj ht _ (List.mem_singleton_self _)
  · refine Or.inr ?_
    rw [bitsAt_eq, sl_eq]; dsimp only [nslots]; omega_arith

theorem fixedOk_genX (h7 : c.n < 10) : FixedOk c (genX c) := by
  refine (fixedOk_slW (by decide)).append fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact fixedOk_tbl h7 0 _ (List.mem_singleton_self _)
  · exact Or.inr (Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide)))))

theorem genX_le (h7 : c.n < 10) : ∀ w ∈ genX c, w.1 + w.2 ≤ 8192 := by
  intro w hw
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  have := sl_le c h7 (i := 44) (by decide)
  have := bitsAt_le c h7 (j := 0) (by decide)
  rw [sl_eq] at *
  rcases hw with ⟨i, rfl | rfl, rfl⟩ | rfl | rfl <;> simp only [sl_eq, ACC, PT, nslots] at * <;> omega_arith

/-- Everything `vg_<curve>_mul` writes is at or past the temporary slot. -/
theorem mulFW_ge (h7 : c.n < 10) : ∀ w ∈ mulFW c, c.sl TMP ≤ w.1 := by
  intro w hw
  obtain hwk := save_le_wk (c := c) h7
  simp only [mulFW, mulBW, mulBX, mulSW, List.mem_append, VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq,
    slW, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [wk_eq, sl_eq] at hwk
  rcases hw with (((⟨j, hj, rfl⟩ | hw) | hw) | (⟨j, hj, rfl⟩ | hw)) | hw
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sl_eq, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP] <;> omega_using []
  · rw [hw, wk_eq, sl_eq]; simp only [TMP]; omega_using [h7]
  · unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
    split at hw
    · rw [List.mem_singleton.mp hw, show c.ladderCfg.M.n = c.n from rfl]
      obtain h1 := save_le_oAt (c := c) ‹_›
      rw [sl_eq] at h1 ⊢; simp only [TMP]; omega_using [h1]
    · simp at hw
  · rcases hj with rfl | rfl <;> simp only [sl_eq, ACC, PT, TMP] <;> omega_using []
  · rw [hw, bitsAt_eq, sl_eq]; simp only [TMP]; omega_using [h7]
  · rw [hw]; simp only [sl_eq, nslots, TMP]; omega_using []

/-! ## `R = [k]P`, by the call or the ladder -/

/-- `qMul`: for any invariant `Q` of the ladder from the point at `px`, `py`,
`ONEP` that accepts `O`, `Q 0` accepts what `R` holds at the end, for the
scalar `k` at `K`'s slot (for the call) or whose bits are the table (for the
ladder), from `R = O`; only `powClob`, the ladder's slots and `genX` change. -/
theorem qMul_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    {g : Reg → BitVec 32} (F : Fixed c base g s.mem) {px py : Nat} (hp : PtSlots px py)
    (hpx : sv c base s px < c.C.p) (hpy : sv c base s py < c.C.p)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (pLadder c px py) c.C base s k Q c.qA0) (hO : Q (8 * c.C.len) 0 1 0)
    (hk : c.mul.isSome → sv c base s K = k)
    (ht : c.mul = none → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (c.qMul px py) s fun t => Rest powClob s t ∧
      Unch base (VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk ++ genX c) s.mem t.mem ∧
      ModOkW c.MP' size c.C.p t.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal t.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY)) (tmv c.C c.n base t (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hpx])
  obtain tone : toM c.C.p (2 ^ (64 * c.n)) (2 ^ (64 * c.n) % c.C.p) = 1 := toM_one hpR
  unfold Cfg.qMul
  cases hm : c.mul with
  | none =>
    simp only
    obtain hlt : ∀ x ∈ ladR (pLadder c px py), wordsVal s.mem base x c.MP'.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, px, py, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c base s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F.ap (hmont _)
      · exact lt_of_eq_of_lt F.b3p (hmont _)
      · exact hpx
      · exact hpy
      · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega_using [hpx]))
      · exact lt_of_eq_of_lt hrx (by omega_using [hpx])
      · exact lt_of_eq_of_lt hry (hmont _)
      · exact lt_of_eq_of_lt hrz (by omega_using [hpx])
    obtain hR : Q (pLadder c px py).nbits (tmv c.C c.n base s (pLadder c px py).R.x)
        (tmv c.C c.n base s (pLadder c px py).R.y) (tmv c.C c.n base s (pLadder c px py).R.z) := by
      show Q _ (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ))
      rw [hrx, hry, hrz, toM_cmont hc, toM_zero]
      exact hO
    refine WP.mono (VG.Proof.Weierstrass.Arm.Point.ladderP_ok (L := pLadder c px py) (k := k) (a0 := c.qA0) (u := c.umaal)
      (pLadLay hc hp) (pLadWk hc hp) hc.fp (pLadPt hp) hpR (bitsAt_lt hc (j := 0) (by decide)) hs hf
      (modP_of hc F.mp) hlt (fun h => by
        simp only [Cfg.qA0, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2.2) hstep hR (fun t h => ht hm t (Nat.lt_of_lt_of_le h (scalarBits_le hc)))
      (scalarBits_enc hc)) fun t ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩
  | some C =>
    simp only
    obtain hpx' := hp px (List.mem_cons_self)
    obtain hpy' := hp py (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain hpxr : px ∉ [RX, RY] := fun h => hpx'.2.2.2.2 (by
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    obtain hpyr : py ∉ [RX, RY] := fun h => hpy'.2.2.2.2 (by
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    obtain hk' : sv c base s K = k := hk (by rw [hm]; rfl)
    obtain hq : c.qA0 = false := by simp only [Cfg.qA0, hm, Option.isNone_some, Bool.false_and]
    rw [hq] at hstep
    obtain hstep' : Step (pLadder c px py) c.C base s (sv c base s K) Q := by rw [hk']; exact hstep
    obtain hO' : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
        (tmv c.C c.n base s (c.sl ZERO)) := by
      show Q _ (toM _ _ (sv c base s ZERO)) (toM _ _ (sv c base s ONEP)) (toM _ _ (sv c base s ZERO))
      rw [show sv c base s ZERO = 0 from F.zero, show sv c base s ONEP = _ from F.onep, toM_zero, tone]
      exact hO
    refine WP.mono (mulAt_ok (px := px) (py := py) (Q := Q) hc C (hc.mulNf C hm) hs hf hpx'.1 hpy'.1
      hpxr hpyr F.mp (lt_of_eq_of_lt F.ap (hmont _)) (lt_of_eq_of_lt F.b3p (hmont _))
      (lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega_using [hpx]))) (lt_of_eq_of_lt F.zero (by omega_using [hpx])) hpx hpy
      hstep' hO')
      fun t ⟨K, U, L, R⟩ => ⟨K.mono (by simp [powClob, clob]), ?_, ?_, L, R⟩
    · refine U.mono fun w hw => ?_
      simp only [mulFW, mulBW, mulBX, mulSW, genX, List.mem_append] at hw ⊢
      rcases hw with hw | ((hw | hw | hw) | hw)
      · refine .inl ?_
        rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq]
        simp only [slW, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
        obtain ⟨i, hi, rfl⟩ := hw
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, by
          rcases hi with rfl | rfl <;> simp, rfl⟩))
      · exact .inl hw
      · exact .inr (.inl hw)
      · exact .inr (.inr (by rw [List.mem_singleton.mp hw]; exact List.mem_cons_self))
      · exact .inr (.inr (by rw [List.mem_singleton.mp hw]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    · have hmp : wordsVal t.mem base (c.sl MP) c.n = wordsVal s.mem base (c.sl MP) c.n := by
        refine U.wordsVal (fun w hw => .inl ?_) ?_
        · have h12 := sl_lt c (i := MP) (j := TMP) (by decide)
          rcases List.mem_append.mp hw with hw | hw
          · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> exact Nat.le_trans h12 (Nat.le_trans (Nat.le_add_right _ _)
              (sl_lt c (by decide)))
          · exact Nat.le_trans h12 (mulFW_ge h7 w hw)
        · have := sl_le c h7 (i := MP) (by decide); dsimp only [size] at this; omega_using [this]
      exact modP_of hc (hmp.trans F.mp)

end VG.Proof.Ecdsa.Arm

end

end

/-!
# ECDSA on 32-bit ARM: the whole function

`sign_ok`: `Cfg.sign` computes the specification's signature of the hash
with `d` and `k`, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and changes memory only in the working space and `out`. Four
stages, each a lemma, as on x86 (`Proof/Ecdsa/X86/Main.lean`): the
setup and the tables of bits (`stage₁`, in `Stages.lean`), `[k]G` and
`Z^(p-2)` (`stage₂`), `x`, `r`, the checks and `k^(n-2)` (`stage₃`), and
`s`, its check and the result (`stage₄`); `signWith_eq` connects what they
compute to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)

variable {c : Cfg} {A : Args}

/-- The ranges of numbered slots and of the accumulator. -/
abbrev slWk (c : Cfg) (l : List Nat) : List (Nat × Nat) := slW c l ++ [(c.wk, 64 * c.n)]

theorem apart_slWk (h7 : c.n < 10) {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    ∀ w ∈ slWk c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_wk h7 hi)

theorem tbl_apart_slWk (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} :
    ∀ w ∈ slWk c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW h7 hl j t) (tbl_apart_wk h7 j t)

theorem fixedOk_slWk (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slWk c l) :=
  (fixedOk_slW hl).append (fixedOk_wk h7)

theorem slWk_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slWk c l, w.1 + w.2 ≤ size := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_le c h7 (hl i hi)
  · rw [List.mem_singleton.mp hw]
    exact wk_le c h7 (M := c.MP') rfl

theorem flag_le (h0 : 0 < c.n) (h7 : c.n < 10) : ∀ w ∈ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_le c h7 (i := FLAG) (by decide)
  dsimp only
  omega_arith

/-! ### The point functions' slots

For coordinates of at most 6 words, the ladder calls the point functions
(`ladderP_ok`), which also write their slots and own working space (`ptW`),
above every numbered slot and below the tables. -/

theorem apart_ptW {i : Nat} (hi : i < 45) :
    ∀ w ∈ VG.Proof.Weierstrass.Arm.Point.ptW c.n, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]; exact Or.inl (sl_below_pt ‹_› hi)
  · simp at hw

theorem tbl_apart_ptW (j t : Nat) :
    ∀ w ∈ VG.Proof.Weierstrass.Arm.Point.ptW c.n, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw, bitsAt_eq]; have := oAt_le c; dsimp only; omega_arith
  · simp at hw

theorem fixedOk_ptW : FixedOk c (VG.Proof.Weierstrass.Arm.Point.ptW c.n) := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]
    exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_pt ‹_› (i := 12) (by decide)))
  · simp at hw

theorem ptW_le : ∀ w ∈ VG.Proof.Weierstrass.Arm.Point.ptW c.n, w.1 + w.2 ≤ size := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]; have := oAt_le c; dsimp only [size]; omega_arith
  · simp at hw

/-- What the ladder writes: numbered slots, the accumulator and the point
functions' slots. -/
abbrev slWkP (c : Cfg) (l : List Nat) : List (Nat × Nat) := slWk c l ++ VG.Proof.Weierstrass.Arm.Point.ptW c.n

theorem apart_slWkP (h7 : c.n < 10) {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    ∀ w ∈ slWkP c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slWk h7 hi hl) (apart_ptW hi)

theorem tbl_apart_slWkP (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} :
    ∀ w ∈ slWkP c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slWk h7 hl) (tbl_apart_ptW j t)

theorem fixedOk_slWkP (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slWkP c l) :=
  (fixedOk_slWk h7 hl).append fixedOk_ptW

theorem slWkP_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slWkP c l, w.1 + w.2 ≤ size :=
  fun w hw => (List.mem_append.mp hw).elim (slWk_le h7 hl w) (ptW_le w)

/-- After `[k]G` and `Z^(p-2)`. -/
structure St₂ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  flag : flagW c base s = BitVec.allOnes 32
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  acc_lt : sv c base s ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s RZ < c.C.p

/-- The generator multiplication result needed by all later ECDSA stages. -/
def GeneratorPost (c : Cfg) (base : Addr) (k : Nat) (s t : State) : Prop :=
  Rest powClob s t ∧ Unch base (VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk ++ genX c) s.mem t.mem ∧
  ModOkW c.MP' size c.C.p t.mem base ∧
  (∀ x ∈ [c.sl RX,c.sl RY,c.sl RZ],wordsVal t.mem base x c.n<c.C.p) ∧
  Rep c.C (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY))
    (tmv c.C c.n base t (c.sl RZ)) (mul k (G c.C))

/-- The common inversion and state preservation after any verified generator routine. -/
theorem stage₂With (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₁ c A s₀ base s)
    {generator : Prog isa} (hMul : WP isa generator s (GeneratorPost c base (kv c A s₀) s))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq generator (.seq (pow c.powP c.SP c.umaal) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  obtain henc : encodable (BitVec.ofNat 32 (64*c.n))=true := by
    obtain en : ∀ n<10,encodable (BitVec.ofNat 32 (64*n))=true := by decide
    exact en _ h7
  refine WP.seq (WP.mono hMul fun s₅ ⟨K₅,U₅,M₅,L₅,R₅⟩ => ?_)
  rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq] at U₅
  obtain hs₅ := hS.scr.of_rest K₅ (by decide)
  obtain hf₅ := hS.far.of_rest K₅
  obtain F₅ := F.unch h7 hn ((fixedOk_slWkP h7 (by decide)).append (fixedOk_genX h7)) U₅
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) (powWkP hc) hc.fp hpR
    (bitsAt_lt hc (j := 1) (by decide)) hs₅ hf₅ M₅
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht
        (apart_append (tbl_apart_slWkP h7 (by decide)) (tbl_apart_genX h7 (by decide) ht))]
      exact hS.t₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_arith) henc) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWxP_eq] at U₆
  obtain e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] →
      i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] →
      sv c base s₆ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_slWk h7 hi h₁)).trans (sv_unch U₅ h7 hn hi
      (apart_append (apart_slWkP h7 hi h₂) (apart_genX h7 hi fun h => h₁ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega_using [h]))))
  obtain r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_slWk h7 hi h₁)
  obtain K₅₆ : Rest work s s₆ := (K₅.mono powClob_work).trans (K₆.mono powClob_work)
  refine ⟨⟨hs₅.of_rest K₆ (by decide), hf₅.of_rest K₆, hS.rest.trans (K₅₆.mono (by simp)), by rw [K₅₆.gpr _ (by decide), hS.lr],
    F₅.unch h7 hn (fixedOk_slWk h7 (by decide)) U₆,
    whole_of (whole_of' hS.whole U₅ fun w hw => (List.mem_append.mp hw).elim
      (fun h => by have := slWkP_le h7 (by decide) w h; dsimp only [size] at this; omega_using [this]) (genX_le h7 w))
      U₆ (slWk_le h7 (by decide))⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flagW, flag_unch U₆ h7 h0 hn (by decide), Unch.readW32 U₅ (fun w hw => by
        rcases apart_append (apart_slWkP (c := c) h7 (i := FLAG) (by decide) (by decide))
          (apart_genX (c := c) h7 (i := FLAG) (by decide) (by decide)) w hw with h | h
        · exact Or.inl (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)
        · exact Or.inr h) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith),
      ← flagW, hS.flag],
    ?_, ?_, lt₆, ?_, ?_⟩
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_slWk h7 (by decide)),
      tbl_unch U₅ h7 (j := 2) (by decide) ht
        (apart_append (tbl_apart_slWkP h7 (by decide)) (tbl_apart_genX h7 (by decide) ht))]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- After `x`, `r`, the checks and `k^(n-2)`. -/
structure St₃ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  x_lt : sv c base s X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s X) =
    tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rr : sv c base s RR = sv c base s X % c.C.n
  flag : flagW c base s = BitVec.allOnes 32 &&&
    mask32 (0 < dv c A s₀ ∧ dv c A s₀ < c.C.n) &&& mask32 (0 < kv c A s₀ ∧ kv c A s₀ < c.C.n) &&&
    mask32 (sv c base s X % c.C.n ≠ 0)
  acc : toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) = Fin.ofNat c.C.n (kv c A s₀) ^ (c.C.n - 2)

/-- `x`, `r`, `k R mod n` and the checks, then `k^(n-2)`. -/
theorem stage₃ (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₂ c A s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₃ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq c.middle (.seq (pow c.powN c.SN c.umaal) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  obtain henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  refine WP.seq ?_
  rw [middle_eq]
  refine midOps_ok hc hS.scr hS.far (modP_of hc F.mp) (modN_of hc F.mn) hS.acc_lt F.one F.zero F.r2n
    fun s₇ Mp => ?_
  obtain F₇ := F.unch h7 hn (fixedOk_slWk h7 (l := [XM, X, RR, KM, TMP]) (by decide)) Mp.unch
  refine WP.mono (checks_ok hc Mp.scr F₇.mn) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_
  obtain hs₈ := Mp.scr.of_rest k₈ (by decide)
  obtain hf₈ := (hS.far.of_rest Mp.rest).of_rest k₈
  obtain F₈ := F₇.unch h7 hn fixedOk_flag O₈.unch
  obtain e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₇ i := fun hi hf =>
    sv_flag O₈ h0 h7 hn hi hf
  obtain e₇ : ∀ {i}, i < 45 → i ∉ [XM, X, RR, KM, TMP] → sv c base s₇ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slWk h7 hi hl)
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) (powWkN hc) hc.fn hnR
    (bitsAt_lt hc (j := 2) (by decide)) hs₈ hf₈
    (modN_of hc F₈.mn) (lt_of_eq_of_lt (e₈ (i := KM) (by decide) (by decide)) Mp.km_lt) F₈.onen
    (fun t ht => by
      show s₈.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch O₈.unch h7 (j := 2) (by decide) ht (tbl_apart_flag h7 h0 2 t),
        tbl_unch Mp.unch h7 (j := 2) (by decide) ht (tbl_apart_slWk h7 (by decide))]
      exact hS.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith) henc) fun s₉ ⟨K₉, U₉, lt₉, v₉⟩ => h s₉ ?_)
  rw [powWxN_eq] at U₉
  obtain e₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₉ i = sv c base s₈ i := fun hi hl =>
    sv_unch U₉ h7 hn hi (apart_slWk h7 hi hl)
  -- The slots `middle` and the power do not write.
  obtain a₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → i ≠ FLAG → i ∉ [XM, X, RR, KM, TMP] →
      sv c base s₉ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    ((e₉ hi h₁).trans (e₈ hi h₂)).trans (e₇ hi h₃)
  obtain x₉ : sv c base s₉ X = sv c base s₇ X :=
    (e₉ (i := X) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  obtain rr₉ : sv c base s₉ RR = sv c base s₇ RR :=
    (e₉ (i := RR) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  obtain tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₉ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₉ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [a₉ (by decide) (by decide) (by decide) (by decide)]
  obtain K₇₉ : Rest work s s₉ := (Mp.rest.mono callClob_work).trans ((k₈.mono (by decide)).trans (K₉.mono powClob_work))
  refine ⟨⟨hs₈.of_rest K₉ (by decide), hf₈.of_rest K₉, hS.rest.trans (K₇₉.mono (by simp)), by rw [K₇₉.gpr _ (by decide), hS.lr],
    F₈.unch h7 hn (fixedOk_slWk h7 (by decide)) U₉,
    whole_of (whole_of (whole_of hS.whole Mp.unch (slWk_le h7 (by decide))) O₈.unch (flag_le h0 h7)) U₉
      (slWk_le h7 (by decide))⟩,
    by rw [a₉ (i := D) (by decide) (by decide) (by decide) (by decide), hS.d],
    by rw [a₉ (i := E) (by decide) (by decide) (by decide) (by decide), hS.e],
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact hS.rep,
    by rw [x₉]; exact Mp.x_lt,
    by rw [x₉, Mp.x, tR RX (by simp), tR RZ (by simp), hS.acc],
    by rw [rr₉, x₉]; exact Mp.rr, ?_, ?_⟩
  · rw [flagW, flag_unch U₉ h7 h0 hn (by decide), ← flagW, f₈, flagW, flag_unch Mp.unch h7 h0 hn (by decide),
      ← flagW, hS.flag, e₇ (i := D) (by decide) (by decide), e₇ (i := K) (by decide) (by decide), hS.d, hS.k,
      Mp.rr, x₉]
  · refine v₉.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ KM) ^ _ = _
    rw [e₈ (i := KM) (by decide) (by decide), Mp.km, hS.k]

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r1) c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) c.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r3) c.C.len)) with
  | some rs => s'.gpr .r0 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) (2 * c.C.len) = Spec.Ecdsa.encode c.C rs
  | none => s'.gpr .r0 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) (2 * c.C.len) = List.replicate (2 * c.C.len) 0

/-- What the ABI asks for: the callee-saved registers and `lr` restored,
`sp` kept; and memory changed only in the working space, then in `out`. -/
structure SignKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  sp : s'.sp = s₀.sp
  frame : ∃ m : Mem, Unch (scPtr s₀) [(0, 8192)] s₀.mem m ∧ Outside (ptr s₀ .r0) 0 (2 * c.C.len) m s'.mem

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra) {base : Addr} (hb : base = scPtr s₀)
    {s : State} (hS : St₃ c .sign s₀ base s) :
    WP isa c.scalar s fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  rw [scalar_eq]
  refine scalarIn_ok hc hS.scr hS.far (modN_of hc F.mn) F.r2n
    fun s₁₀ hs₁₀ hM₁₀ K₁₀ U₁₀ _ dm em trm tdm tem => ?_
  obtain F₁₀ := F.unch h7 hn (fixedOk_slWk h7 (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₀
  refine scalarOut_ok hc hs₁₀ (hS.far.of_rest K₁₀) hM₁₀ F₁₀.one dm em
    fun s₁₁ hs₁₁ K₁₁ U₁₁ ss_lt ss => ?_
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (checkNonzero_ok c hs₁₁ h0 (sl_le c h7 (i := SS) (by decide)) (by omega_arith))
    fun s₁₂ ⟨f₁₂, k₁₂, O₁₂⟩ => ?_
  obtain hs₁₂ := hs₁₁.of_rest k₁₂ (by decide)
  obtain F₁₂ := (F₁₀.unch h7 hn (fixedOk_slWk h7 (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₁).unch
    h7 hn fixedOk_flag O₁₂.unch
  obtain W₁₂ : Unch base [(0, 8192)] s₀.mem s₁₂.mem :=
    whole_of (whole_of (whole_of hS.whole U₁₀ (slWk_le h7 (by decide))) U₁₁ (slWk_le h7 (by decide)))
      O₁₂.unch (flag_le h0 h7)
  obtain acc₁₀ : sv c base s₁₀ ACC = sv c base s ACC :=
    sv_unch U₁₀ h7 hn (by decide) (apart_slWk h7 (by decide) (by decide))
  obtain rr₁₂ : sv c base s₁₂ RR = sv c base s RR :=
    ((sv_flag O₁₂ h0 h7 hn (i := RR) (by decide) (by decide)).trans
      (sv_unch U₁₁ h7 hn (by decide) (apart_slWk h7 (by decide) (by decide)))).trans
      (sv_unch U₁₀ h7 hn (by decide) (apart_slWk h7 (by decide) (by decide)))
  obtain ss₁₂ : sv c base s₁₂ SS = sv c base s₁₁ SS := sv_flag O₁₂ h0 h7 hn (by decide) (by decide)
  -- The flag.
  obtain hflag : flagW c base s₁₂ =
      mask32 (decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true) := by
    rw [f₁₂, flagW, flag_unch U₁₁ h7 h0 hn (by decide), flag_unch U₁₀ h7 h0 hn (by decide), ← flagW, hS.flag,
      BitVec.allOnes_and, mask32_and, mask32_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  obtain K₁₂' : Rest work s s₁₂ := (K₁₀.mono callClob_work).trans ((K₁₁.mono callClob_work).trans (k₁₂.mono (by decide)))
  obtain K₁₂ : Rest (.lr :: work) s₀ s₁₂ := hS.rest.trans (K₁₂'.mono (by simp))
  obtain lr₁₂ : s₁₂.gpr .lr = s₀.gpr .r0 := by rw [K₁₂'.gpr _ (by decide), hS.lr]
  obtain hw : (⟨State.addr (s₀.gpr .r0), 2 * c.C.len⟩ : Region) ∈ s₁₂.wr := by
    rw [K₁₂.wr, hp.wr]; simp
  refine WP.mono (finish_ok hc hs₁₂ lr₁₂ hp.out_fit hw (hb ▸ hp.out_sc.sub_right (sc_sub s₀)) F₁₂.saved _
    hflag) fun s' ⟨bytes, ret, saved, others, Oout⟩ => ⟨⟨saved, by rw [others.sp, K₁₂.sp],
      ⟨s₁₂.mem, hb ▸ W₁₂, Oout⟩⟩, ?_⟩
  -- The specification.
  obtain hsig := signWith_eq hC (C := c.C) (d := dv c .sign s₀) (e := ev c .sign s₀) (k := kv c .sign s₀) hS.rep hS.x_lt hS.x
    (s := wordsVal s₁₁.mem base (c.sl SS) c.n) ss_lt (by
      rw [ss, trm, tdm, tem, acc₁₀, hS.acc, hS.rr, hS.d, hS.e, Lean.Grind.AddCommMonoid.add_comm])
  unfold SignPost
  obtain he : ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) c.C.len) >>> c.sh = ev c .sign s₀ :=
    congrArg (_ >>> ·) (shAt_self c E).symm
  rw [← dv_eq (A := .sign) (shAt_E_D c), ← kv_eq (A := .sign) (shAt_E_K c), hashToInt_eq c, he, hsig]
  rw [ss₁₂, rr₁₂, hS.rr] at bytes
  by_cases hP : 1 ≤ dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n ∧ 1 ≤ kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n ∧
      sv c base s X % c.C.n ≠ 0 ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega_arith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode]
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega_arith
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd]; rfl

/-- The shared signing pipeline with an interchangeable generator multiplication. -/
theorem signWith_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region}
    (hp : Pre c s₀ extra) {generator : Prog isa}
    (hMul : ∀ s, St₁ c .sign s₀ (scPtr s₀) s → s.syms=s₀.syms →
      WP isa generator s (GeneratorPost c (scPtr s₀) (kv c .sign s₀) s)) :
    WP isa (c.signWith generator) s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  obtain setupRun := stage₁ hc hp.setup (rest := .block [])
    (Q := fun s => St₁ c .sign s₀ (scPtr s₀) s) (fun _ S => WP.block_nil S)
  obtain run := WP.mono_syms setupRun fun s S sy =>
    stage₂With hc S (hMul s S sy) fun _ S₂ => stage₃ hc S₂ fun _ S₃ => stage₄ hc hC hp rfl S₃
  simpa only [Cfg.signWith,Cfg.setup,WP.seq_iff (M := isa),WP.block_nil_iff (M := isa)] using run

/-- `gen`: `R = [k]G`, by the call or the ladder. -/
theorem generator_gen_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {s : State}
    (hS : St₁ c A s₀ base s) : WP isa c.gen s (GeneratorPost c base (kv c A s₀) s) := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  obtain hkl : kv c A s₀ < 2 ^ (8 * c.C.len) :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  obtain hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  obtain hstep := step_rep' (L := pLadder c GX GY) (k := kv c A s₀) (a0 := c.qA0) hC hc.onG (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F.b3p]; exact toM_cmont hc _) hG
    (fun h => ⟨by
      simp only [Impl.Ecdsa.Arm.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.2.1]; rfl, by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F.onep]; exact toM_one hpR⟩)
  refine WP.mono (qMul_ok hc hS.scr hS.far F (px := GX) (py := GY) (by decide)
    (lt_of_eq_of_lt F.gx (hmont _)) (lt_of_eq_of_lt F.gy (hmont _)) hS.rx hS.ry hS.rz hstep
    (by rw [shiftRight_eq_zero hkl, mul_zero_pt]; exact rep_infinity' hC) (fun _ => hS.k)
    (fun _ t ht => hS.t₀ t ht)) fun t ⟨K, U, M, L, R⟩ => ?_
  rw [Nat.shiftRight_zero] at R
  exact ⟨K, U, M, L, R⟩

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature, restores
the callee-saved registers and changes only the working space and `out`. -/
theorem sign_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : Pre c s₀) :
    WP isa c.sign s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' :=
  signWith_ok hc hC hp fun _ S _ => generator_gen_ok hc hC S

end VG.Proof.Ecdsa.Arm
