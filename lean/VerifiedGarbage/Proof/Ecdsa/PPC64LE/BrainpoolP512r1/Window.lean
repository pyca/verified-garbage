module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3A
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step

/-!
# `[k]P` by three-bit windows on PPC64LE, brainpoolP512r1

The curve's kit for `Proof/Ecdsa/PPC64LE/WindowAll.lean`: brainpoolP512r1's field, of eight words, whose
`a` is any (`WAll.AKit.anyA`: `rcb`, `dblJa`, `3 b` at `B3P`), and three-bit windows (`WAll.Kit.w3`), which
give the table and each window. The 512 bits of a scalar are 170 windows and two bits above them, which
would make a 171st window read a bit past the table of bits: `R` starts at the entry of the top two bits
(`top2_ok`, `top2_eq`), `[k >>> 510]Q`, and the 170 windows below are the kit's, so that `R = [k]P` for any
`k < 2^512` (`mul_ok`), on the curve's own statements of a point in slots (`PtOk`), of the constants (`KC`)
and of what it reads (`MPre`), as other modules use them.
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE (brainpoolp512r1_ok)

/-- brainpoolP512r1. -/
abbrev W : Spec.Weierstrass.Curve := Spec.BrainpoolP512r1.curve

/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 8 base s p.x) (tmv W 8 base s p.y) (tmv W 8 base s p.z) P
  x : wordsVal s.mem base p.x 8 < W.p
  y : wordsVal s.mem base p.y 8 < W.p
  z : wordsVal s.mem base p.z 8 < W.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base p.x 8 = wordsVal s.mem base p.x 8)
    (ey : wordsVal s'.mem base p.y 8 = wordsVal s.mem base p.y 8)
    (ez : wordsVal s'.mem base p.z 8 = wordsVal s.mem base p.z 8) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `3 b` in Montgomery's form (`3 b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (brainpoolp512r1.sl AP) 8 = W.a * 2 ^ 512 % W.p
  bp : wordsVal s.mem base (brainpoolp512r1.sl bp) 8 = 3 * W.b * 2 ^ 512 % W.p
  zero : wordsVal s.mem base (brainpoolp512r1.sl ZERO) 8 = 0
  onep : wordsVal s.mem base (brainpoolp512r1.sl ONEP) 8 = 2 ^ 512 % W.p

/-- The slot of `3 b`: the signature's (`B3P`). -/
abbrev B3s : Nat := B3P

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := brainpoolp512r1.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

/-- The table of `k`'s bits, one byte each at `4096`. -/
abbrev Bits (base : Addr) (s : State) (k : Nat) : Prop :=
  ∀ t < 512, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0

/-- The top two bits of a scalar of 512 bits: `k >>> 510`, before the first
of the 170 windows below them. -/
theorem top2_eq {k : Nat} (hk : k < 2 ^ 512) : k >>> 510 = bv (k.testBit 510) + 2 * bv (k.testBit 511) := by
  obtain h4 : k >>> 510 < 4 := by rw [Nat.shiftRight_eq_div_pow]; omega_using [hk]
  obtain t0 : k.testBit 510 = (k >>> 510).testBit 0 := by rw [Nat.testBit_shiftRight]
  obtain t1 : k.testBit 511 = (k >>> 510).testBit 1 := by rw [Nat.testBit_shiftRight]
  rw [t0, t1]
  generalize k >>> 510 = m at h4 ⊢
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega_using [h4]
  rcases this with rfl | rfl | rfl | rfl <;> rfl

theorem horner2_eq (b0 b1 : Bool) :
    BitVec.ofNat 64 (bv b1) + BitVec.ofNat 64 (bv b1) + BitVec.ofNat 64 (bv b0) =
      BitVec.ofNat 64 (bv b0 + 2 * bv b1) := by
  cases b0 <;> cases b1 <;> rfl

/-- The top two bits, `k >>> 510`, into `r9`, from the table of `k`'s bits. -/
theorem top2_ok {s : State} {base : Addr} (hw : WsReg s base) {k : Nat}
    (ht : ∀ t < 512, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0) (hk : k < 2 ^ 512) :
    WP isa (.block (WindowA.Cfg.top2 brainpoolp512r1)) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 (k >>> 510) ∧ Kp [.r5, .r9] s s' ∧ s'.mem = s.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  rw [show WindowA.Cfg.top2 brainpoolp512r1 = [.lbz .r9 .r3 4607, .add .r9 .r9 .r9, .lbz .r5 .r3 4606,
    .add .r9 .r9 .r5] from rfl]
  refine wp_step (lbz_ok (base := base) (size := 8192) hs h3 (by decide) (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact h3) (by decide) (by decide)) ?_
  refine wp_step exec_add (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    rw [show 0 + 4607 = 4096 + 511 from rfl, show 0 + 4606 = 4096 + 510 from rfl,
      ht _ (by decide), ht _ (by decide), byte_bit, byte_bit, top2_eq hk]
    exact horner2_eq _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

/-- What `mul` writes. -/
abbrev mulW : List (Nat × Nat) := [(960, 960), (3584, 512), (5632, 1536)]

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (base : Addr) (s : State) (Q : Point W) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC B3s base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true
  bits : Bits base s k
  lt : k < 2 ^ 512

theorem lok : CfgOk brainpoolp512r1 := brainpoolp512r1_ok

/-- The curve's kit: the 170 windows below the top two bits. -/
def kit : WAll.Kit brainpoolp512r1 :=
  WAll.Kit.w3 (WAll.AKit.anyA lok) (WindowA.Cfg.windows3t brainpoolp512r1) (by decide) (by decide)

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (WindowA.Cfg.mul3top brainpoolp512r1 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY B3s) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt brainpoolp512r1) (mul k Q) := by
  have hn := hp.ws.nowrap
  obtain hkc : WAll.KC brainpoolp512r1 kit.bs kit.bK base s := ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩
  obtain hg : WAll.PtOk brainpoolp512r1 base s (WAll.gPt brainpoolp512r1) Q := ⟨hp.g.rep, hp.g.x, hp.g.y, hp.g.z⟩
  rw [WindowA.Cfg.mul3top, List.append_assoc, List.append_assoc]
  refine WP.seq (WP.mono (WAll.build_ok kit hL ⟨hp.ws, hkc, hg, hp.on⟩) fun s₁ ⟨K₁, U₁, B₁, T₁⟩ => ?_)
  have hw₁ := B₁.ws
  obtain hB₁ : Bits base s₁ k := WAll.Bits.of_unch (c := brainpoolp512r1) (by decide) hp.bits U₁ (by decide)
  -- The top two bits, and their entry in `D`.
  refine WP.seq (WP.block_append (WP.mono (top2_ok hw₁ hB₁ hp.lt) fun s₂ ⟨v₂, k₂, m₂⟩ => ?_))
  obtain hw₂ := hw₁.of_kp k₂
  obtain ha : k >>> 510 < 8 := by have := hp.lt; rw [Nat.shiftRight_eq_div_pow]; omega_using [this]
  refine WP.block_append (WP.mono (WAll.scans_ok (c := brainpoolp512r1) (by decide) (E := 8) (by decide)
    (by decide) ha 8 (Nat.le_refl _) hw₂ v₂) fun s₃ ⟨v₃, k₃, U₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃
  -- `R = D`.
  refine WP.block_append (WP.mono (WAll.copyPt_ok hw₃ (o := Cfg.rPt brainpoolp512r1) (p := Cfg.dPt brainpoolp512r1)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨x₄, y₄, z₄, r₄, U₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp r₄
  refine wp_step (exec_li (imm := 170) (by decide)) (WP.block_nil ?_)
  generalize hs₅ : s₄.write .r31 (BitVec.ofNat 64 170) = s₅
  obtain ku₅ : Kp [.r31] s₄ s₅ := hs₅ ▸ Kp.write _ _ (by decide)
  obtain m₅ : s₅.mem = s₄.mem := by rw [← hs₅]; rfl
  obtain c₅ : s₅.gpr .r31 = BitVec.ofNat 64 170 := by rw [← hs₅, write_gpr]; simp
  obtain hw₅ : WsReg s₅ base := hw₄.of_kp ku₅
  obtain U₅ : Unch base [(960, 384)] s₁.mem s₅.mem := by
    rw [m₅, ← m₂]; exact (U₃.trans U₄).cover (by decide)
  obtain k₅ : ∀ d, d + 64 ≤ 960 ∨ 1344 ≤ d → d + 64 ≤ 8192 → wordsVal s₅.mem base d 8 = wordsVal s₁.mem base d 8 :=
    fun d h h' => U₅.wordsVal (by simp; omega_using [h]) (by omega_using [h'])
  obtain hP : WAll.WFix kit base s₅ Q k :=
    ⟨B₁.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₅ _ (by decide) (by decide),
     T₁.of_eq (E := 8) (fun d (h1 : 5632 ≤ d) (h2 : d + 64 ≤ 7168) =>
       k₅ d (by omega_using [h1]) (by omega_using [h2])) (by decide),
     WAll.Bits.of_unch (c := brainpoolp512r1) (by decide) hB₁ U₅ (by decide), hp.on⟩
  -- `R` is the entry of the top two bits, `[k >>> 510]Q`: `R` before the 170 windows.
  obtain pe := T₁ (k >>> 510) (show k >>> 510 ≤ 7 by omega_using [ha])
  rw [m₂] at v₃
  obtain pR : WAll.PtOk brainpoolp512r1 base s₅ (Cfg.rPt brainpoolp512r1) (mul (k >>> 510) Q) := by
    refine pe.move ?_ ?_ ?_ <;> rw [m₅]
    · rw [x₄]; exact v₃ ha 0 (by decide)
    · rw [y₄]; exact v₃ ha 1 (by decide)
    · rw [z₄]; exact v₃ ha 2 (by decide)
  obtain hI : WAll.WInv kit base s₅ s₅ Q k 170 := ⟨hw₅, c₅, Rk.refl _ _, Unch.refl _ _ _, pR⟩
  refine countLoop_ok (Inv := fun j s' => WAll.WInv kit base s₅ s' Q k j) (n := 170) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => WAll.step_ok kit hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  obtain k₂₅ : Kp [.r4, .r5, .r9, .r10, .r31] s₁ s₅ :=
    (((k₂.mono (by decide)).trans (k₃.mono (by decide))).trans (r₄.mono (by decide))).trans (ku₅.mono (by decide))
  have hr := hi.rep
  exact ⟨((rk_mono K₁).trans (rk_of_kp k₂₅)).trans hi.keep, ((U₁.trans U₅).trans hi.unch).cover (by decide),
    ⟨hr.rep, hr.x, hr.y, hr.z⟩⟩

end VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1
