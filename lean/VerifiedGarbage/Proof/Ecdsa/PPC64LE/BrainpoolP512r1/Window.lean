module

-- separate module: its proofs (about 8 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.Window
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3A
public import VerifiedGarbage.Proof.Weierstrass.JacDblA
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step


/-!
# `[k]P` by three-bit windows on PPC64LE, brainpoolP512r1

The proof of `Proof/Ecdsa/PPC64LE/P256/Window.lean` for brainpoolP512r1's three-bit
windows for any `a` (`Impl/Ecdsa/PPC64LE/Window3A.lean`), as
`Proof/Ecdsa/PPC64LE/P521/Window.lean` is for P-521's: brainpoolP512r1's
coordinates are eight words (slots of 64 bytes), so that the table has eight
entries of 192 bytes from `bitsAt 8 3 = 5632`. As for the four-bit windows of
`BrainpoolP384r1/Window.lean`, the doublings and the addition are those for
any `a` (`dblJa`, `InvJ.dblA'`; `rcb`, `Rep.add`), with `a` and `3 b` (at
`B3P`) in Montgomery's form. The 512 bits of a scalar are 170 windows and
two bits above them, which would make a 171st window read a bit past the
table of bits: `R` starts at the entry of the top two bits
(`top2_ok`, `top2_eq`), `[k >>> 510]Q`, and each of the 170 windows below
is `R = 8 R` (three doublings, `quad_ok`) and the addition of entry `k_j`
(`nibble_ok`, `nib3_eq`), so that `R = [k]P` for any `k < 2^512`
(`mul_ok`, by `wstep` with 8). The lemmas that do not depend on the curve,
the layout or the window's width (`ofN_ok`, the masks) are P-256's.
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

/-- `8 P`, by three doublings. -/
abbrev d8 {C : Spec.Weierstrass.Curve} (P : Point C) : Point C := d2 (d2 (d2 P))

section
variable {C : Spec.Weierstrass.Curve}

/-- `R` before window `j - 1`: `[k >>> 3 j]P`. -/
abbrev wpt (Q : Point C) (k j : Nat) : Point C := mul (k >>> (3 * j)) Q

theorem shr_three (k j : Nat) : k >>> (3 * j) = 8 * (k >>> (3 * (j + 1))) + (k >>> (3 * j)) % 8 := by
  rw [show 3 * (j + 1) = 3 * j + 3 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (k >>> (3 * j)) 3]
  omega

/-- A window: `8 R + [k_j]Q`, for `R` before it, is `R` after it. -/
theorem wstep (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (k j : Nat) :
    Spec.Weierstrass.add (d8 (wpt Q k (j + 1))) (mul ((k >>> (3 * j)) % 8) Q) = wpt Q k j := by
  have ek := shr_three k j
  simp only [wpt, d8, d2]
  generalize (k >>> (3 * j)) % 8 = a at ek ⊢
  rw [ek]
  generalize k >>> (3 * (j + 1)) = m
  have hX := hL.onCurve_mul hQ m
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  have h8 := hL.onCurve_add h4 h4
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h8 (hL.onCurve_mul hQ _)) (hL.onCurve_mul hQ _)
  rw [hf.add h8 (hL.onCurve_mul hQ _), hf.add h4 h4, hf.add h2 h2, hf.add hX hX,
    hf.mul hQ, hf.mul hQ, hf.mul hQ]
  have hu : ((8 * m + a : Nat) : Int) = m + m + m + m + m + m + m + m + a := by omega
  rw [hu]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

/-- The top two bits of a scalar of 512 bits: `k >>> 510`, before the first
of the 170 windows below them. -/
theorem top2_eq {k : Nat} (hk : k < 2 ^ 512) : k >>> 510 = bv (k.testBit 510) + 2 * bv (k.testBit 511) := by
  have h4 : k >>> 510 < 4 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have t0 : k.testBit 510 = (k >>> 510).testBit 0 := by rw [Nat.testBit_shiftRight]
  have t1 : k.testBit 511 = (k >>> 510).testBit 1 := by rw [Nat.testBit_shiftRight]
  rw [t0, t1]
  generalize k >>> 510 = m at h4 ⊢
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

theorem horner2_eq (b0 b1 : Bool) :
    BitVec.ofNat 64 (bv b1) + BitVec.ofNat 64 (bv b1) + BitVec.ofNat 64 (bv b0) =
      BitVec.ofNat 64 (bv b0 + 2 * bv b1) := by
  cases b0 <;> cases b1 <;> rfl

end

/-- The table of `k`'s bits, one byte each at `4096`. -/
abbrev Bits (base : Addr) (s : State) (k : Nat) : Prop :=
  ∀ t < 512, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0

theorem Bits.of_unch {base : Addr} {s s' : State} {k : Nat} (h : Bits base s k)
    {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem) (hW : ∀ w ∈ W, w.1 + w.2 ≤ 4096 ∨ 4608 ≤ w.1) :
    Bits base s' k := fun t ht => by
  rw [hU.byte (fun w hw => by have := hW w hw; omega) (by omega)]; exact h t ht

theorem nib3_eq (k j : Nat) : (k >>> (3 * j)) % 8 = bv (k.testBit (3 * j)) + 2 * bv (k.testBit (3 * j + 1)) +
    4 * bv (k.testBit (3 * j + 2)) := by
  have t : ∀ i, k.testBit (3 * j + i) = decide ((k >>> (3 * j)) / 2 ^ i % 2 = 1) := fun i => by
    rw [← Nat.testBit_shiftRight, Nat.testBit_eq_decide_div_mod_eq]
  rw [show 3 * j = 3 * j + 0 from rfl, t 0, t 1, t 2]
  generalize k >>> (3 * j) = m
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, show (2 : Nat) ^ 2 = 4 from rfl, bv]
  split <;> split <;> split <;> simp_all <;> omega

theorem horner3_eq (b0 b1 b2 : Bool) :
    let x1 := BitVec.ofNat 64 (bv b2) + BitVec.ofNat 64 (bv b2) + BitVec.ofNat 64 (bv b1)
    x1 + x1 + BitVec.ofNat 64 (bv b0) = BitVec.ofNat 64 (bv b0 + 2 * bv b1 + 4 * bv b2) := by
  cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-- brainpoolP512r1. -/
abbrev W : Spec.Weierstrass.Curve := Spec.BrainpoolP512r1.curve

theorem unit : UnitMod W.p (2 ^ (64 * 8)) := unitMod_pow_two (by decide) _

/-! ## The slots -/

/-- The field: brainpoolP512r1's prime, of nine words. -/
abbrev FP : Impl.Weierstrass.Mont.Modulus := brainpoolp512r1.SP

instance : NeZero FP.m := ⟨by decide⟩

theorem fp_ok : ModOk FP.k FP.m := brainpoolp512r1_ok.fp

theorem fp_m : FP.m = W.p := rfl

/-- The slots the windows' arithmetic may use: those at multiples of 64 from
zero's (past `p` and the temporary) up to the functions' own working space. -/
abbrev wS (x : Nat) : Prop := x % 64 = 0 ∧ 256 ≤ x ∧ x + 64 ≤ 3584

theorem wLay : Lay brainpoolp512r1.MP' (own brainpoolp512r1.MP'.n) wS :=
  ⟨fun x h => h.2.2, fun x y hx hy hne => by
    obtain ⟨h1, -, -⟩ := hx; obtain ⟨h2, -, -⟩ := hy
    show x + 8 * 8 ≤ y ∨ y + 8 * 8 ≤ x; omega,
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 8 ≤ 64 ∨ 64 + 8 * 8 ≤ x; omega,
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 8 ≤ 192 ∨ 192 + 8 * 8 ≤ x; omega⟩

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

theorem PtOk.move {base : Addr} {s s' : State} {p o : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base o.x 8 = wordsVal s.mem base p.x 8)
    (ey : wordsVal s'.mem base o.y 8 = wordsVal s.mem base p.y 8)
    (ez : wordsVal s'.mem base o.z 8 = wordsVal s.mem base p.z 8) : PtOk base s' o P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `3 b` in Montgomery's form (`3 b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (brainpoolp512r1.sl AP) 8 = W.a * 2 ^ 512 % W.p
  bp : wordsVal s.mem base (brainpoolp512r1.sl bp) 8 = 3 * W.b * 2 ^ 512 % W.p
  zero : wordsVal s.mem base (brainpoolp512r1.sl ZERO) 8 = 0
  onep : wordsVal s.mem base (brainpoolp512r1.sl ONEP) 8 = 2 ^ 512 % W.p

theorem KC.of_eq {bp : Nat} {base : Addr} {s s' : State} (h : KC bp base s)
    (e : ∀ d ∈ [brainpoolp512r1.sl AP, brainpoolp512r1.sl bp, brainpoolp512r1.sl ZERO, brainpoolp512r1.sl ONEP],
      wordsVal s'.mem base d 8 = wordsVal s.mem base d 8) : KC bp base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero,
    (e _ (by simp)).trans h.onep⟩

/-! ## `R = 8 R` -/

/-- The slot of `3 b`: the signature's (`B3P`). -/
abbrev B3s : Nat := B3P

/-- The complete addition's and the doublings' slots. -/
abbrev S3 : RcbSlots := Cfg.slots brainpoolp512r1 B3s

theorem S3_eq : S3 = ⟨448, 512, 1536, 1600, 1664, 1728, 1792, 1856⟩ := rfl
theorem rPt_eq : Cfg.rPt brainpoolp512r1 = ⟨960, 1024, 1088⟩ := rfl
theorem dPt_eq : Cfg.dPt brainpoolp512r1 = ⟨1152, 1216, 1280⟩ := rfl
theorem tPt_eq : Cfg.tPt brainpoolp512r1 = ⟨1344, 1408, 1472⟩ := rfl
theorem zeroPt_eq : Cfg.zeroPt brainpoolp512r1 = ⟨256, 256, 256⟩ := rfl

theorem dblJ_apart_DT : RcbApart S3 (Cfg.dPt brainpoolp512r1) (Cfg.dPt brainpoolp512r1) (Cfg.tPt brainpoolp512r1) := ⟨by decide, by decide⟩
theorem dblJ_apart_TD : RcbApart S3 (Cfg.tPt brainpoolp512r1) (Cfg.tPt brainpoolp512r1) (Cfg.dPt brainpoolp512r1) := ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S3 (Cfg.rPt brainpoolp512r1) (Cfg.zeroPt brainpoolp512r1) (Cfg.dPt brainpoolp512r1) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S3 (Cfg.tPt brainpoolp512r1) (Cfg.zeroPt brainpoolp512r1) (Cfg.rPt brainpoolp512r1) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S3 p p o)
    (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p p, wS x) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 8 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 p p, x ∈ V)
    (ha : E (brainpoolp512r1.sl AP) = Fin.ofNat W.p W.a) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog FP (dblJa S3 p o)) s fun s' => KeepR 8 (fun x => x) base (rcbW S3 o) s s' ∧
      ∃ E', Inv 8 base W.p wS ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S3 o → E' x = E x := by
  rw [dblJa_eq]
  refine WP.mono (ofN_ok (S' := FP) (M := brainpoolp512r1.MP') fp_ok rfl wLay unit dblJaN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dblA' hL hP hJ ha (v.trans (dblJaN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 8 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (Cfg.rPt brainpoolp512r1) (Cfg.zeroPt brainpoolp512r1), x ∈ V) {P : Point W}
    (hR : Rep W (E 960) (E 1024) (E 1088) P) (hz : E 256 = 0) :
    WP isa (fprog FP (toJ S3 (Cfg.rPt brainpoolp512r1) (Cfg.zeroPt brainpoolp512r1) (Cfg.dPt brainpoolp512r1))) s fun s' =>
      KeepR 8 (fun x => x) base (rcbW S3 (Cfg.dPt brainpoolp512r1)) s s' ∧
      ∃ E', Inv 8 base W.p wS ([1152, 1216, 1280] ++ V) E' s' ∧
        InvJ W (E' 1152) (E' 1216) (E' 1280) P ∧
        ∀ x, x ∉ rcbW S3 (Cfg.dPt brainpoolp512r1) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (S' := FP) (M := brainpoolp512r1.MP') fp_ok rfl wLay unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `T` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 8 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (Cfg.tPt brainpoolp512r1) (Cfg.zeroPt brainpoolp512r1), x ∈ V) :
    WP isa (fprog FP (fromJ S3 (Cfg.tPt brainpoolp512r1) (Cfg.zeroPt brainpoolp512r1) (Cfg.rPt brainpoolp512r1))) s fun s' =>
      KeepR 8 (fun x => x) base (rcbW S3 (Cfg.rPt brainpoolp512r1)) s s' ∧
      ∃ E', Inv 8 base W.p wS ([960, 1024, 1088] ++ V) E' s' ∧
        (E' 960, E' 1024, E' 1088) = (E 1344 * E 1472, E 1408 + E 256, E 1472 * E 1472 * E 1472) ∧
        ∀ x, x ∉ rcbW S3 (Cfg.rPt brainpoolp512r1) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (S' := FP) (M := brainpoolp512r1.MP') fp_ok rfl wLay unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- What `R = 8 R` writes: `R`, `D`, `T`, the temporaries and the
functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(960, 960), (3584, 512)]

/-- The slots its field operations write. -/
abbrev quadWl : List Nat := [1536, 1600, 1664, 1728, 1792, 1856, 960, 1024, 1088, 1152, 1216, 1280, 1344, 1408, 1472]

/-- `R = 8 R`, for `R` representing `P`. -/
theorem quad_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC B3s base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (Cfg.rPt brainpoolp512r1) P) :
    WP isa (WindowA.Cfg.trip brainpoolp512r1 B3s) s fun s' => Rk fnClob s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (Cfg.rPt brainpoolp512r1) (d8 P) := by
  have hp0 : 0 < W.p := by decide
  have hn := hw.nowrap
  rw [WindowA.Cfg.trip]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  have hI : Inv 8 base W.p wS [448, 512, 256, 960, 1024, 1088]
      (fun x => toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base x 8)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.zero hp0
    exacts [hR.x, hR.y, hR.z]
  have e0 : toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base 256 8) = 0 := by
    rw [show wordsVal s.mem base 256 8 = 0 from hK.zero]; exact toM_zero _ _
  have a0 : toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base (brainpoolp512r1.sl AP) 8) = Fin.ofNat W.p W.a := by
    rw [hK.ap, toM_mont unit]
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  have a1 : E₁ (brainpoolp512r1.sl AP) = Fin.ofNat W.p W.a := by rw [p₁ _ (by decide)]; exact a0
  -- Three doublings.
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_DT (by decide) I₁ (by decide) a1 hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  have a2 : E₂ (brainpoolp512r1.sl AP) = Fin.ofNat W.p W.a := by rw [p₂ _ (by decide)]; exact a1
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_TD (by decide) I₂ (by decide) a2 (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  have a3 : E₃ (brainpoolp512r1.sl AP) = Fin.ofNat W.p W.a := by rw [p₃ _ (by decide)]; exact a2
  have h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_DT (by decide) I₃ (by decide) a3 h4 J₃)
    fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  -- Back to projective coordinates.
  refine WP.seq (WP.mono (fromJStep_ok I₅ (by decide)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  have z₅ : E₅ 256 = 0 := by
    rw [p₅ _ (by decide), p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  have ltx := I₆.lt 960 (by decide)
  have lty := I₆.lt 1024 (by decide)
  have ltz := I₆.lt 1088 (by decide)
  have vx' : tmv W 8 base s₆ 960 = E₆ 960 := I₆.val 960 (by decide)
  have vy' : tmv W 8 base s₆ 1024 = E₆ 1024 := I₆.val 1024 (by decide)
  have vz' : tmv W 8 base s₆ 1088 = E₆ 1088 := I₆.val 1088 (by decide)
  have KK : KeepR 8 (fun x => x) base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base quadW s.mem s₆.mem := Unch.cover (W := quadWl.map (fun w => (w, 8 * 8)) ++ [(own 8, 64 * 8)])
    KK.mem (by decide)
  have onep₆ : wordsVal s₆.mem base 384 8 = 2 ^ 512 % W.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  -- `Y = 1` where `Z = 0`: the mask of `Z ≠ 0`, then the selection.
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok brainpoolp512r1 hw₆.ws hw₆.at3 (a := 1088) (by decide) (by decide) (by decide))
    fun s₇ ⟨g₇, k₇, m₇⟩ => ?_)
  rw [List.singleton_append]
  refine wp_step exec_logic ?_
  have hc : (s₇.write .r10 (s₇.gpr .r5 ||| s₇.gpr .r5)).gpr .r10 =
      if decide (wordsVal s₆.mem base 1088 8 ≠ 0) then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true, BitVec.or_self, g₇, mask64, decide_eq_true_eq]; rfl
  have hw₇ := (k₇.ws hw₆.ws).write .r10 (s₇.gpr .r5 ||| s₇.gpr .r5)
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base 1088 8 ≠ 0)) 8 hw₇ ((k₇.at hw₆.at3).write _) hc
    (o := 1024) (a := 384) (b := 1024) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr (by decide)) (Or.inl (Nat.le_refl _))) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  simp only [write_mem] at e₈ O₈
  rw [m₇] at e₈ O₈
  have ex : wordsVal s₈.mem base 960 8 = wordsVal s₆.mem base 960 8 := O₈.wordsVal (by decide) (by omega)
  have ez : wordsVal s₈.mem base 1088 8 = wordsVal s₆.mem base 1088 8 := O₈.wordsVal (by decide) (by omega)
  have hZ : (wordsVal s₆.mem base 1088 8 ≠ 0) ↔ E₅ 1472 ≠ 0 := by
    rw [ne_eq, ne_eq, ← toM_eq_zero_iff unit ltz]
    show ¬tmv W 8 base s₆ 1088 = 0 ↔ _
    rw [vz', vz]
    exact not_congr ⟨fun h => Classical.byContradiction fun hz => cube_ne_zero hL hz h,
      fun h => by rw [h]; grind⟩
  have hrep := InvJ.out hL J₅
  have sub : ∀ r ∈ [Reg.r4, .r5], r ∈ fnClob := by decide
  have rk : Rk fnClob s s₈ := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have h10 : r ≠ Reg.r10 := fun h => hr (h ▸ by decide)
      rw [k₈.gpr r (fun h => hr (sub r h)), write_gpr]
      simp only [h10, ↓reduceIte]
      rw [k₇.gpr r (fun h => hr (sub r h)), KK.gpr r hr]
    · rw [k₈.rd, write_rd, k₇.rd, KK.rd]
    · rw [k₈.wr, write_wr, k₇.wr, KK.wr]
    · rw [k₈.sp, write_sp, k₇.sp, KK.sp]
  refine ⟨rk, (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (tmv W 8 base s₈ 960) (tmv W 8 base s₈ 1024) (tmv W 8 base s₈ 1088) _
    simp only [tmv]
    rw [ex, ez]
    show Rep W (tmv W 8 base s₆ 960) _ (tmv W 8 base s₆ 1088) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ 1472 = 0
    · have hc : decide (wordsVal s₆.mem base 1088 8 ≠ 0) = false :=
        decide_eq_false fun h => (hZ.mp h) h0
      have h0' : E₅ (Cfg.tPt brainpoolp512r1).z = 0 := h0
      rw [show (if E₅ (Cfg.tPt brainpoolp512r1).z = 0 then (1 : Fe W) else E₅ (Cfg.tPt brainpoolp512r1).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [onep₆, toM_one unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base 1088 8 ≠ 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : ¬E₅ (Cfg.tPt brainpoolp512r1).z = 0 := h0
      rw [show (if E₅ (Cfg.tPt brainpoolp512r1).z = 0 then (1 : Fe W) else E₅ (Cfg.tPt brainpoolp512r1).y) =
        E₅ (Cfg.tPt brainpoolp512r1).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      show Rep W _ (tmv W 8 base s₆ 1024) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base 960 8 < W.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base 1024 8 < W.p
    rw [e₈]; split
    · exact lty
    · rw [onep₆]; exact Nat.mod_lt _ (by decide)
  · show wordsVal s₈.mem base 1088 8 < W.p
    rw [ez]; exact ltz

/-! ## The complete addition -/

/-- What an addition writes. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW S3 o).map (fun w => (w, 8 * 8)) ++ [(own 8, 64 * 8)]

/-- `o = p + q` by the complete addition, for points in slots of `wS`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC B3s base s)
    {p q o : Pt} (hA : RcbApart S3 p q o) (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p q, wS x)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (fprog FP (rcb S3 p q o)) s fun s' =>
      Rk fnClob s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  have hI : Inv 8 base W.p wS (rcbR S3 p q) (fun x => toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base x 8)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (S' := FP) (M := brainpoolp512r1.MP') fp_ok rfl wLay unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁, _⟩ => ?_
  have eb : toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base (brainpoolp512r1.sl B3s) 8) = Fin.ofNat W.p (3 * W.b) := by
    rw [hK.bp, toM_mont unit]
  have ea : toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base (brainpoolp512r1.sl AP) 8) = Fin.ofNat W.p W.a := by
    rw [hK.ap, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base x 8)) = E at I₁ t₁
  have hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb S3 p q o) E o.x)
    (Y3 := runOps (rcb S3 p q o) E o.y) (Z3 := runOps (rcb S3 p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← eb, ← ea]
      exact t₁.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW S3 o ++ rcbR S3 p q :=
    fun x hx => List.mem_append_left _ (by simp only [rcbW] at hx ⊢; simp_all)
  refine ⟨⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩, k₁.mem,
    ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 8 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 8 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 8 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep


/-! ## Copies -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 4 = 0 ∧ x + 64 ≤ 8192)
    (hxy : o.x + 64 ≤ o.y) (hyz : o.y + 64 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 64 ≤ o.x ∨ o.z + 64 ≤ a) :
    WP isa (.block (Cfg.copyPt brainpoolp512r1 o p)) s fun s' =>
      wordsVal s'.mem base o.x 8 = wordsVal s.mem base p.x 8 ∧ wordsVal s'.mem base o.y 8 = wordsVal s.mem base p.y 8 ∧
      wordsVal s'.mem base o.z 8 = wordsVal s.mem base p.z 8 ∧ Kp [.r4] s s' ∧
      Unch base [(o.x, 64), (o.y, 64), (o.z, 64)] s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => h8 x hx
  have gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, Point.copyPt, show brainpoolp512r1.n = 8 from rfl, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 8 hw.ws hw.at3 (o := o.x) (a := p.x) ox8 px8 (by omega) (by omega)
    (by omega)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_kp r₁
  refine WP.block_append (WP.mono (copy_ok 8 hw₁.ws hw₁.at3 (o := o.y) (a := p.y) oy8 py8 (by omega) (by omega)
    (by omega)) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_kp r₂
  refine WP.mono (copy_ok 8 hw₂.ws hw₂.at3 (o := o.z) (a := p.z) oz8 pz8 (by omega) (by omega) (by omega))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃, ?_⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · rw [O₃.wordsVal (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega)]
  · rw [e₃, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-! ## The table -/

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := Cfg.entry brainpoolp512r1 e

theorem ent_eq (e : Nat) : ent e = ⟨5632 + 192 * e, 5632 + 192 * e + 64, 5632 + 192 * e + 128⟩ := rfl

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := brainpoolp512r1.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

theorem gPt_eq : gPt = ⟨2496, 2816, 384⟩ := rfl

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop := ∀ e ≤ m, PtOk base s (ent e) (mul e Q)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point W} {m : Nat} (h : TabTo base s Q m)
    (he : ∀ d, 5632 ≤ d → d + 64 ≤ 7168 → wordsVal s'.mem base d 8 = wordsVal s.mem base d 8) (hm : m ≤ 7) :
    TabTo base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (5632 + 192 * e) (by omega) (by omega))
    (he (5632 + 192 * e + 64) (by omega) (by omega)) (he (5632 + 192 * e + 128) (by omega) (by omega))

/-- What the table's additions write: `D`, `T`, the temporaries, the
functions' own working space and the table. -/
abbrev addsW : List (Nat × Nat) := [(1152, 768), (3584, 512), (5632, 1536)]

theorem rcbW_S3 (o : Pt) : rcbW S3 o = [1536, 1600, 1664, 1728, 1792, 1856, o.x, o.y, o.z] := rfl

/-- What the table's construction reads and keeps: the constants and `P`. -/
structure BPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  kc : KC B3s base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true

theorem far_addsW {d : Nat} (h : d + 64 ≤ 1152 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584)) :
    ∀ w ∈ addsW, d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> (simp only; omega)

theorem BPre.of_eq {base : Addr} {s s' : State} {Q : Point W} (h : BPre base s Q) (hw : WsReg s' base)
    (e : ∀ d, d + 64 ≤ 1152 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584) → wordsVal s'.mem base d 8 = wordsVal s.mem base d 8) :
    BPre base s' Q :=
  ⟨hw, h.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact e _ (by decide),
    h.g.of_eq (e _ (by decide)) (e _ (by decide)) (e _ (by decide)), h.on⟩

/-- The additions of `[e]Q` for `e = 2 … m + 1`, from `D = Q`: `D = [m + 1]Q`. -/
theorem adds_ok (hL : Law W) {base : Addr} {Q : Point W} :
    ∀ m ≤ 6, ∀ {s : State}, BPre base s Q → TabTo base s Q 1 → PtOk base s (Cfg.dPt brainpoolp512r1) Q →
      WP isa (WindowA.Cfg.adds brainpoolp512r1 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY B3s m) s fun s' =>
        Rk fnClob s s' ∧ Unch base addsW s.mem s'.mem ∧ BPre base s' Q ∧ TabTo base s' Q (m + 1) ∧
          PtOk base s' (Cfg.dPt brainpoolp512r1) (mul (m + 1) Q)
  | 0, _, s, hp, hT, hD => WP.block_nil ⟨Rk.refl _ _, Unch.refl _ _ _, hp, hT, by rw [mul_one']; exact hD⟩
  | m + 1, hm, s, hp, hT, hD => by
    rw [WindowA.Cfg.adds]
    refine WP.seq (WP.mono (adds_ok hL m (by omega_arith) hp hT hD) fun s₁ ⟨k₁, U₁, B₁, T₁, D₁⟩ => ?_)
    have hn := B₁.ws.nowrap
    -- `T = D + Q`.
    refine WP.seq (WP.mono (addPt_ok hL B₁.ws B₁.kc (p := Cfg.dPt brainpoolp512r1) (q := gPt) (o := Cfg.tPt brainpoolp512r1)
      ⟨by decide, by decide⟩ (by decide) (hL.onCurve_mul B₁.on _) B₁.on D₁ B₁.g) fun s₂ ⟨k₂, U₂, p₂⟩ => ?_)
    rw [mul_succ' hL B₁.on] at p₂
    have hw₂ := B₁.ws.of_rk k₂
    -- Entry `m + 2` and `D`.
    have hm2 : m + 2 < 8 := by omega_arith
    refine WP.block_append (WP.mono (copyPt_ok hw₂ (o := ent (m + 2)) (p := Cfg.tPt brainpoolp512r1)
      (by rw [ent_eq, tPt_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega_arith)
      (by rw [ent_eq]; try omega_arith) (by rw [ent_eq]; try omega_arith)
      (by rw [ent_eq, tPt_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl) <;> omega_arith))
      fun s₃ ⟨x₃, y₃, z₃, k₃, U₃⟩ => ?_)
    have hw₃ := hw₂.of_kp k₃
    refine WP.mono (copyPt_ok hw₃ (o := Cfg.dPt brainpoolp512r1) (p := Cfg.tPt brainpoolp512r1) (by decide) (by decide) (by decide)
      (by decide)) fun s₄ ⟨x₄, y₄, z₄, k₄, U₄⟩ => ?_
    have hw₄ := hw₃.of_kp k₄
    rw [ent_eq] at U₃ x₃ y₃ z₃
    rw [dPt_eq] at U₄ x₄ y₄ z₄
    rw [tPt_eq] at x₃ y₃ z₃ x₄ y₄ z₄
    simp only at U₃ U₄ x₃ y₃ z₃ x₄ y₄ z₄
    have U₃₄ : Unch base [(5632 + 192 * (m + 2), 192), (1152, 192)] s₂.mem s₄.mem :=
      (U₃.trans U₄).cover fun w hw => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., by simp only; omega_arith, by simp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_self .., by simp only; omega_arith, by simp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_self .., by simp only; omega_arith, by simp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_arith, by simp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_arith, by simp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_arith, by simp only; omega_arith⟩
    have hU : Unch base addsW s.mem s₄.mem := by
      refine ((U₁.trans U₂).trans U₃₄).cover fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
        · have := (by decide : ∀ w ∈ addW (Cfg.tPt brainpoolp512r1), ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) w hw
          exact this
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨(5632, 1536), by simp, by simp only; omega_arith, by simp only; omega_arith⟩
        · exact ⟨(1152, 768), by simp, by simp only; omega_arith, by simp only; omega_arith⟩
    -- What each part leaves apart.
    have f₂ : ∀ d, d + 64 ≤ 1344 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584) ∨ 4096 ≤ d → d + 64 ≤ 8192 →
        wordsVal s₂.mem base d 8 = wordsVal s₁.mem base d 8 := fun d h h' =>
      U₂.wordsVal (fun w hw => by
        have := (by decide : ∀ w ∈ addW (Cfg.tPt brainpoolp512r1), 1344 ≤ w.1 ∧ w.1 + w.2 ≤ 1920 ∨ w = (3584, 512)) w hw
        rcases this with h1 | rfl
        · omega_arith
        · simp only; omega_arith) (by omega_arith)
    have f₄ : ∀ d, (d + 64 ≤ 1152 ∨ 1344 ≤ d) → (d + 64 ≤ 5632 + 192 * (m + 2) ∨ 5632 + 192 * (m + 2) + 192 ≤ d) →
        d + 64 ≤ 8192 → wordsVal s₄.mem base d 8 = wordsVal s₂.mem base d 8 := fun d h h2 h' =>
      U₃₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> (simp only; omega_arith)) (by omega_arith)
    have B₄ : BPre base s₄ Q := B₁.of_eq hw₄ fun d hd => by
      rw [f₄ d (by omega_arith) (by omega_arith) (by omega_arith), f₂ d (by omega_arith) (by omega_arith)]
    refine ⟨(k₁.trans (k₂.mono (by decide))).trans ⟨fun r hr => ?_, ?_, ?_, ?_⟩, hU, B₄, fun e he => ?_, ?_⟩
    · rw [k₄.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)),
        k₃.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide))]
    · rw [k₄.rd, k₃.rd]
    · rw [k₄.wr, k₃.wr]
    · rw [k₄.sp, k₃.sp]
    · rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := T₁ e (by omega_arith)
        rw [ent_eq] at pe ⊢
        refine pe.of_eq ?_ ?_ ?_ <;> simp only
        · rw [f₄ _ (by omega_arith) (by omega_arith) (by omega_arith), f₂ _ (by omega_arith) (by omega_arith)]
        · rw [f₄ _ (by omega_arith) (by omega_arith) (by omega_arith), f₂ _ (by omega_arith) (by omega_arith)]
        · rw [f₄ _ (by omega_arith) (by omega_arith) (by omega_arith), f₂ _ (by omega_arith) (by omega_arith)]
      · obtain rfl : e = m + 2 := by omega_arith
        rw [ent_eq]
        refine p₂.move ?_ ?_ ?_ <;> rw [tPt_eq] <;> simp only
        · rw [U₄.wordsVal (by simp; omega_arith) (by omega_arith), x₃]
        · rw [U₄.wordsVal (by simp; omega_arith) (by omega_arith), y₃]
        · rw [U₄.wordsVal (by simp; omega_arith) (by omega_arith), z₃]
    · rw [show m + 1 + 1 = m + 2 by omega_arith]
      refine p₂.move ?_ ?_ ?_ <;> rw [dPt_eq, tPt_eq] <;> simp only
      · rw [x₄, ← U₃.wordsVal (by simp; omega_arith) (by omega_arith)]
      · rw [y₄, ← U₃.wordsVal (by simp; omega_arith) (by omega_arith)]
      · rw [z₄, ← U₃.wordsVal (by simp; omega_arith) (by omega_arith)]

/-- The table of `[e]Q`, for `e < 16`, and `D = [15]Q`. -/
theorem build_ok (hL : Law W) {base : Addr} {Q : Point W} {s : State} (hp : BPre base s Q) :
    WP isa (WindowA.Cfg.build3 brainpoolp512r1 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY B3s) s fun s' =>
      Rk fnClob s s' ∧ Unch base addsW s.mem s'.mem ∧ BPre base s' Q ∧ TabTo base s' Q 7 := by
  have hw := hp.ws
  have hn := hw.nowrap
  have hp0 : 0 < W.p := by decide
  rw [WindowA.Cfg.build3, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw (o := ent 0) (p := brainpoolp512r1.pt ZERO ONEP ZERO) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨x₁, y₁, z₁, k₁, U₁⟩ => ?_))
  have hw₁ := hw.of_kp k₁
  refine WP.block_append (WP.mono (copyPt_ok hw₁ (o := ent 1) (p := gPt) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, k₂, U₂⟩ => ?_)
  have hw₂ := hw₁.of_kp k₂
  refine WP.mono (copyPt_ok hw₂ (o := Cfg.dPt brainpoolp512r1) (p := gPt) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨x₃, y₃, z₃, k₃, U₃⟩ => ?_
  have hw₃ := hw₂.of_kp k₃
  rw [ent_eq] at x₁ y₁ z₁ U₁ x₂ y₂ z₂ U₂
  rw [dPt_eq] at x₃ y₃ z₃ U₃
  rw [gPt_eq] at x₂ y₂ z₂ x₃ y₃ z₃
  rw [show brainpoolp512r1.pt ZERO ONEP ZERO = ⟨256, 384, 256⟩ from rfl] at x₁ y₁ z₁
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at x₁ y₁ z₁ U₁ x₂ y₂ z₂ U₂ x₃ y₃ z₃ U₃
  have U₃' : Unch base addsW s.mem s₃.mem := ((U₁.trans U₂).trans U₃).cover (by decide)
  have f : ∀ d, d + 64 ≤ 1152 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584) → wordsVal s₃.mem base d 8 = wordsVal s.mem base d 8 :=
    fun d h => U₃'.wordsVal (far_addsW h) (by omega)
  have B₃ : BPre base s₃ Q := hp.of_eq hw₃ f
  have zv : wordsVal s.mem base 256 8 = 0 := hp.kc.zero
  have ov : wordsVal s.mem base 384 8 = 2 ^ 512 % W.p := hp.kc.onep
  have g1 : ∀ d, d + 64 ≤ 5632 ∨ 5824 ≤ d → d + 64 ≤ 8192 → wordsVal s₁.mem base d 8 = wordsVal s.mem base d 8 := fun d h h' =>
    U₁.wordsVal (by simp; omega) (by omega)
  have g2 : ∀ d, d + 64 ≤ 5824 ∨ 6016 ≤ d → d + 64 ≤ 8192 → wordsVal s₂.mem base d 8 = wordsVal s₁.mem base d 8 := fun d h h' =>
    U₂.wordsVal (by simp; omega) (by omega)
  have g3 : ∀ d, d + 64 ≤ 1152 ∨ 1344 ≤ d → d + 64 ≤ 8192 → wordsVal s₃.mem base d 8 = wordsVal s₂.mem base d 8 := fun d h h' =>
    U₃.wordsVal (by simp; omega) (by omega)
  have hT : TabTo base s₃ Q 1 := by
    intro e he
    rcases Nat.lt_or_ge e 1 with h | h
    · obtain rfl : e = 0 := by omega
      rw [mul_zero', ent_eq]
      simp only [Nat.mul_zero, Nat.add_zero]
      have e0x : wordsVal s₃.mem base 5632 8 = 0 := by
        rw [g3 _ (by omega) (by omega), g2 _ (by omega) (by omega), x₁, zv]
      have e0y : wordsVal s₃.mem base 5696 8 = 2 ^ 512 % W.p := by
        rw [g3 _ (by omega) (by omega), g2 _ (by omega) (by omega), y₁, ov]
      have e0z : wordsVal s₃.mem base 5760 8 = 0 := by
        rw [g3 _ (by omega) (by omega), g2 _ (by omega) (by omega), z₁, zv]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep W (toM W.p (2 ^ (64 * 8)) (wordsVal s₃.mem base 5632 8))
          (toM W.p (2 ^ (64 * 8)) (wordsVal s₃.mem base 5696 8)) (toM W.p (2 ^ (64 * 8)) (wordsVal s₃.mem base 5760 8)) _
        rw [e0x, e0y, e0z, toM_zero, toM_one unit]
        exact rep_infinity' hL
      · show wordsVal s₃.mem base 5632 8 < W.p; rw [e0x]; exact hp0
      · show wordsVal s₃.mem base 5696 8 < W.p; rw [e0y]; exact Nat.mod_lt _ hp0
      · show wordsVal s₃.mem base 5760 8 < W.p; rw [e0z]; exact hp0
    · obtain rfl : e = 1 := by omega
      rw [mul_one', ent_eq]
      simp only [Nat.mul_one]
      refine hp.g.move ?_ ?_ ?_ <;> rw [gPt_eq] <;> simp only
      · rw [g3 _ (by omega) (by omega), x₂, g1 _ (by omega) (by omega)]
      · rw [g3 _ (by omega) (by omega), y₂, g1 _ (by omega) (by omega)]
      · rw [g3 _ (by omega) (by omega), z₂, g1 _ (by omega) (by omega)]
  have hD : PtOk base s₃ (Cfg.dPt brainpoolp512r1) Q := by
    refine hp.g.move ?_ ?_ ?_ <;> rw [gPt_eq, dPt_eq] <;> simp only
    · rw [x₃, g2 _ (by omega) (by omega), g1 _ (by omega) (by omega)]
    · rw [y₃, g2 _ (by omega) (by omega), g1 _ (by omega) (by omega)]
    · rw [z₃, g2 _ (by omega) (by omega), g1 _ (by omega) (by omega)]
  refine WP.mono (adds_ok hL 6 (Nat.le_refl _) B₃ hT hD) fun s₄ ⟨k₄, U₄, B₄, T₄, _⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, (U₃'.trans U₄).cover (by decide), B₄, T₄⟩
  · have h4 : r ∉ [Reg.r4] := fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)
    rw [k₄.gpr r hr, k₃.gpr r h4, k₂.gpr r h4, k₁.gpr r h4]
  · rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]

/-! ## The nibble and the entry -/

/-- The nibble `k_j` into `r9`, for `j` in `r31`, from the table of `k`'s
bits. -/
theorem nibble_ok {s : State} {base : Addr} (hw : WsReg s base) {k j : Nat} (hj : j < 170)
    (h31 : s.gpr .r31 = BitVec.ofNat 64 j)
    (ht : ∀ t < 512, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (Cfg.nibble3 brainpoolp512r1)) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 ((k >>> (3 * j)) % 8) ∧ Kp [.r4, .r5, .r9] s s' ∧ s'.mem = s.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  rw [Cfg.nibble3, show bitsAt brainpoolp512r1.n 0 = 4096 from rfl]
  have a₄ : s.gpr .r3 + (s.gpr .r31 <<< 1 + s.gpr .r31) = off base (3 * j) := by
    rw [h3, h31]
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    rw [show 3 * j + (4096 + 2) = 4096 + (3 * j + 2) by omega,
      show 3 * j + (4096 + 1) = 4096 + (3 * j + 1) by omega, show 3 * j + 4096 = 4096 + 3 * j by omega,
      ht _ (by omega), ht _ (by omega), ht _ (by omega), byte_bit, byte_bit, byte_bit, nib3_eq]
    exact horner3_eq _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `D = entry e` if the mask `r10` is all ones (`c`), else `D`. -/
theorem selD_ok {s : State} {base : Addr} (hw : WsReg s base) (c : Bool)
    (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0)) {e : Nat} (he : e < 8) :
    WP isa (.block (selPt 8 (Cfg.dPt brainpoolp512r1) (Cfg.dPt brainpoolp512r1) (ent e))) s fun s' =>
      (∀ i < 3, wordsVal s'.mem base (1152 + 64 * i) 8 =
        if c then wordsVal s.mem base (5632 + 192 * e + 64 * i) 8 else wordsVal s.mem base (1152 + 64 * i) 8) ∧
      Kp [.r4, .r5] s s' ∧ Unch base [(1152, 192)] s.mem s'.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  have hn := hw.nowrap
  rw [selPt, dPt_eq, ent_eq, List.append_assoc]
  simp only
  refine WP.block_append (WP.mono (sel_ok c 8 hs h3 hc (o := 1152) (a := 1152) (b := 5632 + 192 * e)
    (by decide) (by decide) (by omega) (by decide) (by decide) (by omega) (Or.inl (Nat.le_refl _))
    (Or.inl (by omega))) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  refine WP.block_append (WP.mono (sel_ok c 8 (k₁.ws hs) (k₁.at h3) (by rw [k₁.g]; exact hc) (o := 1216) (a := 1216)
    (b := 5632 + 192 * e + 64) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (Or.inl (Nat.le_refl _)) (Or.inl (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  refine WP.mono (sel_ok c 8 (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) (by rw [k₂.g, k₁.g]; exact hc) (o := 1280) (a := 1280)
    (b := 5632 + 192 * e + 128) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (Or.inl (Nat.le_refl _)) (Or.inl (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ⟨fun i hi => ?_, (k₁.trans k₂).trans k₃,
      ((O₁.unch.trans O₂.unch).trans O₃.unch).cover (by decide)⟩
  have a₁ : ∀ d, d + 64 ≤ 1152 ∨ 1216 ≤ d → d + 64 ≤ 8192 → wordsVal s₁.mem base d 8 = wordsVal s.mem base d 8 :=
    fun d h h' => O₁.wordsVal (by omega) (by omega)
  have a₂ : ∀ d, d + 64 ≤ 1216 ∨ 1280 ≤ d → d + 64 ≤ 8192 → wordsVal s₂.mem base d 8 = wordsVal s₁.mem base d 8 :=
    fun d h h' => O₂.wordsVal (by omega) (by omega)
  have a₃ : ∀ d, d + 64 ≤ 1280 ∨ 1344 ≤ d → d + 64 ≤ 8192 → wordsVal s₃.mem base d 8 = wordsVal s₂.mem base d 8 :=
    fun d h h' => O₃.wordsVal (by omega) (by omega)
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [show 1152 + 64 * 0 = 1152 from rfl, show 5632 + 192 * e + 64 * 0 = 5632 + 192 * e by omega,
      a₃ _ (by omega) (by omega), a₂ _ (by omega) (by omega), e₁]
  · rw [show 1152 + 64 * 1 = 1216 from rfl, show 5632 + 192 * e + 64 * 1 = 5632 + 192 * e + 64 by omega,
      a₃ _ (by omega) (by omega), e₂, a₁ _ (by omega) (by omega), a₁ _ (by omega) (by omega)]
  · rw [show 1152 + 64 * 2 = 1280 from rfl, show 5632 + 192 * e + 64 * 2 = 5632 + 192 * e + 128 by omega, e₃,
      a₂ _ (by omega) (by omega), a₂ _ (by omega) (by omega), a₁ _ (by omega) (by omega), a₁ _ (by omega) (by omega)]

/-- The entries below `e` scanned: `D` holds entry `a` if `a < e`, where `r9 = a`. -/
theorem scans_ok {base : Addr} {a : Nat} (ha : a < 8) : ∀ e ≤ 8, ∀ {s : State}, WsReg s base →
    s.gpr .r9 = BitVec.ofNat 64 a →
    WP isa (.block ((List.range e).flatMap (Cfg.scanEntry brainpoolp512r1))) s fun s' =>
      (a < e → ∀ i < 3, wordsVal s'.mem base (1152 + 64 * i) 8 = wordsVal s.mem base (5632 + 192 * a + 64 * i) 8) ∧
      Kp [.r4, .r5, .r10] s s' ∧ Unch base [(1152, 192)] s.mem s'.mem
  | 0, _, s, _, _ => WP.block_nil ⟨fun h => absurd h (by omega), Kp.refl _ _, Unch.refl _ _ _⟩
  | e + 1, he, s, hw, h9 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scans_ok ha e (by omega) hw h9) fun s₁ ⟨v₁, k₁, U₁⟩ => ?_)
    have hw₁ := hw.of_kp k₁
    rw [Cfg.scanEntry]
    refine WP.block_append (WP.mono (eqMask_ok (a := a) (by omega) (e := e) (by omega) (by rw [k₁.g]; exact h9))
      fun s₂ ⟨c₂, k₂, m₂⟩ => ?_)
    have hw₂ := hw₁.of_kp k₂
    refine WP.mono (selD_ok hw₂ _ c₂ (e := e) (by omega)) fun s₃ ⟨v₃, k₃, U₃⟩ => ⟨fun hae i hi => ?_,
      ((k₁.trans (k₂.mono (by decide))).trans (k₃.mono (by decide))), ?_⟩
    · have hn := hw.nowrap
      have ent_u : ∀ d, 5632 ≤ d → d + 64 ≤ 7168 → wordsVal s₂.mem base d 8 = wordsVal s.mem base d 8 := fun d h h' => by
        rw [m₂]; exact U₁.wordsVal (by simp; omega) (by omega)
      rw [v₃ i hi]
      by_cases h : a = e
      · subst h
        simp only [decide_true, ↓reduceIte]
        exact ent_u _ (by omega) (by omega)
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [m₂]; exact v₁ (by omega) i hi
    · rw [m₂] at U₃; exact (U₁.trans U₃).cover (by decide)

/-- The window's entry `[k_j]Q` to `D`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {k j : Nat} (hj : j < 170)
    (h31 : s.gpr .r31 = BitVec.ofNat 64 j)
    (ht : ∀ t < 512, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0)
    {Q : Point W} (hT : TabTo base s Q 7) :
    WP isa (.block (Cfg.select3 brainpoolp512r1)) s fun s' =>
      PtOk base s' (Cfg.dPt brainpoolp512r1) (mul ((k >>> (3 * j)) % 8) Q) ∧ Kp [.r4, .r5, .r9, .r10] s s' ∧
        Unch base [(1152, 192)] s.mem s'.mem := by
  rw [Cfg.select3]
  refine WP.block_append (WP.mono (nibble_ok hw hj h31 ht) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  have ha : (k >>> (3 * j)) % 8 < 8 := Nat.mod_lt _ (by decide)
  refine WP.mono (scans_ok ha 8 (Nat.le_refl _) (hw.of_kp k₁) v₁) fun s₂ ⟨v₂, k₂, U₂⟩ => ⟨?_,
    (k₁.mono (by decide)).trans (k₂.mono (by decide)), by rw [← m₁]; exact U₂⟩
  have pe := hT ((k >>> (3 * j)) % 8) (by omega)
  rw [ent_eq] at pe
  rw [m₁] at v₂
  refine pe.move ?_ ?_ ?_ <;> rw [dPt_eq] <;> simp only
  · have := v₂ ha 0 (by decide); simpa using this
  · have := v₂ ha 1 (by decide); simpa using this
  · have := v₂ ha 2 (by decide); simpa using this

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

/-! ## The windows -/

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point W) (k : Nat) : Prop where
  kc : KC B3s base s₀
  tab : TabTo base s₀ Q 7
  bits : Bits base s₀ k
  q : onCurve W Q = true

/-- What the windows write: `R`, `D`, `T`, the temporaries and the functions'
own working space. -/
abbrev stepW : List (Nat × Nat) := [(960, 960), (3584, 512)]

/-- The loop's invariant at `r31 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point W) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (Cfg.rPt brainpoolp512r1) (wpt Q k j)

theorem far_stepW {d : Nat} (h : d + 64 ≤ 960 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584) ∨ 4096 ≤ d) :
    ∀ w ∈ stepW, d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> (simp only; omega)

/-- A window. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {Q : Point W} {k : Nat} (hP : WFix base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 170) {s : State} (hI : WInv base s₀ s Q k j) :
    WP isa (WindowA.Cfg.step3 brainpoolp512r1 B3s) s fun s' => WInv base s₀ s' Q k (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, d + 64 ≤ 960 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584) ∨ 4096 ≤ d → d + 64 ≤ 8192 →
      wordsVal s.mem base d 8 = wordsVal s₀.mem base d 8 := fun d h h' =>
    hI.unch.wordsVal (far_stepW h) (by omega)
  rw [WindowA.Cfg.step3]
  refine WP.seq (wp_decCounter hj1 hI.ctr (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have k₁ : Kp [.r31] s s₁ := hs₁ ▸ Kp.write _ _ (by decide)
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁, write_gpr]; simp
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have hw₁ := hI.ws.of_kp k₁
  have hK₁ : KC B3s base s₁ := hP.kc.of_eq fun d hd => by
    rw [m₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact uS _ (by decide) (by decide)
  have pR₁ : PtOk base s₁ (Cfg.rPt brainpoolp512r1) (wpt Q k j) := hI.rep.of_eq (by rw [m₁]) (by rw [m₁]) (by rw [m₁])
  have hX := hL.onCurve_mul hP.q (k >>> (3 * j))
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  have h8 := hL.onCurve_add h4 h4
  have hE := hL.onCurve_mul hP.q ((k >>> (3 * (j - 1))) % 8)
  -- `R = 8 R`.
  refine WP.seq (WP.mono (quad_ok hL hw₁ hK₁ hX pR₁) fun s₂ ⟨K₂, U₂, pR₂⟩ => ?_)
  have hw₂ := hw₁.of_rk K₂
  have u₂ : ∀ d, d + 64 ≤ 960 ∨ (1920 ≤ d ∧ d + 64 ≤ 3584) ∨ 4096 ≤ d → d + 64 ≤ 8192 →
      wordsVal s₂.mem base d 8 = wordsVal s₀.mem base d 8 := fun d h h' => by
    rw [U₂.wordsVal (far_stepW h) (by omega), m₁]; exact uS d h h'
  have hT₂ : TabTo base s₂ Q 7 := hP.tab.of_eq (fun d h1 h2 => u₂ d (by omega) (by omega)) (by decide)
  have hBs : Bits base s k := hP.bits.of_unch hI.unch (by decide)
  have hB₁ : Bits base s₁ k := fun t ht => by rw [m₁]; exact hBs t ht
  have hB₂ : Bits base s₂ k := hB₁.of_unch U₂ (by decide)
  -- The entry.
  refine WP.seq (WP.mono (select_ok hw₂ (j := j - 1) (by omega) (by rw [K₂.gpr _ (by decide)]; exact c₁)
    (fun t ht => hB₂ t ht) hT₂) fun s₃ ⟨pE, k₃, U₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃
  have pR₃ : PtOk base s₃ (Cfg.rPt brainpoolp512r1) (d8 (wpt Q k j)) :=
    pR₂.of_eq (U₃.wordsVal (by decide) (by decide)) (U₃.wordsVal (by decide) (by decide))
      (U₃.wordsVal (by decide) (by decide))
  have hK₃ : KC B3s base s₃ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      exact (U₃.wordsVal (by decide) (by decide)).trans (u₂ _ (by decide) (by decide))
  -- `T = R + D`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃ (p := Cfg.rPt brainpoolp512r1) (q := Cfg.dPt brainpoolp512r1)
    (o := Cfg.tPt brainpoolp512r1) ⟨by decide, by decide⟩ (by decide) h8 hE pR₃ pE) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_rk K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := Cfg.rPt brainpoolp512r1) (p := Cfg.tPt brainpoolp512r1) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, k₅, U₅⟩ => ?_
  refine ⟨hw₄.of_kp k₅, ?_, ?_, ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), k₃.gpr _ (by decide), K₂.gpr _ (by decide), c₁]
  · exact ((((hI.keep.trans (rk_of_kp k₁)).trans (rk_mono K₂)).trans (rk_of_kp k₃)).trans (rk_mono K₄)).trans
      (rk_of_kp k₅)
  · have U₁ : Unch base [] s.mem s₁.mem := fun x _ => by rw [m₁]
    exact (((((hI.unch.trans U₁).trans U₂).trans U₃).trans U₄).trans U₅).cover (by decide)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

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

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (WindowA.Cfg.mul3top brainpoolp512r1 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY B3s) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt brainpoolp512r1) (mul k Q) := by
  have hn := hp.ws.nowrap
  rw [WindowA.Cfg.mul3top, List.append_assoc, List.append_assoc]
  refine WP.seq (WP.mono (build_ok hL ⟨hp.ws, hp.kc, hp.g, hp.on⟩) fun s₁ ⟨K₁, U₁, B₁, T₁⟩ => ?_)
  have hw₁ := B₁.ws
  have hB₁ : Bits base s₁ k := hp.bits.of_unch U₁ (by decide)
  -- The top two bits, and their entry in `D`.
  refine WP.seq (WP.block_append (WP.mono (top2_ok hw₁ hB₁ hp.lt) fun s₂ ⟨v₂, k₂, m₂⟩ => ?_))
  have hw₂ := hw₁.of_kp k₂
  have ha : k >>> 510 < 8 := by have := hp.lt; rw [Nat.shiftRight_eq_div_pow]; omega
  refine WP.block_append (WP.mono (scans_ok ha 8 (Nat.le_refl _) hw₂ v₂) fun s₃ ⟨v₃, k₃, U₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃
  -- `R = D`.
  refine WP.block_append (WP.mono (copyPt_ok hw₃ (o := Cfg.rPt brainpoolp512r1) (p := Cfg.dPt brainpoolp512r1)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨x₄, y₄, z₄, r₄, U₄⟩ => ?_)
  have hw₄ := hw₃.of_kp r₄
  refine wp_step (exec_li (imm := 170) (by decide)) (WP.block_nil ?_)
  generalize hs₅ : s₄.write .r31 (BitVec.ofNat 64 170) = s₅
  have ku₅ : Kp [.r31] s₄ s₅ := hs₅ ▸ Kp.write _ _ (by decide)
  have m₅ : s₅.mem = s₄.mem := by rw [← hs₅]; rfl
  have c₅ : s₅.gpr .r31 = BitVec.ofNat 64 170 := by rw [← hs₅, write_gpr]; simp
  have hw₅ : WsReg s₅ base := hw₄.of_kp ku₅
  have U₅ : Unch base [(960, 384)] s₁.mem s₅.mem := by
    rw [m₅, ← m₂]; exact (U₃.trans U₄).cover (by decide)
  have k₅ : ∀ d, d + 64 ≤ 960 ∨ 1344 ≤ d → d + 64 ≤ 8192 → wordsVal s₅.mem base d 8 = wordsVal s₁.mem base d 8 :=
    fun d h h' => U₅.wordsVal (by simp; omega) (by omega)
  have hP : WFix base s₅ Q k :=
    ⟨B₁.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₅ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₅ d (by omega) (by omega)) (by decide),
     hB₁.of_unch U₅ (by decide), hp.on⟩
  -- `R` is the entry of the top two bits, `[k >>> 510]Q`: `R` before the 170 windows.
  have pe := T₁ (k >>> 510) (by omega)
  rw [ent_eq] at pe
  rw [m₂] at v₃
  have pR : PtOk base s₅ (Cfg.rPt brainpoolp512r1) (mul (k >>> 510) Q) := by
    refine pe.move ?_ ?_ ?_ <;> rw [m₅]
    · rw [x₄, dPt_eq]; have := v₃ ha 0 (by decide); simpa using this
    · rw [y₄, dPt_eq]; have := v₃ ha 1 (by decide); simpa using this
    · rw [z₄, dPt_eq]; have := v₃ ha 2 (by decide); simpa using this
  have hI : WInv base s₅ s₅ Q k 170 := ⟨hw₅, c₅, Rk.refl _ _, Unch.refl _ _ _, pR⟩
  refine countLoop_ok (Inv := fun j s' => WInv base s₅ s' Q k j) (n := 170) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  have k₂₅ : Kp [.r4, .r5, .r9, .r10, .r31] s₁ s₅ :=
    (((k₂.mono (by decide)).trans (k₃.mono (by decide))).trans (r₄.mono (by decide))).trans (ku₅.mono (by decide))
  refine ⟨((rk_mono K₁).trans (rk_of_kp k₂₅)).trans hi.keep, ((U₁.trans U₅).trans hi.unch).cover (by decide), ?_⟩
  have e : wpt Q k 0 = mul k Q := by simp only [wpt, Nat.mul_zero, Nat.shiftRight_zero]
  rw [← e]
  exact hi.rep

end VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1
