module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# The Miller–Rabin round on PPC64LE: the arrays, copies and selections

The working space has 28 arrays (`slot w j`, `j < 28`); `Env` is what every
piece of the round keeps: array 0 at `r10`, the arrays' size in `r29`,
`2 w` in `r11`, and the working space in `r31`. `sel_ok`: a masked copy by
`selectAcc64` into an array other than its sources.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)

theorem slot_lt {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- What every piece of the round keeps. -/
structure Env (s : State) (B : Addr) (Z w : Nat) : Prop where
  hs : Scr s B Z
  h10 : s.gpr .r10 = off B (slot w 0)
  h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)
  h31 : s.gpr .r31 = B
  hw : 4 ≤ w
  hw' : w ≤ 128
  hZ : slot w 28 ≤ Z

/-- The registers `Env` reads. -/
def envRegs : List Reg := [.r10, .r11, .r29, .r31]

theorem Env.keep {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg} (h : Env s B Z w) (k : Keep rs s t)
    (hr : ∀ r ∈ envRegs, r ∉ rs) : Env t B Z w :=
  ⟨h.hs.congr k.wr, (k.gpr _ (hr _ (by decide))).trans h.h10, (k.gpr _ (hr _ (by decide))).trans h.h29,
    (k.gpr _ (hr _ (by decide))).trans h.h11, (k.gpr _ (hr _ (by decide))).trans h.h31, h.hw, h.hw', h.hZ⟩

theorem Env.arr {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {j : Nat} (hj : j < 28) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_lt hj) h.hZ

/-- `base rd j` within `Env`. -/
theorem Env.base {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {rd : Reg} (hrd : rd ≠ .r0)
    (hrd29 : rd ≠ .r29) (j : Nat) :
    WP isa (.block (PublicChecked.base rd j)) s fun t =>
      (t.gpr rd = off B (slot w j) ∧ t.mem = s.mem) ∧ Keep [rd] s t :=
  Pub.base_ok hrd hrd29 h.h10 h.h29 j

/-- The registers `sel` writes. -/
def selRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17]

/-- `sel o a t`, the mask of `b` in `r20`: array `o` is array `a` if `b`, else
array `t`. -/
theorem sel_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {b : Bool} {o a t : Nat}
    (ho : o < 28) (ha : a < 28) (ht : t < 28) (hoa : o ≠ a) (hot : o ≠ t)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (sel o a t) s fun s' =>
      (val32 s'.mem B (slot w o) (2 * w) =
          (if b then val32 s.mem B (slot w a) (2 * w) else val32 s.mem B (slot w t) (2 * w)) ∧
        Outside B (slot w o) (8 * (w + 2)) s.mem s'.mem) ∧ Keep selRegs s s' := by
  unfold sel
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r8) (by decide) (by decide) a) fun t₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e1.base (rd := .r9) (by decide) (by decide) t) fun t₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  refine WP.mono (e2.base (rd := .r5) (by decide) (by decide) o) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  have k13 := (k1.trans k2).trans k3
  have hm : t₃.mem = s.mem := by rw [m3, m2, m1]
  have sep := fun {j k : Nat} (hjk : j ≠ k) => slot_sep (w := w) hjk
  have hO := h.arr ho
  have hA := h.arr ha
  have hT := h.arr ht
  refine WP.mono (selectAcc64_ok32 e3.hs (dA := slot w a) (dT := slot w t) (dO := slot w o) (w := w) (b := b)
      (by rw [k3.gpr .r8 (by decide), k2.gpr .r8 (by decide), a8])
      (by rw [k3.gpr .r9 (by decide), a9]) a5 e3.h11
      (by rw [k13.gpr .r20 (by decide), h20]) (by have := h.hw; omega) (by have := h.hw'; omega)
      (by omega) (by omega) (by omega)
      (by have := sep hoa; omega) (by have := sep hot; omega)) fun s' ⟨hv, hout, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨hv, hout.mono (Nat.le_refl _) (by omega)⟩, (k13.trans k).mono (by simp [selRegs])⟩

end VG.Proof.MillerRabin.PPC64LE
