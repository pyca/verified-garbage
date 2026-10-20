module

public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
public import VerifiedGarbage.Proof.Bignum.CrtExp

/-! Table values and memory frames for the 32-entry CRT window. The
arithmetic arrays and header write set are unchanged from four-bit windows. -/

@[expose] public section

namespace VG.Proof.Bignum.CrtWindowFive
open VG VG.Impl.Bignum VG.Impl.Bignum.Public VG.Proof.Bignum

def crtExpRanges (wx : Nat) : List (Nat × Nat) :=
  (8 * Crt.sExp, 8) :: (8 * Crt.sExpLen, 8) :: (8 * Crt.sI, 8) :: (8 * Crt.sTab, 8) ::
    (slot wx 8, tabBytes32 wx) :: crtWinRanges wx

theorem crtWinRanges_sub (wx : Nat) : ∀ r ∈ crtWinRanges wx, r ∈ crtExpRanges wx := fun _ hr =>
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hr))))

theorem crtExpRanges_ok (wx : Nat) :
    ∀ r ∈ crtExpRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes32 wx := by
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  intro r hr
  simp only [crtExpRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · simp only [Crt.sExp, sFn]; omega_arith
  · simp only [Crt.sExpLen, sFn]; omega_arith
  · simp only [Crt.sI, sFn]; omega_arith
  · simp only [Crt.sTab, sFn]; omega_arith
  · simp only; omega_arith
  · have := crtWinRanges_ok wx r hr; omega_arith

theorem crtExpRanges_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ Crt.aT) : ∀ r ∈ crtExpRanges wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have s3 := slot_sep (w := wx) h3
  have s4 := slot_sep (w := wx) h4
  have s8 := slot_le (w := wx) hj
  simp only [crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sTab, Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;>
    omega_arith

structure CTab (m : Mem) (P : Addr) (wx X : Nat) (Q : Prop) (x : Nat) : Prop where
  tab : word m P (8 * Crt.sTab) = off P (slot wx 8)
  lt : ∀ j < 32, wv m P (slot wx (8 + j)) wx < X
  val : Q → ∀ j < 32, wv m P (slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X

theorem CTab.of_win {m m' : Mem} {P : Addr} {wx X : Nat} {Q : Prop} {x : Nat} (h : CTab m P wx X Q x)
    (hf : Frm P (crtWinRanges wx) m m') (hn : P.toNat + (slot wx 8 + tabBytes32 wx) ≤ 2 ^ 64) :
    CTab m' P wx X Q x := by
  have he : ∀ j < 32, wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx := fun j hj =>
    hf.wv_eq (fun r hr => by have := crtWinRanges_ent wx j r hr; omega_arith) (by have := ent32_le wx hj; omega_arith)
  refine ⟨?_, fun j hj => (he j hj).symm ▸ h.lt j hj, fun hQ j hj => (he j hj).symm ▸ h.val hQ j hj⟩
  rw [hf.word_eq (crtWinRanges_hdr wx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by have := hdr_lt_slot wx 8 (show Crt.sTab < 32 by decide); omega_arith)]
  exact h.tab

def buildRanges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx aAcc, 8 * (wx + 2)), (slot wx aTmp, 8 * (wx + 2)), (slot wx Crt.aT, 8 * (wx + 2)),
    (8 * Crt.sTab, 8), (8 * Crt.sEnt, 8), (8 * Crt.sBit, 8), (slot wx 8, tabBytes32 wx)]

theorem buildRanges_sub (wx : Nat) : ∀ r ∈ buildRanges wx, r ∈ crtExpRanges wx := by
  simp only [buildRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [crtExpRanges, crtWinRanges]

theorem buildRanges_y (wx : Nat) :
    ∀ r ∈ buildRanges wx, slot wx aY + 8 * wx ≤ r.1 ∨ r.1 + r.2 ≤ slot wx aY := by
  have := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) (show aY ≠ aAcc by decide)
  have s2 := slot_sep (w := wx) (show aY ≠ aTmp by decide)
  have s3 := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
  have s8 := slot_le (w := wx) (show aY < 8 by decide)
  simp only [buildRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sTab, Crt.sEnt, Crt.sBit, sFn] at * <;> omega_arith

end VG.Proof.Bignum.CrtWindowFive
