module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

-- separate module: memory range lemmas are shared by correctness and constant-time proofs of the loop

/-! # Memory ranges of the word remainder loop -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Only the low arithmetic words and the digit/counter window change in the loop. -/
def ranges (W : Nat) : List (Nat × Nat) :=
  [(slot W aR, 8 * (W / 2)), (slot W aT, 8 * (W / 2 + 1)), (slot W aV + 8, 16)]

theorem range_mut {W : Nat} {r : Nat × Nat} (hr : r ∈ ranges W) : Mut r := by
  simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> apply Or.inl <;> simp only [slot, Impl.Bignum.hdrBytes] <;> omega_arith

theorem range_ws {s t : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hf : Frm B (ranges W) s.mem t.mem) (hk : Keep mmRegs s t) : Ws t B Z W :=
  h.congr hf (fun _ hr => range_mut hr) hk (by decide)

theorem range_modulus {m m' : Mem} {B : Addr} {W : Nat}
    (hf : Frm B (ranges W) m m') (h : slot W aM + 8 * (W / 2) ≤ 2 ^ 64) :
    wv m' B (slot W aM) (W / 2) = wv m B (slot W aM) (W / 2) := by
  apply hf.wv_eq _ h
  intro r hr
  simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [slot, aM, aR, aT, aV] <;> omega_arith

theorem range_top {m m' : Mem} {B : Addr} {W : Nat} (hW : 4 ≤ W)
    (hf : Frm B (ranges W) m m') (h : slot W aM + 8 * (W / 2 - 1) + 8 ≤ 2 ^ 64) :
    word m' B (slot W aM + 8 * (W / 2 - 1)) = word m B (slot W aM + 8 * (W / 2 - 1)) := by
  apply hf.word_eq _ h
  intro r hr
  simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [slot, aM, aR, aT, aV] <;> omega_arith

theorem range_recip {m m' : Mem} {B : Addr} {W : Nat}
    (hf : Frm B (ranges W) m m') (h : slot W aV + 8 ≤ 2 ^ 64) :
    word m' B (slot W aV) = word m B (slot W aV) := by
  apply hf.word_eq _ h
  intro r hr
  simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [slot, aR, aT, aV] <;> omega_arith

/-- A store within the digit/counter window is covered by the loop frame. -/
theorem range_store {m : Mem} {B : Addr} {W d : Nat} (v : BitVec 64)
    (hd : slot W aV + 8 ≤ d) (hd' : d + 8 ≤ slot W aV + 24) (h : d + 8 ≤ 2 ^ 64) :
    Frm B (ranges W) m (m.writeW (off B d) v) := by
  intro x hx
  apply writeW_outside m B v h x
  have := hx (slot W aV + 8, 16) (by simp [ranges])
  omega_using [this, hd, hd']

/-- The core's narrower frame is included in the loop frame. -/
theorem range_core {m m' : Mem} {B : Addr} {W : Nat}
    (hf : Frm B [(slot W aT, 8 * (W / 2 + 1)), (slot W aR, 8 * (W / 2))] m m') :
    Frm B (ranges W) m m' := hf.mono (by simp [ranges])

end VG.Proof.Rsa.X86_64.WordDivide
