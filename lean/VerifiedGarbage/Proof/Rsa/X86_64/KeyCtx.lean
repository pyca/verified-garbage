import VerifiedGarbage.Proof.Rsa.X86_64.KeyChecks

/-!
# `vg_rsa_check_key` on x86-64: the checks' common context

`KCtx s t`: in the workspace (`Good`), with the header as at `s` but for
`sMask`, memory outside the working space as at `s`, `n` in `aN` and 1 in
`aOne`. Each piece keeps it (`loadK`, `ltK`, …), changing only the arrays
it writes or `sMask`.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

structure KCtx (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N : Nat) : Prop where
  good : Good t B Z w minv
  hZ : slot w 8 ≤ Z
  w1 : 1 ≤ w
  w2 : w < 2 ^ 28
  hdr : ∀ i < 32, i ≠ sMask → word t.mem B (8 * i) = word s.mem B (8 * i)
  ins : InScr B Z s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  n : wv t.mem B (slot w aN) w = N
  one : wv t.mem B (slot w aOne) w = 1

section
variable {s t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

/-- An array `j` that `js` leaves alone. -/
theorem Arrays.wv_other {m m' : Mem} {js : List Nat} (ha : Arrays B w js m m') {j : Nat} (hj : j ∉ js)
    (hj8 : j < 8) (hZ : slot w 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) :
    wv m' B (slot w j) w = wv m B (slot w j) w :=
  ha.wv_eq (fun i hi => by
    have := slot_sep (w := w) (show j ≠ i by rintro rfl; exact hj hi); omega)
    (by have := slot_le (w := w) hj8; omega)

theorem Outside.wv_arr {m m' : Mem} (ho : Outside B (8 * sMask) 8 m m') {j : Nat} (hj8 : j < 8)
    (hZ : slot w 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) {k : Nat} (hk : k ≤ w + 2) :
    wv m' B (slot w j) k = wv m B (slot w j) k :=
  ho.wv (Or.inr (by have := hdr_lt_slot w j (show sMask < 32 by decide); omega))
    (by have := slot_le (w := w) hj8; omega)

theorem KCtx.arr (h : KCtx s t B Z w minv N) {js : List Nat} (ha : Arrays B w js t.mem t'.mem)
    (hjs : ∀ j ∈ js, j < 8) (hN : aN ∉ js) (h1 : aOne ∉ js) (hk : Keep mmRegs t t') : KCtx s t' B Z w minv N := by
  have hn := h.good.scr.nowrap
  refine ⟨Good.of_arrays h.good ha hk hk.2.2, h.hZ, h.w1, h.w2, fun i hi hi' => ?_,
    h.ins.trans (InScr.of_arrays ha h.hZ hjs), hk.2.1.trans h.rd, hk.2.2.trans h.wr, ?_, ?_⟩
  · rw [ha.word_eq (fun j _ => .inl (hdr_lt_slot w j hi)) (by have := hdr_lt_slot w 8 hi; omega)]
    exact h.hdr i hi hi'
  · rw [Arrays.wv_other ha hN (by decide) h.hZ hn]; exact h.n
  · rw [Arrays.wv_other ha h1 (by decide) h.hZ hn]; exact h.one

theorem KCtx.msk (h : KCtx s t B Z w minv N) (ho : Outside B (8 * sMask) 8 t.mem t'.mem)
    (hk : Keep mmRegs t t') : KCtx s t' B Z w minv N := by
  have hn := h.good.scr.nowrap
  have hS : 8 * sMask + 8 ≤ slot w 0 := hdr_lt_slot w 0 (by decide)
  have h08 := slot_le (w := w) (show 0 < 8 by decide)
  have hZ := h.hZ
  refine ⟨Good.of_mask h.good ho hk, h.hZ, h.w1, h.w2, fun i hi hi' => ?_,
    h.ins.trans (InScr.of_outside ho (by omega)), hk.2.1.trans h.rd, hk.2.2.trans h.wr, ?_, ?_⟩
  · rw [ho.word (by unfold sMask sFn at hi' ⊢; omega) (by have := hdr_lt_slot w 8 hi; omega)]
    exact h.hdr i hi hi'
  · rw [Outside.wv_arr ho (by decide) h.hZ hn (by omega)]; exact h.n
  · rw [Outside.wv_arr ho (by decide) h.hZ hn (by omega)]; exact h.one

theorem KCtx.src (h : KCtx s t B Z w minv N) {p : Addr} {bs : List Byte} (hs : Src s B Z p bs) : Src t B Z p bs :=
  hs.congr h.ins h.rd h.wr

end

end VG.Proof.Rsa.X86_64
