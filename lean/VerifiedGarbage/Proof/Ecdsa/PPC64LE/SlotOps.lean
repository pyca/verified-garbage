module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall

/-!
# ECDSA on PPC64LE: field operations on numbered slots

Calls of the Montgomery functions of a modulus `S` on slots `c.sl i`, in the
layout's terms (`slMul_ok`, `slAdd_ok`, `slSub_ok`): numbers of `c.n` words
modulo `m`, for the functions' `S.k = c.n` and `S.m = m`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont

variable {c : Cfg}

/-- What a call writing slot `o` changes. -/
abbrev callW (c : Cfg) (o : Nat) : List (Nat × Nat) := [(c.sl o, 8 * c.n), (own c.n, 64 * c.n)]

theorem callW_unch {S : Impl.Weierstrass.Mont.Modulus} (hk : S.k = c.n) {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeep S.k base (c.sl o) s s') : Unch base (callW c o) s.mem s'.mem := by
  have h' := h.mem; rw [Kept, hk] at h'; exact h'

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem slMul_ok {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} (hM : ModOk S.k S.m) (hk : S.k = c.n)
    (hm : S.m = m) (h7 : c.n < 10) {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o < 45) (ha : a < 45) (hb : b < 45) (hB : sv c base s b < m) :
    WP isa (mulCall S (c.sl o) (c.sl a) (c.sl b)) s fun s' => Rk fnClob s s' ∧
      Unch base (callW c o) s.mem s'.mem ∧ sv c base s' o < m ∧
      sv c base s' o * 2 ^ (64 * c.n) % m = sv c base s a * sv c base s b % m := by
  refine WP.mono (mulCall_ok hM hw (o := c.sl o) (a := c.sl a) (b := c.sl b)
    (by rw [hk]; exact sl_below_own c h7 ho) (by rw [hk]; exact sl_below_own c h7 ha)
    (by rw [hk]; exact sl_below_own c h7 hb) (by rw [hk, hm]; exact hB)) fun s' ⟨K, lt, e⟩ =>
    ⟨K.rk, callW_unch hk K, ?_, ?_⟩
  · rw [hk, hm] at lt; exact lt
  · rw [hk, hm] at e; exact e

/-- `[o] = [a] + [b] mod m`. -/
theorem slAdd_ok {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} (hM : ModOk S.k S.m) (hk : S.k = c.n)
    (hm : S.m = m) (h7 : c.n < 10) {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o < 45) (ha : a < 45) (hb : b < 45) (hAB : sv c base s a + sv c base s b < 2 * m) :
    WP isa (addCall S (c.sl o) (c.sl a) (c.sl b)) s fun s' => Rk fnClob s s' ∧
      Unch base (callW c o) s.mem s'.mem ∧ sv c base s' o = (sv c base s a + sv c base s b) % m := by
  refine WP.mono (addCall_ok hM hw (o := c.sl o) (a := c.sl a) (b := c.sl b)
    (by rw [hk]; exact sl_below_own c h7 ho) (by rw [hk]; exact sl_below_own c h7 ha)
    (by rw [hk]; exact sl_below_own c h7 hb) (by rw [hk, hm]; exact hAB)) fun s' ⟨K, e⟩ =>
    ⟨K.rk, callW_unch hk K, ?_⟩
  rw [hk, hm] at e; exact e

/-- `[o] = [a] - [b] mod m`. -/
theorem slSub_ok {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} (hM : ModOk S.k S.m) (hk : S.k = c.n)
    (hm : S.m = m) (h7 : c.n < 10) {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o < 45) (ha : a < 45) (hb : b < 45) (hA : sv c base s a < m) (hB : sv c base s b < m) :
    WP isa (subCall S (c.sl o) (c.sl a) (c.sl b)) s fun s' => Rk fnClob s s' ∧
      Unch base (callW c o) s.mem s'.mem ∧ sv c base s' o = (sv c base s a + m - sv c base s b) % m := by
  refine WP.mono (subCall_ok hM hw (o := c.sl o) (a := c.sl a) (b := c.sl b)
    (by rw [hk]; exact sl_below_own c h7 ho) (by rw [hk]; exact sl_below_own c h7 ha)
    (by rw [hk]; exact sl_below_own c h7 hb) (by rw [hk, hm]; exact hA) (by rw [hk, hm]; exact hB))
    fun s' ⟨K, e⟩ => ⟨K.rk, callW_unch hk K, ?_⟩
  rw [hk, hm] at e; exact e

theorem apart_callW (h7 : c.n < 10) {o i : Nat} (hi : i < 45) (hio : i ≠ o) :
    ∀ w ∈ callW c o, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact sl_apart c hio
  · exact Or.inl (sl_below_own c h7 hi)

/-- The flag is apart from what a call writes. -/
theorem flag_callW (h0 : 0 < c.n) (h7 : c.n < 10) {base : Addr} {m m' : Mem} {o : Nat} (ho : FLAG ≠ o)
    (hu : Unch base (callW c o) m m') : word m' base (c.sl FLAG) = word m base (c.sl FLAG) :=
  hu.word (fun w hw => (apart_callW h7 (by decide) ho w hw).imp (fun h => by omega) id)
    (by have := sl_le c h7 (i := FLAG) (by decide); omega)

theorem fixedOk_callW (h7 : c.n < 10) {o : Nat} (ho : o = TMP ∨ 12 ≤ o) : FixedOk c (callW c o) :=
  (fixedOk_slW (l := [o]) (by simpa using ho)).append (fixedOk_own h7)

theorem callW_le (h7 : c.n < 10) {o : Nat} (ho : o < 45) : ∀ w ∈ callW c o, w.1 + w.2 ≤ size := by
  have := sl_le c h7 ho
  have := own_eq c.n
  have hsz : size = 8192 := rfl
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> (dsimp only; omega)

theorem tbl_apart_callW (h7 : c.n < 10) {o : Nat} (ho : o < 45) (j t : Nat) :
    ∀ w ∈ callW c o, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  have := sl_below_bits c h7 ho j t
  have := own_below_bits c h7 j
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> (dsimp only; omega)

end VG.Proof.Ecdsa.PPC64LE
