module

public import VerifiedGarbage.Proof.Rsa.Arm.KcOps
public import VerifiedGarbage.Proof.Rsa.Arm.KdDiv
public import VerifiedGarbage.Proof.Rsa.Arm.KdMul
public import VerifiedGarbage.Proof.Rsa.KeyCheckWords
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.Arm.KcChecks
import VerifiedGarbage.Proof.Rsa.Arm.InvParts

/-! # The checks of an RSA key on ARMv7: a balanced key, by words

`keyBodyW_ok`: from `BodyIn`, for `w` even and `p`, `q` of `w / 2` words, the mask is `cW` of
what the code computes: `p q mod 2^(32 w) = n` in place of the division of `n` by `p`, and the
remainders by words (`KeyDiv.divW`), modulo the divisors with their top words made not zero
(`fixT`).
-/

@[expose] public section

/-! ## The checks of an RSA key on ARMv7: the division and product by words between the steps

`Stg.mulLo_ok`, `Stg.fixTop_ok` and `Stg.divW_ok`: `KeyDiv.mulLo`, `KeyDiv.fixTop` and
`KeyDiv.divW` on the arrays the checks track.
-/

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- `(0 - x | x) >> 31`, xor 1: whether `x` is zero. -/
theorem zero_bit (x : BitVec 32) : ((0 - x ||| x) >>> 31) ^^^ 1 = if x = 0 then 1 else 0 := by
  by_cases e : x = 0
  · subst e; decide
  · simp only [e, ↓reduceIte]
    have hx : 0 < x.toNat := Nat.pos_of_ne_zero fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlt := x.isLt
    have top : 2 ^ 31 ≤ (0 - x ||| x).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 31) with h | h
      · have : (0 - x).toNat = 2 ^ 32 - x.toNat := by
          rw [BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]; omega
        have := Nat.left_le_or (n := (0 - x).toNat) (m := x.toNat)
        omega
      · have := Nat.right_le_or (n := (0 - x).toNat) (m := x.toNat)
        omega
    have hy := (0 - x ||| x).isLt
    have sh : (0 - x ||| x) >>> 31 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    rw [sh]; decide

/-- The top word of a number of `k + 1` words, at least `2^(32 k)` and below `2^(32 (k + 1))`, is not
zero. -/
theorem top_word_pos {mem : Mem} {base : Addr} {d k n M : Nat} (hkn : k + 1 ≤ n) (hM : val32 mem base d n = M)
    (hl : M < 2 ^ (32 * (k + 1))) (hg : 2 ^ (32 * k) ≤ M) : 0 < w32 mem base (d + 4 * k) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_assoc, val32_append, Nat.add_comm 1 e, val32] at hM
  have hL := val32_lt mem base d k
  have hP : (2 : Nat) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  rw [hP] at hl
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, Nat.zero_add] at hM
  generalize val32 mem base (d + 4 * k + 4) e = R at hM
  generalize val32 mem base d k = L at hM hL
  generalize (2 : Nat) ^ (32 * k) = P at hM hL hl hg
  rcases Nat.eq_zero_or_pos R with r0 | r0
  · subst r0; omega
  · have := Nat.mul_le_mul_left (P * 2 ^ 32) r0
    rw [← hM, Nat.mul_one, Nat.mul_assoc] at *
    omega

theorem divRegs_body : ∀ x ∈ KeyDiv.divRegs, x ∈ bodyRegs := by decide

/-- `mulLo o x y`: `[o] := X Y mod 2^(32 w)` for `X = [x]` of `w / 2` words, `w` even. -/
theorem Stg.mulLo_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o x y : Nat} (ho : o < nArr) (hx : x ∈ live) (hy : y ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hox : o ≠ x) (hoy : o ≠ y) (ho0 : o ≠ aZ) (hoV : o ≠ aVD) (hw : g.w % 2 = 0)
    (hw2 : 2 ≤ g.w) (hX : A x < 2 ^ (32 * (g.w / 2))) :
    WP isa (KeyDiv.mulLo o x y) s (Stg g s0 (upd A o (A x * A y % 2 ^ (32 * g.w))) (o :: live) c) := by
  have c16 : slot s.mem g.B 16 = g.w := by
    simp only [slot, w32]; rw [h.cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.ws.wle; omega)]
  refine WP.mono (KeyDiv.mulLo_ok h.ws ho (h.live_lt x hx) (h.live_lt y hy) (by decide) hox hoy ho0 c16 hw hw2
    (h.arrs.get hx) hX (h.arrs.get hy) (by have := h.arrs.get hz; rw [hA0] at this; exact this))
    fun t ⟨ht, e, k, r⟩ => ?_
  refine h.next ht k (by simpa using ho) (by decide) r divRegs_body ?_ ?_
    (h.vd_keep k (by simpa using hoV) (by decide)) (h.mask_keep k (by decide))
  · exact (h.arrs_write k e (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n)
      (by decide)).cons (by rw [upd_self]; exact e)
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ho
    · exact h.live_lt j hj'

/-- `divW a r m t nm u`: `[r] := [a] mod M` for `M = [m]` of `w / 2` words, its top word not zero. -/
theorem Stg.divW_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a r m t nm u : Nat} (ha : a ∈ live) (hm : m ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hr : r < nArr) (ht : t < nArr) (hnm : nm < nArr) (hu : u < nArr) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ aZ) (ht0 : t ≠ aZ) (hu0 : u ≠ aZ) (hn0 : nm ≠ aZ)
    (hV : aVD ∉ [r, t, u, nm]) (hw6 : 6 ≤ g.w) (hMl : A m < 2 ^ (32 * (g.w / 2)))
    (hMg : 2 ^ (32 * (g.w / 2 - 1)) ≤ A m) (hlive : ∀ j ∈ live, j = r ∨ j ∉ [r, t, u, nm]) :
    WP isa (KeyDiv.divW a r m t nm u) s (Stg g s0 (upd A r (A a % A m)) (r :: live) c) := by
  have c16 : slot s.mem g.B 16 = g.w := by
    simp only [slot, w32]; rw [h.cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.ws.wle; omega)]
  have hT0 : 0 < w32 s.mem (State.addr g.B) (arr g.w m + 4 * (g.w / 2 - 1)) :=
    top_word_pos (k := g.w / 2 - 1) (n := g.w) (by omega) (h.arrs.get hm)
      (by rw [show g.w / 2 - 1 + 1 = g.w / 2 by omega]; exact hMl) hMg
  refine WP.mono (KeyDiv.divW_ok h.ws (h.live_lt a ha) hr (h.live_lt m hm) ht hnm hu (by decide) hra hrt hru htu hmr
    hmt hmu hnr htn hnu hnm' hr0 ht0 hu0 hn0 hw6 c16 (h.arrs.get hm) hMl hT0
    (by have := h.arrs.get hz; rw [hA0] at this; exact this))
    fun v ⟨hv, e, _, k, rr⟩ => ?_
  have hjs : ∀ j ∈ [r, t, u, nm], j < nArr := by simp; exact ⟨hr, ht, hu, hnm⟩
  refine h.next hv k hjs (by decide) rr divRegs_body ?_ ?_ (h.vd_keep k (fun j hj e' => hV (e' ▸ hj)) (by decide))
    (h.mask_keep k (by decide))
  · rw [h.arrs.get ha] at e
    exact (h.arrs_write k e hlive (by decide)).cons (by rw [upd_self, e])
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact hr
    · exact h.live_lt j hj'

/-- A number of `k + 1` words below `2^(32 (k + 1))` from its top word and the rest. -/
theorem val32_top_word {mem : Mem} {base : Addr} {d k n : Nat} (hkn : k + 1 ≤ n)
    (hl : val32 mem base d n < 2 ^ (32 * (k + 1))) :
    val32 mem base d n = val32 mem base d k + 2 ^ (32 * k) * w32 mem base (d + 4 * k) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_assoc, val32_append, Nat.add_comm 1 e, val32] at hl ⊢
  have hL := val32_lt mem base d k
  have hw := (mem.readW (off base (d + 4 * k)) 32).isLt
  have hP : (2 : Nat) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  rw [hP] at hl
  generalize val32 mem base (d + 4 * k + 4) e = R at hl ⊢
  generalize val32 mem base d k = L at hl hL ⊢
  generalize w32 mem base (d + 4 * k) = W at hl hw ⊢
  generalize (2 : Nat) ^ (32 * k) = P at hl hL ⊢
  rcases Nat.eq_zero_or_pos R with r0 | r0
  · subst r0; simp only [Nat.mul_zero, Nat.add_zero]
  · have := Nat.mul_le_mul_left (P * 2 ^ 32) r0
    rw [Nat.mul_one, Nat.mul_add, ← Nat.mul_assoc] at *
    omega

end VG.Proof.Rsa.Arm.KeyCheck

namespace VG.Proof.Rsa.Arm.KeyDiv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (fixT)
open VG.Proof.Rsa.Arm.KeyCheck (zero_bit)

/-- `fixTop m`: `[m]`'s top word (`w / 2 - 1`) made not zero: its value is `fixT`'s. -/
theorem fixTopW_ok {s : State} {B : BitVec 32} {Z w N m : Nat} (W : Ws s B Z w N) (hmN : m < N)
    (hN : N ≤ 256) {M : Nat} (hnum : num s.mem B w m = M) (hMl : M < 2 ^ (32 * (w / 2))) (hw2 : 2 ≤ w) :
    WP isa (.block (VG.Impl.Rsa.Arm.KeyDiv.fixTop m)) s fun v => Ws v B Z w N ∧ Keep B w [m] [] s.mem v.mem ∧
      num v.mem B w m = fixT (w / 2) M ∧ Rest [.r0, .r1, .r2, .r3] s v ∧
      w32 v.mem (State.addr B) (arr w m + 4 * w) = w32 s.mem (State.addr B) (arr w m + 4 * w) := by
  have := W.wle
  have nw := W.nowrap
  have fm := W.arr_fit hmN
  have gm := W.fit64 hmN
  simp only [S] at fm gm
  rw [VG.Impl.Rsa.Arm.KeyDiv.fixTop]
  refine topPtr_ok W (r := .r0) (t := .r1) (by decide) (by decide) (by decide) (j := m) (i := 1)
    (by omega) (by omega) (by decide) (by omega)
    fun u p1 r1 m1 W1 => ?_
  generalize eX : arr w m + 4 * (w / 2 - 1) = X at p1
  have aX : State.addr (B + BitVec.ofNat 32 X) = off (State.addr B) X := W.addr (by omega)
  have rX : InRegions (u.rd ++ u.wr) (off (State.addr B) X) 4 := W1.read (by omega)
  have wX : InRegions u.wr (off (State.addr B) X) 4 := W1.write (by omega)
  generalize ex : u.mem.readW (off (State.addr B) X) 32 = x
  refine WP.mono (WP.keep [.r2, .r3] (Q := fun v =>
      v.mem = u.mem.writeW (off (State.addr B) X) (x + (((0 - x ||| x) >>> 31) ^^^ 1))) (by
    krun [p1, aX, rX, wX, ex]) (by decide)) fun v ⟨mv, kv⟩ => ?_
  rw [zero_bit] at mv
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have mu : u.mem = s.mem := m1
  have K : Keep B w [m] [] s.mem v.mem := by
    rw [mv, mu, ← eX]
    exact Keep.of_arr (d := 4 * (w / 2 - 1)) (writeW32_outside _ _ _ (by omega)) (by simp only [S]; omega)
      (by simp)
  -- The value: the low words `L`, the top word, and none above it.
  simp only [num] at hnum
  have split : ∀ mem : Mem, val32 mem (State.addr B) (arr w m) w =
      val32 mem (State.addr B) (arr w m) (w / 2 - 1) + 2 ^ (32 * (w / 2 - 1)) *
        (w32 mem (State.addr B) X + 2 ^ 32 * val32 mem (State.addr B) (X + 4) (w - w / 2)) := fun mem => by
    have e := val32_append mem (State.addr B) (arr w m) (w / 2 - 1) (w - w / 2 + 1)
    rw [show w / 2 - 1 + (w - w / 2 + 1) = w by omega, val32] at e
    rw [e, eX]
  have hL := val32_lt s.mem (State.addr B) (arr w m) (w / 2 - 1)
  have hP : (2 : Nat) ^ (32 * (w / 2)) = 2 ^ (32 * (w / 2 - 1)) * 2 ^ 32 := by
    rw [← Nat.pow_add]; congr 1; omega
  have sS := split s.mem
  rw [hnum] at sS
  have hH : val32 s.mem (State.addr B) (X + 4) (w - w / 2) = 0 := by
    have hMl' := hMl
    rw [hP] at hMl'
    generalize val32 s.mem (State.addr B) (X + 4) (w - w / 2) = H at sS
    generalize (2 : Nat) ^ (32 * (w / 2 - 1)) = P at sS hMl' hL
    rcases Nat.eq_zero_or_pos H with e | e
    · exact e
    · have := Nat.mul_le_mul_left (P * 2 ^ 32) e
      rw [Nat.mul_one] at this
      rw [Nat.mul_add, ← Nat.mul_assoc] at sS
      omega
  have new : num v.mem B w m = fixT (w / 2) M := by
    have oL : val32 v.mem (State.addr B) (arr w m) (w / 2 - 1) =
        val32 s.mem (State.addr B) (arr w m) (w / 2 - 1) := by
      rw [mv, mu]; exact Outside.val32 (writeW32_outside _ _ _ (by omega)) (Or.inl (by omega)) (by omega)
    have oH : val32 v.mem (State.addr B) (X + 4) (w - w / 2) =
        val32 s.mem (State.addr B) (X + 4) (w - w / 2) := by
      rw [mv, mu]; exact Outside.val32 (writeW32_outside _ _ _ (by omega)) (Or.inr (by omega)) (by omega)
    have hx' : x.toNat = w32 s.mem (State.addr B) X := by rw [← ex, mu]
    have oW : w32 v.mem (State.addr B) X = x.toNat + if x.toNat = 0 then 1 else 0 := by
      rw [mv, w32_write_self]
      by_cases e : x = 0
      · subst e; rfl
      · have e' : x.toNat ≠ 0 := fun h0 => e (BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [e, e', ↓reduceIte, Nat.add_zero]
        rw [show x + 0 = x from BitVec.add_zero x]
    simp only [num]
    rw [split v.mem, oL, oH, oW, hH, Nat.mul_zero, Nat.add_zero, hx']
    rw [hH, Nat.mul_zero, Nat.add_zero] at sS
    unfold fixT
    rw [sS]
    have hdiv : (val32 s.mem (State.addr B) (arr w m) (w / 2 - 1) +
        2 ^ (32 * (w / 2 - 1)) * w32 s.mem (State.addr B) X) / 2 ^ (32 * (w / 2 - 1)) =
        w32 s.mem (State.addr B) X := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hL, Nat.zero_add]
    rw [hdiv]
    by_cases e : w32 s.mem (State.addr B) X = 0
    · simp only [e, ↓reduceIte, Nat.mul_one, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    · simp only [e, ↓reduceIte, Nat.add_zero]
  refine ⟨W1.rest kv, K, new, (r1.mono (ws' := [.r0, .r1, .r2, .r3]) (by decide)).trans (kv.mono (by decide)), ?_⟩
  rw [mv, mu]
  exact Outside.w32 (writeW32_outside _ _ _ (by omega)) (Or.inr (by omega)) (by omega)

end VG.Proof.Rsa.Arm.KeyDiv

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- `fixTop m`: `[m]`'s top word (`w / 2 - 1`) made not zero. -/
theorem Stg.fixTop_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {m : Nat} (hm : m ∈ live) (hMl : A m < 2 ^ (32 * (g.w / 2))) (hw2 : 2 ≤ g.w) :
    WP isa (.block (KeyDiv.fixTop m)) s (Stg g s0 (upd A m (fixT (g.w / 2) (A m))) live c) := by
  refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.fixTopW_ok h.ws (h.live_lt m hm) (by decide) (h.arrs.get hm) hMl hw2)
    fun v ⟨Wv, K, new, R, top⟩ => ?_
  refine h.next Wv K (by simpa using h.live_lt m hm) (by decide) R (by decide)
    (h.arrs_write K new (fun j _ => (Decidable.em (j = m)).imp_right fun n => by simpa using n) (by decide))
    h.live_lt ?_ (h.mask_keep K (by decide))
  by_cases hv : m = aVD
  · subst hv
    rw [top, h.vdTop]
  · exact h.vd_keep K (by simpa using hv) (by decide)

end VG.Proof.Rsa.Arm.KeyCheck

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The products of a balanced key's checks, when their factors are below their moduli. -/
def ProdsW (g : Geo) (v : Vals) (R₁ R₂ : Nat) : Prop :=
  (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
    R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
  (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
    R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2)))

/-- The mask a balanced key's checks compute. -/
abbrev cW (g : Geo) (v : Vals) (R₁ R₂ : Nat) : Bool :=
  VG.Proof.Rsa.keyBitsW g.w v.n v.d v.p v.q v.dP v.dQ v.qI R₁ R₂

theorem divK_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (haV : a ≠ aVD) (hdV : d ≠ aVD) (hav : a ∉ [aVR, aVT, aY, aX]) (hw6 : 6 ≤ g.w)
    (hD : A d < 2 ^ (32 * (g.w / 2)))
    (hlive : ∀ j ∈ live, j = aVR ∨ j ∉ [aVR, aVT, aY, aX]) :
    WP isa (seqs (divK a d)) s (Stg g s0 (upd (upd A aVD (fixT (g.w / 2) (A d))) aVR
      (A a % fixT (g.w / 2) (A d))) (aVR :: aVD :: live) c) := by
  unfold divK
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h.copy_ok (o := aVD) (a := d) (by decide) hd (Ne.symm hdV)) fun t1 h1 => ?_
  rw [wp_seqs_cons (by simp)]
  have hD1 : upd A aVD (A d) aVD < 2 ^ (32 * (g.w / 2)) := by rw [upd_self]; exact hD
  refine WP.mono (h1.fixTop_ok (m := aVD) (by simp) hD1 (by omega)) fun t2 h2 => ?_
  rw [upd_self] at h2
  simp only [seqs]
  have ha' : a ∈ aVD :: live := List.mem_cons_of_mem _ ha
  have hz' : aZ ∈ aVD :: live := List.mem_cons_of_mem _ hz
  have hm' : aVD ∈ aVD :: live := by simp
  have e1 : upd (upd A aVD (A d)) aVD (fixT (g.w / 2) (A d)) = upd A aVD (fixT (g.w / 2) (A d)) := by
    funext j; simp only [upd]; split <;> rfl
  rw [e1] at h2
  have := h2.divW_ok (a := a) (r := aVR) (m := aVD) (t := aVT) (nm := aY) (u := aX) ha' hm' hz'
    (by rw [upd_ne _ _ (by decide : aZ ≠ aVD)]; exact hA0) (hr := by decide) (ht := by decide)
    (hnm := by decide) (hu := by decide) (hra := fun e => hav (by simp [e])) (hrt := by decide)
    (hru := by decide) (htu := by decide) (hmr := by decide) (hmt := by decide) (hmu := by decide)
    (hnr := by decide) (htn := by decide) (hnu := by decide) (hnm' := by decide) (hr0 := by decide)
    (ht0 := by decide) (hu0 := by decide) (hn0 := by decide) (hV := by decide) (hw6 := hw6)
    (hMl := by rw [upd_self]; exact fixT_lt (by omega) hD) (hMg := by rw [upd_self]; exact fixT_ge)
    (hlive := fun j hj => by
      rcases List.mem_cons.mp hj with rfl | hj'
      · right; decide
      · rcases hlive j hj' with e | e
        · left; exact e
        · right; simpa [List.mem_cons, or_comm, or_left_comm] using e)
  rw [upd_self, upd_ne _ _ haV] at this
  exact this

/-- The lists of programs the checks are made of are not empty. -/
macro "ne_nil" : tactic => `(tactic| first
  | exact List.cons_ne_nil _ _
  | exact List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _
  | (apply List.append_ne_nil_of_left_ne_nil; unfold eqA; exact List.cons_ne_nil _ _)
  | (apply List.append_ne_nil_of_left_ne_nil; unfold ltA; exact List.cons_ne_nil _ _)
  | (apply List.append_ne_nil_of_left_ne_nil; unfold mulA; exact List.cons_ne_nil _ _)
  | (apply List.append_ne_nil_of_left_ne_nil; unfold divK; exact List.cons_ne_nil _ _)
  | (unfold eqA; exact List.cons_ne_nil _ _)
  | (unfold ltA; exact List.cons_ne_nil _ _)
  | (unfold mulA; exact List.cons_ne_nil _ _)
  | (unfold divK; exact List.cons_ne_nil _ _))

theorem mulIdx_qp : MulIdx nArr aZ aY aX aA aP aT := by decide

/-- `keyBodyW`: for a balanced key, the mask is `cW` of what the checks compute. -/
theorem keyBodyW_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) (hw : g.w % 2 = 0)
    (hp : v.p < 2 ^ (32 * (g.w / 2))) (hq : v.q < 2 ^ (32 * (g.w / 2))) :
    WP isa keyBodyW s fun t => ∃ R₁ R₂, ProdsW g v R₁ R₂ ∧ ∃ A live, Stg g s A live (cW g v R₁ R₂) t := by
  have kb := h.kb
  have hw6 : 6 ≤ g.w := by simp only [Geo.w]; omega
  have wle : g.w ≤ 1024 := by simp only [Geo.w]; omega
  unfold keyBodyW crtChecksW dChecksW
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (first_ok h) fun t0 h0 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h0.mulLo_ok (o := aVQ) (x := aP) (y := aQ) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) (by decide) (by decide) hw (by omega) hp) fun t1 h1 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h1.eqA_ok (a := aVQ) (b := aN) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m1 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m2 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h13.mulLo_ok (o := aT) (x := aQ) (y := aQI) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) (by decide) (by decide) hw (by omega) hq) fun t14 h14 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (divK_ok h14 (a := aT) (d := aP) (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hw6 hp (by decide)) fun t15 h15 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h15.eqA_ok (a := aVR) (b := aOne) (by decide) (by decide) (by decide)) fun t16 h16 => ?_
  -- `d`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h16.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t17 h17 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  have p2 : 2 * (v.p / 2) < 2 ^ (32 * (g.w / 2)) := Nat.lt_of_le_of_lt (by omega) hp
  have q2 : 2 * (v.q / 2) < 2 ^ (32 * (g.w / 2)) := Nat.lt_of_le_of_lt (by omega) hq
  refine WP.mono (divK_ok h17 (a := aD) (d := aM1) (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hw6 p2 (by decide)) fun t18 h18 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h18.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide) (by decide)) fun t19 h19 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (divK_ok h19 (a := aD) (d := aM2) (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hw6 q2 (by decide)) fun t20 h20 => ?_
  exact WP.mono (h20.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide) (by decide)) fun t h21 =>
    ⟨R₁, R₂, ⟨hR₁, hR₂⟩, _, _, h21⟩

end VG.Proof.Rsa.Arm.KeyCheck
