module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.Block

/-!
# The checks of an RSA key on PPC64LE: the products

From `Stg`: the product truncated to `w` digits (`Stg.mulLo_ok`) and
Montgomery's multiplication modulo `p | 1`, in `aVD` (`Stg.montP_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)
open VG.Proof.Rsa.PPC64LE.MontKey (mulLo_ok montMul_ok mkRegs val32_low)

theorem mkRegs_body : ∀ x ∈ mkRegs, x ∈ bodyRegs := by decide

/-- `orOne j`. -/
theorem Stg.orOne_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.orOne j)) s (Stg g s0 (upd A j (2 * (A j / 2) + 1)) live c) := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.orOne j)]
  refine orOne_top_ok h.ws (h.live_lt j hj) (by decide) fun t ht k e r top => WP.block_nil ?_
  refine h.next ht k (by simpa using h.live_lt j hj) (by simp) r KeyCheck.opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt ?_ (h.mask_keep k (by simp))
  by_cases hv : j = aVD
  · subst hv; rw [top, h.vdTop]
  · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `mulLo o x y r19`: `[o] := [x] [y] mod 2^(32 w)`, for `[x] < 2^(8 L)`,
`L = p_len` in `r19`. -/
theorem Stg.mulLo_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o x y : Nat} (ho : o < nArr) (hx : x ∈ live) (hy : y ∈ live)
    (hfree : ∀ j ∈ live, j ≠ o) (hoVD : o ≠ aVD) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * g.w) (hxL : A x < 2 ^ (8 * L)) :
    WP isa (VG.Impl.Rsa.PPC64LE.MontKey.mulLo o x y .r19) s
      (Stg g s0 (upd A o (A x * A y % 2 ^ (32 * g.w))) (o :: live) c) := by
  have nx := h.live_lt x hx
  have ny := h.live_lt y hy
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulLo_ok h.ws (by decide) ho nx ny (fun e => hfree x hx e.symm) (fun e => hfree y hy e.symm)
    hl hL1 hLw (by decide) (by decide)) fun t ⟨ht, k, v, r⟩ => ?_
  have vx : val32 s.mem g.B (arr g.w x) ((L + 3) / 4) = A x :=
    val32_low (h.arrs.get hx) (by omega) (Nat.lt_of_lt_of_le hxL (Nat.pow_le_pow_right (by decide) (by omega)))
  have e : num t.mem g.B g.w o = A x * A y % 2 ^ (32 * g.w) := by rw [v, vx, h.arrs.get hy]
  refine h.next ht k (by simpa using ho) (by simp) r mkRegs_body
    ((h.arrs_write k e (fun j hj => .inr (by simpa using hfree j hj)) (by simp)).cons (by rw [upd_self]; exact e))
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j)) (h.vd_keep k (by simpa using hoVD) (by simp))
    (h.mask_keep k (by simp))

/-- `montP a x y`: `[a] := [x] [y] 2^(-32 w) mod (p | 1)`, the modulus in
`aVD`: for `[y] < (p | 1)`, below it and congruent. -/
theorem Stg.montP_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a x y : Nat} (ha : a < nArr) (hx : x ∈ live) (hy : y ∈ live) (hVD : aVD ∈ live)
    (hfree : ∀ j ∈ live, j ≠ a ∧ j ≠ aT) (haT : a ≠ aT) (hyVD : aVD ≠ y) {L : Nat} (hl : s.gpr .r19 = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLw : (L + 3) / 4 ≤ g.w) (hodd : A aVD % 2 = 1) (hmt : A aVD < 2 ^ (32 * ((L + 3) / 4)))
    (hYt : A y < 2 ^ (32 * ((L + 3) / 4))) :
    WP isa (montP a x y) s fun t => ∃ R, (A y < A aVD → R < A aVD ∧
      R * 2 ^ (32 * g.w) % A aVD = A x * A y % A aVD) ∧ Stg g s0 (upd A a R) (a :: live) c t := by
  have nx := h.live_lt x hx
  have ny := h.live_lt y hy
  have nm := h.live_lt aVD hVD
  have hax : a ≠ x := fun e => (hfree x hx).1 e.symm
  have hay : a ≠ y := fun e => (hfree y hy).1 e.symm
  have ham : a ≠ aVD := fun e => (hfree aVD hVD).1 e.symm
  have htx : aT ≠ x := fun e => (hfree x hx).2 e.symm
  have hty : aT ≠ y := fun e => (hfree y hy).2 e.symm
  refine WP.mono (montMul_ok h.ws (by decide) ha nx ny nm (by decide) hax hay ham haT
    htx hty (by decide) hyVD hl hL1 hLw (by decide) (by decide) (h.arrs.get hVD) hmt hodd (h.arrs.get hy) hYt)
    fun t ⟨ht, k, nmv, nY, top, cg, r⟩ => ⟨num t.mem g.B g.w a, fun hlt => by
      have := cg hlt; rw [h.arrs.get hx] at this; exact this, ?_⟩
  have hnl : ∀ j ∈ [a, aT, aVD, y], j < nArr := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ha
    · decide
    · exact nm
    · exact ny
  refine h.next ht k hnl (by simp) r mkRegs_body ?_ ?_ top (h.mask_keep k (by simp))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [upd_self]
    · obtain ⟨hja, hjt⟩ := hfree j hj'
      rw [upd_ne _ _ hja]
      by_cases e1 : j = aVD
      · subst e1; exact nmv
      · by_cases e2 : j = y
        · subst e2; exact nY
        · rw [k.num (by
            intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> omega) (by simp) (h.ws.fit64 (h.live_lt j hj')),
            h.arrs.get hj']
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ha
    · exact h.live_lt j hj'

end VG.Proof.Rsa.PPC64LE.KeyCheck
