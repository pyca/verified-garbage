module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.SmallMod
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A prime search on PPC64LE: the sieve

`sieve_ok`: `hBad` stays zero exactly when it was and no number of `ds`
divides the `w` words at `o`; `hBad` is the only word written.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

theorem flag_eq {r : Nat} (hr : r < 2 ^ 63) : (BitVec.ofNat 64 r - 1#64) >>> 63 = 0#64 ↔ r ≠ 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- `hBad` stored over `m`. -/
theorem bad_post {m : Mem} {B : Addr} {t : State} {v : BitVec 64} {P : Prop}
    (tm : t.mem = m.writeW (B + BitVec.ofNat 64 200) v) (hv : v = 0#64 ↔ P) :
    (word t.mem B (8 * hBad) = 0#64 ↔ P) ∧ Frm B [(8 * hBad, 8)] m t.mem := by
  refine ⟨?_, ?_⟩
  · simp only [word, off, hBad, Nat.reduceMul, tm, rw_self]; exact hv
  · rw [tm]
    exact frm_writeW (a := 200) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)

/-- The registers a trial division writes. -/
def trRegs : List Reg := .r22 :: .r4 :: smRegs

theorem trial_ok {s : State} {B : Addr} {Z o w x d : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B o)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hx : wv s.mem B o w = x) (hw1 : 1 ≤ w)
    (hw : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (hd2 : 2 ≤ d) (hd : d < 2 ^ 15) {P : Prop}
    (h22 : s.gpr .r22 = 0#64 ↔ P) :
    WP isa (trial d) s fun t => ((t.gpr .r22 = 0#64 ↔ P ∧ x % d ≠ 0) ∧ t.mem = s.mem) ∧ Keep trRegs s t := by
  unfold trial
  refine WP.seq (WP.mono (WP.keep [.r4] (Q := fun v => v.gpr .r4 = BitVec.ofNat 64 d ∧ v.mem = s.mem) ?_
    (by rfl)) fun v ⟨⟨v4, vm⟩, kv⟩ => ?_)
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li hd, gpr_write, mem_write, ↓reduceIte,
      Option.some.injEq, exists_eq_left', and_self]
  refine WP.seq (WP.mono (smallMod_ok (hs.congr kv.wr) ((kv.gpr .r10 (by decide)).trans h10)
    ((kv.gpr .r11 (by decide)).trans h11) v4 hw1 hw hZ hd2 (by omega)) fun t' ⟨⟨t3, tm'⟩, kt'⟩ => ?_)
  rw [vm, hx] at t3
  have k := kv.trans kt'
  have e22 : t'.gpr .r22 = s.gpr .r22 := k.gpr .r22 (by decide)
  refine WP.mono (WP.keep [.r3, .r22] (Q := fun t => t.gpr .r22 = t'.gpr .r22 |||
      (BitVec.ofNat 64 (x % d) - 1#64) >>> 63 ∧ t.mem = t'.mem) (by prun [t3]) (by decide))
    fun t ⟨⟨t22, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm, tm', vm]⟩, (k.trans kt).mono (by decide)⟩
  rw [t22, BitVec.or_eq_zero_iff, e22, h22, flag_eq (by have := Nat.mod_lt x (show 0 < d by omega); omega)]

theorem trials_ok {B : Addr} {Z o w x : Nat} (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z)
    (hZ8 : 208 ≤ Z) :
    ∀ (ds : List Nat), (∀ d ∈ ds, 2 ≤ d ∧ d < 2 ^ 15) → ∀ {u : State} {P : Prop}, Scr u B Z →
      u.gpr .r31 = B → u.gpr .r10 = off B o → u.gpr .r11 = BitVec.ofNat 64 (2 * w) → wv u.mem B o w = x →
      (u.gpr .r22 = 0#64 ↔ P) →
      WP isa (ds.foldr (fun d c => .seq (trial d) c) (.block [sth .r22 hBad])) u fun t =>
        ((word t.mem B (8 * hBad) = 0#64 ↔ P ∧ ∀ d ∈ ds, x % d ≠ 0) ∧ Frm B [(8 * hBad, 8)] u.mem t.mem) ∧
          Keep trRegs u t
  | [], _, u, P, hu, u31, _, _, _, h22 => by
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = u.mem.writeW (B + BitVec.ofNat 64 200) (u.gpr .r22)) ?_
      (by decide)) fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, kt.mono (by decide)⟩
    · simp only [List.foldr_nil, sth, hBad]
      prun [u31, hu.st (d := 200) (n := 8) (by omega)]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true]; exact h22
  | d :: ds, hds, u, P, hu, u31, u10, u11, ux, h22 => by
    have hd := hds d List.mem_cons_self
    refine WP.seq (WP.mono (trial_ok hu u10 u11 ux hw1 hw hZ hd.1 hd.2 h22) fun t' ⟨⟨t22, tm'⟩, kt'⟩ => ?_)
    refine WP.mono (trials_ok (x := x) hw1 hw hZ hZ8 ds (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
      (hu.congr kt'.wr) ((kt'.gpr .r31 (by decide)).trans u31) ((kt'.gpr .r10 (by decide)).trans u10)
      ((kt'.gpr .r11 (by decide)).trans u11) (by rw [tm']; exact ux) t22)
      fun t ⟨⟨tb, tf⟩, kt⟩ => ⟨⟨?_, by rw [← tm']; exact tf⟩, (kt'.trans kt).mono (by decide)⟩
    rw [tb, List.forall_mem_cons]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

theorem oddPrimes256_bounds : ∀ d ∈ oddPrimes256, 2 ≤ d ∧ d < 2 ^ 15 := by decide

theorem sieve_ok {s : State} {B : Addr} {Z o w x : Nat} (ds : List Nat) (hds : ∀ d ∈ ds, 2 ≤ d ∧ d < 2 ^ 15)
    (hs : Scr s B Z) (h31 : s.gpr .r31 = B) (h10 : s.gpr .r10 = off B o)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hx : wv s.mem B o w = x) (hw1 : 1 ≤ w)
    (hw : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (hZ8 : 208 ≤ Z) :
    WP isa (sieve ds) s fun t =>
      ((word t.mem B (8 * hBad) = 0#64 ↔ word s.mem B (8 * hBad) = 0#64 ∧ ∀ d ∈ ds, x % d ≠ 0) ∧
        Frm B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep trRegs s t := by
  unfold sieve
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = word s.mem B (8 * hBad) ∧ u.mem = s.mem)
    (by simp only [ldh, hBad, word, off]; prun [h31, hs.ld (d := 200) (n := 8) (by omega)]) (by decide))
    fun u ⟨⟨u22, um⟩, ku⟩ => ?_)
  refine WP.mono (trials_ok hw1 hw hZ hZ8 ds hds (hs.congr ku.wr) ((ku.gpr .r31 (by decide)).trans h31)
    ((ku.gpr .r10 (by decide)).trans h10) ((ku.gpr .r11 (by decide)).trans h11) (by rw [um]; exact hx)
    (P := word s.mem B (8 * hBad) = 0#64) (by rw [u22])) fun t ⟨⟨tb, tf⟩, kt⟩ =>
      ⟨⟨tb, by rw [← um]; exact tf⟩, (ku.trans kt).mono (by decide)⟩

end VG.Proof.MillerRabin.PPC64LE.Search
