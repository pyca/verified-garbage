module
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarryWord

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEightRaw
open VG.Proof.MlKem.AArch64 (Keep)

def carryPrefix (n : Nat) : List Instr := (List.range n).flatMap SquareEightRaw.carryWord

private theorem carry_join {old new digit next c prior rhs radix weight : Nat}
    (hp : new + weight*c = old + prior)
    (hd : digit + radix*next = rhs+c) :
    new + weight*digit + (weight*radix)*next = old + weight*rhs + prior := by grind

/-- Propagate the inter-tile carry through all seven remaining high words.
The final carry is retained in the equation, rather than assumed absent. -/
theorem carryPrefix_ok {s : State} {B : Addr} {Z e n : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e + 64 + 8*(n+1) ≤ Z) (hn : n+1 ≤ 7) :
    WP isa (.block (carryPrefix (n+1))) s fun t =>
      wv t.mem B (e+64) (n+1) + 2 ^ (64*(n+1))*t.c.toNat =
        wv s.mem B (e+64) (n+1) + (s.gpr .x10).toNat ∧
      Outside B (e+64) (8*(n+1)) s.mem t.mem ∧ Keep [.x13] s t := by
  have hwrap := hs.nowrap
  induction n with
  | zero =>
    change WP isa (.block (SquareEightRaw.carryWord 0)) s _
    refine WP.mono (firstCarry_ok hs h16 (by omega)) fun t ⟨⟨v, hm, hv⟩, kt⟩ => ?_
    refine ⟨?_, ?_, kt⟩
    · rw [hm]
      simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
        word_writeW_self] using hv
    · rw [hm]
      exact writeW_outside s.mem B v (by omega)
  | succ n ih =>
    rw [carryPrefix, List.range_succ, List.flatMap_append]
    apply WP.block_append
    refine WP.mono (ih (by omega) (by omega)) fun t ⟨htv, hto, kt⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (nextCarry_ok (hs.congr kt.wr) ((kt.gpr _ (by decide)).trans h16)
      ((kt.gpr _ (by decide)).trans h7) (by omega) (by omega) (by omega))
      fun u ⟨⟨v, hm, hv⟩, ku⟩ => ?_
    have offeq : e + 8*(n+1+8) = e+64+8*(n+1) := by omega
    rw [offeq] at hm hv
    have ho : Outside B (e+64+8*(n+1)) 8 t.mem u.mem := by
      rw [hm]
      exact writeW_outside t.mem B v (by omega)
    have hold := hto.word (d := e+64+8*(n+1)) (by omega) (by omega)
    rw [hold] at hv
    refine ⟨?_, (hto.mono (by omega) (by omega)).trans (ho.mono (by omega) (by omega)),
      (kt.trans ku).mono (by simp)⟩
    have hrec : wv s.mem B (e+64) (n+1+1) =
        wv s.mem B (e+64) (n+1) + 2 ^ (64*(n+1)) * (word s.mem B (e+64+8*(n+1))).toNat := rfl
    rw [hrec]
    rw [hm, wv_writeW_top _ _ _ _ _ (by omega), pow64_succ (n+1)]
    exact carry_join htv hv

theorem finishCarry_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e + 120 ≤ Z) :
    WP isa (.block finishCarry) s fun t =>
      wv t.mem B (e+64) 7 + 2 ^ (64*7)*t.c.toNat =
        wv s.mem B (e+64) 7 + (s.gpr .x10).toNat ∧
      Outside B (e+64) 56 s.mem t.mem ∧ Keep [.x13] s t := by
  simpa only [show 6+1 = 7 from rfl, show 8*7 = 56 from rfl, carryPrefix, finishCarry] using
    carryPrefix_ok (n := 6) hs h16 h7 (by omega) (by decide)

end VG.Proof.Bignum.AArch64.SquareEight
