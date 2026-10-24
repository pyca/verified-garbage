module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem

/-!
# An FFDH parameter candidate on PPC64LE: the entry

`entryA_ok`: `scratch_len` from the stack, the save area's address in
`r11`, the link register saved.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE.Search (rw_off rw_self)

theorem entryA_ok {s : State} {B : Addr} {n : Nat} (h10 : s.gpr .r10 = B) (hn : stackArg s 0 = BitVec.ofNat 64 n)
    (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (hn160 : 160 ≤ 8 * n)
    (hsv : InRegions s.wr (off B (8 * n - 160 + 144)) 8) :
    WP isa (.block [.addSp .r11 96, .load .d .r12 .r11 0, .lsl .r11 .r12 3, .add .r11 .r10 .r11,
      .subi .r11 .r11 saveBytes, .mflr .r0, .store .d .r0 .r11 144]) s fun t =>
      (t.gpr .r11 = off B (8 * n - 160) ∧ t.gpr .r12 = BitVec.ofNat 64 n ∧
        t.mem = s.mem.writeW (off B (8 * n - 160 + 144)) s.lr) ∧ Keep [.r0, .r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, stackArg, Nat.reduceMul, Nat.reduceAdd] at hargs hn
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  have e1 : B + BitVec.ofNat 64 (8 * n) - BitVec.ofNat 64 160 = off B (8 * n - 160) :=
    VG.Offset.add_ofNat_sub B hn160
  prun [ea, hargs, hn, h10, Pub.ofNat_shl3, saveBytes, e1, exec_mflr, off_add, hsv]

/-- The first `k` registers saved, from the state `s₀` after `entryA`. -/
structure SV (B : Addr) (n : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside B (8 * n - 160) 160 s₀.mem s.mem
  saved : ∀ i < k, word s.mem B (8 * n - 160 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i)
  lrW : word s.mem B (8 * n - 160 + 144) = word s₀.mem B (8 * n - 160 + 144)

theorem save_step {B : Addr} {n : Nat} {s₀ : State} (h11 : s₀.gpr .r11 = off B (8 * n - 160))
    (hn160 : 160 ≤ 8 * n) (hn : 8 * n < 2 ^ 63)
    (hin : ∀ i < 18, InRegions s₀.wr (off B (8 * n - 160 + 8 * i)) 8) {k : Nat} (hk : k < 18) {s : State}
    (h : SV B n s₀ k s) : WP isa (.block [.store .d (Impl.Ffdh.PPC64LE.ParameterCandidate.saved k) .r11 (8 * k)]) s (SV B n s₀ (k + 1)) := by
  have hw : s.gpr .r11 = off B (8 * n - 160) := by rw [h.gpr, h11]
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.wr, hw, off_add]; exact hin k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r11 ≠ .r0 by decide) (show 8 * k < 2 ^ 15 ∧ (8 * k) % 4 = 0 by omega) hout,
    Option.some.injEq, exists_eq_left', hw, off_add]
  have hW := writeW_outside s.mem B (d := 8 * n - 160 + 8 * k) (s.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved k)) (by omega)
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr, h.out.trans (hW.mono (by omega) (by omega)), fun i hi => ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · simp only [word, off]
      rw [rw_off _ _ _ (by omega) (by omega) (by omega)]
      exact h.saved i hi
    · simp only [word, off]; rw [rw_self, h.gpr]
  · simp only [word, off] at h ⊢
    rw [rw_off _ _ _ (by omega) (by omega) (by omega)]
    exact h.lrW

theorem map_flatMap {α β : Type} (g : α → β) (l : List α) : l.map g = l.flatMap fun i => [g i] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem saves_ok {B : Addr} {n : Nat} {s₀ : State} (h11 : s₀.gpr .r11 = off B (8 * n - 160))
    (hn160 : 160 ≤ 8 * n) (hn : 8 * n < 2 ^ 63)
    (hin : ∀ i < 18, InRegions s₀.wr (off B (8 * n - 160 + 8 * i)) 8) :
    WP isa (.block ((List.range 18).map fun i => .store .d (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i) .r11 (8 * i))) s₀ (SV B n s₀ 18) := by
  rw [map_flatMap]
  exact wp_range_flatMap (M := isa) (SV B n s₀) (fun k s hk h => save_step h11 hn160 hn hin hk h) 18
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), rfl⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
