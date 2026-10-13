module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Chunk
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 and Poly1305 together (x86-64): a chunk's rounds with `vprold`

`Stitch.sroundsVL` is `Stitch.srounds` with AVX-512VL's `vprold`, as
`Avx2.roundsVL` is `Avx2.rounds`: words 10 and 11 loaded into `ymm14`,
`ymm15` (`Avx2.loadV_ok`), the double rounds with every word in its register
(`Avx2.HoldsV`) and the pieces of Poly1305 between their quarter rounds, then
the words stored back (`Avx2.storeV_ok`). The quarter rounds keep memory and
every general-purpose register, and the pieces keep memory and the vector
registers, so they compose under an invariant of both (`SIV`), and the
rounds end in `SR`, as `srounds` does (`sroundsVL_ok`, and `sroundsFor_ok`
for either).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds HoldsV RV M16 bufR slotsR quarterV_ok doubleRoundV_ok
  loadV_ok storeV_ok)
open VG.Proof.ChaCha20 (CState)
open VG.Proof.Poly1305.X86_64 (Keeps absorbRegs)
open VG.Spec.ChaCha20 (innerBlock qround)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- Within a double round with `vprold`: the eight states `vs` in their
registers (`HoldsV`), memory and the kernel's registers as at `s₁`, and
Poly1305's registers satisfying `Q`. -/
structure SIV (s₁ : State) (vs : Nat → CState) (Q : State → Prop) (s : State) : Prop where
  holds : HoldsV vs s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

section
variable {buf q : Addr} {R0 R1 : BitVec 64} {X : Nat} {s₁ : State}

theorem quarterV_siv {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : [x, y, z, w].Nodup) {vs : Nat → CState} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') {s : State} (h : SIV s₁ vs Q s) :
    WP isa (Impl.ChaCha20.X86_64.Avx2.quarterV x y z w) s
      (SIV s₁ (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) Q) :=
  WP.mono (quarterV_ok hx hy hz hw hq h.holds) fun s' ⟨hh, hg, hm, hrd, hwr⟩ =>
    ⟨hh, by rw [hm, h.mem], fun r hr => by rw [hg, h.gpr r hr], by rw [hrd, h.rd],
      by rw [hwr, h.wr], hQ s s' hg h.poly⟩

/-- A piece of Poly1305 keeps the kernel's state. -/
theorem SIV.piece {vs : Nat → CState} {Q Q' : State → Prop} {s s' : State}
    (h : SIV s₁ vs Q s) (hq : Q' s') (k : Keeps absorbRegs s s') (hx : s'.xmm = s.xmm)
    (hy : s'.ymmHi = s.ymmHi) : SIV s₁ vs Q' s' :=
  ⟨fun k' hk' l q' hl hq' => by
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using h.holds k' hk' l q' hl hq',
    by rw [k.2.1, h.mem], fun r hr => by rw [k.1 r hr, h.gpr r hr], by rw [k.2.2.1, h.rd],
    by rw [k.2.2.2, h.wr], hq⟩

theorem addProdV_si (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q)
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {j : Nat} (hj : j < 32) {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (addProd j)) s (SIV s₁ vs (HalfTo q R0 R1 X s₁ j)) := by
  refine WP.mono (addProd_ok hk h.poly (p := q) (by rw [h.gpr _ (by decide), hrsi]) (j := j)
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega)) fun s' ⟨a, k, x, y⟩ => h.piece ?_ k x y
  show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
  rw [Nat.mul_add, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega)]
  rw [h.mem] at a
  exact a

theorem carryV_si (hk : Key R0 R1) {j : Nat} {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (HalfTo q R0 R1 X s₁ j) s) :
    WP isa (.block Impl.Poly1305.X86_64.carry) s (SIV s₁ vs (AccTo q R0 R1 X s₁ (j + 1))) :=
  WP.mono (carry1_ok hk h.poly) fun _ ⟨a, k, x, y⟩ => h.piece a k x y

section
variable (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q)
  (hin : ∀ off n, off + n ≤ 512 → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrsi hin

theorem sround4V_ok {j : Nat} (hj : j + 4 ≤ 32) {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround4V j) s (SIV s₁ (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 4))) := by
  unfold sround4V
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₄) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁₃) fun t₁₅ h₁₅ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁₅) fun t₁₆ h₁₆ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₆) fun t₁₇ h₁₇ => ?_)
  exact carryV_si hk h₁₇

theorem sround3V_ok {j : Nat} (hj : j + 3 ≤ 32) {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround3V j) s (SIV s₁ (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 3))) := by
  unfold sround3V
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₃) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁₁) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₄) fun t₁₅ h₁₅ => ?_)
  exact carryV_si hk h₁₅

omit hk hrsi hin in
/-- A double round with `vprold` absorbing nothing. -/
theorem sround0V_ok {j : Nat} {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRoundV s
      (SIV s₁ (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ j)) :=
  WP.mono (doubleRoundV_ok (s₁ := s) ⟨h.holds, rfl, rfl, rfl, rfl⟩) fun s' ⟨hh, hg, hm, hrd, hwr⟩ =>
    ⟨hh, by rw [hm, h.mem], fun r hr => by rw [hg, h.gpr r hr], by rw [hrd, h.rd],
      by rw [hwr, h.wr], acc_gpr s s' hg h.poly⟩

theorem sroundsV_ok (pre : Bool) {V : Nat → CState} {s : State}
    (h : SIV s₁ V (AccTo q R0 R1 X s₁ (firstBlock pre 0)) s) : ∀ n, n ≤ 10 →
    WP isa (sroundsV pre n) s
      (SIV s₁ (fun j => Nat.repeat innerBlock n (V j)) (AccTo q R0 R1 X s₁ (firstBlock pre n)))
  | 0, _ => WP.block_nil h
  | n + 1, hn => by
    refine WP.seq (WP.mono (sroundsV_ok pre h n (by omega)) fun s hs => ?_)
    have hb' : firstBlock pre n + blocks pre n ≤ 32 := by
      rw [← firstBlock_succ]; exact Nat.le_trans (firstBlock_le pre (by omega)) (total_le pre)
    show WP isa (sroundV pre n) s _
    rw [firstBlock_succ]
    unfold sroundV
    rcases blocks_cases pre n with e | e | e
    · rw [ite_eq_left e]
      rw [e] at hb' ⊢
      exact sround4V_ok hk hrsi hin hb' hs
    · rw [ite_eq_right (by omega), ite_eq_left e]
      rw [e] at hb' ⊢
      exact sround3V_ok hk hrsi hin hb' hs
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), e, Nat.add_zero]
      exact sround0V_ok hs

/-- A chunk's rounds with `vprold` end as `srounds` does. -/
theorem sroundsVL_ok (pre : Bool) {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h16 : M16 s₁.mem buf) (n : Nat) (hn : n ≤ 10)
    (h : SR pre buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsVL pre n) s₁ (SR pre buf q R0 R1 X V s₁ n) := by
  unfold sroundsVL
  refine WP.seq (WP.mono (loadV_ok h.holds hrcx hb) fun s₂ ⟨h₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : SIV s₁ V (AccTo q R0 R1 X s₁ (firstBlock pre 0)) s₂ :=
    ⟨h₂, m₂, fun r _ => by rw [g₂], rd₂, wr₂, acc_gpr s₁ s₂ g₂ h.acc⟩
  refine WP.seq (WP.mono (sroundsV_ok hk hrsi hin pre i₂ n hn) fun s₃ h₃ => ?_)
  have r₃ : s₃.gpr .rcx = buf := by rw [h₃.gpr _ (by decide), hrcx]
  refine WP.mono (storeV_ok (s₀ := s₃) ⟨h₃.holds, rfl, rfl, rfl, rfl⟩ r₃ (by rw [h₃.wr]; exact hb)
    (by rw [h₃.mem]; exact h16)) fun s₄ h₄ => ?_
  exact ⟨h₄.holds, h₄.m16, by rw [← h₃.mem]; exact h₄.frame, fun r hr => by rw [h₄.gpr, h₃.gpr r hr],
    by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr], acc_gpr s₃ s₄ h₄.gpr h₃.poly⟩

/-- A chunk's rounds, with `vprold` or without. -/
theorem sroundsFor_ok (vl pre : Bool) {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h8 : Proof.ChaCha20.X86_64.Avx2.M8 s₁.mem buf) (h16 : M16 s₁.mem buf)
    (hd : (Proof.ChaCha20.X86_64.Avx2.dR5 q).Disjoint (slotsR buf))
    (h : SR pre buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsFor vl pre) s₁ (SR pre buf q R0 R1 X V s₁ 10) := by
  cases vl
  · exact srounds_ok hk hrcx hrsi hb h8 hd hin pre 10 (by decide) h
  · exact sroundsVL_ok hk hrsi hin pre hrcx hb h16 10 (by decide) h

end

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
