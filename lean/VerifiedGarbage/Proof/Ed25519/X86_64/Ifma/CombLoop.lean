module

import VerifiedGarbage.Proof.Ed25519.Group.Double
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombAdd
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ed25519's comb with AVX512_IFMA: doublings in the lanes

Four and five doublings of the point in the lanes (`vdbl4_ok`, `vdbl5_ok`),
as `Zmm.combMultiply` ends, an addition of a cached entry as `pointAdd`
(`vAddPt_cache`), and the lanes read as field elements.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord y ld)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr vm vm_gpr vm_rd vm_wr Ctx run_ok symOf symOf_eq Sym T envOf
  envOf_m envOf_v mq)
open VG.Proof.X25519.X86_64 (Outside F off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The sum -/

/-- The sum the lanes compute is `pointAdd` with a cached point. -/
theorem vAddPt_cache (P q : Spec.Ed25519.Point) :
    vAddPt P (cache q) = Spec.Ed25519.pointAdd P q := by
  simp only [vAddPt, cache, Spec.Ed25519.pointAdd]
  congr 1 <;> grind

/-! ## Four doublings -/

/-- The doublings' invariant, with `n` left. -/
structure DInv (s : State) (base : Addr) (a : EPoint dZ) (n : Nat) (t : State) : Prop where
  pos : 0 < n
  le : n ≤ 4
  rdi : t.gpr .rdi = base
  rsi : t.gpr .rsi = BitVec.ofNat 64 n
  gpr : ∀ r, r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 1024 320 s.mem t.mem
  consts : EConsts t.mem base
  small : Small t
  rep : Rep (lanePt t) ((2 ^ (4 - n) : Nat) • a)

theorem vdbl4_ok {s : State} {base : Addr} (hs : Scratch s base) (hk : EConsts s.mem base) (hx : Small s)
    {a : EPoint dZ} (ha : Rep (lanePt s) a) :
    WP isa vdbl4 s fun t => (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1024 320 s.mem t.mem ∧ Small t ∧ Rep (lanePt t) ((16 : Nat) • a) := by
  rw [vdbl4]
  refine WP.seq (WP.mono (mov32_wp s .rsi 4) fun s₁ ⟨r₁, g₁, m₁, rd₁, wr₁, q₁⟩ => ?_)
  have h₁ : DInv s base a 4 s₁ :=
    ⟨by decide, by decide, by rw [g₁ _ (by decide)]; exact hs.rdi, r₁, g₁, rd₁, wr₁,
      by rw [m₁]; exact Outside.refl _ _ _ _, by rw [m₁]; exact hk,
      fun l hl i hi => by rw [lanes_qw q₁]; exact hx l hl i hi, by rw [lanePt_qw q₁]; simpa using ha⟩
  refine WP.loop (DInv s base a) (fun n t h => ?_) 4 s₁ h₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.pos; omega_arith : n ≠ 0)
  have hst : Scratch t base := ⟨h.rdi, by rw [h.wr]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vdbl_wp h.rdi (ctx_of hst) h.consts h.small) fun u ⟨ug, urd, uwr, uo, usm, up⟩ => ?_
  refine WP.mono (dec_wp u k (by have := h.le; omega_arith) (by rw [ug]; exact h.rsi)) fun w ⟨wc, wz, kw, wq⟩ => ?_
  have wr' : w.gpr .rdi = base := by rw [kw.1 _ (by decide), ug]; exact h.rdi
  have wg : ∀ r, r ≠ .rsi → w.gpr r = s.gpr r := fun r hr' => by
    rw [kw.1 _ (by simpa using hr'), ug]; exact h.gpr r hr'
  have wrd : w.rd = s.rd := by rw [kw.2.2.1, urd]; exact h.rd
  have wwr : w.wr = s.wr := by rw [kw.2.2.2, uwr]; exact h.wr
  have wm : Outside base 1024 320 s.mem w.mem := by rw [kw.2.1]; exact h.mem.trans uo
  have wk : EConsts w.mem base := by rw [kw.2.1]; exact h.consts.outside uo
  have wsm : Small w := by intro l hl i hi; rw [lanes_qw wq]; exact usm l hl i hi
  have wp : Rep (lanePt w) ((2 ^ (4 - k) : Nat) • a) := by
    rw [lanePt_qw wq, up, show 4 - k = (4 - (k + 1)) + 1 by have := h.le; omega_arith, pow_succ, mul_nsmul,
      two_nsmul]
    exact dblPoint_rep h.rep.proj
  by_cases hk0 : k = 0
  · subst hk0
    exact Or.inl ⟨by simp only [eval, wz, decide_true, Option.map_some, Bool.not_true], wg, wrd, wwr, wm, wsm,
      by simpa using wp⟩
  · exact Or.inr ⟨by simp only [eval, wz, decide_eq_false hk0, Option.map_some, Bool.not_false],
      k, by omega_arith, ⟨by omega_arith, by have := h.le; omega_arith, wr', wc, wg, wrd, wwr, wm, wk, wsm, wp⟩⟩

/-- Five doublings: `vdbl4`'s, and one more. -/
theorem vdbl5_ok {s : State} {base : Addr} (hs : Scratch s base) (hk : EConsts s.mem base) (hx : Small s)
    {a : EPoint dZ} (ha : Rep (lanePt s) a) :
    WP isa vdbl5 s fun t => (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1024 320 s.mem t.mem ∧ Small t ∧ Rep (lanePt t) ((32 : Nat) • a) := by
  rw [vdbl5]
  refine WP.seq (WP.mono (vdbl4_ok hs hk hx ha) fun u ⟨ug, urd, uwr, uo, usm, up⟩ => ?_)
  have hsu : Scratch u base := ⟨by rw [ug _ (by decide)]; exact hs.rdi, by rw [uwr]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (vdbl_wp hsu.rdi (ctx_of hsu) (hk.outside uo) usm) fun t ⟨tg, trd, twr, tou, tsm, tp⟩ =>
    ⟨fun r hr => by rw [tg]; exact ug r hr, trd.trans urd, twr.trans uwr, uo.trans tou, tsm, ?_⟩
  rw [tp, show (32 : Nat) = 16 * 2 by rfl, mul_nsmul, two_nsmul]
  exact dblPoint_rep up.proj

/-! ## The entry's value -/

theorem val4_feWord (v : Spec.X25519.Fe) :
    VG.Proof.X25519.toFe ((feWord v 0).toNat + 2 ^ 64 * (feWord v 1).toNat + 2 ^ 128 * (feWord v 2).toNat +
      2 ^ 192 * (feWord v 3).toNat) = v := by
  have := feWord_val v
  simp only [VG.Proof.X25519.X86_64.val4] at this
  rw [this, VG.Proof.X25519.toFe_self]

/-! ## The loop's invariant -/

theorem lanes0_eq {s t : State} (h : ∀ r < 5, ∀ l < 4, qw t (xr r) l = qw s (xr r) l) :
    lanePt t = lanePt s ∧ (Small s → Small t) := by
  have e : ∀ l < 4, ∀ i < 5, lanes t 0 l i = lanes s 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]; rw [h i hi l hl]
  refine ⟨?_, fun hs l hl i hi => by rw [e l hl i hi]; exact hs l hl i hi⟩
  simp only [lanePt]
  rw [fe5_congr (e 0 (by decide)), fe5_congr (e 1 (by decide)), fe5_congr (e 2 (by decide)),
    fe5_congr (e 3 (by decide))]

theorem lanes0_vec {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    ∀ r < 5, ∀ l < 4, qw t (xr r) l = qw s (xr r) l := fun _ _ _ _ => qw_of hx hy _ _

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  simp only [combCached]; split <;> rfl

end VG.Proof.Ed25519.X86_64.Ifma
