module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The blocks after the last group, as a masked group: after the rounds

`remMaskG_ok`: from `r9 = 16 + r`, `StitchZH.remMaskG` puts in `r10` the mask
of the last register's `c = (r - 1) mod 4 + 1` blocks (`maskG_ok`: its
quadwords are the first `2 c`). `tailG_ok`: then `xorG`, `hashG` and `fin`
add the data at `src` to the keystream in the registers and store the `r`
blocks to `rdx`, and put in `Y` the four lanes' products of the blocks
stored, reduced and added (`laneAccG`, the powers after the `r` blocks
zero: `laneAccG_pad`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (fin)
open VG.Impl.Gcm.X86_64.StitchZH (remMaskG xorG hashG)
open VG.Proof.Gcm.X86_64.StitchZ (aregs_ok fin_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt)

/-- The masks of one to four blocks: their first `2 c` quadwords. -/
theorem maskG_ok : ∀ c < 5, 1 ≤ c →
    State.qOn (BitVec.ofNat 64 (4 ^ c - 1)) = List.range (2 * c) ∧
      ∀ j < 8, (BitVec.ofNat 64 (4 ^ c - 1)).getLsbD j = decide (j < 2 * c) := by decide

/-- The mask of the last register's `(r - 1) mod 4 + 1` blocks, in `r10`. -/
theorem remMaskG_ok (s : State) {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) :
    WP isa remMaskG s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (4 ^ ((r - 1) % 4 + 1) - 1) ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.mono (testR9_ok s 1) fun t ⟨z, g, l, m, rd, wr⟩ => ?_)
  have zt : t.zf = some (decide (r % 2 = 0)) := by rw [z, h9, test1 r hr]
  refine WP.ite (decide (r % 2 = 0)) (by simp only [eval, zt]) (fun h => ?_) (fun h => ?_)
  all_goals refine WP.seq (WP.mono (testR9_ok t 2) fun t₂ ⟨z₂, g₂, l₂, m₂, rd₂, wr₂⟩ => ?_)
  all_goals have zt₂ : t₂.zf = some (decide (r % 4 < 2)) := by rw [z₂, g, h9, test2 r hr]
  all_goals refine WP.ite (decide (r % 4 < 2)) (by simp only [eval, zt₂]) (fun h' => ?_) (fun h' => ?_)
  all_goals refine WP.mono (movR10_ok t₂ _) fun t' ⟨a, b, c, d, e, f⟩ => ⟨?_, fun q hq => by rw [b q hq, g₂, g],
    fun x l' => by rw [c, l₂, l], by rw [d, m₂, m], by rw [e, rd₂, rd], by rw [f, wr₂, wr]⟩
  all_goals rw [a]
  all_goals simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h h'
  · rw [show (r - 1) % 4 + 1 = 4 by omega]; decide
  · rw [show (r - 1) % 4 + 1 = 2 by omega]; decide
  · rw [show (r - 1) % 4 + 1 = 1 by omega]; decide
  · rw [show (r - 1) % 4 + 1 = 3 by omega]; decide

/-- The registers of a group of `k`. -/
theorem aregs_take (k : Nat) : (aregs.take k).Nodup ∧ .xmm13 ∉ aregs.take k ∧ ∀ b ∈ aregs.take k, b ∈ aregs := by
  obtain ⟨hnd, h13, _⟩ := aregs_ok
  exact ⟨hnd.sublist (List.take_sublist _ _), fun h => h13 (List.mem_of_mem_take h),
    fun _ h => List.mem_of_mem_take h⟩

/-- After the rounds of a group of `k` registers for the last `r` blocks:
the data at `src` (`S`) added to their keystream (`K`), the `r` blocks
stored to `rdx` (`A`), and `Y` the four lanes' products of them with the
powers at `rax` (`W`), from `Y` in `xmm2`, reduced and added. -/
theorem tailG_ok (src : Reg) (hsrc : src ≠ .r10) {k r : Nat} (hk4 : k ≤ 4) (hr1 : 1 ≤ r) (hr15 : r ≤ 15) (hrk : r ≤ 4 * k)
    (hkr : 4 * k < r + 4) {t : State} {A S W : Addr} {K D T : Nat → Block} {y : Block}
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hA : t.gpr .rdx = A) (hS : t.gpr src = S) (hW : t.gpr .rax = W)
    (hks : ∀ n < r, XBinOp.eval .pshufb (t.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask = K n)
    (hD : ∀ n < r, blockAt t.mem (S + BitVec.ofNat 64 (16 * n)) = D n)
    (hT : ∀ n < r, t.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinS : InRegions (t.rd ++ t.wr) S (16 * r)) (hinD : InRegions t.wr A (16 * r))
    (hinW : InRegions (t.rd ++ t.wr) W (16 * r))
    (hsep : ∀ n q', q' < n / 4 → n < r →
      Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A + BitVec.ofNat 64 (64 * q'), 64⟩)
    (hWA : ∀ n < r, Region.Disjoint ⟨W + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A, 16 * r⟩)
    (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask) (h1 : ∀ l < 4, t.zlane .xmm1 l = poly)
    (h2 : ∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0) :
    WP isa (.seq remMaskG (.block (xorG src (aregs.take k) 0 ++ hashG (aregs.take k) 0 ++ fin))) t fun t' =>
      (∀ n < r, blockAt t'.mem (A + BitVec.ofNat 64 (16 * n)) = D n ^^^ K n) ∧
      Frame [⟨A, 16 * r⟩] t.mem t'.mem ∧
      t'.zlane .xmm2 0 =
        (reduceB (laneAccG (fun n => D n ^^^ K n) T y 0 r) ^^^ reduceB (laneAccG (fun n => D n ^^^ K n) T y 2 r)) ^^^
          (reduceB (laneAccG (fun n => D n ^^^ K n) T y 1 r) ^^^ reduceB (laneAccG (fun n => D n ^^^ K n) T y 3 r)) ∧
      (∀ l, 1 ≤ l → l < 4 → t'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) →
        ∀ l < 4, t'.zlane x l = t.zlane x l) := by
  obtain ⟨hnd, h13, hin⟩ := aregs_take k
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega
  have hk1 : 1 ≤ k := by omega
  have hc : 4 * ((aregs.take k).length - 1) + ((r - 1) % 4 + 1) = r := by rw [hlen]; omega
  have hc16 : 64 * ((aregs.take k).length - 1) + 16 * ((r - 1) % 4 + 1) = 16 * r := by rw [hlen]; omega
  obtain ⟨mq, mb⟩ := maskG_ok ((r - 1) % 4 + 1) (by omega) (by omega)
  refine WP.seq (WP.mono (remMaskG_ok t hr1 (by omega) h9) fun t₁ ⟨a₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 (64 * 0) = a := fun a => BitVec.add_zero a
  refine WP.mono (xorG_ok src (aregs.take k) 0 t₁ (c := (r - 1) % 4 + 1) (by
      intro h; rw [h] at hlen; simp at hlen; omega) hnd h13 (by omega)
      (by rw [a₁]; exact mq) (by rw [a₁]; exact mb)
      (by rw [rd₁, wr₁, g₁ _ hsrc, hS, e0, hc16]; exact hinS)
      (by rw [wr₁, g₁ _ (by decide), hA, e0, hc16]; exact hinD)
      (fun n q' hq hn => by
        rw [g₁ _ hsrc, g₁ _ (by decide), hS, hA, Nat.mul_zero, Nat.zero_add, Nat.zero_add]
        exact hsep n q' hq (by omega))
      (by rw [hlen]; omega)) fun t₂ ⟨b₂, z₂, f₂, g₂, rd₂, wr₂, k₂⟩ => ?_
  rw [hc, g₁ _ (by decide), hA] at b₂ z₂
  rw [hc16, g₁ _ (by decide), hA, e0] at f₂
  rw [g₁ _ hsrc, hS] at b₂
  simp only [Nat.mul_zero, Nat.zero_add] at b₂ z₂
  -- The lanes of the registers, now the blocks stored, and the powers.
  let X' : Nat → Block := fun n => XBinOp.eval .pshufb (t₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask
  let T₀ : Nat → BitVec 128 := fun n => t₂.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128
  have hT₀ : ∀ n < r, T₀ n = T n := fun n hn => by
    show t₂.mem.readW _ 128 = _
    rw [f₂.readW (r := ⟨W + BitVec.ofNat 64 (16 * n), 16⟩) (Region.contains_self _ _)
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hWA n hn) (by decide), m₁]
    exact hT n hn
  have hX' : ∀ n < r, X' n = D n ^^^ K n := fun n hn => by
    show XBinOp.eval .pshufb _ revMask = _
    rw [z₂ n hn, b₂ n hn, m₁, hD n hn]
    congr 1
    rw [← hks n hn, l₁]
  have hW₂ : t₂.gpr .rax = W := by rw [g₂, g₁ _ (by decide), hW]
  have keep₂ : ∀ x, x ∉ aregs.take k → x ≠ .xmm13 → ∀ l < 4, t₂.zlane x l = t.zlane x l := fun x hx h13' l hl => by
    rw [k₂ x hx h13' l hl, l₁]
  have nA : ∀ x, x ∉ aregs → x ∉ aregs.take k := fun x hx h => hx (List.mem_of_mem_take h)
  refine WP.mono (hashG_ok (aregs.take k) 0 t₂ (c := (r - 1) % 4 + 1) X' (fun n => if n < r then T₀ n else 0) y
      (by intro h; rw [h] at hlen; simp at hlen; omega) hin (by omega) (by omega)
      (by rw [g₂, a₁]; exact mq) (by rw [g₂, a₁]; exact mb)
      (fun l hl => by rw [keep₂ _ (nA _ (by decide)) (by decide) l hl, h0 l hl])
      (fun l hl => by rw [keep₂ _ (nA _ (by decide)) (by decide) l hl, h2 l hl])
      (by rw [hW₂, e0, hc16, rd₂, wr₂, rd₁, wr₁]; exact hinW)
      (fun n _ => by simp only [Nat.mul_zero, Nat.zero_add]; rfl)
      (fun n _ => by simp only [Nat.mul_zero, Nat.zero_add, hc, hW₂]; rfl)
      (fun h => absurd rfl h)) fun t₃ ⟨p₃, f₃⟩ => ?_
  refine WP.mono (fin_ok t₃ fun l hl => by
      rw [f₃.zlane _ (by decide) l hl, keep₂ _ (nA _ (by decide)) (by decide) l hl, h1 l hl])
    fun t' ⟨y', y1', f'⟩ => ?_
  have acc : ∀ l < 4, prod (t₃.zproj l) = laneAccG (fun n => D n ^^^ K n) T y l r := fun l hl => by
    rw [p₃ l hl, Nat.zero_add, laneAccG_pad X' T₀ y l r (4 * (aregs.take k).length) (by rw [hlen]; omega)]
    exact laneAccG_congr y l r hX' hT₀
  refine ⟨fun n hn => ?_, ?_, ?_, y1', fun q hq => ?_, ?_, ?_, fun x hx hx' l hl => ?_⟩
  · rw [f'.mem, f₃.mem, ← z₂ n hn]; exact hX' n hn
  · rw [f'.mem, f₃.mem, ← m₁]; exact f₂
  · rw [y', acc 0 (by decide), acc 1 (by decide), acc 2 (by decide), acc 3 (by decide)]
  · rw [f'.gpr, f₃.gpr, g₂, g₁ q hq]
  · rw [f'.rd, f₃.rd, rd₂, rd₁]
  · rw [f'.wr, f₃.wr, wr₂, wr₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    obtain ⟨n13, n12, n7, n8, n9, n10, n11, n2⟩ := hx'
    rw [f'.zlane x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨n8, n9, n10, n11, n11, n10, n11, n2⟩) l hl,
      f₃.zlane x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨n12, n7, n8, n9, n10, n11⟩) l hl, keep₂ x (nA x hx) n13 l hl]

end VG.Proof.Gcm.X86_64.StitchZH
