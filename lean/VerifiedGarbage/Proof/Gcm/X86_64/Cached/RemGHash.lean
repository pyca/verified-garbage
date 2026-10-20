module
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGXor
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuadK
import VerifiedGarbage.Proof.Framework.X86_64.MaskedPrefix
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The blocks after the last group, hashed in registers

`hashG_ok`: `StitchZH.hashG rs j` multiplies the lanes of the registers
`rs`, byte-reversed (`Y` added to the first block), by the powers at
`rax + 64 j` …, the last register's loaded through the mask of its `c`
blocks, so that its other lanes are multiplied by zero: each lane's products
are `laneAccG`'s, block `n` in lane `n mod 4`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (hash1 hashG)
open VG.Proof.Gcm.X86_64.StitchZ (ldInit ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block)

/-- The SSE block of `hash1 b j` in each lane. -/
def hashSse (b : XReg) (j : Nat) : List Instr :=
  .xop (.bin .movdqa .xmm7 b) ::
    (if j = 0 then ([.xop (.bin .pshufb .xmm7 .xmm0), .xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ ldInit.tail
      else ldAcc false)

theorem lane_hash1 {b : XReg} (hb : b ∈ aregs) (j : Nat) : zlaneSseBlock (hash1 b j) = some (hashSse b j) := by
  simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb
  by_cases hj : j = 0 <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [hash1, hashSse, hj, ↓reduceIte] <;> rfl

theorem hashSse_ok {b : XReg} (hb : b ∈ aregs) (j : Nat) (t : State) :
    WP isa (.block (hashSse b j)) t fun t' =>
      prod t' = (if j = 0 then Prod.zero else prod t).acc
        ((if j = 0 then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm b) (t.xmm .xmm0)) (t.xmm .xmm12) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb
  by_cases hj : j = 0
  · apply WP.of_runBlock
    rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [hashSse, hj, ↓reduceIte, ldInit, List.tail_cons, List.cons_append, List.nil_append, reduceCtorEq,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm, Pclmul.eval_pxor, eval_movdqa,
      Option.some.injEq, exists_eq_left'] <;>
    refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩ <;>
    first
    | (simp only [prod, Prod.acc, Prod.zero, Stitch.zero_xor_b, reduceCtorEq, ↓reduceIte,
        BitVec.xor_comm (t.xmm .xmm2)]; done)
    | (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
       simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false])
  · simp only [hashSse, hj, ↓reduceIte]
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, WP.mono (ldAcc_ok false _) fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩⟩
    · rw [p']
      rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [XOp.exec, State.setXmm, eval_movdqa, prod, reduceCtorEq, ↓reduceIte, Bool.false_eq_true]
    · have o₁ : Only [.xmm7] t (XOp.exec (.bin .movdqa .xmm7 b) t) :=
        ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
          simp only [List.mem_singleton] at hr
          simp only [XOp.exec, State.setXmm, hr, ite_false]⟩
      exact (o₁.trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- The products of register `b`'s lanes, byte-reversed (`Y` added if
`j = 0`), with the powers in `zmm12`, written (`j = 0`) or added. -/
theorem hash1_ok {b : XReg} (hb : b ∈ aregs) (j : Nat) (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask) :
    WP isa (.block (hash1 b j)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (if j = 0 then Prod.zero else prod (t.zproj l)).acc
        ((if j = 0 then t.zlane .xmm2 l else 0) ^^^ XBinOp.eval .pshufb (t.zlane b l) revMask) (t.zlane .xmm12 l)) ∧
      ZFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  refine WP.mono (WP.zlanes (lane_hash1 hb j) fun l _ => hashSse_ok hb j (t.zproj l))
    fun t' ⟨hk, hq⟩ => ⟨fun l hl => ?_, ⟨hk.gpr, hk.mem, hk.rd, hk.wr, fun r hr l hl => ?_⟩⟩
  · rw [(hq l hl).1]; simp only [State.zproj_xmm, h0 l hl]
  · have := (hq l hl).2.xmm r hr
    simpa only [State.zproj_xmm] using this

/-- The 64 bytes at `b + d` in `zmm` `x`. -/
theorem ld512_ok (x : XReg) (b : Reg) (d : Nat) (t : State)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr b + BitVec.ofNat 64 d) 64) :
    WP isa (.block [.vmovdqu32Load x (at_ b d)]) t fun t' =>
      (∀ l < 4, t'.zlane x l = t.mem.readW (t.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128) ∧
      ZFrame [x] t t' := by
  rw [WP.block_cons_iff]
  refine ⟨setZv t x (t.mem.readW (t.gpr b + BitVec.ofNat 64 d) 512),
    by simp only [isa, exec, State.load512, ea_at', hin, ite_true, Option.map_some], WP.block_nil ⟨fun l hl => ?_,
      ⟨rfl, rfl, rfl, rfl, fun r hr l hl => State.zlane_setZ_ne _ (fun h => hr (List.mem_singleton.mpr h)) _ _ _ _ hl⟩⟩⟩
  rw [zlane_setZv _ _ _ hl]; exact load512_lane _ _ hl

/-- The `c` blocks at `b + d` in `zmm` `x`, through the mask in `r10`, and
zero in its other lanes. -/
theorem ld512K_ok (x : XReg) (b : Reg) (d : Nat) (t : State) {c : Nat} (hc : c ≤ 4)
    (hk : State.qOn (t.gpr .r10) = List.range (2 * c))
    (hbk : ∀ j < 8, (t.gpr .r10).getLsbD j = decide (j < 2 * c))
    (hin : InRegions (t.rd ++ t.wr) (t.gpr b + BitVec.ofNat 64 d) (16 * c)) :
    WP isa (.block [.kLoad .r10 x (at_ b d)]) t fun t' =>
      (∀ l < 4, t'.zlane x l =
        if l < c then t.mem.readW (t.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128 else 0) ∧
      ZFrame [x] t t' := by
  obtain ⟨v, ev, lv⟩ := State.loadMasked512_prefix (s := t) (a := t.gpr b + BitVec.ofNat 64 d) hc hk hbk hin
  rw [WP.block_cons_iff]
  refine ⟨setZv t x v, by simp only [isa, exec]; rw [ea_at', ev]; rfl, WP.block_nil ⟨fun l hl => ?_,
      ⟨rfl, rfl, rfl, rfl, fun r hr l hl => State.zlane_setZ_ne _ (fun h => hr (List.mem_singleton.mpr h)) _ _ _ _ hl⟩⟩⟩
  rw [zlane_setZv _ _ _ hl, lv l hl]

/-- A register's products, as the lanes' of the next four blocks. -/
theorem hashStep_eq {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {l j : Nat} (hl : l < 4) (p : Prod)
    (y2 x2 pw : BitVec 128) (hp : j ≠ 0 → p = laneAccG X T y l (4 * j)) (hy : y2 = if l = 0 then y else 0)
    (hx : X (4 * j + l) = x2) (hT : T (4 * j + l) = pw) :
    (if j = 0 then Prod.zero else p).acc ((if j = 0 then y2 else 0) ^^^ x2) pw = laneAccG X T y l (4 * (j + 1)) := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega, laneAccG_quad X T y j hl, hx, hT]
  by_cases hj : j = 0
  · subst hj
    simp only [ite_true, hy, Nat.mul_zero, Nat.zero_add]
    rfl
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hj), ite_eq_right_iff.mpr (fun h => absurd h hj), ← hp hj,
      ite_eq_right_iff.mpr (fun h => absurd (show j = 0 by omega) hj)]

/-- The registers `rs`, from the `j`-th, hashed with the powers at
`rax + 64 j` …, the last's through the mask of its `c` blocks: the lanes'
products are those of blocks `4 j` … `4 (j + |rs|)`, block `n` lane `n mod
4` of its register byte-reversed, with power `T n`, zero after the
`4 (|rs| - 1) + c`. -/
theorem hashG_ok : ∀ (rs : List XReg) (j : Nat) (t : State) {c : Nat} (X : Nat → Block) (T : Nat → BitVec 128)
    (y : Block), rs ≠ [] → (∀ b ∈ rs, b ∈ aregs) → rs.length ≤ 4 → c ≤ 4 →
    State.qOn (t.gpr .r10) = List.range (2 * c) → (∀ i < 8, (t.gpr .r10).getLsbD i = decide (i < 2 * c)) →
    (∀ l < 4, t.zlane .xmm0 l = revMask) → (∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0) →
    InRegions (t.rd ++ t.wr) (t.gpr .rax + BitVec.ofNat 64 (64 * j)) (64 * (rs.length - 1) + 16 * c) →
    (∀ n < 4 * rs.length, X (4 * j + n) = XBinOp.eval .pshufb (t.zlane (rs.getD (n / 4) .xmm0) (n % 4)) revMask) →
    (∀ n < 4 * rs.length, T (4 * j + n) =
      if n < 4 * (rs.length - 1) + c then t.mem.readW (t.gpr .rax + BitVec.ofNat 64 (16 * (4 * j + n))) 128
      else 0) →
    (j ≠ 0 → ∀ l < 4, prod (t.zproj l) = laneAccG X T y l (4 * j)) →
    WP isa (.block (hashG rs j)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = laneAccG X T y l (4 * (j + rs.length))) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t'
  | [], _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl h
  | [b], j, t, c, X, T, y, _, hrs, _, hc, hk, hbk, h0, h2, hin, hX, hT, hP => by
    have hb := hrs b (List.mem_singleton_self _)
    have hb12 : b ≠ .xmm12 := by simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with
      rfl | rfl | rfl | rfl <;> decide
    simp only [List.length_singleton, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at hin hX hT ⊢
    rw [show hashG [b] j = ([.kLoad .r10 .xmm12 (at_ .rax (64 * j))] : List Instr) ++ hash1 b j from rfl,
      WP.block_append_iff]
    refine WP.mono (ld512K_ok .xmm12 .rax (64 * j) t hc hk hbk hin) fun t₁ ⟨l₁, f₁⟩ => ?_
    refine WP.mono (hash1_ok hb j t₁ fun l hl => by rw [f₁.zlane _ (by decide) l hl, h0 l hl])
      fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, (f₁.comp f').mono (by decide)⟩
    rw [p' l hl]
    refine hashStep_eq hl _ _ _ _ (fun hj => ?_) ?_ ?_ ?_
    · rw [← hP hj l hl]
      simp only [prod, State.zproj_xmm, f₁.zlane .xmm8 (by decide) l hl, f₁.zlane .xmm9 (by decide) l hl,
        f₁.zlane .xmm10 (by decide) l hl]
    · rw [f₁.zlane _ (by decide) l hl, h2 l hl]
    · rw [hX l (by omega), f₁.zlane _ (fun h => hb12 (List.mem_singleton.mp h)) l hl,
        show l / 4 = 0 by omega, show l % 4 = l by omega]; rfl
    · rw [hT l (by omega), l₁ l hl, Offset.add_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega]
  | b :: b₂ :: bs, j, t, c, X, T, y, _, hrs, hlen, hc, hk, hbk, h0, h2, hin, hX, hT, hP => by
    have hb := hrs b List.mem_cons_self
    have hb12 : b ≠ .xmm12 := by simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with
      rfl | rfl | rfl | rfl <;> decide
    simp only [List.length_cons] at hin hX hT hlen ⊢
    have hn64 : 64 * (bs.length + 1 + 1 - 1) + 16 * c < 2 ^ 64 := by omega
    rw [show hashG (b :: b₂ :: bs) j = ([.vmovdqu32Load .xmm12 (at_ .rax (64 * j))] : List Instr) ++ hash1 b j ++
      hashG (b₂ :: bs) (j + 1) from rfl, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ld512_ok .xmm12 .rax (64 * j) t
      (by have := CallLay.inRegions_sub (off := 0) (l := 64) hin (by omega) hn64
          rwa [BitVec.add_zero] at this)) fun t₁ ⟨l₁, f₁⟩ => ?_
    refine WP.mono (hash1_ok hb j t₁ fun l hl => by rw [f₁.zlane _ (by decide) l hl, h0 l hl])
      fun t₂ ⟨p₂, f₂⟩ => ?_
    have f₁₂ := f₁.comp f₂
    have keep : ∀ r, r ∉ [XReg.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] → ∀ l < 4, t₂.zlane r l = t.zlane r l :=
      fun r hr l hl => f₁₂.zlane r (by simpa only [List.cons_append, List.nil_append] using hr) l hl
    have kreg : ∀ r ∈ b :: b₂ :: bs, ∀ l < 4, t₂.zlane r l = t.zlane r l := fun r hr l hl =>
      keep r (by
        have := hrs r hr
        simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl <;> decide) l hl
    have step : ∀ l < 4, prod (t₂.zproj l) = laneAccG X T y l (4 * (j + 1)) := fun l hl => by
      rw [p₂ l hl]
      refine hashStep_eq hl _ _ _ _ (fun hj => ?_) ?_ ?_ ?_
      · rw [← hP hj l hl]
        simp only [prod, State.zproj_xmm, f₁.zlane .xmm8 (by decide) l hl, f₁.zlane .xmm9 (by decide) l hl,
          f₁.zlane .xmm10 (by decide) l hl]
      · rw [f₁.zlane _ (by decide) l hl, h2 l hl]
      · rw [hX l (by omega), f₁.zlane _ (fun h => hb12 (List.mem_singleton.mp h)) l hl,
          show l / 4 = 0 by omega, show l % 4 = l by omega]; rfl
      · rw [hT l (by omega), ite_eq_left (by omega), l₁ l hl, Offset.add_add,
          show 64 * j + 16 * l = 16 * (4 * j + l) by omega]
    refine WP.mono (hashG_ok (b₂ :: bs) (j + 1) t₂ X T y (List.cons_ne_nil _ _)
      (fun r hr => hrs r (List.mem_cons_of_mem _ hr)) (by simp only [List.length_cons]; omega) hc
      (by rw [f₁₂.gpr]; exact hk) (by rw [f₁₂.gpr]; exact hbk)
      (fun l hl => by rw [keep _ (by decide) l hl, h0 l hl]) (fun l hl => by rw [keep _ (by decide) l hl, h2 l hl])
      (by
        rw [f₁₂.rd, f₁₂.wr, f₁₂.gpr]
        have := CallLay.inRegions_sub (off := 64) (l := 64 * ((b₂ :: bs).length - 1) + 16 * c) hin
          (by simp only [List.length_cons]; omega) hn64
        rwa [Offset.add_add, show 64 * j + 64 = 64 * (j + 1) by omega] at this)
      (fun n hn => by
        simp only [List.length_cons] at hn
        rw [show 4 * (j + 1) + n = 4 * j + (n + 4) by omega, hX (n + 4) (by omega),
          show (n + 4) / 4 = n / 4 + 1 by omega, show (n + 4) % 4 = n % 4 by omega, List.getD_cons_succ,
          kreg _ (by
            rw [← List.getElem_eq_getD (h := by simp only [List.length_cons]; omega)]
            exact List.mem_cons_of_mem _ (List.getElem_mem _)) _ (by omega)])
      (fun n hn => by
        simp only [List.length_cons] at hn ⊢
        rw [show 4 * (j + 1) + n = 4 * j + (n + 4) by omega, hT (n + 4) (by omega), f₁₂.mem, f₁₂.gpr]
        by_cases h : n < 4 * (bs.length + 1 - 1) + c
        · rw [ite_eq_left (by omega), ite_eq_left h]
        · rw [ite_eq_right (by omega), ite_eq_right h])
      (fun _ => step)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, ?_⟩
    · rw [p' l hl, show j + 1 + (b₂ :: bs).length = j + (bs.length + 1 + 1) by simp only [List.length_cons]; omega]
    · exact (f₁₂.comp f').mono (by decide)

end VG.Proof.Gcm.X86_64.StitchZH
