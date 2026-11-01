module

import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeCheck
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Proof.Ed448.RISCV64.VSel
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X448.RISCV64.Slots

/-!
# Ed448's verification on RISCV64: the negated point

`decodeNeg xo yo` writes `-x'` to `xo` and `y` to `yo`, for `x'` the decoded
x-coordinate: `(x - x) - x` if the low bit of `x` (fully reduced at `OUT`) is
the sign, else `x` (`decodeNeg_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

theorem xor_le_one' {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The slots of `-x'` and `y`, above the field area and below `PK`, at multiples of 4. -/
def NegOut (xo yo : Nat) : Prop :=
  1064 ≤ xo ∧ xo + 56 ≤ PK ∧ 1064 ≤ yo ∧ yo + 56 ≤ PK ∧ (xo + 56 ≤ yo ∨ yo + 56 ≤ xo) ∧
    xo % 4 = 0 ∧ yo % 4 = 0

theorem decodeNeg_ok {s : State} (hc : VCtx b s) {xo yo : Nat} (ho : NegOut xo yo) {x y : Fe}
    (hx : FS s.mem b DXX = x) (hy : FS s.mem b DY = y)
    (hout : VG.Spec.X448.bytesAt s.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val)
    {sg : Nat} (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa (.block (decodeNeg xo yo)) s fun t => VCtx b t ∧ Rest R64.clob64 s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩] s.mem t.mem ∧
      FS t.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x ∧ FS t.mem b yo = y ∧
      FS t.mem b DK = FS s.mem b DK := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain ⟨hx1, hx2, hy1, hy2, hxy, hx4, hy4⟩ := ho
  have hPK : PK = 1456 := rfl
  have hDY : DY = 168 := rfl
  have hA := ACC_eq
  unfold decodeNeg
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS0 : SlotsOk s.mem b [DXX, DY, DK] (FS s.mem b) := fun _ _ => rfl
  refine WP.append (R64.subS (o := DTMP) (x := DXX) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc.ctx hS0) fun s1 ⟨hr1, hf1, hS1⟩ => ?_
  have hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (R64.subS (o := DNEG) (x := DTMP) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc1.ctx hS1) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  have hf12 : Frame [FA b] s.mem s2.mem := hf1.trans hf2
  -- The mask: the low bit of `x` against the sign.
  have hb2 : s2.mem (b + BitVec.ofNat 64 OUT) = BitVec.ofNat 8 x.val := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := OUT) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact byte0 hout
  have hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact hs
  refine wp_lbz (a := b + BitVec.ofNat 64 OUT) (by decide) (by rw [hc2.a0, BitVec.add_zero])
    (by rw [← BitVec.add_zero (b + BitVec.ofNat 64 OUT)]; exact (by rw [Offset.add_add]; exact hc2.inR (by omega_arith)))
    fun s3 u3 => wp_li (by decide) fun s4 u4 => wp_and fun s5 u5 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), hc2.ctx.a3])
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr]; exact hc2.inR (by omega_arith)) fun s6 u6 => wp_xor fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_sub fun s9 u9 => ?_
  have hm9 : s9.mem = s2.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  have hr9 : Rest [.a4, .a5, .a6, .t0] s2 s9 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest (by decide)).trans (u9.rest (by decide)))))))
  have hc9 : VCtx b s9 := hc2.of_rest hr9 (by decide) (by decide)
  have hsg' : sg < 2 ^ 64 := by omega_arith
  have hm : x.val % 2 ^^^ sg ≤ 1 := xor_le_one' (by omega_arith) hsg
  have e5 : (s5.gpr .a5).toNat = x.val % 2 := by
    rw [u5.gpr, BitVec.toNat_and, u4.other _ (by decide), u4.gpr, u3.gpr, hb2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega_arith
  have e6 : (s6.gpr .a4).toNat = sg := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, hs2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega_arith
  have e7 : s7.gpr .a5 = BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    apply BitVec.eq_of_toNat_eq
    rw [u7.gpr, BitVec.toNat_xor, u6.other _ (by decide), e5, e6, toNat_imm (by omega_arith)]
  have e11 : s9.gpr .t0 = 0 - BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), e7]; rfl
  -- The selections.
  refine WP.append (sel_ok (b := b) (o := xo) (q := DNEG) (r := DXX) (by omega_arith) (by decide) (by decide)
    (by unfold DNEG; omega_arith) (by unfold DXX; omega_arith) hx4 (by decide) (by decide) hc9.ctx hm e11) fun s10 h10 => ?_
  have hc10 : VCtx b s10 := hc9.of_rest h10.rest (by decide) (by decide)
  refine WP.mono (sel_ok (b := b) (o := yo) (q := DY) (r := DY) (by omega_arith) (by decide) (by decide)
    (by unfold DY; omega_arith) (by unfold DY; omega_arith) hy4 (by decide) (by decide) hc10.ctx hm (by rw [h10.rest.gpr _ (by decide), e11]))
    fun t ht => ?_
  have hrt : Rest R64.clob64 s t :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr9.mono (by decide)).trans
      ((h10.rest.mono (by decide)).trans (ht.rest.mono (by decide)))))
  -- The values.
  have v2 : ∀ q ∈ [DNEG, DXX, DY, DK], FS s2.mem b q = upd (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX))
      DNEG (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DTMP -
        upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DXX) q := fun q hq => hS2 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> decide)
  have hx' : FS s.mem b 672 = x := hx
  have hy' : FS s.mem b 168 = y := hy
  have eN : FS s2.mem b DNEG = (x - x) - x := by
    rw [v2 DNEG (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  have eX : FS s2.mem b DXX = x := by
    rw [v2 DXX (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  have eY : FS s2.mem b DY = y := by
    rw [v2 DY (by simp)]; simp only [upd, DNEG, DTMP, DY, Nat.reduceEqDiff, ↓reduceIte, hy']
  have hxo : FS s10.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x := by
    rw [fs_pick hm h10.lo, hm9, eN, eX]
  have eK : FS s2.mem b DK = FS s.mem b DK := by
    rw [v2 DK (by simp)]; simp only [upd, DNEG, DTMP, DK, Nat.reduceEqDiff, ↓reduceIte]
  refine ⟨hc.of_rest hrt (by decide) (by decide), hrt, ?_, ?_, ?_, ?_⟩
  · refine (hf12.mono (by simp)).trans ?_
    rw [← hm9]
    exact (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  · -- `xo` is kept by the write of `yo`.
    rw [← hxo]
    have e := limb_frame (o := xo) ht.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := xo + 4 * k) (n := 4) (e := yo) (k := 4 * 14) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- `y`, kept by the write of `xo`.
    rw [fs_pick hm ht.lo]
    have e := limb_frame (o := DY) h10.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by unfold DY; omega_arith) (by omega_arith) (by omega_arith)
    rw [show FS s10.mem b DY = FS s9.mem b DY by rw [FS, V, val32_congr e]; rfl, hm9, eY]
    unfold pick VG.Proof.X25519.sel; split <;> rfl

  · -- `d`, kept by both writes.
    rw [← eK, ← hm9]
    have f : Frame [⟨b + BitVec.ofNat 64 xo, 4 * 14⟩, ⟨b + BitVec.ofNat 64 yo, 4 * 14⟩] s9.mem t.mem :=
      (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
    have e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl

end

end VG.Proof.Ed448.RISCV64
