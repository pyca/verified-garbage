module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.R10
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The counters of a batch added to as bytes

`fastCtrs_ok`: when the low byte of the first counter, `b`, is at most 240,
`StitchZH.fastCtrs` leaves in the lanes of `zmm3`–`zmm6` the byte-reversed
counter blocks `ctrsZ` would (the first register's byte-reversed, and each
next one's `beFour` more, `paddd_beFour`), and the counters 16 on
(`paddd_sixteen`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (fastCtrs)
open VG.Proof.Gcm.X86_64 (revMask beFour paddd_beFour)
open VG.Proof.Gcm.X86_64.StitchZ (sixteen bcast_exec zlane_bcast)
open VG.Proof.Aes.X86_64.VaesZ (four paddd_four)
open VG.Spec.Gcm (Block inc32)

/-- The low byte of a counter block, `inc₃₂` applied `n` times. -/
theorem lo8_repeat (Y : Block) (n : Nat) :
    ((Nat.repeat inc32 n Y).extractLsb' 0 8).toNat = ((Y.extractLsb' 0 8).toNat + n) % 256 := by
  have one : (1 : BitVec 32).toNat = 1 := rfl
  have := Y.isLt
  induction n with
  | zero =>
    simp only [Nat.repeat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    omega
  | succ n ih =>
    rw [Nat.repeat]
    simp only [inc32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one,
      VG.Proof.Gcm.X86_64.toNat_append', BitVec.toNat_add, one] at ih ⊢
    omega

theorem paddd_sixteen (c : Block) : XBinOp.eval .paddd c sixteen = Nat.repeat inc32 16 c := by
  have r4 : ∀ x : Block, Nat.repeat inc32 4 x = inc32 (inc32 (inc32 (inc32 x))) := fun _ => rfl
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, VG.Proof.Gcm.repeat_add, VG.Proof.Gcm.repeat_add,
    VG.Proof.Gcm.repeat_add, r4, r4, r4, r4, ← paddd_four, ← paddd_four, ← paddd_four, ← paddd_four]
  apply ext_dword <;>
  rw [dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_paddd _ _ (by decide),
    dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_assoc] <;>
  exact congrArg (_ + ·) (by decide)

/-- `paddd_beFour` for the counter blocks `j + l + 4 k` of a batch whose
first block's low byte is at most 240. -/
theorem paddd_beFour_at (X : Block) {j l k : Nat} (hb : ((X.extractLsb' 0 8).toNat + j) % 256 ≤ 240)
    (hl : l < 4) (hk : k < 3) :
    XBinOp.eval .paddd (XBinOp.eval .pshufb (Nat.repeat inc32 (j + 4 * k + l) X) revMask) beFour =
      XBinOp.eval .pshufb (Nat.repeat inc32 (j + 4 * (k + 1) + l) X) revMask := by
  rw [paddd_beFour _ (by rw [lo8_repeat]; omega), ← VG.Proof.Gcm.repeat_add]
  exact congrArg (fun n => XBinOp.eval .pshufb (Nat.repeat inc32 n X) revMask) (by omega)

/-- One unmasked 512-bit operation. -/
theorem zbin_ok (op : ZBinOp) (d a b : XReg) (t : State) :
    WP isa (.block [.zop (.zbin op d a b)]) t fun t' =>
      (∀ l < 4, t'.zlane d l = op.sse.eval (t.zlane a l) (t.zlane b l)) ∧ ZFrame [d] t t' := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ⟨fun l hl => by simp only [zlane_zbin _ _ _ _ _ _ hl, ite_true],
    ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ?_⟩⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [zlane_zbin _ _ _ _ _ _ hl, hr, ite_false]

/-- A 16-byte broadcast to the four lanes. -/
theorem bcast_ok (d : XReg) (b : Reg) (o : Nat) (t : State)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr b + BitVec.ofNat 64 o) 16) :
    WP isa (.block [.vbroadcasti32x4 d (at_ b o)]) t fun t' =>
      (∀ l < 4, t'.zlane d l = t.mem.readW (t.gpr b + BitVec.ofNat 64 o) 128) ∧ ZFrame [d] t t' := by
  rw [WP.block_cons_iff]
  refine ⟨_, bcast_exec d b o t hin, WP.block_nil ⟨fun l hl => zlane_bcast _ _ _ hl,
    ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ?_⟩⟩⟩
  simp only [List.mem_singleton] at hr
  exact State.zlane_setZ_ne _ hr _ _ _ _ hl

/-- `StitchZH.fastCtrs`, as `ctrsZ` on `aregs`. -/
theorem fastCtrs_ok (s : State) (X : Block) (j : Nat)
    (hc : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (j + l) X)
    (hm : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (hb : ((X.extractLsb' 0 8).toNat + j) % 256 ≤ 240)
    (h4 : s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 896) 128 = beFour)
    (h16 : s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 912) 128 = sixteen)
    (hin4 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 896) 16)
    (hin16 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 912) 16) :
    WP isa (.block fastCtrs) s fun s' =>
      (∀ k (h : k < aregs.length), ∀ l < 4,
        s'.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + 4 * k + l) X) revMask) ∧
      (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 (j + 16 + l) X) ∧
      ZFrame (.xmm13 :: .xmm14 :: aregs) s s' := by
  let R : Nat → Nat → BitVec 128 := fun k l => XBinOp.eval .pshufb (Nat.repeat inc32 (j + 4 * k + l) X) revMask
  rw [show fastCtrs = [.vbroadcasti32x4 .xmm13 (at_ .r11 896)] ++ ([.zop (.zbin .vpshufb .xmm3 .xmm14 .xmm0)] ++
      ([.zop (.zbin .vpaddd .xmm4 .xmm3 .xmm13)] ++ ([.zop (.zbin .vpaddd .xmm5 .xmm4 .xmm13)] ++
      ([.zop (.zbin .vpaddd .xmm6 .xmm5 .xmm13)] ++ ([.vbroadcasti32x4 .xmm13 (at_ .r11 912)] ++
      ([.zop (.zbin .vpaddd .xmm14 .xmm14 .xmm13)] : List Instr)))))) from rfl]
  rw [WP.block_append_iff]; refine WP.mono (bcast_ok .xmm13 .r11 896 s hin4) fun s₁ ⟨v₁, f₁⟩ => ?_
  rw [WP.block_append_iff]; refine WP.mono (zbin_ok .vpshufb .xmm3 .xmm14 .xmm0 s₁) fun s₂ ⟨v₂, f₂⟩ => ?_
  rw [WP.block_append_iff]; refine WP.mono (zbin_ok .vpaddd .xmm4 .xmm3 .xmm13 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  rw [WP.block_append_iff]; refine WP.mono (zbin_ok .vpaddd .xmm5 .xmm4 .xmm13 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  rw [WP.block_append_iff]; refine WP.mono (zbin_ok .vpaddd .xmm6 .xmm5 .xmm13 s₄) fun s₅ ⟨v₅, f₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcast_ok .xmm13 .r11 912 s₅ (by
    rw [f₅.gpr, f₄.gpr, f₃.gpr, f₂.gpr, f₁.gpr, f₅.rd, f₄.rd, f₃.rd, f₂.rd, f₁.rd, f₅.wr, f₄.wr, f₃.wr, f₂.wr,
      f₁.wr]; exact hin16)) fun s₆ ⟨v₆, f₆⟩ => ?_
  refine WP.mono (zbin_ok .vpaddd .xmm14 .xmm14 .xmm13 s₆) fun s₇ ⟨v₇, f₇⟩ => ?_
  -- `zmm13` holds `beFour` until the second broadcast.
  have k2 : ∀ l < 4, s₂.zlane .xmm13 l = beFour := fun l hl => by
    rw [f₂.zlane _ (by decide) l hl, v₁ l hl, h4]
  have k3 : ∀ l < 4, s₃.zlane .xmm13 l = beFour := fun l hl => by
    rw [f₃.zlane _ (by decide) l hl, k2 l hl]
  have k4 : ∀ l < 4, s₄.zlane .xmm13 l = beFour := fun l hl => by
    rw [f₄.zlane _ (by decide) l hl, k3 l hl]
  have r0 : ∀ l < 4, s₂.zlane .xmm3 l = R 0 l := fun l hl => by
    rw [v₂ l hl, f₁.zlane _ (by decide) l hl, f₁.zlane _ (by decide) l hl, hc l hl, hm l hl]
    exact congrArg (fun n => XBinOp.eval .pshufb (Nat.repeat inc32 n X) revMask) (by omega)
  have r1 : ∀ l < 4, s₃.zlane .xmm4 l = R 1 l := fun l hl => by
    rw [v₃ l hl, r0 l hl, k2 l hl]; exact paddd_beFour_at X hb hl (k := 0) (by decide)
  have r2 : ∀ l < 4, s₄.zlane .xmm5 l = R 2 l := fun l hl => by
    rw [v₄ l hl, r1 l hl, k3 l hl]; exact paddd_beFour_at X hb hl (k := 1) (by decide)
  have r3 : ∀ l < 4, s₅.zlane .xmm6 l = R 3 l := fun l hl => by
    rw [v₅ l hl, r2 l hl, k4 l hl]; exact paddd_beFour_at X hb hl (k := 2) (by decide)
  have g₆ : s₆.gpr = s.gpr := by rw [f₆.gpr, f₅.gpr, f₄.gpr, f₃.gpr, f₂.gpr, f₁.gpr]
  have m₅ : s₅.mem = s.mem := by rw [f₅.mem, f₄.mem, f₃.mem, f₂.mem, f₁.mem]
  have g₅ : s₅.gpr = s.gpr := by rw [f₅.gpr, f₄.gpr, f₃.gpr, f₂.gpr, f₁.gpr]
  refine ⟨fun k hk l hl => ?_, fun l hl => ?_, ?_⟩
  · have hk4 : k < 4 := by simpa [aregs] using hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · show s₇.zlane .xmm3 l = R 0 l
      rw [f₇.zlane _ (by decide) l hl, f₆.zlane _ (by decide) l hl, f₅.zlane _ (by decide) l hl,
        f₄.zlane _ (by decide) l hl, f₃.zlane _ (by decide) l hl, r0 l hl]
    · show s₇.zlane .xmm4 l = R 1 l
      rw [f₇.zlane _ (by decide) l hl, f₆.zlane _ (by decide) l hl, f₅.zlane _ (by decide) l hl,
        f₄.zlane _ (by decide) l hl, r1 l hl]
    · show s₇.zlane .xmm5 l = R 2 l
      rw [f₇.zlane _ (by decide) l hl, f₆.zlane _ (by decide) l hl, f₅.zlane _ (by decide) l hl, r2 l hl]
    · show s₇.zlane .xmm6 l = R 3 l
      rw [f₇.zlane _ (by decide) l hl, f₆.zlane _ (by decide) l hl, r3 l hl]
  · rw [v₇ l hl, f₆.zlane _ (by decide) l hl, f₅.zlane _ (by decide) l hl, f₄.zlane _ (by decide) l hl,
      f₃.zlane _ (by decide) l hl, f₂.zlane _ (by decide) l hl, f₁.zlane _ (by decide) l hl, hc l hl,
      v₆ l hl, g₅, m₅, h16]
    show XBinOp.eval .paddd _ sixteen = _
    rw [paddd_sixteen, ← VG.Proof.Gcm.repeat_add]
    exact congrArg (fun n => Nat.repeat inc32 n X) (by omega)
  · refine ⟨by rw [f₇.gpr, g₆], by rw [f₇.mem, f₆.mem, m₅], by
      rw [f₇.rd, f₆.rd, f₅.rd, f₄.rd, f₃.rd, f₂.rd, f₁.rd], by
      rw [f₇.wr, f₆.wr, f₅.wr, f₄.wr, f₃.wr, f₂.wr, f₁.wr], fun r hr l hl => ?_⟩
    simp only [aregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h13, h14, h3, h4', h5, h6⟩ := hr
    rw [f₇.zlane _ (by simp [h14]) l hl, f₆.zlane _ (by simp [h13]) l hl, f₅.zlane _ (by simp [h6]) l hl,
      f₄.zlane _ (by simp [h5]) l hl, f₃.zlane _ (by simp [h4']) l hl, f₂.zlane _ (by simp [h3]) l hl,
      f₁.zlane _ (by simp [h13]) l hl]

/-- `add r10d, 0x10000000`. -/
theorem add10_ok (s : State) :
    WP isa (.block [.alu32 .add .r10 (.imm 0x10000000)]) s fun t =>
      t.gpr .r10 = ((s.gpr .r10).setWidth 32 + 0x10000000).setWidth 64 ∧
      t.cf = some (decide (2 ^ 32 ≤ ((s.gpr .r10).setWidth 32).toNat + 2 ^ 28)) ∧
      (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ (∀ x l, t.zlane x l = s.zlane x l) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ HKeep s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  exact ⟨by simp only [RegUpd.gpr_setReg_self], rfl, fun r hr => by
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A shift into the top byte keeps the low byte. -/
theorem shl24_toNat (x : BitVec 32) : (x <<< 24).toNat = x.toNat % 256 * 2 ^ 24 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 32 = 256 * 2 ^ 24 from rfl, Nat.mul_mod_mul_right]
/-- The low byte of `i + n - 1`. -/
theorem idx_lo (i : BitVec 32) (n : Nat) : (i + BitVec.ofNat 32 n - 1).toNat % 256 = (i.toNat + n + 255) % 256 := by
  have one : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, one]
  have := i.isLt
  omega
/-- 16 more in the top byte of the index's word. -/
theorem idx_add (i : BitVec 32) (c : Nat) :
    ((((i + BitVec.ofNat 32 c - 1) <<< 24).setWidth 64).setWidth 32 + 0x10000000).setWidth 64 =
      ((i + BitVec.ofNat 32 (c + 16) - 1) <<< 24).setWidth 64 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  refine congrArg (BitVec.setWidth 64) (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_add, shl24_toNat, shl24_toNat, idx_lo, idx_lo,
    show (0x10000000 : BitVec 32).toNat = 16 * 2 ^ 24 from rfl]
  omega
/-- The low byte of a block is that of its low word. -/
theorem lo8_32 (Y : BitVec 128) : (Y.extractLsb' 0 8).toNat = (Y.extractLsb' 0 32).toNat % 256 := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  exact (Nat.mod_mod_of_dvd _ (by decide)).symm
/-- Without a carry out of the top byte, the low byte of the index of block `c` is at most 240. -/
theorem idx_nc (Y : BitVec 128) (c : Nat)
    (h : decide (2 ^ 32 ≤ ((((Y.extractLsb' 0 32 + BitVec.ofNat 32 c - 1) <<< 24).setWidth 64).setWidth 32).toNat + 2 ^ 28) = false) :
    ((Y.extractLsb' 0 8).toNat + c) % 256 ≤ 240 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, shl24_toNat, idx_lo] at h
  simp only [decide_eq_false_iff_not, Nat.not_le] at h
  rw [lo8_32]
  omega

open VG.Proof.Gcm.X86_64.StitchZ (R10 idxR BeConsts) in
open VG.Proof.Gcm.X86_64.Stitch (cb pp) in
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok) in
/-- The counter blocks of a batch from block `c` (`StitchZH.ctrs`): as
`ctrsZ`, through `fastCtrs` when the block index is public (`be`) and the low
bytes do not wrap; `r10` advanced to the next batch's (`R10`). -/
theorem ctrs_ok (be : Bool) {s₀ : State} {c : Nat} (s : State)
    (hc : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hm : ∀ l < 4, s.zlane .xmm0 l = revMask) (hi : ∀ l < 4, s.zlane .xmm15 l = four)
    (hR : R10 be s₀ c s) (hr11 : s.gpr .r11 = pp s₀)
    (hin : be = true → InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofNat 64 896) 16 ∧
      InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofNat 64 912) 16) :
    WP isa (Impl.Gcm.X86_64.StitchZH.ctrs be) s fun s' =>
      (∀ k (h : k < aregs.length), ∀ l < 4,
        s'.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) revMask) ∧
      (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 (c + 16 + l) (cb s₀)) ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      R10 be s₀ (c + 16) s' ∧ (be = false → s'.gpr = s.gpr) ∧ HKeep s s' := by
  have slow : ∀ t : State, (∀ l < 4, t.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)) →
      (∀ l < 4, t.zlane .xmm0 l = revMask) → (∀ l < 4, t.zlane .xmm15 l = four) →
      WP isa (.block (Impl.Aes.X86_64.VaesZ.ctrsZ .xmm14 .xmm0 .xmm15 aregs)) t fun t' =>
        (∀ k (h : k < aregs.length), ∀ l < 4,
          t'.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) revMask) ∧
        (∀ l < 4, t'.zlane .xmm14 l = Nat.repeat inc32 (c + 16 + l) (cb s₀)) ∧
        ZFrame (.xmm13 :: .xmm14 :: aregs) t t' ∧ HKeep t t' := fun t tc tm ti =>
    WP.mono (WP.hkeep (by decide) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs t (cb s₀) c
      (by decide) (by decide) tc tm ti)) fun t' ⟨⟨e, c', f⟩, hh⟩ =>
      ⟨e, fun l hl => by rw [c' l hl]; rfl, f.mono fun r hr => List.mem_cons_of_mem _ hr, hh⟩
  cases be
  · refine WP.mono (slow s hc hm hi) fun s' ⟨e, c', f, hh⟩ => ⟨e, c', fun x h13 h14 hx l hl =>
      f.zlane x (by simp [h13, h14, hx]) l hl, fun r _ => by rw [f.gpr], f.mem, f.rd, f.wr,
      by show _ = _; rw [f.gpr]; exact hR, fun _ => f.gpr, hh⟩
  · obtain ⟨h4in, h16in⟩ := hin rfl
    obtain ⟨hr10, hk⟩ : s.gpr .r10 = idxR s₀ c ∧ BeConsts (pp s₀) s.mem := hR
    refine WP.seq (WP.mono (add10_ok s) fun s₁ ⟨g10, cf₁, gk, zk, m₁, rd₁, wr₁, hk₁⟩ => ?_)
    have r10' : s₁.gpr .r10 = idxR s₀ (c + 16) := by rw [g10, hr10]; exact idx_add _ c
    have r11' : s₁.gpr .r11 = pp s₀ := by rw [gk _ (by decide), hr11]
    have done : ∀ s' : State, (∀ k (h : k < aregs.length), ∀ l < 4,
          s'.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) revMask) →
        (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 (c + 16 + l) (cb s₀)) →
        ZFrame (.xmm13 :: .xmm14 :: aregs) s₁ s' → HKeep s₁ s' →
        (∀ k (h : k < aregs.length), ∀ l < 4,
          s'.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) revMask) ∧
        (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 (c + 16 + l) (cb s₀)) ∧
        (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
        (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        R10 true s₀ (c + 16) s' ∧ (true = false → s'.gpr = s.gpr) ∧ HKeep s s' :=
      fun s' e c' f hh => ⟨e, c', fun x h13 h14 hx l hl => by
          rw [f.zlane x (by simp [h13, h14, hx]) l hl, zk], fun r hr => by rw [f.gpr, gk r hr],
        by rw [f.mem, m₁], by rw [f.rd, rd₁], by rw [f.wr, wr₁],
        ⟨by rw [f.gpr, r10'], by rw [f.mem, m₁]; exact hk⟩, fun h => absurd h (by decide), hk₁.trans hh⟩
    refine WP.ite (!decide (2 ^ 32 ≤ ((s.gpr .r10).setWidth 32).toNat + 2 ^ 28)) (by simp only [eval, cf₁, Option.map_some])
      (fun h => ?_) (fun _ => ?_)
    · rw [hr10] at h
      have h' : decide (2 ^ 32 ≤ ((idxR s₀ c).setWidth 32).toNat + 2 ^ 28) = false :=
        Bool.eq_false_iff.mpr fun e => by rw [e] at h; exact absurd h (by decide)
      have hb := idx_nc (cb s₀) c h'
      refine WP.mono (WP.hkeep (by decide) (fastCtrs_ok s₁ (cb s₀) c (fun l hl => by rw [zk]; exact hc l hl)
        (fun l hl => by rw [zk]; exact hm l hl) hb (by rw [r11', m₁]; exact hk.1) (by rw [r11', m₁]; exact hk.2)
        (by rw [r11', rd₁, wr₁]; exact h4in) (by rw [r11', rd₁, wr₁]; exact h16in)))
        fun s' ⟨⟨e, c', f⟩, hh⟩ => done s' e c' f hh
    · exact WP.mono (slow s₁ (fun l hl => by rw [zk]; exact hc l hl) (fun l hl => by rw [zk]; exact hm l hl)
        (fun l hl => by rw [zk]; exact hi l hl)) fun s' ⟨e, c', f, hh⟩ => done s' e c' f hh

open VG.Proof.Gcm.X86_64.Stitch (SPre nb pp bAddr pR) in
/-- The working space at `pp + o` is kept by the sixteen blocks of data written
from block `c`. -/
theorem keepAt {s₀ : State} (hp : SPre s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {o : Nat} (ho : o + 16 ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 o) 128 = m.readW (pp s₀ + BitVec.ofNat 64 o) 128 := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)

open VG.Proof.Gcm.X86_64.Stitch (SPre nb pp bAddr) in
open VG.Proof.Gcm.X86_64.StitchZ (R10 BeConsts) in
/-- `R10` is kept by the sixteen blocks of data written from block `c`, with
`r10` kept. -/
theorem R10.data {be : Bool} {s₀ : State} (hp : SPre s₀) {c c' : Nat} (hc : c + 16 ≤ nb s₀) {s s' : State}
    (h : R10 be s₀ c' s) (hg : s'.gpr .r10 = s.gpr .r10) (hf : Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem) :
    R10 be s₀ c' s' := by
  cases be
  · simp only [R10, Bool.false_eq_true, ↓reduceIte] at h ⊢; rw [hg]; exact h
  · simp only [R10, ↓reduceIte, BeConsts] at h ⊢
    exact ⟨by rw [hg]; exact h.1, by rw [keepAt hp hc hf (by decide)]; exact h.2.1,
      by rw [keepAt hp hc hf (by decide)]; exact h.2.2⟩

end VG.Proof.Gcm.X86_64.StitchZH
