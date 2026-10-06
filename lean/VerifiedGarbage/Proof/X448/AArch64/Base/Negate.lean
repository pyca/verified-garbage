import VerifiedGarbage.Proof.X448.AArch64.Base.Select
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder

/-!
# X448 of the base point on AArch64: negating an entry for a negative digit

Untrusted: everything here is checked by Lean. `negate ox o w` computes
`0 - x` into slot `w`, loads the top bit of the digit's nibble (`n < 8` exactly
if it is clear) as a mask, and swaps `x` with `0 - x` under it, as Ed25519's
comb negates its cached entries.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs contains_sc read1_eq)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib nib_bits)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem bit_mask : ∀ b < 2,
    ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 =
      VG.Proof.X448.AArch64.mask (decide (b = 0)) := by
  decide

theorem nib_neg (k i : Nat) : decide (nib k i < 8) = decide ((k / 2 ^ (4 * i + 3)) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (k / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have h1 := Nat.mod_lt (k / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have h2 := Nat.mod_lt (k / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have h3 := Nat.mod_lt (k / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  apply decide_eq_decide.mpr
  omega

private theorem index3_fact : ∀ j < 57, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) {n k j i o : Nat} (hn : n ≤ 57)
    (hj : j < 57) (hi : i < 2 * n) (hoi : 8 * j + o = BITS + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hb : Bits n base k s.mem) :
    WP isa (.block [.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (o + 3),
      .subImm .x .x6 .x6 1]) s fun t =>
      t.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (nib k i < 8)) ∧ Keeps [.x6] s t ∧
        t.mem = s.mem := by
  have hr : InRegions (s.rd ++ s.wr) (off base (BITS + (4 * i + 3))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have he : base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (o + 3) = off base (BITS + (4 * i + 3)) := by
    simp only [off]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (base + ·) (congrArg (BitVec.ofNat 64) (by omega))
  have hv := bit_mask _ (Nat.mod_lt (k / 2 ^ (4 * i + 3)) (show 2 > 0 by decide))
  rw [← nib_neg, ← bit_eq, ← hb _ (by omega)] at hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, addr, Size.bits,
    show (3 : Nat) < 64 from by decide, show (1 : Nat) < 4096 from by decide,
    show o + 3 < 4096 * 1 by omega, Nat.mod_one, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hc, index3_fact j hj, hs.x3, he, hr, read1_eq, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X448.AArch64.ofs base (off base d) = d := by
  have := VG.Proof.X448.AArch64.ofs_off base (d := d) (i := 0) (by omega)
  simpa only [BitVec.add_zero, Nat.add_zero] using this

/-- The scalar's bits are outside the slots and the products' working space. -/
theorem Bits.of_fkeep {base : Addr} {n k : Nat} {s t : State} (hn : n ≤ 57) (hs : Scr s base)
    (h : Bits n base k s.mem) (hk : FKeep base s t) : Bits n base k t.mem := fun q hq => by
  have hn := hs.nowrap
  rw [hk.mem _ (by rw [ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
  exact h q hq

/-- `0 - x` into slot 10. -/
theorem subNeg_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (ox : Index)
    (hox : ox ≠ 10) (hx : Bnd Mb s.mem base (slot ox.val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (VG.Impl.X448.AArch64.Fast.ops [.sub (slot (10 : Index).val) (slot (19 : Index).val) (slot ox.val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [10] s.mem t.mem ∧
      EV t.mem base = Function.update (EV s.mem base) 10 (EV s.mem base 19 - EV s.mem base ox) :=
  subOp hs hb h19 hx (by decide) (Ne.symm hox) fun _ k b sm e => WP.block_nil ⟨k, b, sm, e⟩

theorem negate_eq (ox : Index) (n : Nat) :
    negate (slot ox.val) n (slot (10 : Index).val) =
      VG.Impl.X448.AArch64.Fast.codeOf ([.sub (slot (10 : Index).val) (slot (19 : Index).val) (slot ox.val)] :
          List Impl.X448.AArch64.Fast.Op) ++
        (([.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (n + 3), .subImm .x .x6 .x6 1] : List Instr) ++
          VG.Impl.Curve448.AArch64.cswap (slot ox.val) (slot (10 : Index).val)) := by
  simp only [negate, List.append_assoc]; rfl

/-- **The negation** of the entry's `x` in slot `ox` for the digit `nib k i - 8`, if negative. -/
theorem negate_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {k j i o : Nat}
    (ox : Index) (hox : ox ≠ 10) {n : Nat} (hn : n ≤ 57) (hj : j < 57) (hi : i < 2 * n)
    (hoi : 8 * j + o = BITS + 4 * i) (ho : o + 3 < 4096) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : Bits n base k s.mem)
    (hx : Bnd Mb s.mem base (slot ox.val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (.block (negate (slot ox.val) o (slot (10 : Index).val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([10] ++ [ox, 10]) s.mem t.mem ∧
      EV t.mem base = opSwap ox 10 (decide (nib k i < 8))
        (Function.update (EV s.mem base) 10 (EV s.mem base 19 - EV s.mem base ox)) := by
  rw [negate_eq ox o, WP.block_append_iff]
  refine WP.mono (block_codeOf (subNeg_ok hs hb ox hox hx h19)) fun t1 ⟨k1, b1, s1, e1⟩ => ?_
  have hs1 := k1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok hs1 hn hj hi hoi ho (by rw [k1.regs.1 _ (by decide)]; exact hc)
    (Bits.of_fkeep hn hs hbits k1)) fun t2 ⟨m2, k2, mem2⟩ => ?_
  have f2 : FKeep base t1 t2 := ⟨k2.mono (by decide), fun x _ _ => by rw [mem2]⟩
  have hs2 := f2.scr hs1
  have b2 : BEnv t2.mem base := fun i => by
    have := b1 i; intro w hw; rw [show t2.mem = t1.mem from mem2]; exact this w hw
  refine WP.mono (VG.Proof.X448.AArch64.Fast.cswapE hs2 b2 ox 10 hox m2) fun t3 ⟨k3, b3, _, _, _, s3, e3⟩ =>
    ⟨k1.trans (f2.trans k3), b3, fun i hi w hw => ?_, ?_⟩
  · have hi' : i ∉ [(10 : Index)] := fun h => hi (List.mem_append_left _ h)
    have hi'' : i ∉ [ox, 10] := fun h => hi (List.mem_append_right _ h)
    rw [s3 i hi'' w hw, show limbs t2.mem base (slot i.val) w = limbs t1.mem base (slot i.val) w by
      rw [mem2], s1 i hi' w hw]
  · rw [e3, show EV t2.mem base = EV t1.mem base by rw [mem2], e1]

end VG.Proof.X448.AArch64.Base
