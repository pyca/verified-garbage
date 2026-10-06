import VerifiedGarbage.Proof.Rsa.AArch64.PrivPub
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-!
# `vg_rsa_private_checked` on AArch64: the check and the release

After the calls, `out` (which `vg_rsa_public_precomputed_checked` wrote) is
compared with the input without branches (`cmpLoop_ok`), and `M` is
released to `out` under the mask of `r₁ = r₂ = r₃ = 1` and their equality,
and zeroed (`releaseLoop_ok`), whatever `M` and `out` hold (`tail_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- `t` differs from `t₀` only in the registers `rs` (and the flags and
memory, which this does not say). -/
structure Keep (rs : List Reg) (t₀ t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  sp : t.sp = t₀.sp
  v : t.v = t₀.v

theorem Keep.refl (rs : List Reg) (t : State) : Keep rs t t := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {a b c : State} (h₁ : Keep rs a b) (h₂ : Keep rs b c) : Keep rs a c :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₂.v.trans h₁.v⟩

/-- The scratch registers the tail uses. -/
abbrev tailRegs : List Reg := [.x0, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- `Ctx` survives code that changes only the tail's registers and the
inner frame. -/
theorem Ctx.keep {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
    (hc : Ctx L g vv m₀ t) (hk : Keep tailRegs t t') (hm : t'.mem = t.mem) : Ctx L g vv m₀ t' :=
  hc.regs hk.rd hk.wr hk.sp hm hk.v fun r hr _ => hk.gpr r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- A loop counting `r` down from `N > 0` to zero, one an iteration. -/
theorem wp_down {body : Prog isa} {r : Reg} {N : Nat} (hN : 0 < N) (hN64 : N < 2 ^ 64)
    (Inv : Nat → State → Prop) {Q : State → Prop}
    (hbody : ∀ j, j < N → ∀ s, Inv j s →
      WP isa body s fun s' => s'.gpr r = BitVec.ofNat 64 (N - (j + 1)) ∧ Inv (j + 1) s')
    (hQ : ∀ s, Inv N s → Q s) {s : State} (h0 : Inv 0 s) :
    WP isa (.loop body (.nonzero .x r)) s Q := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = N - j ∧ j < N ∧ Inv j s) ?_ N s ⟨0, rfl, hN, h0⟩
  rintro n s ⟨j, rfl, hj, hI⟩
  refine WP.mono (hbody j hj s hI) fun s' ⟨hr, hI'⟩ => ?_
  have hev : isa.eval (.nonzero .x r) s' = some (decide (j + 1 ≠ N)) := by
    show eval (.nonzero .x r) s' = _
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hr, Option.some.injEq]
    by_cases he : j + 1 = N
    · rw [he, Nat.sub_self]; simp
    · have h0 : BitVec.ofNat 64 (N - (j + 1)) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      simp only [he, bne_iff_ne, ne_eq, not_false_eq_true, decide_true]; exact h0
  by_cases he : j + 1 = N
  · refine .inl ⟨?_, hQ s' (he ▸ hI')⟩
    rw [hev]; simp [he]
  · refine .inr ⟨?_, N - (j + 1), by omega, j + 1, rfl, by omega, hI'⟩
    rw [hev]; simp [he]

/-! ## The comparison -/

/-- A byte loaded by `ldrb`, as a 64-bit register. -/
theorem zext_read1 (m : Mem) (a : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = BitVec.setWidth 64 (m a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat]
  have := (m a).isLt
  simp
  omega

theorem ofNat_sub_one {k j : Nat} (hj : j < k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k - j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k - (j + 1) < 2 ^ 64)]
  simp only [Nat.reducePow, Nat.one_mod]
  omega

theorem ofNat_add_one' (p : Addr) (j : Nat) : p + BitVec.ofNat 64 j + 1#64 = p + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

/-- After `j` bytes of the comparison of the `k` bytes at `op` and `ip`. -/
structure CmpInv (t₀ : State) (op ip : Addr) (k j : Nat) (t : State) : Prop where
  keep : Keep [.x8, .x10, .x11, .x12, .x13, .x14] t₀ t
  mem : t.mem = t₀.mem
  x11 : t.gpr .x11 = op + BitVec.ofNat 64 j
  x12 : t.gpr .x12 = ip + BitVec.ofNat 64 j
  x13 : t.gpr .x13 = BitVec.ofNat 64 (k - j)
  x14 : t.gpr .x14 = 0 ↔ ∀ i < j, t₀.mem (op + BitVec.ofNat 64 i) = t₀.mem (ip + BitVec.ofNat 64 i)

theorem cmp_step {t₀ t : State} {op ip : Addr} {k j : Nat} (hj : j < k) (hk : k < 2 ^ 63)
    (ho : InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 j) 1)
    (hi : InRegions (t.rd ++ t.wr) (ip + BitVec.ofNat 64 j) 1) (hI : CmpInv t₀ op ip k j t) :
    WP isa (.block [.ldrb .x8 .x11 0, .ldrb .x10 .x12 0, .logic .eor .x .x8 .x8 .x10,
      .logic .orr .x .x14 .x14 .x8, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1,
      .subImm .x .x13 .x13 1]) t fun t' =>
      t'.gpr .x13 = BitVec.ofNat 64 (k - (j + 1)) ∧ CmpInv t₀ op ip k (j + 1) t' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hI.x11, hI.x12,
    hI.x13, BitVec.add_zero, ho, hi, Option.some.injEq, exists_eq_left', Nat.zero_mod, and_self,
    show (0 : Nat) < 4096 * 1 by decide, show (1 : Nat) < 4096 by decide]
  rw [zext_read1, zext_read1]
  refine ⟨ofNat_sub_one hj (by omega), ⟨⟨fun r hr => ?_, hI.keep.rd, hI.keep.wr, hI.keep.sp, hI.keep.v⟩,
    hI.mem, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h10, h11, h12, h13, h14⟩ := hr
    simp only [RegUpd.gpr_write, h8, h10, h11, h12, h13, h14, ite_false]
    exact hI.keep.gpr r (by simp [h8, h10, h11, h12, h13, h14])
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact ofNat_add_one' _ _
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact ofNat_add_one' _ _
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact ofNat_sub_one hj (by omega)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl,
      zext_xor_eq_zero, hI.x14, hI.mem]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h j (by omega)⟩

/-- The comparison of the `k` bytes at `op` and `ip`: `x14` is zero exactly
when they are equal. -/
theorem cmpLoop_ok {t : State} {op ip : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 63)
    (h11 : t.gpr .x11 = op) (h12 : t.gpr .x12 = ip) (h13 : t.gpr .x13 = BitVec.ofNat 64 k)
    (h14 : t.gpr .x14 = 0)
    (ho : ∀ i < k, InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 i) 1)
    (hi : ∀ i < k, InRegions (t.rd ++ t.wr) (ip + BitVec.ofNat 64 i) 1) :
    WP isa cmpLoop t (CmpInv t op ip k k) := by
  refine wp_down (r := .x13) hk1 (by omega) (CmpInv t op ip k) (fun j hj u hI => ?_) (fun _ h => h)
    ⟨Keep.refl _ _, rfl, by rw [h11, BitVec.add_zero], by rw [h12, BitVec.add_zero], by rw [h13, Nat.sub_zero],
      ⟨fun _ _ h => absurd h (by omega), fun _ => h14⟩⟩
  have hrw : u.rd ++ u.wr = t.rd ++ t.wr := by rw [hI.keep.rd, hI.keep.wr]
  exact cmp_step hj hk (hrw ▸ ho j hj) (hrw ▸ hi j hj) hI

/-! ## The masks -/

theorem holds_eq_addWithCarry (s : State) (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    CondCode.holds (s.addWithCarry sz d a b c) .eq = decide (a + b + BitVec.ofNat sz.bits c.toNat = 0) := rfl

theorem setWidth16_0 : BitVec.setWidth 64 (0#16) = 0#64 := rfl
theorem setWidth16_1 : BitVec.setWidth 64 (1#16) = 1#64 := rfl
theorem setWidth16_2 : BitVec.setWidth 64 (2#16) = 2#64 := rfl

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

theorem masks_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) {gv : BitVec 64}
    {eq : Bool} (h9 : t.gpr .x9 = gv) (hg : gv = 0 ∨ gv = 1) (h14 : t.gpr .x14 = 0 ↔ eq = true) :
    WP isa (.block masks) t fun t' => t'.mem = t.mem ∧ Keep tailRegs t t' ∧
      t'.gpr .x13 = Proof.Rsa.result gv eq ∧ t'.gpr .x12 = Proof.Rsa.relMask gv eq ∧
      t'.gpr .x10 = 0 ∧ t'.gpr .x11 = L.out ∧ t'.gpr .x14 = L.B + BitVec.ofNat 64 oM ∧ t'.gpr .x15 = L.k := by
  have lO := hc.inFr hL (d := oOut) (n := 8) (by decide)
  have lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  apply WP.of_runBlock
  simp only [masks, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.gpr_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry,
    RegUpd.sp_addWithCarry, RegUpd.sp_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, lO, lK, read8,
    hs.out, hs.k, h9, Option.some.injEq, exists_eq_left', show oOut % 8 = 0 by decide,
    show oOut < 32768 by decide, show oK % 8 = 0 by decide, show oK < 32768 by decide,
    show oM < 4096 by decide, and_self, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    holds_eq_addWithCarry, setWidth16_0, setWidth16_1, setWidth16_2, BitVec.add_zero, Bool.toNat_false,
    BitVec.ofNat_eq_ofNat]
  have hd : (t.gpr .x14 = 0#64) ↔ eq = true := h14
  simp only [hd, Bool.decide_eq_true]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, trivial⟩
  · simp only [tailRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨-, h8, -, h10, h11, h12, h13, h14, h15⟩ := hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, h8, h10, h11, h12, h13, h14, h15, ite_false]
  all_goals rcases hg with rfl | rfl <;> cases eq <;> decide

end

end VG.Proof.Rsa.AArch64
