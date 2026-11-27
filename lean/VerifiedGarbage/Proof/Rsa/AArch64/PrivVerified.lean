module

import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Rsa.PrivCheck
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Rsa.AArch64.PrivCT`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.PrivCorrect`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.PrivCheckOk`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.PrivRelease`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.PrivTail`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: the check and the release

After the calls, `out` (which `vg_rsa_public_precomputed_checked` wrote) is
compared with the input without branches (`cmpLoop_ok`), and `M` is
released to `out` under the mask of `r₁ = r₂ = r₃ = 1` and their equality,
and zeroed (`releaseLoop_ok`), whatever `M` and `out` hold (`tail_ok`).
-/

@[expose] public section

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
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        simp at this; omega_arith
      simp only [he, bne_iff_ne, ne_eq, not_false_eq_true, decide_true]; exact h0
  by_cases he : j + 1 = N
  · refine .inl ⟨?_, hQ s' (he ▸ hI')⟩
    rw [hev]; simp [he]
  · refine .inr ⟨?_, N - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI'⟩
    rw [hev]; simp [he]

/-! ## The comparison -/

/-- A byte loaded by `ldrb`, as a 64-bit register. -/
theorem zext_read1 (m : Mem) (a : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = BitVec.setWidth 64 (m a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat]
  have := (m a).isLt
  simp
  omega_arith

theorem ofNat_sub_one {k j : Nat} (hj : j < k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith : k - j < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith : k - (j + 1) < 2 ^ 64)]
  simp only [Nat.reducePow, Nat.one_mod]
  omega_arith

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
  refine ⟨ofNat_sub_one hj (by omega_arith), ⟨⟨fun r hr => ?_, hI.keep.rd, hI.keep.wr, hI.keep.sp, hI.keep.v⟩,
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
    exact ofNat_sub_one hj (by omega_arith)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl,
      zext_xor_eq_zero, hI.x14, hI.mem]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega_arith), h j (by omega_arith)⟩

/-- The comparison of the `k` bytes at `op` and `ip`: `x14` is zero exactly
when they are equal. -/
theorem cmpLoop_ok {t : State} {op ip : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 63)
    (h11 : t.gpr .x11 = op) (h12 : t.gpr .x12 = ip) (h13 : t.gpr .x13 = BitVec.ofNat 64 k)
    (h14 : t.gpr .x14 = 0)
    (ho : ∀ i < k, InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 i) 1)
    (hi : ∀ i < k, InRegions (t.rd ++ t.wr) (ip + BitVec.ofNat 64 i) 1) :
    WP isa cmpLoop t (CmpInv t op ip k k) := by
  refine wp_down (r := .x13) hk1 (by omega_arith) (CmpInv t op ip k) (fun j hj u hI => ?_) (fun _ h => h)
    ⟨Keep.refl _ _, rfl, by rw [h11, BitVec.add_zero], by rw [h12, BitVec.add_zero], by rw [h13, Nat.sub_zero],
      ⟨fun _ _ h => absurd h (by omega_arith), fun _ => h14⟩⟩
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

/-! ## The release -/

theorem write1_apply (m : Mem) (a x : Addr) (b : BitVec (8 * 1)) :
    m.write a 1 b x = if x = a then b else m x := by
  simp only [Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 1 := by
      intro h'
      apply h
      have : (x - a).toNat = 0 := by omega_arith
      have : x - a = 0 := BitVec.eq_of_toNat_eq (by simpa using this)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ite_false]

theorem ite_neg' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬p) : (if p then a else b) = b := by
  simp [h]

theorem ite_pos' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

theorem low8 (x : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_mod_of_dvd _ (by decide)

/-- After `j` bytes of the release of the `k` bytes at `Mb` to `op`, under
the mask `relMask gv eq` in `x12`. -/
structure RelInv (t₀ : State) (op Mb : Addr) (gv : BitVec 64) (eq : Bool) (k j : Nat) (t : State) : Prop where
  keep : Keep [.x8, .x11, .x14, .x15] t₀ t
  x11 : t.gpr .x11 = op + BitVec.ofNat 64 j
  x14 : t.gpr .x14 = Mb + BitVec.ofNat 64 j
  x15 : t.gpr .x15 = BitVec.ofNat 64 (k - j)
  out : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if gv = 1 ∧ eq = true then t₀.mem (Mb + BitVec.ofNat 64 i) else 0
  m : ∀ i < j, t.mem (Mb + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → (∀ i < j, x ≠ Mb + BitVec.ofNat 64 i) → t.mem x = t₀.mem x

theorem rel_step {t₀ t : State} {op Mb : Addr} {gv : BitVec 64} {eq : Bool} {k j : Nat} (hj : j < k)
    (hk : k < 2 ^ 63) (h10 : t₀.gpr .x10 = 0) (h12 : t₀.gpr .x12 = Proof.Rsa.relMask gv eq)
    (hsep : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i ≠ Mb + BitVec.ofNat 64 i')
    (hinj : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i = op + BitVec.ofNat 64 i' → i = i')
    (hinjM : ∀ i < k, ∀ i' < k, Mb + BitVec.ofNat 64 i = Mb + BitVec.ofNat 64 i' → i = i')
    (ho : InRegions t.wr (op + BitVec.ofNat 64 j) 1) (hm : InRegions t.wr (Mb + BitVec.ofNat 64 j) 1)
    (hI : RelInv t₀ op Mb gv eq k j t) :
    WP isa (.block [.ldrb .x8 .x14 0, .logic .and .x .x8 .x8 .x12, .strb .x8 .x11 0, .strb .x10 .x14 0,
      .addImm .x .x11 .x11 1, .addImm .x .x14 .x14 1, .subImm .x .x15 .x15 1]) t fun t' =>
      t'.gpr .x15 = BitVec.ofNat 64 (k - (j + 1)) ∧ RelInv t₀ op Mb gv eq k (j + 1) t' := by
  have hmr : InRegions (t.rd ++ t.wr) (Mb + BitVec.ofNat 64 j) 1 := by
    obtain ⟨r, hr, hc⟩ := hm; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have h12' : t.gpr .x12 = Proof.Rsa.relMask gv eq := (hI.keep.gpr _ (by decide)).trans h12
  have h10' : t.gpr .x10 = 0 := (hI.keep.gpr _ (by decide)).trans h10
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hI.x11, hI.x14, hI.x15, h12', h10',
    BitVec.add_zero, ho, hm, hmr, Option.some.injEq, exists_eq_left', Nat.zero_mod, and_self,
    show (0 : Nat) < 4096 * 1 by decide, show (1 : Nat) < 4096 by decide]
  rw [zext_read1]
  refine ⟨ofNat_sub_one hj (by omega_arith), ⟨⟨fun r hr => ?_, hI.keep.rd, hI.keep.wr, hI.keep.sp, hI.keep.v⟩,
    ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun x hx hx' => ?_⟩⟩
  all_goals simp only [RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_false, ite_true,
    BitVec.setWidth_eq, write1_apply]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h11, h14, h15⟩ := hr
    simp only [h8, h11, h14, h15, ite_false]
    exact hI.keep.gpr r (by simp [h8, h11, h14, h15])
  · exact ofNat_add_one' _ _
  · exact ofNat_add_one' _ _
  · exact ofNat_sub_one hj (by omega_arith)
  · rw [ite_neg' (hsep i (by omega_arith) j hj)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_neg' fun h => absurd (hinj i (by omega_arith) j hj h) (by omega_arith)]
      exact hI.out i hi
    · rw [ite_pos' rfl, hI.frame _ (fun i' hi' h => hsep i' (by omega_arith) i hj h.symm)
        (fun i' hi' h => absurd (hinjM i hj i' (by omega_arith) h) (by omega_arith)), low8,
        Proof.Rsa.low_and_mask]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_neg' fun h => absurd (hinjM i (by omega_arith) j hj h) (by omega_arith),
        ite_neg' fun h => hsep j hj i (by omega_arith) h.symm]
      exact hI.m i hi
    · rw [ite_pos' rfl]; rfl
  · rw [ite_neg' (hx' j (by omega_arith)), ite_neg' (hx j (by omega_arith))]
    exact hI.frame x (fun i hi => hx i (by omega_arith)) fun i hi => hx' i (by omega_arith)

/-- The release of the `k` bytes at `Mb` to `op`. -/
theorem releaseLoop_ok {t : State} {op Mb : Addr} {gv : BitVec 64} {eq : Bool} {k : Nat} (hk1 : 1 ≤ k)
    (hk : k < 2 ^ 63) (h10 : t.gpr .x10 = 0) (h12 : t.gpr .x12 = Proof.Rsa.relMask gv eq)
    (h11 : t.gpr .x11 = op) (h14 : t.gpr .x14 = Mb) (h15 : t.gpr .x15 = BitVec.ofNat 64 k)
    (hsep : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i ≠ Mb + BitVec.ofNat 64 i')
    (hinj : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i = op + BitVec.ofNat 64 i' → i = i')
    (hinjM : ∀ i < k, ∀ i' < k, Mb + BitVec.ofNat 64 i = Mb + BitVec.ofNat 64 i' → i = i')
    (ho : ∀ i < k, InRegions t.wr (op + BitVec.ofNat 64 i) 1)
    (hm : ∀ i < k, InRegions t.wr (Mb + BitVec.ofNat 64 i) 1) :
    WP isa releaseLoop t (RelInv t op Mb gv eq k k) := by
  refine wp_down (r := .x15) hk1 (by omega_arith) (RelInv t op Mb gv eq k) (fun j hj u hI => ?_) (fun _ h => h)
    ⟨Keep.refl _ _, by rw [h11, BitVec.add_zero], by rw [h14, BitVec.add_zero], by rw [h15, Nat.sub_zero],
      fun _ h => absurd h (by omega_arith), fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl⟩
  have hw : u.wr = t.wr := hI.keep.wr
  exact rel_step hj hk h10 h12 hsep hinj hinjM (hw ▸ ho j hj) (hw ▸ hm j hj) hI

/-- Distinct offsets below `k ≤ 2 ^ 64` of an address are distinct addresses. -/
theorem add_ofNat_inj (p : Addr) {k : Nat} (hk : k ≤ 2 ^ 64) :
    ∀ i < k, ∀ i' < k, p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 i' → i = i' := by
  intro i hi i' hi' h
  have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp h)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at this
  exact this

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: the tail

`tail_ok` runs the check and the release from the frames, after the calls:
whatever `M` and `out` hold and the calls returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem Keep.mono {rs rs' : List Reg} {a b : State} (h : Keep rs a b) (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' a b := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp, h.v⟩

theorem bytesAt_ext {m m' : Mem} {p q : Addr} {k : Nat} {c : Prop} [Decidable c]
    (h : ∀ i < k, m' (p + BitVec.ofNat 64 i) = if c then m (q + BitVec.ofNat 64 i) else 0) :
    Spec.Rsa.bytesAt m' p k = if c then Spec.Rsa.bytesAt m q k else List.replicate k 0 := by
  split
  · rename_i hc
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi), ite_pos' hc]
  · rename_i hc
    simp only [Spec.Rsa.bytesAt, List.eq_replicate_iff, List.length_map, List.length_range, List.mem_map,
      List.mem_range, true_and]
    rintro _ ⟨i, hi, rfl⟩
    rw [h i hi, ite_neg' hc]

theorem contains_of_lt (p : Addr) {k i : Nat} (hk : k ≤ 2 ^ 64) (hi : i < k) :
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
  Offset.contains_base _ (by omega_using [hi]) (by omega_using [hk, hi])

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- `Ctx` survives code that changes only the tail's registers, `out` and
`M`. -/
theorem Ctx.outM (hL : L.Ok) {t t' : State} (hc : Ctx L g vv m₀ t) (hk : Keep tailRegs t t')
    (hf : Frame [L.OUT, L.M] t.mem t'.mem) : Ctx L g vv m₀ t' := by
  have hnB := hL.nB
  have hk' := hL.khi
  refine ⟨hk.rd.trans hc.rd, hk.wr.trans hc.wr, hk.sp.trans hc.sp, fun r hr hr' => (hk.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans
      (hc.cs r hr hr'), fun r hr => by rw [hk.v]; exact hc.vs r hr, ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    rw [hf.readW hlr (fun R hR => ?_) (by decide)]
    · exact hc.lr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact (hL.ko.sub_left (Offset.sub_base _ (by decide))).symm.symm
      · exact Offset.disjoint L.B (d := frameBytes) (n := 16) (e := oM) (k := L.k.toNat) (by
          simp only [frameBytes, oM]; omega_using [hk']) (by simp only [frameBytes]; omega_using []) (by simp only [oM]; omega_using [hk'])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, fun _ h => h⟩
    · exact ⟨L.STK, by simp, hL.M_sub⟩

/-- The comparison's registers. -/
theorem cmpArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) {r1 r3 : BitVec 64}
    (h1 : t.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = r1) (h3 : t.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = r3) :
    WP isa (.block cmpArgs) t fun t' => t'.mem = t.mem ∧ Keep tailRegs t t' ∧
      t'.gpr .x9 = Proof.Rsa.gOf (t.gpr .x0) r1 r3 ∧ t'.gpr .x11 = L.out ∧ t'.gpr .x12 = L.inp ∧
      t'.gpr .x13 = L.k ∧ t'.gpr .x14 = 0 := by
  have l1 := hc.inFr hL (d := oR1) (n := 8) (by decide)
  have l3 := hc.inFr hL (d := oR3) (n := 8) (by decide)
  have lO := hc.inFr hL (d := oOut) (n := 8) (by decide)
  have lI := hc.inFr hL (d := oIn) (n := 8) (by decide)
  have lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  apply WP.of_runBlock
  simp only [cmpArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.sp_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, l1, l3, lO, lI, lK, read8,
    h1, h3, hs.out, hs.inp, hs.k, Option.some.injEq, exists_eq_left', show oR1 % 8 = 0 by decide,
    show oR1 < 32768 by decide, show oR3 % 8 = 0 by decide, show oR3 < 32768 by decide,
    show oOut % 8 = 0 by decide, show oOut < 32768 by decide, show oIn % 8 = 0 by decide,
    show oIn < 32768 by decide, show oK % 8 = 0 by decide, show oK < 32768 by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl, trivial, trivial, trivial, rfl⟩
  simp only [tailRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨-, -, h9, h10, h11, h12, h13, h14, -⟩ := hr
  simp only [RegUpd.gpr_write, h9, h10, h11, h12, h13, h14, ite_false]

theorem tail_eq : seqs tail = .seq (.block cmpArgs) (.seq cmpLoop (.seq (.block masks)
    (.seq releaseLoop (.block [.addImm .x .x0 .x13 0])))) := rfl

/-- The check and the release, after the calls, from `t`: whatever `M`,
`out` and the values returned hold. -/
theorem tail_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) {r1 r3 : BitVec 64}
    (h1 : t.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = r1) (h3 : t.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = r3) :
    WP isa (seqs tail) t fun t' => Ctx L g vv m₀ t' ∧
      t'.gpr .x0 = Proof.Rsa.result (Proof.Rsa.gOf (t.gpr .x0) r1 r3)
        (decide (Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat)) ∧
      Spec.Rsa.bytesAt t'.mem L.out L.k.toNat =
        (if Proof.Rsa.gOf (t.gpr .x0) r1 r3 = 1 ∧
            Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat then
          Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat
        else List.replicate L.k.toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat = List.replicate L.k.toNat 0 := by
  have hnB := hL.nB
  have hkk := hL.khi
  have hk1 : 1 ≤ L.k.toNat := by have := hL.klo; omega_using [this]
  have hk64 : L.k.toNat < 2 ^ 63 := by omega_using [hkk]
  have hok : L.out.toNat + L.k.toNat ≤ 2 ^ 64 := hL.olk ▸ hL.bo
  have hik : L.inp.toNat + L.k.toNat ≤ 2 ^ 64 := hL.ilk ▸ hL.bi
  have hOk : L.OUT = ⟨L.out, L.k.toNat⟩ := by rw [Lay.OUT, hL.olk]
  have hdisj : L.OUT.Disjoint L.M := (hL.ko.sub_left hL.M_sub).symm
  rw [tail_eq]
  refine WP.seq (WP.mono (cmpArgs_ok hL hc hs h1 h3) fun t₁ ⟨hm₁, k₁, x9, x11, x12, x13, x14⟩ => ?_)
  have hc₁ := hc.keep k₁ hm₁
  refine WP.seq (WP.mono (cmpLoop_ok (op := L.out) (ip := L.inp) hk1 hk64 x11 x12
    (by rw [x13, BitVec.ofNat_toNat, BitVec.setWidth_eq]) x14
    (fun i hi => ⟨L.OUT, by rw [hc₁.rd, hc₁.wr]; simp, hOk ▸ contains_of_lt _ (by omega_using []) hi⟩)
    (fun i hi => ⟨L.IN, by rw [hc₁.rd, hc₁.wr]; simp, by rw [Lay.IN, hL.ilk]; exact contains_of_lt _ (by omega_using []) hi⟩))
    fun t₂ hI => ?_)
  have hc₂ := hc₁.keep (Keep.trans ⟨fun r hr => (hI.keep.gpr r (by simp_all)), hI.keep.rd, hI.keep.wr,
    hI.keep.sp, hI.keep.v⟩ (Keep.refl _ _)) hI.mem
  have hs₂ : Slots L t₂.mem := by rw [hI.mem, hm₁]; exact hs
  have g9 : t₂.gpr .x9 = Proof.Rsa.gOf (t.gpr .x0) r1 r3 := (hI.keep.gpr _ (by decide)).trans x9
  have heq : t₂.gpr .x14 = 0 ↔
      decide (Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat) = true := by
    rw [hI.x14, decide_eq_true_eq, Proof.Rsa.bytesAt_eq_iff, hm₁]
  refine WP.seq (WP.mono (masks_ok hL hc₂ hs₂ g9 (Proof.Rsa.gOf_cases _ _ _) heq)
    fun t₃ ⟨hm₃, k₃, y13, y12, y10, y11, y14, y15⟩ => ?_)
  have hc₃ := hc₂.keep k₃ hm₃
  have hMk : ∀ i < L.k.toNat, InRegions t₃.wr (L.B + BitVec.ofNat 64 oM + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨L.FR, by rw [hc₃.wr]; simp, by
      rw [add_add]; exact Offset.contains_base _ (by simp only [oM, frameBytes]; omega_using [hkk, hi]) (by simp only [oM]; omega_using [hkk, hi])⟩
  refine WP.seq (WP.mono (releaseLoop_ok (op := L.out) (Mb := L.B + BitVec.ofNat 64 oM) hk1 hk64 y10 y12 y11 y14
    (by rw [y15, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun i hi i' hi' h => hdisj _ (by rw [hOk]; exact contains_of_lt _ (by omega_using []) hi)
      (by rw [h]; exact contains_of_lt _ (by omega_using []) hi'))
    (add_ofNat_inj _ (by omega_using [])) (add_ofNat_inj _ (by omega_using []))
    (fun i hi => ⟨L.OUT, by rw [hc₃.wr]; simp, hOk ▸ contains_of_lt _ (by omega_using []) hi⟩) hMk)
    fun t₄ hR => ?_)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    show (0 : Nat) < 4096 by decide, ite_true, Option.some.injEq, exists_eq_left', BitVec.add_zero]
  have z13 : t₄.gpr .x13 = Proof.Rsa.result (Proof.Rsa.gOf (t.gpr .x0) r1 r3)
      (decide (Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat)) :=
    (hR.keep.gpr _ (by decide)).trans y13
  have m₃ : t₃.mem = t.mem := hm₃.trans (hI.mem.trans hm₁)
  have kk : Keep tailRegs t t₄ := ((k₁.trans (hI.keep.mono (by decide))).trans k₃).trans (hR.keep.mono (by decide))
  have hf : Frame [L.OUT, L.M] t.mem t₄.mem := fun x hx => by
    rw [hR.frame x (fun i hi h => hx L.OUT (by simp) (by rw [h, hOk]; exact contains_of_lt _ (by omega_using []) hi))
      (fun i hi h => hx L.M (by simp) (by
        rw [h, add_add]
        exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by simp only [oM]; omega_using [hkk]))), m₃]
  refine ⟨Ctx.outM hL hc ⟨fun r hr => ?_, kk.rd, kk.wr, kk.sp, kk.v⟩ hf, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write]
    split
    · rename_i h; subst h; simp at hr
    · exact kk.gpr r hr
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, z13]
  · simp only [RegUpd.mem_write]
    refine bytesAt_ext fun i hi => ?_
    rw [hR.out i hi, m₃]; simp only [decide_eq_true_eq]
  · simp only [RegUpd.mem_write, Spec.Rsa.bytesAt, List.eq_replicate_iff, List.length_map,
      List.length_range, List.mem_map, List.mem_range, true_and]
    rintro _ ⟨i, hi, rfl⟩
    exact hR.m i hi

end

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.PrivPub`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: the calls of the public operation

`pcArgs` keeps `r₁` and sets the arguments of `vg_rsa_public_precompute`
(`pcArgs_ok`), which writes `n`'s values to `PRE` (`pc_call`); `pdArgs`
keeps `r₃` and sets those of `vg_rsa_public_precomputed_checked`
(`pdArgs_ok`), which writes `M^e mod n` to `out` (`pd_call`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- `2 ⌈k / 8⌉`, as `preWords` computes it. -/
theorem preWords_eq (k : BitVec 64) (hk : k.toNat ≤ 1024) :
    (k + BitVec.ofNat 64 7) >>> 3 + (k + BitVec.ofNat 64 7) >>> 3 =
      BitVec.ofNat 64 (2 * ((k.toNat + 7) / 8)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := k.toNat + 7 % 2 ^ 64) (by omega_arith)]
  have : (k.toNat + 7) / 2 ^ 3 < 2 ^ 63 := by omega_arith
  rw [Nat.mod_eq_of_lt (a := (k.toNat + 7 % 2 ^ 64) / 2 ^ 3 + (k.toNat + 7 % 2 ^ 64) / 2 ^ 3) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem pw_le {L : Lay} (hL : L.Ok) : L.pw ≤ 256 := by have := hL.khi; unfold Lay.pw; omega_arith

theorem toNat_pw {L : Lay} (hL : L.Ok) : (BitVec.ofNat 64 L.pw).toNat = L.pw := by
  have := pw_le hL
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-! ## `vg_rsa_public_precompute` -/

/-- The arguments of `vg_rsa_public_precompute`. -/
structure PcArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.B + BitVec.ofNat 64 oPre
  x1 : t.gpr .x1 = BitVec.ofNat 64 L.pw
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.scr
  x5 : t.gpr .x5 = L.sl

theorem pcArgs_ok (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) :
    WP isa (.block pcArgs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ PcArgs L t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = t.gpr .x0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 oR1, 8⟩] t.mem t'.mem := by
  have hnB := hL.nB
  obtain lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  obtain lN := hc.inFr hL (d := oN) (n := 8) (by decide)
  obtain w := hc.inFrW hL (d := oR1) (n := 8) (by decide)
  obtain l10 := hc.inArgs hL (j := 10) (by omega_arith)
  obtain l11 := hc.inArgs hL (j := 11) (by omega_arith)
  obtain a10 := (hc.argW hL (j := 10) (by omega_arith)).trans (ha 10 (by omega_arith))
  obtain a11 := (hc.argW hL (j := 11) (by omega_arith)).trans (ha 11 (by omega_arith))
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 oR1, 8⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hsl := hs.frame hf (fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oR1) (k := 8) (by decide) (by simp only [oOut]; omega_arith)
      (by simp only [oR1]; omega_arith)) (by omega_arith)
  have k' : (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)).readW (L.B + BitVec.ofNat 64 oK) 64 = L.k :=
    hsl.k
  have n' : (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)).readW (L.B + BitVec.ofNat 64 oN) 64 = L.n :=
    hsl.n
  obtain hfr : Frame [L.FR] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain ea : ∀ j < 12, ((t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)).readW
      (L.B + BitVec.ofNat 64 (arg j)) 64) = t.mem.readW (L.B + BitVec.ofNat 64 (arg j)) 64 := fun j hj =>
    Mem.readW_writeW_sep (Offset.sep _ (d := arg j) (n := 8) (e := oR1) (k := 8)
      (by simp only [oR1, arg, frameBytes]; omega_arith) (by simp only [arg, frameBytes]; omega_arith)
      (by simp only [oR1]; omega_arith)) (by decide)
  apply WP.of_runBlock
  simp only [pcArgs, preWords, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, w, read8, write8, BitVec.add_zero, Option.some.injEq, exists_eq_left',
    show oR1 % 8 = 0 by decide, show oR1 < 4096 * 8 by decide, show oPre < 4096 by decide,
    show (0 : Nat) < 4096 by decide, show oK % 8 = 0 by decide, show oK < 32768 by decide,
    show oN % 8 = 0 by decide, show oN < 32768 by decide, show arg 10 % 8 = 0 by decide,
    show arg 10 < 32768 by decide, show arg 11 % 8 = 0 by decide, show arg 11 < 32768 by decide,
    show (7 : Nat) < 4096 by decide, show (3 : Nat) < 64 by decide, and_self, lK, lN, l10, l11,
    k', n', ea 10 (by omega_arith), ea 11 (by omega_arith), a10, a11, Lay.argv]
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) hfr, hsl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    Mem.readW_writeW_self64 _ _ _, hf⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  exact preWords_eq _ hL.khi

/-- The regions `vg_rsa_public_precompute` reads and writes. -/
abbrev pcRd (L : Lay) : List Region := [L.N]
abbrev pcWr (L : Lay) : List Region := [L.PRE, L.SC]

theorem pcCall_pre (hL : L.Ok) {t : State} (_hc : Ctx L g vv m₀ t) (ha : PcArgs L t) :
    pcA.pre (t.callEntry.withRegions (pcRd L) (pcWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  obtain hP := hL.stk_sub hL.PRE_sub
  simp only [pcA, State.withRegions_rd, State.withRegions_wr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, toNat_pw hL]
  obtain hPk : BitVec.toNat (L.B + BitVec.ofNat 64 oPre) + L.pw * 8 ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; have := pw_le hL; simp only [oPre]; omega_arith
  exact ⟨trivial, trivial, hP.2.1, hP.2.2.2.2.2.2.2.2.2, hL.nsc, hPk, hL.bn, hL.bsc, ⟨hL.klo, hL.khi⟩, rfl,
    hL.slk⟩

theorem pc_sub (hL : L.Ok) : ∀ r ∈ pcRd L ++ pcWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [pcRd, pcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.N, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oPre, frameBytes, Lay.pw]; omega_arith)⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem pc_wsub (hL : L.Ok) : ∀ r ∈ pcWr L, InW L r := by
  simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inr hL.PRE_HI)
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What `vg_rsa_public_precompute` writes and returns, from the memory `m`
at the call. -/
abbrev PcOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m L.n L.k.toNat) with
  | some ws => r.setWidth 32 = 1 ∧ Spec.Rsa.wordsAt m' (L.B + BitVec.ofNat 64 oPre) L.pw = ws
  | none => r.setWidth 32 = 0 ∧
    Spec.Rsa.wordsAt m' (L.B + BitVec.ofNat 64 oPre) L.pw = List.replicate L.pw 0

theorem pc_call (v : CrtImpl) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : PcArgs L t) :
    WP isa (.call v.pcName v.pc) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (pcWr L) t.mem t'.mem ∧ PcOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL v.pc_ok v.pcNoFrames hc hs (pcCall_pre hL hc ha) (pc_sub hL) (pc_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have h := hpost
  simp only [pcA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, toNat_pw hL] at h
  exact h

/-! ## `vg_rsa_public_precomputed_checked` -/

/-- The arguments of `vg_rsa_public_precomputed_checked`, in registers and
on the stack at `B`. -/
structure PdArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.B + BitVec.ofNat 64 oPre
  x3 : t.gpr .x3 = BitVec.ofNat 64 L.pw
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.B + BitVec.ofNat 64 oM
  x7 : t.gpr .x7 = L.k
  s0 : t.mem.readW L.B 64 = L.scr
  s1 : t.mem.readW (L.B + BitVec.ofNat 64 8) 64 = L.sl

theorem pdArgs_ok (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) :
    WP isa (.block pdArgs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ PdArgs L t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = t.gpr .x0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 oR3, 8⟩, ⟨L.B, 16⟩] t.mem t'.mem := by
  have hnB := hL.nB
  have lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  have lO := hc.inFr hL (d := oOut) (n := 8) (by decide)
  have lE := hc.inFr hL (d := oE) (n := 8) (by decide)
  have lEl := hc.inFr hL (d := oEl) (n := 8) (by decide)
  have w3 := hc.inFrW hL (d := oR3) (n := 8) (by decide)
  have w0 := hc.inFrW hL (d := 0) (n := 8) (by decide)
  have w8 := hc.inFrW hL (d := 8) (n := 8) (by decide)
  simp only [BitVec.add_zero] at w0
  have l10 := hc.inArgs hL (j := 10) (by omega_arith)
  have l11 := hc.inArgs hL (j := 11) (by omega_arith)
  have a10 := (hc.argW hL (j := 10) (by omega_arith)).trans (ha 10 (by omega_arith))
  have a11 := (hc.argW hL (j := 11) (by omega_arith)).trans (ha 11 (by omega_arith))
  -- The three stores.
  have sepA : ∀ j < 12, ∀ d, d + 8 ≤ frameBytes → Mem.Sep (L.B + BitVec.ofNat 64 (arg j)) (64 / 8)
      (L.B + BitVec.ofNat 64 d) (64 / 8) := fun j hj d hd =>
    Offset.sep _ (d := arg j) (n := 8) (e := d) (k := 8) (by simp only [arg, frameBytes] at hd ⊢; omega_arith)
      (by simp only [arg, frameBytes]; omega_arith) (by simp only [frameBytes] at hd; omega_arith)
  have f1 : Frame [⟨L.B + BitVec.ofNat 64 oR3, 8⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have s1 := hs.frame f1 (fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oR3) (k := 8) (by decide) (by simp only [oOut]; omega_arith)
      (by simp only [oR3]; omega_arith)) (by omega_arith)
  have e10 : (t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).readW (L.B + BitVec.ofNat 64 (arg 10)) 64 = L.scr :=
    (Mem.readW_writeW_sep (sepA 10 (by omega_arith) oR3 (by decide)) (by decide)).trans a10
  have e11 : ((t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).writeW L.B L.scr).readW (L.B + BitVec.ofNat 64 (arg 11)) 64 = L.sl := by
    have := sepA 11 (by omega_arith) 0 (by decide)
    simp only [BitVec.add_zero] at this
    exact (Mem.readW_writeW_sep this (by decide)).trans
      ((Mem.readW_writeW_sep (sepA 11 (by omega_arith) oR3 (by decide)) (by decide)).trans a11)
  apply WP.of_runBlock
  simp only [pdArgs, preWords, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some,
    Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.sp, read8, write8, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', show oR3 % 8 = 0 by decide, show oR3 < 4096 * 8 by decide,
    show oPre < 4096 by decide, show oM < 4096 by decide, show (0 : Nat) < 4096 by decide,
    show oK % 8 = 0 by decide, show oK < 32768 by decide, show oOut % 8 = 0 by decide,
    show oOut < 32768 by decide, show oE % 8 = 0 by decide, show oE < 32768 by decide,
    show oEl % 8 = 0 by decide, show oEl < 32768 by decide, show arg 10 % 8 = 0 by decide,
    show arg 10 < 32768 by decide, show arg 11 % 8 = 0 by decide, show arg 11 < 32768 by decide,
    show (0 : Nat) % 8 = 0 by decide, show (0 : Nat) < 4096 * 8 by decide,
    show (8 : Nat) < 4096 * 8 by decide, show (7 : Nat) < 4096 by decide, show (3 : Nat) < 64 by decide,
    and_self, lK, lO, lE, lEl, l10, l11, w3, w0, w8, s1.out, s1.k, s1.e, s1.el, e10, e11]
  have hc3 : (⟨L.B + BitVec.ofNat 64 oR3, 8⟩ : Region).Contains (L.B + BitVec.ofNat 64 oR3) (64 / 8) :=
    Region.contains_self _ _
  have hc0 : (⟨L.B, 16⟩ : Region).Contains L.B (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have hc8 : (⟨L.B, 16⟩ : Region).Contains (L.B + BitVec.ofNat 64 8) (64 / 8) :=
    Offset.contains_base _ (by decide) (by decide)
  have f3 : Frame [⟨L.B + BitVec.ofNat 64 oR3, 8⟩, ⟨L.B, 16⟩] t.mem
      (((t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).writeW L.B L.scr).writeW
        (L.B + BitVec.ofNat 64 8) L.sl) :=
    (((Frame.refl _ _).writeW (by simp) _ hc3).writeW (by simp) _ hc0).writeW (by simp) _ hc8
  have fFR : Frame [L.FR] t.mem
      (((t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).writeW L.B L.scr).writeW
        (L.B + BitVec.ofNat 64 8) L.sl) := Frame.sub f3 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.FR, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨L.FR, by simp, Region.sub_prefix (by decide)⟩
  have s3 := hs.frame f3 (fun R hR => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oR3) (k := 8) (by decide)
        (by simp only [oOut]; omega_arith) (by simp only [oR3]; omega_arith)
    · exact Offset.disjoint_base _ (by decide) (by simp only [oOut]; omega_arith)) (by omega_arith)
  have sep08 : Mem.Sep L.B (64 / 8) (L.B + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep L.B (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by omega_arith)
    simpa using this
  have sepR : ∀ d, d + 8 ≤ oR3 → Mem.Sep (L.B + BitVec.ofNat 64 oR3) (64 / 8) (L.B + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.sep L.B (d := oR3) (n := 8) (e := d) (k := 8) (by omega_arith) (by simp only [oR3]; omega_arith)
      (by simp only [oR3] at hd; omega_arith)
  have sepR0 : Mem.Sep (L.B + BitVec.ofNat 64 oR3) (64 / 8) L.B (64 / 8) := by
    have := sepR 0 (by decide); simpa using this
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) fFR, s3, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, f3⟩
  all_goals try simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  · exact preWords_eq _ hL.khi
  · rw [Mem.readW_writeW_sep sep08 (by decide), Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (sepR 8 (by decide)) (by decide), Mem.readW_writeW_sep sepR0 (by decide),
      Mem.readW_writeW_self64]

theorem OUT_k (hL : L.Ok) : (⟨L.out, L.k.toNat⟩ : Region) = L.OUT := by rw [Lay.OUT, hL.olk]

/-- The regions `vg_rsa_public_precomputed_checked` reads and writes. -/
abbrev pdRd (L : Lay) : List Region := [L.PRE, L.E, L.M, ⟨L.B, 16⟩]
abbrev pdWr (L : Lay) : List Region := [⟨L.out, L.k.toNat⟩, L.SC]

theorem pdCall_pre (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (ha : PdArgs L t) :
    pdA.pre (t.callEntry.withRegions (pdRd L) (pdWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  obtain sa0 : stackArg (t.callEntry.withRegions (pdRd L) (pdWr L)) 0 = L.scr := by
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp, Nat.mul_zero, BitVec.add_zero]
    exact ha.s0
  obtain sa1 : stackArg (t.callEntry.withRegions (pdRd L) (pdWr L)) 1 = L.sl := by
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.s1
  obtain hP := hL.stk_sub hL.PRE_sub
  obtain hM := hL.stk_sub hL.M_sub
  obtain hA := hL.stk_sub (low_sub L (n := 16) (by decide))
  simp only [pdRd, pdWr, OUT_k hL] at sa0 sa1
  simp only [pdA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, sa0, sa1, stackArgAddr, Nat.mul_zero, BitVec.add_zero,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, toNat_pw hL, OUT_k hL, pdRd, pdWr]
  obtain hPk : BitVec.toNat (L.B + BitVec.ofNat 64 oPre) + L.pw * 8 ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; have := pw_le hL; simp only [oPre]; omega_arith
  obtain hMk : BitVec.toNat (L.B + BitVec.ofNat 64 oM) + L.k.toNat ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; simp only [oM]; omega_arith
  exact ⟨by omega_arith, trivial, trivial, hP.1.symm, hL.oe, hM.1.symm, hL.osc, hA.1.symm, hP.2.2.2.2.2.2.2.2.2,
    hL.esc, hM.2.2.2.2.2.2.2.2.2, hA.2.2.2.2.2.2.2.2.2.symm, by rw [← hL.olk]; exact hL.bo, hPk, hL.be, hMk,
    hL.bsc, ⟨hL.klo, hL.khi⟩, rfl, trivial, hL.el1, hL.elk, hL.slk⟩

theorem pd_sub (hL : L.Ok) : ∀ r ∈ pdRd L ++ pdWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oPre, frameBytes, Lay.pw]; omega_arith)⟩
  · exact ⟨L.E, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oM, frameBytes]; omega_arith)⟩
  · exact ⟨L.FR, by simp, within_base _ (by decide)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by rw [hL.olk])⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem pd_wsub (hL : L.Ok) : ∀ r ∈ pdWr L, InW L r := by
  simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (within_base _ (by rw [hL.olk]))
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What `vg_rsa_public_precomputed_checked` writes and returns, from the
memory `m` at the call. -/
abbrev PdOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  ∀ nB : List Byte, nB.length = L.k.toNat →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt m (L.B + BitVec.ofNat 64 oPre) L.pw) →
    Spec.Rsa.written m' L.out L.k.toNat (r.setWidth 32)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt m L.e L.el.toNat)
        (Spec.Rsa.bytesAt m (L.B + BitVec.ofNat 64 oM) L.k.toNat))

theorem pd_call (v : CrtImpl) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : PdArgs L t) :
    WP isa (.call v.pdName v.pd) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (pdWr L) t.mem t'.mem ∧ PdOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL v.pd_ok v.pdNoFrames hc hs (pdCall_pre hL hc ha) (pd_sub hL) (pd_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have h := hpost
  simp only [pdA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, toNat_pw hL] at h
  exact h

end

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: what follows the CRT

`check_ok` runs everything after the call of the CRT, from any state the
frames allow: whatever `M` holds and whatever the CRT returned (`r₁`), it
releases `M` to `out` (and returns 1) only if `r₁` is odd, `n` is a valid
modulus and the public operation of `M` with `e`, within BoringSSL's
limits, is the input; otherwise `out` is zeros (`released`, `checkResult`).
This is the fault tolerance of the check.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked
open VG.Proof.Rsa (released checkResult gOf result)

/-- The bytes of a region that a frame's regions miss are unchanged. -/
theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The words of a region that a frame's regions miss are unchanged. -/
theorem frame_wordsAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 8 * n⟩ r) (hn : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (r := ⟨p, 8 * n⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi])) hd (by decide)

theorem check_eq (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) :
    seqs (check pcName pc pdName pd) =
      .seq (.block pcArgs) (.seq (.call pcName pc) (.seq (.block pdArgs) (.seq (.call pdName pd)
        (seqs tail)))) := rfl

theorem checkWith_eq (stage : Prog isa) (pdName : String) (pd : Prog isa) :
    seqs (checkWith stage pdName pd) =
      .seq (.block pcArgs) (.seq stage (.seq (.block pdArgs) (.seq (.call pdName pd)
        (seqs tail)))) := rfl

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

namespace Ctx
variable {t : State} (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

theorem n_bytes : Spec.Rsa.bytesAt t.mem L.n L.k.toNat = Spec.Rsa.bytesAt m₀ L.n L.k.toNat :=
  frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hL.on.symm, hL.nsc, hL.kn.symm]) (by have := hL.bn; omega_using [])

theorem e_bytes : Spec.Rsa.bytesAt t.mem L.e L.el.toNat = Spec.Rsa.bytesAt m₀ L.e L.el.toNat :=
  frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hL.oe.symm, hL.esc, hL.ke.symm]) (by have := hL.be; omega_using [])

theorem inp_bytes : Spec.Rsa.bytesAt t.mem L.inp L.k.toNat = Spec.Rsa.bytesAt m₀ L.inp L.k.toNat := by
  have h := frame_bytesAt hc.frame (p := L.inp) (n := L.il.toNat) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hL.oi.symm, hL.isc, hL.ki.symm]) (by have := hL.bi; omega_using [])
  rwa [hL.ilk] at h

end Ctx

/-- A slot, in the inner frame below `M`, misses what the calls write. -/
theorem slot_disj (hL : L.Ok) {d : Nat} (hd : 80 ≤ d ∧ d + 8 ≤ oM) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.PRE ∧ Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.SC ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.M ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ ⟨L.out, L.k.toNat⟩ ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ ⟨L.B, 16⟩ := by
  have hnB := hL.nB
  have hk := hL.khi
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.STK := Offset.sub_base _ (by simp only [oM, stackBytes] at hd ⊢; omega_using [hd])
  refine ⟨Offset.disjoint _ (.inl (by simp only [oM, oPre] at hd ⊢; omega_using [hd])) (by simp only [oM] at hd; omega_using [hd])
      (by simp only [oPre, Lay.pw]; omega_using [hk]), (hL.ksc.sub_left hs),
    Offset.disjoint _ (.inl hd.2) (by simp only [oM] at hd; omega_using [hd]) (by simp only [oM]; omega_using [hk]), ?_,
    Offset.disjoint_base _ (by omega_using [hd]) (by simp only [oM] at hd; omega_using [hd])⟩
  rw [show (⟨L.out, L.k.toNat⟩ : Region) = L.OUT by rw [Lay.OUT, hL.olk]]
  exact hL.ko.sub_left hs

/-- Everything after the CRT, from any state the frames allow: whatever `M`
holds and the CRT returned. -/
theorem checkWith_ok (v : CrtImpl) (stage : Prog isa) (hL : L.Ok) (ha : ArgsAt L m₀)
    (hst : ∀ t, Ctx L g vv m₀ t → Slots L t.mem → PcArgs L t →
      WP isa stage t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Frame (pcWr L) t.mem t'.mem ∧
        PcOut L t.mem t'.mem (t'.gpr .x0))
    {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) :
    WP isa (seqs (checkWith stage v.pdName v.pd)) t fun t' => Ctx L g vv m₀ t' ∧
      t'.gpr .x0 = checkResult (t.gpr .x0) (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)
        (Spec.Rsa.bytesAt m₀ L.e L.el.toNat) (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat)
        (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat) ∧
      Spec.Rsa.bytesAt t'.mem L.out L.k.toNat =
        (if released (t.gpr .x0) (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
            (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat)
          then Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat
          else List.replicate L.k.toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat = List.replicate L.k.toNat 0 := by
  have hnB := hL.nB
  have hk := hL.khi
  have hMs : Region.Sub L.M L.STK := hL.M_sub
  have hM := hL.stk_sub hMs
  have hOk : (⟨L.out, L.k.toNat⟩ : Region) = L.OUT := by rw [Lay.OUT, hL.olk]
  rw [checkWith_eq]
  refine WP.seq (WP.mono (pcArgs_ok hL ha hc hs) fun t₁ ⟨hc₁, hs₁, pa, hR1, f₁⟩ => ?_)
  refine WP.seq (WP.mono (hst t₁ hc₁ hs₁ pa) fun t₂ ⟨hc₂, hs₂, f₂, hpc⟩ => ?_)
  refine WP.seq (WP.mono (pdArgs_ok hL ha hc₂ hs₂) fun t₃ ⟨hc₃, hs₃, pda, hR3, f₃⟩ => ?_)
  refine WP.seq (WP.mono (pd_call v hL hc₃ hs₃ pda) fun t₄ ⟨hc₄, hs₄, f₄, hpd⟩ => ?_)
  -- The slots `r₁` and `r₃`.
  have d1 := slot_disj hL (d := oR1) (by decide)
  have d3 := slot_disj hL (d := oR3) (by decide)
  have d13 : Region.Disjoint ⟨L.B + BitVec.ofNat 64 oR1, 8⟩ ⟨L.B + BitVec.ofNat 64 oR3, 8⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by simp only [oR1]; omega_using []) (by simp only [oR3]; omega_using [])
  have r1₄ : t₄.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = t.gpr .x0 := by
    rw [f₄.readW (Region.contains_self _ _) (by
        simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d1.2.2.2.1, d1.2.1]) (by decide),
      f₃.readW (Region.contains_self _ _) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d13, d1.2.2.2.2]) (by decide),
      f₂.readW (Region.contains_self _ _) (by
        simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d1.1, d1.2.1]) (by decide)]
    exact hR1
  have r3₄ : t₄.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = t₂.gpr .x0 := by
    rw [f₄.readW (Region.contains_self _ _) (by
        simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d3.2.2.2.1, d3.2.1]) (by decide)]
    exact hR3
  -- `M`, `n`'s values, and the inputs.
  have hMk : L.k.toNat ≤ 2 ^ 64 := by omega_using []
  have hMR1 : L.M.Disjoint ⟨L.B + BitVec.ofNat 64 oR1, 8⟩ := d1.2.2.1.symm
  have hMR3 : L.M.Disjoint ⟨L.B + BitVec.ofNat 64 oR3, 8⟩ := d3.2.2.1.symm
  have hMP : L.M.Disjoint L.PRE :=
    Offset.disjoint _ (.inl (by simp only [oM, oPre]; omega_using [hk])) (by simp only [oM]; omega_using [hk])
      (by simp only [oPre, Lay.pw]; omega_using [hk])
  have hMB : L.M.Disjoint ⟨L.B, 16⟩ := Offset.disjoint_base _ (by decide) (by simp only [oM]; omega_using [hk])
  have m₃ : Spec.Rsa.bytesAt t₃.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat =
      Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat := by
    rw [frame_bytesAt f₃ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [hMR3, hMB]) hMk,
      frame_bytesAt f₂ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [hMP, hM.2.2.2.2.2.2.2.2.2]) hMk,
      frame_bytesAt f₁ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl; exact hMR1) hMk]
  have m₄ : Spec.Rsa.bytesAt t₄.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat =
      Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat := by
    rw [frame_bytesAt f₄ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · rw [hOk]; exact hM.1
        · exact hM.2.2.2.2.2.2.2.2.2) hMk, m₃]
  have hpre : Spec.Rsa.wordsAt t₃.mem (L.B + BitVec.ofNat 64 oPre) L.pw =
      Spec.Rsa.wordsAt t₂.mem (L.B + BitVec.ofNat 64 oPre) L.pw := by
    have hP16 : L.PRE.Disjoint ⟨L.B, 16⟩ :=
      Offset.disjoint_base _ (by decide) (by simp only [oPre, Lay.pw]; omega_using [hk])
    refine frame_wordsAt f₃ (fun r hr => ?_) (by unfold Lay.pw; omega_using [hk])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (by rw [Nat.mul_comm]; exact d3.1.symm)
    · exact (by rw [Nat.mul_comm]; exact hP16)
  have hn₁ := hc₁.n_bytes hL
  have he₃ := hc₃.e_bytes hL
  have hi₄ := hc₄.inp_bytes hL
  simp only [PcOut, PdOut] at hpc hpd
  rw [hn₁] at hpc
  rw [he₃, m₃] at hpd
  refine WP.mono (tail_ok hL hc₄ hs₄ r1₄ r3₄) fun t' ⟨hc', hax, hout, hM'⟩ => ⟨hc', ?_, ?_, ?_⟩
  all_goals rw [hi₄] at hax hout
  all_goals rw [m₄] at hout
  all_goals
    have h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) with
        | some _ => (t₂.gpr .x0).setWidth 32 = 1
        | none => (t₂.gpr .x0).setWidth 32 = 0 := by
      cases hcs : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) <;>
        simp only [hcs] at hpc ⊢ <;> exact hpc.1
    have hl := Proof.Rsa.check_logic (r₁ := t.gpr .x0) (r₂ := t₄.gpr .x0) (r₃ := t₂.gpr .x0)
      (eB := Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
      (mB := Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat)
      (outB := Spec.Rsa.bytesAt t₄.mem L.out L.k.toNat)
      (xB := Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) h3 (fun hsm => by
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hsm
        rw [hws] at hpc
        have := hpd _ (Proof.Rsa.bytesAt_length' _ _ _) (by rw [hws, hpre, hpc.2])
        cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)
            (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
            (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat) <;>
          simp only [hpo, Spec.Rsa.written] at this ⊢
        · exact this.1
        · exact this)
  · rw [hax]; exact hl.1
  · rw [hout]; simp only [hl.2]
  · exact hM'


/-- `checkWith_ok`, calling `vg_rsa_public_precompute`. -/
theorem check_ok (v : CrtImpl) (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hs : Slots L t.mem) :
    WP isa (seqs (check v.pcName v.pc v.pdName v.pd)) t fun t' => Ctx L g vv m₀ t' ∧
      t'.gpr .x0 = checkResult (t.gpr .x0) (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)
        (Spec.Rsa.bytesAt m₀ L.e L.el.toNat) (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat)
        (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat) ∧
      Spec.Rsa.bytesAt t'.mem L.out L.k.toNat =
        (if released (t.gpr .x0) (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
            (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat)
          then Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat
          else List.replicate L.k.toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat = List.replicate L.k.toNat 0 :=
  checkWith_ok v _ hL ha (fun _ hc hs pa => pc_call v hL hc hs pa) hc hs

end

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: correctness

The frames' pushes, the CRT's arguments and call (`crtArgs_ok`,
`crt_call`), the check (`check_ok`) and the pops: `code_correct`, for every
implementation of the CRT.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked
open VG.Proof.Rsa (released checkResult)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

namespace Ctx
variable {t : State} (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

omit hL in
/-- A buffer the code only reads is as it was on entry. -/
theorem ro_bytes {R : Region} (ho : R.Disjoint L.OUT) (hs : R.Disjoint L.SC) (hk : L.STK.Disjoint R)
    (hR : R.base.toNat + R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m₀ R.base R.len :=
  frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [ho, hs, hk.symm]) (by omega_using [hR])

/-- The key, as the CRT reads it. -/
theorem key_bytes :
    Spec.Rsa.bytesAt t.mem L.p L.pl.toNat = Spec.Rsa.bytesAt m₀ L.p L.pl.toNat ∧
    Spec.Rsa.bytesAt t.mem L.q L.ql.toNat = Spec.Rsa.bytesAt m₀ L.q L.ql.toNat ∧
    Spec.Rsa.bytesAt t.mem L.dp L.pl.toNat = Spec.Rsa.bytesAt m₀ L.dp L.pl.toNat ∧
    Spec.Rsa.bytesAt t.mem L.dq L.ql.toNat = Spec.Rsa.bytesAt m₀ L.dq L.ql.toNat ∧
    Spec.Rsa.bytesAt t.mem L.qi L.pl.toNat = Spec.Rsa.bytesAt m₀ L.qi L.pl.toNat := by
  have hdp := hc.ro_bytes hL.odp.symm hL.dpsc hL.kdp hL.bdp
  have hdq := hc.ro_bytes hL.odq.symm hL.dqsc hL.kdq hL.bdq
  have hqi := hc.ro_bytes hL.oqi.symm hL.qisc hL.kqi hL.bqi
  simp only [hL.dpl, hL.dql, hL.qil] at hdp hdq hqi
  exact ⟨hc.ro_bytes hL.op.symm hL.psc hL.kp hL.bp, hc.ro_bytes hL.oq.symm hL.qsc hL.kq hL.bq,
    hdp, hdq, hqi⟩

end Ctx

/-- The CRT's arguments, from the inner frame's entry. -/
theorem crtArgs_ok (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hr : Regs L t) :
    WP isa (.block crtArgs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ CrtArgs L t' := by
  rw [crtArgs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveSlots_ok hL hc hr) fun t₁ ⟨hc₁, hs₁, hr₁, h15, _⟩ => ?_
  refine WP.mono (copyArgs_upto hL (t₀ := t₁) 10 (by omega_using []) t₁
    ⟨hc₁, hs₁, hr₁, h15, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩) fun t₂ hI => ?_
  exact WP.mono (crtRegs_ok hL ha hI) fun t₃ ⟨hc₃, hs₃, a₃, _⟩ => ⟨hc₃, hs₃, a₃⟩

theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl
theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_v (b : Nat) (s : State) : (freed b s).v = s.v := rfl
theorem popped_mem (s : State) : (popped .x30 s).mem = s.mem := rfl
theorem popped_sp (s : State) : (popped .x30 s).sp = s.sp + 16 := rfl
theorem popped_v (s : State) : (popped .x30 s).v = s.v := rfl
theorem popped_gpr (s : State) (r : Reg) :
    (popped .x30 s).gpr r = if r = .x30 then s.mem.read s.sp 8 else s.gpr r := by
  show (s.write .x .x30 _).gpr r = _
  rw [RegUpd.gpr_write, BitVec.setWidth_eq]

theorem body_eq (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) :
    body crtName crt pcName pc pdName pd =
      .seq (.block crtArgs) (.seq (.call crtName crt) (seqs (check pcName pc pdName pd))) := rfl

/-- `vg_rsa_private_checked`, calling the CRT `v` and its public operation. -/
abbrev privCodeOf (v : CrtImpl) : Prog isa := code v.name v.code v.pcName v.pc v.pdName v.pd

/-- `vg_rsa_private_checked`'s frames and calls, calling the CRT `C`, with
`stage` writing `n`'s values. -/
abbrev codeWith (C : CrtCallee) (v : CrtImpl) (stage : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes)
    (seqs ([.block crtArgs, .call C.name C.code] ++ checkWith stage v.pdName v.pd)) (.free frameBytes))
    (.pop .x30)

/-- What `stage` does in place of calling `vg_rsa_public_precompute`. -/
abbrev StageOk (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (stage : Prog isa) : Prop :=
  ∀ t, Ctx L g vv m₀ t → Slots L t.mem → PcArgs L t →
    WP isa stage t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Frame (pcWr L) t.mem t'.mem ∧
      PcOut L t.mem t'.mem (t'.gpr .x0)

/-- The frames, the CRT `C` and the check, for a call that may also read `X`
(`chkA` holding of it reading the rest, `R₀`), whatever `stage` writes `n`'s
values, given that the CRT's call states have `C.K`. -/
theorem codeWith_correct (C : CrtCallee) (v : CrtImpl) (stage : Prog isa) {s : State} {R₀ X : List Region}
    (h : chkA.pre (s.withRegions R₀ s.wr)) (hX : s.rd = R₀ ++ X)
    (hst : StageOk (layW s X) s.gpr s.v s.mem stage)
    (hK : ∀ t, Ctx (layW s X) s.gpr s.v s.mem t → CrtArgs (layW s X) t →
      C.K (t.callEntry.withRegions (crtRd (layW s X)) (crtWr (layW s X)))) :
    WP isa (codeWith C v stage) s fun s' => abiPreserved s s' ∧ chkA.post s s' := by
  have hL : (layW s X).Ok := (lay_ok h).withX X
  have hst0 : stackBytes ≤ s.sp.toNat := h.1
  have hnB := hL.nB
  refine WP.frame (by unfold stackBytes at hst0; omega_using [hst0]) ?_
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by
    show frameBytes ≤ (s.sp - 16).toNat
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.toNat_sub_ofNat]
    simp only [frameBytes, stackBytes] at hst0 ⊢
    omega_using [hst0]) ?_
  show WP isa (seqs _) (entered s) _
  have ha : ArgsAt (layW s X) s.mem := argsAt_entry s
  refine WP.seq (WP.mono (crtArgs_ok hL ha (entered_ctxW h hX) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    fun t₁ ⟨hc₁, hs₁, a₁⟩ => ?_)
  refine WP.seq (WP.mono (crt_call C hL hc₁ hs₁ a₁ (hK t₁ hc₁ a₁)) fun t₂ ⟨hc₂, hs₂, _, hcrt⟩ => ?_)
  refine WP.mono (checkWith_ok v stage hL ha hst hc₂ hs₂) fun t₃ ⟨hc₃, hax, hout, _⟩ m₁ u₁ f₁ m₂ u₂ f₂ => ?_
  have hsp₃ : (freed frameBytes t₃).sp = (layW s X).B + BitVec.ofNat 64 frameBytes := by
    rw [freed_sp, hc₃.sp]
  -- The two frames' bytes are lost: the inner frame's by the `free`, then
  -- the one saving `x30` by the pop, which reads it from the outer frame.
  have e₁ : (pushed .x30 s).sp - BitVec.ofNat 64 frameBytes = (layW s X).B := entered_sp s
  rw [e₁] at f₁
  have f₁' : Frame [(layW s X).FR] t₃.mem m₁ := f₁
  rw [lr_slot] at f₂
  have f₂' : Frame [(layW s X).LR] m₁ m₂ := f₂
  have fS : Frame [(layW s X).STK] t₃.mem m₂ := by
    refine (Frame.sub f₁' fun r hr => ?_).trans (Frame.sub f₂' fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · show (popped .x30 { freed frameBytes t₃ with mem := m₁, unknowns := u₁ }).gpr r = s.gpr r
    rw [popped_gpr]
    split
    · rename_i h; subst h
      show m₁.read (freed frameBytes t₃).sp 8 = _
      rw [hsp₃, read8, f₁'.readW (r := (layW s X).LR)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
        (fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR
          exact Offset.disjoint_base _ (Nat.le_refl _) (by decide)) (by decide)]
      exact hc₃.lr
    · rename_i h; exact hc₃.cs r hr h
  · show (freed frameBytes t₃).sp + 16 = s.sp
    rw [hsp₃, BitVec.add_assoc]
    exact lay_top s
  · exact hc₃.vs r hr
  · -- The outcome.
    obtain ⟨kp, kq, kdp, kdq, kqi⟩ := hc₁.key_bytes hL
    simp only [CrtOut] at hcrt
    rw [hc₁.n_bytes hL, hc₁.inp_bytes hL, kp, kq, kdp, kdq, kqi] at hcrt
    -- The output lies apart from the stack, whose frames' bytes are lost.
    have hb : Spec.Rsa.bytesAt m₂ (s.gpr .x0) (s.gpr .x3).toNat =
        Spec.Rsa.bytesAt t₃.mem (s.gpr .x0) (s.gpr .x3).toNat :=
      List.map_congr_left fun i hi => lost_byte (R := (layW s X).OUT) fS hL.ko.symm
        (show i < (layW s X).ol.toNat by rw [hL.olk]; exact List.mem_range.mp hi)
    refine Proof.Rsa.writtenOutcome_of_bytesAt hb ?_
    show Spec.Rsa.writtenOutcome t₃.mem (s.gpr .x0) (s.gpr .x3).toNat
      (((popped .x30 { freed frameBytes t₃ with mem := m₁, unknowns := u₁ }).gpr .x0).setWidth 32) _
    rw [popped_gpr, ite_neg' (by decide)]
    show Spec.Rsa.writtenOutcome t₃.mem (s.gpr .x0) (s.gpr .x3).toNat ((t₃.gpr .x0).setWidth 32) _
    exact Proof.Rsa.outcome_eq (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) hcrt hax hout

theorem code_correct (v : CrtImpl) (s : State) (h : chkA.pre s) :
    ∃ t s', Exec isa (privCodeOf v) s t s' ∧ abiPreserved s s' ∧ chkA.post s s' := by
  have hL := lay_ok h
  obtain ⟨t, s', he, hq⟩ := codeWith_correct v.callee v (.call v.pcName v.pc) (R₀ := s.rd) (X := [])
    (by exact h) (List.append_nil _).symm (fun _ hc hs pa => pc_call v ((lay_ok h).withX []) hc hs pa)
    fun _ _ _ => trivial
  exact ⟨t, s', he, hq⟩

end

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: constant time

Two runs whose public data agree (the pointers and lengths, `n` and `e`)
have the same layout, so between the frames' pushes and pops they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the
next piece needs), whatever their secrets. The blocks are checked by the
taint analysis, from the registers `Φ` fixes as functions of the layout;
each call is of constant-time code whose public data agree (`RelCT.call`):
`n` and `e`, and `n`'s values, which are a function of `n`. The frames leak
only `sp`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The public data of the two runs' memories agree. -/
def PubEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`, with `G`
holding of their layout and memories on entry. -/
def Two (G : Env → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, G e ∧ e.L.Ok ∧ ArgsAt e.L e.m₁ ∧ ArgsAt e.L e.m₂ ∧ PubEq e.L e.m₁ e.m₂ ∧
    Ctx e.L e.g₁ e.v₁ e.m₁ a ∧ Ctx e.L e.g₂ e.v₂ e.m₂ b ∧ Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

variable {G : Env → Prop}

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two G Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two G Φ) c (Two G Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hG, hL, a₁, a₂, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL a₁ c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL a₂ c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hG, hL, a₁, a₂, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses and branches depend only on `sp` and the
registers `rs`, which `Φ` fixes as functions `f` of the layout. -/
theorem two_blk {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop} (rs : List Reg)
    (f : Lay → Reg → BitVec 64) (hf : ∀ L m t, Φ L m t → ∀ r ∈ rs, t.gpr r = f L r)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two G Φ) c (Two G Ψ) :=
  two_wp (RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
      rw [Taint.mem_ofRegs] at hr
      rw [hf _ _ _ f₁ r hr, hf _ _ _ f₂ r hr]⟩) h) hw

/-- A call of verified code, with the same regions in both runs, after
which `Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ v₁ v₂ m₁ m₂, L.Ok → PubEq L m₁ m₂ → Ctx L g₁ v₁ m₁ t₁ →
      Ctx L g₂ v₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay), L.Ok → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay), L.Ok → ∀ r ∈ wr L, InW L r)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two G Φ) (.call n c) (Two G Ψ) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hG, hL, a₁, a₂, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := covers c₁ (hsub _ hL) (hwsub _ hL)
    have w₂ := covers c₂ (hsub _ hL) (hwsub _ hL)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ _ hL a₁ c₁ f₁, hpre _ _ _ _ _ hL a₂ c₂ f₂,
          hpub _ _ _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The tail -/

/-- After the comparison's set-up. -/
abbrev PhiB (L : Lay) (_ : Mem) (t : State) : Prop :=
  Slots L t.mem ∧ t.gpr .x11 = L.out ∧ t.gpr .x12 = L.inp ∧ t.gpr .x13 = L.k ∧ t.gpr .x14 = 0 ∧
    (t.gpr .x9 = 0 ∨ t.gpr .x9 = 1)

/-- After the comparison. -/
abbrev PhiC (L : Lay) (_ : Mem) (t : State) : Prop := Slots L t.mem ∧ (t.gpr .x9 = 0 ∨ t.gpr .x9 = 1)

/-- After the masks. -/
abbrev PhiD (L : Lay) (_ : Mem) (t : State) : Prop :=
  t.gpr .x11 = L.out ∧ t.gpr .x14 = L.B + BitVec.ofNat 64 oM ∧ t.gpr .x15 = L.k

/-- The registers `PhiB`, `PhiD` fix. -/
def fixB (L : Lay) : Reg → BitVec 64
  | .x11 => L.out | .x12 => L.inp | .x13 => L.k | _ => 0

theorem cmpArgs_ct : RelCT isa (Two G fun L _ t => Slots L t.mem) (.block cmpArgs) (Two G PhiB) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun L _ _ _ t hL _ hc hs => WP.mono (cmpArgs_ok hL hc hs rfl rfl)
      fun t' ⟨hm, hk, x9, x11, x12, x13, x14⟩ =>
        ⟨hc.keep hk hm, by rw [hm]; exact hs, x11, x12, x13, x14, x9 ▸ Proof.Rsa.gOf_cases _ _ _⟩

theorem cmpLoop_ct : RelCT isa (Two G PhiB) cmpLoop (Two G PhiC) := by
  refine two_blk [.x11, .x12, .x13] fixB (fun L _ t ⟨_, x11, x12, x13, _⟩ r hr => ?_) (by taint_decide)
    fun L _ _ _ t hL _ hc ⟨hs, x11, x12, x13, x14, x9⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [fixB] <;> with_reducible assumption
  · have hk := hL.khi
    have hk1 : 1 ≤ L.k.toNat := by have := hL.klo; omega_arith
    have hok : L.out.toNat + L.k.toNat ≤ 2 ^ 64 := hL.olk ▸ hL.bo
    have hik : L.inp.toNat + L.k.toNat ≤ 2 ^ 64 := hL.ilk ▸ hL.bi
    have hOk : L.OUT = ⟨L.out, L.k.toNat⟩ := by rw [Lay.OUT, hL.olk]
    refine WP.mono (cmpLoop_ok (op := L.out) (ip := L.inp) hk1 (by omega_arith) x11 x12
      (by rw [x13, BitVec.ofNat_toNat, BitVec.setWidth_eq]) x14
      (fun i hi => ⟨L.OUT, by rw [hc.rd, hc.wr]; simp, hOk ▸ contains_of_lt _ (by omega_arith) hi⟩)
      (fun i hi => ⟨L.IN, by rw [hc.rd, hc.wr]; simp, by rw [Lay.IN, hL.ilk]; exact contains_of_lt _ (by omega_arith) hi⟩))
      fun t' hI => ⟨hc.keep (hI.keep.mono (by decide)) hI.mem, by rw [hI.mem]; exact hs, ?_⟩
    rw [hI.keep.gpr _ (by decide)]; exact x9

theorem masks_ct : RelCT isa (Two G PhiC) (.block masks) (Two G PhiD) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun L _ _ _ t hL _ hc ⟨hs, x9⟩ => WP.mono (masks_ok (eq := decide (t.gpr .x14 = 0)) hL hc hs rfl x9
      (by simp)) fun t' ⟨hm, hk, _, _, _, x11, x14, x15⟩ => ⟨hc.keep hk hm, x11, x14, x15⟩

theorem release_ct :
    RelCT isa (Two G PhiD) (.seq releaseLoop (.block [.addImm .x .x0 .x13 0])) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x11, .x14, .x15])
    (fun _ _ ⟨_, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
      rw [Taint.mem_ofRegs] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [f₁.1, f₂.1]
      · rw [f₁.2.1, f₂.2.1]
      · rw [f₁.2.2, f₂.2.2]⟩) (by taint_decide)

theorem tail_ct : RelCT isa (Two G fun L _ t => Slots L t.mem) (seqs tail) fun _ _ => True := by
  rw [tail_eq]
  exact cmpArgs_ct.seq (cmpLoop_ct.seq (masks_ct.seq release_ct))

/-! ## The calls -/

theorem ce_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (8 * i)) 64 := rfl

/-- The CRT `C` gets `C.K` at its call from what `H` says of the layout and
the memory on entry. -/
def KOk (C : CrtCallee) (H : Lay → Mem → Prop) : Prop :=
  ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → CrtArgs L t → H L m₀ →
    C.K (t.callEntry.withRegions (crtRd L) (crtWr L))

theorem crt_ct (C : CrtCallee) {H : Lay → Mem → Prop} (hK : KOk C H) :
    RelCT isa (Two G fun L m₀ t => (Slots L t.mem ∧ CrtArgs L t) ∧ H L m₀) (.call C.name C.code)
      (Two G fun L _ t => Slots L t.mem) :=
  two_call C.ok C.ct crtRd crtWr
    (fun _ _ _ _ _ hL a hc ⟨⟨_, ha⟩, hH⟩ => ⟨crtCall_pre hL hc ha, hK _ _ _ _ _ hL a hc ha hH⟩)
    (fun L t₁ t₂ _ _ _ _ m₁ m₂ hL hk c₁ c₂ ⟨⟨_, a₁⟩, _⟩ ⟨⟨_, a₂⟩, _⟩ => by
      have st : ∀ i < 10, stackArg (t₁.callEntry.withRegions (crtRd L) (crtWr L)) i =
          stackArg (t₂.callEntry.withRegions (crtRd L) (crtWr L)) i := fun i hi => by
        rw [ce_stackArg, ce_stackArg, c₁.sp, c₂.sp, a₁.stk i hi, a₂.stk i hi]
      refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, c₁.sp, c₂.sp], ?_, ?_⟩
      · have hl : r ∉ linkRegs := by
          simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [gpr_ce _ _ _ hl, gpr_ce _ _ _ hl]
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [a₁.x0.trans a₂.x0.symm, a₁.x1.trans a₂.x1.symm, a₁.x2.trans a₂.x2.symm,
          a₁.x3.trans a₂.x3.symm, a₁.x4.trans a₂.x4.symm, a₁.x5.trans a₂.x5.symm, a₁.x6.trans a₂.x6.symm,
          a₁.x7.trans a₂.x7.symm]
      · simp only [stackArgs_ten, st 0 (by omega_arith), st 1 (by omega_arith), st 2 (by omega_arith), st 3 (by omega_arith),
          st 4 (by omega_arith), st 5 (by omega_arith), st 6 (by omega_arith), st 7 (by omega_arith), st 8 (by omega_arith),
          st 9 (by omega_arith)]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
          a₁.x2, a₁.x3, a₂.x2, a₂.x3, c₁.n_bytes hL, c₂.n_bytes hL]
        exact hk.1)
    (fun _ hL => crt_sub hL) (fun _ hL => crt_wsub hL)
    (fun _ _ _ _ _ hL a hc ⟨⟨hs, ha⟩, hH⟩ => WP.mono (crt_call C hL hc hs ha (hK _ _ _ _ _ hL a hc ha hH))
      fun _ ⟨hc', hs', _⟩ => ⟨hc', hs'⟩)

/-- `n`'s values, as `vg_rsa_public_precompute` writes them for `n`. -/
def preVal (L : Lay) (nB : List Byte) : List (BitVec 64) :=
  match Spec.Rsa.publicPrecompute nB with
  | some ws => ws
  | none => List.replicate L.pw 0

/-- `n`'s values are in the inner frame. -/
abbrev PreW (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  Spec.Rsa.wordsAt t.mem (L.B + BitVec.ofNat 64 oPre) L.pw = preVal L (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)

theorem pcArgs_ct : RelCT isa (Two G fun L _ t => Slots L t.mem) (.block pcArgs)
    (Two G fun L _ t => Slots L t.mem ∧ PcArgs L t) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun _ _ _ _ _ hL ha hc hs => WP.mono (pcArgs_ok hL ha hc hs) fun _ ⟨hc', hs', pa, _⟩ => ⟨hc', hs', pa⟩

theorem pc_ct (v : CrtImpl) :
    RelCT isa (Two G fun L _ t => Slots L t.mem ∧ PcArgs L t) (.call v.pcName v.pc)
      (Two G fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t) :=
  two_call v.pc_ok v.pc_ct pcRd pcWr (fun _ _ _ _ _ hL _ hc ⟨_, ha⟩ => pcCall_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ m₁ m₂ hL hk c₁ c₂ ⟨_, a₁⟩ ⟨_, a₂⟩ => by
      refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, c₁.sp, c₂.sp], ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [gpr_ce _ _ _ (by decide), gpr_ce _ _ _ (by decide)]
        exacts [a₁.x0.trans a₂.x0.symm, a₁.x1.trans a₂.x1.symm, a₁.x2.trans a₂.x2.symm,
          a₁.x3.trans a₂.x3.symm, a₁.x4.trans a₂.x4.symm, a₁.x5.trans a₂.x5.symm]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
          a₁.x2, a₁.x3, a₂.x2, a₂.x3, c₁.n_bytes hL, c₂.n_bytes hL]
        exact hk.1)
    (fun _ hL => pc_sub hL) (fun _ hL => pc_wsub hL)
    (fun _ _ _ _ _ hL _ hc ⟨hs, ha⟩ => WP.mono (pc_call v hL hc hs ha) fun _ ⟨hc', hs', _, hpc⟩ => by
      refine ⟨hc', hs', ?_⟩
      simp only [PcOut, hc.n_bytes hL] at hpc
      simp only [PreW, preVal]
      split <;> rename_i h <;> simp only [h] at hpc <;> exact hpc.2)

theorem pdArgs_ct : RelCT isa (Two G fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t) (.block pdArgs)
    (Two G fun L m₀ t => Slots L t.mem ∧ PdArgs L t ∧ PreW L m₀ t) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun L _ _ _ _ hL ha hc ⟨hs, hp⟩ => WP.mono (pdArgs_ok hL ha hc hs) fun _ ⟨hc', hs', pda, _, f₃⟩ => by
      refine ⟨hc', hs', pda, ?_⟩
      have hnB := hL.nB
      have hk := hL.khi
      have d3 := slot_disj hL (d := oR3) (by decide)
      have hP16 : L.PRE.Disjoint ⟨L.B, 16⟩ :=
        Offset.disjoint_base _ (by decide) (by simp only [oPre, Lay.pw]; omega_arith)
      rw [PreW, frame_wordsAt f₃ (fun r hr => ?_) (by unfold Lay.pw; omega_arith)]
      · exact hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (by rw [Nat.mul_comm]; exact d3.1.symm)
        · exact (by rw [Nat.mul_comm]; exact hP16)

theorem pd_ct (v : CrtImpl) :
    RelCT isa (Two G fun L m₀ t => Slots L t.mem ∧ PdArgs L t ∧ PreW L m₀ t) (.call v.pdName v.pd)
      (Two G fun L _ t => Slots L t.mem) :=
  two_call v.pd_ok v.pd_ct pdRd pdWr (fun _ _ _ _ _ hL _ hc ⟨_, ha, _⟩ => pdCall_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ m₁ m₂ hL hk c₁ c₂ ⟨_, a₁, p₁⟩ ⟨_, a₂, p₂⟩ => by
      refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, c₁.sp, c₂.sp], ?_, ?_,
        ?_, ?_⟩
      · have hl : r ∉ linkRegs := by
          simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [gpr_ce _ _ _ hl, gpr_ce _ _ _ hl]
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [a₁.x0.trans a₂.x0.symm, a₁.x1.trans a₂.x1.symm, a₁.x2.trans a₂.x2.symm,
          a₁.x3.trans a₂.x3.symm, a₁.x4.trans a₂.x4.symm, a₁.x5.trans a₂.x5.symm, a₁.x6.trans a₂.x6.symm,
          a₁.x7.trans a₂.x7.symm]
      · rw [ce_stackArg, ce_stackArg, c₁.sp, c₂.sp, Nat.mul_zero, BitVec.add_zero, a₁.s0, a₂.s0]
      · rw [ce_stackArg, ce_stackArg, c₁.sp, c₂.sp, a₁.s1, a₂.s1]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
          a₁.x2, a₁.x3, a₂.x2, a₂.x3, toNat_pw hL]
        rw [p₁, p₂, hk.1]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
          a₁.x4, a₁.x5, a₂.x4, a₂.x5, c₁.e_bytes hL, c₂.e_bytes hL]
        exact hk.2)
    (fun _ hL => pd_sub hL) (fun _ hL => pd_wsub hL)
    (fun _ _ _ _ _ hL _ hc ⟨hs, ha, _⟩ => WP.mono (pd_call v hL hc hs ha) fun _ ⟨hc', hs', _⟩ => ⟨hc', hs'⟩)

/-! ## The whole function -/

theorem lay_eq {s₁ s₂ : State} (hp : chkA.pub s₁ s₂) : lay s₂ = lay s₁ := by
  obtain ⟨hr, hsp, ha, -⟩ := hp
  simp only [stackArgs_twelve, List.cons.injEq, and_true] at ha
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ha
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  simp only [lay, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hsp]

/-- Two calls whose public data agree, in the inner frame, each meeting
`chkA` but for reading also `X`, with `G` of their layout and memories. -/
def EnteredW (G : Env → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂ R₁ R₂ X, chkA.pre (s₁.withRegions R₁ s₁.wr) ∧ chkA.pre (s₂.withRegions R₂ s₂.wr) ∧
    s₁.rd = R₁ ++ X ∧ s₂.rd = R₂ ++ X ∧ chkA.pub s₁ s₂ ∧
    G ⟨layW s₁ X, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩ ∧ a = entered s₁ ∧ b = entered s₂

theorem crtArgs_ct : RelCT isa (EnteredW G) (.block crtArgs) (Two G fun L _ t => Slots L t.mem ∧ CrtArgs L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, R₁, R₂, X, h₁, h₂, x₁, x₂, hp, hG, ea, eb⟩ e₁ e₂
  subst ea eb
  have e := lay_eq hp
  have eW : layW s₂ X = layW s₁ X := by simp only [layW, e]
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp, entered_sp, e]) e₁ e₂).1
  obtain ⟨_, u₁, x₁', y₁⟩ := crtArgs_ok ((lay_ok h₁).withX X) (argsAt_entry s₁) (entered_ctxW (s := s₁) h₁ x₁)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨_, u₂, x₂', y₂⟩ := crtArgs_ok ((lay_ok h₂).withX X) (argsAt_entry s₂) (entered_ctxW (s := s₂) h₂ x₂)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁'
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂'
  have y₂' : Ctx (layW s₁ X) s₂.gpr s₂.v s₂.mem b' ∧ Slots (layW s₁ X) b'.mem ∧ CrtArgs (layW s₁ X) b' :=
    eW ▸ y₂
  have a₂ : ArgsAt (layW s₁ X) s₂.mem := eW ▸ (argsAt_entry s₂ : ArgsAt (layW s₂ X) s₂.mem)
  refine ⟨ht, ⟨layW s₁ X, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, hG, (lay_ok h₁).withX X,
    argsAt_entry s₁, a₂, ?_, y₁.1, y₂'.1, y₁.2, y₂'.2⟩
  obtain ⟨hr, -, -, hn, he⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨-, -, r2, r3, r4, r5, -, -⟩ := hr
  refine ⟨?_, ?_⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    exact hn.trans (by rw [← r2, ← r3])
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    exact he.trans (by rw [← r4, ← r5])

/-- The frames, the CRT `C` and the check, whatever `stage` writes `n`'s
values with: constant time for calls that agree on `pub` and enter as
`EnteredW`, given that `G` gives the CRT's calls `C.K`. -/
theorem codeWith_constantTime (C : CrtCallee) (v : CrtImpl) (stage : Prog isa) {H : Lay → Mem → Prop}
    (hGH : ∀ e, G e → H e.L e.m₁ ∧ H e.L e.m₂) (hK : KOk C H)
    (hstage : RelCT isa (Two G fun L _ t => Slots L t.mem ∧ PcArgs L t) stage
      (Two G fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t))
    {pre : State → Prop} {pub : State → State → Prop}
    (hsp : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → s₁.sp = s₂.sp)
    (hent : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → EnteredW G (entered s₁) (entered s₂)) :
    ConstantTime isa pre pub (codeWith C v stage) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => hsp _ _ h.1 h.2.1 h.2.2)
    (RelCT.alloc (R := fun _ _ => True) ?_))
  show RelCT isa _ (seqs _) _
  rw [show seqs ([.block crtArgs, .call C.name C.code] ++ checkWith stage v.pdName v.pd) =
    .seq (.block crtArgs) (.seq (.call C.name C.code) (seqs (checkWith stage v.pdName v.pd))) from rfl,
    checkWith_eq]
  have hA := crtArgs_ct (G := G).mono (fun _ _ h => h) fun _ _ ⟨e, hG, hL, a₁, a₂, hk, c₁, c₂, f₁, f₂⟩ =>
    (⟨e, hG, hL, a₁, a₂, hk, c₁, c₂, ⟨f₁, (hGH e hG).1⟩, ⟨f₂, (hGH e hG).2⟩⟩ :
      Two G (fun L m₀ t => (Slots L t.mem ∧ CrtArgs L t) ∧ H L m₀) _ _)
  refine (hA.seq ((crt_ct C hK).seq (pcArgs_ct.seq (hstage.seq (pdArgs_ct.seq
    ((pd_ct v).seq tail_ct)))))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact hent s₁ s₂ h₁ h₂ hp

theorem code_constantTime (v : CrtImpl) : ConstantTime isa chkA.pre chkA.pub (privCodeOf v) :=
  codeWith_constantTime (G := fun _ => True) v.callee v _ (H := fun _ _ => True) (fun _ _ => ⟨trivial, trivial⟩)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) (pc_ct v) (fun _ _ _ _ hp => hp.2.1)
    fun s₁ s₂ h₁ h₂ hp => ⟨s₁, s₂, s₁.rd, s₂.rd, [], h₁, h₂, (List.append_nil _).symm,
      (List.append_nil _).symm, hp, trivial, rfl, rfl⟩

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: the shared contract

`vg_rsa_private_checked`, calling the implementation `v` of
`vg_rsa_private_crt` and its public operation, is verified against
`Proof.Rsa.privateCheckedContract` for the `stackBytes` bytes of stack its
frames use (`code_verified`); its frames nest `stackBytes / 16` units deep
(`privCode_depth`), which its callers need.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The name of `vg_rsa_private_checked` calling `v`. -/
def privName (v : CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix

/-- Its code. -/
abbrev privCode (v : CrtImpl) : Prog isa := privCodeOf v

theorem code_verified (v : CrtImpl) :
    Verified AArch64.target (privCode v) (Proof.Rsa.privateCheckedContract AArch64.abi stackBytes) :=
  Verified.of_correct (fun s h => code_correct v s h) (code_constantTime v) private_checked_implies

/-- Code without frames uses no stack. -/
theorem aarch64Depth_of_noFrames : ∀ {c : Prog isa}, c.noFrames = true → c.aarch64Depth = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h.1, aarch64Depth_of_noFrames h.2, Nat.max_self]
  | .ite _ a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h.1, aarch64Depth_of_noFrames h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h]
  | .call _ b, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h]
  | .frame .., h => by simp [Code.noFrames] at h
  | .icall _ _ b n, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h.1, aarch64Depth_of_noFrames h.2, Nat.max_self]

/-- Its frames: `x30`'s, and the 3232 bytes of the inner frame. -/
theorem privCode_depth (v : CrtImpl) : (privCode v).aarch64Depth = stackBytes / 16 := by
  simp only [privCode, privCodeOf, code, body, check, checkWith, tail, seqs, List.cons_append, List.nil_append,
    Code.aarch64Depth, aarch64Depth_of_noFrames v.noFrames, aarch64Depth_of_noFrames v.pcNoFrames,
    aarch64Depth_of_noFrames v.pdNoFrames, cmpLoop, releaseLoop, Instr.frameUnits, frameBytes, stackBytes]
  decide

/-- `vg_rsa_private_checked` never touches PSTATE.DIT, its callees not either. -/
theorem privCode_noDit (v : CrtImpl) : (privCode v).all (fun i => !i.touchesDit) = true := by
  simp only [privCode, privCodeOf, code, body, check, checkWith, tail, seqs, List.cons_append, List.nil_append,
    Code.all, v.noDit, v.pcNoDit, v.pdNoDit, cmpLoop, releaseLoop, Bool.true_and]
  decide

end VG.Proof.Rsa.AArch64
