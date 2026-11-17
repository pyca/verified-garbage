module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.PrivCheck

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
