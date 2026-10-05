import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlKem.Arm.Ntt
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.Arm.Sample
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Reduce`. -/
section

/-!
# ML-KEM on 32-bit ARM: Barrett reduction, the tables and the saved registers

`reduce` computes `x mod q` of any `x < 2²⁵` (`red_toNat`), through
`barrett32` (`Proof/MlKem/Arith.lean`); `table` stores a table of 128 `u32`s
(`table_ok`), and the tables of the code are those of the standard
(`zetaTable_eq`, `gammaTable_eq`); `saveRegs` and `restoreRegs` keep our
caller's `r4`–`r11` in memory.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-! ## Barrett reduction -/

/-- What `barrett d t c` leaves in `d`, with `c` in `c`. -/
def bar (c x : BitVec 32) : BitVec 32 :=
  x - (x >>> 11 * c) >>> 18 - (x >>> 11 * c) >>> 18 <<< 8 - (x >>> 11 * c) >>> 18 <<< 10 -
    (x >>> 11 * c) >>> 18 <<< 11

/-- What `reduce d t c` leaves in `d`. -/
def red (c x : BitVec 32) : BitVec 32 := fixq (VG.Proof.MlKem.Arm.bar c x - 3328 - 1)

/-- The constant of `consts`. -/
def C : BitVec 32 := 161270

theorem consts_val : ((0x2 : BitVec 16) ++ ((0x75F6 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = VG.Proof.MlKem.Arm.C := by
  decide

theorem bar_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (VG.Proof.MlKem.Arm.bar VG.Proof.MlKem.Arm.C x).toNat = barrett32 x.toNat := by
  obtain ⟨b1, b2⟩ := barrett32_bounds hx
  have hT : ((x >>> 11 * VG.Proof.MlKem.Arm.C) >>> 18).toNat = barrett32Quot x.toNat := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, show C.toNat = 161270 from rfl, Nat.mod_eq_of_lt b1]
    rfl
  unfold VG.Proof.MlKem.Arm.bar barrett32
  generalize (x >>> 11 * VG.Proof.MlKem.Arm.C) >>> 18 = T at hT
  rw [VG.Proof.MlKem.q_eq] at b2 ⊢
  bv_omega

theorem red_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C x).toNat = x.toNat % VG.Spec.MlKem.q := by
  have h1 := barrett32_lt hx
  unfold VG.Proof.MlKem.Arm.red
  rw [fixq_subq (by rw [VG.Proof.MlKem.Arm.bar_toNat hx]; exact h1), VG.Proof.MlKem.Arm.bar_toNat hx, ← reduce32 hx, condSub_eq h1]

theorem red_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C x).toNat < VG.Spec.MlKem.q := by
  rw [VG.Proof.MlKem.Arm.red_toNat hx]; exact Nat.mod_lt _ (by decide)

/-- A product of reduced values, reduced. -/
theorem red_mul {a b : Zq} :
    VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val) = BitVec.ofNat 32 (a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hp : (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val).toNat = a.val * b.val := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a.val) (by omega),
      Nat.mod_eq_of_lt (a := b.val) (by omega)]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 ha hb; omega)
  refine ofNat_val_eq ?_
  rw [VG.Proof.MlKem.Arm.red_toNat (by rw [hp]; have := mul_lt_q2 ha hb; omega), hp, val_mul]

/-! ## Tables -/

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < VG.Spec.MlKem.q := by decide +kernel

theorem gammaTable_lt : ∀ k < 128, gammaTable.getD k 0 < VG.Spec.MlKem.q := by decide +kernel

/-- An entry of a table, as `movw` builds it. -/
theorem movw_val {v : Nat} (hv : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega)]

/-- After the first `k` entries of a table at `b`. -/
structure TabInv (T : List Nat) (b : Reg) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b), 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * j)) 32 =
    BitVec.ofNat 32 (T.getD j 0)

theorem tab_step {s : State} {b : Reg} {B : BitVec 32} {k : Nat} (hk : 4 * k < 4096) (hb : s.gpr b = B)
    (hin : InRegions s.wr (State.addr (B + BitVec.ofNat 32 (4 * k))) 4) (v : BitVec 16) (hbr : b ≠ .r12) :
    WP isa (.block [.movw .r12 v, .str .r12 b (4 * k)]) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (State.addr (B + BitVec.ofNat 32 (4 * k))) (v.setWidth 32) := by
  have ho : 4 * k < 4096 := hk
  run_block [hb, hbr, hin, ho, ite_false, implies_true]
  exact ⟨fun r hr => ite_eq_right hr, trivial⟩

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {b : Reg} (hb : b ≠ .r12)
    {s₀ : State} (hfit : (s₀.gpr b).toNat + 512 ≤ 2 ^ 32)
    (hwr : ∀ k < 128, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (VG.Proof.MlKem.Arm.TabInv T b s₀ 128) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.MlKem.Arm.TabInv T b s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s₀.gpr b + BitVec.ofNat 32 (4 * k)) = State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  refine WP.mono (VG.Proof.MlKem.Arm.tab_step (k := k) (by omega) (h.gpr b hb) (by rw [ea, h.wr]; exact hwr k hk) _ hb)
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r hr => (g r hr).trans (h.gpr r hr), rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, ?_, fun j hj => ?_⟩
  · rw [m, ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · rw [m, ea, VG.Proof.MlKem.Arm.movw_val (hT k hk)]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
      exact h.tab j (by omega)

/-! ## Regions at offsets from a base -/

theorem region_sub_off {S : Addr} {o n len : Nat} (h : o + n ≤ len) :
    Region.Sub ⟨S + BitVec.ofNat 64 o, n⟩ ⟨S, len⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem region_disj_off {S : Addr} {o₁ n₁ o₂ n₂ L : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ + n₁ ≤ L) (h₂ : o₂ + n₂ ≤ L) (hS : S.toNat + L ≤ 2 ^ 64) :
    Region.Disjoint ⟨S + BitVec.ofNat 64 o₁, n₁⟩ ⟨S + BitVec.ofNat 64 o₂, n₂⟩ := by
  intro a ha hb
  simp only [Region.Contains] at ha hb
  bv_omega

theorem add_ofNat_zero (S : Addr) : S + BitVec.ofNat 64 0 = S := by simp

theorem add_ofNat_add (S : Addr) (a b : Nat) :
    S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ptr_add_add32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem addr_toNat64 (a : BitVec 32) : (State.addr a).toNat + 2 ^ 32 ≤ 2 ^ 64 := by
  rw [VG.Proof.MlKem.Arm.addr_toNat]; have := a.isLt; omega

/-- A pointer to `L ≤ 2³²` bytes, as a 64-bit address, does not wrap around. -/
theorem addr_fit (a : BitVec 32) {L : Nat} (hL : L ≤ 2 ^ 32) : (State.addr a).toNat + L ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add_left hL _) (VG.Proof.MlKem.Arm.addr_toNat64 a)

theorem fit_le {a : BitVec 32} {k L : Nat} (hk : k ≤ L) (h : a.toNat + L ≤ 2 ^ 32) : a.toNat + k ≤ 2 ^ 32 :=
  Nat.le_trans (Nat.add_le_add_left hk _) h

/-! ## Saved registers -/

theorem savedRegs_nodup : ∀ i < 8, ∀ j < 8, savedRegs.getD i .r4 = savedRegs.getD j .r4 → i = j := by
  decide

theorem savedRegs_mem : ∀ i < 8, savedRegs.getD i .r4 ∈ savedRegs := by decide

theorem savedRegs_ne_lr : ∀ i < 8, savedRegs.getD i .r4 ≠ .lr := by decide

/-- The registers `g` saved at `A`. -/
def Saved (m : Mem) (A : Addr) (g : Reg → BitVec 32) : Prop :=
  ∀ i < 8, m.readW (A + BitVec.ofNat 64 (4 * i)) 32 = g (savedRegs.getD i .r4)

/-- After saving the first `k` registers at `A = b + off`. -/
structure SaveInv (b : Reg) (off : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b) + BitVec.ofNat 64 off, 32⟩] s₀.mem s.mem
  saved : ∀ i < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 32 =
    s₀.gpr (savedRegs.getD i .r4)

theorem saveRegs_ok (b : Reg) {off : Nat} (ho : off + 28 < 4096) {s₀ : State}
    (hfit : (s₀.gpr b).toNat + (off + 32) ≤ 2 ^ 32)
    (hwr : ∀ i < 8, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (saveRegs b off)) s₀ (VG.Proof.MlKem.Arm.SaveInv b off s₀ 8) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.MlKem.Arm.SaveInv b off s₀) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (off + 4 * k)) =
      State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) := by
    rw [h.gpr, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_str (by omega) (by rw [ea, h.wr]; exact hwr k hk), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · rw [ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ _ = _
    rw [ea, h.gpr]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
      exact h.saved j (by omega)

/-- After loading the first `k` registers from `A = b + off`. -/
structure RestoreInv (g : Reg → BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  other : ∀ r, r ∉ savedRegs → s.gpr r = s₀.gpr r
  loaded : ∀ i < k, s.gpr (savedRegs.getD i .r4) = g (savedRegs.getD i .r4)

theorem restoreRegs_ok (b : Reg) (hb : b ∉ savedRegs) {off : Nat} (ho : off + 28 < 4096) {s₀ : State}
    (hfit : (s₀.gpr b).toNat + (off + 32) ≤ 2 ^ 32) {g : Reg → BitVec 32}
    (hs : VG.Proof.MlKem.Arm.Saved s₀.mem (State.addr (s₀.gpr b) + BitVec.ofNat 64 off) g)
    (hrd : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr)
      (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (restoreRegs b off)) s₀ (VG.Proof.MlKem.Arm.RestoreInv g s₀ 8) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.MlKem.Arm.RestoreInv g s₀) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (off + 4 * k)) =
      State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) := by
    rw [h.other b hb, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr (by omega) (by rw [ea, h.rd, h.wr]; exact hrd k hk), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, h.mem, h.rd, h.wr, h.sp, fun r hr => ?_, fun j hj => ?_⟩
  · show (s.setReg _ _).gpr r = _
    simp only [State.setReg]
    rw [ite_eq_right (fun (e : r = savedRegs.getD k .r4) => hr (e ▸ VG.Proof.MlKem.Arm.savedRegs_mem k hk)), h.other r hr]
  · show (s.setReg _ _).gpr _ = _
    simp only [State.setReg]
    by_cases e : j = k
    · subst e; rw [ite_eq_left rfl, ea, h.mem]; exact hs j hk
    · rw [ite_eq_right (fun e' => e (VG.Proof.MlKem.Arm.savedRegs_nodup j (by omega) k hk e'))]
      exact h.loaded j (by omega)

/-- The callee-saved registers, restored. -/
theorem preserved_of_restore {g : Reg → BitVec 32} {s₀ s : State} (h : VG.Proof.MlKem.Arm.RestoreInv g s₀ 8 s)
    (hlr : s₀.gpr .lr = g .lr) : ∀ r ∈ preserved, s.gpr r = g r := by
  have : ∀ r ∈ preserved, r = .lr ∨ ∃ i < 8, savedRegs.getD i .r4 = r := by decide
  intro r hr
  rcases this r hr with rfl | ⟨i, hi, rfl⟩
  · rw [h.other .lr (by decide), hlr]
  · exact h.loaded i hi

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Keccak`. -/
section

/-!
# ML-KEM on 32-bit ARM: calling the SHA-3 sponge

The calls of `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` in
their frames (`absorbCall`, `padCall`, `squeezeCall`), from the callees'
proofs (`WP.callCalls`, with the per-target contracts `Proof.Sha3.absorbArm`,
…): what each needs of the state it is called from (`AbsorbArgs`, …), and what
holds when it returns; and that two runs that call it with the same arguments
leak the same trace (`absorb_ct`, …, by `RelCT.frame` and `RelCT.call`). The
frame stores the stack arguments in the 8 bytes below the stack pointer, which
the callers' contracts reserve (`below`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (Repr stateAt squeezeFrom rates)

/-- The `n` bytes at the 32-bit pointer `b`. -/
abbrev regA (b : BitVec 32) (n : Nat) : Region := ⟨State.addr b, n⟩

/-- The `n` bytes below the stack pointer. -/
abbrev below (s : State) (n : Nat) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 n, n⟩

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `lr`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem rates_lt {rate : Nat} (h : rate ∈ rates) : rate ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem absorb_noFrames : Impl.Sha3.Arm.Stream.absorb.noFrames = true := by decide +kernel
theorem pad_noFrames : Impl.Sha3.Arm.Stream.pad.noFrames = true := by decide +kernel
theorem squeeze_noFrames : Impl.Sha3.Arm.Stream.squeeze.noFrames = true := by decide +kernel

/-! ## Frames -/

theorem addr_sub {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    State.addr (sp - BitVec.ofNat 32 n) = State.addr sp - BitVec.ofNat 64 n := by
  have := sp.isLt
  simp only [State.addr]; bv_omega

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 := rfl

theorem e4 : BitVec.ofNat 32 (4 * [Reg.lr].length) = BitVec.ofNat 32 4 := rfl

/-- A frame of two words: the stack pointer, the stack arguments and the
memory. -/
theorem push2_sp (s : State) : (pushed [.r12, .lr] s).sp = s.sp - BitVec.ofNat 32 8 := by
  rw [pushed_sp, VG.Proof.MlKem.Arm.e8]

theorem push2_mem {s : State} (hsp : 8 ≤ s.sp.toNat) : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - BitVec.ofNat 64 8) (s.gpr .r12)).writeW
      (State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [VG.Proof.MlKem.Arm.e8]
  show (s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 8)) (s.gpr .r12)).writeW
    (State.addr (s.sp - BitVec.ofNat 32 8 + 4)) (s.gpr .lr) = _
  rw [VG.Proof.MlKem.Arm.addr_sub hsp, show s.sp - BitVec.ofNat 32 8 + 4 = s.sp - BitVec.ofNat 32 8 + BitVec.ofNat 32 4 from rfl,
    addr_add (by bv_omega), VG.Proof.MlKem.Arm.addr_sub hsp]

theorem push2_arg {s t : State} (hsp : 8 ≤ s.sp.toNat) (ht : t.sp = s.sp - BitVec.ofNat 32 8)
    (hm : t.mem = (pushed [.r12, .lr] s).mem) :
    stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 8 ∧ stackArg t 0 = s.gpr .r12 ∧
      stackArg t 1 = s.gpr .lr := by
  have a0 : stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 8 := by
    unfold stackArgAddr
    rw [ht, addr_add (by bv_omega), VG.Proof.MlKem.Arm.addr_sub hsp]; simp
  have a1 : stackArgAddr t 1 = State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4 := by
    unfold stackArgAddr; rw [ht, show 4 * 1 = 4 from rfl, addr_add (by bv_omega), VG.Proof.MlKem.Arm.addr_sub hsp]
  refine ⟨a0, ?_, ?_⟩
  · rw [stackArg, a0, hm, VG.Proof.MlKem.Arm.push2_mem hsp, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
      Mem.readW_writeW_self32]
  · rw [stackArg, a1, hm, VG.Proof.MlKem.Arm.push2_mem hsp, Mem.readW_writeW_self32]

theorem push2_frame {s : State} (hsp : 8 ≤ s.sp.toNat) : Frame [VG.Proof.MlKem.Arm.below s 8] s.mem (pushed [.r12, .lr] s).mem := by
  rw [VG.Proof.MlKem.Arm.push2_mem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [show State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4 - (State.addr s.sp - BitVec.ofNat 64 8) =
      BitVec.ofNat 64 4 by bv_omega]; decide

/-- The stack arguments are the frame: the regions a callee is given within
those of the frame's state. -/
theorem cov_push {s : State} (hsp : 8 ≤ s.sp.toNat) {rs ws : List Region} {rr : Region} (hr : rr = VG.Proof.MlKem.Arm.below s 8)
    (hc : Covers rs (s.rd ++ s.wr)) (hw : Covers ws s.wr) (rs' : List Region) (hrs : rs' = rs ++ [rr]) :
    Covers (rs' ++ ws) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  subst hrs hr
  intro x n ⟨r, hr, hc'⟩
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | rfl) | hr
  · obtain ⟨r', hr', hc''⟩ := hc x n ⟨r, hr, hc'⟩
    refine ⟨r', ?_, hc''⟩
    rw [pushed_rd, pushed_wr]
    rcases List.mem_append.mp hr' with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rw [VG.Proof.MlKem.Arm.e8, VG.Proof.MlKem.Arm.addr_sub hsp]; exact hc'
  · obtain ⟨r', hr', hc''⟩ := hw x n ⟨r, hr, hc'⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc''⟩

/-! ## `vg_keccak_absorb` -/

/-- What a call of `vg_keccak_absorb` in its frame needs: the state at `st`,
the rate, the position, the data at `data`, its length and the working
space at `scr` in `r0`–`r3`, `r12` and `lr`; the buffers apart, and apart
from the 8 bytes below the stack pointer. -/
structure AbsorbArgs (s : State) (st scr data : BitVec 32) (rate pos len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 pos
  r3 : s.gpr .r3 = data
  r12 : s.gpr .r12 = BitVec.ofNat 32 len
  lr : s.gpr .lr = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  hlen : len < 2 ^ 32
  sp : 8 ≤ s.sp.toNat
  fst : st.toNat + 200 ≤ 2 ^ 32
  fdata : data.toNat + len ≤ 2 ^ 32
  fscr : scr.toNat + 640 ≤ 2 ^ 32
  d_st_scr : (VG.Proof.MlKem.Arm.regA st 200).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  d_data_st : (VG.Proof.MlKem.Arm.regA data len).Disjoint (VG.Proof.MlKem.Arm.regA st 200)
  d_data_scr : (VG.Proof.MlKem.Arm.regA data len).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  b_st : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA st 200)
  b_scr : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  b_data : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA data len)
  cw : Covers [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] s.wr
  cr : Covers [VG.Proof.MlKem.Arm.regA data len] (s.rd ++ s.wr)

/-- The state `vg_keccak_absorb` runs from, with the permissions it is given. -/
abbrev absorbView (s : State) (st scr data : BitVec 32) (len : Nat) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions [VG.Proof.MlKem.Arm.regA data len, VG.Proof.MlKem.Arm.below s 8] [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640]

theorem view_gpr (rs : List Reg) (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    ((pushed rs s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem absorb_pre {s : State} {st scr data : BitVec 32} {rate pos len : Nat}
    (h : VG.Proof.MlKem.Arm.AbsorbArgs s st scr data rate pos len) : Proof.Sha3.absorbArm.pre (VG.Proof.MlKem.Arm.absorbView s st scr data len) := by
  obtain ⟨a0, a1, a2⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.absorbView s st scr data len) h.sp (VG.Proof.MlKem.Arm.push2_sp s) rfl
  have hr := VG.Proof.MlKem.Arm.rates_lt h.hrate
  have hp := h.hpos
  simp only [Proof.Sha3.absorbArm, VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, a0, a1, a2, h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, VG.Proof.MlKem.Arm.toNat_ofNat32 h.hlen,
    VG.Proof.MlKem.Arm.toNat_ofNat32 (show rate < 2 ^ 32 by omega), VG.Proof.MlKem.Arm.toNat_ofNat32 (show pos < 2 ^ 32 by omega),
    State.callEntry_sp, VG.Proof.MlKem.Arm.push2_sp]
  refine ⟨trivial, trivial, h.d_st_scr, h.d_data_st, h.d_data_scr, h.b_st, h.b_scr, h.fst, h.fdata, h.fscr, ?_,
    h.hrate, h.hpos⟩
  have := h.sp; have := s.sp.isLt; bv_omega

theorem absorb_ok {s : State} {st scr data : BitVec 32} {rate pos len : Nat}
    (h : VG.Proof.MlKem.Arm.AbsorbArgs s st scr data rate pos len) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.Arm.Kept [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640, VG.Proof.MlKem.Arm.below s 8] s s' →
      (∀ msg, Repr s.mem (State.addr st) rate msg → pos = msg.length % rate →
        Repr s'.mem (State.addr st) rate (msg ++ Spec.Sha3.bytesAt s.mem (State.addr data) len)) →
      (s'.gpr .r0).toNat = (pos + len) % rate → Q s') :
    WP isa absorbCall s Q := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.sp) (by decide) ?_
  obtain ⟨a0, a1, a2⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.absorbView s st scr data len) h.sp (VG.Proof.MlKem.Arm.push2_sp s) rfl
  have hr := VG.Proof.MlKem.Arm.rates_lt h.hrate
  have hp := h.hpos
  have hl := h.hlen
  have fA := VG.Proof.MlKem.Arm.push2_frame h.sp
  refine WP.callCalls (k := Proof.Sha3.absorbArm) Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1
    (VG.Proof.MlKem.Arm.absorb_pre h) (VG.Proof.MlKem.Arm.cov_push h.sp rfl h.cr h.cw _ rfl)
    (fun x n hi => by
      obtain ⟨r', hr', hc'⟩ := h.cw x n hi
      exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩) ?_ VG.Proof.MlKem.Arm.absorb_noFrames
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  simp only [Proof.Sha3.absorbArm, VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_mem, State.withRegions_gpr,
    a1, h.r0, h.r1, h.r2, h.r3, h.r12, VG.Proof.MlKem.Arm.toNat_ofNat32 h.hlen, VG.Proof.MlKem.Arm.toNat_ofNat32 (show rate < 2 ^ 32 by omega),
    VG.Proof.MlKem.Arm.toNat_ofNat32 (show pos < 2 ^ 32 by omega), State.callEntry_mem] at hpost
  have hst : ∀ r ∈ [VG.Proof.MlKem.Arm.below s 8], (VG.Proof.MlKem.Arm.regA st 200).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_st.symm
  have hdat : ∀ r ∈ [VG.Proof.MlKem.Arm.below s 8], (VG.Proof.MlKem.Arm.regA data len).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_data.symm
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ (fun msg hm hp => ?_) ?_
  · have hr12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr12, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, VG.Proof.MlKem.Arm.push2_sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]
    have e := hpost.1 msg (by
      unfold Spec.Sha3.Repr at hm ⊢
      rw [Proof.Sha3.stateAt_congr (bytes_frame fA hst (by decide))]; exact hm) hp
    rwa [bytesAt_frame fA hdat (by omega)] at e
  · rw [popped_gpr (by decide), hpost.2]

theorem push_eq {rs : List Reg} {s a : State} (h : isa.push (.push rs) s = some a) : a = pushed rs s := by
  simp only [isa, push] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem absorb_ct {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∃ st scr data rate pos len,
      VG.Proof.MlKem.Arm.AbsorbArgs s₁ st scr data rate pos len ∧ VG.Proof.MlKem.Arm.AbsorbArgs s₂ st scr data rate pos len) :
    RelCT isa P absorbCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP s₁ s₂ h).1) ?_
  refine RelCT.mono (P := fun a b => ∃ x : BitVec 32 × BitVec 32 × BitVec 32 × Nat × Nat × Nat × BitVec 32,
      ∃ s₁ s₂, s₁.sp = x.2.2.2.2.2.2 ∧ s₂.sp = x.2.2.2.2.2.2 ∧
        VG.Proof.MlKem.Arm.AbsorbArgs s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        VG.Proof.MlKem.Arm.AbsorbArgs s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        a = pushed [.r12, .lr] s₁ ∧ b = pushed [.r12, .lr] s₂) ?_ ?_ (fun _ _ h => h)
  · refine RelCT.exists_ fun ⟨st, scr, data, rate, pos, len, sp⟩ => ?_
    refine RelCT.call (k := Proof.Sha3.absorbArm) Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1
      Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1
      [VG.Proof.MlKem.Arm.regA data len, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩] [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] ?_
    rintro a b ⟨s₁, s₂, e₁, e₂, h₁, h₂, rfl, rfl⟩
    dsimp only at e₁ e₂ h₁ h₂
    have v₁ : (pushed [.r12, .lr] s₁).callEntry.withRegions [VG.Proof.MlKem.Arm.regA data len, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] = VG.Proof.MlKem.Arm.absorbView s₁ st scr data len := by simp only [VG.Proof.MlKem.Arm.absorbView, VG.Proof.MlKem.Arm.below, e₁]
    have v₂ : (pushed [.r12, .lr] s₂).callEntry.withRegions [VG.Proof.MlKem.Arm.regA data len, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] = VG.Proof.MlKem.Arm.absorbView s₂ st scr data len := by simp only [VG.Proof.MlKem.Arm.absorbView, VG.Proof.MlKem.Arm.below, e₂]
    rw [v₁, v₂]
    obtain ⟨a₀, a₁, a₂⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.absorbView s₁ st scr data len) h₁.sp (VG.Proof.MlKem.Arm.push2_sp s₁) rfl
    obtain ⟨b₀, b₁, b₂⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.absorbView s₂ st scr data len) h₂.sp (VG.Proof.MlKem.Arm.push2_sp s₂) rfl
    refine ⟨VG.Proof.MlKem.Arm.absorb_pre h₁, VG.Proof.MlKem.Arm.absorb_pre h₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlKem.Arm.push2_sp, e₁, e₂]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r0, h₂.r0]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r1, h₂.r1]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r2, h₂.r2]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r3, h₂.r3]
    · rw [a₁, b₁, h₁.r12, h₂.r12]
    · rw [a₂, b₂, h₁.lr, h₂.lr]
    · exact VG.Proof.MlKem.Arm.cov_push h₁.sp (by simp only [VG.Proof.MlKem.Arm.below, e₁]) h₁.cr h₁.cw _ rfl
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₁.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
    · exact VG.Proof.MlKem.Arm.cov_push h₂.sp (by simp only [VG.Proof.MlKem.Arm.below, e₂]) h₂.cr h₂.cw _ rfl
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₂.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · rintro a b ⟨s₁, s₂, hp, pa, pb⟩
    obtain ⟨hsp, st, scr, data, rate, pos, len, h₁, h₂⟩ := hP s₁ s₂ hp
    exact ⟨⟨st, scr, data, rate, pos, len, s₁.sp⟩, s₁, s₂, rfl, hsp.symm, h₁, h₂, VG.Proof.MlKem.Arm.push_eq pa, VG.Proof.MlKem.Arm.push_eq pb⟩

/-! ## `vg_keccak_pad` -/

theorem push1_sp (s : State) : (pushed [.lr] s).sp = s.sp - BitVec.ofNat 32 4 := by
  rw [pushed_sp, VG.Proof.MlKem.Arm.e4]

theorem push1_mem {s : State} (hsp : 8 ≤ s.sp.toNat) : (pushed [.lr] s).mem =
    s.mem.writeW (State.addr s.sp - BitVec.ofNat 64 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.lr].length)) [s.gpr .lr] = _
  rw [VG.Proof.MlKem.Arm.e4]
  show s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 4)) (s.gpr .lr) = _
  rw [VG.Proof.MlKem.Arm.addr_sub (by omega)]

theorem push1_arg {s t : State} (hsp : 8 ≤ s.sp.toNat) (ht : t.sp = s.sp - BitVec.ofNat 32 4)
    (hm : t.mem = (pushed [.lr] s).mem) :
    stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 4 ∧ stackArg t 0 = s.gpr .lr := by
  have a0 : stackArgAddr t 0 = State.addr s.sp - BitVec.ofNat 64 4 := by
    unfold stackArgAddr
    rw [ht, addr_add (by bv_omega), VG.Proof.MlKem.Arm.addr_sub (by omega)]; simp
  refine ⟨a0, ?_⟩
  rw [stackArg, a0, hm, VG.Proof.MlKem.Arm.push1_mem hsp, Mem.readW_writeW_self32]

theorem push1_frame {s : State} (hsp : 8 ≤ s.sp.toNat) : Frame [VG.Proof.MlKem.Arm.below s 8] s.mem (pushed [.lr] s).mem := by
  rw [VG.Proof.MlKem.Arm.push1_mem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains]
  rw [show State.addr s.sp - BitVec.ofNat 64 4 - (State.addr s.sp - BitVec.ofNat 64 8) = BitVec.ofNat 64 4 by
    bv_omega]; decide

theorem below4_sub (s : State) : Region.Sub (VG.Proof.MlKem.Arm.below s 4) (VG.Proof.MlKem.Arm.below s 8) := by
  intro a ha
  have := s.sp.isLt
  have e : (State.addr s.sp).toNat = s.sp.toNat := addr_toNat _
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem cov_push1 {s : State} (hsp : 8 ≤ s.sp.toNat) {ws : List Region} (hw : Covers ws s.wr) :
    Covers ([VG.Proof.MlKem.Arm.below s 4] ++ ws) ((pushed [.lr] s).rd ++ (pushed [.lr] s).wr) := by
  intro x n ⟨r, hr, hc'⟩
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | hr
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rw [VG.Proof.MlKem.Arm.e4, VG.Proof.MlKem.Arm.addr_sub (by omega)]; exact hc'
  · obtain ⟨r', hr', hc''⟩ := hw x n ⟨r, hr, hc'⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc''⟩

/-- What a call of `vg_keccak_pad` in its frame needs. -/
structure PadArgs (s : State) (st scr : BitVec 32) (rate pos : Nat) (suffix : BitVec 32) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 pos
  r3 : s.gpr .r3 = suffix
  lr : s.gpr .lr = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  sp : 8 ≤ s.sp.toNat
  fst : st.toNat + 200 ≤ 2 ^ 32
  fscr : scr.toNat + 640 ≤ 2 ^ 32
  d_st_scr : (VG.Proof.MlKem.Arm.regA st 200).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  b_st : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA st 200)
  b_scr : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  cw : Covers [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] s.wr

abbrev padView (s : State) (st scr : BitVec 32) : State :=
  (pushed [.lr] s).callEntry.withRegions [VG.Proof.MlKem.Arm.below s 4] [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640]

theorem pad_pre {s : State} {st scr : BitVec 32} {rate pos : Nat} {suffix : BitVec 32}
    (h : VG.Proof.MlKem.Arm.PadArgs s st scr rate pos suffix) : Proof.Sha3.padArm.pre (VG.Proof.MlKem.Arm.padView s st scr) := by
  obtain ⟨a0, a1⟩ := VG.Proof.MlKem.Arm.push1_arg (t := VG.Proof.MlKem.Arm.padView s st scr) h.sp (VG.Proof.MlKem.Arm.push1_sp s) rfl
  have hr := VG.Proof.MlKem.Arm.rates_lt h.hrate
  have hp := h.hpos
  have hs := VG.Proof.MlKem.Arm.below4_sub s
  simp only [Proof.Sha3.padArm, VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, a0, a1, h.r0, h.r1, h.r2, h.lr,
    VG.Proof.MlKem.Arm.toNat_ofNat32 (show rate < 2 ^ 32 by omega), VG.Proof.MlKem.Arm.toNat_ofNat32 (show pos < 2 ^ 32 by omega),
    State.callEntry_sp, VG.Proof.MlKem.Arm.push1_sp]
  refine ⟨trivial, trivial, h.d_st_scr, h.b_st.sub_left hs, h.b_scr.sub_left hs, h.fst, h.fscr, ?_, h.hrate,
    h.hpos⟩
  have := h.sp; have := s.sp.isLt; bv_omega

theorem pad_ok {s : State} {st scr : BitVec 32} {rate pos : Nat} {suffix : BitVec 32}
    (h : VG.Proof.MlKem.Arm.PadArgs s st scr rate pos suffix) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.Arm.Kept [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640, VG.Proof.MlKem.Arm.below s 8] s s' →
      (∀ msg, Repr s.mem (State.addr st) rate msg → pos = msg.length % rate →
        stateAt s'.mem (State.addr st) = Spec.Sha3.absorb rate (Spec.Sha3.pad rate (suffix.setWidth 8) msg)) →
      Q s') :
    WP isa padCall s Q := by
  refine WP.frame (rs := [.lr]) (r := .r12) rfl (by simpa using (show 4 ≤ s.sp.toNat by have := h.sp; omega))
    (by decide) ?_
  have hr := VG.Proof.MlKem.Arm.rates_lt h.hrate
  have hp := h.hpos
  have fA := VG.Proof.MlKem.Arm.push1_frame h.sp
  refine WP.callCalls (k := Proof.Sha3.padArm) Proof.Sha3.Arm.Stream.Pad.pad_verified.1
    (VG.Proof.MlKem.Arm.pad_pre h) (VG.Proof.MlKem.Arm.cov_push1 h.sp h.cw)
    (fun x n hi => by
      obtain ⟨r', hr', hc'⟩ := h.cw x n hi
      exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩) ?_ VG.Proof.MlKem.Arm.pad_noFrames
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  simp only [Proof.Sha3.padArm, VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_mem,
    h.r0, h.r1, h.r2, h.r3, VG.Proof.MlKem.Arm.toNat_ofNat32 (show rate < 2 ^ 32 by omega),
    VG.Proof.MlKem.Arm.toNat_ofNat32 (show pos < 2 ^ 32 by omega), State.callEntry_mem] at hpost
  have hst : ∀ r ∈ [VG.Proof.MlKem.Arm.below s 8], (VG.Proof.MlKem.Arm.regA st 200).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_st.symm
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ (fun msg hm hp => ?_)
  · have hr12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr12, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, VG.Proof.MlKem.Arm.push1_sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]
    exact hpost msg (by
      unfold Spec.Sha3.Repr at hm ⊢
      rw [Proof.Sha3.stateAt_congr (bytes_frame fA hst (by decide))]; exact hm) hp

theorem pad_ct {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∃ st scr rate pos suffix,
      VG.Proof.MlKem.Arm.PadArgs s₁ st scr rate pos suffix ∧ VG.Proof.MlKem.Arm.PadArgs s₂ st scr rate pos suffix) :
    RelCT isa P padCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP s₁ s₂ h).1) ?_
  refine RelCT.mono (P := fun a b => ∃ x : BitVec 32 × BitVec 32 × Nat × Nat × BitVec 32 × BitVec 32,
      ∃ s₁ s₂, s₁.sp = x.2.2.2.2.2 ∧ s₂.sp = x.2.2.2.2.2 ∧
        VG.Proof.MlKem.Arm.PadArgs s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
        VG.Proof.MlKem.Arm.PadArgs s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
        a = pushed [.lr] s₁ ∧ b = pushed [.lr] s₂) ?_ ?_ (fun _ _ h => h)
  · refine RelCT.exists_ fun ⟨st, scr, rate, pos, suffix, sp⟩ => ?_
    refine RelCT.call (k := Proof.Sha3.padArm) Proof.Sha3.Arm.Stream.Pad.pad_verified.1
      Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1
      [⟨State.addr sp - BitVec.ofNat 64 4, 4⟩] [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] ?_
    rintro a b ⟨s₁, s₂, e₁, e₂, h₁, h₂, rfl, rfl⟩
    dsimp only at e₁ e₂ h₁ h₂
    have v₁ : (pushed [.lr] s₁).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 4, 4⟩]
        [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] = VG.Proof.MlKem.Arm.padView s₁ st scr := by simp only [VG.Proof.MlKem.Arm.padView, VG.Proof.MlKem.Arm.below, e₁]
    have v₂ : (pushed [.lr] s₂).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 4, 4⟩]
        [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA scr 640] = VG.Proof.MlKem.Arm.padView s₂ st scr := by simp only [VG.Proof.MlKem.Arm.padView, VG.Proof.MlKem.Arm.below, e₂]
    rw [v₁, v₂]
    obtain ⟨a₀, a₁⟩ := VG.Proof.MlKem.Arm.push1_arg (t := VG.Proof.MlKem.Arm.padView s₁ st scr) h₁.sp (VG.Proof.MlKem.Arm.push1_sp s₁) rfl
    obtain ⟨b₀, b₁⟩ := VG.Proof.MlKem.Arm.push1_arg (t := VG.Proof.MlKem.Arm.padView s₂ st scr) h₂.sp (VG.Proof.MlKem.Arm.push1_sp s₂) rfl
    have c₁ := VG.Proof.MlKem.Arm.cov_push1 h₁.sp h₁.cw
    have c₂ := VG.Proof.MlKem.Arm.cov_push1 h₂.sp h₂.cw
    simp only [VG.Proof.MlKem.Arm.below, e₁, e₂] at c₁ c₂
    refine ⟨VG.Proof.MlKem.Arm.pad_pre h₁, VG.Proof.MlKem.Arm.pad_pre h₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, ?_, c₂, ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlKem.Arm.push1_sp, e₁, e₂]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r0, h₂.r0]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r1, h₂.r1]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r2, h₂.r2]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r3, h₂.r3]
    · rw [a₁, b₁, h₁.lr, h₂.lr]
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₁.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₂.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · rintro a b ⟨s₁, s₂, hp, pa, pb⟩
    obtain ⟨hsp, st, scr, rate, pos, suffix, h₁, h₂⟩ := hP s₁ s₂ hp
    exact ⟨⟨st, scr, rate, pos, suffix, s₁.sp⟩, s₁, s₂, rfl, hsp.symm, h₁, h₂, VG.Proof.MlKem.Arm.push_eq pa, VG.Proof.MlKem.Arm.push_eq pb⟩

/-! ## `vg_keccak_squeeze` -/

/-- What a call of `vg_keccak_squeeze` in its frame needs. -/
structure SqueezeArgs (s : State) (st scr out : BitVec 32) (rate pos len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 pos
  r3 : s.gpr .r3 = out
  r12 : s.gpr .r12 = BitVec.ofNat 32 len
  lr : s.gpr .lr = scr
  hrate : rate ∈ rates
  hpos : pos ≤ rate
  hlen : len < 2 ^ 32
  sp : 8 ≤ s.sp.toNat
  fst : st.toNat + 200 ≤ 2 ^ 32
  fout : out.toNat + len ≤ 2 ^ 32
  fscr : scr.toNat + 640 ≤ 2 ^ 32
  d_st_out : (VG.Proof.MlKem.Arm.regA st 200).Disjoint (VG.Proof.MlKem.Arm.regA out len)
  d_st_scr : (VG.Proof.MlKem.Arm.regA st 200).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  d_out_scr : (VG.Proof.MlKem.Arm.regA out len).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  b_st : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA st 200)
  b_out : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA out len)
  b_scr : (VG.Proof.MlKem.Arm.below s 8).Disjoint (VG.Proof.MlKem.Arm.regA scr 640)
  cw : Covers [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA out len, VG.Proof.MlKem.Arm.regA scr 640] s.wr

abbrev squeezeView (s : State) (st scr out : BitVec 32) (len : Nat) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions [VG.Proof.MlKem.Arm.below s 8] [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA out len, VG.Proof.MlKem.Arm.regA scr 640]

theorem squeeze_pre {s : State} {st scr out : BitVec 32} {rate pos len : Nat}
    (h : VG.Proof.MlKem.Arm.SqueezeArgs s st scr out rate pos len) : Proof.Sha3.squeezeArm.pre (VG.Proof.MlKem.Arm.squeezeView s st scr out len) := by
  obtain ⟨a0, a1, a2⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.squeezeView s st scr out len) h.sp (VG.Proof.MlKem.Arm.push2_sp s) rfl
  have hr := VG.Proof.MlKem.Arm.rates_lt h.hrate
  have hp := h.hpos
  simp only [Proof.Sha3.squeezeArm, VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, a0, a1, a2, h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, VG.Proof.MlKem.Arm.toNat_ofNat32 h.hlen,
    VG.Proof.MlKem.Arm.toNat_ofNat32 (show rate < 2 ^ 32 by omega), VG.Proof.MlKem.Arm.toNat_ofNat32 (show pos < 2 ^ 32 by omega),
    State.callEntry_sp, VG.Proof.MlKem.Arm.push2_sp]
  refine ⟨trivial, trivial, h.d_st_out, h.d_st_scr, h.d_out_scr, h.b_st, h.b_out, h.b_scr, h.fst, h.fout,
    h.fscr, ?_, h.hrate, h.hpos⟩
  have := h.sp; have := s.sp.isLt; bv_omega

theorem cov_squeeze {s : State} (hsp : 8 ≤ s.sp.toNat) {ws : List Region} (hw : Covers ws s.wr) :
    Covers ([VG.Proof.MlKem.Arm.below s 8] ++ ws) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) :=
  VG.Proof.MlKem.Arm.cov_push hsp rfl (rs := []) (fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil) hw _ rfl

theorem squeeze_ok {s : State} {st scr out : BitVec 32} {rate pos len : Nat}
    (h : VG.Proof.MlKem.Arm.SqueezeArgs s st scr out rate pos len) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.Arm.Kept [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA out len, VG.Proof.MlKem.Arm.regA scr 640, VG.Proof.MlKem.Arm.below s 8] s s' →
      Spec.Sha3.bytesAt s'.mem (State.addr out) len = squeezeFrom rate (stateAt s.mem (State.addr st)) pos len →
      (s'.gpr .r0).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem (State.addr st)) (s'.gpr .r0).toNat d =
        squeezeFrom rate (stateAt s.mem (State.addr st)) (pos + len) d) → Q s') :
    WP isa squeezeCall s Q := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.sp) (by decide) ?_
  obtain ⟨a0, a1, a2⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.squeezeView s st scr out len) h.sp (VG.Proof.MlKem.Arm.push2_sp s) rfl
  have hr := VG.Proof.MlKem.Arm.rates_lt h.hrate
  have hp := h.hpos
  have hl := h.hlen
  have fA := VG.Proof.MlKem.Arm.push2_frame h.sp
  refine WP.callCalls (k := Proof.Sha3.squeezeArm) Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1
    (VG.Proof.MlKem.Arm.squeeze_pre h) (VG.Proof.MlKem.Arm.cov_squeeze h.sp h.cw)
    (fun x n hi => by
      obtain ⟨r', hr', hc'⟩ := h.cw x n hi
      exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩) ?_ VG.Proof.MlKem.Arm.squeeze_noFrames
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  simp only [Proof.Sha3.squeezeArm, VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs),
    VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_mem, State.withRegions_gpr,
    a1, h.r0, h.r1, h.r2, h.r3, h.r12, VG.Proof.MlKem.Arm.toNat_ofNat32 h.hlen, VG.Proof.MlKem.Arm.toNat_ofNat32 (show rate < 2 ^ 32 by omega),
    VG.Proof.MlKem.Arm.toNat_ofNat32 (show pos < 2 ^ 32 by omega), State.callEntry_mem] at hpost
  have hst : ∀ r ∈ [VG.Proof.MlKem.Arm.below s 8], (VG.Proof.MlKem.Arm.regA st 200).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact h.b_st.symm
  have est : stateAt (pushed [.r12, .lr] s).mem (State.addr st) = stateAt s.mem (State.addr st) :=
    Proof.Sha3.stateAt_congr (bytes_frame fA hst (by decide))
  rw [est] at hpost
  obtain ⟨p1, p2, p3⟩ := hpost
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
  · have hr12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr12, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, VG.Proof.MlKem.Arm.push2_sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact p1
  · rw [popped_gpr (by decide)]; exact p2
  · rw [popped_gpr (by decide), popped_mem]; exact p3

theorem squeeze_ct {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∃ st scr out rate pos len,
      VG.Proof.MlKem.Arm.SqueezeArgs s₁ st scr out rate pos len ∧ VG.Proof.MlKem.Arm.SqueezeArgs s₂ st scr out rate pos len) :
    RelCT isa P squeezeCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP s₁ s₂ h).1) ?_
  refine RelCT.mono (P := fun a b => ∃ x : BitVec 32 × BitVec 32 × BitVec 32 × Nat × Nat × Nat × BitVec 32,
      ∃ s₁ s₂, s₁.sp = x.2.2.2.2.2.2 ∧ s₂.sp = x.2.2.2.2.2.2 ∧
        VG.Proof.MlKem.Arm.SqueezeArgs s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        VG.Proof.MlKem.Arm.SqueezeArgs s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 ∧
        a = pushed [.r12, .lr] s₁ ∧ b = pushed [.r12, .lr] s₂) ?_ ?_ (fun _ _ h => h)
  · refine RelCT.exists_ fun ⟨st, scr, out, rate, pos, len, sp⟩ => ?_
    refine RelCT.call (k := Proof.Sha3.squeezeArm) Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1
      Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1
      [⟨State.addr sp - BitVec.ofNat 64 8, 8⟩] [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA out len, VG.Proof.MlKem.Arm.regA scr 640] ?_
    rintro a b ⟨s₁, s₂, e₁, e₂, h₁, h₂, rfl, rfl⟩
    dsimp only at e₁ e₂ h₁ h₂
    have v₁ : (pushed [.r12, .lr] s₁).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA out len, VG.Proof.MlKem.Arm.regA scr 640] = VG.Proof.MlKem.Arm.squeezeView s₁ st scr out len := by
      simp only [VG.Proof.MlKem.Arm.squeezeView, VG.Proof.MlKem.Arm.below, e₁]
    have v₂ : (pushed [.r12, .lr] s₂).callEntry.withRegions [⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
        [VG.Proof.MlKem.Arm.regA st 200, VG.Proof.MlKem.Arm.regA out len, VG.Proof.MlKem.Arm.regA scr 640] = VG.Proof.MlKem.Arm.squeezeView s₂ st scr out len := by
      simp only [VG.Proof.MlKem.Arm.squeezeView, VG.Proof.MlKem.Arm.below, e₂]
    rw [v₁, v₂]
    obtain ⟨a₀, a₁, a₂⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.squeezeView s₁ st scr out len) h₁.sp (VG.Proof.MlKem.Arm.push2_sp s₁) rfl
    obtain ⟨b₀, b₁, b₂⟩ := VG.Proof.MlKem.Arm.push2_arg (t := VG.Proof.MlKem.Arm.squeezeView s₂ st scr out len) h₂.sp (VG.Proof.MlKem.Arm.push2_sp s₂) rfl
    have c₁ := VG.Proof.MlKem.Arm.cov_squeeze h₁.sp h₁.cw
    have c₂ := VG.Proof.MlKem.Arm.cov_squeeze h₂.sp h₂.cw
    simp only [VG.Proof.MlKem.Arm.below, e₁, e₂] at c₁ c₂
    refine ⟨VG.Proof.MlKem.Arm.squeeze_pre h₁, VG.Proof.MlKem.Arm.squeeze_pre h₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, ?_, c₂, ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlKem.Arm.push2_sp, e₁, e₂]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r0, h₂.r0]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r1, h₂.r1]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r2, h₂.r2]
    · rw [VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), VG.Proof.MlKem.Arm.view_gpr _ _ _ _ (by decide), h₁.r3, h₂.r3]
    · rw [a₁, b₁, h₁.r12, h₂.r12]
    · rw [a₂, b₂, h₁.lr, h₂.lr]
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₁.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
    · exact fun x n hi => by
        obtain ⟨r', hr', hc'⟩ := h₂.cw x n hi
        exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · rintro a b ⟨s₁, s₂, hp, pa, pb⟩
    obtain ⟨hsp, st, scr, out, rate, pos, len, h₁, h₂⟩ := hP s₁ s₂ hp
    exact ⟨⟨st, scr, out, rate, pos, len, s₁.sp⟩, s₁, s₂, rfl, hsp.symm, h₁, h₂, VG.Proof.MlKem.Arm.push_eq pa, VG.Proof.MlKem.Arm.push_eq pb⟩

end VG.Proof.MlKem.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Mul`. -/
section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_multiply_ntts`

The registers saved and the table of the `γᵢ` stored (`setup_ok`); then one
pair of coefficients per iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`),
whose body is symbolically executed once for any pointers (`body_ok`); the
invariant says which coefficients of `h` are written, and that `h` is the only
memory written since the setup (`Inv`); then the registers restored.
-/

namespace VG.Proof.MlKem.Arm.Mul

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## Values -/

theorem red_mac (x y z w : Zq) :
    VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val + BitVec.ofNat 32 z.val * BitVec.ofNat 32 w.val) =
      BitVec.ofNat 32 (x * y + z * w).val := by
  have hx := val_lt x
  have hy := val_lt y
  have hz := val_lt z
  have hw := val_lt w
  have p1 := mul_lt_q2 hx hy
  have p2 := mul_lt_q2 hz hw
  have hs : (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val + BitVec.ofNat 32 z.val * BitVec.ofNat 32 w.val).toNat =
      x.val * y.val + z.val * w.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.val) (by omega),
      Nat.mod_eq_of_lt (a := y.val) (by omega), Nat.mod_eq_of_lt (a := z.val) (by omega),
      Nat.mod_eq_of_lt (a := w.val) (by omega), Nat.mod_eq_of_lt (a := x.val * y.val) (by omega),
      Nat.mod_eq_of_lt (a := z.val * w.val) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ofNat_val_eq ?_
  rw [VG.Proof.MlKem.Arm.red_toNat (by rw [hs]; omega), hs, val_add', val_mul, val_mul, ← Nat.add_mod]

theorem even_eq (a b c d γ : Zq) :
    VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val +
      VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 c.val * BitVec.ofNat 32 d.val) * BitVec.ofNat 32 γ.val) =
      BitVec.ofNat 32 (a * b + c * d * γ).val := by
  rw [VG.Proof.MlKem.Arm.red_mul]; exact VG.Proof.MlKem.Arm.Mul.red_mac a b (c * d) γ

/-! ## The loop body -/

section
variable {s : State} {x0 x1 x2 x3 c : BitVec 32}

theorem body_ok (h0 : s.gpr .r0 = x0) (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h3 : s.gpr .r3 = x3)
    (h8 : s.gpr .r8 = VG.Proof.MlKem.Arm.C) (h11 : s.gpr .r11 = c)
    (if0 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4)
    (if1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 4)) 4)
    (ig0 : InRegions (s.rd ++ s.wr) (State.addr (x2 + BitVec.ofNat 32 0)) 4)
    (ig1 : InRegions (s.rd ++ s.wr) (State.addr (x2 + BitVec.ofNat 32 4)) 4)
    (iγ : InRegions (s.rd ++ s.wr) (State.addr (x3 + BitVec.ofNat 32 0)) 4)
    (o0 : InRegions s.wr (State.addr (x0 + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (x0 + BitVec.ofNat 32 4)) 4) :
    WP isa (.block mulBody) s fun s' =>
      s'.gpr .r0 = x0 + 8 ∧ s'.gpr .r1 = x1 + 8 ∧ s'.gpr .r2 = x2 + 8 ∧ s'.gpr .r3 = x3 + 4 ∧
      s'.gpr .r8 = VG.Proof.MlKem.Arm.C ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (x0 + BitVec.ofNat 32 0))
          (VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 0)) 32 +
            VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 4)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 4)) 32) *
            s.mem.readW (State.addr (x3 + BitVec.ofNat 32 0)) 32))).writeW
        (State.addr (x0 + BitVec.ofNat 32 4))
          (VG.Proof.MlKem.Arm.red VG.Proof.MlKem.Arm.C (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 4)) 32 +
            s.mem.readW (State.addr (x1 + BitVec.ofNat 32 4)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 0)) 32)) := by
  run_block [mulBody, reduce, barrett, subQ, fixup, VG.Proof.MlKem.Arm.red, VG.Proof.MlKem.Arm.bar, fixq, h0, h1, h2, h3, h8, h11, if0, if1, ig0,
    ig1, iγ, o0, o1, and_self, and_true]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev ph : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev pg : BitVec 32 := s₀.gpr .r2
abbrev ps : BitVec 32 := s₀.gpr .r3
abbrev H : Addr := State.addr (VG.Proof.MlKem.Arm.Mul.ph s₀)
abbrev F : Addr := State.addr (VG.Proof.MlKem.Arm.Mul.pf s₀)
abbrev G : Addr := State.addr (VG.Proof.MlKem.Arm.Mul.pg s₀)
abbrev S : Addr := State.addr (VG.Proof.MlKem.Arm.Mul.ps s₀)
abbrev fp : VG.Spec.MlKem.Poly := polyAt s₀.mem (VG.Proof.MlKem.Arm.Mul.F s₀)
abbrev gp : VG.Spec.MlKem.Poly := polyAt s₀.mem (VG.Proof.MlKem.Arm.Mul.G s₀)

/-- Coefficient `j` of the output. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (VG.Proof.MlKem.Arm.Mul.fp s₀) (VG.Proof.MlKem.Arm.Mul.gp s₀))[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem.Arm.Mul.F s₀), polyRegion (VG.Proof.MlKem.Arm.Mul.G s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.Arm.Mul.H s₀), polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀)]
  hf : (polyRegion (VG.Proof.MlKem.Arm.Mul.H s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Mul.F s₀))
  hg : (polyRegion (VG.Proof.MlKem.Arm.Mul.H s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Mul.G s₀))
  hs : (polyRegion (VG.Proof.MlKem.Arm.Mul.H s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀))
  fs : (polyRegion (VG.Proof.MlKem.Arm.Mul.F s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀))
  gs : (polyRegion (VG.Proof.MlKem.Arm.Mul.G s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀))
  fitH : (VG.Proof.MlKem.Arm.Mul.ph s₀).toNat + 1024 ≤ 2 ^ 32
  fitF : (VG.Proof.MlKem.Arm.Mul.pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (VG.Proof.MlKem.Arm.Mul.pg s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (VG.Proof.MlKem.Arm.Mul.ps s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (VG.Proof.MlKem.Arm.Mul.F s₀)
  redG : Reduced s₀.mem (VG.Proof.MlKem.Arm.Mul.G s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : VG.Proof.MlKem.Arm.Saved m₁ (VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (gammaTable.getD j 0)
  f : ∀ j < 256, coeffAt m₁ (VG.Proof.MlKem.Arm.Mul.F s₀) j = coeffAt s₀.mem (VG.Proof.MlKem.Arm.Mul.F s₀) j
  g : ∀ j < 256, coeffAt m₁ (VG.Proof.MlKem.Arm.Mul.G s₀) j = coeffAt s₀.mem (VG.Proof.MlKem.Arm.Mul.G s₀) j

/-- After `i` pairs, from the memory `m₁` the setup left. -/
structure Inv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Mul.ph s₀ + BitVec.ofNat 32 (8 * i)
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Mul.pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Mul.pg s₀ + BitVec.ofNat 32 (8 * i)
  r3 : s.gpr .r3 = VG.Proof.MlKem.Arm.Mul.ps s₀ + BitVec.ofNat 32 (4 * i)
  r8 : s.gpr .r8 = VG.Proof.MlKem.Arm.C
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (128 - i))
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (VG.Proof.MlKem.Arm.Mul.H s₀)] m₁ s.mem
  coeff : ∀ j < 256, coeffAt s.mem (VG.Proof.MlKem.Arm.Mul.H s₀) j = if j < 2 * i then VG.Proof.MlKem.Arm.Mul.out s₀ j else coeffAt m₁ (VG.Proof.MlKem.Arm.Mul.H s₀) j

theorem out_even (s₀ : State) {i : Nat} (hi : i < 128) :
    VG.Proof.MlKem.Arm.Mul.out s₀ (2 * i) = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Mul.fp s₀)[2 * i]! * (VG.Proof.MlKem.Arm.Mul.gp s₀)[2 * i]! +
      (VG.Proof.MlKem.Arm.Mul.fp s₀)[2 * i + 1]! * (VG.Proof.MlKem.Arm.Mul.gp s₀)[2 * i + 1]! * gamma i).val := by
  rw [VG.Proof.MlKem.Arm.Mul.out, multiplyNTTs_even _ _ hi]

theorem out_odd (s₀ : State) {i : Nat} (hi : i < 128) :
    VG.Proof.MlKem.Arm.Mul.out s₀ (2 * i + 1) = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Mul.fp s₀)[2 * i]! * (VG.Proof.MlKem.Arm.Mul.gp s₀)[2 * i + 1]! +
      (VG.Proof.MlKem.Arm.Mul.fp s₀)[2 * i + 1]! * (VG.Proof.MlKem.Arm.Mul.gp s₀)[2 * i]!).val := by
  rw [VG.Proof.MlKem.Arm.Mul.out, multiplyNTTs_odd _ _ hi]

theorem step {s₀ : State} (hp : VG.Proof.MlKem.Arm.Mul.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Mul.Setup s₀ m₁) {i : Nat} (hi : i < 128) {s : State}
    (h : VG.Proof.MlKem.Arm.Mul.Inv s₀ m₁ i s) :
    WP isa (.block mulBody) s fun s' => VG.Proof.MlKem.Arm.Mul.Inv s₀ m₁ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fH := hp.fitH
  have fF := hp.fitF
  have fG := hp.fitG
  have fS := hp.fitS
  have eF0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fF (by omega) (by omega)
  have eF1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fF (by omega) (by omega)
  have eG0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fG (by omega) (by omega)
  have eG1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fG (by omega) (by omega)
  have eH0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fH (by omega) (by omega)
  have eH1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fH (by omega) (by omega)
  have eS := addr_ptr (VG.Proof.MlKem.Arm.Mul.ps s₀) (4 * i) 0 (by omega)
  have cF0 := coeff_contains (VG.Proof.MlKem.Arm.Mul.F s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have cF1 := coeff_contains (VG.Proof.MlKem.Arm.Mul.F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cG0 := coeff_contains (VG.Proof.MlKem.Arm.Mul.G s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have cG1 := coeff_contains (VG.Proof.MlKem.Arm.Mul.G s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cH0 := coeff_contains (VG.Proof.MlKem.Arm.Mul.H s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have cH1 := coeff_contains (VG.Proof.MlKem.Arm.Mul.H s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cS : (polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀)).Contains (VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 (4 * i + 0)) 4 :=
    contains_off (by omega) (by omega)
  have iR : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.rd ++ s₀.wr → R.Contains a n →
      InRegions (s.rd ++ s.wr) a n := fun hR hc => by rw [h.rd, h.wr]; exact inRegions_of hR hc
  have iW : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.wr → R.Contains a n → InRegions s.wr a n :=
    fun hR hc => by rw [h.wr]; exact inRegions_of hR hc
  -- The values read.
  have vF : ∀ j < 256, coeffAt s.mem (VG.Proof.MlKem.Arm.Mul.F s₀) j = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Mul.fp s₀)[j]!).val := fun j hj => by
    rw [frame_coeff h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm)
      (by rw [n_eq]; exact hj), hm.f j hj]
    exact ofNat_val_eq (polyAt_val hp.redF (by rw [n_eq]; exact hj)).symm
  have vG : ∀ j < 256, coeffAt s.mem (VG.Proof.MlKem.Arm.Mul.G s₀) j = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Mul.gp s₀)[j]!).val := fun j hj => by
    rw [frame_coeff h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm)
      (by rw [n_eq]; exact hj), hm.g j hj]
    exact ofNat_val_eq (polyAt_val hp.redG (by rw [n_eq]; exact hj)).symm
  have vS : s.mem.readW (VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 (4 * i + 0)) 32 = BitVec.ofNat 32 (gamma i).val := by
    rw [h.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hs.symm)
      (by decide), Nat.add_zero, hm.tab i hi, VG.Proof.MlKem.Arm.gammaTable_eq, gammas_getD hi]
  refine WP.mono (VG.Proof.MlKem.Arm.Mul.body_ok h.r0 h.r1 h.r2 h.r3 h.r8 h.r11
    (by rw [eF0]; exact iR (by simp [hp.rd]) cF0) (by rw [eF1]; exact iR (by simp [hp.rd]) cF1)
    (by rw [eG0]; exact iR (by simp [hp.rd]) cG0) (by rw [eG1]; exact iR (by simp [hp.rd]) cG1)
    (by rw [eS]; exact iR (by simp [hp.wr]) cS) (by rw [eH0]; exact iW (by simp [hp.wr]) cH0)
    (by rw [eH1]; exact iW (by simp [hp.wr]) cH1))
    fun s' ⟨r0, r1, r2, r3, r8, r11, z, lr, rd, wr, sp, m⟩ => ⟨⟨?_, ?_, ?_, ?_, r8, ?_, lr.trans h.lr,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 8 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact ptr_succ _ 8 i
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r11]; exact count_sub (k := 1) hi
  · rw [m, eH0, eH1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH0).writeW (List.mem_singleton_self _) _ cH1
  · rw [m, eF0, eF1, eG0, eG1, eH0, eH1, eS]
    show ∀ j < 256, coeffAt ((s.mem.writeW (coeffAddr (VG.Proof.MlKem.Arm.Mul.H s₀) (2 * i)) _).writeW _ _) _ j = _
    rw [← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, vF _ (by omega), vF _ (by omega),
      vG _ (by omega), vG _ (by omega), vS, VG.Proof.MlKem.Arm.Mul.even_eq, VG.Proof.MlKem.Arm.Mul.red_mac, ← VG.Proof.MlKem.Arm.Mul.out_even s₀ hi, ← VG.Proof.MlKem.Arm.Mul.out_odd s₀ hi,
      show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    exact coeff_one (a := 2 * i + 1) (by omega) (coeff_one (a := 2 * i) (by omega) h.coeff rfl) rfl
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## Setup and the end -/

theorem setup_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Mul.Pre s₀) :
    WP isa (.block (saveRegs .r3 512 ++ table gammaTable .r3 ++ consts ++ ([.mov .r11 (.imm 128)] : List Instr)))
      s₀ fun s => VG.Proof.MlKem.Arm.Mul.Setup s₀ s.mem ∧ VG.Proof.MlKem.Arm.Mul.Inv s₀ s.mem 0 s := by
  have fS := hp.fitS
  have wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega))
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.Arm.saveRegs_ok .r3 (off := 512) (by decide) (VG.Proof.MlKem.Arm.fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  have g3 : (s₁.gpr .r3) = VG.Proof.MlKem.Arm.Mul.ps s₀ := by rw [h₁.gpr]
  refine WP.mono (VG.Proof.MlKem.Arm.table_ok gammaTable (by decide) (b := .r3) (by decide) (by rw [g3]; exact VG.Proof.MlKem.Arm.fit_le (by decide) fS)
    fun k hk => by rw [g3, h₁.wr]; exact wS (by omega)) fun s₂ h₂ => ?_
  -- The memory after the setup, and its bytes outside `scratch`.
  have hS : (VG.Proof.MlKem.Arm.Mul.S s₀).toNat + 1024 ≤ 2 ^ 64 := VG.Proof.MlKem.Arm.addr_fit _ (by decide)
  have fr : Frame [polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact VG.Proof.MlKem.Arm.region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g3, ← VG.Proof.MlKem.Arm.add_ofNat_zero (State.addr (VG.Proof.MlKem.Arm.Mul.ps s₀))]
      exact VG.Proof.MlKem.Arm.region_sub_off (by decide)
  have hm : VG.Proof.MlKem.Arm.Mul.Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [h₂.frame.readW (r := ⟨VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g3, VG.Proof.MlKem.Arm.add_ofNat_add, ← VG.Proof.MlKem.Arm.add_ofNat_zero (State.addr (VG.Proof.MlKem.Arm.Mul.ps s₀))]
        exact VG.Proof.MlKem.Arm.region_disj_off (by omega) (by omega) (by omega) hS
    · have := h₂.tab j hj; rwa [g3] at this
    · exact frame_coeff fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs)
        (by rw [n_eq]; exact hj)
    · exact frame_coeff fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.gs)
        (by rw [n_eq]; exact hj)
  have e : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr])
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have e2 := e .r2 (by decide)
  have e3 := e .r3 (by decide)
  have elr := e .lr (by decide)
  run_block [consts, e0, e1, e2, e3, elr, h₂.rd, h₁.rd, h₂.wr, h₁.wr, h₂.sp, h₁.sp, VG.Proof.MlKem.Arm.consts_val, hm, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, Frame.refl _ _, fun j _ => ?_⟩ <;> simp [e0, e1, e2, e3, elr]

theorem restore_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Mul.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Mul.Setup s₀ m₁) {s : State}
    (h : VG.Proof.MlKem.Arm.Mul.Inv s₀ m₁ 128 s) :
    WP isa (.block (restoreRegs .r3 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (VG.Proof.MlKem.Arm.Mul.H s₀) (multiplyNTTs (VG.Proof.MlKem.Arm.Mul.fp s₀) (VG.Proof.MlKem.Arm.Mul.gp s₀)) := by
  have fS := hp.fitS
  have hS : (VG.Proof.MlKem.Arm.Mul.S s₀).toNat + 1024 ≤ 2 ^ 64 := VG.Proof.MlKem.Arm.addr_fit _ (by decide)
  have e3 : State.addr (s.gpr .r3) + BitVec.ofNat 64 0 = VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 512 := by
    rw [h.r3, addr_add (by omega), VG.Proof.MlKem.Arm.add_ofNat_zero]
  refine WP.mono (VG.Proof.MlKem.Arm.restoreRegs_ok .r3 (by decide) (off := 0) (by decide) (by rw [h.r3]; bv_omega)
    (g := s₀.gpr) (by
      rw [e3]
      intro i hi
      rw [h.frame.readW (r := ⟨VG.Proof.MlKem.Arm.Mul.S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.hs.symm.sub_left ?_
        rw [VG.Proof.MlKem.Arm.add_ofNat_add]
        exact VG.Proof.MlKem.Arm.region_sub_off (by omega))
    fun i hi => by
      rw [e3, h.rd, h.wr, hp.wr, VG.Proof.MlKem.Arm.add_ofNat_add]
      exact inRegions_of (R := polyRegion (VG.Proof.MlKem.Arm.Mul.S s₀)) (by simp) (contains_off (by omega) (by omega)))
    fun s' h' => ⟨VG.Proof.MlKem.Arm.preserved_of_restore h' h.lr, h'.sp.trans h.sp, ?_⟩
  rw [h'.mem]
  exact polyIs_of_coeffAt fun j hj => by
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega)]; rfl

theorem correct {s₀ : State} (hp : VG.Proof.MlKem.Arm.Mul.Pre s₀) :
    WP isa multiplyNTTs s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (VG.Proof.MlKem.Arm.Mul.H s₀) (Spec.MlKem.multiplyNTTs (VG.Proof.MlKem.Arm.Mul.fp s₀) (VG.Proof.MlKem.Arm.Mul.gp s₀)) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Mul.setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_ne (VG.Proof.MlKem.Arm.Mul.Inv s₀ s₁.mem) (N := 128) (by decide) (fun i hi s h => VG.Proof.MlKem.Arm.Mul.step hp hm hi h)
    (fun s h => VG.Proof.MlKem.Arm.Mul.restore_ok hp hm h) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.mulContract Arm.abi).pre s) : VG.Proof.MlKem.Arm.Mul.Pre s := by
  sig_pre [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.multiplyNTTs (Spec.MlKem.mulContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlKem.Arm.Mul.pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlKem.Arm.Mul.correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlKem.Arm.Mul.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.Arm.Mul

end
