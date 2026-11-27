module

public import VerifiedGarbage.Impl.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.Arm.StraightNot
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The bitsliced AES S-boxes on ARMv7

The S-boxes' code (`Impl/Aes/Arm/Sbox.lean`) is checked by evaluation on the
truth tables of the 256 inputs against the specification's S-box, computed on
the same tables (`Proof/Aes/SboxSpec.lean`). `subBytes_ok`, `subBytesQ_ok`,
`invSubBytes_ok` and `sbox_ok` then give the code's effect at each of the 32
bit positions of the slices.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.Aes (bsByte getLsbD_bsByte sbIn sbox0T invSbox0T sboxOfT sbox0T_bit invSbox0T_bit sboxOfT_bit sbox0
  invSbox0)
open VG.Spec.Aes (sbox invSbox)

/-- The memory the S-boxes use: the scratch buffer's first slots. -/
def spillCfg : Cfg := { base := sb, slots := 12, ext := sb, exts := 0 }
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

/-! ## The registers -/

/-- The registers the S-box in place writes. -/
def layerWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11, .r12, .lr]

/-- The others. -/
def layerKeep : List Reg := [.r8, .r9]

theorem not_layerWrites (r : Reg) (hr : r ∉ layerWrites) : r ∈ layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => !clobbers i r) = true) (r : Reg) (hr : r ∉ layerWrites) :
    (is.all fun i => !clobbers i r) = true :=
  List.all_eq_true.mp h r (not_layerWrites r hr)

/-- A block that does not write the scratch buffer's base writes only
`layerWrites` and `kp`. -/
theorem writes_sb {is : List Instr} (h : (is.all fun i => !clobbers i sb) = true) (r : Reg)
    (hr : r ∉ layerWrites) (hk : r ≠ kp) : (is.all fun i => !clobbers i r) = true := by
  have : r = sb := by revert hr hk; cases r <;> decide
  rw [this]; exact h

/-! ## The checks -/

/-- The slices `q j` hold the inputs' tables. -/
def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map sbIn, slot := fun _ => none }

/-- The slices `r j` hold the tables `T`. -/
def sboxPost (r : Nat → Reg) (T : List Nat) (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (r j) == some (T.getD j 0)

theorem subBytes_check : checkN (table 32 256) spillCfg (fun _ => none) subBytes sboxEnv
    (sboxPost p sbox0T) = true := by decide +kernel

theorem invSubBytes_check : checkN (table 32 256) spillCfg (fun _ => none) invSubBytes sboxEnv
    (sboxPost p invSbox0T) = true := by decide +kernel

theorem subBytesQ_check : checkN (table 32 256) sboxCfg (fun _ => none) subBytesQ sboxEnv
    (sboxPost q sbox0T) = true := by decide +kernel

theorem sbox_check : checkN (table 32 256) sboxCfg (fun _ => none) sboxCode sboxEnv
    (sboxPost q sboxOfT) = true := by decide +kernel

/-! ## On the machine -/

/-- A block that the check accepts, at every bit position of the slices. -/
theorem table_ok {cfg : Cfg} {is : List Instr} {r : Nat → Reg} {T : List Nat} {f : Byte → Byte}
    (hchk : checkN (table 32 256) cfg (fun _ => none) is sboxEnv (sboxPost r T) = true)
    (hf : ∀ c < 256, ∀ j < 8, (T.getD j 0).testBit c = (f (BitVec.ofNat 8 c)).getLsbD j) {s : State} (hok : Ok cfg s) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ x < 32, bsByte (fun j => s'.gpr (r j)) x = f (bsByte (fun j => s.gpr (q j)) x)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r', (is.all fun i => !clobbers i r') = true → s'.gpr r' = s.gpr r') ∧
      Frame [slotRegion cfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_checkN _ _ _ hchk
  have hout : ∀ j < 8, e'.reg (r j) = some (T.getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ x < 32, ∃ s', runBlock isa is s = some s' ∧
      Post (TableRel x (bsByte (fun k => s.gpr (q k)) x).toNat) cfg (fun _ => none) e' s s'
        (fun r' => (is.all fun i => !clobbers i r') = false) := by
    intro x hx
    have hc := (bsByte (fun k => s.gpr (q k)) x).isLt
    refine runN (table_sound hx hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqk := List.find?_some hk
    have hk8 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, sbIn, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun x hx => ?_, p₀.rd, p₀.wr, p₀.sp, fun r' hr => p₀.other r' (by simp [hr]), p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key x hx
  obtain rfl := run_unique hs'' hs'
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := p₁.rel.reg (r j) _ (hout j hj)
  simp only [TableRel] at this
  rw [getLsbD_bsByte _ _ hj, ← this, hf _ (BitVec.isLt _) j hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem subBytes_ok {s : State} (hok : Ok spillCfg s) :
    ∃ s', runBlock isa subBytes s = some s' ∧
      (∀ x < 32, bsByte (fun j => s'.gpr (p j)) x = sbox (bsByte (fun j => s.gpr (q j)) x) ^^^ 0x63) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ Frame [slotRegion spillCfg s] s.mem s'.mem := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := table_ok subBytes_check (fun c hc j hj => sbox0T_bit hc hj) hok
  exact ⟨s', h1, h2, h3, h4, h5, fun r hr hk => h6 r (writes_sb (by decide +kernel) r hr hk), h7⟩

theorem invSubBytes_ok {s : State} (hok : Ok spillCfg s) :
    ∃ s', runBlock isa invSubBytes s = some s' ∧
      (∀ x < 32, bsByte (fun j => s'.gpr (p j)) x = invSbox (bsByte (fun j => s.gpr (q j)) x ^^^ 0x63)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ Frame [slotRegion spillCfg s] s.mem s'.mem := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := table_ok invSubBytes_check (fun c hc j hj => invSbox0T_bit hc hj) hok
  exact ⟨s', h1, h2, h3, h4, h5, fun r hr hk => h6 r (writes_sb (by decide +kernel) r hr hk), h7⟩

theorem subBytesQ_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa subBytesQ s = some s' ∧
      (∀ x < 32, bsByte (fun j => s'.gpr (q j)) x = sbox (bsByte (fun j => s.gpr (q j)) x) ^^^ 0x63) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := table_ok subBytesQ_check (fun c hc j hj => sbox0T_bit hc hj) hok
  exact ⟨s', h1, h2, h3, h4, h5, fun r hr => h6 r (writes_rest (by decide +kernel) r hr), h7⟩

/-- The S-box in place, its constant included. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ x < 32, (s'.gpr (q j)).getLsbD x = (sbox (bsByte (fun k => s.gpr (q k)) x)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := table_ok sbox_check (fun c hc j hj => sboxOfT_bit hc hj) hok
  exact ⟨s', h1, fun j hj x hx => by rw [← h2 x hx, getLsbD_bsByte _ _ hj], h3, h4, h5,
    fun r hr => h6 r (writes_rest (by decide +kernel) r hr), h7⟩

end VG.Proof.Aes.Arm
