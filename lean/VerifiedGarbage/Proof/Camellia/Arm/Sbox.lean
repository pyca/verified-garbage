module

public import VerifiedGarbage.Impl.Camellia.Arm.Sbox
public import VerifiedGarbage.Proof.Camellia.SboxTable
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Proof.Camellia.Bitsliced32
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The bitsliced Camellia S-box on ARMv7

As on the 64-bit targets: `sboxCode` only combines words bitwise (and
builds all ones with `mov` and `sub`), so the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's `SBOX1`. `sbox_ok` then gives, at every bit
position `p`, `SBOX1` of the byte formed by bit `p` of the eight words.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm VG.Impl.Camellia.Arm
open VG.Proof.Camellia
open VG.Proof.Camellia.W32 (bsByte getLsbD_bsByte)

/-- The S-box's memory: its spill slots, at `r8`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sbox1T j)

theorem sbox_check :
    check (table 32 256) sboxCfg (fun _ => none) Impl.Camellia.Arm.sboxCode sboxEnv sboxPost = true := by
  lit_decide

/-- The registers the layers may write: the state, the S-box's temporaries
and all ones, and the linear layers' temporaries. -/
def layerWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11, .r12, .lr]

/-- The registers outside `layerWrites`. -/
def layerKeep : List Reg := [.r8, .r9]

theorem not_layerWrites (r : Reg) (hr : r ∉ layerWrites) : r ∈ layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => !clobbers i r) = true)
    (r : Reg) (hr : r ∉ layerWrites) : (is.all fun i => !clobbers i r) = true :=
  List.all_eq_true.mp h r (not_layerWrites r hr)

/-- `SBOX1`, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa Impl.Camellia.Arm.sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (q j)).getLsbD p = (Spec.Camellia.sbox1 (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (sbox1T j) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 32, ∃ s', runBlock isa Impl.Camellia.Arm.sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (Impl.Camellia.Arm.sboxCode.all fun i => !clobbers i r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, testBit_sbox1T hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp [writes_rest (is := Impl.Camellia.Arm.sboxCode) (by decide +kernel) r hr]

end VG.Proof.Camellia.Arm
