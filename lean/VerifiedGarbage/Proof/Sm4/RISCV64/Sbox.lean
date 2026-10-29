module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Sbox
public import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Aes.RISCV64.Layers
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The bitsliced SM4 S-box on RISC-V

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 64 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's S-box on the same inputs. `sbox_ok` then gives,
at every bit position `p`, the S-box of the byte formed by bit `p` of the
eight words. As AES's (`Proof/Aes/RISCV64/Layers.lean`), whose registers it
writes (`sboxWrites`), and `a0`, `a4` and `ra` (`sm4Writes`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Aes.RISCV64 VG.Impl.Sm4.RISCV64
open VG.Proof.Sm4
open VG.Proof.Aes (bsByte getLsbD_bsByte)
open VG.Proof.Aes.RISCV64 (TabAll tabAll_sound tabAll_fun sboxWrites)

/-- The S-box's memory: its spill slots, at `a5`. -/
def sboxCfg : Cfg := { base := sb, slots := 40, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map fun k => .v (inT k)
    slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => word (e.reg (q j)) == some (sboxT j)

/-- The registers SM4's S-box writes: AES's (`sboxWrites`), and `a0`, `a4`
and `ra`, which the rounds set again or restore after it. -/
def sm4Writes : List Reg := sboxWrites ++ [.a0, .a4, .ra]

/-- The registers outside `sm4Writes`. -/
def sm4Rest : List Reg := [.a1, .a2, .a3, .a5]

theorem not_sm4Writes (r : Reg) (hr : r ∉ sm4Writes) : r ∈ sm4Rest := by
  revert hr; cases r <;> decide

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) Impl.Sm4.RISCV64.sboxCode sboxEnv sboxPost = true := by
  decide +kernel

theorem sbox_writes_rest :
    sm4Rest.all (fun r => Impl.Sm4.RISCV64.sboxCode.all fun i => dst i != some r) = true := by
  decide +kernel

theorem sbox_writes (r : Reg) (hr : r ∉ sm4Writes) :
    (Impl.Sm4.RISCV64.sboxCode.all fun i => dst i != some r) = true :=
  List.all_eq_true.mp sbox_writes_rest r (not_sm4Writes r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa Impl.Sm4.RISCV64.sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (sboxB (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sm4Writes → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (.v (sboxT j)) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at this
    cases h : e'.reg (q j) with
    | none => rw [h] at this; cases this
    | some v => cases v <;> rw [h] at this <;> simp_all [word]
  let cs : Nat → Nat := fun p => (bsByte (fun k => s.gpr (q k)) p).toNat
  have hcs : ∀ p < 64, cs p < 256 := fun p _ => (bsByte (fun k => s.gpr (q k)) p).isLt
  have hrel : Rel (TabAll cs) sboxCfg (fun _ => none) sboxEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    intro p hp
    simp only [TableRel, inT, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) tabAll_fun hok hrel he
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hc := hcs p hp
    have := p₀.rel.reg (q j) _ (hout j hj) p hp
    simp only [TableRel] at this
    rw [← this, sboxT, testBit_tableOf]
    simp [hc, cs, sboxN_eq hc, BitVec.testBit_toNat]
  · simp [sbox_writes r hr]

end VG.Proof.Sm4.RISCV64
