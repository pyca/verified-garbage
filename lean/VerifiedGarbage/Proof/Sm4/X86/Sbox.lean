import VerifiedGarbage.Impl.Sm4.X86.Sbox
import VerifiedGarbage.Proof.Sm4.SboxTable
import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Sm4.Bitsliced32

/-!
# The bitsliced SM4 S-box on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/Sbox.lean`), with the planes in slots: the
kernel evaluates `sboxCode` once on truth tables of the 256 inputs
(`Bitslice.table`) and compares the result with the specification's S-box
on the same inputs. `sbox_ok` then gives, at every bit position `p`, the
S-box of the byte formed by bit `p` of the planes in slots `0 … 7`.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb tmpRegs)
open VG.Proof.Sm4
open VG.Proof.Sm4.W32 (bsByte getLsbD_bsByte)

/-- The S-box's memory: its planes and spill slots, at `edi`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

/-- Slot `j` of the scratch buffer. -/
abbrev slotW (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) j) 32

def sboxEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if k < 8 then some (inT k) else none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some (sboxT j)

theorem sbox_check :
    check (table 32 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

/-- The registers the layers may write. -/
theorem not_tmp (r : Reg) (hr : r ∉ tmpRegs) : r ∈ [Reg.esp, .esi, .edi] := by
  revert hr; cases r <;> decide

/-- The S-box, at every bit position of the planes in slots `0 … 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32, (slotW s' j).getLsbD p = (sboxB (bsByte (slotW s) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.slot j = some (sboxT j) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 32, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (slotW s) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (slotW s) p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a _ h => ?_,
      (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv] at h
    split at h
    · rename_i hk8
      cases h
      simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
        BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, slotW, sboxCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (slotW s) p).isLt
    have := p₁.rel.slot j _ (by simp [sboxCfg]; omega) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, sboxCfg, hb] at this
    rw [slotW, hb, ← this, sboxT, testBit_tableOf]
    simp [hc]
  · have h : ([Reg.esp, .esi, .edi].all fun r => sboxCode.all fun i => i.dst != some r) = true := by
      decide +kernel
    simp [List.all_eq_true.mp h r (not_tmp r hr)]

end VG.Proof.Sm4.X86
