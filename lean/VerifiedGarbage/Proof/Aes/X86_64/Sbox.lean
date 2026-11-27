module

public import VerifiedGarbage.Impl.Aes.X86_64.Sbox
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Aes.X86_64.Sbox
meta import VerifiedGarbage.Proof.Aes.Sbox0
meta import VerifiedGarbage.Proof.Framework.X86_64.Straight
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# The bitsliced AES S-box on x86-64's general registers

`sboxCode` works on each bit position by itself, so the kernel evaluates it
once on the truth tables of the 256 inputs (`sbox_check`). `sbox_ok`: at
every bit position, the S-box of the byte the eight words have there.
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64
open VG.Proof.Aes

/-- The S-box's memory: its spill slots, at `r9`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map sbIn, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sboxOfT.getD j 0)

theorem sbox_check : check (table 64 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

/-- The registers the S-box writes. -/
def sboxWrites : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, t0, t1]

theorem sbox_writes_rest :
    [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all (fun r => sboxCode.all fun i => i.dst != some r) = true := by
  decide +kernel

theorem sbox_writes (r : Reg) (hr : r ∉ sboxWrites) : (sboxCode.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp sbox_writes_rest r (by revert hr; cases r <;> decide)

theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (Spec.Aes.sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (sboxOfT.getD j 0) := fun j hj => by
    simpa using List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  -- The run at bit position `p`.
  have key : ∀ p < 64, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqk := List.find?_some hk
    have hk8 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, sbIn, testBit_tableOf, hc, decide_true, Bool.true_and, BitVec.testBit_toNat,
      getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r (by simp [sbox_writes r hr]), p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key p hp
  obtain rfl := run_unique hs'' hs'
  have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
  have := p₁.rel.reg (q j) _ (hout j hj)
  simp only [TableRel] at this
  rw [← this, sboxOfT_bit hc hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Aes.X86_64
