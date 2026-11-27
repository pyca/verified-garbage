module

-- separate module: checked once for all who use the S-box's circuit on slices
public import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK

/-!
# The bitsliced S-box on PPC64LE

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 64 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's S-box on the same tables (`Proof/Aes/Sbox0.lean`).
`sbox_ok` then gives, at every bit position `p`, the S-box of the byte formed
by bit `p` of the eight words.
-/

@[expose] public section

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Aes.PPC64LE VG.Proof.Aes

/-- The S-box's memory: its spill slots, at `r8`. -/
def sboxCfg : Cfg := { base := sb, slots := 40, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map sbIn, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sboxOfT.getD j 0)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

/-- The registers the S-box writes. -/
def sboxWrites : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, .r22, .r23, .r24, .r25,
  .r26, .r27, .r28, .r29, .r30, .r31, .r0, .r9]

/-- The registers outside `sboxWrites`. -/
def restRegs : List Reg := [.r2, .r3, .r4, .r5, .r6, .r7, .r8, .r10, .r11, .r12]

theorem sbox_writes_rest :
    restRegs.all (fun r => sboxCode.all fun i => dstOf i != some r) = true := by
  decide +kernel

theorem not_sboxWrites (r : Reg) (hr : r ∉ sboxWrites) : r ∈ restRegs := by
  revert hr; cases r <;> decide

theorem sbox_writes (r : Reg) (hr : r ∉ sboxWrites) :
    (sboxCode.all fun i => dstOf i != some r) = true :=
  List.all_eq_true.mp sbox_writes_rest r (not_sboxWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (Spec.Aes.sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (sboxOfT.getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 64, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => dstOf i != some r) = false) := by
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
    simp only [TableRel, sbIn, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, sboxOfT_bit hc hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp [sbox_writes r hr]

end VG.Proof.Aes.PPC64LE
