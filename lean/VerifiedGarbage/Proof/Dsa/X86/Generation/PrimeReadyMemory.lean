module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset

/-! # Returning to the search frame retains the prepared modulus and constants -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem PrimeReady.sameWorkspace {G : PrimeConfig} {s t : State} {regs : List Reg}
    (R : PrimeReady G s)
    (same : ∀ d, d + 4 ≤ G.size → t.mem.readW (off G.base d) 32 = s.mem.readW (off G.base d) 32)
    (K : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) : PrimeReady G t := by
  have room := G.room
  have width := G.width
  change primeExponent + 8 * G.n ≤ G.size at room
  have value (d k : Nat) (fits : d + 4 * k ≤ G.size) : val32 t.mem G.base d k = val32 s.mem G.base d k := by
    apply val32_congr
    intro j hj
    exact congrArg BitVec.toNat (same (d + 4 * j) (by omega))
  have slotValue (i : Nat) (hi : i < 9) : wordsVal t.mem G.base (slot G.n i) G.n = wordsVal s.mem G.base (slot G.n i) G.n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply value
    have := slot_bound (n := G.n) hi
    have := R.context.size_le
    unfold stride at *
    omega
  have inv : w32 t.mem G.base 0 = w32 s.mem G.base 0 := congrArg BitVec.toNat (same 0 (by unfold primeExponent at room; omega))
  have C : Context G.n G.modulus G.base G.size t := ⟨R.context.scr.of_keeps K di sp, R.context.size_le,
    ⟨R.context.modulus.n0, R.context.modulus.mo, R.context.modulus.tmp, R.context.modulus.sep,
      (slotValue 0 (by decide)).trans R.context.modulus.val⟩, R.context.gt_one, by rw [inv]; exact R.context.inverse⟩
  exact ⟨C, (slotValue 3 (by decide)).trans R.one, (slotValue 4 (by decide)).trans R.r2,
    (value primeExponent (2 * G.n) (by omega)).trans R.exponent,
    (same primeTwos (by unfold primeTwos primeExponent at *; omega)).trans R.twos,
    (same primeTape (by unfold primeTape primeExponent at *; omega)).trans R.tape,
    (same primeTapeLen (by unfold primeTapeLen primeExponent at *; omega)).trans R.tapeLen,
    (same primeWitness (by unfold primeWitness primeExponent at *; omega)).trans R.witness,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.tapeRead i hi,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.witnessRead i hi,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.witnessReadByte i hi,
    by intro i hi; rw [K.2.2]; exact R.witnessWrite i hi⟩
theorem PrimeReady.frame {G : PrimeConfig} {s t : State} {regs : List Reg} {rs : List Region}
    (R : PrimeReady G s) (O : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, (⟨G.base, G.size⟩ : Region).Disjoint r)
    (K : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs) : PrimeReady G t := by
  apply R.sameWorkspace ?_ K di sp
  intro d hd
  exact O.readW (r := ⟨G.base, G.size⟩)
    (Offset.contains_base _ hd (by have := R.context.scr.nowrap; omega)) apart (by decide)

end VG.Proof.Dsa.X86.Generation
