module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableStep
public import VerifiedGarbage.Proof.MillerRabin.X86.TableInit
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # The public fourteen-iteration power-table loop -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

abbrev tablePower (σ : State) (base : Addr) (w i : Nat) : Nat :=
  VG.Proof.MillerRabin.Math.tp (val32 σ.mem base 256 (2 * w)) w
    (numAt σ.mem base w 5) (numAt σ.mem base w 9) i

structure TableState (σ : State) (base : Addr) (bytes w n : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  bounded : n ≤ 14
  count : w32 s.mem base sK = 14 - n
  cursor : s.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w (13 + n))
  witness : numAt s.mem base w 5 = numAt σ.mem base w 5
  accumulator : numAt s.mem base w 6 = tablePower σ base w (n + 1)
  table : ∀ i, i < n + 2 → numAt s.mem base w (11 + i) = tablePower σ base w i

theorem table_state_step {σ s : State} {base : Addr} {bytes w n : Nat}
    (facts : RoundFacts σ base bytes w) (hn : n < 14) (h : TableState σ base bytes w n s) :
    WP isa tabStep s fun t => TableState σ base bytes w (n + 1) t ∧
      t.zf = some (decide (n + 1 = 14)) := by
  have count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 (14 - n) := by
    apply BitVec.eq_of_toNat_eq
    change w32 s.mem base sK = _
    rw [h.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (table_step facts h.stage (j := 13 + n) (k := 14 - n)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ h.witness h.cursor count) ?_
  rintro t ⟨ht, countT, zt, cursorT, acc, appended, same⟩
  have next : numAt t.mem base w 6 = tablePower σ base w (n + 1 + 1) := by
    rw [h.accumulator] at acc
    exact acc
  refine ⟨⟨ht, by omega, ?_, ?_, ?_, next, ?_⟩, ?_⟩
  · simpa only [show 14 - n - 1 = 14 - (n + 1) by omega] using countT
  · simpa only [show 13 + n + 1 = 13 + (n + 1) by omega] using cursorT
  · exact (same 5 (by decide) (by decide) (by decide) (by omega)).trans h.witness
  · intro i hi
    by_cases last : i = n + 2
    · have index : 11 + i = 13 + n := by omega
      rw [index, appended, next, last]
    · exact (same (11 + i) (by omega) (by omega) (by omega) (by omega)).trans
        (h.table i (by omega))
  · rw [zt]
    congr 1
    exact decide_eq_decide.mpr (by omega)

theorem table_loop {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : TableState σ base bytes w 0 s) :
    WP isa (.loop tabStep .ne) s (TableState σ base bytes w 14) :=
  VG.Proof.Bignum.X86.PublicRt.countLoop (by decide) (TableState σ base bytes w)
    (fun _ _ hn hi => table_state_step facts hn hi) h

theorem table_start {σ : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ σ) :
    WP isa tabInit σ (TableState σ base bytes w 0) := by
  refine WP.mono (table_init h facts.lower facts.upper facts.fit facts.width) ?_
  rintro t ⟨ht, count, cursor, one, first, acc, witness⟩
  refine ⟨ht, by decide, count, cursor, witness, acc, ?_⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact one
  · exact first

end VG.Proof.MillerRabin.X86
