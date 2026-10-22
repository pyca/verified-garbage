module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableLoop
public import VerifiedGarbage.Proof.MillerRabin.X86.Window
public import VerifiedGarbage.Proof.MillerRabin.X86.WordDigit

/-! # The exponent-window run and its reusable operational invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

abbrev roundRun (σ : State) (base : Addr) (w n : Nat) : Nat × Bool :=
  VG.Proof.MillerRabin.Math.mrun (val32 σ.mem base 256 (2 * w)) w (numAt σ.mem base w 10)
    (tablePower σ base w) (numAt σ.mem base w 27) (16 * w) n

structure RunState (σ : State) (base : Addr) (bytes w n : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  count : w32 s.mem base sK = 16 * w - n
  value : numAt s.mem base w 6 = (roundRun σ base w n).1
  flag : w32 s.mem base sF = (roundRun σ base w n).2.toNat
  reduced : numAt s.mem base w 6 < val32 σ.mem base 256 (2 * w)
  minus : numAt s.mem base w 8 = numAt σ.mem base w 10
  table : ∀ i, i < 16 → numAt s.mem base w (11 + i) = tablePower σ base w i

theorem RunState.of_memory {σ s t : State} {base : Addr} {bytes w n : Nat}
    (h : RunState σ base bytes w n s) (stage : Stage base bytes w σ t) (mem : t.mem = s.mem) :
    RunState σ base bytes w n t := by
  exact ⟨stage, by rw [mem]; exact h.count, by rw [mem]; exact h.value,
    by rw [mem]; exact h.flag, by rw [mem]; exact h.reduced, by rw [mem]; exact h.minus,
    by rw [mem]; exact h.table⟩

theorem run_window {σ s : State} {base : Addr} {bytes w n : Nat} {v : BitVec 32}
    (facts : RoundFacts σ base bytes w) (h : RunState σ base bytes w n s) (hn : n < 16 * w)
    (word : s.mem.readW (off base sV) 32 = v)
    (digit : v >>> 28 = BitVec.ofNat 32
      (numAt σ.mem base w 27 / 16 ^ (16 * w - 1 - n) % 16)) :
    WP isa win s fun t => RunState σ base bytes w (n + 1) t ∧
      t.mem.readW (off base sV) 32 = v <<< 4 ∧
      t.zf = some (decide ((16 * w - (n + 1)) % 8 = 0)) := by
  have upper := facts.upper
  have pos : 0 < val32 σ.mem base 256 (2 * w) := by have := facts.odd; omega
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  have headers : WindowHeaders s.mem base v (16 * w - n) (roundRun σ base w n).2 :=
    ⟨word, readW_of_w32 (by omega) h.count, readW_of_w32 (boolSmall _) h.flag⟩
  have tableLt : ∀ i, i < 16 → tablePower σ base w i < val32 σ.mem base 256 (2 * w) := by
    intro i _
    exact VG.Proof.MillerRabin.Math.tp_lt pos facts.witness facts.one i
  refine WP.mono (window_ok facts h.stage headers (Nat.mod_lt _ (by decide))
    ⟨by omega, by omega⟩ digit h.table tableLt h.reduced) ?_
  rintro t ⟨ht, valueT, flagT, wordT, countT, zeroT, same⟩
  rw [h.minus, h.value] at valueT flagT
  have valueNext : numAt t.mem base w 6 = (roundRun σ base w (n + 1)).1 := valueT
  have flagNext : w32 t.mem base sF = (roundRun σ base w (n + 1)).2.toNat := flagT
  refine ⟨⟨ht, ?_, valueNext, flagNext, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [show 16 * w - n - 1 = 16 * w - (n + 1) by omega] using countT
  · rw [valueT]
    exact VG.Proof.MillerRabin.Math.mm_lt pos
  · exact (same 8 (by decide) (by decide) (by decide) (by decide)).trans h.minus
  · intro i hi
    exact (same (11 + i) (by omega) (by omega) (by omega) (by omega)).trans (h.table i hi)
  · exact BitVec.eq_of_toNat_eq wordT
  · simpa only [show 16 * w - n - 1 = 16 * w - (n + 1) by omega] using zeroT

end VG.Proof.MillerRabin.X86
