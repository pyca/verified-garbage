module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
/-! # A rejected candidate advances the native search invariant -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchReject.lean`, which only this module imported.
section

/-! # Native byte accounting and budget decrement after candidate rejection -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def rejectValues (p : SearchPublic) (used remaining : Nat) (consumed : BitVec 64) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 used + consumed), (10, off p.c.rp used + consumed),
    (11, BitVec.ofNat 64 (p.c.rand.length - used) - consumed),
    (0, BitVec.ofNat 64 remaining - 1), (14, 4)]

theorem reject_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block reject) s fun t =>
      t.mem = writeController s.mem p.control (rejectValues p used remaining consumed) ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hs0 : InRegions s.wr p.control 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hl0 : InRegions (s.rd ++ s.wr) p.control 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hup : InRegions (s.rd ++ s.wr) p.c.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_memory h.wr).ld (d := 0) (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used remaining) :
      s.mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv7 := hv 7 p.c.up (by simp [SearchPublic.headers])
  have hv12 := hv 12 (BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have hv10 := hv 10 (off p.c.rp used) (by simp [SearchPublic.headers])
  have hv11 := hv 11 (BitVec.ofNat 64 (p.c.rand.length - used)) (by simp [SearchPublic.headers])
  have hv0 : s.mem.readW p.control 64 = BitVec.ofNat 64 remaining := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using hv 0 (BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  have other (i j : Nat) (hi : i < 16) (hj : j < 16) (hne : i ≠ j) :=
    fun (m : Mem) (v : BitVec 64) => controller_read_other m p.control v (i := i) (j := j) hi hj hne
  have other0 (i : Nat) (hi : i < 16) (hne : i ≠ 0) (m : Mem) (v : BitVec 64) :
      (m.writeW (p.control + BitVec.ofNat 64 (8 * i)) v).readW p.control 64 = m.readW p.control 64 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using other i 0 hi (by decide) hne m v
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold reject writeController rejectValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    BitVec.add_zero, hs0, hl0, hup, hu, hv7, hv12, hv10, hv11, hv0,
    hl 56 (by decide), hl 96 (by decide), hl 80 (by decide), hl 88 (by decide),
    hs 96 (by decide), hs 80 (by decide), hs 88 (by decide), hs 112 (by decide),
    other 12 10 (by decide) (by decide) (by decide), other 12 11 (by decide) (by decide) (by decide),
    other 10 11 (by decide) (by decide) (by decide), other0 12 (by decide) (by decide),
    other0 10 (by decide) (by decide), other0 11 (by decide) (by decide)]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.MlKem.X86_64

theorem rejectValues_bound (p : SearchPublic) (used remaining : Nat) (n : BitVec 64) :
    ∀ e ∈ rejectValues p used remaining n, e.1 < 16 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem reject_headers {p : SearchPublic} {original s : State} {used remaining n : Nat}
    (h : SearchLive p original used remaining s) (hn : n ≤ p.c.rand.length - used)
    (hr : 0 < remaining) :
    Slots (writeController s.mem p.control (rejectValues p used remaining (BitVec.ofNat 64 n)))
      p.control (p.headers (used + n) (remaining - 1)) := by
  have ht := h.input.tape_lt
  have hr64 : remaining < 2 ^ 64 := by
    have hb : p.remaining < 2 ^ 64 := by
      cases h.input.2
      exact (original.mem.readW (stackArg original 3) 64).isLt
    omega_using [h.remaining_le, hb]
  have hn64 : n < 2 ^ 64 := by omega_using [hn, ht]
  have hh := h.headers
  simp only [Slots, SearchPublic.headers, List.forall_mem_cons] at hh
  obtain ⟨h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15, _⟩ := hh
  have hd : BitVec.ofNat 64 (p.c.rand.length - used) - BitVec.ofNat 64 n =
      BitVec.ofNat 64 (p.c.rand.length - (used + n)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ hn64 hn]
    congr 1
    omega
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (rejectValues_bound p used remaining _) _ (by dsimp only; decide)] <;>
    simp only [rejectValues, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false, h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15,
      hd, ofNat64_pred hr hr64, off, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Ffdh.X86_64.Generation
