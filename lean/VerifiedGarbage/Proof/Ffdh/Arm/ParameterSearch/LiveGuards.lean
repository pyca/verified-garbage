module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CounterMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Counter
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Compare
import VerifiedGarbage.Proof.Ffdh.Arm.Block
/-! Every native decision reads only proven public counters and lengths. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/Guard.lean`, which only this module imported.
section

/-! Exhaustion tests both native halves of the attempt counter. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

theorem guard_ok (s : State) {base : BitVec 32} {n : Nat} (h : Controller base s)
    (bound : n ≤ 2 ^ 32) (counter : s.mem.readW (State.addr base) 64 = BitVec.ofNat 64 n) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
      VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard)) s fun t =>
      (t.z = decide (n = 0) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10] s t := by
  have fits : n < 2 ^ 64 := by omega
  have lo := packedLow s.mem base 0 n fits (by simpa [off] using counter)
  have hi := packedHigh s.mem base 0 n fits (by simpa [off] using counter)
  rw [WP.block_append_iff]
  refine WP.mono (counterLoads_ok s h) ?_
  rintro u ⟨⟨lowU, highU, memU⟩, restU⟩
  refine WP.mono (budgetGuard_ok u bound (lowU.trans lo) (highU.trans hi)) ?_
  rintro t ⟨⟨zero, memT⟩, restT⟩
  exact ⟨⟨zero, memT.trans memU⟩, restU.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/FieldGuard.lean`, which only this module imported.
section

/-! Compare two public native controller fields without changing memory. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

theorem fieldLoads_ok (s : State) {base : BitVec 32} {i j : Nat}
    (h : Controller base s) (hi : i < 16) (hj : j < 16) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 i,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 j]) s fun t =>
      (t.gpr .r9 = lowWord s.mem base i ∧ t.gpr .r10 = lowWord s.mem base j ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10] s t := by
  refine withRest_all [.r9, .r10] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord
  ffrun [show 8 * i < 4096 by omega, show 8 * j < 4096 by omega,
    h.addr hi, h.addr hj, h.read hi, h.read hj]

theorem fieldGuard_ok (s : State) {base : BitVec 32} {i j x y : Nat}
    (h : Controller base s) (hi : i < 16) (hj : j < 16)
    (xFits : x < 2 ^ 32) (yFits : y < 2 ^ 32)
    (left : lowWord s.mem base i = BitVec.ofNat 32 x)
    (right : lowWord s.mem base j = BitVec.ofNat 32 y) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 i,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 j] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s fun t =>
      (t.z = decide (x < y) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10, .r11] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldLoads_ok s h hi hj) ?_
  rintro u ⟨⟨loadX, loadY, memU⟩, restU⟩
  refine WP.mono (less_ok u) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  rw [loadX, loadY, left, right, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt xFits, Nat.mod_eq_of_lt yFits] at flag
  exact ⟨⟨flag, memT.trans memU⟩, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.budget_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
      VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard)) s fun t =>
      (SearchLive p used remaining t ∧ t.z = decide (remaining = 0) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10] s t := by
  refine WP.mono (guard_ok s h.buffers.controller h.remaining_bound h.counter) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

theorem SearchLive.length_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s fun t =>
      (SearchLive p used remaining t ∧ t.z = decide (p.c.bytes.length - used < p.c.length) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r11] s t := by
  have tape := h.saved 10 (by simp [searchSlots])
  have width := h.saved 1 (by simp [searchSlots])
  simp only [searchValues] at tape width
  refine WP.mono (fieldGuard_ok s h.buffers.controller (by decide : 10 < 16) (by decide : 1 < 16)
    (by have := p.c.tapeCount; omega) (by have := p.width_bounds; omega) tape width) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

theorem SearchLive.entropy_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s fun t =>
      (SearchLive p used remaining t ∧
        t.z = decide (p.c.bytes.length - used < Spec.Ffdh.parameterEntropy p.c.bits) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r11] s t := by
  have tape := h.saved 10 (by simp [searchSlots])
  have cap := h.saved 2 (by simp [searchSlots])
  simp only [searchValues] at tape cap
  refine WP.mono (fieldGuard_ok s h.buffers.controller (by decide : 10 < 16) (by decide : 2 < 16)
    (by have := p.c.tapeCount; omega) p.entropy_fits tape cap) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
