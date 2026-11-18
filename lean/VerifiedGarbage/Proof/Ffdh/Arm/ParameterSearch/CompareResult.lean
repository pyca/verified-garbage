module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Compare
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-! ### `Ffdh.Arm.ParameterSearch.CandidateFacts`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.Result`, which this module and modules that import it used -/

section

/-! Each native transition preserves the shared complete-search result. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Spec.Ffdh VG.Proof.Ffdh.SievedGeneration VG.Proof.Ffdh.ParameterCandidate

theorem candidateUsed_bound (p : SearchParams) (used : Nat) :
    candidateUsed p used ≤ p.c.bytes.length - used := by
  unfold candidateUsed
  split <;> omega_using []

theorem candidate_short (p : SearchParams) (used : Nat)
    (short : p.c.bytes.length - used < p.c.length) : candidateResult p used = none := by
  unfold candidateResult
  unfold Spec.Ffdh.sievedParameterCandidate
  have draw := draw_of_short (r := p.c.bytes.drop used) (len := p.c.length)
    (by simpa only [List.length_drop] using short)
  change VG.Spec.RsaKeyGen.draw ((p.c.bits + 7) / 8) (p.c.bytes.drop used) = none at draw
  rw [draw]
  rfl

theorem SearchParams.tail_short {p : SearchParams} {used remaining : Nat} (positive : 0 < remaining)
    (candidate : candidateResult p used = none) :
    p.tail used remaining = if Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.bytes.length - used
      then .exhausted used else .entropy remaining (p.c.bytes.length - used) used := by
  cases remaining with
  | zero => omega
  | succ n =>
    unfold SearchParams.tail
    rw [sievedParameterSearch]
    change sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used) = _ at candidate
    rw [candidate]
    simp only [List.length_drop]
    split <;> rfl

theorem SearchParams.tail_accept {p : SearchParams} {used remaining prime : Nat}
    {rest : VG.Spec.RsaKeyGen.Rand} (positive : 0 < remaining)
    (candidate : candidateResult p used = some (some prime, rest)) :
    p.tail used remaining = .accepted prime (used + candidateUsed p used) := by
  cases remaining with
  | zero => omega
  | succ n =>
    unfold SearchParams.tail
    rw [sievedParameterSearch]
    change sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used) = _ at candidate
    rw [candidate]
    simp only [List.length_drop, ParameterSearchResult.consume, candidateUsed, candidateResult, candidate]

theorem SearchParams.tail_reject {p : SearchParams} {used remaining : Nat}
    {rest : VG.Spec.RsaKeyGen.Rand} (positive : 0 < remaining)
    (candidate : candidateResult p used = some (none, rest)) :
    p.tail used remaining = p.tail (used + candidateUsed p used) (remaining - 1) := by
  have step := search_reject positive candidate
  simpa only [SearchParams.tail, candidateUsed, candidate, List.length_drop] using step

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! The candidate's public result supplies the exact native consumption field and classification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem CandidatePost.consumed_low {p : SearchParams} {used : Nat} {s : State}
    (post : CandidatePost p used s) : lowWord s.mem p.control 14 = BitVec.ofNat 32 (candidateUsed p used) := by
  have result := post.consumed
  change [s.mem.readW (State.addr (p.control + 112#32) + 0#64) 64] =
    [BitVec.ofNat 64 (candidateUsed p used)] at result
  rw [BitVec.add_zero, List.singleton_inj, p.used_addr] at result
  exact packedLow s.mem p.control 14 (candidateUsed p used)
    (by have := candidateUsed_bound p used; have := p.c.tapeCount; omega_arith) result

theorem CandidatePost.after_read {p : SearchParams} {used : Nat} {s t : State} {rs : List Reg}
    (post : CandidatePost p used s) (mem : t.mem = s.mem) (rest : Rest rs s t) (kept : .r0 ∉ rs) :
    CandidatePost p used t :=
  ⟨by rw [rest.gpr .r0 kept]; exact post.status, by rw [mem]; exact post.output,
    by rw [mem]; exact post.consumed⟩

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.LiveGuards`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.CounterMemory`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.Counter`, which this module and modules that import it used -/

section

/-! The 8192-bit safe-prime budget is 2^32: its first decrement borrows
from the high word rather than treating the low word's zero as exhaustion. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem decrementWords_ok (s : State) {n : Nat} (positive : 0 < n) (bound : n ≤ 2 ^ 32)
    (low : s.gpr .r9 = BitVec.ofNat 32 n)
    (high : s.gpr .r10 = BitVec.ofNat 32 (n / 2 ^ 32)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 32 (n - 1) ∧
        t.gpr .r10 = BitVec.ofNat 32 ((n - 1) / 2 ^ 32) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r12] s t := by
  have lower : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by
    change BitVec.ofNat 32 n - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  have noborrow : decide (1 ≤ (BitVec.ofNat 32 n).toNat) = decide (n < 2 ^ 32) := by
    by_cases small : n < 2 ^ 32
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
      simp only [show 1 ≤ n by omega_using [positive], small, decide_true]
    · have full : n = 2 ^ 32 := by omega_using [bound, small]
      subst n
      rfl
  have upper : BitVec.ofNat 32 (n / 2 ^ 32) - 1 +
      (if n < 2 ^ 32 then 1 else 0) = BitVec.ofNat 32 ((n - 1) / 2 ^ 32) := by
    by_cases small : n < 2 ^ 32
    · rw [ite_eq_left small, Nat.div_eq_of_lt small,
        Nat.div_eq_of_lt (by omega_using [bound] : n - 1 < 2 ^ 32)]
      rfl
    · have full : n = 2 ^ 32 := by omega_using [bound, small]
      subst n
      rfl
  refine withRest_all [.r9, .r10, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords
  ffrun [low, high, lower, noborrow, upper,
    show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add,
    show (1 : BitVec 32).toNat = 1 from rfl, decide_eq_true_eq]
  exact upper

theorem budgetGuard_ok (s : State) {n : Nat} (bound : n ≤ 2 ^ 32)
    (low : s.gpr .r9 = BitVec.ofNat 32 n)
    (high : s.gpr .r10 = BitVec.ofNat 32 (n / 2 ^ 32)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard) s fun t =>
      (t.z = decide (n = 0) ∧ t.mem = s.mem) ∧ Rest [.r9] s t := by
  have zero : ((BitVec.ofNat 32 n ||| BitVec.ofNat 32 (n / 2 ^ 32)) == (0 : BitVec 32)) =
      decide (n = 0) := by
    by_cases small : n < 2 ^ 32
    · rw [Nat.div_eq_of_lt small]
      change ((BitVec.ofNat 32 n ||| 0#32) == (0 : BitVec 32)) = _
      rw [BitVec.or_zero, VG.Proof.X25519.Arm.ofNat_beq_zero small]
    · have full : n = 2 ^ 32 := by omega_using [bound, small]
      subst n
      rfl
  refine withRest_all [.r9] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard
  ffrun [low, high, show (0 : BitVec 32) = 0#32 from rfl, BitVec.sub_zero]
  exact zero

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! Load, decrement and store the entire native u64 attempt budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

theorem counterLoads_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4]) s fun t =>
      (t.gpr .r9 = lowWord s.mem base 0 ∧ t.gpr .r10 = s.mem.readW (off (State.addr base) 4) 32 ∧ t.mem = s.mem) ∧
      Rest [.r9, .r10] s t := by
  refine withRest_all [.r9, .r10] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord
  ffrun [controllerAddr h 0 (by decide), controllerAddr h 4 (by decide),
    h.space.read (off := 0) (by decide), h.space.read (off := 4) (by decide)]

theorem decrement_ok (s : State) {base : BitVec 32} {n : Nat} (h : Controller base s)
    (positive : 0 < n) (bound : n ≤ 2 ^ 32)
    (counter : s.mem.readW (State.addr base) 64 = BitVec.ofNat 64 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.decrement) s fun t =>
      t.mem = s.mem.writeW (State.addr base) (BitVec.ofNat 64 (n - 1)) ∧ Rest [.r9, .r10, .r12] s t := by
  have fits : n < 2 ^ 64 := by omega_using [bound]
  have lo : lowWord s.mem base 0 = BitVec.ofNat 32 n :=
    packedLow s.mem base 0 n fits (by simpa [off] using counter)
  have hi : s.mem.readW (off (State.addr base) 4) 32 = BitVec.ofNat 32 (n / 2 ^ 32) :=
    packedHigh s.mem base 0 n fits (by simpa [off] using counter)
  change WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
    (VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords ++
      [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r9 0, .str .r10 .r4 4]))) s _
  rw [WP.block_append_iff]
  refine WP.mono (counterLoads_ok s h) ?_
  rintro u ⟨⟨lowU, highU, memU⟩, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (decrementWords_ok u positive bound (lowU.trans lo) (highU.trans hi)) ?_
  rintro v ⟨⟨lowV, highV, memV⟩, restV⟩
  have restUV : Rest [.r9, .r10, .r12] s v := (restU.mono (by simp)).trans restV
  have context : Controller base v :=
    ⟨h.space.congr restUV.wr, (restUV.gpr .r4 (by simp)).trans h.ptr⟩
  have raw : WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r9 0, .str .r10 .r4 4]) v fun t =>
      t.mem = s.mem.writeW (State.addr base) (BitVec.ofNat 64 (n - 1)) ∧ Rest [] v t := by
    refine withRest_all [] ?_ (by rfl) (by rfl)
    unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
    ffrun [controllerAddr context 0 (by decide), controllerAddr context 4 (by decide),
      context.space.write (off := 0) (by decide), context.space.write (off := 4) (by decide),
      lowV, highV, memV, memU]
    simpa [off] using writeCounter s.mem base (n - 1) (by omega_using [bound])
  exact WP.mono raw (fun _ post => ⟨post.1, restUV.trans (post.2.mono (by simp))⟩)

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

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
    (by have := p.c.tapeCount; omega_using [this]) (by have := p.width_bounds; omega_using [this]) tape width) ?_
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
    (by have := p.c.tapeCount; omega_using [this]) p.entropy_fits tape cap) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! Public candidate status comparison changes only flags. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem compareResult_ok (s : State) {status test : Nat} (small : status < 3)
    (which : test = 1 ∨ test = 2) (value : s.gpr .r0 = BitVec.ofNat 32 status) :
    WP isa (.block [.cmp .r0 (.imm (BitVec.ofNat 32 test))]) s fun t =>
      (t.z = decide (status = test) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by
    intro r _ i hi
    simp only [instrs, List.mem_singleton] at hi
    subst i
    rfl) (by rfl)
  have choices : status = 0 ∨ status = 1 ∨ status = 2 := by omega_using [small]
  rcases which with rfl | rfl
  all_goals ffrun [value]
  all_goals rcases choices with rfl | rfl | rfl <;> rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
