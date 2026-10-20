module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRejectHeaders
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchUpdate

/-! # A native rejection continues with smaller budgets and the exact suffix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_reject_step {p : SearchPublic} {original s : State} {used remaining n : Nat}
    (h : SearchLive p original used remaining s) (hn : n ≤ p.c.rand.length - used)
    (hr : 0 < remaining) (hu : s.mem.readW p.c.up 64 = BitVec.ofNat 64 n) :
    WP isa (.block reject) s fun t =>
      SearchLive p original (used + n) (remaining - 1) t ∧ word t.mem p.control 112 = 4 := by
  refine WP.mono (reject_ok h (BitVec.ofNat 64 n) hu) fun t ⟨hm, k⟩ => ?_
  have hb := rejectValues_bound p used remaining (BitVec.ofNat 64 n)
  have h4 : ∀ e ∈ rejectValues p used remaining (BitVec.ofNat 64 n), 4 ≠ e.1 := by
    simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.control_update (by omega_using [hn, h.used_le])
    (by omega_using [h.remaining_le]) _ hb h4 hm k.2.1 k.2.2
    (fun reg hr => k.gpr (by cases reg <;> simp_all [calleeSaved]))
    (by rw [hm]; exact reject_headers h hn hr), ?_⟩
  rw [hm]
  change word (writeController s.mem p.control (rejectValues p used remaining (BitVec.ofNat 64 n)))
    p.control (8 * 14) = _
  rw [writeController_word _ _ _ hb 14 (by decide)]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
