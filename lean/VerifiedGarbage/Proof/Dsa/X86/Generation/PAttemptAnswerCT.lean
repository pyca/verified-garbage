module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptOffsetCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttemptCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchValue

/-! # Relate the public outcome of each complete p-search attempt -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pAttempt_answer {H : Hash} (K : HashOK H) {P : PSearchPlan} {p : PSearchPublic P}
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length)
    {s : State} (Hpre : PAttemptAt P p.counter p.used s) :
    WP isa (pAttempt H P.context.geometry.pLen P.context.geometry.qLen) s (PAttemptAnswered P p) := by
  obtain ⟨⟨W, R, cursor⟩, C⟩ := Hpre
  have shape := P.value_shape p.counter hashSize
  refine WP.mono (pAttempt_ok K R.context R.seed P.seedLength digest final p.counterBound C R.source cursor p.usedBound
    R.qval P.qPositive P.qBound hash hashSize shape.1 shape.2)
    fun t ⟨Wt, result, Rt, source, seedCursor, cursorT, _, seedT, qvalT, _, _, outcome, Ct, status, _, _⟩ => ?_
  have known := outcome.public
  change result.status = p.result.1 ∧ (result.status ≠ 0 → result.used = p.result.2) at known
  refine ⟨⟨Wt, result.used, ⟨Rt, seedT, source, qvalT, seedCursor.trans R.seedUsed⟩,
    cursorT, outcome.bound, fun nz => known.2 (by rw [known.1]; exact nz)⟩, ?_⟩
  refine ⟨⟨Ct, p.counterBound, ?_⟩, rfl, ?_, ?_⟩
  · have := P.context.geometry.width; omega
  · change p.result.1 ≤ 3
    rw [← known.1]
    rcases outcome.status with h | h | h <;> omega
  · change t.mem.readW _ 32 = BitVec.ofNat 32 p.result.1
    exact status.trans (congrArg (BitVec.ofNat 32) known.1)

theorem pAttempt_answer_ct {H : Hash} (K : HashOK H) (P : PSearchPlan)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (p : PSearchPublic P) => PAttemptAt P p.counter p.used)
      (pAttempt H P.context.geometry.pLen P.context.geometry.qLen) (Two (PAttemptAnswered P)) := by
  refine two_post ?_ (fun _ _ h => pAttempt_answer K digest final hash hashSize h)
  intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
  exact pAttempt_ct K P p.counter p.used digest final p.counterBound p.usedBound hash hashSize
    s t ts tt s' t' ⟨(), hs, ht⟩ es et
end VG.Proof.Dsa.X86.Generation
