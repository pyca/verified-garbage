module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterSemantics
import VerifiedGarbage.Proof.Framework.Omega

/-! # Each native seed iteration advances the seed and witness tapes exactly -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem parameter_body_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    {p : GenerationContext} {expected : Option Spec.Dsa.Params} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : ParameterInvariant p expected initial used s) (room : used + p.geo.qLen ≤ p.seeds.bytes.length)
    (R : Rep s.mem p.geo.F p.geo.hash V W) (Lt : Lay t p.geo.F p.geo.hash)
    (Rt : Rep t.mem p.geo.F p.geo.hash V
      (upd (upd W 1 (off (W 8) used)) 10 (BitVec.ofNat 64 (used + p.geo.qLen))))
    (ft : Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem) (kt : Keep [.rax, .rcx] s t) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAttempt H.sha1 H.sha256 Sq.mm M.mm K.run p.geo.pLen p.geo.qLen) t fun u =>
      ∃ V' W', Lay u p.geo.F p.geo.hash ∧ Rep u.mem p.geo.F p.geo.hash V' W' ∧
        (if W' 19 = 3 then ParameterInvariant p expected initial (used + p.geo.qLen) u
          else ParameterFinished p expected initial u) := by
  obtain ⟨Wi, randUsed, h, bound, _, h16, he, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 37, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  let Wt := upd (upd W 1 (off (W 8) used)) 10 (BitVec.ofNat 64 (used + p.geo.qLen))
  have ff := p.frame_single ft
  have ht : GenerationMemory p Wt t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Wt, upd] <;> exact words _ (by decide)) ff kt.2.1 kt.2.2
  let seed := p.seeds.slice used p.geo.qLen room
  have hlen : seed.bytes.length = p.geo.qLen := by
    change ((p.seeds.bytes.drop used).take p.geo.qLen).length = p.geo.qLen
    simp only [List.length_take, List.length_drop, Nat.min_eq_left (by omega : p.geo.qLen ≤ p.seeds.bytes.length - used)]
  have h1 : Wt 1 = seed.ptr := by
    have h8 := (h.slots 8 (by simp [generationSlots])).trans p.seedsSlot
    simp [Wt, upd, words 8 (by decide), h8, seed, GenerationTape.slice]
  have ht16 : Wt 16 = BitVec.ofNat 64 randUsed := by
    simpa [Wt, upd, words 16 (by decide)] using h16
  refine WP.mono (seedAttempt_ok H M Sq K ht seed hlen (ht.seeds.slice room) h1 ht16 bound)
    fun u ⟨Wu, randUsed', mu, bound', u16, slots, result, fu, ru, wu⟩ => ?_
  have frame := (fi.trans ff).trans fu
  have rd := ru.trans (kt.2.1.trans ri)
  have wr := wu.trans (kt.2.2.trans wi)
  have u10 : Wu 10 = BitVec.ofNat 64 (used + p.geo.qLen) := by
    simpa [Wt, upd] using slots 10 (by simp [searchSlots])
  have step := he.trans (p.remaining_step used randUsed room)
  change SeedOutcome p (VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen)
    ((p.seeds.bytes.drop used).take p.geo.qLen)
    ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop randUsed)) Wu randUsed' u at result
  obtain ⟨Vu, Ru⟩ := mu.rep
  refine ⟨Vu, Wu, mu.layout, Ru, ?_⟩
  rcases result with ⟨h19, hr⟩ | ⟨h19, hr⟩ | ⟨h19, a, hr, bytes⟩
  · rw [ite_eq_right (by rw [h19]; decide)]
    rw [hr] at step
    exact ⟨Wu, mu, Or.inl ⟨Or.inl h19, step⟩, frame, rd, wr⟩
  · rw [ite_eq_left h19]
    rw [hr] at step
    exact ⟨Wu, randUsed', mu, bound', u10, u16, step, frame, rd, wr⟩
  · rw [ite_eq_right (by rw [h19]; decide)]
    rw [hr] at step
    exact ⟨Wu, mu, Or.inr ⟨h19, a, step, bytes⟩, frame, rd, wr⟩

end VG.Proof.Dsa.X86_64.Generation
