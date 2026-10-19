module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashOne
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! # Advance the native hash-contribution sequence -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.Dsa.Generation

theorem hashStep_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} {k : Nat} (hk : k ≤ p.count)
    (hs : HashState p Hs k s) :
    WP isa (Impl.Dsa.AArch64.Generation.pHashOne G p.len p.count k) s fun t =>
      HashState p Hs (k + 1) t ∧ Step p.F p.S [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame p.changed s.mem t.mem := by
  have hls := p.size.2.1
  obtain ⟨V, R⟩ := hs.rep
  have hw : ∀ i < p.len, InRegions s.wr (off (p.dest k) i) 1 := by
    intro i hi
    rw [HashPlan.dest, off_off]
    apply hs.outputWrite
    have hm := Nat.mul_le_mul_right p.len (show p.count - k + 1 ≤ p.count + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  have hsep : ∀ i < p.len, ∀ j < p.len, off p.seedPtr i ≠ off p.wrapped j := by
    intro i hi j hj he
    have ha : Region.Contains ⟨p.seedPtr, p.len⟩ (off p.seedPtr i) 1 := Offset.contains_base _ (by omega) (by omega)
    have hb : Region.Contains ⟨p.wrapped, p.len⟩ (off p.wrapped j) 1 := Offset.contains_base _ (by omega) (by omega)
    exact p.seed_wrap _ (he ▸ ha) hb
  refine WP.mono (pHashOne_ok hG hHh hsize p.width hd p.count_le hk
    (by omega_using [p.carry, hk]) rfl hs.layout R hs.hashArgs
    p.seed_slot p.wrapped_slot p.output_slot p.offset_slot hs.seedRead hs.wrappedWrite hw hsep
    p.wrapped_sep (p.dest_sep k)) fun t ⟨Lt, step, hf, Rt, hout⟩ => ?_
  have hframe : Frame p.changed s.mem t.mem := hf.sub (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨p.output, (p.count + 1) * p.len⟩, by simp [HashPlan.changed], p.dest_sub k⟩
    all_goals exact ⟨_, by simp [HashPlan.changed], fun _ h => h⟩)
  have rd := step.rd
  have wr := step.wr
  refine ⟨⟨Lt, Rt, hs.hashArgs.congr rd wr rfl rfl,
    (fun i hi => by rw [rd, wr]; exact hs.seedRead i hi),
    (fun i hi => by rw [wr]; exact hs.wrappedWrite i hi),
    (fun i hi => by rw [wr]; exact hs.outputWrite i hi), ?_, ?_⟩, ⟨rd, wr, step.sp, step.cs, step.vec, hframe.mono (by simp [HashPlan.changed])⟩, hframe⟩
  · rw [frame_bytesAt hframe (by
      intro r hr
      simp only [HashPlan.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact p.seed_output
      · exact p.seed_wrap
      · exact p.seed_scratch
      · exact p.seed_stack) (by omega_using [p.size.2.1])]
    exact hs.seed
  · intro j hj
    by_cases he : j = k
    · subst j
      simpa only [hs.seed, HashPlan.digest, HashPlan.dest] using hout
    · have hjk : j < k := by omega
      rw [frame_bytesAt hf (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact p.dest_disjoint (by omega) hk he
        · exact p.output_wrap.sub_left (p.dest_sub j)
        · exact p.output_scratch.sub_left (p.dest_sub j)
        · exact p.output_stack.sub_left (p.dest_sub j)) (by omega_using [p.size.2.1])]
      exact hs.hashes j hjk

end VG.Proof.Dsa.AArch64.Generation
