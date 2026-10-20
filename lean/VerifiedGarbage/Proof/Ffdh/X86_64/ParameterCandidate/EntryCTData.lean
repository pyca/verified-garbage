module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HeaderCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: public ABI inputs and the entered frame -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def CR (p : CandidateP) (s : State) : Prop := pcPre s ∧ candidateOfState s = p

def candidateWr (p : CandidateP) : List Region := [⟨p.op, p.k⟩, ⟨p.up, 8⟩, ⟨p.B, p.Z⟩]

def Entered (p : CandidateP) (s : State) : Prop := CandidateTape p 0 s ∧ s.gpr .rdi = p.B ∧
  s.wr = candidateWr p ∧ InnerKW p.B (candidateWr p)

theorem pc_wr {s : State} (h : pcPre s) : s.wr = candidateWr (candidateOfState s) := h.2.2.2.1

theorem pc_kw {s : State} (h : pcPre s) : InnerKW (candidateOfState s).B (candidateWr (candidateOfState s)) := by
  have c := pcCtx_of h
  obtain ⟨_, _, _, _, dou, _, dos, _, _, dus, _, _, _, _, _, _, _, _, _, _, _, _, _,
    wo, _, _, ws, _, _, _, _, _⟩ := h
  refine ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, (stackArg s 2).toNat * 8, rfl, by change 8 ≤ 8; decide, ?_, ?_, ?_⟩
  · change 512 ≤ (stackArg s 2).toNat * 8
    have hk : 64 ≤ (s.gpr .rsi).toNat := by omega_using [c.bits1, c.len]
    omega_using [c.room, hk]
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl); exacts [dou, dos]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl; exact dus
  · intro r hr
    simp only [candidateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (s.gpr .rsi).toNat ≤ 2 ^ 64; omega_using [wo]
    · change 8 ≤ 2 ^ 64; decide
    · change (stackArg s 2).toNat * 8 ≤ 2 ^ 64; omega_using [ws]

theorem entry_entered (p : CandidateP) (s : State) (h : CR p s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.ParameterCandidate.entry) s (Entered p) := by
  refine WP.mono (candidateEntry_base (pcCtx_of h.1)) fun t ⟨ht, hd, _, _, _, k⟩ => ?_
  have hw : t.wr = candidateWr p := by rw [k.2.2, pc_wr h.1, h.2]
  have hk : InnerKW p.B (candidateWr p) := by rw [← h.2]; exact pc_kw h.1
  exact ⟨by simpa only [h.2] using ht, by simpa only [h.2] using hd, hw, hk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
