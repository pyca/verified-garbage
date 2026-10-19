module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSequenceCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public addressing for shaping the full-width p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

def PShapeReady (len count plen : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .rdi = p.plan.W 0 ∧ s.gpr .rsi = off p.plan.output ((count + 1) * len - plen) ∧
    s.gpr .rcx = BitVec.ofNat 64 plen ∧ s.gpr .rdx = BitVec.ofNat 64 (8 * plen)

theorem pShapeArgs_ct (n : Nat) (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 2 ^ 31) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (.block (Impl.Dsa.X86_64.Generation.pShapeArgs len count plen))
      (Two (PShapeReady len count plen)) := by
  have args : ∀ p s, ContributionBefore n H k len count p s →
      WP isa (.block (Impl.Dsa.X86_64.Generation.pShapeArgs len count plen)) s
        (PShapeReady len count plen p) := by
    intro p s h
    obtain ⟨⟨W, hw, hs, _⟩, _⟩ := h
    obtain ⟨V, R⟩ := hs.rep
    exact WP.mono (pShapeArgs_ok hs.layout R (hw 0 (by decide)) ((hw 4 (by decide)).trans p.plan.output_slot) hn hl)
      fun _ ⟨a, b, c, d, _, _⟩ => ⟨a, b, c, d⟩
  apply two_post (hw := args)
  apply RelCT.block_append (M := isa) (l₁ :=
    [.mov .rsi (.mem (Impl.Mgf1.X86_64.sp 32)),
      .alu .add .rsi (.imm (BitVec.ofNat 32 ((count + 1) * len - plen)))])
    (l₂ := [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 0)), .mov32 .rcx (.imm plen),
      .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * plen)))])
  refine RelCT.seq (two_post (Ψ := fun (p : PHashPublic) s => s.gpr .rsp = p.plan.F)
    (two_taint [.rsp] ?_ (hc := .block []) (by rfl)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨⟨_, _, hs, _⟩, _⟩ := hs
    obtain ⟨⟨_, _, ht, _⟩, _⟩ := ht
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    have total := args p s h
    change WP isa (.block
      ([.mov .rsi (.mem (Impl.Mgf1.X86_64.sp 32)),
        .alu .add .rsi (.imm (BitVec.ofNat 32 ((count + 1) * len - plen)))] ++
       [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 0)), .mov32 .rcx (.imm plen),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * plen)))])) s _ at total
    obtain ⟨⟨_, _, hs, _⟩, _⟩ := h
    exact WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rsi] (WP.block_append_iff.mp total) rfl)
      fun t ⟨_, hk⟩ => (hk.gpr (by decide)).trans hs.layout.rsp
  · exact two_taint [.rsp] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact hs.trans ht.symm) (hc := .block []) (by rfl)

theorem pShape_ct (n : Nat) (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 2 ^ 31) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pShape len count plen) (fun _ _ => True) := by
  refine RelCT.seq (pShapeArgs_ct n H k len count plen hn hl) ?_
  apply VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ct
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem pBuild_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count plen : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore n H 0 len count))
      (.seq (Impl.Dsa.X86_64.Generation.pHashes G len count)
        (Impl.Dsa.X86_64.Generation.pShape len count plen)) (fun _ _ => True) := by
  refine RelCT.seq (pHashes_ct hG n hn H hmatch hsize len count hlen hd hc)
    (pShape_ct n H (count + 1) len count plen ?_ hl)
  rcases hlen with rfl | rfl <;> omega

end VG.Proof.Dsa.X86_64.Generation
