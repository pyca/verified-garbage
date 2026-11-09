module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordLoop
public import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time word reductions with a public word counter -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Pub where
  B : Addr
  Z : Nat
  W : Nat
  j : Nat

structure Ready (p : Pub) (s : State) : Prop where
  ws : Ws s p.B p.Z p.W
  z : slot p.W 17 ≤ p.Z
  w : 4 ≤ p.W
  j : p.j ≤ p.W
  counter : word s.mem p.B (slot p.W aV + 16) = BitVec.ofNat 64 p.j
  top : 2 ^ 63 ≤ (word s.mem p.B (slot p.W aM + 8 * (p.W / 2 - 1))).toNat
  reciprocal : (word s.mem p.B (slot p.W aV)).toNat =
    (2 ^ 128 - 1) / (word s.mem p.B (slot p.W aM + 8 * (p.W / 2 - 1))).toNat - 2 ^ 64
  remainder : wv s.mem p.B (slot p.W aR) (p.W / 2) < wv s.mem p.B (slot p.W aM) (p.W / 2)

/-- Public register values immediately before the indexed digit load. -/
def loadVal (p : Pub) : Reg → BitVec 64
  | .rdi => p.B
  | .r12 => BitVec.ofNat 64 p.W
  | .r9 => BitVec.ofNat 64 (8 * (p.W + 2))
  | .rbp => off p.B (slot p.W aV)
  | .r11 => off p.B (slot p.W aD)
  | .rcx => BitVec.ofNat 64 p.j
  | _ => 0

/-- The block's public counter pins the only input-dependent address. -/
theorem core_ct : RelCT isa (Two fun (p : Pub) s => 0 < p.j ∧ Ready p s)
    (.seq (.block stepSetup) Impl.Rsa.X86_64.WordReduce.step)
    (Two fun (p : Pub) s => Ws s p.B p.Z p.W ∧ slot p.W 17 ≤ p.Z ∧
      0 < p.j ∧ p.j ≤ p.W ∧ word s.mem p.B (slot p.W aV + 16) = BitVec.ofNat 64 p.j) := by
  apply two_post (Ψ := fun (p : Pub) s => Ws s p.B p.Z p.W ∧ slot p.W 17 ≤ p.Z ∧
      0 < p.j ∧ p.j ≤ p.W ∧ word s.mem p.B (slot p.W aV + 16) = BitVec.ofNat 64 p.j)
  · unfold stepSetup
    apply RelCT.block_seq
    refine RelCT.seq (R := Two fun (p : Pub) s => ∀ r ∈ [.rdi, .r12, .r9, .rbp, .r11, .rcx],
      s.gpr r = loadVal p r) ?_ (two_taint [.rdi, .r12, .r9, .rbp, .r11, .rcx]
        (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) (by taint_decide))
    unfold stepLoad
    refine ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.2.ws) (by taint_decide) ?_
    intro p s h
    refine WP.mono (stepLoad_ok h.2.ws h.2.z h.2.counter) fun t ⟨hdi, h12, h9, hbp, h11, hcx⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hdi | exact h12 | exact h9 | exact hbp | exact h11 | exact hcx
  · intro p s h
    exact WP.mono (core_ok h.2.ws h.2.z h.2.w h.1 h.2.j h.2.counter h.2.top h.2.reciprocal h.2.remainder)
      fun t ⟨_, hc, hf, hk⟩ => ⟨range_ws h.2.ws hf hk, h.2.z, h.1, h.2.j, hc⟩

/-- Counter update addresses and branch result depend on the public count. -/
theorem body_ct : RelCT isa (Two fun (p : Pub) s => 0 < p.j ∧ Ready p s) body fun _ _ => True := by
  unfold body
  change RelCT isa _ (.seq (.block stepSetup) (.seq Impl.Rsa.X86_64.WordReduce.step (.block next))) _
  apply RelCT.assoc
  refine (RelCT.seq (Q := Two fun (_ : Pub) (_ : State) => True) core_ct ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  unfold next
  refine ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide) ?_
  intro p s h
  exact WP.mono (next_ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) fun _ _ => trivial

/-- The arithmetic hypotheses are preserved for the next public count. -/
theorem ready_step {p : Pub} {s : State} (h : Ready p s) (hj : 0 < p.j) :
    WP isa body s fun t => Ready { p with j := p.j - 1 } t ∧ t.zf = some (decide (p.j = 1)) := by
  have hn := h.ws.scr.nowrap
  have hz := window_bound h.ws h.z
  have hm := h.ws.sl (j := aM) (by decide)
  refine WP.mono (body_ok h.ws h.z h.w hj h.j h.counter h.top h.reciprocal h.remainder)
    fun t ⟨hx, hc, _, hf, ff, hk⟩ => ?_
  have M := range_modulus ff (by omega_arith)
  have top := range_top h.w ff (by omega_arith)
  have v := range_recip ff (by omega_arith)
  refine ⟨⟨range_ws h.ws ff hk, h.z, h.w, by dsimp only; omega_using [h.j], hc, ?_, ?_, ?_⟩, hf⟩
  · dsimp only; rw [top]; exact h.top
  · dsimp only; rw [top, v]; exact h.reciprocal
  · dsimp only; rw [hx, M]; exact Nat.mod_lt _ (by omega_using [h.remainder])

def At (p : Pub) (i : Nat) : State → Prop := Ready { p with j := p.W - i }

/-- Both executions run exactly `W` digit iterations. -/
theorem loop_ct : RelCT isa (Two fun (p : Pub) s => 0 < p.W ∧ At p 0 s)
    (.loop body .ne) (Two fun (p : Pub) s => At p p.W s) := by
  refine two_loop (Φ := At) Pub.W ?_ ?_
  · exact two_map (fun q : Pub × Nat => { q.1 with j := q.1.W - q.2 })
      (fun _ _ h => ⟨by dsimp only; omega_using [h.1], h.2⟩) body_ct
  · intro p i s hi h
    refine WP.mono (ready_step h (by dsimp only; omega_using [hi])) fun t ⟨ht, hz⟩ => ?_
    have he : isa.eval .ne t = some (decide (i + 1 < p.W)) := by
      simp only [eval, hz, Option.map_some, show (p.W - i = 1) ↔ ¬ (i + 1 < p.W) by omega_using [hi], decide_not, Bool.not_not]
    refine ⟨he, fun _ => ?_, fun hi' => ?_⟩
    · simpa only [At, Nat.sub_add_eq] using ht
    · simpa only [At, show p.W - i - 1 = p.W - p.W by omega_using [hi']] using ht

end VG.Proof.Rsa.X86_64.WordDivide
