import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Core
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Finish

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blocksAt)

def Post (s₀ : State) (dec : Bool) (s : State) : Prop := if dec then DPost s₀ s else EPost s₀ s

theorem finish_complete {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (dec : Bool)
    (hE : Env s₀ P s) (hD : DataInv s₀ (nb s₀) s.mem)
    (hc : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (nb s₀ + 8))
    (hy : s.lane .xmm2 0 = hashPrefix s₀ dec (nb s₀)) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx8.finish) s (Post s₀ dec) := by
  refine WP.mono (finish_ok hp hE (nb s₀) hc) fun t ht => ?_
  have hd : DataInv s₀ (nb s₀) t.mem := hD.frame ht.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c
    · exact hp.d_y)
  have hb : ∀ k < nb s₀, Spec.Gcm.blockAt t.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk; simpa only [hk, ite_true] using hd k hk
  have hm : blocksAt t.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
    apply List.map_congr_left
    intro k hk
    exact hb k (List.mem_range.mp hk)
  have hf : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem t.mem :=
    (hE.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  cases dec with
  | false =>
    refine ⟨blocks_ctr32 hb, ht.counter, ?_, hf, ht.regs, ht.rd, ht.wr⟩
    rw [ht.hash, hy, hm]
    rfl
  | true =>
    refine ⟨blocks_ctr32 hb, ht.counter, ?_, hf, ht.regs, ht.rd, ht.wr⟩
    rw [ht.hash, hy]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8
