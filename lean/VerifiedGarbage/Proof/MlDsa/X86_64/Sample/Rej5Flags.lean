import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Batch

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq G PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (segment batch)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (flags)

/-- A saturated rejection fold is unchanged by the sixth block. -/
theorem full_after_five (σ : State) (k : Nat) (h : (Lt σ k 280).length = 256) :
    Lt σ k 336 = Lt σ k 280 := by
  have e : G (B σ k) 1008 = G (B σ k) 840 ++ (G (B σ k) 1008).drop 840 := by
    rw [← VG.Proof.MlDsa.Sample.G_take (B σ k) (by decide : 840 ≤ 1008), List.take_append_drop]
  have hl : Lt σ k 280 = rnFold [] (G (B σ k) 840) := by
    simp only [Lt, show 3 * 280 = 840 by rfl]
    rw [VG.Proof.MlDsa.Sample.G_take _ (by decide)]
  rw [Lt_336, hl, e, VG.Proof.MlDsa.Sample.rnFold_append _ _ _ (by rw [G_length]),
    VG.Proof.MlDsa.Sample.rnFold_full (by rwa [hl] at h)]

def allFull (σ : State) (n : Nat) : Bool :=
  (List.range 4).all fun k => (Lt σ k n).length == 256

section
variable {σ : State} (hp : Pre σ)
include hp

theorem flags_ok {n : Nat} {s : State} (env : EnvK σ s)
    (j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k n).length) :
    WP isa (.block flags) s fun s' =>
      (s'.gpr .r14 = (if allFull σ n then 1 else 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  have hin : ∀ k < 4, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * k)) 8 :=
    fun k hk => in_scr' hp env.rd env.wr (by simp only [oJ]; omega)
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide)
  have h2 := hin 2 (by decide); have h3 := hin 3 (by decide)
  have j0 := j 0 (by decide); have j1 := j 1 (by decide)
  have j2 := j 2 (by decide); have j3 := j 3 (by decide)
  simp only [oJ, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 j0 j1 j2 j3
  refine WP.keep _ ?_ (by decide)
  change WP isa (.block ([.mov32 .r14 (.imm 1),
    .mov .rax (.mem (at_ .rbx 4424)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4432)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4440)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4448)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])) s _
  xrun [env.rbx, h0, h1, h2, h3, j0, j1, j2, j3]
  simp only [full_bit (Lt_length_le σ _ _)]
  unfold allFull
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  cases (Lt σ 0 n).length == 256 <;> cases (Lt σ 1 n).length == 256 <;>
    cases (Lt σ 2 n).length == 256 <;> cases (Lt σ 3 n).length == 256 <;> rfl

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment
