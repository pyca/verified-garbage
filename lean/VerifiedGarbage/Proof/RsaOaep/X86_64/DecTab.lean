module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecFrame
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86-64: MGF1's table

From a state in the frame (`EnvD`) naming the entry state's addresses of
statics, the tables that the stack arguments 17 (the label's hash
function's) and 18 (MGF1's) point to as the code that calls their functions
needs them (`Table.Tab`): readable, and with their words and those arguments
in every memory the code may leave, since the tables and the stack arguments
are apart from everything it writes (`dtabL`, `dtab`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.RsaOaep.X86_64.Table (Tab TabOK TabMem)

/-- A word of a region apart from what the code writes, in memory it may
leave. -/
theorem FrD.readW' {s : State} {m : Mem} (h : FrD s m) {r : Region} {a : Addr}
    (hc : r.Contains a 8) (hk : (stkD s).Disjoint r) (ho : (outR s).Disjoint r) (hm : (mlR s).Disjoint r)
    (hs : (scrD s).Disjoint r) : m.readW a 64 = s.mem.readW a 64 :=
  Frame.readW h hc (fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hk.symm
    · exact ho.symm
    · exact hm.symm
    · exact hs.symm) (by decide)

/-- The table at the stack argument `j`, from the entry state's. -/
theorem dtabJ {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {G : Stream} {f : Fns}
    {j : Nat} (hj : j < 19) (hT : (⟨stackArg s j, 40⟩ : Region) ∈ s.rd) (wT : (stackArg s j).toNat + 40 ≤ 2 ^ 64)
    (dK : (stkD s).Disjoint ⟨stackArg s j, 40⟩) (dO : (outR s).Disjoint ⟨stackArg s j, 40⟩)
    (dM : (mlR s).Disjoint ⟨stackArg s j, 40⟩) (dS : (scrD s).Disjoint ⟨stackArg s j, 40⟩)
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s j) s.mem)
    (hD : s.mem.readW (off (stackArg s j) 32) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s j) (frameBytes + 8 + 8 * j) t := by
  have hsp := hp.sp2
  have hT' : (⟨stackArg s j, 40⟩ : Region) ∈ t.rd := by rw [he.rd]; exact hT
  have hA : (⟨stackArgAddr s 0, 152⟩ : Region) ∈ t.rd := by rw [he.rd, hp.hrd]; simp
  have cT : ∀ d, d + 8 ≤ 40 → (⟨stackArg s j, 40⟩ : Region).Contains (off (stackArg s j) d) 8 := fun d hd =>
    Offset.contains_base _ hd (by have := wT; omega)
  have cA : (⟨stackArgAddr s 0, 152⟩ : Region).Contains (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by have := hp.sp2; omega)
  refine ⟨by rw [hsy]; exact ok, fun i hi => ⟨_, List.mem_append_left _ hT', cT _ (by omega)⟩,
    ⟨_, List.mem_append_left _ hT', cT 32 (by omega)⟩, ⟨_, List.mem_append_left _ hA, cA⟩, fun m hf => ?_⟩
  have hF : FrD s m := FrD.step he.fr he.wr hf
  have rt : ∀ d, d + 8 ≤ 40 → m.readW (off (stackArg s j) d) 64 = s.mem.readW (off (stackArg s j) d) 64 :=
    fun d hd => hF.readW' (cT d hd) dK dO dM dS
  rw [hsy]
  refine ⟨⟨(rt _ (by omega)).trans hm.1, (rt _ (by omega)).trans hm.2.1, (rt _ (by omega)).trans hm.2.2⟩,
    (rt 32 (by omega)).trans hD, ?_⟩
  rw [hF.readW' cA hp.dKa hp.dOa hp.dMa hp.dsa, argAddr]
  rfl

/-- MGF1's table, from the entry state's. -/
theorem dtab {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {G : Stream} {f : Fns}
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 18) s.mem)
    (hD : s.mem.readW (off (stackArg s 18) 32) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 18) (frameBytes + 8 + 8 * 18) t :=
  dtabJ hp he hsy (by decide) (by rw [hp.hrd]; simp [tabR]) hp.wT hp.dKt hp.dOt hp.dMt hp.dst ok hm hD

/-- The table of the label's hash function, from the entry state's. -/
theorem dtabL {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {G : Stream} {f : Fns}
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 17) s.mem)
    (hD : s.mem.readW (off (stackArg s 17) 32) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 17) (frameBytes + 8 + 8 * 17) t :=
  dtabJ hp he hsy (by decide) (by rw [hp.hrd]; simp [tabL]) hp.wTL hp.dKtL hp.dOtL hp.dMtL hp.dstL ok hm hD

end VG.Proof.RsaOaep.X86_64
