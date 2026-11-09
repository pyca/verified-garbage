module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCtx
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: MGF1's table

From a state in the frame (`EnvE`) naming the entry state's addresses of
statics, the table that the stack argument 9 points to as MGF1 needs it
(`Table.Tab`), as for decryption (`DecTab.lean`): the table and the stack
arguments are apart from everything the code writes (`etab`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.RsaOaep.X86_64.Table (Tab TabOK TabMem)

/-- A word of a region apart from what the code writes, in memory it may
leave. -/
theorem FrE.readW' {s : State} {m : Mem} (h : FrE s m) {r : Region} {a : Addr}
    (hc : r.Contains a 8) (hk : r.Disjoint (stkR s)) (ho : r.Disjoint (outR s)) (hs : r.Disjoint (scrR s)) :
    m.readW a 64 = s.mem.readW a 64 :=
  Frame.readW h hc (fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hk
    · exact ho
    · exact hs) (by decide)

/-- The table at the stack argument `j`, from the entry state's. -/
theorem etabJ {H : Spec.Mgf1.Hash} {s t : State} (hp : PPreT H s) (he : EnvE s t) (hsy : t.syms = s.syms)
    {G : Stream} {f : Fns} {j : Nat} (hj : j < 12) (hT : InRegions s.rd (stackArg s j) 40)
    (wT : (stackArg s j).toNat + 40 ≤ 2 ^ 64) (dK : (⟨stackArg s j, 40⟩ : Region).Disjoint (stkR s))
    (dO : (⟨stackArg s j, 40⟩ : Region).Disjoint (outR s)) (dS : (⟨stackArg s j, 40⟩ : Region).Disjoint (scrR s))
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s j) s.mem)
    (hD : s.mem.readW (off (stackArg s j) 32) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s j) (frameBytes + 8 + 8 * j) t := by
  have hsp := hp.sp4
  have cT : ∀ d, d + 8 ≤ 40 → (⟨stackArg s j, 40⟩ : Region).Contains (off (stackArg s j) d) 8 := fun d hd =>
    Offset.contains_base _ hd (by have := wT; omega)
  have cA : (argsT s).Contains (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  have rT : ∀ d, d + 8 ≤ 40 → InRegions (t.rd ++ t.wr) (off (stackArg s j) d) 8 := fun d hd => by
    rw [he.rd]; exact Covers.left (Covers.one hT) _ _ ⟨_, List.mem_singleton_self _, cT d hd⟩
  have rA : InRegions (t.rd ++ t.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [he.rd]; exact Covers.left (Covers.one hp.argsT') _ _ ⟨_, List.mem_singleton_self _, cA⟩
  refine ⟨by rw [hsy]; exact ok, fun i hi => rT _ (by omega), rT 32 (by omega), rA, fun m hf => ?_⟩
  have hF : FrE s m := FrE.step he.fr he.wr hf
  have rt : ∀ d, d + 8 ≤ 40 → m.readW (off (stackArg s j) d) 64 = s.mem.readW (off (stackArg s j) d) 64 :=
    fun d hd => FrE.readW' hF (cT d hd) dK dO dS
  rw [hsy]
  refine ⟨⟨(rt _ (by omega)).trans hm.1, (rt _ (by omega)).trans hm.2.1, (rt _ (by omega)).trans hm.2.2⟩,
    (rt 32 (by omega)).trans hD, ?_⟩
  rw [FrE.readW' hF cA hp.argsTStack hp.argsTOut hp.argsTScr, argAddr]
  rfl

/-- MGF1's table, from the entry state's. -/
theorem etab {H : Spec.Mgf1.Hash} {s t : State} (hp : PPreT H s) (he : EnvE s t) (hsy : t.syms = s.syms)
    {G : Stream} {f : Fns} (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 11) s.mem)
    (hD : s.mem.readW (off (stackArg s 11) 32) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 11) (frameBytes + 8 + 8 * 11) t :=
  etabJ hp he hsy (by decide) hp.tab hp.tabWrap hp.tabStack hp.tabOut hp.tabScr ok hm hD

/-- The table of the label's hash function, from the entry state's. -/
theorem etabL {H : Spec.Mgf1.Hash} {s t : State} (hp : PPreT H s) (he : EnvE s t) (hsy : t.syms = s.syms)
    {G : Stream} {f : Fns} (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 10) s.mem)
    (hD : s.mem.readW (off (stackArg s 10) 32) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t :=
  etabJ hp he hsy (by decide) hp.tabL hp.tabLWrap hp.tabLStack hp.tabLOut hp.tabLScr ok hm hD

end VG.Proof.RsaOaep.X86_64.Pc
