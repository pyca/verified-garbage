module

public import VerifiedGarbage.Proof.Mont.Words32

/-! Compare numbers whose words are stored at different bases and offsets. -/

@[expose] public section
namespace VG.Proof.Mont

theorem val32_congr_at {m m' : Mem} {base base' : Addr} {d d' : Nat} :
    ∀ {k : Nat}, (∀ i<k,w32 m base (d+4*i)=w32 m' base' (d'+4*i)) →
      val32 m base d k=val32 m' base' d' k
  | 0,_ => rfl
  | k+1,h => by
    rw [val32_succ,val32_succ,h k (Nat.lt_succ_self _),
      val32_congr_at fun i hi => h i (by omega)]

end VG.Proof.Mont
