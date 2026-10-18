module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT

/-! # Public invariants across vector and scalar rejection steps -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def PairInvW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr)
    (s₀ u₀ : State) (t : Nat) (s u : State) : Prop :=
  Scalar.InvW w16 initial N B bP aP s₀ t s ∧ Scalar.InvW w16 initial N B bP aP u₀ t u ∧
    Constants s ∧ Constants u

abbrev PairInv := PairInvW false

theorem vectorStep_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (ht : t+4≤N)
    (hroom : (Scalar.LA initial B t).length+8≤256) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t)
      (.block (Impl.MlKem.AArch64.Rej8.rejEight w16)) (PairInvW w16 initial N B bP aP s₀ u₀ (t+4)) := by
  intro s u tr ur s' u' hp es eu
  obtain ⟨hs,hu,cs,cu⟩ := hp
  have pub := inv_public hs hu hsp
  have htr := (batch_relCT w16 s u tr ur s' u'
    ⟨cs,cu,inv_candidates ps pu hs hu ht,
      by rw [hs.acc.rd,hs.acc.wr,hs.x2]; exact ps.input16 t ht,
      by rw [hu.acc.rd,hu.acc.wr,hu.x2]; exact pu.input16 t ht,
      pub.1,pub.2 .x2 (by simp),pub.2 .x3 (by simp),
      by rw [hs.keep.get .x16,hu.keep.get .x16,htab]⟩ es eu).1
  obtain ⟨_,a,ea,ha,ca⟩ := vector_ok ps hs cs ht (by rw [hs.acc.x4]; omega)
  obtain ⟨_,b,eb,hb,cb⟩ := vector_ok pu hu cu ht (by rw [hu.acc.x4]; omega)
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  exact ⟨htr,ha,hb,ca,cb⟩

theorem scalarFour_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (ht : t+4≤N) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t) (scalarFour w16)
      (PairInvW w16 initial N B bP aP s₀ u₀ (t+4)) := by
  have hct : RelCT isa (fun s u => Scalar.InvW w16 initial N B bP aP s₀ t s ∧
      Scalar.InvW w16 initial N B bP aP u₀ t u) (scalarFour w16)
      (fun s u => Scalar.InvW w16 initial N B bP aP s₀ (t+4) s ∧
        Scalar.InvW w16 initial N B bP aP u₀ (t+4) u) := by
    exact RelCT.seq (scalarBody_relCT ps pu hsp (by omega))
      (RelCT.seq (scalarBody_relCT ps pu hsp (by omega))
        (RelCT.seq (scalarBody_relCT ps pu hsp (by omega))
          (scalarBody_relCT ps pu hsp (by omega))))
  intro s u tr ur s' u' hp es eu
  obtain ⟨htr,hs,hu⟩ := hct s u tr ur s' u' ⟨hp.1,hp.2.1⟩ es eu
  obtain ⟨_,a,ea,_,va⟩ := scalarFour_ok ps.toLPreW hp.1 ht
  obtain ⟨_,b,eb,_,vb⟩ := scalarFour_ok pu.toLPreW hp.2.1 ht
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  refine ⟨htr,hs,hu,?_,?_⟩
  · exact ⟨by rw [va]; exact hp.2.2.1.index,by rw [va]; exact hp.2.2.1.mask,
      by simpa only [va] using hp.2.2.1.q,by simpa only [va] using hp.2.2.1.weights,
      by simpa only [va] using hp.2.2.1.zero⟩
  · exact ⟨by rw [vb]; exact hp.2.2.2.index,by rw [vb]; exact hp.2.2.2.mask,
      by simpa only [vb] using hp.2.2.2.q,by simpa only [vb] using hp.2.2.2.weights,
      by simpa only [vb] using hp.2.2.2.zero⟩

end VG.Proof.MlKem.AArch64.Rej8
