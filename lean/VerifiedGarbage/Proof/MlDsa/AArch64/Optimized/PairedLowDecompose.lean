import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Round

def lowDecompose (g : Nat) (a t h : VReg) : List Instr :=
 lowHb g h a t ++ lowMls a t h

theorem lowDecompose_ok {g : Nat} (hg : IsG g) {a t h : VReg}
    (hat : a≠t) (hah : a≠h) (hht : h≠t)
    (hregs : ∀r∈[a,t,h],r≠.v8 ∧ r≠.v12 ∧ r≠.v13 ∧ r≠.v14 ∧ r≠.v15 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀u,VChg [a,t,h] s u →
      (∀e<4,vword (u.v h) e=lowHighWord g (vword (s.v a) e)) →
      (∀e<4,vword (u.v a) e=Response.reduceWord
        (vword (s.v a) e-lowHighWord g (vword (s.v a) e)*vword (s.v .v15) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowDecompose g a t h++rest)) s Q := by
  unfold lowDecompose
  rw [List.append_assoc]
  have hh := hregs h (by simp)
  have ha := hregs a (by simp)
  have ht := hregs t (by simp)
  refine lowHb_ok hg hht hh.2.1 hh.2.2.1 hh.2.2.2.1 h11 h12 h13 h14 fun u hu hw => ?_
  have keep (r : VReg) (hr : r≠h ∧ r≠t) : u.v r=s.v r :=
    hu.get r (by simpa using hr)
  refine lowMls_ok hat ha.2.2.2.2.2 ha.1 ht.2.2.2.2.2
    (by intro e he; rw [keep .v31 ⟨Ne.symm hh.2.2.2.2.2,Ne.symm ht.2.2.2.2.2⟩]; exact hq e he)
    (by intro e he; rw [keep .v8 ⟨Ne.symm hh.1,Ne.symm ht.1⟩]; exact hc e he)
    fun v hv hvw => k v ((hu.trans hv).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_
  · intro e he
    rw [hv.get h (by simp [Ne.symm hah,hht])]
    exact hw e he
  · intro e he
    rw [hvw e he,keep a ⟨hah,hat⟩,hw e he,
      keep .v15 ⟨Ne.symm hh.2.2.2.2.1,Ne.symm ht.2.2.2.2.1⟩]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
