import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowDifference

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem firstPass_lowInput_read {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    (firstPassMem m work challenge secret 8).read (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16=
      m.read (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16 := by
  exact (firstPass_frame (m:=m) (a:=challenge) (b:=secret) (by decide : 8≤8)).read
    (lowAddr_contains out hu i h)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem firstPass_lowInputField {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : LowIndex) (h : Fin 2) (raw : BitVec 128) (e : Nat)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    lowInputField (firstPassMem m work challenge secret 8) (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e=
      lowInputField m (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e := by
  rw [lowInputField,firstPass_lowInput_read hu i h hd]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
