module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero

/-! # Finalize both bounded matrix samples, retaining zero-filled failure outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem zeroBoth_ok {s : State} {p a b c : Addr} {L M : List Zq}
    (hctx : Context p a b c s) (hp : s.gpr .x19=p)
    (hl : L.length≤256) (hm : M.length≤256)
    (ca : Rej8.Scalar.Coeffs s.mem a L) (cb : Rej8.Scalar.Coeffs s.mem b M)
    (sa : checkpoint (p+1680) a L s.mem) (sb : checkpoint (p+1696) b M s.mem) :
    WP isa (.seq (Impl.MlKem.AArch64.Paired.zeroExtra 1680)
      (Impl.MlKem.AArch64.Paired.zeroExtra 1696)) s fun u =>
      Keep [.x3,.x4,.x13] s u ∧ Frame [polyRegion a,polyRegion b] s.mem u.mem ∧
      CoeffsUpTo u.mem a L.length (Sample.cv L) (fun _=>0) ∧ Reduced u.mem a ∧
      CoeffsUpTo u.mem b M.length (Sample.cv M) (fun _=>0) ∧ Reduced u.mem b := by
  have iw {o l : Nat} (h : o+l≤2048) := in_rd_wr (rd := s.rd) (Noise.inScratch hctx.scratch h (by decide))
  refine WP.seq (WP.mono (zeroExtra_ok s (slot:=1680) (by decide) (by decide) hl ca
    (by rw [hp]; exact sa) (by rw [hp]; exact iw (by decide)) (by rw [hp]; exact iw (by decide))
    (fun i hi=>Noise.inScratch hctx.outA (by omega) (by decide))) fun t ⟨kt,ft,ct,rt⟩ => ?_)
  have t19 : t.gpr .x19=p := (kt.get .x19).trans hp
  have cb' : Rej8.Scalar.Coeffs t.mem b M := coeffs_frame cb hm ft (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact hctx.apart.symm)
  have sb' : checkpoint (t.gpr .x19+1696) b M t.mem := by
    rw [t19]
    exact checkpoint_frame sb ft (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact hctx.farA.sub_left (Offset.sub_base p (by decide)))
  refine WP.mono (zeroExtra_ok t (slot:=1696) (by decide) (by decide) hm cb' sb'
    (by rw [kt.rd,kt.wr,t19]; exact iw (by decide))
    (by rw [kt.rd,kt.wr,t19]; exact iw (by decide))
    (fun i hi=>by rw [kt.wr]; exact Noise.inScratch hctx.outB (by omega) (by decide))) fun u ⟨ku,fu,cu,ru⟩ => ?_
  have ca' : CoeffsUpTo u.mem a L.length (Sample.cv L) (fun _=>0) := by
    intro i hi
    rw [coeffAt_frame fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact hctx.apart) hi]
    exact ct i hi
  exact ⟨(kt.trans ku).mono (by decide),
    (ft.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans
      (fu.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp)),
    ca',Sample.reduced_of_coeffs (w16 := false) ca',cu,ru⟩

end VG.Proof.MlKem.AArch64.Paired
