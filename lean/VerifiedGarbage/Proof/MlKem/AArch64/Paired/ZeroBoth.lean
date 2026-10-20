module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset

/-! # Finalize both bounded matrix samples, retaining zero-filled failure outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem zeroBoth_ok {w16 : Bool} {s : State} {p a b c : Addr} {L M : List Zq}
    (hctx : Context p a b c s) (hp : s.gpr .x19=p)
    (hl : L.length≤256) (hm : M.length≤256)
    (ca : Rej8.Scalar.CoeffsW w16 s.mem a L) (cb : Rej8.Scalar.CoeffsW w16 s.mem b M)
    (sa : checkpointW w16 (p+1680) a L s.mem) (sb : checkpointW w16 (p+1696) b M s.mem) :
    WP isa (.seq (Impl.MlKem.AArch64.Paired.zeroExtra 1680 w16)
      (Impl.MlKem.AArch64.Paired.zeroExtra 1696 w16)) s fun u =>
      Keep [.x3,.x4,.x13] s u ∧ Frame [polyRegion a,polyRegion b] s.mem u.mem ∧
      CoeffsUpToW w16 u.mem a L.length (Sample.cvW w16 L) (fun _=>0) ∧ ReducedW (cw w16) u.mem a ∧
      CoeffsUpToW w16 u.mem b M.length (Sample.cvW w16 M) (fun _=>0) ∧ ReducedW (cw w16) u.mem b := by
  have iw {o l : Nat} (h : o+l≤2048) := in_rd_wr (rd := s.rd) (Noise.inScratch hctx.scratch h (by decide))
  refine WP.seq (WP.mono (zeroExtra_ok s (slot:=1680) (by decide) (by decide) hl ca
    (by rw [hp]; exact sa) (by rw [hp]; exact iw (by decide)) (by rw [hp]; exact iw (by decide))
    (fun i hi=>Noise.inScratch hctx.outA (cs_store_le w16 hi) (by decide))) fun t ⟨kt,ft,ct,rt⟩ => ?_)
  have t19 : t.gpr .x19=p := (kt.get .x19).trans hp
  have cb' : Rej8.Scalar.CoeffsW w16 t.mem b M := coeffs_frame cb hm ft (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact hctx.apart.symm)
  have sb' : checkpointW w16 (t.gpr .x19+1696) b M t.mem := by
    rw [t19]
    exact checkpoint_frame sb ft (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact hctx.farA.sub_left (Offset.sub_base p (by decide)))
  refine WP.mono (zeroExtra_ok t (slot:=1696) (by decide) (by decide) hm cb' sb'
    (by rw [kt.rd,kt.wr,t19]; exact iw (by decide))
    (by rw [kt.rd,kt.wr,t19]; exact iw (by decide))
    (fun i hi=>by rw [kt.wr]; exact Noise.inScratch hctx.outB (cs_store_le w16 hi) (by decide))) fun u ⟨ku,fu,cu,ru⟩ => ?_
  have ca' : CoeffsUpToW w16 u.mem a L.length (Sample.cvW w16 L) (fun _=>0) := by
    intro i hi
    rw [coeffAtW_frame fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact hctx.apart) hi]
    exact ct i hi
  exact ⟨(kt.trans ku).mono (by decide),
    (ft.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans
      (fu.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp)),
    ca',Sample.reduced_of_coeffs ca',cu,ru⟩

end VG.Proof.MlKem.AArch64.Paired
