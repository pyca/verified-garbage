import VerifiedGarbage.Proof.P256.EcdhJac.Dblu
import VerifiedGarbage.Proof.P256.EcdhJac.BuildStore

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem buildDblu_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hi : BuildInv base P k 1 s) :
    WP isa (.seq (Impl.P256.EcdhJac.arithmetic Impl.P256.EcdhJac.dbluOps)
      (.block (copy 4 K.D.x K.S.t3++copy 4 K.D.y K.S.t2++
        ([.movz .x .x19 2 0] : List Instr)++Impl.P256.EcdhJac.storeEntry))) s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k 2 t := by
  refine WP.seq (WP.mono (dblu_ok hC ha hO hP hi.fixed) fun a ⟨ka,fa,pa,da,xa,ya⟩ => ?_)
  have ta := table_keep hi.table (by decide) ka
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyD_ok fa pa da xa ya) fun b ⟨kb,pb,lb,db⟩ => ?_
  have fb := fa.keep (frame_build kb)
  have tb := table_keep ta (by decide) kb
  rw [WP.block_append_iff]
  refine WP.mono (movCounter_ok b 2) fun d ⟨cd,kd⟩ => ?_
  have fd := fb.keep (frame_build ((AllocatedFrame.of_keeps kd).widenRegs (by decide)))
  have td : TblOk base P 1 d := by
    intro m hm hm1
    apply (tb m hm hm1).congr
    intro i hi
    rw [kd.mem]
  have pd := selected_keeps pb kd
  have ld : ∀x∈[K.D.x,K.D.y],wordsVal d.mem base x 4<C.p := by simpa only [kd.mem] using lb
  have dd : InvJ C (tmv C 4 base d K.D.x) (tmv C 4 base d K.D.y) (tmv C 4 base d K.E.z) P := by
    simpa only [tmv,kd.mem] using db
  refine WP.mono (storeCoZ_ok (m:=2) (by decide) (by decide) fd td pd ld dd cd) fun t ⟨kt,it⟩ =>
    ⟨(frame_build (ka.trans kb)).trans (((AllocatedFrame.of_keeps kd).widenRegs (by decide)).trans kt),it⟩

end VG.Proof.P256.EcdhJac
