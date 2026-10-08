import VerifiedGarbage.Proof.P256.EcdhJac.BuildState

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open Spec.Weierstrass

 theorem movCounter_ok (s : State) (n : BitVec 16) :
    WP isa (.block [.movz .x .x19 n 0]) s fun t => t.gpr .x19=n.setWidth 64 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · simp
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

 theorem buildStart_ok {base : Addr} {P : Point C} {k : Nat} {s : State} (hf : Fixed base P k s) :
    WP isa (.block (copyPt 4 K.E K.P++copy 4 5400 K.P.z++copy 4 5432 K.P.z++
      [.movz .x .x19 1 0]++Impl.P256.EcdhJac.storeEntry)) s fun t =>
      Frame base buildWork s t ∧ BuildInv base P k 1 t := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (initialPoint_ok hf) fun a ⟨ka,fa,pa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movCounter_ok a 1) fun b ⟨cb,kb⟩ => ?_
  have fb := fa.keep (frame_build ((AllocatedFrame.of_keeps kb).widenRegs (by decide)))
  have pb := selected_keeps pa kb
  refine WP.mono (storePoint_ok (m:=1) fb.field.scr (by decide) (by decide) cb pb) fun t ⟨kt,ot,pt,ct⟩ => ?_
  have pb' := selected_store (m:=1) pb (by decide) (by decide) ot
  have fr := (frame_build ka).trans
    (((AllocatedFrame.of_keeps kb).widenRegs (by decide)).trans kt)
  refine ⟨fr,⟨fb.keep kt,?_,?_,ct.trans cb⟩⟩
  · intro m hm hm1
    have : m=1 := by omega
    subst m
    simpa only [mul_one_pt] using pt
  · simpa only [mul_one_pt] using pb'

end VG.Proof.P256.EcdhJac
