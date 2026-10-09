import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_ofChg setup_mono)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def commonConstants : List Instr := vc .v8 (2^22) ++ vc .v10 1 ++
  [.vop (.dup .s4 .v9 .x8),.vop (.sub .s4 .v9 .v9 .v10),
   .vop (.dup .s4 .v10 .x8),.vop (.add .s4 .v10 .v10 .v9),.vop (.movi0 .v30)]

theorem commonConstants_ok (s : State) :
    WP isa (.block commonConstants) s fun t =>
      SetupKeep [.v8,.v9,.v10,.v30] s t ∧
      t.v .v8=HighPack.repeatedWord (2^22) ∧ t.v .v30=0 ∧
      (∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1) ∧
      (∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)) := by
  unfold commonConstants
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v8 (2^22)) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v10 1) fun b hb => ?_
  refine wp_vop (d := .v9) rfl fun c hc => wp_vop (d := .v9) rfl fun d hd =>
    wp_vop (d := .v10) rfl fun e he => wp_vop (d := .v10) rfl fun f hf =>
    wp_vop (d := .v30) rfl fun t ht => WP.block_nil_iff.mpr ?_
  have hframe := (SetupKeep.ofConst ha.1).trans ((SetupKeep.ofConst hb.1).trans
    (setup_ofChg (hc.chg.trans (hd.chg.trans (he.chg.trans (hf.chg.trans ht.chg))))))
  refine ⟨setup_mono hframe (by decide),?_,ht.v,?_,?_⟩
  · rw [ht.other .v8 (by decide),hf.other .v8 (by decide),he.other .v8 (by decide),
      hd.other .v8 (by decide),hc.other .v8 (by decide),hb.1.vec .v8 (by decide),ha.2]
  · intro i hi
    rw [ht.other .v9 (by decide),hf.other .v9 (by decide),he.other .v9 (by decide),hd.v,
      vword_map2 _ _ _ hi,hc.v,hc.other .v10 (by decide),hb.2,HighPack.repeatedWord_lane _ hi]
    change vword (HighPack.repeatedWord (b.gpr .x8).toNat) i - 1 = _
    rw [HighPack.repeatedWord_lane _ hi,hb.1.gpr .x8 (by decide),ha.1.gpr .x8 (by decide)]
    rfl
  · intro i hi
    rw [ht.other .v10 (by decide),hf.v,vword_map2 _ _ _ hi,he.v,
      he.other .v9 (by decide),hd.v,vword_map2 _ _ _ hi,hc.v,
      hc.other .v10 (by decide),hb.2,HighPack.repeatedWord_lane _ hi]
    change vword (HighPack.repeatedWord (d.gpr .x8).toNat) i +
      (vword (HighPack.repeatedWord (b.gpr .x8).toNat) i-1) = _
    rw [HighPack.repeatedWord_lane _ hi,HighPack.repeatedWord_lane _ hi,hd.gpr,hc.gpr,
      hb.1.gpr .x8 (by decide),ha.1.gpr .x8 (by decide)]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
