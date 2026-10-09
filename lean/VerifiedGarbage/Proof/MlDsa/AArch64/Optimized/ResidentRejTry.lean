import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def reduceRegisterCode (r : VReg) : List Instr :=
 [.umov .x .x6 r 0,.umov .x .x7 r 1,.logic .and .x .x6 .x6 .x7,
  .logic .eor .x .x6 .x6 .x12]

theorem reduceRegister_ok (s : State) (r : VReg) :
    WP isa (.block (reduceRegisterCode r)) s fun t => Only [.x6,.x7] s t ∧ t.v=s.v ∧
      t.gpr .x6=(vdword (s.v r) 0 &&& vdword (s.v r) 1) ^^^ s.gpr .x12 := by
  have h : WP isa (.block (reduceRegisterCode r)) s fun t => Only [.x6,.x7] s t ∧
      t.gpr .x6=(vdword (s.v r) 0 &&& vdword (s.v r) 1) ^^^ s.gpr .x12 := by
    let a := s.write .x .x6 (vdword (s.v r) 0)
    let b := a.write .x .x7 (vdword (s.v r) 1)
    have ha : Only [.x6] s a := only_write _ _ _ _
    have hb : Only [.x7] a b := only_write _ _ _ _
    refine WP.cons (s' := a) rfl (WP.cons (s' := b) rfl ?_)
    refine wp_and fun c hc ec => wp_eor fun t ht et => wp_nil ?_
    refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_⟩
    rw [et,ec,hb.get .x6,hc.get .x12,hb.get .x12,ha.get .x12]
    rfl
  exact WP.mono (WP.keepV (by rfl : (reduceRegisterCode r).all (fun i => !writesV i)=true) h)
    fun _ ⟨⟨hk,hv⟩,hvec⟩ => ⟨hk,hvec,hv⟩

def reduceCode : List Instr := reduceRegisterCode .v2

theorem reduce_ok (s : State) :
    WP isa (.block reduceCode) s fun t => Only [.x6,.x7] s t ∧ t.v=s.v ∧
      t.gpr .x6=(vdword (s.v .v2) 0 &&& vdword (s.v .v2) 1) ^^^ s.gpr .x12 :=
  reduceRegister_ok s .v2

/-- Complete four-candidate probe, with an exact branch flag and vector
frame suitable for composing probes into the sixteen-candidate path. -/
theorem vectorTry_ok {s : State}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (hi : s.v .v3=gatherIndex) :
    WP isa (.block vectorTry) s fun t =>
      Keep [.x6,.x7] s t ∧ t.mem=s.mem ∧
      (∀r,r≠.v0 → r≠.v1 → r≠.v2 → t.v r=s.v r) ∧
      t.v .v1=candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4) ∧
      t.gpr .x6=
        (vdword (accepted (candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)) (s.v .v5)) 0 &&&
         vdword (accepted (candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)) (s.v .v5)) 1) ^^^ s.gpr .x12 := by
  refine wp_ldrq (a := s.gpr .x2) (by decide) (ptr_zero _) hr fun a ha => ?_
  rw [show ([Instr.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
      .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
      .umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.logic .and .x .x6 .x6 .x7,
      .logic .eor .x .x6 .x6 .x12] : List Instr) =
      ([.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
      .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31)] : List Instr)++reduceCode from rfl,
    WP.block_append_iff]
  refine WP.mono (decode_ok (d := .v1) (by decide) (by decide) (by decide)
    (by rw [ha.other .v3 (by decide)]; exact hi)) fun b ⟨hb,hv,hflag⟩ => ?_
  refine WP.mono (reduce_ok b) fun t ⟨ht,hvec,hx⟩ => ?_
  refine ⟨((ha.chg.keep.trans hb.keep).trans ht.keep).mono (by decide),
    ht.mem.trans (hb.mem.trans ha.mem),?_,?_,?_⟩
  · intro r h0 h1 h2
    rw [hvec,hb.v r (by simpa using And.intro h1 h2),ha.other r h0]
  · rw [hvec,hv,ha.v,ha.other .v4 (by decide)]
  · rw [hx,hflag,ha.v,ha.other .v4 (by decide),ha.other .v5 (by decide),hb.gpr,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
