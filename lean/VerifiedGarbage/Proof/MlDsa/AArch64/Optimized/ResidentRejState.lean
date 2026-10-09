import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegment

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oSave saved)

abbrev seedP := VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP
abbrev aP := VG.Proof.MlDsa.AArch64.Sample.Rej4.aP
abbrev scr := VG.Proof.MlDsa.AArch64.Sample.Rej4.scr
abbrev at' := VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
abbrev scrR := VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR
abbrev lowR := VG.Proof.MlDsa.AArch64.Sample.Rej4.lowR
abbrev saveR := VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR
abbrev vSaveR := VG.Proof.MlDsa.AArch64.Sample.Rej4.vSaveR
abbrev B := VG.Proof.MlDsa.AArch64.Sample.Rej4.B
abbrev A0 := VG.Proof.MlDsa.AArch64.Sample.Rej4.A0
abbrev stateP := VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP
abbrev bufP := VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP

def seedsR (v : Nat) (s : State) : Region := ⟨seedP s,34*v⟩
def aR (v : Nat) (s : State) : Region := ⟨aP s,1024*v⟩
def polyP (s : State) (k : Nat) : Addr := aP s+BitVec.ofNat 64 (1024*k)
def countP (s : State) (k : Nat) : Addr := at' s (Impl.MlDsa.AArch64.Optimized.ResidentRej.counts+8*k)

/-- Precisely sized external buffers for either two or four matrix streams. -/
structure Pre (v : Nat) (s : State) : Prop where
 streams : v=2 ∨ v=4
 rd : s.rd=[seedsR v s]
 wr : s.wr=[aR v s,scrR s]
 seed_a : (seedsR v s).Disjoint (aR v s)
 seed_scr : (seedsR v s).Disjoint (scrR s)
 a_scr : (aR v s).Disjoint (scrR s)

structure Env (v : Nat) (σ s : State) : Prop where
 rd : s.rd=σ.rd
 wr : s.wr=σ.wr
 sp : s.sp=σ.sp
 x19 : s.gpr .x19=scr σ
 x20 : s.gpr .x20=seedP σ
 x21 : s.gpr .x21=aP σ
 x30 : s.gpr .x30=σ.gpr .x30
 savedG : ∀i<10,s.mem.readW (at' σ (oSave+8*i)) 64=σ.gpr saved[i]!
 savedV : ∀i<8,s.mem.readW (at' σ (oSave+80+8*i)) 64=
   vdword (σ.v (Impl.Sha3.AArch64.Sha3.Vector.vreg (8+i))) 0
 frame : Frame [aR v σ,scrR σ] σ.mem s.mem

theorem in_scr {v : Nat} {σ s : State} (hp : Pre v σ) (hw : s.wr=σ.wr)
    {d n : Nat} (hd : d+n≤8192) : InRegions s.wr (at' σ d) n := by
  rw [hw,hp.wr]
  exact ⟨scrR σ,by simp,Offset.contains_base (scr σ) hd (by omega)⟩

theorem in_scr_rd {v : Nat} {σ s : State} (hp : Pre v σ) (hw : s.wr=σ.wr)
    {d n : Nat} (hd : d+n≤8192) : InRegions (s.rd++s.wr) (at' σ d) n := by
  obtain ⟨r,hr,hc⟩ := in_scr hp hw hd
  exact ⟨r,List.mem_append.mpr (.inr hr),hc⟩

theorem in_seed {v : Nat} {σ s : State} (hp : Pre v σ) (hr : s.rd=σ.rd)
    {d n : Nat} (hd : d+n≤34*v) : InRegions (s.rd++s.wr) (seedP σ+BitVec.ofNat 64 d) n := by
  rw [hr,hp.rd]
  exact ⟨seedsR v σ,by simp,Offset.contains_base (seedP σ) hd (by have:=hp.streams; omega)⟩

theorem Env.frameStep {v : Nat} {σ s t : State} (he : Env v σ s) {rs : List Region}
    (hf : Frame rs s.mem t.mem)
    (hsub : ∀r∈rs,∃R∈[aR v σ,scrR σ],Region.Sub r R)
    (hsave : ∀r∈rs,(saveR σ).Disjoint r)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hsp : t.sp=s.sp)
    (hg : ∀r∈[Reg.x19,.x20,.x21,.x30],t.gpr r=s.gpr r) : Env v σ t := by
  refine ⟨hr.trans he.rd,hw.trans he.wr,hsp.trans he.sp,
    (hg .x19 (by simp)).trans he.x19,(hg .x20 (by simp)).trans he.x20,
    (hg .x21 (by simp)).trans he.x21,(hg .x30 (by simp)).trans he.x30,
    ?_,?_,he.frame.trans (hf.sub hsub)⟩
  · intro i hi
    rw [hf.readW (Offset.contains (scr σ) (d := oSave+8*i) (e := oSave) (n := 8) (k := 144)
      (by omega) (by omega) (by decide)) hsave (by decide)]
    exact he.savedG i hi
  · intro i hi
    rw [hf.readW (Offset.contains (scr σ) (d := oSave+80+8*i) (e := oSave) (n := 8) (k := 144)
      (by omega) (by omega) (by decide)) hsave (by decide)]
    exact he.savedV i hi

theorem Env.lowStep {v : Nat} {σ s t : State} (he : Env v σ s) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hsub : ∀r∈rs,Region.Sub r (lowR σ))
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hsp : t.sp=s.sp)
    (hg : ∀r∈[Reg.x19,.x20,.x21,.x30],t.gpr r=s.gpr r) : Env v σ t :=
  he.frameStep hf (fun r hm => ⟨scrR σ,by simp,fun x hx =>
    (Region.sub_prefix (by decide : oSave≤8192)) x (hsub r hm x hx)⟩)
    (fun r hm => (VG.Proof.MlDsa.AArch64.Sample.Rej4.low_save σ).sub_right (hsub r hm))
    hr hw hsp hg

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
