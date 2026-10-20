module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullReject
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Readonly
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Constants and complete-stream rejection entry for the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def fullPrep (out : Nat) : List Instr := Rej8.rejConsts ++
  [.movz .x .x9 0 0,.str .x .x9 .x19 1240] ++ fullEntry 400 out

def prepWrites (p : Addr) : List Region := [⟨p+1408,8⟩,⟨p+1240,8⟩]
def prepRegs : List Reg := [.x2,.x3,.x4,.x5,.x9,.x10,.x16]

theorem fullPrep_ok {w16 : Bool} {s : State} {p out : Addr} {off : Nat} {B : Nat → Byte}
    (hoff : off<65536) (hp : s.gpr .x19=p) (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hc : Covers [⟨p,2048⟩] s.wr) (ho : Covers [⟨out,1024⟩] s.wr)
    (hd : (Region.mk p 2048).Disjoint ⟨out,1024⟩)
    (bytes : ∀i<840,s.mem ((p+400)+BitVec.ofNat 64 i)=B i)
    (tab : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE"))
    (tr : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr))
    (ts : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨p,2048⟩)
    (to : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨out,1024⟩) :
    WP isa (.block (fullPrep off)) s fun u =>
      Keep prepRegs s u ∧ Frame (prepWrites p) s.mem u.mem ∧ Rej8.EntryW w16 [] 280 B (p+400) out u ∧ u.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE" := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  rw [fullPrep,List.append_assoc,WP.block_append_iff]
  refine WP.mono_syms (Rej8.constants_ok s (by rw [hp]; exact iw (by decide))) fun a ⟨ka,ca,ma,ta⟩ sa => ?_
  have fa : Frame (prepWrites p) s.mem a.mem := by
    rw [ma,hp]
    exact (Frame.refl _ _).writeW (r := ⟨p+1408,8⟩) (by simp [prepWrites]) _ (Region.contains_self _ 8)
  have zero : WP isa (.block [.movz .x .x9 0 0,.str .x .x9 .x19 1240]) a fun c =>
      Keep [.x9] a c ∧ c.mem=a.mem.writeW (p+1240) (0 : BitVec 64) := by
    refine wp_movz fun b kb eb => wp_strx (a := p+1240) (by decide)
      (by rw [kb.get .x19,ka.get .x19,hp]; rfl)
      (by rw [kb.wr,ka.wr]; exact iw (by decide)) fun c kc => wp_nil ?_
    exact ⟨(kb.keep.trans kc.keep).mono (by decide),by rw [kc.mem,eb,kb.mem]; rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by decide) zero) fun c ⟨⟨kc,mc⟩,vc⟩ => ?_
  have pc : Keep [.x9,.x16] s c := (ka.trans kc).mono (by decide)
  have fc : Frame (prepWrites p) s.mem c.mem := by
    rw [mc]; exact fa.writeW (r := ⟨p+1240,8⟩) (by simp [prepWrites]) _ (Region.contains_self _ 8)
  have subs : ∀r∈prepWrites p,Region.Sub r ⟨p,2048⟩ := by
    intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base p (by decide)
  have cc : Rej8.Constants c := by
    have v : c.v=a.v := vc
    exact ⟨by rw [v]; exact ca.index,by rw [v]; exact ca.mask,
      by simpa only [v] using ca.q,by simpa only [v] using ca.weights,by simpa only [v] using ca.zero⟩
  have c16 : c.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE" := by rw [kc.get .x16,ta,sa]
  have ready : Rej8.TableReady c out := by
    refine ⟨?_,?_,?_⟩
    · rw [c16]; exact tab.frame fc (fun r hr => ts.sub_right (subs r hr))
    · rw [c16,pc.rd,pc.wr]; exact tr
    · rw [c16]; exact to
  have env : Rej8.EnvW w16 280 B (p+400) out c := rejection_envW (w16 := w16) (by decide) (by decide)
    (by rw [pc.wr]; exact hc) (by rw [pc.wr]; exact ho) hd
    (by
      intro i hi
      have hsep : ∀r∈prepWrites p,(Region.mk (p+400) 840).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      exact (fc.bytes hsep (by change 840≤2^64; decide) hi).trans (bytes i hi))
    (fun _ hm => ready.read hm) (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
  have env' : Rej8.EnvW w16 280 B (c.gpr .x19+400) (c.gpr .x28+BitVec.ofNat 64 off) c := by
    rw [pc.get .x19,pc.get .x28,hp,hout]; exact env
  refine WP.mono (fullEntry_ok c (by decide) hoff env' cc) fun u ⟨ku,eu⟩ => ?_
  refine ⟨(pc.trans ku.keep).mono (by decide),?_,?_,(ku.get .x16).trans c16⟩
  · rw [ku.mem]; exact fc
  · rw [pc.get .x19,pc.get .x28,hp,hout] at eu
    exact eu

end VG.Proof.MlKem.AArch64.Paired
