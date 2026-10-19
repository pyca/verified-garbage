module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def stepWrites (p a b : Addr) : List Region := [⟨p,2048⟩,polyRegion a,polyRegion b]

structure Context (p a b c : Addr) (s : State) : Prop where
  scratch : Covers [⟨p,2048⟩] s.wr
  outA : Covers [polyRegion a] s.wr
  outB : Covers [polyRegion b] s.wr
  farA : (Region.mk p 2048).Disjoint (polyRegion a)
  farB : (Region.mk p 2048).Disjoint (polyRegion b)
  apart : (polyRegion a).Disjoint (polyRegion b)
  artifact : Rej8.TableArtifact s.mem c
  readable : Covers [⟨c,4096⟩] (s.rd++s.wr)
  tableScratch : (Region.mk c 4096).Disjoint ⟨p,2048⟩
  tableA : (Region.mk c 4096).Disjoint (polyRegion a)
  tableB : (Region.mk c 4096).Disjoint (polyRegion b)

theorem Context.frame {s t : State} {p a b c : Addr} (h : Context p a b c s)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hf : Frame (stepWrites p a b) s.mem t.mem) : Context p a b c t := by
  refine ⟨by simpa only [hw] using h.scratch,by simpa only [hw] using h.outA,
    by simpa only [hw] using h.outB,h.farA,h.farB,h.apart,?_,by simpa only [hr,hw] using h.readable,
    h.tableScratch,h.tableA,h.tableB⟩
  exact h.artifact.frame hf (by
    intro r hh
    simp only [stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl
    · exact h.tableScratch
    · exact h.tableA
    · exact h.tableB)

theorem Context.envW {w16 : Bool} {s : State} {p a b c out : Addr} {N off : Nat} {B : Nat→Byte}
    (h : Context p a b c s) (hx : s.gpr .x16=c) (hn : N≤280) (ho : off+3*N+4≤2048)
    (hout : out=a ∨ out=b)
    (bytes : ∀i<3*N,s.mem ((p+BitVec.ofNat 64 off)+BitVec.ofNat 64 i)=B i) :
    Rej8.EnvW w16 N B (p+BitVec.ofNat 64 off) out s := by
  have hc : Covers [polyRegion out] s.wr := by rcases hout with rfl|rfl; exact h.outA; exact h.outB
  have hd : (Region.mk p 2048).Disjoint (polyRegion out) := by rcases hout with rfl|rfl; exact h.farA; exact h.farB
  have ht : Rej8.TableReady s out := by
    refine ⟨by rw [hx]; exact h.artifact,by rw [hx]; exact h.readable,?_⟩
    rw [hx]
    rcases hout with rfl|rfl
    · exact h.tableA
    · exact h.tableB
  exact rejection_envW hn ho h.scratch hc hd bytes (fun _ hm=>ht.read hm)
    (fun _ hm=>ht.artifact.vector hm) (fun _ hm=>ht.disjoint hm)

theorem Context.env {s : State} {p a b c out : Addr} {N off : Nat} {B : Nat→Byte}
    (h : Context p a b c s) (hx : s.gpr .x16=c) (hn : N≤280) (ho : off+3*N+4≤2048)
    (hout : out=a ∨ out=b)
    (bytes : ∀i<3*N,s.mem ((p+BitVec.ofNat 64 off)+BitVec.ofNat 64 i)=B i) :
    Rej8.Env N B (p+BitVec.ofNat 64 off) out s :=
  h.envW hx hn ho hout bytes

end VG.Proof.MlKem.AArch64.Paired
