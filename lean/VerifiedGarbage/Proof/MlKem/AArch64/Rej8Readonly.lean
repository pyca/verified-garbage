module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8 VG.Proof.MlKem

theorem tableWords_length : tableWords.length=512 := by decide +kernel

theorem tableWords_entry : ∀mask<256, ∀j<2,
    tableWords.getD (2*mask+j) 0=tableWord mask j := by decide +kernel

def TableArtifact (m : Mem) (p : Addr) : Prop :=
  ∀i<512,m.readW (p+BitVec.ofNat 64 (8*i)) 64=tableWords.getD i 0

theorem TableArtifact.vector {m : Mem} {p : Addr} (h : TableArtifact m p)
    {mask : Nat} (hm : mask<256) :
    m.read (p+BitVec.ofNat 64 (16*mask)) 16=tableVec mask := by
  rw [VG.Proof.MlKem.AArch64.Ntt16.read16_dw]
  have h0 := h (2*mask) (by omega)
  have h1 := h (2*mask+1) (by omega)
  rw [show 8*(2*mask)=16*mask by omega,←Nat.add_zero (2*mask),tableWords_entry mask hm 0 (by decide)] at h0
  rw [tableWords_entry mask hm 1 (by decide)] at h1
  rw [h0,BitVec.add_assoc,←BitVec.ofNat_add,
    show 16*mask+8=8*(2*mask+1) by omega,h1]
  rfl

structure TableReady (s : State) (a : Addr) : Prop where
  artifact : TableArtifact s.mem (s.gpr .x16)
  readable : Covers [⟨s.gpr .x16,4096⟩] (s.rd++s.wr)
  apart : (Region.mk (s.gpr .x16) 4096).Disjoint (polyRegion a)

theorem table_sub (p : Addr) {mask : Nat} (hm : mask<256) :
    Region.Sub ⟨p+BitVec.ofNat 64 (16*mask),16⟩ ⟨p,4096⟩ :=
  Offset.sub_base p (by omega)

theorem TableReady.read {s : State} {a : Addr} (h : TableReady s a)
    {mask : Nat} (hm : mask<256) :
    InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16 := by
  apply h.readable
  exact ⟨⟨s.gpr .x16,4096⟩,List.mem_singleton_self _,Offset.contains_base _ (by omega) (by omega)⟩

theorem TableReady.disjoint {s : State} {a : Addr} (h : TableReady s a)
    {mask : Nat} (hm : mask<256) :
    (Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint (polyRegion a) :=
  h.apart.sub_left (table_sub _ hm)

theorem TableArtifact.frame {m m' : Mem} {p : Addr} {rs : List Region}
    (h : TableArtifact m p) (hf : Frame rs m m')
    (hd : ∀r∈rs,(Region.mk p 4096).Disjoint r) : TableArtifact m' p := by
  intro i hi
  rw [hf.readW (Offset.contains_base p (by omega : 8*i+8≤4096) (by omega)) hd (by decide)]
  exact h i hi

end VG.Proof.MlKem.AArch64.Rej8
