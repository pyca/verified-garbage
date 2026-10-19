module
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Table
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8 VG.Proof.MlKem

theorem tableWords_length : tableWords.length=512 := by decide +kernel

/-- Entry `i` of block `b` of a list of blocks of `k` entries. -/
theorem flatMap_range_getD {α : Type} (f : Nat → List α) {k : Nat} (hf : ∀ b, (f b).length = k) (d : α) :
    ∀ n b i, b < n → i < k → ((List.range n).flatMap f).getD (k * b + i) d = (f b).getD i d := by
  have hl : ∀ n, ((List.range n).flatMap f).length = k * n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append, ih, hf,
        Nat.mul_succ]
  intro n
  induction n with
  | zero => intro b i hb; omega
  | succ n ih =>
    intro b i hb hi
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    by_cases h : b < n
    · have : k * b + i < k * n := by
        have := Nat.mul_le_mul_left k (show b + 1 ≤ n by omega); rw [Nat.mul_succ] at this; omega
      rw [ite_eq_left this, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
      exact ih b i h hi
    · have : b = n := by omega
      subst this
      rw [ite_eq_right (by omega), show k * b + i - k * b = i by omega]

/-- An entry of the table, from its blocks of two words: by the list's shape,
not by evaluating all 512 entries. -/
theorem tableWords_entry : ∀mask<256, ∀j<2,
    tableWords.getD (2*mask+j) 0=tableWord mask j := by
  intro mask hm j hj
  rw [tableWords, flatMap_range_getD _ (k := 2) (fun _ => by simp) 0 256 mask j hm hj]
  match j, hj with
  | 0, _ | 1, _ => rfl

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
