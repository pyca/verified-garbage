import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParsePublic

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def CandidatesEq (s t : State) (n : Nat) : Prop :=
  ∀j<n,candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (3*j))=
    candidate t.mem (t.gpr .x2+BitVec.ofNat 64 (3*j))

theorem vector_eq_of_words {a b : BitVec 128}
    (h : ∀e<4,vword a e=vword b e) : a=b := by
  rw [← VG.AArch64.ofVWords_vword a,← VG.AArch64.ofVWords_vword b]
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]

theorem quarterValues_eq {s t : State} (hs : Constants s) (ht : Constants t)
    (he : CandidatesEq s t 16) {j : Nat} (hj : j<4) : quarterValues s j=quarterValues t j := by
  apply vector_eq_of_words
  intro e he4
  apply BitVec.eq_of_toNat_eq
  unfold quarterValues
  rw [candidates_word _ _ _ he4 (hs.mask e he4),candidates_word _ _ _ he4 (ht.mask e he4),
    Offset.add_add,Offset.add_add]
  rw [show 12*j+3*e=3*(4*j+e) by omega]
  exact he _ (by omega)

theorem quarterMask_eq {s t : State} (hs : Constants s) (ht : Constants t)
    (he : CandidatesEq s t 16) : quarterMask (wideInitial s) 4=quarterMask (wideInitial t) 4 := by
  apply vector_eq_of_words
  intro e he4
  rw [quarterMask_word hs 4 he4,quarterMask_word ht 4 he4]
  congr 1
  apply propext
  have eqc (j : Nat) (hj : j<4) :
      candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e))=
      candidate t.mem (t.gpr .x2+BitVec.ofNat 64 (12*j+3*e)) := by
    rw [show 12*j+3*e=3*(4*j+e) by omega]
    exact he _ (by omega)
  exact ⟨fun h j hj => by rw [← eqc j hj]; exact h j hj,
    fun h j hj => by rw [eqc j hj]; exact h j hj⟩

theorem fourDecoded_eq {s t : State} (hs : Constants s) (ht : Constants t)
    (he : CandidatesEq s t 4) :
    candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)=
    candidates (t.mem.read (t.gpr .x2) 16) (t.v .v4) := by
  apply vector_eq_of_words
  intro e he4
  apply BitVec.eq_of_toNat_eq
  rw [candidates_word _ _ _ he4 (hs.mask e he4),candidates_word _ _ _ he4 (ht.mask e he4)]
  exact he e he4

theorem modulusVector_eq {s t : State} (hs : Constants s) (ht : Constants t) : s.v .v5=t.v .v5 := by
  apply vector_eq_of_words
  intro e he
  rw [hs.modulus e he,ht.modulus e he]

theorem InputEq.candidate {σ τ : State} {b : Addr} {n j : Nat}
    (h : InputEq σ τ b n) (hj : j<n) :
    candidate σ.mem (b+BitVec.ofNat 64 (3*j))=candidate τ.mem (b+BitVec.ofNat 64 (3*j)) := by
  unfold ResidentRej.candidate
  have h1 : b+BitVec.ofNat 64 (3*j)+1=b+BitVec.ofNat 64 (3*j+1) := by bv_omega
  have h2 : b+BitVec.ofNat 64 (3*j)+2=b+BitVec.ofNat 64 (3*j+2) := by bv_omega
  rw [h1,h2,h _ (by omega),h _ (by omega),h _ (by omega)]

theorem ParseInv.candidates_eq {σ τ s t : State} {b p : Addr} {n d k : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (he : InputEq σ τ b n) (ps : ParseInv σ b p n L d s) (pt : ParseInv τ b p n L d t)
    (hk : d+k≤n) : CandidatesEq s t k := by
  intro j hj
  rw [ps.candidate hs (by omega),pt.candidate ht (by omega)]
  exact he.candidate (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
