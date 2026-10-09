import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackBody

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

/-- Moving by a whole sixteen-field block preserves bit alignment. -/
theorem fieldValue_shift (m : Mem) (a : Addr) {d : Nat} (hd : d=18 ∨ d=20) (j i : Nat) :
    fieldValue m (a+BitVec.ofNat 64 (2*d*j)) d i=fieldValue m a d (16*j+i) := by
  have hdiv : d*(16*j+i)/8=2*d*j+d*i/8 := by rcases hd with rfl | rfl <;> omega
  have hmod : d*(16*j+i)%8=d*i%8 := by rcases hd with rfl | rfl <;> omega
  simp only [fieldValue,Offset.add_add,hdiv,hmod]

theorem fieldValue_keep {m m' : Mem} {a : Addr} {d i : Nat} {rs : List Region}
    (hd : d=18 ∨ d=20) (hi : i<256) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, (Region.mk a (32*d)).Disjoint r) :
    fieldValue m' a d i=fieldValue m a d i := by
  have hb : d*i/8+3≤32*d := by rcases hd with rfl | rfl <;> omega
  unfold fieldValue
  rw [hf.read (r := ⟨a,32*d⟩) (Offset.contains_base a hb (by rcases hd with rfl | rfl <;> omega)) hs (by decide)]

def Parsed (m : Mem) (o : Addr) (input : Mem) (a : Addr) (d n : Nat) : Prop :=
  ∀ i<n, (m.readW (o+BitVec.ofNat 64 (4*i)) 32).toNat =
    (2^(d-1)+8380417-fieldValue input a d i)%8380417

theorem BodyPost.words {d : Nat} {s t : State} (h : BodyPost d s t) :
    Parsed t.mem (s.gpr .x4) s.mem (s.gpr .x0) d 16 := by
  intro i hi
  have hv := h.values (i/4) (by omega) (i%4) (by omega)
  rw [vword_read16 _ _ (by omega),Offset.add_add] at hv
  simpa only [show 16*(i/4)+4*(i%4)=4*i by omega,
    show 4*(i/4)+i%4=i by omega] using hv

/-- Later disjoint blocks preserve every earlier coefficient. -/
theorem Parsed.keep {m m' input : Mem} {o a : Addr} {d n : Nat} {rs : List Region}
    (h : Parsed m o input a d n) (hn : n≤256) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, (Region.mk o (4*n)).Disjoint r) :
    Parsed m' o input a d n := by
  intro i hi
  rw [hf.readW (r := ⟨o,4*n⟩) (Offset.contains_base o (by omega) (by omega)) hs (by decide)]
  exact h i hi

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
