import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWide

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev wideVectors : List VReg := [.v0,.v2,.v20,.v16,.v17,.v18,.v19]

def quarterValues (s : State) (j : Nat) : BitVec 128 :=
 candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4)

def quarterMask (s : State) : Nat → BitVec 128
 | 0 => s.v .v20
 | j+1 => quarterMask s j &&& accepted (quarterValues s j) (s.v .v5)

structure QuarterPost (s : State) (n : Nat) (t : State) : Prop where
 frame : ProbeFrame [.x6] wideVectors s t
 values : ∀j<n,t.v wideRegs[j]! = quarterValues s j
 mask : t.v .v20=quarterMask s n

private theorem wide_ne {j : Nat} (hj : j<4) :
    wideRegs[j]! ≠ .v0 ∧ wideRegs[j]! ≠ .v2 ∧ wideRegs[j]! ≠ .v20 := by
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl | rfl | rfl | rfl <;> decide

private theorem wide_inj {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) :
    wideRegs[i]! ≠ wideRegs[j]! := by
  have hh : ∀i<4,∀j<4,wideRegs[i]! =wideRegs[j]! → i=j := by decide +kernel
  exact fun he => hne (hh i hi j hj he)

/-- Compose the four independent probes while preserving earlier decoded
vectors and accumulating their acceptance bits. -/
theorem quarters_ok (n : Nat) (hn : n≤4) {s : State}
    (hi : s.v .v3=gatherIndex)
    (hr : ∀j<n,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) :
    WP isa (.block ((List.range n).flatMap quarterCode)) s (QuarterPost s n) := by
  induction n with
  | zero =>
    exact WP.block_nil_iff.mpr ⟨⟨Only.refl _ _,fun _ _ => rfl⟩,
      fun _ h => absurd h (Nat.not_lt_zero _),rfl⟩
  | succ n ih =>
    have hn4 : n<4 := by omega
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega) (fun j hj => hr j (by omega))) fun a ha => ?_
    refine WP.mono (quarter_ok (s := a) hn4
      (by rw [ha.frame.only.rd,ha.frame.only.wr,ha.frame.only.get .x2]; exact hr n (by omega))
      (by rw [ha.frame.vectors .v3 (by decide)]; exact hi)) fun t ⟨ht,hval,hmask⟩ => ?_
    have hv : candidates (a.mem.read (a.gpr .x2+BitVec.ofNat 64 (12*n)) 16) (a.v .v4)=
        quarterValues s n := by
      rw [ha.frame.only.mem,ha.frame.only.get .x2,ha.frame.vectors .v4 (by decide)]
      rfl
    have hframe : ProbeFrame [.x6] wideVectors s t := (ha.frame.trans ht).mono
      (by simp) (by
        intro r hr'
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr'
        rcases hr' with h | rfl | h | rfl | rfl
        · simpa only [wideVectors,List.mem_cons,List.not_mem_nil,or_false] using h
        · decide
        · rcases h with rfl
          rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl | rfl | rfl | rfl <;> decide
        · decide
        · decide)
    refine ⟨hframe,?_,?_⟩
    · intro j hj
      by_cases he : j=n
      · subst j
        rw [hval,hv]
      · rw [ht.vectors _ (by
          have hh := wide_ne (j := j) (by omega)
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hh.1,wide_inj (by omega) hn4 he,hh.2.1,hh.2.2⟩)]
        exact ha.values j (by omega)
    · rw [hmask,hv,ha.mask,ha.frame.vectors .v5 (by decide)]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
