import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Batch
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ready

/-! # The prefix of data already transformed by counter mode -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)

def DataInv (s₀ : State) (c : Nat) (m : Mem) : Prop :=
  ∀ k < nb s₀, blockAt m (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k

theorem bAddr_add (s₀ : State) (g k : Nat) :
    bAddr s₀ g + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := by
  simp only [bAddr, Offset.add_add]
  congr 2
  omega

theorem bAddr_toNat {s₀ : State} (hp : SPre s₀) (k : Nat) (hk : k < nb s₀) :
    (bAddr s₀ k).toNat = (dp s₀).toNat + 16 * k := by
  have hw := hp.wrap_d
  rw [bAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 16 * k < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

theorem DataInv.frame {s₀ : State} {c : Nat} {m m' : Mem} {rs : List Region}
    (h : DataInv s₀ c m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, (dR s₀).Disjoint r) : DataInv s₀ c m' := by
  intro k hk
  exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf (fun r hr =>
    (hs r hr).sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega)))).trans (h k hk)

theorem DataInv.initial {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (h : Ready s₀ P s) : DataInv s₀ 0 s.mem :=
  (show DataInv s₀ 0 s₀.mem from fun _ _ => rfl).frame h.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.d_p)

theorem DataInv.batch {s₀ s t : State} {P X Y : Nat → Block} {y : Block}
    {c j : Nat} {hashing : Bool} (hp : SPre s₀) (h : DataInv s₀ c s.mem)
    (hc : c + 8 ≤ nb s₀) (ha : s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c)
    (hb : BatchPost s₀ s P X Y y c j hashing t) : DataInv s₀ (c + 8) t.mem := by
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (16 * (j + i)) = bAddr s₀ (c + i) := by
    intro i
    rw [show 16 * (j + i) = 16 * j + 16 * i by omega, ← Offset.add_add, ha, bAddr_add]
  have hm : Frame [⟨bAddr s₀ c, 128⟩, workR s₀] s.mem t.mem := by
    simpa only [batchR, ha] using hb.frame
  intro k hk
  by_cases hin : c ≤ k ∧ k < c + 8
  · have hi : k - c < 8 := by omega
    have hv := hb.data (k - c) hi
    rw [addr, show c + (k - c) = k by omega] at hv
    rw [hv, h k hk, ite_eq_right (by omega : ¬k < c), ite_eq_left hin.2]
  · have he : (if k < c + 8 then ctb s₀ k else blk s₀ k) =
        (if k < c then ctb s₀ k else blk s₀ k) := by
      split_ifs <;> first | rfl | omega
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hw := hp.wrap_d
        exact Offset.disjoint (dp s₀) (d := 16 * k) (n := 16) (e := 16 * c) (k := 128)
          (by omega) (by omega) (by omega)
      · exact (hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))).sub_right (work_sub_p s₀)), he]
    exact h k hk

end VG.Proof.Gcm.X86_64.StitchAvx8
