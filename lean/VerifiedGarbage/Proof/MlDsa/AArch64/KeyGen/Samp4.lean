module

import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import all Init.Data.Nat.Bitwise.Basic

/-! ### `MlDsa.AArch64.KeyGen.Seed4`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa (Params Poly IPoly)
open VG.Proof.MlDsa (Reduced PolyIs polyAt poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

theorem copySeed4_generic {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : inB (rbs++wbs) (sc oSA) 32 = true)
    (hdst : inB wbs (sc (oSA4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oSA) 32 (sc (oSA4+34*j)) 32 = true) :
    WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  unfold copySeed4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oSA4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oSA,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oSA),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oSA4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oSA4+34*j))) (sb := .x28) (db := .x10) (so := oSA) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oSA),32⟩ : Region).Disjoint ⟨pa s (sc (oSA4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

theorem copySeed4_ok {S : Nat} {p : Params} (hF : PFacts p) {s : State} (L : Lay S kgR (kgW p) s)
    {j : Nat} (hj : j < 4) : WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  exact copySeed4_generic L (by layd) (by layd) (by layd)

structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : KSamp p σ e 0 s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oSA4+34*k))) 34 =
    seedA (rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ)

end VG.Proof.MlDsa.AArch64.KeyGen

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem slot_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs [.x28]) (seedSlot4 p e j) (.seq (Taint.ofRegs [.x28,.x10]) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 copySeed4 lea
  rw [VG.Proof.MlDsa.KeyGen.ifp (by dsimp only [oSA4]; omega_using [hj] : oSA4+34*j < 4096)]
  with_unfolding_all rfl

end VG.Proof.MlDsa.AArch64.KeyGen

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly minBounds)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA ifp ifn masked_one masked_zero)
open VG.Spec.Sha3 (bytesAt)

theorem seed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oSA4)) k = seedA (rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := by
  unfold seed4
  rw [show pa s (sc oSA4) + BitVec.ofNat 64 (34 * k) = pa s (sc (oSA4 + 34 * k)) from sc_add _ _ _]
  exact h.done k hk

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl, Proof.MlKem.bytesAt_add,
    show 68 = 34 + 34 from rfl, Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds are those of the entries, from `ρ`. -/
theorem GS.seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 4 s) :
    bytesAt s.mem (pa s (sc oSA4)) 136 = seedA (rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      seedA (rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ seedA (rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      seedA (rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (pa s (sc oSA4) + BitVec.ofNat 64 (34 * k)) 34 =
      seedA (rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := fun k hk => seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-! ## The four polynomials -/

theorem coeffAt_poly4 (m : Mem) (a : Addr) (k j : Nat) : coeffAt m (poly4 a k) j = coeffAt m a (256 * k + j) := by
  unfold coeffAt poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega_using []]

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (aP e)) k = pa s (aP (e + k)) := by
  unfold poly4
  rw [show pa s (aP e) + BitVec.ofNat 64 (1024 * k) = pa s (sc (oP e + 1024 * k)) from sc_add _ _ _,
    show oP e + 1024 * k = oP (e + k) by simp only [oP]; omega_using []]

/-- One bound for the four polynomials. -/
theorem bound4 {ρ : Nat → List Byte} {x : Nat → Poly} (h : ∀ k < 4, ∃ b : Spec.MlDsa.Bounds,
    rejNTTPoly b.rejNTT (ρ k) = some (x k)) : ∃ n : Nat, ∀ k < 4, rejNTTPoly n (ρ k) = some (x k) := by
  obtain ⟨b0, h0⟩ := h 0 (by decide)
  obtain ⟨b1, h1⟩ := h 1 (by decide)
  obtain ⟨b2, h2⟩ := h 2 (by decide)
  obtain ⟨b3, h3⟩ := h 3 (by decide)
  refine ⟨max (max b0.rejNTT b1.rejNTT) (max b2.rejNTT b3.rejNTT), fun k hk => ?_⟩
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega_using []) h0
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega_using []) h1
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega_using []) h2
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega_using []) h3


theorem mask4_taint : ∀ j < 80,(taint.check (Taint.ofRegs [.x28]) (mask4 (sc (oP j)))
    (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (mask4 (sc 0)))).isSome = true := by decide +kernel

end VG.Proof.MlDsa.AArch64.KeyGen
