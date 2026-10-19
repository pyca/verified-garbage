module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvModel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers

`nttIR pb` (`pb` pass B reading the input as `src` says, as `checkI` says)
leaves `NTT⁻¹` of the input at `rdi` there, as `u32`s (`nttIR_ok`): after
`pro`, the terms of `initIB src` hold, with the polynomial's words after `st`
layers `LfI W st` for the canonical words `W` of its coefficients and their
outputs `OfI W`; pass B keeps them (`run_ok`) in the regions `rsA`, pass A
in the regions `rsB .rdi`, and `checkI` says the output's terms are `OfI W`,
which `OfI_nttInv` takes to `NTT⁻¹`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly PolyRep wordAt wAddr pR Keep)

/-- The input `F` at `p`, as `src` says: an accumulator (coefficient
`accIdx w` in word `w`). -/
def InOk : InvIn → Mem → Addr → Poly → Prop
  | .acc, m, p, F => ∀ w < 256, (wordAt m p w).toNat = (F[accIdx w]!).val

/-- The canonical words of the coefficients. -/
def canW (F : Poly) : WPoly := F.map fun x => BitVec.ofNat 16 x.val

theorem canW_get (F : Poly) {i : Nat} (hi : i < 256) : ((canW F)[i]!).toNat = (F[i]!).val := by
  rw [canW, getElem!_map _ _ hi, BitVec.toNat_ofNat]
  have := (F[i]!).isLt; simp only [q] at this; omega

theorem accIdx_lt (j : Nat) (hj : j < 256) : accIdx j < 256 := by unfold accIdx; omega

theorem accTerms_get {j : Nat} (hj : j < 512) :
    Y.get (accTerms.getD (j / 16) []) (j % 16) = if j < 256 then .lv 0 (accIdx j) else .junk := by
  unfold accTerms
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, Y.get, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range (Nat.mod_lt _ (by decide)), Option.map_some, Option.getD_some,
      show 16 * (j / 16) + j % 16 = j by omega]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), ← List.getD_eq_getElem?_getD]
    exact junks_get _ _ _

/-- The input's words hold the terms of `srcTerms src`. -/
theorem src_hd {src : InvIn} {m : Mem} {p : Addr} {F : Poly} (h : InOk src m p F) {O : Nat → BitVec 16}
    {j : Nat} (hj : j < 512) :
    Hd (LfI (canW F)) O (Y.get ((srcTerms src).getD (j / 16) []) (j % 16)) (wordAt m p j) := by
  cases src with
  | acc =>
    rw [srcTerms, accTerms_get hj]
    split
    · rename_i hj'
      refine Hd.of_eq (BitVec.eq_of_toNat_eq ?_)
      simp only [E.eval, LfI, LIW, List.take_zero, List.foldl_nil]
      have ha : accIdx j < 256 := accIdx_lt j hj'
      rw [canW_get _ ha, h j hj']
    · exact Hd.junk _

theorem initIB_reg (src : InvIn) (r : XReg) :
    (initIB src).reg r = if r = .xmm15 then List.replicate 16 (.c qN) else List.replicate 16 .junk := by
  cases r <;> rfl

theorem initIB_rel {src : InvIn} {F : Poly} {O : Nat → BitVec 16} {s₁ : State}
    (h : InOk src s₁.mem (s₁.gpr .rdi) F) (hq : ∀ e < 16, wd s₁ .xmm15 e = 3329) :
    Rel rsA (LfI (canW F)) O (initIB src) s₁ s₁ := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, by cases s₁; rfl,
    ⟨by simp only [initIB, rsA, List.length_cons, List.length_nil], by simp [initIB]⟩, fun _ _ => rfl⟩
  · rw [initIB_reg]
    split
    · rename_i hr; subst hr
      rw [get_replicate _ he, hq e he]; exact Hd.of_eq rfl
    · rw [get_replicate _ he]; exact Hd.junk _
  · simp only [rsA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left
      rw [show (initIB src).mem.getD 0 [] = junks 16 by simp only [initIB, List.getD_cons_zero], junks_get]; rfl
    · have hb : rbase rsA s₁ 1 = s₁.gpr .rdi := by simp [rbase, rsA]
      rw [show (initIB src).mem.getD 1 [] = srcTerms src by
        simp only [initIB, List.getD_cons_succ, List.getD_cons_zero], hb]
      exact src_hd h hj

/-- `nttIR pb` leaves `NTT⁻¹` of the input at `rdi` there, if `checkI src pb`. -/
theorem nttIR_ok {src : InvIn} {pb : List Instr} (hc : checkI src pb = true) {s : State} {F : Poly}
    (hS : pR (s.gpr .rsi) ∈ s.wr) (hO : pR (s.gpr .rdi) ∈ s.wr)
    (hD : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hin : InOk src s.mem (s.gpr .rdi) F) :
    WP isa (nttIR pb) s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv F) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold checkI at hc
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  unfold nttIR
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  let W := canW F
  have hM : Model invRules (LfI W) (OfI W) := modelI W fun p hp => by
    rw [canW_get _ hp]; have := (F[p]!).isLt; simp only [q] at this; omega
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (canW_get F hp)
  have hrel0 : Rel rsA (LfI W) (OfI W) (initIB src) s1 s1 :=
    initIB_rel (by rw [gdi, hm1]; exact hin) hq
  have cB : Ctx rsA s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO)
    (fun h => by cases h) (by rw [gdi, gsi]; exact hD) h8
  have cA : Ctx (rsB .rdi) s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS)
    (by rw [gdi, k1.2.1, k1.2.2]; exact List.mem_append_right _ hO) (fun _ => by rw [gdi, k1.2.2]; exact hO)
    (by rw [gdi, gsi]; exact hD) h8
  refine WP.mono (run_ok hM cB pb hrel0 hB) fun s2 hr2 => ?_
  refine WP.mono (run_ok hM cA passIA (reframe hr2) hA) fun s3 hr3 => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have hb : rbase (rsB .rdi) s1 1 = s.gpr .rdi := by simp [rbase, rsB, gdi]
    refine VG.Proof.MlKem.polyIs_of_toNat fun p hp => ?_
    rw [n_eq] at hp
    have h0 := hr3.mem 1 (2 * p) (by simp [rsB]) (by simp [rlen, rsB]; omega)
    have h1 := hr3.mem 1 (2 * p + 1) (by simp [rsB]) (by simp [rlen, rsB]; omega)
    rw [outOk_get hc (by omega), hb] at h0 h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show 2 * p / 2 = p by omega] at h0
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at h1
    have e0 := h0.eq rfl
    have e1 := h1.eq rfl
    show (coeffAt s3.mem (s.gpr .rdi) p).toNat = _
    rw [coeff_words, toNat_app16, e0, e1]
    simp only [E.eval]
    rw [OfI_nttInv W F hrep hp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
  · intro x hx
    show s3.mem x = s.mem x
    rw [← hm1]
    refine hr3.fr x fun k hk hw hlt => ?_
    simp only [rsB, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine hx (pR (s.gpr .rsi)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_zero, gsi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rsi).toNat + 1 ≤ 1024
      simp only [oS] at hlt; omega
    · refine hx (pR (s.gpr .rdi)) (by simp) ?_
      simp only [rbase, rlen, rsB, List.getD_cons_succ, List.getD_cons_zero, gdi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rdi).toNat + 1 ≤ 1024
      omega
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · show s3.gpr r = s.gpr r
      rw [hr3.gpr]; exact k1.1 r hr
    · show s3.rd = s.rd
      rw [hr3.rd]; exact k1.2.1
    · show s3.wr = s.wr
      rw [hr3.wr]; exact k1.2.2

end VG.Proof.MlKem.X86_64.NttR
