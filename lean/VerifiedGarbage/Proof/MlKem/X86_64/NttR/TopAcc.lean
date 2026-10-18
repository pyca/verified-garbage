module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on x86-64: the NTT on registers, to an accumulator

`nttR pb` with pass B storing to the accumulator at `d` (`passBAcc`, as
`checkAcc` says) leaves `NTT` of the polynomial at `rdi` there, in the
accumulator's order (`Acc16`): `nttR_ok`'s proof, with the regions `rsBA d`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly PolyRep wordAt wAddr pR sR Keep Acc16)

/-- The regions of `S` and of the accumulator at `d`: writable and apart. -/
theorem ctxA {s : State} {d : Reg} (hS : pR (s.gpr .rsi) ∈ s.wr) (hX : sR (s.gpr d) ∈ s.wr)
    (hD : (sR (s.gpr d)).Disjoint (pR (s.gpr .rsi))) (h8 : s.gpr .r8 = s.syms tblName) :
    Ctx (rsBA d) s := by
  have cS : (pR (s.gpr .rsi)).Contains (s.gpr .rsi + BitVec.ofNat 64 oS) 512 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; simp [oS]
  have cX : (sR (s.gpr d)).Contains (s.gpr d + BitVec.ofNat 64 0) 512 := by
    unfold Region.Contains
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have sep : Mem.Sep (s.gpr .rsi + BitVec.ofNat 64 oS) 512 (s.gpr d + BitVec.ofNat 64 0) 512 := by
    intro x h1 h2
    rw [Offset.lt_iff x _ (by decide)] at h1
    rw [Offset.lt_iff x _ (by decide)] at h2
    exact hD x (by show (x - s.gpr d).toNat + 1 ≤ 512; omega)
      (by show (x - s.gpr .rsi).toNat + 1 ≤ 1024; simp only [oS] at h1; omega)
  refine ⟨fun k hk => ?_, fun k hk hw => ?_, fun k k' hk hk' hne => ?_, fun k hk => ?_, h8⟩
  · simp only [rsBA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, List.mem_append_right _ hS, cS⟩
    · exact ⟨_, List.mem_append_right _ hX, cX⟩
  · simp only [rsBA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ⟨_, hS, cS⟩
    · exact ⟨_, hX, cX⟩
  · simp only [rsBA, List.length_cons, List.length_nil] at hk hk'
    rcases (by omega : k = 0 ∧ k' = 1 ∨ k = 1 ∧ k' = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sep
    · exact fun x h1 h2 => sep x h2 h1
  · simp only [rsBA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [rlen, rsBA, oS]

/-- Pass B to an accumulator starts from the registers and `S` pass A leaves. -/
theorem reframeA {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16} {X d : Reg} {n : Nat} {σ : St} {s₀ s : State}
    (h : Rel [(.rsi, oS, 256, true), (X, 0, n, false)] L O σ s₀ s) :
    Rel (rsBA d) L O (toBA σ) s₀ s := by
  refine ⟨fun r e he => ?_, fun k j hk hj => ?_, h.eq, ⟨rfl, by simp [toBA, St.set, h.len.2]⟩,
    fun x hx => h.fr x ?_⟩
  · show Hd L O (((σ.set .xmm3 (List.replicate 16 .junk)).reg r).get e) _
    rw [St.reg_set _ _ _ _ h.len.2]
    split
    · rw [get_replicate _ he]; exact Hd.junk _
    · exact h.reg r e he
  · simp only [rsBA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact h.mem 0 j (by simp) hj
    · left
      rw [show (toBA σ).mem.getD 1 [] = junks 16 by simp only [toBA, List.getD_cons_succ, List.getD_cons_zero],
        junks_get]; rfl
  · intro k hk hw
    simp only [List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact hx 0 (by simp [rsBA]) rfl
    · cases hw

theorem outAccOk_get {σ : St} (h : outAccOk σ = true) {w : Nat} (hw : w < 256) :
    Y.get ((σ.mem.getD 1 []).getD (w / 16) []) (w % 16) = .out (accIdx w) :=
  E.beq_eq (List.all_eq_true.1 h w (List.mem_range.2 hw))

/-- `nttR pb` leaves `NTT` of the polynomial at `rdi` in the accumulator at
`d`, if `checkAcc pb d`. -/
theorem nttRAcc_ok {pb : List Instr} {d : Reg} (hc : checkAcc pb d = true) (hd : d = .rdi ∨ d = .r10)
    {s : State} (hS : pR (s.gpr .rsi) ∈ s.wr) (hI : pR (s.gpr .rdi) ∈ s.rd ++ s.wr) (hO : sR (s.gpr d) ∈ s.wr)
    (hDI : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi))) (hDO : (sR (s.gpr d)).Disjoint (pR (s.gpr .rsi)))
    (hred : Reduced s.mem (s.gpr .rdi)) :
    WP isa (nttR pb) s fun s' => Acc16 s'.mem (s.gpr d) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [sR (s.gpr d), pR (s.gpr .rsi)] s.mem s'.mem ∧ Keep [.rax, .r8] s s' := by
  unfold checkAcc at hc
  split at hc <;> [skip; cases hc]
  rename_i σA hA
  split at hc <;> [skip; cases hc]
  rename_i σB hB
  unfold nttR
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok s) fun s1 ⟨h8, hq, hm1, k1⟩ => ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s1.gpr r = s.gpr r := fun r h1 h2 =>
    k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have gdi : s1.gpr .rdi = s.gpr .rdi := g _ (by decide) (by decide)
  have gsi : s1.gpr .rsi = s.gpr .rsi := g _ (by decide) (by decide)
  have gd : s1.gpr d = s.gpr d := g _ (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide)
  let W := inW s.mem (s.gpr .rdi)
  let F := polyAt s.mem (s.gpr .rdi)
  have hW : ∀ p < 256, (W[p]!).toNat = (F[p]!).val := fun p hp => by
    rw [inW_get _ _ hp, (reduced_words hred hp).2, VG.Proof.MlKem.polyAt_val hred (by rw [n_eq]; exact hp)]
  have hM : Model fwdRules (Lf W) (Of W) := model W fun p hp => by
    rw [hW p hp]; have := (F[p]!).isLt; simp only [q] at this; omega
  have hrep : PolyRep 1 W F := fun p hp => VG.Proof.MlKem.X86_64.Rep.of_can (hW p hp)
  have hrel0 : Rel rsA (Lf W) (Of W) initA s1 s1 := by
    refine initA_rel (fun p hp => ?_) (fun p hp => ?_) hq
    · show (LW W 0)[p]! = _
      rw [gdi, hm1]; exact inW_get _ _ hp
    · rw [gdi, hm1]; exact (reduced_words hred hp).1
  have cA : Ctx rsA s1 := ctx2 (by rw [gsi, k1.2.2]; exact hS) (by rw [gdi, k1.2.1, k1.2.2]; exact hI)
    (fun h => by cases h) (by rw [gdi, gsi]; exact hDI) h8
  have cB : Ctx (rsBA d) s1 := ctxA (by rw [gsi, k1.2.2]; exact hS) (by rw [gd, k1.2.2]; exact hO)
    (by rw [gd, gsi]; exact hDO) h8
  refine WP.mono (run_ok hM cA passA hrel0 hA) fun s2 hr2 => ?_
  refine WP.mono (run_ok hM cB pb (reframeA hr2) hB) fun s3 hr3 => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have hb : rbase (rsBA d) s1 1 = s.gpr d := by simp [rbase, rsBA, gd]
    intro w hw
    have h0 := hr3.mem 1 w (by simp [rsBA]) (by simp [rlen, rsBA]; omega)
    rw [outAccOk_get hc hw, hb] at h0
    have e0 := h0.eq rfl
    show (wordAt s3.mem (s.gpr d) w).toNat = _
    rw [e0]
    exact Of_ntt W F hrep (accIdx_lt hw)
  · intro x hx
    show s3.mem x = s.mem x
    rw [← hm1]
    refine hr3.fr x fun k hk hw hlt => ?_
    simp only [rsBA, List.length_cons, List.length_nil] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine hx (pR (s.gpr .rsi)) (by simp) ?_
      simp only [rbase, rlen, rsBA, List.getD_cons_zero, gsi] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr .rsi).toNat + 1 ≤ 1024
      simp only [oS] at hlt; omega
    · refine hx (sR (s.gpr d)) (by simp) ?_
      simp only [rbase, rlen, rsBA, List.getD_cons_succ, List.getD_cons_zero, gd] at hlt
      rw [Offset.lt_iff x _ (by decide)] at hlt
      show (x - s.gpr d).toNat + 1 ≤ 512
      omega
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · show s3.gpr r = s.gpr r
      rw [hr3.gpr]; exact k1.1 r hr
    · show s3.rd = s.rd
      rw [hr3.rd]; exact k1.2.1
    · show s3.wr = s.wr
      rw [hr3.wr]; exact k1.2.2

end VG.Proof.MlKem.X86_64.NttR
