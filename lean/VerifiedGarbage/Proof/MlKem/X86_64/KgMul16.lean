module

import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodiesY
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMul
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulY
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `keygen_mul` reading `Â` as `u16`s

The rows of `keygenMul16Y` (`rowY16`, `Â`'s polynomials 512 bytes apart)
keep `KgMul.RInvG` with the rows of `Â` read as `u16`s (`row16_ok`), and its
first loop `KgMul.NInv` with `e` read as `u16`s (`nttStep16_ok`), so
`KgMul.wp_allg` gives its contract `kgMulK16` (`wp_all16`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What `rowY16` may write: `rax` (the constants), `rcx` (the count) and the
pointers. -/
theorem rowY16_wo {k : Nat} (hk : k = 3 ∨ k = 4) :
    writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowY16 k) = true := by
  rcases hk with rfl | rfl <;> decide +kernel

namespace KgMul

open DecMul (sub_c sub_c0 sub_v in_c in_c0 in_v dis_cc cov_one sx1024 sx2048)
open EncMul (hiR hi_dis_c hi_dis_c0 hi_dis_tab sub_hi in_vec)

/-- Row `i` of `Â`, of `u16`s. -/
abbrev rowW (k : Nat) (s₀ : State) (i : Nat) : List Poly :=
  vecAtW 16 s₀.mem (aP s₀ + BitVec.ofNat 64 (512 * (k * i))) k

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK16 k).pre s₀)
include hp

theorem e16_frame {m : Mem} (hf : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem m) {e : Nat}
    (he : e < k) :
    PolyIsW 16 m (eP s₀ + BitVec.ofNat 64 (512 * e)) (polyAtW 16 s₀.mem (eP s₀ + BitVec.ofNat 64 (512 * e))) := by
  have hs : Region.Sub ⟨eP s₀ + BitVec.ofNat 64 (512 * e), 512⟩ ⟨eP s₀, 512 * k⟩ := Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame hf (fun r hr' => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ((dTE hp).sub_right hs).symm
    · exact ((dSE hp).sub_right hs).symm
    · exact (dEC hp).sub_left hs
  · have := (redE hp) e he
    rwa [show 32 * 16 * e = 512 * e by omega_arith] at this

theorem a16_frame {m : Mem} (hf : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem m) {e : Nat}
    (he : e < k * k) :
    PolyIsW 16 m (aP s₀ + BitVec.ofNat 64 (512 * e)) (polyAtW 16 s₀.mem (aP s₀ + BitVec.ofNat 64 (512 * e))) := by
  have hs : Region.Sub ⟨aP s₀ + BitVec.ofNat 64 (512 * e), 512⟩ ⟨aP s₀, 512 * (k * k)⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame hf (fun r hr' => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ((dTA hp).sub_right hs).symm
    · exact ((dSA hp).sub_right hs).symm
    · exact (dAC hp).sub_left hs
  · have := (redA hp) e he
    rwa [show 32 * 16 * e = 512 * e by omega_arith] at this

end

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK16 k).pre s₀) (hk : k ≤ 4)
include hp hk

set_option linter.unusedSimpArgs false in
/-- An iteration of the first loop: `NTT(s[j])` in place, and `NTT(e[j])` of
`u16`s to `t[j]`. -/
theorem nttStep16_ok {j : Nat} (hj : j < k) {s : State} (hI : NInv k s₀ (ev16 k s₀) 512 j s) :
    WP isa KpkeMul.nttK16 s fun s' => NInv k s₀ (ev16 k s₀) 512 (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hsr : s.rd = [⟨aP s₀, 512 * (k * k)⟩, ⟨eP s₀, 512 * k⟩] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hS := hI.srest j (Nat.le_refl _) hj
  unfold KpkeMul.nttK16 KpkeMul.nttKg
  -- `NTT(s[j])` in place
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = sP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = sP s₀ + BitVec.ofNat 64 (1024 * j) ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hI.r12, hI.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.seq (WP.inline (k := nttOK) BodiesOk.avx2.nttO (rd := [pR (sP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) BodiesOk.avx2.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, vc0_dis (dSC hp) hj, vc0_dis (dSC hp) hj, (rS hp).sub_right (sub_v _ hj),
      (rC hp).sub_right (sub_c0 _), hS.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons ((cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttOK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1, hS.2] at hpost2
  rw [← vecAt_map_get _ _ hj] at hpost2
  rw [hm1] at hf2
  have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by rw [habi2.1 r hr, cs (by decide) k1 r hr]
  have hb2 : Base k s₀ s2 := hI.toBase.step hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (.inl (sub_v _ hj)), .inr (.inr (sub_c0 _))]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dChi (dSC hp) hj, hi_dis_c0 _]) (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) g2
  have hE := e16_frame hp hb2.frame hj
  have hsub : Region.Sub (sR (eP s₀ + BitVec.ofNat 64 (512 * j))) ⟨eP s₀, 512 * k⟩ := Offset.sub_base _ (by omega_arith)
  -- `NTT(e[j])` to `t[j]`
  refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = eP s₀ + BitVec.ofNat 64 (512 * j) ∧
      s3.gpr .rsi = cP s₀ ∧ s3.gpr .r10 = tP s₀ + BitVec.ofNat 64 (1024 * j) ∧ s3.mem = s2.mem ∧
      Keep [.rdi, .rsi, .r10] s2 s3) (by
        vrunm [g2 .r15 (by decide), g2 .rbx (by decide), g2 .rbp (by decide), hI.r15, hI.rbx, hI.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, h3r10, hm3, k3⟩ => ?_)
  have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [k3.gpr (by decide), hb2.rsp]
  have hsr2 : s3.rd = [⟨aP s₀, 512 * (k * k)⟩, ⟨eP s₀, 512 * k⟩] := by rw [k3.2.1, hb2.rd, hp.1]
  have hsw2 : s3.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [k3.2.2, hb2.wr, hp.2.1]
  refine WP.seq (WP.inline (k := nttO16K) nttOBY16_correct (rd := [sR (eP s₀ + BitVec.ofNat 64 (512 * j))])
    (wr := [pR (tP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) (by decide +kernel))
  · simp only [nttO16K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, h3r10, hsp3, hm3, retR]
    exact ⟨trivial, trivial, ((dEC hp).sub_left hsub).sub_right (sub_c0 _), vc0_dis (dTC hp) hj,
      (rT hp).sub_right (sub_v _ hj), (rC hp).sub_right (sub_c0 _), hE.1⟩
  · rw [hsr2, hsw2]
    exact (cov_one (by simp) (show Region.Contains ⟨eP s₀, 512 * k⟩ (eP s₀ + BitVec.ofNat 64 (512 * j)) 512 from
      Offset.contains_base _ (by omega_arith) (by omega_arith))).cons ((cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [hsw2]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttO16K, State.withRegions_gpr, State.withRegions_mem, h3di, h3r10, hm3, hE.2] at hpost4
  rw [← EncMulY.vecAtW16_map_get _ _ hj] at hpost4
  rw [hm3] at hf4
  have g4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by
    rw [habi4.1 r hr, cs (by decide) k3 r hr, g2 r hr]
  have hb4 : Base k s₀ s4 := hb2.step hf4 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl (sub_v _ hj), .inr (.inr (sub_c0 _))]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dChi (dTC hp) hj, hi_dis_c0 _]) (by rw [hrd4, k3.2.1]) (by rw [hwr4, k3.2.2])
    (fun r hr => by rw [habi4.1 r hr, cs (by decide) k3 r hr])
  -- what the two writes keep
  have fS2 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (sP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega_arith) hj' hj hne, vc0_dis (dSC hp) hj']
  have fS4 : ∀ {j'}, j' < k → ∀ r ∈ [pR (tP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (sP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis (dTS hp).symm hj' hj, vc0_dis (dSC hp) hj']
  have fT2 : ∀ {j'}, j' < k → ∀ r ∈ [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (tP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis (dTS hp) hj' hj, vc0_dis (dTC hp) hj']
  have fT4 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (tP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (tP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega_arith) hj' hj hne, vc0_dis (dTC hp) hj']
  -- the next `j`
  vrunm [g4 .r12 (by decide), g4 .r15 (by decide), g4 .rbp (by decide), g4 .r14 (by decide), hI.r12, hI.r15,
    hI.rbp, sx1024, sx512]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun j' hj' => ?_, fun j' hj1 hj2 => ?_, fun j' hj' => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb4.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb4.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .r13 (by decide), hI.r13]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine polyIs_frame hf4 (fS4 (by omega_arith)) ?_
    by_cases h : j' = j
    · subst h; exact hpost2
    · exact polyIs_frame hf2 (fS2 (by omega_arith) h) (hI.sdone j' (by omega_arith))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf4 (fS4 hj2) (polyIs_frame hf2 (fS2 hj2 (by omega_arith)) (hI.srest j' (by omega_arith) hj2))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : j' = j
    · subst h; exact hpost4
    · exact polyIs_frame hf4 (fT4 (by omega_arith) h) (polyIs_frame hf2 (fT2 (by omega_arith)) (hI.tdone j' (by omega_arith)))

end

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK16 k).pre s₀)
include hp

set_option linter.unusedSimpArgs false in
/-- A row of `keygenMul16Y`, by `rowY16`. -/
theorem row16_ok (hk : k ≤ 4) (hk3 : k = 3 ∨ k = 4) {i : Nat} (hi : i < k) {s : State}
    (hI : RInvG k s₀ (ev16 k s₀) 512 (rowW k s₀) accY tabY i s) :
    WP isa (KpkeMul.rowKRs rowY16 k 512) s fun s' => RInvG k s₀ (ev16 k s₀) 512 (rowW k s₀) accY tabY (i + 1) s' ∧
      s'.gpr .r14 = s.gpr .r14 - 1 ∧ s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hsr : s.rd = [⟨aP s₀, 512 * (k * k)⟩, ⟨eP s₀, 512 * k⟩] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hkk : k * k ≤ 64 := Nat.le_trans (Nat.mul_le_mul hk hk) (by decide)
  have hrow : ∀ j < k, k * i + j < k * k := fun j hj => by
    have := Nat.mul_le_mul_left k (show i + 1 ≤ k by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  have ea : ∀ j, aP s₀ + BitVec.ofNat 64 (512 * (k * i)) + BitVec.ofNat 64 (512 * j) =
      aP s₀ + BitVec.ofNat 64 (512 * (k * i + j)) := fun j => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  unfold KpkeMul.rowKRs
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = tP s₀ + BitVec.ofNat 64 (1024 * i) ∧
      s1.gpr .rsi = aP s₀ + BitVec.ofNat 64 (512 * (k * i)) ∧ s1.gpr .rdx = sP s₀ ∧ s1.gpr .rcx = cP s₀ ∧
      s1.mem = s.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s1) (by
        vrunm [hI.r15, hI.r13, hI.r12, hI.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1di, h1si, h1dx, h1cx, hm1, k1⟩ => ?_)
  have hT := hI.trest i (Nat.le_refl _) hi
  have hx : RowY.CtxG (FRep.u16 512) k (aP s₀ + BitVec.ofNat 64 (512 * (k * i))) (sP s₀)
      (tP s₀ + BitVec.ofNat 64 (1024 * i)) (cP s₀) (rowW k s₀ i) (sv k s₀) s1.mem s1.rd s1.wr :=
    { k1 := by omega_arith
      k4 := hk
      fl := by rw [vecAtW_length]
      gl := by rw [List.length_map, vecAt_length]
      F := fun j hj => by
        show PolyIsW 16 _ _ _
        rw [vecAtW16_get _ _ hj, ea, hm1]; exact a16_frame hp hI.frame (hrow j hj)
      G := fun j hj => by rw [hm1]; exact hI.shat j hj
      dF := fun j hj => by
        rw [ea]
        exact ((dTA hp).sub_left (sub_v _ hi)).sub_right
          (Offset.sub_base (n := 512) (k := 512 * (k * k)) _ (by have := hrow j hj; omega_arith))
      dG := fun j hj => vr_dis (dTS hp) hi hj
      dT := vc_dis (dTC hp) hi (by decide)
      inF := fun j hj => by
        rw [ea, k1.2.1, k1.2.2, hsr]
        exact ⟨⟨aP s₀, 512 * (k * k)⟩, by simp,
          Offset.contains_base (n := 512) _ (by have := hrow j hj; omega_arith) (by have := hrow j hj; omega_arith)⟩
      inG := fun j hj => by
        rw [k1.2.1, k1.2.2, hsw]; exact ⟨_, by simp, in_vec _ (by omega_arith) hj⟩
      inTab := by rw [k1.2.1, k1.2.2, hsw]; exact ⟨_, by simp, in_c (by decide)⟩
      inT := by rw [k1.2.2, hsw]; exact ⟨_, by simp, in_vec _ (by omega_arith) hi⟩
      tab := by rw [hm1]; exact hI.tab
      red := by rw [hm1]; exact hT.1 }
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8]
    (RowY.rowYg_ok (FRep.u16 512) hx h1si h1dx h1di h1cx) (rowY16_wo hk3)) fun s2 ⟨⟨hP2, hf2, hrd2, hwr2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have cs : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => k12.gpr (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hR4 : PolyIs s2.mem (tP s₀ + BitVec.ofNat 64 (1024 * i)) (tgtG k s₀ (ev16 k s₀) (rowW k s₀) i) := by
    rw [hm1, hT.2, dotP_full (vecAtW_length _ _ _ _) (by rw [List.length_map, vecAt_length]), add_comm_poly] at hP2
    exact hP2
  rw [hm1] at hf2
  have hb4 : Base k s₀ s2 := hI.toBase.step hf2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl (sub_v _ hi))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dChi (dTC hp) hi)
    (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) cs
  have hk31 : 512 * k < 2 ^ 31 := by omega_arith
  have fo : ∀ r ∈ [pR (tP s₀ + BitVec.ofNat 64 (1024 * i))], (tabR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (vc_dis (dTC hp) hi (by decide)).symm
  have g4 : ∀ r, r ∉ [Reg.rdi, .rsi, .rdx, .rcx, .rax, .rcx, .rdx, .rsi, .rdi, .r8] → s2.gpr r = s.gpr r :=
    fun r hr => k12.gpr hr
  vrunm [g4 .r13 (by decide), g4 .r15 (by decide), g4 .r14 (by decide), hI.r13, hI.r15, sx1024, sx_ofNat hk31]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun i' hi' => ?_, fun i' h1 h2 => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb4.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb4.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .rbp (by decide), hI.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .r12 (by decide), hI.r12]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ, Nat.mul_add]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact tabY.frame hf2 fo hI.tab
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vr_dis (dTS hp).symm hj hi) (hI.shat j hj)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i' = i
    · subst h; exact hR4
    · exact polyIs_frame hf2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact vv_dis _ (by omega_arith) (by omega_arith) hi h)
        (hI.tdone i' (by omega_arith))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vv_dis _ (by omega_arith) h2 hi (by omega_arith))
      (hI.trest i' (by omega_arith) h2)

/-- `keygenMul16Y k` meets `kgMulK16 k`. -/
theorem wp_all16 (hk3 : k = 3 ∨ k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (innerG KpkeMul.nttK16 (KpkeMul.rowKRs rowY16 k 512) Bodies.avx2 k) = true) :
    WP isa (keygenMul16Y k) s₀ fun s' => gprPreserved s₀ s' ∧ (kgMulK16 k).post s₀ s' :=
  wp_allg hp (by omega_arith) BodiesOk.avx2 (by omega_arith) (se := 512) (ra := 512) (rA := rowW k s₀) (vecAtW_length _ _ _ _)
    (fun _ hj _ hI => nttStep16_ok hp (by omega_arith) hj hI) (by simp [matAtW])
    (fun i hi => by simp [matAtW, List.getD_eq_getElem?_getD, List.getElem?_range hi])
    (fun _ hi _ hR => row16_ok hp (by omega_arith) hk3 hi hR) hwo

end

end KgMul

end VG.Proof.MlKem.X86_64
