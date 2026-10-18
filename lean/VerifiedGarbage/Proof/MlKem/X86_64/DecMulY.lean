module

public import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
public import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
public import VerifiedGarbage.Proof.MlKem.X86_64.NttAccY

/-!
# ML-KEM on x86-64: `vg_mlkem*_decrypt_mul_avx2`, row by row

`decryptMulY k` (`Impl/MlKem/X86_64/KpkeMul.lean`) computes each
`û[j] = NTT(u'[j])` to the accumulator at `scratch + 1024 + 512 j` (`yA`,
`nttAccY`, `NInv`); then the sum of the products of `ŝ` and `û` in one row
(`rowEY`, `RowEY.lean`) to the accumulator at `w`, and `NTT⁻¹` of it to `w`
(`nttInvAccY`). The prologue and epilogue are `decryptMul`'s
(`DecMul.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The accumulators of the `NTT`s, in `scratch` -/

/-- Accumulator `j`, at `C + 1024 + 512 j`. -/
abbrev yA (C : Addr) (j : Nat) : Addr := C + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (512 * j)

theorem yA_eq (C : Addr) (j : Nat) : yA C j = C + BitVec.ofNat 64 (1024 + 512 * j) := by
  rw [yA, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem yA_succ (C : Addr) (j : Nat) : yA C j + BitVec.ofNat 64 512 = yA C (j + 1) := by
  rw [yA, yA, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

theorem yA_zero (C : Addr) : C + BitVec.ofNat 64 1024 = yA C 0 := by
  rw [yA, Nat.mul_zero, add_ofNat_zero]

theorem yA_sub {C : Addr} {j : Nat} (hj : j < 4) : Region.Sub (sR (yA C j)) (cR C) := by
  rw [yA_eq]; exact DecMul.sub_c (by omega)

theorem yA_in {C : Addr} {j : Nat} (hj : j < 4) : (cR C).Contains (yA C j) 512 := by
  rw [yA_eq]; exact DecMul.in_c (by omega)

theorem yA_dis_c0 (C : Addr) (j : Nat) (hj : j < 4) : (sR (yA C j)).Disjoint (pR C) := by
  rw [yA_eq]; exact Offset.disjoint_base C (by omega) (by omega)

theorem yA_dis {C : Addr} {i j : Nat} (hi : i < 4) (hj : j < 4) (hne : i ≠ j) :
    (sR (yA C i)).Disjoint (sR (yA C j)) := by
  rw [yA_eq, yA_eq]; exact Offset.disjoint C (by omega) (by omega) (by omega)

theorem yA_dis_tab {C : Addr} {j : Nat} (hj : j < 4) : (sR (yA C j)).Disjoint (tabR C) := by
  rw [yA_eq]; exact Offset.disjoint C (.inl (by omega)) (by omega) (by omega)

theorem slot_dis_yA {C : Addr} {d j : Nat} (h3 : 3072 ≤ d) (h8 : d + 8 ≤ 3120) (hj : j < 4) :
    Region.Disjoint ⟨C + BitVec.ofNat 64 d, 8⟩ (sR (yA C j)) := by
  rw [yA_eq]; exact Offset.disjoint C (.inr (by omega)) (by omega) (by omega)

theorem sR_sub_pR (p : Addr) : Region.Sub (sR p) (pR p) := Region.sub_prefix (by decide)

theorem pR_contains_sR (p : Addr) : (pR p).Contains p 512 := by
  simpa using Offset.contains_base p (d := 0) (n := 512) (k := 1024) (by decide) (by decide)

theorem sx512 : BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 := by decide

namespace DecMulY

open DecMul (wP sP uP cP sv uv sub_c sub_c0 sub_v in_c in_c0 in_v cov_one sx1024 saved_keep slots_bound
  slot_dis_c0 slot_dis_tab save_eq restore_eq dis_wc dis_wc0 dis_uc0 dis_sw ret_c ret_c0 s_frame u_frame)

/-- After `j` `NTT`s. -/
structure NInv (k : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = cP s₀
  rbp : s.gpr .rbp = wP s₀
  r12 : s.gpr .r12 = sP s₀
  r13 : s.gpr .r13 = uP s₀ + BitVec.ofNat 64 (1024 * j)
  r9 : s.gpr .r9 = yA (cP s₀) j
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s.mem
  saved : Spill.Saved s.mem (cP s₀) s₀.gpr KpkeMul.slots
  tab : TabY s.mem (cP s₀)
  acc : ∀ i < j, Acc16 s.mem (yA (cP s₀) i) (uv k s₀)[i]!

section
variable {k : Nat} {s₀ : State} (hp : (decMulK k).pre s₀) (hk : k ≤ 4)
include hp hk

set_option linter.unusedSimpArgs false in
/-- `û[j] = NTT(u'[j])` to accumulator `j`. -/
theorem term_ok {j : Nat} (hj : j < k) {s : State} (hI : NInv k s₀ j s) :
    WP isa KpkeMul.nttTermY s fun s' => NInv k s₀ (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hj4 : j < 4 := by omega
  have hsr : s.rd = [vR (sP s₀) k, vR (uP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [pR (wP s₀), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hU := u_frame hp hI.frame hj
  unfold KpkeMul.nttTermY
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = yA (cP s₀) j ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hI.r13, hI.rbx, hI.r9]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.seq (WP.inline (k := nttAccK) nttAccY_correct (rd := [pR (uP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [sR (yA (cP s₀) j), pR (cP s₀)]) ?_ ?_ ?_ (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_))
  · simp only [nttAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, dis_uc0 hp hj, yA_dis_c0 _ _ hj4,
      by rw [yA_eq]; exact ret_c hp (o := 1024 + 512 * j) (n := 512) (by omega), ret_c0 hp, hU.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_v _ hk hj)).cons ((cov_one (by simp) (yA_in hj4)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (yA_in hj4)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttAccK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1] at hpost2
  rw [hm1] at hf2
  have cs : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by
    rw [habi2.1 r hr]; exact k1.gpr (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have fo : ∀ r ∈ [sR (yA (cP s₀) j), pR (cP s₀)], Region.Sub r (cR (cP s₀)) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [yA_sub hj4, sub_c0 _]
  obtain ⟨hA2, hg2⟩ := hpost2
  have g2 : ∀ r, r ∉ [Reg.rax, .r8, .rdi, .rsi, .r10] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have e := hg2 r hr.1 hr.2.1
    rw [e, k1.gpr (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  have hj' : j < (uv k s₀).length := by rw [List.length_map, vecAt_length]; exact hj
  vrunm [g2 .r13 (by decide), g2 .r9 (by decide), g2 .r14 (by decide), hI.r13, hI.r9, sx1024, sx512]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .rbx (by decide), hI.rbx]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .rbp (by decide), hI.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .r12 (by decide), hI.r12]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact yA_succ _ _
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .rsp (by decide), hI.rsp]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]
    rw [hrd2, k1.2.1, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]
    rw [hwr2, k1.2.2, hI.wr]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact hI.frame.trans (hf2.sub fun r hr => ⟨cR (cP s₀), by simp, fo r hr⟩)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine saved_keep hI.saved hf2 fun r hr d h3 h8 => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [slot_dis_yA h3 h8 hj4, slot_dis_c0 h3 h8]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine tabY.frame hf2 (fun r hr => ?_) hI.tab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(yA_dis_tab hj4).symm, (DecMul.prod_dis (cP s₀)).2.2.2.1.symm]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i < j
    · refine acc16_frame hf2 (fun r hr => ?_) (hI.acc i h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [yA_dis (by omega) hj4 (by omega), yA_dis_c0 _ _ (by omega)]
    · obtain rfl : i = j := by omega
      rw [vecAt_map_get _ _ hj, ← hU.2]
      exact hA2

omit hk in
/-- After the `NTT`s: the row of products to `w`, and `NTT⁻¹` of it. -/
theorem row_ok (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hrw : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowEY 1024 k) = true) {s : State}
    (hI : NInv k s₀ k s) :
    WP isa (KpkeMul.rowInvY [.mov .rsi (.reg .r12)] 1024 k) s fun s' =>
      s'.gpr .rbx = cP s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s'.mem ∧ Spill.Saved s'.mem (cP s₀) s₀.gpr KpkeMul.slots ∧
      PolyIs s'.mem (wP s₀) (nttInv (dot (sv k s₀) (uv k s₀))) := by
  have hsr : s.rd = [vR (sP s₀) k, vR (uP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [pR (wP s₀), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  unfold KpkeMul.rowInvY
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = wP s₀ ∧ s1.gpr .rsi = sP s₀ ∧
      s1.gpr .rdx = cP s₀ + BitVec.ofNat 64 1024 ∧ s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx] s s1) (by
        vrunm [hI.rbp, hI.r12, hI.rbx, sx1024]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1dx, h1cx, hm1, k1⟩ => ?_)
  have hr1 : s1.rd ++ s1.wr = [vR (sP s₀) k, vR (uP s₀) k] ++ [pR (wP s₀), cR (cP s₀)] := by
    rw [k1.2.1, k1.2.2, hsr, hsw]
  have hx : RowEY.Ctx 1024 k (sP s₀) (cP s₀ + BitVec.ofNat 64 1024) (wP s₀) (cP s₀) (sv k s₀) (uv k s₀)
      s1.mem s1.rd s1.wr :=
    { k1 := hk1
      k4 := hk4
      fl := by rw [vecAt_length]
      gl := by rw [List.length_map, vecAt_length]
      F := fun j hj => by rw [hm1]; exact s_frame hp hI.frame hj
      G := fun j hj => by rw [hm1]; exact hI.acc j hj
      dF := fun j hj => (dis_sw hp hj).symm.sub_left (sR_sub_pR _)
      dG := fun j hj => by
        show (sR (wP s₀)).Disjoint (sR (yA (cP s₀) j))
        rw [yA_eq]; exact (dis_wc hp (o := 1024 + 512 * j) (n := 512) (by omega)).sub_left (sR_sub_pR _)
      dT := (dis_wc hp (o := 3328) (n := 256) (by decide)).sub_left (sR_sub_pR _)
      inF := fun j hj => by rw [hr1]; exact ⟨_, by simp, in_v _ hk4 hj⟩
      inG := fun j hj => by rw [hr1]; exact ⟨_, by simp, yA_in (C := cP s₀) (by omega)⟩
      inTab := by rw [hr1]; exact ⟨_, by simp, in_c (by decide)⟩
      inA := by rw [k1.2.2, hsw]; exact ⟨_, by simp, pR_contains_sR _⟩
      tab := by rw [hm1]; exact hI.tab }
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (RowEY.rowEY_ok hx h1si h1dx h1di h1cx) hrw)
    fun s2 ⟨⟨hA2, hf2, hrd2, hwr2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  rw [hm1] at hf2
  have hf2' : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s2.mem := hI.frame.trans (hf2.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sR_sub_pR _⟩)
  have hs2 : Spill.Saved s2.mem (cP s₀) s₀.gpr KpkeMul.slots := saved_keep hI.saved hf2 fun r hr d h3 h8 => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((dis_wc hp (o := d) (n := 8) (by omega)).sub_left (sR_sub_pR _)).symm
  -- `NTT⁻¹` of the sum
  refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = wP s₀ ∧ s3.gpr .rsi = cP s₀ ∧ s3.mem = s2.mem ∧
      Keep [.rdi, .rsi] s2 s3) (by
        vrunm [k12.gpr (by decide : Reg.rbp ∉ _), k12.gpr (by decide : Reg.rbx ∉ _), hI.rbx, hI.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3di, h3si, hm3, k3⟩ => ?_)
  have k13 := k12.trans k3
  have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [k13.gpr (by decide), hI.rsp]
  have hsw3 : s3.wr = [pR (wP s₀), cR (cP s₀)] := by rw [k3.2.2, hwr2, k1.2.2, hsw]
  have hA3 : Acc16 s3.mem (wP s₀) (dotP (sv k s₀) (uv k s₀) k) := by rw [hm3]; exact hA2
  refine WP.inline (k := invAccK accY) nttInvAccY_correct (rd := []) (wr := [pR (wP s₀), pR (cP s₀)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_)
  · simp only [invAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, hsp3, retR]
    exact ⟨trivial, trivial, dis_wc0 hp, hp.2.2.2.2.2.2.2.1, ret_c0 hp, ⟨_, hA3⟩⟩
  · rw [hsw3]
    exact Covers.right ((cov_one (by simp) (Region.contains_self _ _)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [hsw3]
    exact (cov_one (by simp) (Region.contains_self _ _)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [invAccK, State.withRegions_gpr, State.withRegions_mem, h3di] at hpost4
  rw [hm3] at hf4
  refine ⟨by rw [habi4.1 .rbx (by decide), k13.gpr (by decide), hI.rbx],
    by rw [habi4.1 .rsp (by decide), hsp3], by rw [hrd4, k3.2.1, hrd2, k1.2.1, hI.rd],
    by rw [hwr4, k3.2.2, hwr2, k1.2.2, hI.wr], hf2'.trans (hf4.sub fun r hr => ?_), saved_keep hs2 hf4 ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨_, by simp, fun _ h => h⟩, ⟨_, by simp, sub_c0 _⟩]
  · intro r hr d h3 h8
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(dis_wc hp (o := d) (n := 8) (by omega)).symm, slot_dis_c0 h3 h8]
  · rw [← dotP_full (vecAt_length _ _ _) (by rw [List.length_map, vecAt_length])]
    exact hpost4 _ hA3

/-- The code inside the MXCSR region. -/
abbrev innerY (k : Nat) : Prog isa :=
  .seq (.block KpkeMul.startY) (.seq (.loop KpkeMul.nttTermY .ne) (KpkeMul.rowInvY [.mov .rsi (.reg .r12)] 1024 k))

/-- The function but for the restore of the callee-saved registers, inline. -/
theorem body_ok (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (innerY k) = true)
    (hrw : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowEY 1024 k) = true) :
    WP isa (.seq (.block (KpkeMul.save ++ ([.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi),
      .mov .r13 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))] : List Instr)))
      (withMxcsr .rbx oMx (innerY k))) s₀ fun s5 => s5.gpr .rbx = cP s₀ ∧ s5.gpr .rsp = s₀.gpr .rsp ∧
      s5.rd = s₀.rd ∧ s5.wr = s₀.wr ∧ Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s5.mem ∧
      PolyIs s5.mem (wP s₀) (nttInv (dot (sv k s₀) (uv k s₀))) := by
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  refine WP.seq ?_
  rw [save_eq]
  refine Spill.save_then .rcx KpkeMul.slots (fun p hp' => ⟨_, hcw, in_c (by have := slots_bound p hp'; omega)⟩) ?_
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rbx = cP s₀ ∧ s1.gpr .rbp = wP s₀ ∧ s1.gpr .r12 = sP s₀ ∧
      s1.gpr .r13 = uP s₀ ∧ s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.gpr .rsp = s₀.gpr .rsp ∧ s1.rd = s₀.rd ∧
      s1.wr = s₀.wr ∧ s1.mem = Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (by
        vrunm
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega) fun s1 ⟨h1bx, h1bp, h112, h113, h114, h1sp, h1rd, h1wr, hm1⟩ => ?_
  have h0 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 768) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 772) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  refine WP.mono (withMxcsr_ok' (r := .rbx) (by decide) _ (by decide) h1bx h0 h4 hwo
    (Q := fun s' => s'.gpr .rbx = cP s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s'.mem ∧ Spill.Saved s'.mem (cP s₀) s₀.gpr KpkeMul.slots ∧
      PolyIs s'.mem (wP s₀) (nttInv (dot (sv k s₀) (uv k s₀))))
    (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, hq4, hf5, k5⟩ => ?_
  · -- the table, the `NTT`s, the row
    have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := fun r hr =>
      k2.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    refine WP.seq ?_
    unfold KpkeMul.startY
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .rcx = cP s₀ ∧ s3.mem = s2.mem ∧ Keep [.rcx] s2 s3) (by
        vrunm [g2 .rbx (by decide), h1bx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3cx, hm3, k3⟩ => ?_
    rw [WP.block_append_iff]
    have hin : InRegions s3.wr (s3.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
      rw [k3.2.2, k2.2.2, h1wr, h3cx]; exact ⟨cR (cP s₀), hcw, in_c (by decide)⟩
    refine WP.mono (tabAccY_wp s3 hin) fun s4 ⟨hT4, hf4, k4⟩ => ?_
    rw [h3cx] at hT4 hf4
    have k24 := (k3.trans k4)
    refine WP.mono (Q := fun (s6 : State) => s6.gpr .r9 = yA (cP s₀) 0 ∧ s6.mem = s4.mem ∧ Keep [.r9] s4 s6) (by
        vrunm [k24.gpr (by decide : Reg.rbx ∉ _), g2 .rbx (by decide), h1bx, sx1024]
        refine ⟨yA_zero _, fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s6 ⟨h6r9, hm6, k6⟩ => ?_
    have k26 := k24.trans k6
    have e6 : ∀ r ∈ calleeSaved, s6.gpr r = s1.gpr r := fun r hr => by
      rw [k26.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h]), g2 r hr]
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (NInv k s₀)
      (fun j hj u hI _ => term_ok hp hk hj hI) (fun u hI => row_ok hp hk0 hk hrw hI) ?_
      (by rw [e6 .r14 (by decide), h114]))
    have hsv : Spill.Saved (Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (cP s₀) s₀.gpr KpkeMul.slots :=
      Spill.saveMem_saved _ _ _ _ (by decide)
    rw [← hm1] at hsv
    rw [hm3] at hf4
    refine ⟨by rw [e6 .rbx (by decide), h1bx], by rw [e6 .rbp (by decide), h1bp], by rw [e6 .r12 (by decide), h112],
      by rw [e6 .r13 (by decide), h113, Nat.mul_zero, add_ofNat_zero], h6r9, by rw [e6 .rsp (by decide), h1sp],
      by rw [k26.2.1, k2.2.1, h1rd], by rw [k26.2.2, k2.2.2, h1wr], ?_, ?_, by rw [hm6]; exact hT4,
      fun i hi => absurd hi (by omega)⟩
    · rw [hm6]
      refine (Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots
        (L := 4096) (fun p hp' => by have := slots_bound p hp'; omega) (by decide)).sub
        (fun r hr => ⟨_, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩) |>.trans ?_
      rw [← hm1]
      refine (f2.sub fun r hr => ⟨cR (cP s₀), by simp, ?_⟩).trans (hf4.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact sub_c (by decide)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, sub_c (by decide)⟩
    · rw [hm6]
      refine saved_keep (saved_keep hsv f2 ?_) hf4 ?_ <;> intro r hr d h3 h8
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact slot_dis_tab h3 h8
  · obtain ⟨h4bx, h4sp, h4rd, h4wr, hf4, _, hW4⟩ := hq4
    have hmx : ∀ r ∈ [mxR (cP s₀)], Region.Sub r (cR (cP s₀)) := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)
    refine ⟨by rw [k5.gpr (by decide), h4bx], by rw [k5.gpr (by decide), h4sp], by rw [k5.2.1, h4rd],
      by rw [k5.2.2, h4wr], hf4.trans (hf5.sub fun r hr => ⟨cR (cP s₀), by simp, hmx r hr⟩), ?_⟩
    refine polyIs_frame hf5 (fun r hr => ?_) hW4
    simp only [List.mem_singleton] at hr; subst hr
    exact dis_wc hp (by decide)

/-- The whole function. -/
theorem wp_all (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (innerY k) = true)
    (hrw : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowEY 1024 k) = true) :
    WP isa (decryptMulY k) s₀ fun s' => gprPreserved s₀ s' ∧ (decMulK k).post s₀ s' := by
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  unfold decryptMulY
  refine WP.seq ?_
  rw [save_eq]
  refine Spill.save_then .rcx KpkeMul.slots (fun p hp' => ⟨_, hcw, in_c (by have := slots_bound p hp'; omega)⟩) ?_
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rbx = cP s₀ ∧ s1.gpr .rbp = wP s₀ ∧ s1.gpr .r12 = sP s₀ ∧
      s1.gpr .r13 = uP s₀ ∧ s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.gpr .rsp = s₀.gpr .rsp ∧ s1.rd = s₀.rd ∧
      s1.wr = s₀.wr ∧ s1.mem = Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (by
        vrunm
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega) fun s1 ⟨h1bx, h1bp, h112, h113, h114, h1sp, h1rd, h1wr, hm1⟩ => ?_
  have h0 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 768) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 772) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  refine WP.seq (WP.mono (withMxcsr_ok' (r := .rbx) (by decide) _ (by decide) h1bx h0 h4 hwo
    (Q := fun s' => s'.gpr .rbx = cP s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s'.mem ∧ Spill.Saved s'.mem (cP s₀) s₀.gpr KpkeMul.slots ∧
      PolyIs s'.mem (wP s₀) (nttInv (dot (sv k s₀) (uv k s₀))))
    (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, hq4, hf5, k5⟩ => ?_)
  · -- the table, the `NTT`s, the row
    have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := fun r hr =>
      k2.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    refine WP.seq ?_
    unfold KpkeMul.startY
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .rcx = cP s₀ ∧ s3.mem = s2.mem ∧ Keep [.rcx] s2 s3) (by
        vrunm [g2 .rbx (by decide), h1bx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3cx, hm3, k3⟩ => ?_
    rw [WP.block_append_iff]
    have hin : InRegions s3.wr (s3.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
      rw [k3.2.2, k2.2.2, h1wr, h3cx]; exact ⟨cR (cP s₀), hcw, in_c (by decide)⟩
    refine WP.mono (tabAccY_wp s3 hin) fun s4 ⟨hT4, hf4, k4⟩ => ?_
    rw [h3cx] at hT4 hf4
    have k24 := (k3.trans k4)
    refine WP.mono (Q := fun (s6 : State) => s6.gpr .r9 = yA (cP s₀) 0 ∧ s6.mem = s4.mem ∧ Keep [.r9] s4 s6) (by
        vrunm [k24.gpr (by decide : Reg.rbx ∉ _), g2 .rbx (by decide), h1bx, sx1024]
        refine ⟨yA_zero _, fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s6 ⟨h6r9, hm6, k6⟩ => ?_
    have k26 := k24.trans k6
    have e6 : ∀ r ∈ calleeSaved, s6.gpr r = s1.gpr r := fun r hr => by
      rw [k26.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h]), g2 r hr]
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (NInv k s₀)
      (fun j hj u hI _ => term_ok hp hk hj hI) (fun u hI => row_ok hp hk0 hk hrw hI) ?_
      (by rw [e6 .r14 (by decide), h114]))
    have hsv : Spill.Saved (Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (cP s₀) s₀.gpr KpkeMul.slots :=
      Spill.saveMem_saved _ _ _ _ (by decide)
    rw [← hm1] at hsv
    rw [hm3] at hf4
    refine ⟨by rw [e6 .rbx (by decide), h1bx], by rw [e6 .rbp (by decide), h1bp], by rw [e6 .r12 (by decide), h112],
      by rw [e6 .r13 (by decide), h113, Nat.mul_zero, add_ofNat_zero], h6r9, by rw [e6 .rsp (by decide), h1sp],
      by rw [k26.2.1, k2.2.1, h1rd], by rw [k26.2.2, k2.2.2, h1wr], ?_, ?_, by rw [hm6]; exact hT4,
      fun i hi => absurd hi (by omega)⟩
    · rw [hm6]
      refine (Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots
        (L := 4096) (fun p hp' => by have := slots_bound p hp'; omega) (by decide)).sub
        (fun r hr => ⟨_, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩) |>.trans ?_
      rw [← hm1]
      refine (f2.sub fun r hr => ⟨cR (cP s₀), by simp, ?_⟩).trans (hf4.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact sub_c (by decide)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, sub_c (by decide)⟩
    · rw [hm6]
      refine saved_keep (saved_keep hsv f2 ?_) hf4 ?_ <;> intro r hr d h3 h8
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact slot_dis_tab h3 h8
  · -- the epilogue
    obtain ⟨h4bx, h4sp, h4rd, h4wr, hf4, hs4, hW4⟩ := hq4
    have h5bx : s5.gpr .rbx = cP s₀ := by rw [k5.gpr (by decide), h4bx]
    have hmx : ∀ r ∈ [mxR (cP s₀)], Region.Sub r (cR (cP s₀)) := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)
    have hf : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s5.mem :=
      hf4.trans (hf5.sub fun r hr => ⟨cR (cP s₀), by simp, hmx r hr⟩)
    have hs5 : Spill.Saved s5.mem (s5.gpr .rbx) s₀.gpr KpkeMul.slots := by
      rw [h5bx]
      refine saved_keep hs4 hf5 fun r hr d h3 h8 => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    rw [restore_eq]
    refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots s₀.gpr s5 (by decide) (fun p hp' => ?_) hs5)
      fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by rw [k5.gpr (by decide), h4sp]), ?_⟩, ?_⟩
    · rw [h5bx, k5.2.1, k5.2.2, h4rd, h4wr]
      exact ⟨_, List.mem_append_right _ hcw, in_c (by have := slots_bound p hp'; omega)⟩
    · rw [hm']
      refine hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1]
    · show PolyIs s'.mem (wP s₀) _
      rw [hm']
      refine polyIs_frame hf5 (fun r hr => ?_) hW4
      simp only [List.mem_singleton] at hr; subst hr
      exact dis_wc hp (by decide)

end

end DecMulY

end VG.Proof.MlKem.X86_64
