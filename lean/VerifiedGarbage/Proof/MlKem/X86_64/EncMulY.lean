module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncMul
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
public import VerifiedGarbage.Proof.MlKem.X86_64.RowY
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: the products of K-PKE.Encrypt with AVX2, row by row

`encryptMulYg` (`Impl/MlKem/X86_64/KpkeMul.lean`), as `encryptMul16Y k`
inlines it in `vg_mlkem*_kpke_encrypt`, computes each
`ŷ[j] = NTT(y[j])` to the accumulator at `scratch + 1024 + 512 j` (as
`Kpke16.dmInnerY` does, `NInv`); then each `u[i]`, from column `i` of `Â`, and
`v`, from `t̂`, in one row of products to an accumulator at `u[i]` and
`NTT⁻¹` of it (`row_ok`, `RInv`). The prologue and epilogue are
`encryptMul`'s (`EncMul.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

namespace EncMulY

open DecMul (sub_c sub_c0 sub_v in_c in_c0 in_v cov_one sx1024 saved_keep slots_bound slot_dis_c0 slot_dis_tab)
open EncMul (uP aP tP yP cP yv tv colE colE_get colE_length Base hiR hi_dis_c0 hi_dis_tab sub_hi in_vec dUC dAC
  dTC dYC rU rC a_frame t_frame y_frame dUU dUhi mulMatTVec_getD mulMatTVec_length saveE_eq)

/-- `ŷ` of `y` as `k` polynomials of `u16`s. -/
abbrev yv16 (k : Nat) (s₀ : State) : List Poly := (vecAtW 16 s₀.mem (yP s₀) k).map ntt

/-- After `j` `NTT`s of `y` (`sy` bytes apart), to `Y`. -/
structure NInv (k : Nat) (s₀ : State) (Y : List Poly) (sy j : Nat) (s : State) : Prop extends Base k s₀ s where
  rbp : s.gpr .rbp = uP s₀
  r12 : s.gpr .r12 = aP s₀
  r13 : s.gpr .r13 = yP s₀ + BitVec.ofNat 64 (sy * j)
  r15 : s.gpr .r15 = tP s₀
  r9 : s.gpr .r9 = yA (cP s₀) j
  tab : TabY s.mem (cP s₀)
  acc : ∀ i < j, Acc16 s.mem (yA (cP s₀) i) Y[i]!

/-- After the first `i` rows, of the columns `aCol` of `Â` and `ŷ = Y`. -/
structure RInv (k : Nat) (s₀ : State) (Y : List Poly) (aCol : Nat → List Poly) (sa i : Nat) (s : State) : Prop
    extends Base k s₀ s where
  rbp : s.gpr .rbp = uP s₀ + BitVec.ofNat 64 (1024 * i)
  r12 : s.gpr .r12 = aP s₀ + BitVec.ofNat 64 (sa * i)
  r15 : s.gpr .r15 = tP s₀
  tab : TabY s.mem (cP s₀)
  acc : ∀ j < k, Acc16 s.mem (yA (cP s₀) j) Y[j]!
  done : ∀ i' < i, PolyIs s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i')) (nttInv (dot (aCol i') Y))

theorem hi_dis_yA {C : Addr} {j : Nat} (hj : j < 4) : (hiR C).Disjoint (sR (yA C j)) := by
  rw [yA_eq]; exact Offset.disjoint C (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

theorem cs_of {rs : List Reg} (h : ∀ r ∈ calleeSaved, r ∉ rs) {a b : State} (kk : Keep rs a b) :
    ∀ r ∈ calleeSaved, b.gpr r = a.gpr r := fun r hr => kk.gpr (h r hr)

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} (hp : (encMulKA k aR aRed aMat).pre s₀) (hk : k ≤ 4)
include hp hk

set_option linter.unusedSimpArgs false in
/-- `ŷ[j] = NTT(y[j])` to accumulator `j`. -/
theorem term_ok {j : Nat} (hj : j < k) {s : State} (hI : NInv k s₀ (yv k s₀) 1024 j s) :
    WP isa KpkeMul.nttTermY s fun s' => NInv k s₀ (yv k s₀) 1024 (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hj4 : j < 4 := by omega_arith
  have hsr : s.rd = [aR (aP s₀), vR (tP s₀) k, vR (yP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hY := y_frame hp hI.frame hj
  unfold KpkeMul.nttTermY KpkeMul.nttTermYg
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = yP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = yA (cP s₀) j ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hI.r13, hI.rbx, hI.r9]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.seq (WP.inline (k := nttAccK) nttAccY_correct (rd := [pR (yP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [sR (yA (cP s₀) j), pR (cP s₀)]) ?_ ?_ ?_ (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_))
  · simp only [nttAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, ((dYC hp).sub_left (sub_v _ hj)).sub_right (sub_c0 _), yA_dis_c0 _ _ hj4,
      by rw [yA_eq]; exact (rC hp).sub_right (sub_c (o := 1024 + 512 * j) (n := 512) (by omega_arith)),
      (rC hp).sub_right (sub_c0 _), hY.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons ((cov_one (by simp) (yA_in hj4)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (yA_in hj4)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttAccK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1] at hpost2
  rw [hm1] at hf2
  obtain ⟨hA2, hg2⟩ := hpost2
  have g2 : ∀ r, r ∉ [Reg.rax, .r8, .rdi, .rsi, .r10] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg2 r hr.1 hr.2.1, k1.gpr (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  have hhi : ∀ r ∈ [sR (yA (cP s₀) j), pR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hi_dis_yA hj4, hi_dis_c0 _]
  have hb2 : Base k s₀ s2 := hI.toBase.step hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (yA_sub hj4), .inr (sub_c0 _)]) hhi
    (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) (fun r hr => g2 r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  vrunm [g2 .r13 (by decide), g2 .r9 (by decide), g2 .r14 (by decide), hI.r13, hI.r9, sx1024, sx512]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb2.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb2.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb2.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb2.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb2.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb2.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .rbp (by decide), hI.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .r12 (by decide), hI.r12]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .r15 (by decide), hI.r15]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact yA_succ _ _
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
      exacts [yA_dis (by omega_arith) hj4 (by omega_arith), yA_dis_c0 _ _ (by omega_arith)]
    · obtain rfl : i = j := by omega_arith
      rw [vecAt_map_get _ _ hj, ← hY.2]
      exact hA2

end

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} {yR : Addr → Region} {yRed : Mem → Addr → Prop}
  {yVec : Mem → Addr → List Poly} (hp : (encMulKG k aR aRed aMat yR yRed yVec).pre s₀) (hk : k ≤ 4)
include hp hk

/-- A row: `u[i]` (at `rbp`) from the `k` polynomials of `fs` at `fB`, `o`
bytes apart (through `R`), and `ŷ = Y`. -/
theorem row_ok {o : Nat} (FR : FRep o) {R : Reg} (hRr : R ≠ .rdi) {fs Y : List Poly} {fB : Addr} {i : Nat}
    (hk1 : 1 ≤ k) (hi : i < k + 1) (hfl : fs.length = k) (hYl : Y.length = k)
    (hF : ∀ {m : Mem}, Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m → ∀ j < k,
      FR.Is m (fB + BitVec.ofNat 64 (o * j)) fs[j]!)
    (hdF : ∀ j < k, (vR (uP s₀) (k + 1)).Disjoint ⟨fB + BitVec.ofNat 64 (o * j), FR.sz⟩)
    (hinF : ∀ j < k, InRegions (s₀.rd ++ s₀.wr) (fB + BitVec.ofNat 64 (o * j)) FR.sz)
    (hrw : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowEg FR.ld FR.stv k) = true)
    {s : State} (hb : Base k s₀ s) (hbp : s.gpr .rbp = uP s₀ + BitVec.ofNat 64 (1024 * i)) (hR : s.gpr R = fB)
    (htab : TabY s.mem (cP s₀)) (hacc : ∀ j < k, Acc16 s.mem (yA (cP s₀) j) Y[j]!) :
    WP isa (KpkeMul.rowInvYg [.mov .rsi (.reg R)] (rowEg FR.ld FR.stv k)) s fun s' => Base k s₀ s' ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)] s.mem s'.mem ∧
      PolyIs s'.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (nttInv (dot fs Y)) := by
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hb.wr, hp.2.1]
  have hU : Region.Sub (pR (uP s₀ + BitVec.ofNat 64 (1024 * i))) (vR (uP s₀) (k + 1)) := sub_v _ hi
  unfold KpkeMul.rowInvYg
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * i) ∧
      s1.gpr .rsi = fB ∧ s1.gpr .rdx = cP s₀ + BitVec.ofNat 64 1024 ∧ s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx] s s1) (by
        vrunm [hbp, hR, hb.rbx, sx1024, hRr]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1dx, h1cx, hm1, k1⟩ => ?_)
  have hr1 : s1.rd ++ s1.wr = s₀.rd ++ s₀.wr := by rw [k1.2.1, k1.2.2, hb.rd, hb.wr]
  have dA : (sR (uP s₀ + BitVec.ofNat 64 (1024 * i))).Disjoint (cR (cP s₀)) :=
    ((dUC hp).sub_left hU).sub_left (sR_sub_pR _)
  have hx : RowEY.CtxG FR k fB (cP s₀ + BitVec.ofNat 64 1024) (uP s₀ + BitVec.ofNat 64 (1024 * i)) (cP s₀) fs
      Y s1.mem s1.rd s1.wr :=
    { k1 := hk1
      k4 := hk
      fl := by rw [hfl]
      gl := by rw [hYl]
      F := fun j hj => by rw [hm1]; exact hF hb.frame j hj
      G := fun j hj => by rw [hm1]; exact hacc j hj
      dF := fun j hj => ((hdF j hj).sub_left hU).sub_left (sR_sub_pR _)
      dG := fun j hj => by
        show (sR _).Disjoint (sR (yA (cP s₀) j))
        exact dA.sub_right (yA_sub (C := cP s₀) (j := j) (by omega_arith))
      dT := dA.sub_right (sub_c (by decide))
      inF := fun j hj => by rw [hr1]; exact hinF j hj
      inG := fun j hj => by rw [hr1, hp.2.1]; exact ⟨_, by simp, yA_in (C := cP s₀) (by omega_arith)⟩
      inTab := by rw [hr1, hp.2.1]; exact ⟨_, by simp, in_c (by decide)⟩
      inA := by
        rw [k1.2.2, hsw]
        refine ⟨vR (uP s₀) (k + 1), by simp, Offset.contains_base _ ?_ (by omega_arith)⟩
        have := Nat.mul_le_mul_left 1024 (show i + 1 ≤ k + 1 by omega_arith); rw [Nat.mul_succ] at this; omega_arith
      tab := by rw [hm1]; exact htab }
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (RowEY.rowEg_ok FR hx h1si h1dx h1di h1cx) hrw)
    fun s2 ⟨⟨hA2, hf2, hrd2, hwr2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  rw [hm1] at hf2
  -- `NTT⁻¹` of the sum
  refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * i) ∧
      s3.gpr .rsi = cP s₀ ∧ s3.mem = s2.mem ∧ Keep [.rdi, .rsi] s2 s3) (by
        vrunm [k12.gpr (by decide : Reg.rbp ∉ _), k12.gpr (by decide : Reg.rbx ∉ _), hb.rbx, hbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3di, h3si, hm3, k3⟩ => ?_)
  have k13 := k12.trans k3
  have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [k13.gpr (by decide), hb.rsp]
  have hsw3 : s3.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [k3.2.2, hwr2, k1.2.2, hsw]
  have hA3 : Acc16 s3.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (dotP fs Y k) := by rw [hm3]; exact hA2
  refine WP.inline (k := invAccK accY) nttInvAccY_correct (rd := [])
    (wr := [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_)
  · simp only [invAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, hsp3, retR]
    exact ⟨trivial, trivial, ((dUC hp).sub_left hU).sub_right (sub_c0 _), (rU hp).sub_right hU,
      (rC hp).sub_right (sub_c0 _), ⟨_, hA3⟩⟩
  · rw [hsw3]
    exact Covers.right ((cov_one (by simp) (in_vec _ (by omega_arith) hi)).cons ((cov_one (by simp) (in_c0 _)).cons
      Covers.nil))
  · rw [hsw3]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hi)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [invAccK, State.withRegions_gpr, State.withRegions_mem, h3di] at hpost4
  rw [hm3] at hf4
  have hf : Frame [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)] s.mem s4.mem :=
    (hf2.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sR_sub_pR _⟩).trans hf4
  have cs4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by
    rw [habi4.1 r hr, cs_of (by decide) k13 r hr]
  refine ⟨hb.step hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl hU, .inr (sub_c0 _)]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dUhi hp hi, hi_dis_c0 _])
    (by rw [hrd4, k3.2.1, hrd2, k1.2.1]) (by rw [hwr4, k3.2.2, hwr2, k1.2.2]) cs4, cs4, hf, ?_⟩
  rw [← dotP_full hfl hYl]
  exact hpost4 _ hA3

/-- Sum `i` of `encrypt_mul`: of column `i` of `Â` for `i < k`, of `t̂` for `k`, with `ŷ = Y`. -/
abbrev accF (Y : List Poly) (aCol : Nat → List Poly) (k : Nat) (s₀ : State) (i : Nat) : Poly :=
  if i < k then dot (aCol i) Y else dot (tv k s₀) Y

omit hp hk in
theorem mmtv_length (k : Nat) (M : List (List Poly)) (v : List Poly) :
    ((mulMatTVec k M v).map nttInv).length = k := by
  simp [mulMatTVec]

omit hp hk in
theorem mmtv_getD (M : List (List Poly)) (v : List Poly) {k i : Nat} (hi : i < k) :
    ((mulMatTVec k M v).map nttInv).getD i zero = nttInv (dot (M.map fun row => row.getD i zero) v) := by
  simp [mulMatTVec, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- The code inside the MXCSR region, with the `NTT`s of `y` computed by
`term` and the rows of `Â` by `rowA`. -/
abbrev innerYg (term rowA : Prog isa) (k : Nat) : Prog isa :=
  .seq (.block KpkeMul.startY) (.seq (.loop term .ne)
    (.seq (.block [.mov32 .r14 (.imm (BitVec.ofNat 32 k))]) (.seq (.loop rowA .ne)
      (KpkeMul.rowInvY [.mov .rsi (.reg .r15)] 1024 k))))

/-- `encryptMulYg term rowA k`, given that `term` computes the `NTT`s of `y`
(`sy` bytes apart) and `rowA` the rows of `Â` (its columns `aCol`, `sa`
bytes apart). -/
theorem wp_allg (hk3 : k = 3 ∨ k = 4) {term rowA : Prog isa} {sy : Nat} {aCol : Nat → List Poly} {sa : Nat}
    (hYl : (yVec s₀.mem (yP s₀)).length = k)
    (hterm : ∀ j < k, ∀ s, NInv k s₀ ((yVec s₀.mem (yP s₀)).map ntt) sy j s → WP isa term s fun s' =>
      NInv k s₀ ((yVec s₀.mem (yP s₀)).map ntt) sy (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
        s'.zf = some (s.gpr .r14 - 1 == 0))
    (hcol : ∀ i < k, aCol i = (aMat s₀.mem (aP s₀)).map fun row => row.getD i zero)
    (hrowA : ∀ i < k, ∀ s, RInv k s₀ ((yVec s₀.mem (yP s₀)).map ntt) aCol sa i s → WP isa rowA s fun s' =>
      RInv k s₀ ((yVec s₀.mem (yP s₀)).map ntt) aCol sa (i + 1) s' ∧
      s'.gpr .r14 = s.gpr .r14 - 1 ∧ s'.zf = some (s.gpr .r14 - 1 == 0))
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (innerYg term rowA k) = true) :
    WP isa (encryptMulYg term rowA k) s₀ fun s' => gprPreserved s₀ s' ∧
      (encMulKG k aR aRed aMat yR yRed yVec).post s₀ s' := by
  have hk0 : 0 < k := by omega_arith
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  unfold encryptMulYg
  refine WP.seq ?_
  rw [saveE_eq]
  refine Spill.save_then .r8 KpkeMul.slots (fun p hp' => ⟨_, hcw, in_c (by
    have := DecMul.slots_bound p hp'; omega_arith)⟩) ?_
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rbx = cP s₀ ∧ s1.gpr .rbp = uP s₀ ∧ s1.gpr .r12 = aP s₀ ∧
      s1.gpr .r13 = yP s₀ ∧ s1.gpr .r15 = tP s₀ ∧ s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.gpr .rsp = s₀.gpr .rsp ∧
      s1.rd = s₀.rd ∧ s1.wr = s₀.wr ∧ s1.mem = Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (by
        vrunm
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega_arith) fun s1 ⟨h1bx, h1bp, h112, h113, h115, h114, h1sp, h1rd, h1wr, hm1⟩ => ?_
  have h0 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 768) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 772) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  -- the memory after the prologue
  have hsv : Spill.Saved s1.mem (cP s₀) s₀.gpr KpkeMul.slots := by
    rw [hm1]; exact Spill.saveMem_saved _ _ _ _ (by decide)
  have hf1 : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem s1.mem := by
    rw [hm1]
    exact (Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots (L := 4096)
      (fun p hp' => by have := DecMul.slots_bound p hp'; omega_arith) (by decide)).sub
      (fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  have hmx : ∀ r ∈ [mxR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (withMxcsr_ok' (r := .rbx) (by decide) _ (by decide) h1bx h0 h4 hwo
    (Q := fun s' => Base k s₀ s' ∧ ∀ i < k + 1, PolyIs s'.mem (uP s₀ + BitVec.ofNat 64 (1024 * i))
      (nttInv (accF ((yVec s₀.mem (yP s₀)).map ntt) aCol k s₀ i)))
    (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, ⟨hb4, hacc4⟩, hf5, k5⟩ => ?_)
  · -- the table, the `NTT`s, the rows
    have hb2 : Base k s₀ s2 := ⟨by rw [k2.gpr (by decide), h1bx], by rw [k2.gpr (by decide), h1sp],
      by rw [k2.2.1, h1rd], by rw [k2.2.2, h1wr],
      hf1.trans (f2.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩),
      hsv.frame f2 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega_arith))⟩
    have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := fun r hr =>
      k2.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    refine WP.seq ?_
    unfold KpkeMul.startY
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .rcx = cP s₀ ∧ s3.mem = s2.mem ∧ Keep [.rcx] s2 s3) (by
        vrunm [hb2.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3cx, hm3, k3⟩ => ?_
    rw [WP.block_append_iff]
    have hin : InRegions s3.wr (s3.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
      rw [k3.2.2, hb2.wr, h3cx]; exact ⟨cR (cP s₀), hcw, in_c (by decide)⟩
    refine WP.mono (tabAccY_wp s3 hin) fun s4 ⟨hT4, hf4, k4⟩ => ?_
    rw [h3cx] at hT4 hf4
    have k24 := (k3.trans k4)
    refine WP.mono (Q := fun (s6 : State) => s6.gpr .r9 = yA (cP s₀) 0 ∧ s6.mem = s4.mem ∧ Keep [.r9] s4 s6) (by
        vrunm [k24.gpr (by decide : Reg.rbx ∉ _), hb2.rbx, sx1024]
        refine ⟨yA_zero _, fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s6 ⟨h6r9, hm6, k6⟩ => ?_
    have k26 := k24.trans k6
    have e6 : ∀ r ∈ calleeSaved, s6.gpr r = s2.gpr r := fun r hr =>
      k26.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    rw [hm3] at hf4
    have hb6 : Base k s₀ s6 := hb2.step (rs := [tabR (cP s₀)]) (by rw [hm6]; exact hf4)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (sub_c (by decide)))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hi_dis_tab _)
      (by rw [k26.2.1]) (by rw [k26.2.2]) e6
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega_arith) hk0 (NInv k s₀ ((yVec s₀.mem (yP s₀)).map ntt) sy)
      (fun j hj u hI _ => hterm j hj u hI) (fun u hI => ?_)
      ⟨hb6, by rw [e6 .rbp (by decide), g2 .rbp (by decide), h1bp], by rw [e6 .r12 (by decide), g2 .r12 (by decide), h112],
        by rw [e6 .r13 (by decide), g2 .r13 (by decide), h113, Nat.mul_zero, add_ofNat_zero],
        by rw [e6 .r15 (by decide), g2 .r15 (by decide), h115], h6r9, by rw [hm6]; exact hT4,
        fun i hi => absurd hi (by omega_arith)⟩
      (by rw [e6 .r14 (by decide), g2 .r14 (by decide), h114]))
    refine WP.seq (WP.mono (Q := fun (s7 : State) => s7.gpr .r14 = BitVec.ofNat 64 k ∧ s7.mem = u.mem ∧
        Keep [.r14] u s7) (by
          vrunm
          refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
          · apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_arith
          · simp only [List.mem_singleton] at hr
            simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s7 ⟨h714, hm7, k7⟩ => ?_)
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega_arith) hk0 (RInv k s₀ ((yVec s₀.mem (yP s₀)).map ntt) aCol sa)
      (fun i hi v hR _ => hrowA i hi v hR) (fun v hR => ?_)
      ⟨⟨by rw [k7.gpr (by decide)]; exact hI.rbx, by rw [k7.gpr (by decide)]; exact hI.rsp,
        by rw [k7.2.1]; exact hI.rd, by rw [k7.2.2]; exact hI.wr, by rw [hm7]; exact hI.frame,
        by rw [hm7]; exact hI.saved⟩, by rw [k7.gpr (by decide), hI.rbp, Nat.mul_zero, add_ofNat_zero],
        by rw [k7.gpr (by decide), hI.r12, Nat.mul_zero, add_ofNat_zero], by rw [k7.gpr (by decide)]; exact hI.r15,
        by rw [hm7]; exact hI.tab, fun j hj => by rw [hm7]; exact hI.acc j hj, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      h714)
    -- `v`, from `t̂`
    refine WP.mono (row_ok hp hk (FRep.u32 1024) (R := .r15) (by decide) (fs := tv k s₀) (fB := tP s₀) (i := k)
      (by omega_arith) (by omega_arith) (vecAt_length _ _ _) (by rw [List.length_map, hYl]) (fun hf j hj => by rw [vecAt_get _ _ hj]; exact t_frame hp hf hj)
      (fun j hj => hp.2.2.2.1.sub_right (sub_v _ hj)) (fun j hj => by rw [hp.1]; exact ⟨_, by simp, in_vec _ (by omega_arith) hj⟩)
      (rowEY_wo hk3 (.inl rfl)) hR.toBase hR.rbp hR.r15 hR.tab hR.acc) fun s' ⟨hb', _, hf', hP'⟩ => ⟨hb', fun i hi => ?_⟩
    by_cases h : i < k
    · simp only [accF, h, ↓reduceIte]
      refine polyIs_frame hf' (fun r hr => ?_) (hR.done i h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dUU hk (by omega_arith) (by omega_arith) (by omega_arith), ((dUC hp).sub_left (sub_v _ hi)).sub_right (sub_c0 _)]
    · obtain rfl : i = k := by omega_arith
      simp only [accF, Nat.lt_irrefl, ↓reduceIte]; exact hP'
  · -- the epilogue
    have h5bx : s5.gpr .rbx = cP s₀ := by rw [k5.gpr (by decide), hb4.rbx]
    have hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem s5.mem :=
      hb4.frame.trans (hf5.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩)
    have hs5 : Spill.Saved s5.mem (s5.gpr .rbx) s₀.gpr KpkeMul.slots := by
      rw [h5bx]
      exact hb4.saved.frame hf5 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega_arith))
    rw [DecMul.restore_eq]
    refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots s₀.gpr s5 (by decide) (fun p hp' => ?_) hs5)
      fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by rw [k5.gpr (by decide), hb4.rsp]), ?_⟩, ?_⟩
    · rw [h5bx, k5.2.1, k5.2.2, hb4.rd, hb4.wr]
      exact ⟨_, List.mem_append_right _ hcw, in_c (by have := DecMul.slots_bound p hp'; omega_arith)⟩
    · rw [hm']
      refine hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [rU hp, rC hp]
    · refine ⟨by rw [List.length_append, mmtv_length]; rfl, fun i hi => ?_⟩
      rw [hm']
      have := polyIs_frame hf5 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((dUC hp).sub_left (sub_v _ hi)).sub_right (sub_c (by decide))) (hacc4 i hi)
      by_cases h : i < k
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [mmtv_length]; exact h),
          ← List.getD_eq_getElem?_getD, mmtv_getD _ _ h, ← hcol i h]
        simpa only [accF, h, ite_true] using this
      · have hik : i = k := by omega_arith
        subst hik
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [mmtv_length]),
          mmtv_length, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        simpa only [accF, Nat.lt_irrefl, ite_false] using this

end

section
variable {k : Nat} {s₀ : State} (hp : (encMulK16 k).pre s₀) (hk : k ≤ 4)
include hp

/-- Column `i` of the matrix of `u16`s at `p`. -/
abbrev colW (m : Mem) (p : Addr) (k i : Nat) : List Poly := (matAtW 16 m p k).map fun row => row.getD i zero

omit hp in
theorem colW_length (m : Mem) (p : Addr) (k i : Nat) : (colW m p k i).length = k := by
  simp [colW, matAtW]

omit hp in
theorem colW_get (m : Mem) (p : Addr) {k i j : Nat} (hi : i < k) (hj : j < k) :
    (colW m p k i)[j]! = polyAtW 16 m (p + BitVec.ofNat 64 (512 * (k * j + i))) := by
  rw [getElem!_pos _ j (by rw [colW_length]; exact hj)]
  simp only [colW, matAtW, List.getElem_map, List.getElem_range, vecAtW, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun x => polyAtW 16 m (p + BitVec.ofNat 64 x)) (by omega_arith)

omit hp in
theorem a16_addr (p : Addr) (k i j : Nat) :
    p + BitVec.ofNat 64 (512 * i) + BitVec.ofNat 64 (512 * k * j) = p + BitVec.ofNat 64 (512 * (k * j + i)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + BitVec.ofNat 64 ·) (by rw [Nat.mul_assoc]; omega_arith)

theorem a16_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k * k) :
    PolyIsW 16 m (aP s₀ + BitVec.ofNat 64 (512 * e)) (polyAtW 16 s₀.mem (aP s₀ + BitVec.ofNat 64 (512 * e))) := by
  have hs : Region.Sub ⟨aP s₀ + BitVec.ofNat 64 (512 * e), 512⟩ ⟨aP s₀, 512 * (k * k)⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame hf (fun r hr' => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (hp.2.2.1.sub_right hs).symm
    · exact (dAC hp).sub_left hs
  · have := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
    rwa [show 32 * 16 * e = 512 * e by omega_arith] at this

theorem y16_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k) :
    PolyIsW 16 m (yP s₀ + BitVec.ofNat 64 (512 * e)) (polyAtW 16 s₀.mem (yP s₀ + BitVec.ofNat 64 (512 * e))) := by
  have hs : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 (512 * e), 512⟩ ⟨yP s₀, 512 * k⟩ := Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame hf (fun r hr' => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (hp.2.2.2.2.1.sub_right hs).symm
    · exact (dYC hp).sub_left hs
  · have := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 e he
    rwa [show 32 * 16 * e = 512 * e by omega_arith] at this

omit hp in
theorem vecAtW16_map_get (m : Mem) (p : Addr) {k j : Nat} (hj : j < k) :
    ((vecAtW 16 m p k).map ntt)[j]! = ntt (polyAtW 16 m (p + BitVec.ofNat 64 (512 * j))) := by
  rw [getElem!_pos _ j (by rw [List.length_map, vecAtW_length]; exact hj), List.getElem_map,
    ← getElem!_pos _ j (by rw [vecAtW_length]; exact hj), vecAtW16_get _ _ hj]

include hk

set_option linter.unusedSimpArgs false in
/-- `ŷ[j] = NTT(y[j])` to accumulator `j`, `y` of `u16`s. -/
theorem term16_ok {j : Nat} (hj : j < k) {s : State} (hI : NInv k s₀ (yv16 k s₀) 512 j s) :
    WP isa KpkeMul.nttTermY16 s fun s' => NInv k s₀ (yv16 k s₀) 512 (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hj4 : j < 4 := by omega_arith
  have hsr : s.rd = [⟨aP s₀, 512 * (k * k)⟩, vR (tP s₀) k, ⟨yP s₀, 512 * k⟩] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hY := y16_frame hp hI.frame hj
  have hsub : Region.Sub (sR (yP s₀ + BitVec.ofNat 64 (512 * j))) ⟨yP s₀, 512 * k⟩ := Offset.sub_base _ (by omega_arith)
  unfold KpkeMul.nttTermY16 KpkeMul.nttTermYg
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = yP s₀ + BitVec.ofNat 64 (512 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = yA (cP s₀) j ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hI.r13, hI.rbx, hI.r9]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.seq (WP.inline (k := nttAcc16K) nttAccY16_correct (rd := [sR (yP s₀ + BitVec.ofNat 64 (512 * j))])
    (wr := [sR (yA (cP s₀) j), pR (cP s₀)]) ?_ ?_ ?_ (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_))
  · simp only [nttAcc16K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, ((dYC hp).sub_left hsub).sub_right (sub_c0 _), yA_dis_c0 _ _ hj4,
      by rw [yA_eq]; exact (rC hp).sub_right (sub_c (o := 1024 + 512 * j) (n := 512) (by omega_arith)),
      (rC hp).sub_right (sub_c0 _), hY.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (show Region.Contains ⟨yP s₀, 512 * k⟩ (yP s₀ + BitVec.ofNat 64 (512 * j)) 512 from
      Offset.contains_base _ (by omega_arith) (by omega_arith))).cons ((cov_one (by simp) (yA_in hj4)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (yA_in hj4)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttAcc16K, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1] at hpost2
  rw [hm1] at hf2
  obtain ⟨hA2, hg2⟩ := hpost2
  have g2 : ∀ r, r ∉ [Reg.rax, .r8, .rdi, .rsi, .r10] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg2 r hr.1 hr.2.1, k1.gpr (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  have hhi : ∀ r ∈ [sR (yA (cP s₀) j), pR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hi_dis_yA hj4, hi_dis_c0 _]
  have hb2 : Base k s₀ s2 := hI.toBase.step hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (yA_sub hj4), .inr (sub_c0 _)]) hhi
    (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) (fun r hr => g2 r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  vrunm [g2 .r13 (by decide), g2 .r9 (by decide), g2 .r14 (by decide), hI.r13, hI.r9, sx512]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb2.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb2.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb2.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb2.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb2.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb2.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .rbp (by decide), hI.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .r12 (by decide), hI.r12]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g2 .r15 (by decide), hI.r15]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact yA_succ _ _
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
      exacts [yA_dis (by omega_arith) hj4 (by omega_arith), yA_dis_c0 _ _ (by omega_arith)]
    · obtain rfl : i = j := by omega_arith
      rw [vecAtW16_map_get _ _ hj, ← hY.2]
      exact hA2

set_option linter.unusedSimpArgs false in
/-- Row `i < k`: `u[i]` from column `i` of `Â` of `u16`s. -/
theorem rowA16_ok (hk3 : k = 3 ∨ k = 4) {i : Nat} (hi : i < k) {s : State}
    (hR : RInv k s₀ (yv16 k s₀) (colW s₀.mem (aP s₀) k) 512 i s) :
    WP isa (KpkeMul.rowAY16 k) s fun s' => RInv k s₀ (yv16 k s₀) (colW s₀.mem (aP s₀) k) 512 (i + 1) s' ∧
      s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hkk : k * k ≤ 64 := Nat.le_trans (Nat.mul_le_mul hk hk) (by decide)
  have hrow : ∀ j < k, k * j + i < k * k := fun j hj => by
    have := Nat.mul_le_mul_left k (show j + 1 ≤ k by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  unfold KpkeMul.rowAY16 KpkeMul.rowAYg
  have hb : ∀ j < k, 512 * (k * j + i) + 512 ≤ 512 * (k * k) := fun j hj => by have := hrow j hj; omega_arith
  refine WP.seq (WP.mono (row_ok hp hk (FRep.u16 (512 * k)) (R := .r12) (by decide)
    (fs := colW s₀.mem (aP s₀) k i) (fB := aP s₀ + BitVec.ofNat 64 (512 * i)) (i := i) (by omega_arith) (by omega_arith)
    (colW_length _ _ _ _) (by rw [List.length_map, vecAtW_length])
    (fun hf j hj => by rw [colW_get _ _ hi hj, a16_addr]; exact a16_frame hp hf (hrow j hj))
    (fun j hj => by rw [a16_addr]; exact hp.2.2.1.sub_right (Offset.sub_base _ (hb j hj)))
    (fun j hj => by
      rw [a16_addr, hp.1]; exact ⟨_, by simp, Offset.contains_base _ (hb j hj) (by have := hb j hj; omega_arith)⟩)
    (rowEY16_wo hk3) hR.toBase hR.rbp hR.r12 hR.tab hR.acc) fun s1 ⟨hb1, cs1, hf1, hP1⟩ => ?_)
  have fo : ∀ {p : Addr}, (∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)], (sR p).Disjoint r) →
      ∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)], (sR p).Disjoint r := fun h => h
  vrunm [cs1 .rbp (by decide), cs1 .r12 (by decide), cs1 .r14 (by decide), cs1 .r15 (by decide), hR.rbp, hR.r12,
    sx1024, sx512]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun j hj => ?_, fun i' hi' => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb1.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb1.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb1.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb1.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb1.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb1.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [cs1 .r15 (by decide)]; exact hR.r15
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine tabY.frame hf1 (fun r hr => ?_) hR.tab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(((dUC hp).sub_left (sub_v _ (by omega_arith))).sub_right (sub_c (by decide))).symm,
      (DecMul.prod_dis (cP s₀)).2.2.2.1.symm]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine acc16_frame hf1 (fun r hr => ?_) (hR.acc j hj)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(((dUC hp).sub_left (sub_v _ (by omega_arith))).sub_right (yA_sub (C := cP s₀) (j := j) (by omega_arith))).symm,
      yA_dis_c0 _ _ (by omega_arith)]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i' = i
    · subst h; exact hP1
    · refine polyIs_frame hf1 (fun r hr => ?_) (hR.done i' (by omega_arith))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dUU hk (by omega_arith) (by omega_arith) h, ((dUC hp).sub_left (sub_v _ (by omega_arith))).sub_right (sub_c0 _)]

/-- The code inside the MXCSR region, with `Â` of `u16`s. -/
abbrev innerY16 (k : Nat) : Prog isa := innerYg KpkeMul.nttTermY16 (KpkeMul.rowAY16 k) k

theorem wp_all16 (hk3 : k = 3 ∨ k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp] (innerY16 k) = true) :
    WP isa (encryptMul16Y k) s₀ fun s' => gprPreserved s₀ s' ∧ (encMulK16 k).post s₀ s' :=
  wp_allg hp hk hk3 (aCol := colW s₀.mem (aP s₀) k) (sa := 512) (vecAtW_length _ _ _ _)
    (fun _ hj _ hI => term16_ok hp hk hj hI) (fun _ _ => rfl) (fun _ hi _ hR => rowA16_ok hp hk hk3 hi hR) hwo

end

end EncMulY

end VG.Proof.MlKem.X86_64
