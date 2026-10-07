import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV

/-!
# ML-KEM on x86-64: `vg_mlkem*_encrypt_mul`

`encryptMul B k` (`Impl/MlKem/X86_64/KpkeMul.lean`), as `decryptMul`
(`DecMul.lean`) with a sum per output: the prologue saves the callee-saved
registers in `scratch` and keeps the pointers in registers; `zeroU` zeroes
the `k + 1` sums (`zeroU_ok`); after `j` iterations of the outer loop, sum
`i < k` holds the first `j` terms of `Â^⊺ ∘ ŷ`'s entry `i` (its column `i`
of `Â`, `colE`), and sum `k` those of `t̂^⊺ ∘ ŷ` (`EInv`); an iteration
computes `ŷ[j] = NTT(y[j])`, adds `Â[j, i] ×_T ŷ[j]` to each sum `i < k`
(`IInv`, `innerE_ok`, unrolled), then `t̂[j] ×_T ŷ[j]` to sum `k`
(`termE_ok`); the last loop computes `NTT⁻¹` of each sum (`invStep_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open DecMul (sub_c sub_c0 sub_v in_c in_c0 in_v dis_cc cov_one sx1024 sx2048)

/-- `vg_mlkem*_encrypt_mul(u = rdi, a = rsi, t = rdx, y = rcx, scratch = r8)` of rank `k`. -/
def encMulK (k : Nat) : Contract isa where
  pre s :=
    s.rd = [vR (s.gpr .rsi) (k * k), vR (s.gpr .rdx) k, vR (s.gpr .rcx) k] ∧
    s.wr = [vR (s.gpr .rdi) (k + 1), cR (s.gpr .r8)] ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (vR (s.gpr .rsi) (k * k)) ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (vR (s.gpr .rdx) k) ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (vR (s.gpr .rcx) k) ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (cR (s.gpr .r8)) ∧
    (vR (s.gpr .rsi) (k * k)).Disjoint (cR (s.gpr .r8)) ∧ (vR (s.gpr .rdx) k).Disjoint (cR (s.gpr .r8)) ∧
    (vR (s.gpr .rcx) k).Disjoint (cR (s.gpr .r8)) ∧
    (retR s).Disjoint (vR (s.gpr .rdi) (k + 1)) ∧ (retR s).Disjoint (vR (s.gpr .rsi) (k * k)) ∧
    (retR s).Disjoint (vR (s.gpr .rdx) k) ∧ (retR s).Disjoint (vR (s.gpr .rcx) k) ∧
    (retR s).Disjoint (cR (s.gpr .r8)) ∧
    VecReduced s.mem (s.gpr .rsi) (k * k) ∧ VecReduced s.mem (s.gpr .rdx) k ∧ VecReduced s.mem (s.gpr .rcx) k
  post s s' :=
    VecIs s'.mem (s.gpr .rdi) (k + 1)
      (((mulMatTVec k (matAt s.mem (s.gpr .rsi) k) ((vecAt s.mem (s.gpr .rcx) k).map ntt)).map nttInv) ++
        [nttInv (dot (vecAt s.mem (s.gpr .rdx) k) ((vecAt s.mem (s.gpr .rcx) k).map ntt))])
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace EncMul

/-! ## Columns of the matrix -/

/-- Column `i` of the matrix at `p`: `Â[j, i]` for each row `j`. -/
abbrev colE (m : Mem) (p : Addr) (k i : Nat) : List Poly := (matAt m p k).map fun row => row.getD i zero

theorem colE_length (m : Mem) (p : Addr) (k i : Nat) : (colE m p k i).length = k := by
  simp [colE, matAt]

theorem colE_get (m : Mem) (p : Addr) {k i j : Nat} (hi : i < k) (hj : j < k) :
    (colE m p k i)[j]! = polyAt m (p + BitVec.ofNat 64 (1024 * (k * j + i))) := by
  rw [getElem!_pos _ j (by rw [colE_length]; exact hj)]
  simp only [colE, matAt, List.getElem_map, List.getElem_range, vecAt, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem mulMatTVec_getD (m : Mem) (p : Addr) (k : Nat) (v : List Poly) {i : Nat} (hi : i < k) :
    ((mulMatTVec k (matAt m p k) v).map nttInv).getD i zero = nttInv (dot (colE m p k i) v) := by
  simp [mulMatTVec, colE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem mulMatTVec_length (m : Mem) (p : Addr) (k : Nat) (v : List Poly) :
    ((mulMatTVec k (matAt m p k) v).map nttInv).length = k := by
  simp [mulMatTVec]

/-! ## Regions -/

/-- The top quarter of `scratch`, where the registers are kept. -/
abbrev hiR (C : Addr) : Region := ⟨C + BitVec.ofNat 64 3072, 1024⟩

theorem hi_dis_c {C : Addr} {o : Nat} (ho : o ≤ 2048) : (hiR C).Disjoint (pR (C + BitVec.ofNat 64 o)) :=
  Offset.disjoint C (.inr (by omega)) (by omega) (by omega)

theorem hi_dis_c0 (C : Addr) : (hiR C).Disjoint (pR C) := Offset.disjoint_base C (by omega) (by omega)

theorem sub_hi {C : Addr} {d n : Nat} (h3 : 3072 ≤ d) (h8 : d + n ≤ 4096) :
    Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ (hiR C) :=
  Offset.sub C h3 (by omega)

/-! ## A product added to a sum -/

section
variable {B : Bodies} (hB : BodiesOk B)
include hB

set_option linter.unusedSimpArgs false in
/-- `prodAdd B f o`: the product of the polynomial `f` points `rsi` at with
the one at `scratch + 1024`, to `scratch + 2048`, added to polynomial `o` at
`rbp`. -/
theorem prodAdd_ok {f : List Instr} {o : Nat} (ho : 1024 * o < 2 ^ 31) {s : State} {C F U : Addr}
    (hbx : s.gpr .rbx = C) (hbp : s.gpr .rbp = U) {P : Addr} (hP : U + BitVec.ofNat 64 (1024 * o) = P)
    (hset : WP isa (.block (([.mov .rdi (.reg .rbx), .alu .add .rdi (.imm 2048)] : List Instr) ++ f ++
      ([.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)] : List Instr))) s fun s1 =>
      s1.gpr .rdi = C + BitVec.ofNat 64 2048 ∧ s1.gpr .rsi = F ∧ s1.gpr .rdx = C + BitVec.ofNat 64 1024 ∧
        s1.gpr .rcx = C ∧ s1.mem = s.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s1)
    (hcov : Covers [pR F, pR (C + BitVec.ofNat 64 1024), pR (C + BitVec.ofNat 64 2048), pR C, pR P]
      (s.rd ++ s.wr))
    (hw : Covers [pR (C + BitVec.ofNat 64 2048), pR C, pR P] s.wr)
    (hFC : (pR F).Disjoint (cR C)) (hPC : (pR P).Disjoint (cR C)) (hrF : (retR s).Disjoint (pR F))
    (hrP : (retR s).Disjoint (pR P)) (hrC : (retR s).Disjoint (cR C))
    (rX : Reduced s.mem P) (rG : Reduced s.mem F) (rY : Reduced s.mem (C + BitVec.ofNat 64 1024)) :
    WP isa (KpkeMul.prodAdd B f o) s fun s' =>
      PolyIs s'.mem P (add (polyAt s.mem P) (multiplyNTTs (polyAt s.mem F) (polyAt s.mem (C + BitVec.ofNat 64 1024)))) ∧
      Frame [pR (C + BitVec.ofNat 64 2048), pR C, pR P] s.mem s'.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hcov' : ∀ R ∈ [pR F, pR (C + BitVec.ofNat 64 1024), pR (C + BitVec.ofNat 64 2048), pR C, pR P],
      Covers [R] (s.rd ++ s.wr) := fun R hR a n h => hcov a n (let ⟨r, hr, hc⟩ := h; ⟨r, by
        simp only [List.mem_singleton] at hr; subst hr; exact hR, hc⟩)
  have hw' : ∀ R ∈ [pR (C + BitVec.ofNat 64 2048), pR C, pR P], Covers [R] s.wr := fun R hR a n h =>
    hw a n (let ⟨r, hr, hc⟩ := h; ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact hR, hc⟩)
  unfold KpkeMul.prodAdd
  refine WP.seq (WP.mono hset fun s3 ⟨h3di, h3si, h3dx, h3cx, hm3, k3⟩ => ?_)
  have hsp3 : s3.gpr .rsp = s.gpr .rsp := cs (by decide) k3 .rsp (by decide)
  refine WP.seq (WP.inline (k := mulK) hB.mul (rd := [pR F, pR (C + BitVec.ofNat 64 1024)])
    (wr := [pR (C + BitVec.ofNat 64 2048), pR C]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) hB.nc.2.2.1)
  · simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, h3dx, h3cx, hsp3, hm3, retR]
    exact ⟨trivial, trivial, (hFC.sub_right (sub_c (by decide))).symm,
      Offset.disjoint _ (.inr (by decide)) (by decide) (by decide), Offset.disjoint_base _ (by decide) (by decide),
      hFC.sub_right (sub_c0 _), Offset.disjoint_base _ (by decide) (by decide), hrC.sub_right (sub_c (by decide)),
      hrF, hrC.sub_right (sub_c (by decide)), hrC.sub_right (sub_c0 _), rG, rY⟩
  · rw [k3.2.1, k3.2.2]
    exact (hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons
      Covers.nil)))
  · rw [k3.2.2]
    exact (hw' _ (by simp)).cons ((hw' _ (by simp)).cons Covers.nil)
  simp only [mulK, State.withRegions_gpr, State.withRegions_mem, h3di, h3si, h3dx, hm3] at hpost4
  rw [hm3] at hf4
  have g4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [habi4.1 r hr, cs (by decide) k3 r hr]
  refine WP.seq (WP.mono (Q := fun (s5 : State) => s5.gpr .rdi = P ∧ s5.gpr .rsi = C + BitVec.ofNat 64 2048 ∧
      s5.mem = s4.mem ∧ Keep [.rdi, .rsi] s4 s5) (by
        vrunm [g4 .rbx (by decide), g4 .rbp (by decide), hbx, hbp, sx2048, sx_ofNat ho, hP]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s5 ⟨h5di, h5si, hm5, k5⟩ => ?_)
  have hsp5 : s5.gpr .rsp = s.gpr .rsp := by rw [cs (by decide) k5 .rsp (by decide), g4 .rsp (by decide)]
  have hX5 : PolyIs s5.mem P (polyAt s.mem P) := by
    rw [hm5]
    refine polyIs_frame hf4 (fun r hr => ?_) ⟨rX, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hPC.sub_right (sub_c (by decide)), hPC.sub_right (sub_c0 _)]
  rw [← hm5] at hpost4
  refine WP.inline (k := accK Spec.MlKem.add) hB.add (rd := [pR (C + BitVec.ofNat 64 2048)]) (wr := [pR P]) ?_ ?_ ?_
    (fun s6 hrd6 hwr6 habi6 hf6 _ hpost6 => ?_) hB.nc.2.2.2
  · simp only [accK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h5di, h5si, hsp5, retR]
    exact ⟨trivial, trivial, hPC.sub_right (sub_c (by decide)), hrP, hrC.sub_right (sub_c (by decide)), hX5.1,
      hpost4.1⟩
  · rw [k5.2.1, k5.2.2, hrd4, hwr4, k3.2.1, k3.2.2]
    exact (hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons Covers.nil)
  · rw [k5.2.2, hwr4, k3.2.2]
    exact (hw' _ (by simp)).cons Covers.nil
  simp only [accK, State.withRegions_gpr, State.withRegions_mem, h5di, h5si] at hpost6
  rw [hX5.2, hpost4.2] at hpost6
  rw [hm5] at hf6
  refine ⟨hpost6, (hf4.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans
    (hf6.sub fun r hr => ⟨r, ?_, fun _ h => h⟩), fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    subst hr; simp
  · rw [habi6.1 r hr, cs (by decide) k5 r hr, g4 r hr]
  · rw [hrd6, k5.2.1, hrd4, k3.2.1]
  · rw [hwr6, k5.2.2, hwr4, k3.2.2]

end

/-! ## The loops -/

section
variable (k : Nat) (s₀ : State)

abbrev uP : Addr := s₀.gpr .rdi
abbrev aP : Addr := s₀.gpr .rsi
abbrev tP : Addr := s₀.gpr .rdx
abbrev yP : Addr := s₀.gpr .rcx
abbrev cP : Addr := s₀.gpr .r8
abbrev yv : List Poly := (vecAt s₀.mem (yP s₀) k).map ntt
abbrev tv : List Poly := vecAt s₀.mem (tP s₀) k

/-- The first `j` terms of sum `i`. -/
def accE (j i : Nat) : Poly :=
  if i < k then dotP (colE s₀.mem (aP s₀) k i) (yv k s₀) j else dotP (tv k s₀) (yv k s₀) j

/-- What the loops keep. -/
structure Base (s : State) : Prop where
  rbx : s.gpr .rbx = cP s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem s.mem
  saved : Spill.Saved s.mem (cP s₀) s₀.gpr KpkeMul.slots

/-- After `j` iterations of the outer loop. -/
structure EInv (j : Nat) (s : State) : Prop extends Base k s₀ s where
  rbp : s.gpr .rbp = uP s₀
  r12 : s.gpr .r12 = aP s₀ + BitVec.ofNat 64 (1024 * (k * j))
  r13 : s.gpr .r13 = yP s₀ + BitVec.ofNat 64 (1024 * j)
  r15 : s.gpr .r15 = tP s₀ + BitVec.ofNat 64 (1024 * j)
  acc : ∀ i < k + 1, PolyIs s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (accE k s₀ j i)

/-- After the terms `j` of the first `i` sums. -/
structure IInv (j i : Nat) (c14 : BitVec 64) (s : State) : Prop extends Base k s₀ s where
  r14 : s.gpr .r14 = c14
  rbp : s.gpr .rbp = uP s₀
  r12 : s.gpr .r12 = aP s₀ + BitVec.ofNat 64 (1024 * (k * j))
  r13 : s.gpr .r13 = yP s₀ + BitVec.ofNat 64 (1024 * j)
  r15 : s.gpr .r15 = tP s₀ + BitVec.ofNat 64 (1024 * j)
  yh : PolyIs s.mem (cP s₀ + BitVec.ofNat 64 1024) ((yv k s₀)[j]!)
  acc : ∀ i' < k + 1, PolyIs s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i'))
    (if i' < i then accE k s₀ (j + 1) i' else accE k s₀ j i')

end

/-- After `NTT⁻¹` of the first `i` sums. -/
structure VInv (k : Nat) (s₀ : State) (i : Nat) (s : State) : Prop extends Base k s₀ s where
  rbp : s.gpr .rbp = uP s₀ + BitVec.ofNat 64 (1024 * i)
  acc : ∀ i' < k + 1, PolyIs s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i'))
    (if i' < i then nttInv (accE k s₀ k i') else accE k s₀ k i')

theorem accE_succ {k : Nat} {s₀ : State} {j i : Nat} (hj : j < k) (hi : i < k) :
    accE k s₀ (j + 1) i = add (accE k s₀ j i)
      (multiplyNTTs (polyAt s₀.mem (aP s₀ + BitVec.ofNat 64 (1024 * (k * j + i)))) ((yv k s₀)[j]!)) := by
  simp only [accE, ifp hi]
  rw [dotP_succ (by rw [colE_length]; exact hj) (by rw [List.length_map, vecAt_length]; exact hj), colE_get _ _ hi hj]

theorem accE_succ_t {k : Nat} {s₀ : State} {j : Nat} (hj : j < k) :
    accE k s₀ (j + 1) k = add (accE k s₀ j k)
      (multiplyNTTs (polyAt s₀.mem (tP s₀ + BitVec.ofNat 64 (1024 * j))) ((yv k s₀)[j]!)) := by
  simp only [accE, ifn (Nat.lt_irrefl k)]
  rw [dotP_succ (by rw [vecAt_length]; exact hj) (by rw [List.length_map, vecAt_length]; exact hj), vecAt_get _ _ hj]

/-! ## Regions of the arguments -/

section
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀) (hk : k ≤ 4)
include hp

theorem dUC : (vR (uP s₀) (k + 1)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.1
theorem dAC : (vR (aP s₀) (k * k)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.1
theorem dTC : (vR (tP s₀) k).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.1
theorem dYC : (vR (yP s₀) k).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.1
theorem rU : (retR s₀).Disjoint (vR (uP s₀) (k + 1)) := hp.2.2.2.2.2.2.2.2.2.1
theorem rA : (retR s₀).Disjoint (vR (aP s₀) (k * k)) := hp.2.2.2.2.2.2.2.2.2.2.1
theorem rT : (retR s₀).Disjoint (vR (tP s₀) k) := hp.2.2.2.2.2.2.2.2.2.2.2.1
theorem rY : (retR s₀).Disjoint (vR (yP s₀) k) := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rC : (retR s₀).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1

omit hp in
/-- A polynomial of `a`, `t` or `y` in memory that differs from the start only in `u` and `scratch`. -/
theorem in_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {p : Addr} {n e : Nat}
    (he : e < n) (hU : (vR (uP s₀) (k + 1)).Disjoint (vR p n)) (hC : (vR p n).Disjoint (cR (cP s₀)))
    (hr : VecReduced s₀.mem p n) :
    PolyIs m (p + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (p + BitVec.ofNat 64 (1024 * e))) := by
  refine polyIs_frame hf (fun r hr' => ?_) ⟨hr e he, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact (hU.sub_right (sub_v _ he)).symm
  · exact hC.sub_left (sub_v _ he)

theorem a_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k * k) :
    PolyIs m (aP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (aP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  in_frame hf he hp.2.2.1 (dAC hp) hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem t_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k) :
    PolyIs m (tP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (tP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  in_frame hf he hp.2.2.2.1 (dTC hp) hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem y_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k) :
    PolyIs m (yP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (yP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  in_frame hf he hp.2.2.2.2.1 (dYC hp) hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

omit hp in
include hk in
theorem dUU {i i' : Nat} (hi : i < k + 1) (hi' : i' < k + 1) (hne : i ≠ i') :
    (pR (uP s₀ + BitVec.ofNat 64 (1024 * i))).Disjoint (pR (uP s₀ + BitVec.ofNat 64 (1024 * i'))) :=
  Offset.disjoint _ (by omega) (by omega) (by omega)

theorem dUhi {i : Nat} (hi : i < k + 1) : (hiR (cP s₀)).Disjoint (pR (uP s₀ + BitVec.ofNat 64 (1024 * i))) := by
  have h1 := (dUC hp).sub_left (sub_v _ hi)
  have h2 : Region.Sub (hiR (cP s₀)) (cR (cP s₀)) := sub_c (by decide)
  exact (h1.sub_right h2).symm

end

/-! ## Steps that write `u` and the first three quarters of `scratch` -/

theorem in_vec (p : Addr) {n j : Nat} (hn : n ≤ 64) (hj : j < n) :
    (vR p n).Contains (p + BitVec.ofNat 64 (1024 * j)) 1024 :=
  Offset.contains_base p (by have := Nat.mul_le_mul_left 1024 (show j + 1 ≤ n by omega); rw [Nat.mul_succ] at this; omega)
    (by omega)

theorem hi_read {m m' : Mem} {C : Addr} {rs : List Region} (hf : Frame rs m m') (hhi : ∀ r ∈ rs, (hiR C).Disjoint r)
    {d : Nat} (h3 : 3072 ≤ d) (h8 : d + 8 ≤ 4096) : m'.readW (C + BitVec.ofNat 64 d) 64 = m.readW (C + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨C + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => (hhi r hr).sub_left (sub_hi h3 h8))
    (by decide)

theorem Base.step {k : Nat} {s₀ s s' : State} (hb : Base k s₀ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, Region.Sub r (vR (uP s₀) (k + 1)) ∨ Region.Sub r (cR (cP s₀)))
    (hhi : ∀ r ∈ rs, (hiR (cP s₀)).Disjoint r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : Base k s₀ s' :=
  ⟨by rw [hcs .rbx (by decide), hb.rbx], by rw [hcs .rsp (by decide), hb.rsp], hrd.trans hb.rd, hwr.trans hb.wr,
    hb.frame.trans (hf.sub fun r hr => (hsub r hr).elim (fun h => ⟨_, by simp, h⟩) fun h => ⟨_, by simp, h⟩),
    hb.saved.frame hf fun p hp' r hr => (hhi r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1 (by
      have := (DecMul.slots_bound p hp').2; omega))⟩

/-! ## Zeroing the sums -/

theorem coeffAtN_write128 (m : Mem) (p : Addr) {N j : Nat} (hN : N ≤ 2 ^ 20) (hj : j + 4 ≤ N) (x : BitVec 128)
    {i : Nat} (hi : i < N) :
    coeffAt (m.writeW (coeffAddr p j) x) p i = if j ≤ i ∧ i < j + 4 then dword x (i - j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_off, show j + (i - j) = i by omega]]
    exact readW_writeW128 _ _ _ (by omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

namespace ZeroU

/-- After `i` stores of sixteen bytes. -/
structure Inv (k : Nat) (s₀ : State) (wP : Addr) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr wP (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x0 : s.xmm .xmm0 = 0
  keep : Keep [.rdi, .rcx] s₀ s
  frame : Frame [vR wP (k + 1)] s₀.mem s.mem
  zero : ∀ c < 4 * i, coeffAt s.mem wP c = 0

end ZeroU

theorem zeroU_ok {k : Nat} (hk : k ≤ 4) {s : State} {wP : Addr} (hU : s.gpr .rbp = wP) (hw : vR wP (k + 1) ∈ s.wr) :
    WP isa (KpkeMul.zeroU k) s fun s' => (∀ i < k + 1, PolyIs s'.mem (wP + BitVec.ofNat 64 (1024 * i)) zero) ∧
      Frame [vR wP (k + 1)] s.mem s'.mem ∧ Keep [.rdi, .rcx] s s' := by
  unfold KpkeMul.zeroU
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = wP ∧ s1.xmm .xmm0 = 0 ∧ s1.mem = s.mem ∧
      Keep [.rdi] s s1) (by
        vrunm [hU]
        refine ⟨by simp [XBinOp.eval], fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun s1 ⟨hdi, hx, hm, k1⟩ => ?_)
  have hN : 64 * (k + 1) < 2 ^ 31 := by omega
  refine WP.mono (wp_rcxLoop (N := 64 * (k + 1)) (by omega) hN (ZeroU.Inv k s wP) (fun u g _ => ?_)
    fun i hi u hI => ?_) fun u hI => ⟨fun i hi => polyIs_of_toNat fun c hc => ?_, hI.frame, hI.keep⟩
  · refine ⟨by rw [g.keep.gpr (by decide), hdi]; exact (BitVec.add_zero _).symm, by rw [g.keep.2.1, k1.2.1],
      by rw [g.keep.2.2, k1.2.2], by rw [g.xmm, hx], (k1.trans g.keep).mono (by decide),
      by rw [g.mem, hm]; exact Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  · have hc : InRegions u.wr (u.gpr .rdi) 16 := by
      rw [hI.wr, hI.rdi]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    have hc' : InRegions (u.rd ++ u.wr) (u.gpr .rdi) 16 := let ⟨r, hr, h⟩ := hc; ⟨r, List.mem_append_right _ hr, h⟩
    vrunm [hc, hc']
    refine ⟨?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hI.rd,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hI.wr,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hI.x0, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, fun c hc => ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
      rw [hI.rdi, show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_off, Nat.mul_succ]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      exact hI.keep.gpr (by simp [hr])
    · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hI.keep.2.1
    · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hI.keep.2.2
    · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
      rw [hI.rdi]
      exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
      rw [hI.rdi, coeffAtN_write128 _ _ (N := 256 * (k + 1)) (by omega) (by omega) _ (by omega), hI.x0]
      split
      · simp [dword]
      · exact hI.zero c (by omega)
  · rw [n_eq] at hc
    have e := hI.zero (256 * i + c) (by omega)
    rw [coeffAt_eq] at e
    rw [coeffAt_eq, show coeffAddr (wP + BitVec.ofNat 64 (1024 * i)) c = coeffAddr wP (256 * i + c) by
      simp only [coeffAddr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega, e, zero,
      getElem!_pos _ c (by rw [n_eq]; exact hc)]
    simp

/-! ## The inner loop -/

section
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} (hB : BodiesOk B)
include hp hk hB

set_option linter.unusedSimpArgs false in
/-- A product of the terms `j`: `Â[j, i] ×_T ŷ[j]` added to sum `i`. -/
theorem innerStep_ok {j i : Nat} {c14 : BitVec 64} (hj : j < k) (hi : i < k) {s : State} (hI : IInv k s₀ j i c14 s) :
    WP isa (KpkeMul.prodAdd B [.mov .rsi (.reg .r12), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * i)))] i) s
      (IInv k s₀ j (i + 1) c14) := by
  have e : k * j + i < k * k := by
    have := Nat.mul_le_mul_left k (show j + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega
  have hkk : k * k ≤ 64 := Nat.le_trans (Nat.mul_le_mul hk hk) (by decide)
  have hsr : s.rd = [vR (aP s₀) (k * k), vR (tP s₀) k, vR (yP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hret : retR s = retR s₀ := by simp only [retR, hI.rsp]
  have hA := a_frame hp hI.frame e
  have hX := hI.acc i (by omega)
  rw [ifn (Nat.lt_irrefl i)] at hX
  have hi31 : 1024 * i < 2 ^ 31 := by omega
  refine WP.mono (prodAdd_ok hB hi31 (C := cP s₀) (F := aP s₀ + BitVec.ofNat 64 (1024 * (k * j + i)))
    hI.rbx hI.rbp rfl ?_ ?_ ?_
    ((dAC hp).sub_left (sub_v _ e)) ((dUC hp).sub_left (sub_v _ (by omega)))
    (by rw [hret]; exact (rA hp).sub_right (sub_v _ e)) (by rw [hret]; exact (rU hp).sub_right (sub_v _ (by omega)))
    (by rw [hret]; exact rC hp) hX.1 hA.1 hI.yh.1) fun s1 ⟨hP1, hf1, hcs1, hrd1, hwr1⟩ => ?_
  · vrunm [hI.rbx, hI.r12, sx1024, sx2048, sx_ofNat hi31]
    refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  · rw [hsr, hsw]
    exact (cov_one (by simp) (in_vec _ hkk e)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_vec _ (by omega) (show i < k + 1 by omega))).cons Covers.nil))))
  · rw [hsw]
    exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_vec _ (by omega) (show i < k + 1 by omega))).cons Covers.nil))
  rw [hX.2, hA.2, hI.yh.2, ← accE_succ hj hi] at hP1
  have hb1 : Base k s₀ s1 := hI.toBase.step hf1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inr (sub_c (by decide)), .inr (sub_c0 _), .inl (sub_v _ (by omega))])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hi_dis_c (by decide), hi_dis_c0 _, dUhi hp (by omega)]) hrd1 hwr1 hcs1
  have keep : ∀ {q : Addr} {F : Poly}, PolyIs s.mem q F → (pR q).Disjoint (pR (cP s₀ + BitVec.ofNat 64 2048)) →
      (pR q).Disjoint (pR (cP s₀)) → (pR q).Disjoint (pR (uP s₀ + BitVec.ofNat 64 (1024 * i))) → PolyIs s1.mem q F :=
    fun h d1 d2 d3 => polyIs_frame hf1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [d1, d2, d3]) h
  refine ⟨hb1, by rw [hcs1 .r14 (by decide), hI.r14], by rw [hcs1 .rbp (by decide), hI.rbp],
    by rw [hcs1 .r12 (by decide), hI.r12], by rw [hcs1 .r13 (by decide), hI.r13],
    by rw [hcs1 .r15 (by decide), hI.r15], ?_, fun i' hi' => ?_⟩
  · exact keep hI.yh (dis_cc (.inl (by decide)) (by decide) (by decide)) (Offset.disjoint_base _ (by decide) (by decide))
      ((dUC hp).sub_left (sub_v _ (by omega)) |>.sub_right (sub_c (by decide)) |>.symm)
  · by_cases h : i' = i
    · subst h; rw [ifp (Nat.lt_succ_self _)]; exact hP1
    · have hd := (dUC hp).sub_left (sub_v (uP s₀) hi')
      have := keep (hI.acc i' hi') (hd.sub_right (sub_c (by decide))) (hd.sub_right (sub_c0 _))
        (dUU hk hi' (by omega) h)
      by_cases h' : i' < i
      · rwa [ifp h', ifp (by omega)] at *
      · rwa [ifn h', ifn (by omega)] at *

/-- The products of the terms `j` of the sums `i, …, k - 1`. -/
theorem innerE_ok {j : Nat} {c14 : BitVec 64} (hj : j < k) :
    ∀ n i, i + n = k → ∀ {s : State}, IInv k s₀ j i c14 s → WP isa (KpkeMul.innerE B i n) s (IInv k s₀ j k c14)
  | 0, i, h, _, hI => WP.block_nil (by rwa [show i = k by omega] at hI)
  | n + 1, i, h, _, hI => WP.seq (WP.mono (innerStep_ok hp hk hB hj (by omega) hI) fun _ h' =>
      innerE_ok hj n (i + 1) (by omega) h')

set_option linter.unusedSimpArgs false in
/-- An iteration of the outer loop: `ŷ[j]`, the terms `j` of every sum. -/
theorem termE_ok {j : Nat} (hj : j < k) {s : State} (hE : EInv k s₀ j s) :
    WP isa (KpkeMul.termE B k) s fun s' => EInv k s₀ (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hkk : k * k ≤ 64 := Nat.le_trans (Nat.mul_le_mul hk hk) (by decide)
  have hsr : s.rd = [vR (aP s₀) (k * k), vR (tP s₀) k, vR (yP s₀) k] := by rw [hE.rd, hp.1]
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hE.wr, hp.2.1]
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hY := y_frame hp hE.frame hj
  unfold KpkeMul.termE
  -- `ŷ[j]` to `scratch + 1024`
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = yP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = cP s₀ + BitVec.ofNat 64 1024 ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hE.r13, hE.rbx, sx1024]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hE.rsp]
  refine WP.seq (WP.inline (k := nttOK) hB.nttO (rd := [pR (yP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (cP s₀ + BitVec.ofNat 64 1024), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, (dYC hp).sub_left (sub_v _ hj) |>.sub_right (sub_c0 _),
      Offset.disjoint_base _ (by decide) (by decide), (rC hp).sub_right (sub_c (by decide)),
      (rC hp).sub_right (sub_c0 _), hY.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega) hj)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttOK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1, hY.2] at hpost2
  rw [← vecAt_map_get _ _ hj] at hpost2
  rw [hm1] at hf2
  have hhi2 : ∀ r ∈ [pR (cP s₀ + BitVec.ofNat 64 1024), pR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hi_dis_c (by decide), hi_dis_c0 _]
  have hb2 : Base k s₀ s2 := hE.toBase.step hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (sub_c (by decide)), .inr (sub_c0 _)]) hhi2
    (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) (fun r hr => by rw [habi2.1 r hr, cs (by decide) k1 r hr])
  have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by rw [habi2.1 r hr, cs (by decide) k1 r hr]
  have hacc2 : ∀ i < k + 1, PolyIs s2.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (accE k s₀ j i) := fun i hi =>
    polyIs_frame hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hd := (dUC hp).sub_left (sub_v (uP s₀) hi)
      rcases hr with rfl | rfl
      exacts [hd.sub_right (sub_c (by decide)), hd.sub_right (sub_c0 _)]) (hE.acc i hi)
  -- the products of `Â`'s row `j`
  refine WP.seq (WP.mono (innerE_ok hp hk hB (c14 := s.gpr .r14) hj k 0 (Nat.zero_add k)
    ⟨hb2, g2 .r14 (by decide), by rw [g2 .rbp (by decide), hE.rbp], by rw [g2 .r12 (by decide), hE.r12],
      by rw [g2 .r13 (by decide), hE.r13], by rw [g2 .r15 (by decide), hE.r15], hpost2,
      fun i' hi' => by rw [ifn (Nat.not_lt_zero _)]; exact hacc2 i' hi'⟩) fun u hI => ?_)
  -- the term of `t̂`
  have hret : retR u = retR s₀ := by simp only [retR, hI.rsp]
  have hT := t_frame hp hI.frame hj
  have hX := hI.acc k (by omega)
  rw [ifn (Nat.lt_irrefl k)] at hX
  have usr : u.rd = [vR (aP s₀) (k * k), vR (tP s₀) k, vR (yP s₀) k] := by rw [hI.rd, hp.1]
  have usw : u.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hk31 : 1024 * k < 2 ^ 31 := by omega
  refine WP.seq (WP.mono (prodAdd_ok hB hk31 (f := [.mov .rsi (.reg .r15)]) (C := cP s₀)
    (F := tP s₀ + BitVec.ofNat 64 (1024 * j)) hI.rbx hI.rbp rfl ?_ ?_ ?_
    ((dTC hp).sub_left (sub_v _ hj)) ((dUC hp).sub_left (sub_v _ (by omega)))
    (by rw [hret]; exact (rT hp).sub_right (sub_v _ hj)) (by rw [hret]; exact (rU hp).sub_right (sub_v _ (by omega)))
    (by rw [hret]; exact rC hp) hX.1 hT.1 hI.yh.1) fun s4 ⟨hP4, hf4, hcs4, hrd4, hwr4⟩ => ?_)
  · vrunm [hI.rbx, hI.r15, sx1024, sx2048]
    refine ⟨fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  · rw [usr, usw]
    exact (cov_one (by simp) (in_vec _ (by omega) hj)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_vec _ (by omega) (show k < k + 1 by omega))).cons Covers.nil))))
  · rw [usw]
    exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_vec _ (by omega) (show k < k + 1 by omega))).cons Covers.nil))
  rw [hX.2, hT.2, hI.yh.2, ← accE_succ_t hj] at hP4
  have hhi4 : ∀ r ∈ [pR (cP s₀ + BitVec.ofNat 64 2048), pR (cP s₀), pR (uP s₀ + BitVec.ofNat 64 (1024 * k))],
      (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hi_dis_c (by decide), hi_dis_c0 _, dUhi hp (by omega)]
  have hb4 : Base k s₀ s4 := hI.toBase.step hf4 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inr (sub_c (by decide)), .inr (sub_c0 _), .inl (sub_v _ (by omega))]) hhi4 hrd4 hwr4 hcs4
  -- the next row of `Â`, `t̂[j]` and `y[j]`
  vrunm [hcs4 .r12 (by decide), hcs4 .r13 (by decide), hcs4 .r14 (by decide), hcs4 .r15 (by decide), hI.r12,
    hI.r13, hI.r14, hI.r15, sx1024, sx_ofNat hk31]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb4.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb4.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [hcs4 .rbp (by decide), hI.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ, Nat.mul_add]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i = k
    · subst h; exact hP4
    · have := hI.acc i hi
      rw [ifp (by omega)] at this
      exact polyIs_frame hf4 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hd := (dUC hp).sub_left (sub_v (uP s₀) hi)
        rcases hr with rfl | rfl | rfl
        exacts [hd.sub_right (sub_c (by decide)), hd.sub_right (sub_c0 _), dUU hk hi (by omega) h]) this

set_option linter.unusedSimpArgs false in
theorem invStep_ok {i : Nat} (hi : i < k + 1) {s : State} (hV : VInv k s₀ i s) :
    WP isa (KpkeMul.invE B) s fun s' => VInv k s₀ (i + 1) s' ∧ s'.gpr .r15 = s.gpr .r15 - 1 ∧
      s'.zf = some (s.gpr .r15 - 1 == 0) := by
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hV.wr, hp.2.1]
  have hX := hV.acc i hi
  rw [ifn (Nat.lt_irrefl i)] at hX
  unfold KpkeMul.invE
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * i) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.mem = s.mem ∧ Keep [.rdi, .rsi] s s1) (by
        vrunm [hV.rbx, hV.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1di, h1si, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hV.rsp]
  refine WP.seq (WP.inline (k := inPlaceK nttInv) hB.inv (rd := [])
    (wr := [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.2.1)
  · simp only [inPlaceK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, hsp1, hm1, retR]
    exact ⟨trivial, trivial, (dUC hp).sub_left (sub_v _ hi) |>.sub_right (sub_c0 _),
      (rU hp).sub_right (sub_v _ hi), (rC hp).sub_right (sub_c0 _), hX.1⟩
  · rw [k1.2.1, k1.2.2, hsw]
    exact Covers.right ((cov_one (by simp) (in_vec _ (by omega) hi)).cons ((cov_one (by simp) (in_c0 _)).cons
      Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega) hi)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [inPlaceK, State.withRegions_gpr, State.withRegions_mem, h1di, hm1, hX.2] at hpost2
  rw [hm1] at hf2
  have hhi : ∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [dUhi hp hi, hi_dis_c0 _]
  have hb2 : Base k s₀ s2 := hV.toBase.step hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl (sub_v _ hi), .inr (sub_c0 _)]) hhi
    (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) (fun r hr => by rw [habi2.1 r hr, cs (by decide) k1 r hr])
  vrunm [habi2.1 .rbp (by decide), habi2.1 .r15 (by decide), k1.gpr (r := .rbp) (by decide),
    k1.gpr (r := .r15) (by decide), sx1024]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun i' hi' => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb2.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb2.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb2.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb2.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb2.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb2.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [hV.rbp, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i' = i
    · subst h; rw [ifp (Nat.lt_succ_self _)]; exact hpost2
    · have := hV.acc i' hi'
      have hd := (dUC hp).sub_left (sub_v (uP s₀) hi')
      have h2 := polyIs_frame hf2 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [dUU hk hi' hi h, hd.sub_right (sub_c0 _)]) this
      by_cases h' : i' < i
      · rwa [ifp h', ifp (by omega)] at *
      · rwa [ifn h', ifn (by omega)] at *

end

/-- The code inside the MXCSR region. -/
abbrev innerE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (KpkeMul.zeroU k) (.seq (.loop (KpkeMul.termE B k) .ne)
    (.seq (.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (k + 1)))])
      (.loop (KpkeMul.invE B) .ne)))

theorem saveE_eq : KpkeMul.saveE = Spill.saveCode .r8 KpkeMul.slots := rfl

theorem accE_zero (k : Nat) (s₀ : State) (i : Nat) : accE k s₀ 0 i = zero := by
  simp only [accE]; split <;> exact dotP_zero _ _

theorem accE_full {k : Nat} {s₀ : State} {i : Nat} (hi : i < k) :
    accE k s₀ k i = dot (colE s₀.mem (aP s₀) k i) (yv k s₀) := by
  simp only [accE, ifp hi]; exact dotP_full (colE_length _ _ _ _) (by rw [List.length_map, vecAt_length])

theorem accE_full_t (k : Nat) (s₀ : State) : accE k s₀ k k = dot (tv k s₀) (yv k s₀) := by
  simp only [accE, ifn (Nat.lt_irrefl k)]; exact dotP_full (vecAt_length _ _ _) (by rw [List.length_map, vecAt_length])

section
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} (hB : BodiesOk B)
include hp hk hB

theorem wp_all (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp] (innerE B k) = true) :
    WP isa (encryptMul B k) s₀ fun s' => gprPreserved s₀ s' ∧ (encMulK k).post s₀ s' := by
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hww : vR (uP s₀) (k + 1) ∈ s₀.wr := by rw [hp.2.1]; simp
  unfold encryptMul
  refine WP.seq ?_
  rw [saveE_eq]
  refine Spill.save_then .r8 KpkeMul.slots (fun p hp' => ⟨_, hcw, in_c (by
    have := DecMul.slots_bound p hp'; omega)⟩) ?_
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rbx = cP s₀ ∧ s1.gpr .rbp = uP s₀ ∧ s1.gpr .r12 = aP s₀ ∧
      s1.gpr .r13 = yP s₀ ∧ s1.gpr .r15 = tP s₀ ∧ s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.gpr .rsp = s₀.gpr .rsp ∧
      s1.rd = s₀.rd ∧ s1.wr = s₀.wr ∧ s1.mem = Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (by
        vrunm
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega) fun s1 ⟨h1bx, h1bp, h112, h113, h115, h114, h1sp, h1rd, h1wr, hm1⟩ => ?_
  have h0 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 768) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 772) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  -- the memory after the prologue
  have hsv : Spill.Saved s1.mem (cP s₀) s₀.gpr KpkeMul.slots := by
    rw [hm1]; exact Spill.saveMem_saved _ _ _ _ (by decide)
  have hf1 : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem s1.mem := by
    rw [hm1]
    exact (Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots (L := 4096)
      (fun p hp' => by have := DecMul.slots_bound p hp'; omega) (by decide)).sub
      (fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  have hmx : ∀ r ∈ [mxR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (withMxcsr_ok' (r := .rbx) (by decide) _ (by decide) h1bx h0 h4 hwo
    (Q := fun s' => Base k s₀ s' ∧ ∀ i < k + 1, PolyIs s'.mem (uP s₀ + BitVec.ofNat 64 (1024 * i))
      (nttInv (accE k s₀ k i)))
    (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, ⟨hb4, hacc4⟩, hf5, k5⟩ => ?_)
  · -- zero the sums, the loops
    have k12 := k2
    have hb2 : Base k s₀ s2 := ⟨by rw [k2.gpr (by decide), h1bx], by rw [k2.gpr (by decide), h1sp],
      by rw [k2.2.1, h1rd], by rw [k2.2.2, h1wr],
      hf1.trans (f2.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩),
      hsv.frame f2 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega))⟩
    refine WP.seq (WP.mono (zeroU_ok hk (s := s2) (wP := uP s₀) (by rw [k2.gpr (by decide), h1bp])
      (by rw [hb2.wr]; exact hww)) fun s3 ⟨hz, hf3, k3⟩ => ?_)
    have hu3 : ∀ r ∈ [vR (uP s₀) (k + 1)], (hiR (cP s₀)).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((dUC hp).sub_right (sub_c (by decide))).symm
    have hb3 : Base k s₀ s3 := hb2.step hf3 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl fun _ h => h) hu3 k3.2.1 k3.2.2
      (fun r hr => k3.gpr ((show ∀ r ∈ calleeSaved, r ∉ [Reg.rdi, .rcx] by decide) r hr))
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (EInv k s₀)
      (fun j hj u hE _ => termE_ok hp hk hB hj hE) (fun u hE => ?_)
      ⟨hb3, by rw [k3.gpr (by decide), k2.gpr (by decide), h1bp],
        by rw [k3.gpr (by decide), k2.gpr (by decide), h112, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero],
        by rw [k3.gpr (by decide), k2.gpr (by decide), h113, Nat.mul_zero, add_ofNat_zero],
        by rw [k3.gpr (by decide), k2.gpr (by decide), h115, Nat.mul_zero, add_ofNat_zero],
        fun i hi => by rw [accE_zero]; exact hz i hi⟩
      (by rw [k3.gpr (by decide), k2.gpr (by decide), h114]))
    -- `NTT⁻¹` of each sum
    refine WP.seq (WP.mono (Q := fun (s6 : State) => s6.gpr .rbp = uP s₀ ∧
        s6.gpr .r15 = BitVec.ofNat 64 (k + 1) ∧ s6.mem = u.mem ∧ Keep [.rbp, .r15] u s6) (by
          vrunm [hE.rbp]
          refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
          · apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s6 ⟨h6bp, h615, hm6, k6⟩ => ?_)
    refine wp_countdown (cnt := .r15) (N := k + 1) (by omega) (by omega) (VInv k s₀)
      (fun i hi u hV _ => invStep_ok hp hk hB hi hV) (fun u hV => ⟨hV.toBase, fun i hi => by
        have := hV.acc i hi; rwa [ifp hi] at this⟩)
      ⟨⟨by rw [k6.gpr (by decide)]; exact hE.rbx, by rw [k6.gpr (by decide)]; exact hE.rsp,
        by rw [k6.2.1]; exact hE.rd, by rw [k6.2.2]; exact hE.wr, by rw [hm6]; exact hE.frame,
        by rw [hm6]; exact hE.saved⟩, by rw [h6bp, Nat.mul_zero, add_ofNat_zero],
        fun i hi => by rw [ifn (Nat.not_lt_zero _), hm6]; exact hE.acc i hi⟩ h615
  · -- the epilogue
    have h5bx : s5.gpr .rbx = cP s₀ := by rw [k5.gpr (by decide), hb4.rbx]
    have hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem s5.mem :=
      hb4.frame.trans (hf5.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩)
    have hs5 : Spill.Saved s5.mem (s5.gpr .rbx) s₀.gpr KpkeMul.slots := by
      rw [h5bx]
      exact hb4.saved.frame hf5 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega))
    rw [DecMul.restore_eq]
    refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots s₀.gpr s5 (by decide) (fun p hp' => ?_) hs5)
      fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by rw [k5.gpr (by decide), hb4.rsp]), ?_⟩, ?_⟩
    · rw [h5bx, k5.2.1, k5.2.2, hb4.rd, hb4.wr]
      exact ⟨_, List.mem_append_right _ hcw, in_c (by have := DecMul.slots_bound p hp'; omega)⟩
    · rw [hm']
      refine hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [rU hp, rC hp]
    · refine ⟨by rw [List.length_append, mulMatTVec_length]; rfl, fun i hi => ?_⟩
      rw [hm']
      have := polyIs_frame hf5 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((dUC hp).sub_left (sub_v _ hi)).sub_right (sub_c (by decide))) (hacc4 i hi)
      by_cases h : i < k
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [mulMatTVec_length]; exact h),
          ← List.getD_eq_getElem?_getD, mulMatTVec_getD _ _ _ _ h, ← accE_full h]
        exact this
      · have hik : i = k := by omega
        subst hik
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [mulMatTVec_length]),
          mulMatTVec_length, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ← accE_full_t]
        exact this

end

end EncMul

end VG.Proof.MlKem.X86_64
