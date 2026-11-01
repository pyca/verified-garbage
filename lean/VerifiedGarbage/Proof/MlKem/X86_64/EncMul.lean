module

public import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem*_encrypt_mul`

`encryptMul B k` (`Impl/MlKem/X86_64/KpkeMul.lean`), as `decryptMul`
(`DecMul.lean`) with an accumulator per output, at `u[i]`: the prologue
saves the callee-saved registers in `scratch` and keeps the pointers in
registers; `startE` sets up the table and the `k + 1` accumulators of zero
(`startE_ok`); after `j` iterations of the outer loop, accumulator `i < k`
holds the first `j` terms of `Â^⊺ ∘ ŷ`'s entry `i` (its column `i` of `Â`,
`colE`), and accumulator `k` those of `t̂^⊺ ∘ ŷ` (`EInv`); an iteration
computes `ŷ[j] = NTT(y[j])`, adds `Â[j, i] ×_T ŷ[j]` to each accumulator
`i < k` (`IInv`, `innerE_ok`, unrolled), then `t̂[j] ×_T ŷ[j]` to
accumulator `k` (`termE_ok`); the last loop computes `NTT⁻¹` of each
accumulator, to `u[i]` (`invStep_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open DecMul (sub_c sub_c0 sub_v in_c in_c0 in_v dis_cc cov_one sx1024 sx2048)

/-- `vg_mlkem*_encrypt_mul(u = rdi, a = rsi, t = rdx, y = rcx, scratch = r8)` of rank `k`, with
`Â` stored at `a` in the region `aR a`, reduced as `aRed` says, as the matrix `aMat`, and `y`
stored at `y` in the region `yR y`, reduced as `yRed` says, as the vector `yVec`. -/
def encMulKG (k : Nat) (aR : Addr → Region) (aRed : Mem → Addr → Prop) (aMat : Mem → Addr → List (List Poly))
    (yR : Addr → Region) (yRed : Mem → Addr → Prop) (yVec : Mem → Addr → List Poly) : Contract isa where
  pre s :=
    s.rd = [aR (s.gpr .rsi), vR (s.gpr .rdx) k, yR (s.gpr .rcx)] ∧
    s.wr = [vR (s.gpr .rdi) (k + 1), cR (s.gpr .r8)] ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (aR (s.gpr .rsi)) ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (vR (s.gpr .rdx) k) ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (yR (s.gpr .rcx)) ∧
    (vR (s.gpr .rdi) (k + 1)).Disjoint (cR (s.gpr .r8)) ∧
    (aR (s.gpr .rsi)).Disjoint (cR (s.gpr .r8)) ∧ (vR (s.gpr .rdx) k).Disjoint (cR (s.gpr .r8)) ∧
    (yR (s.gpr .rcx)).Disjoint (cR (s.gpr .r8)) ∧
    (retR s).Disjoint (vR (s.gpr .rdi) (k + 1)) ∧ (retR s).Disjoint (aR (s.gpr .rsi)) ∧
    (retR s).Disjoint (vR (s.gpr .rdx) k) ∧ (retR s).Disjoint (yR (s.gpr .rcx)) ∧
    (retR s).Disjoint (cR (s.gpr .r8)) ∧
    aRed s.mem (s.gpr .rsi) ∧ VecReduced s.mem (s.gpr .rdx) k ∧ yRed s.mem (s.gpr .rcx)
  post s s' :=
    VecIs s'.mem (s.gpr .rdi) (k + 1)
      (((mulMatTVec k (aMat s.mem (s.gpr .rsi)) ((yVec s.mem (s.gpr .rcx)).map ntt)).map nttInv) ++
        [nttInv (dot (vecAt s.mem (s.gpr .rdx) k) ((yVec s.mem (s.gpr .rcx)).map ntt))])
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `encMulKG` with `y` as `k` polynomials of `u32`s. -/
abbrev encMulKA (k : Nat) (aR : Addr → Region) (aRed : Mem → Addr → Prop) (aMat : Mem → Addr → List (List Poly)) :
    Contract isa :=
  encMulKG k aR aRed aMat (fun p => vR p k) (fun m p => VecReduced m p k) (fun m p => vecAt m p k)

/-- `encMulKA` with `Â` as `k²` polynomials of `u32`s. -/
abbrev encMulK (k : Nat) : Contract isa :=
  encMulKA k (fun p => vR p (k * k)) (fun m p => VecReduced m p (k * k)) (fun m p => matAt m p k)

/-- `encMulKG` with `Â` as `k²` polynomials of `u16`s and `y` as `k`. -/
abbrev encMulK16 (k : Nat) : Contract isa :=
  encMulKG k (fun p => ⟨p, 512 * (k * k)⟩) (fun m p => VecReducedW 16 m p (k * k)) (fun m p => matAtW 16 m p k)
    (fun p => ⟨p, 512 * k⟩) (fun m p => VecReducedW 16 m p k) (fun m p => vecAtW 16 m p k)

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

/-- The 256 bytes of `scratch` from 3072, where the registers are kept. -/
abbrev hiR (C : Addr) : Region := ⟨C + BitVec.ofNat 64 3072, 256⟩

theorem hi_dis_c {C : Addr} {o : Nat} (ho : o ≤ 2048) : (hiR C).Disjoint (pR (C + BitVec.ofNat 64 o)) :=
  Offset.disjoint C (.inr (by omega)) (by omega) (by omega)

theorem hi_dis_c0 (C : Addr) : (hiR C).Disjoint (pR C) := Offset.disjoint_base C (by omega) (by omega)

theorem hi_dis_tab (C : Addr) : (hiR C).Disjoint (tabR C) := Offset.disjoint C (.inl (by omega)) (by omega) (by omega)


theorem sub_hi {C : Addr} {d n : Nat} (h3 : 3072 ≤ d) (h8 : d + n ≤ 3328) :
    Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ (hiR C) :=
  Offset.sub C h3 (by omega)

/-! ## A product added to an accumulator -/

section
variable {B : Bodies} {R : AccRep} {T : TabRep} (hB : BodiesOk B R T)
include hB

set_option linter.unusedSimpArgs false in
/-- `prodAcc B f o`: the product of the polynomial `f` points `rsi` at with
the one at `scratch + 1024`, added to accumulator `o` at `rbp`. -/
theorem prodAcc_ok {f : List Instr} {o : Nat} (ho : 1024 * o < 2 ^ 31) {s : State} {C F P : Addr} {A : Poly}
    (hbx : s.gpr .rbx = C) (hbp : s.gpr .rbp + BitVec.ofNat 64 (1024 * o) = P)
    (hset : WP isa (.block (([.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * o)))] : List Instr) ++
      f ++ ([.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)] : List Instr))) s fun s1 =>
      s1.gpr .rdi = P ∧ s1.gpr .rsi = F ∧ s1.gpr .rdx = C + BitVec.ofNat 64 1024 ∧
        s1.gpr .rcx = C ∧ s1.mem = s.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s1)
    (hcov : Covers [pR F, pR (C + BitVec.ofNat 64 1024), tabR C, pR P, pR C, tmpR C] (s.rd ++ s.wr))
    (hw : Covers [pR P, pR C, tmpR C] s.wr)
    (hFC : (pR F).Disjoint (cR C)) (hPC : (pR P).Disjoint (cR C)) (hPF : (pR P).Disjoint (pR F))
    (hrF : (retR s).Disjoint (pR F)) (hrP : (retR s).Disjoint (pR P)) (hrC : (retR s).Disjoint (cR C))
    (rG : Reduced s.mem F) (rY : Reduced s.mem (C + BitVec.ofNat 64 1024)) (hT : T.is s.mem C)
    (hA : R.is s.mem P A) :
    WP isa (KpkeMul.prodAcc B f o) s fun s' =>
      R.is s'.mem P (add A (multiplyNTTs (polyAt s.mem F) (polyAt s.mem (C + BitVec.ofNat 64 1024)))) ∧
      Frame [pR P, pR C, tmpR C] s.mem s'.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hcov' : ∀ Q ∈ [pR F, pR (C + BitVec.ofNat 64 1024), tabR C, pR P, pR C, tmpR C],
      Covers [Q] (s.rd ++ s.wr) := fun Q hQ a n h => hcov a n (let ⟨r, hr, hc⟩ := h; ⟨r, by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ, hc⟩)
  have hw' : ∀ Q ∈ [pR P, pR C, tmpR C], Covers [Q] s.wr := fun Q hQ a n h =>
    hw a n (let ⟨r, hr, hc⟩ := h; ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact hQ, hc⟩)
  have pd := DecMul.prod_dis C
  unfold KpkeMul.prodAcc
  refine WP.seq (WP.mono hset fun s3 ⟨h3di, h3si, h3dx, h3cx, hm3, k3⟩ => ?_)
  have hsp3 : s3.gpr .rsp = s.gpr .rsp := cs (by decide) k3 .rsp (by decide)
  have hbx3 : s3.gpr .rbx = C := by rw [cs (by decide) k3 .rbx (by decide), hbx]
  have hbp3 : s3.gpr .rbp + BitVec.ofNat 64 (1024 * o) = P := by rw [cs (by decide) k3 .rbp (by decide), hbp]
  refine WP.inline (k := mulAccK R T o) (hB.mulAcc o ho) (rd := [pR F, pR (C + BitVec.ofNat 64 1024), tabR C])
    (wr := [pR P, pR C, tmpR C]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) (hB.nc.2.2.2 o)
  · simp only [mulAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, h3dx, h3cx, hsp3, hbx3, hbp3, hm3, retR]
    exact ⟨trivial, trivial, hPF, hPC.sub_right (sub_c (by decide)), hPC.sub_right (sub_c0 _),
      hPC.sub_right (sub_c (by decide)), hPC.sub_right (sub_c (by decide)), hFC.sub_right (sub_c0 _),
      hFC.sub_right (sub_c (by decide)), pd.1, pd.2.1, pd.2.2.1, pd.2.2.2.1, pd.2.2.2.2,
      hrP, hrF, hrC.sub_right (sub_c (by decide)), hrC.sub_right (sub_c0 _),
      hrC.sub_right (sub_c (by decide)), hrC.sub_right (sub_c (by decide)), trivial, trivial, rG, rY, hT, ⟨_, hA⟩⟩
  · rw [k3.2.1, k3.2.2]
    exact (hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons
      ((hcov' _ (by simp)).cons ((hcov' _ (by simp)).cons Covers.nil)))))
  · rw [k3.2.2]
    exact (hw' _ (by simp)).cons ((hw' _ (by simp)).cons ((hw' _ (by simp)).cons Covers.nil))
  simp only [mulAccK, State.withRegions_gpr, State.withRegions_mem, h3di, h3si, h3dx, hm3] at hpost4
  rw [hm3] at hf4
  exact ⟨hpost4 A hA, hf4, fun r hr => by rw [habi4.1 r hr, cs (by decide) k3 r hr], by rw [hrd4, k3.2.1],
    by rw [hwr4, k3.2.2]⟩

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
structure EInv (R : AccRep) (T : TabRep) (j : Nat) (s : State) : Prop extends Base k s₀ s where
  rbp : s.gpr .rbp = uP s₀
  r12 : s.gpr .r12 = aP s₀ + BitVec.ofNat 64 (1024 * (k * j))
  r13 : s.gpr .r13 = yP s₀ + BitVec.ofNat 64 (1024 * j)
  r15 : s.gpr .r15 = tP s₀ + BitVec.ofNat 64 (1024 * j)
  tab : T.is s.mem (cP s₀)
  acc : ∀ i < k + 1, R.is s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (accE k s₀ j i)

/-- After the terms `j` of the first `i` sums. -/
structure IInv (R : AccRep) (T : TabRep) (j i : Nat) (c14 : BitVec 64) (s : State) : Prop extends Base k s₀ s where
  r14 : s.gpr .r14 = c14
  rbp : s.gpr .rbp = uP s₀
  r12 : s.gpr .r12 = aP s₀ + BitVec.ofNat 64 (1024 * (k * j))
  r13 : s.gpr .r13 = yP s₀ + BitVec.ofNat 64 (1024 * j)
  r15 : s.gpr .r15 = tP s₀ + BitVec.ofNat 64 (1024 * j)
  yh : PolyIs s.mem (cP s₀ + BitVec.ofNat 64 1024) ((yv k s₀)[j]!)
  tab : T.is s.mem (cP s₀)
  acc : ∀ i' < k + 1, R.is s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i'))
    (if i' < i then accE k s₀ (j + 1) i' else accE k s₀ j i')

end

/-- After `NTT⁻¹` of the first `i` sums. -/
structure VInv (R : AccRep) (k : Nat) (s₀ : State) (i : Nat) (s : State) : Prop extends Base k s₀ s where
  rbp : s.gpr .rbp = uP s₀ + BitVec.ofNat 64 (1024 * i)
  done : ∀ i' < i, PolyIs s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i')) (nttInv (accE k s₀ k i'))
  acc : ∀ i', i ≤ i' → i' < k + 1 → R.is s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i')) (accE k s₀ k i')

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
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} {yR : Addr → Region} {yRed : Mem → Addr → Prop}
  {yVec : Mem → Addr → List Poly} (hp : (encMulKG k aR aRed aMat yR yRed yVec).pre s₀) (hk : k ≤ 4)
include hp

theorem dUC : (vR (uP s₀) (k + 1)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.1
theorem dAC : (aR (aP s₀)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.1
theorem dTC : (vR (tP s₀) k).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.1
theorem dYC : (yR (yP s₀)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.1
theorem rU : (retR s₀).Disjoint (vR (uP s₀) (k + 1)) := hp.2.2.2.2.2.2.2.2.2.1
theorem rA : (retR s₀).Disjoint (aR (aP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.1
theorem rT : (retR s₀).Disjoint (vR (tP s₀) k) := hp.2.2.2.2.2.2.2.2.2.2.2.1
theorem rY : (retR s₀).Disjoint (yR (yP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
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

theorem t_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k) :
    PolyIs m (tP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (tP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  in_frame hf he hp.2.2.2.1 (dTC hp :) hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


omit hp in
include hk in
theorem dUU {i i' : Nat} (hi : i < k + 1) (hi' : i' < k + 1) (hne : i ≠ i') :
    (pR (uP s₀ + BitVec.ofNat 64 (1024 * i))).Disjoint (pR (uP s₀ + BitVec.ofNat 64 (1024 * i'))) :=
  Offset.disjoint _ (by omega) (by omega) (by omega)

theorem dUhi {i : Nat} (hi : i < k + 1) : (hiR (cP s₀)).Disjoint (pR (uP s₀ + BitVec.ofNat 64 (1024 * i))) := by
  have h1 := (dUC hp :).sub_left (sub_v _ hi)
  have h2 : Region.Sub (hiR (cP s₀)) (cR (cP s₀)) := sub_c (by decide)
  exact (h1.sub_right h2).symm

end

section
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀)
include hp

theorem a_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k * k) :
    PolyIs m (aP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (aP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  in_frame hf he hp.2.2.1 (dAC hp :) hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} (hp : (encMulKA k aR aRed aMat).pre s₀)
include hp

theorem y_frame {m : Mem} (hf : Frame [vR (uP s₀) (k + 1), cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k) :
    PolyIs m (yP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (yP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  in_frame hf he hp.2.2.2.2.1 (dYC hp :) hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

/-! ## Steps that write `u` and the first three quarters of `scratch` -/

theorem in_vec (p : Addr) {n j : Nat} (hn : n ≤ 64) (hj : j < n) :
    (vR p n).Contains (p + BitVec.ofNat 64 (1024 * j)) 1024 :=
  Offset.contains_base p (by have := Nat.mul_le_mul_left 1024 (show j + 1 ≤ n by omega); rw [Nat.mul_succ] at this; omega)
    (by omega)

theorem hi_read {m m' : Mem} {C : Addr} {rs : List Region} (hf : Frame rs m m') (hhi : ∀ r ∈ rs, (hiR C).Disjoint r)
    {d : Nat} (h3 : 3072 ≤ d) (h8 : d + 8 ≤ 3328) : m'.readW (C + BitVec.ofNat 64 d) 64 = m.readW (C + BitVec.ofNat 64 d) 64 :=
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

/-! ## The table and the accumulators of zero -/

/-- After the accumulators of the first `i` sums are zeroed, with the
callee-saved registers as in `g`. -/
structure ZInv (k : Nat) (s₀ : State) (R : AccRep) (T : TabRep) (g : Reg → BitVec 64) (i : Nat) (s : State) : Prop
    extends Base k s₀ s where
  cs : ∀ r ∈ calleeSaved, s.gpr r = g r
  tab : T.is s.mem (cP s₀)
  acc : ∀ i' < i, R.is s.mem (uP s₀ + BitVec.ofNat 64 (1024 * i')) zero

section
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

set_option linter.unusedSimpArgs false in
theorem zeroStep_ok {g : Reg → BitVec 64} (hbp : g .rbp = uP s₀) {i : Nat} (hi : i < k + 1) {s : State}
    (hI : ZInv k s₀ R T g i s) :
    WP isa (.seq (.block [.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * i)))]) B.zero) s
      (ZInv k s₀ R T g (i + 1)) := by
  have hi31 : 1024 * i < 2 ^ 31 := by omega
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * i) ∧
      s1.mem = s.mem ∧ Keep [.rdi] s s1) (by
        vrunm [hI.cs .rbp (by decide), hbp, sx_ofNat hi31]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.inline (k := zeroK R) hB.zero (rd := []) (wr := [pR (uP s₀ + BitVec.ofNat 64 (1024 * i))]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.2.2.1
  · simp only [zeroK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h1di, hsp1, retR]
    exact ⟨trivial, trivial, (rU hp :).sub_right (sub_v _ hi)⟩
  · rw [k1.2.1, k1.2.2, hsw]
    exact Covers.right ((cov_one (by simp) (in_vec _ (by omega) hi)).cons Covers.nil)
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega) hi)).cons Covers.nil
  simp only [zeroK, State.withRegions_gpr, State.withRegions_mem, h1di] at hpost2
  rw [hm1] at hf2
  have hcs2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by
    rw [habi2.1 r hr]; exact k1.gpr (fun h => by simp at h; subst h; simp [calleeSaved] at hr)
  have hd := (dUC hp :).sub_left (sub_v (uP s₀) hi)
  refine ⟨hI.toBase.step hf2 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl (sub_v _ hi))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dUhi hp hi)
    (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) hcs2, fun r hr => by rw [hcs2 r hr, hI.cs r hr], ?_,
    fun i' hi' => ?_⟩
  · refine T.frame hf2 (fun r hr => ?_) hI.tab
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_right (sub_c (o := 3328) (n := 256) (by decide))).symm
  · by_cases h : i' = i
    · subst h; exact hpost2
    · exact R.frame hf2 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dUU hk (by omega) hi h)
        (hI.acc i' (by omega))

theorem zeroE_ok {g : Reg → BitVec 64} (hbp : g .rbp = uP s₀) :
    ∀ n i, i + n = k + 1 → ∀ {s : State}, ZInv k s₀ R T g i s →
      WP isa (KpkeMul.zeroE B i n) s (ZInv k s₀ R T g (k + 1))
  | 0, i, h, _, hI => WP.block_nil (by rwa [show i = k + 1 by omega] at hI)
  | n + 1, i, h, _, hI => WP.seq (WP.mono (zeroStep_ok hp hk hB hbp (by omega) hI) fun _ h' =>
      zeroE_ok hbp n (i + 1) (by omega) h')

/-- The table, and the `k + 1` accumulators of zero. -/
theorem startE_ok {s : State} (hb : Base k s₀ s) (hbp : s.gpr .rbp = uP s₀) :
    WP isa (KpkeMul.startE B k) s (ZInv k s₀ R T s.gpr (k + 1)) := by
  unfold KpkeMul.startE
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧ Keep [.rcx] s s1) (by
      vrunm [hb.rbx]
      refine ⟨fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1cx, hm1, k1⟩ => ?_
  have hin : InRegions s1.wr (s1.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
    rw [k1.2.2, hb.wr, hp.2.1, h1cx]; exact ⟨cR (cP s₀), by simp, in_c (by decide)⟩
  refine WP.mono (hB.tab s1 hin) fun s2 ⟨hT2, hf2, k2⟩ => ?_
  rw [h1cx] at hT2 hf2
  rw [hm1] at hf2
  have k12 := k1.trans k2
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr =>
    k12.gpr (fun h => by simp at h; rcases h with rfl | rfl | rfl <;> simp [calleeSaved] at hr)
  refine zeroE_ok hp hk hB (g := s.gpr) hbp (k + 1) 0 (by omega)
    ⟨hb.step hf2 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (sub_c (by decide)))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hi_dis_tab _) k12.2.1 k12.2.2 hcs,
      hcs, hT2, fun _ h => absurd h (Nat.not_lt_zero _)⟩

end

/-! ## The inner loop -/

section
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

omit hB in
/-- What a product writes misses `ŷ[j]`, the table, the saved registers and the other accumulators. -/
theorem prod_frame {i : Nat} (hi : i < k + 1) :
    (∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀), tmpR (cP s₀)],
      Region.Sub r (vR (uP s₀) (k + 1)) ∨ Region.Sub r (cR (cP s₀))) ∧
    (∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀), tmpR (cP s₀)], (hiR (cP s₀)).Disjoint r) ∧
    (∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀), tmpR (cP s₀)], (tabR (cP s₀)).Disjoint r) ∧
    (∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀), tmpR (cP s₀)],
      (pR (cP s₀ + BitVec.ofNat 64 1024)).Disjoint r) ∧
    (∀ i' < k + 1, i' ≠ i → ∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀), tmpR (cP s₀)],
      (pR (uP s₀ + BitVec.ofNat 64 (1024 * i'))).Disjoint r) := by
  have pd := DecMul.prod_dis (cP s₀)
  have hd := (dUC hp :).sub_left (sub_v (uP s₀) hi)
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun i' hi' hne r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact .inl (sub_v _ hi)
  · exact .inr (sub_c0 _)
  · exact .inr (sub_c (by decide))
  · exact dUhi hp hi
  · exact hi_dis_c0 _
  · exact hi_dis_c (by decide)
  · exact (hd.sub_right (sub_c (o := 3328) (n := 256) (by decide))).symm
  · exact pd.2.2.2.1.symm
  · exact pd.2.2.2.2.symm
  · exact (hd.sub_right (sub_c (by decide))).symm
  · exact pd.1
  · exact pd.2.1
  · exact dUU hk hi' hi hne
  · exact ((dUC hp :).sub_left (sub_v (uP s₀) hi')).sub_right (sub_c0 _)
  · exact ((dUC hp :).sub_left (sub_v (uP s₀) hi')).sub_right (sub_c (by decide))

set_option linter.unusedSimpArgs false in
/-- A product of the terms `j`: `Â[j, i] ×_T ŷ[j]` added to accumulator `i`. -/
theorem innerStep_ok {j i : Nat} {c14 : BitVec 64} (hj : j < k) (hi : i < k) {s : State}
    (hI : IInv k s₀ R T j i c14 s) :
    WP isa (KpkeMul.prodAcc B [.mov .rsi (.reg .r12), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * i)))] i) s
      (IInv k s₀ R T j (i + 1) c14) := by
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
  have hiu : i < k + 1 := by omega
  refine WP.mono (prodAcc_ok hB hi31 (C := cP s₀) (F := aP s₀ + BitVec.ofNat 64 (1024 * (k * j + i)))
    hI.rbx (by rw [hI.rbp]) ?_ ?_ ?_
    ((dAC hp :).sub_left (sub_v _ e)) ((dUC hp :).sub_left (sub_v _ hiu))
    (((hp.2.2.1).sub_left (sub_v _ hiu)).sub_right (sub_v _ e))
    (by rw [hret]; exact (rA hp :).sub_right (sub_v _ e)) (by rw [hret]; exact (rU hp :).sub_right (sub_v _ hiu))
    (by rw [hret]; exact rC hp) hA.1 hI.yh.1 hI.tab hX) fun s1 ⟨hP1, hf1, hcs1, hrd1, hwr1⟩ => ?_
  · vrunm [hI.rbx, hI.r12, hI.rbp, sx1024, sx_ofNat hi31]
    refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  · rw [hsr, hsw]
    exact (cov_one (by simp) (in_vec _ hkk e)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_vec _ (by omega) hiu)).cons
      ((cov_one (by simp) (in_c0 _)).cons ((cov_one (by simp) (in_c (by decide))).cons Covers.nil)))))
  · rw [hsw]
    exact (cov_one (by simp) (in_vec _ (by omega) hiu)).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_c (by decide))).cons Covers.nil))
  rw [hA.2, hI.yh.2, ← accE_succ hj hi] at hP1
  obtain ⟨fs, fhi, ftab, fy, fu⟩ := prod_frame hp hk hiu
  refine ⟨hI.toBase.step hf1 fs fhi hrd1 hwr1 hcs1, by rw [hcs1 .r14 (by decide), hI.r14],
    by rw [hcs1 .rbp (by decide), hI.rbp], by rw [hcs1 .r12 (by decide), hI.r12],
    by rw [hcs1 .r13 (by decide), hI.r13], by rw [hcs1 .r15 (by decide), hI.r15],
    polyIs_frame hf1 fy hI.yh, T.frame hf1 ftab hI.tab, fun i' hi' => ?_⟩
  by_cases h : i' = i
  · subst h; rw [ifp (Nat.lt_succ_self _)]; exact hP1
  · have := R.frame hf1 (fu i' hi' h) (hI.acc i' hi')
    by_cases h' : i' < i
    · rw [ifp h', ifp (by omega)] at *; with_reducible assumption
    · rw [ifn h', ifn (by omega)] at *; with_reducible assumption

/-- The products of the terms `j` of the sums `i, …, k - 1`. -/
theorem innerE_ok {j : Nat} {c14 : BitVec 64} (hj : j < k) :
    ∀ n i, i + n = k → ∀ {s : State}, IInv k s₀ R T j i c14 s →
      WP isa (KpkeMul.innerE B i n) s (IInv k s₀ R T j k c14)
  | 0, i, h, _, hI => WP.block_nil (by rwa [show i = k by omega] at hI)
  | n + 1, i, h, _, hI => WP.seq (WP.mono (innerStep_ok hp hk hB hj (by omega) hI) fun _ h' =>
      innerE_ok hj n (i + 1) (by omega) h')

set_option linter.unusedSimpArgs false in
/-- An iteration of the outer loop: `ŷ[j]`, the terms `j` of every sum. -/
theorem termE_ok {j : Nat} (hj : j < k) {s : State} (hE : EInv k s₀ R T j s) :
    WP isa (KpkeMul.termE B k) s fun s' => EInv k s₀ R T (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
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
    exact ⟨trivial, trivial, (dYC hp :).sub_left (sub_v _ hj) |>.sub_right (sub_c0 _),
      Offset.disjoint_base _ (by decide) (by decide), (rC hp :).sub_right (sub_c (by decide)),
      (rC hp :).sub_right (sub_c0 _), hY.1⟩
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
  have hacc2 : ∀ i < k + 1, R.is s2.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (accE k s₀ j i) := fun i hi =>
    R.frame hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hd := (dUC hp :).sub_left (sub_v (uP s₀) hi)
      rcases hr with rfl | rfl
      exacts [hd.sub_right (sub_c (by decide)), hd.sub_right (sub_c0 _)]) (hE.acc i hi)
  have htab2 : T.is s2.mem (cP s₀) := T.frame hf2 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [Offset.disjoint _ (.inr (by decide)) (by decide) (by decide),
        (DecMul.prod_dis (cP s₀)).2.2.2.1.symm]) hE.tab
  -- the products of `Â`'s row `j`
  refine WP.seq (WP.mono (innerE_ok hp hk hB (c14 := s.gpr .r14) hj k 0 (Nat.zero_add k)
    ⟨hb2, g2 .r14 (by decide), by rw [g2 .rbp (by decide), hE.rbp], by rw [g2 .r12 (by decide), hE.r12],
      by rw [g2 .r13 (by decide), hE.r13], by rw [g2 .r15 (by decide), hE.r15], hpost2, htab2,
      fun i' hi' => by rw [ifn (Nat.not_lt_zero _)]; exact hacc2 i' hi'⟩) fun u hI => ?_)
  -- the term of `t̂`
  have hret : retR u = retR s₀ := by simp only [retR, hI.rsp]
  have hT := t_frame hp hI.frame hj
  have hX := hI.acc k (by omega)
  rw [ifn (Nat.lt_irrefl k)] at hX
  have usr : u.rd = [vR (aP s₀) (k * k), vR (tP s₀) k, vR (yP s₀) k] := by rw [hI.rd, hp.1]
  have usw : u.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hk31 : 1024 * k < 2 ^ 31 := by omega
  have hku : k < k + 1 := by omega
  refine WP.seq (WP.mono (prodAcc_ok hB hk31 (f := [.mov .rsi (.reg .r15)]) (C := cP s₀)
    (F := tP s₀ + BitVec.ofNat 64 (1024 * j)) hI.rbx (by rw [hI.rbp]) ?_ ?_ ?_
    ((dTC hp :).sub_left (sub_v _ hj)) ((dUC hp :).sub_left (sub_v _ hku))
    (((hp.2.2.2.1).sub_left (sub_v _ hku)).sub_right (sub_v _ hj))
    (by rw [hret]; exact (rT hp :).sub_right (sub_v _ hj)) (by rw [hret]; exact (rU hp :).sub_right (sub_v _ hku))
    (by rw [hret]; exact rC hp) hT.1 hI.yh.1 hI.tab hX) fun s4 ⟨hP4, hf4, hcs4, hrd4, hwr4⟩ => ?_)
  · vrunm [hI.rbx, hI.r15, hI.rbp, sx1024, sx_ofNat hk31]
    refine ⟨fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  · rw [usr, usw]
    exact (cov_one (by simp) (in_vec _ (by omega) hj)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_vec _ (by omega) hku)).cons
      ((cov_one (by simp) (in_c0 _)).cons ((cov_one (by simp) (in_c (by decide))).cons Covers.nil)))))
  · rw [usw]
    exact (cov_one (by simp) (in_vec _ (by omega) hku)).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_c (by decide))).cons Covers.nil))
  rw [hT.2, hI.yh.2, ← accE_succ_t hj] at hP4
  obtain ⟨fs, fhi, ftab, _, fu⟩ := prod_frame hp hk hku
  have hb4 : Base k s₀ s4 := hI.toBase.step hf4 fs fhi hrd4 hwr4 hcs4
  -- the next row of `Â`, `t̂[j]` and `y[j]`
  vrunm [hcs4 .r12 (by decide), hcs4 .r13 (by decide), hcs4 .r14 (by decide), hcs4 .r15 (by decide), hI.r12,
    hI.r13, hI.r14, hI.r15, sx1024, sx_ofNat hk31]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
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
    exact T.frame hf4 ftab hI.tab
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i = k
    · subst h; exact hP4
    · have := hI.acc i hi
      rw [ifp (by omega)] at this
      exact R.frame hf4 (fu i hi h) this

set_option linter.unusedSimpArgs false in
theorem invStep_ok {i : Nat} (hi : i < k + 1) {s : State} (hV : VInv R k s₀ i s) :
    WP isa (KpkeMul.invE B) s fun s' => VInv R k s₀ (i + 1) s' ∧ s'.gpr .r15 = s.gpr .r15 - 1 ∧
      s'.zf = some (s.gpr .r15 - 1 == 0) := by
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hsw : s.wr = [vR (uP s₀) (k + 1), cR (cP s₀)] := by rw [hV.wr, hp.2.1]
  have hX := hV.acc i (Nat.le_refl _) hi
  unfold KpkeMul.invE
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * i) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.mem = s.mem ∧ Keep [.rdi, .rsi] s s1) (by
        vrunm [hV.rbx, hV.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1di, h1si, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hV.rsp]
  have hX1 : R.is s1.mem (uP s₀ + BitVec.ofNat 64 (1024 * i)) (accE k s₀ k i) := by rw [hm1]; exact hX
  refine WP.seq (WP.inline (k := invAccK R) hB.inv (rd := [])
    (wr := [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.2.1)
  · simp only [invAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, hsp1, retR]
    exact ⟨trivial, trivial, (dUC hp :).sub_left (sub_v _ hi) |>.sub_right (sub_c0 _),
      (rU hp :).sub_right (sub_v _ hi), (rC hp :).sub_right (sub_c0 _), ⟨_, hX1⟩⟩
  · rw [k1.2.1, k1.2.2, hsw]
    exact Covers.right ((cov_one (by simp) (in_vec _ (by omega) hi)).cons ((cov_one (by simp) (in_c0 _)).cons
      Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_vec _ (by omega) hi)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [invAccK, State.withRegions_gpr, State.withRegions_mem, h1di] at hpost2
  have hP2 := hpost2 _ hX1
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
  have fo : ∀ {i'}, i' < k + 1 → i' ≠ i → ∀ r ∈ [pR (uP s₀ + BitVec.ofNat 64 (1024 * i)), pR (cP s₀)],
      (pR (uP s₀ + BitVec.ofNat 64 (1024 * i'))).Disjoint r := fun hi' h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [dUU hk hi' hi h, ((dUC hp :).sub_left (sub_v (uP s₀) hi')).sub_right (sub_c0 _)]
  vrunm [habi2.1 .rbp (by decide), habi2.1 .r15 (by decide), k1.gpr (r := .rbp) (by decide),
    k1.gpr (r := .r15) (by decide), sx1024]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun i' hi' => ?_, fun i' hi1 hi2 => ?_⟩
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
    · subst h; exact hP2
    · exact polyIs_frame hf2 (fo (by omega) h) (hV.done i' (by omega))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact R.frame hf2 (fo hi2 (by omega)) (hV.acc i' (by omega) hi2)

end

/-- The code inside the MXCSR region. -/
abbrev innerE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (KpkeMul.startE B k) (.seq (.loop (KpkeMul.termE B k) .ne)
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
variable {k : Nat} {s₀ : State} (hp : (encMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

theorem wp_all (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp] (innerE B k) = true) :
    WP isa (encryptMul B k) s₀ fun s' => gprPreserved s₀ s' ∧ (encMulK k).post s₀ s' := by
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
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
  · -- the table and the accumulators of zero, the loops
    have hb2 : Base k s₀ s2 := ⟨by rw [k2.gpr (by decide), h1bx], by rw [k2.gpr (by decide), h1sp],
      by rw [k2.2.1, h1rd], by rw [k2.2.2, h1wr],
      hf1.trans (f2.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩),
      hsv.frame f2 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega))⟩
    refine WP.seq (WP.mono (startE_ok hp hk hB (s := s2) hb2 (by rw [k2.gpr (by decide), h1bp]))
      fun s3 hz => ?_)
    have e3 : ∀ r ∈ calleeSaved, s3.gpr r = s1.gpr r := fun r hr => by
      rw [hz.cs r hr]; exact k2.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (EInv k s₀ R T)
      (fun j hj u hE _ => termE_ok hp hk hB hj hE) (fun u hE => ?_)
      ⟨hz.toBase, by rw [e3 .rbp (by decide), h1bp],
        by rw [e3 .r12 (by decide), h112, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero],
        by rw [e3 .r13 (by decide), h113, Nat.mul_zero, add_ofNat_zero],
        by rw [e3 .r15 (by decide), h115, Nat.mul_zero, add_ofNat_zero], hz.tab,
        fun i hi => by rw [accE_zero]; exact hz.acc i hi⟩
      (by rw [e3 .r14 (by decide), h114]))
    -- `NTT⁻¹` of each sum
    refine WP.seq (WP.mono (Q := fun (s6 : State) => s6.gpr .rbp = uP s₀ ∧
        s6.gpr .r15 = BitVec.ofNat 64 (k + 1) ∧ s6.mem = u.mem ∧ Keep [.rbp, .r15] u s6) (by
          vrunm [hE.rbp]
          refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
          · apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s6 ⟨h6bp, h615, hm6, k6⟩ => ?_)
    refine wp_countdown (cnt := .r15) (N := k + 1) (by omega) (by omega) (VInv R k s₀)
      (fun i hi u hV _ => invStep_ok hp hk hB hi hV) (fun u hV => ⟨hV.toBase, fun i hi => hV.done i hi⟩)
      ⟨⟨by rw [k6.gpr (by decide)]; exact hE.rbx, by rw [k6.gpr (by decide)]; exact hE.rsp,
        by rw [k6.2.1]; exact hE.rd, by rw [k6.2.2]; exact hE.wr, by rw [hm6]; exact hE.frame,
        by rw [hm6]; exact hE.saved⟩, by rw [h6bp, Nat.mul_zero, add_ofNat_zero],
        fun _ h => absurd h (Nat.not_lt_zero _), fun i _ hi => by rw [hm6]; exact hE.acc i hi⟩ h615
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
        exact ((dUC hp :).sub_left (sub_v _ hi)).sub_right (sub_c (by decide))) (hacc4 i hi)
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
