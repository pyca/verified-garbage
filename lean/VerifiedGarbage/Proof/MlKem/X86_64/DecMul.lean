module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeAcc
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.MlKem.KpkeMulContract
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem*_decrypt_mul`

`decryptMul B k` (`Impl/MlKem/X86_64/KpkeMul.lean`) inlines the code of a
backend `B`, whose pieces meet their contracts (`BodiesOk`, `KpkeAcc.lean`;
`WP.inline` runs them with the permissions they need), around an
accumulator at `w` in the backend's form `R`. The prologue saves the
callee-saved registers in `scratch` (`Spill`); `start` sets up the table
and the accumulator of zero (`start_ok`); after `j` iterations of the loop,
the accumulator holds the first `j` terms of the sum (`dotP`, `DInv`), each
`NTT(u'[j])` and its product with `ŝ[j]` added (`term_ok`); then `NTT⁻¹` of
the accumulator to `w`, and the epilogue loads the registers back.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Sums of products, a term at a time -/

/-- The first `j` terms of `dot a b`. -/
def dotP (a b : List Poly) (j : Nat) : Poly := ((List.zipWith multiplyNTTs a b).take j).foldl add zero

theorem dotP_zero (a b : List Poly) : dotP a b 0 = zero := by simp [dotP]

theorem dotP_succ {a b : List Poly} {j : Nat} (ha : j < a.length) (hb : j < b.length) :
    dotP a b (j + 1) = add (dotP a b j) (multiplyNTTs a[j]! b[j]!) := by
  have hz : j < (List.zipWith multiplyNTTs a b).length := by simp; omega
  rw [dotP, dotP, List.take_add_one, List.getElem?_eq_getElem hz, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getElem_zipWith, getElem!_pos a j ha, getElem!_pos b j hb]

theorem dotP_full {a b : List Poly} {k : Nat} (ha : a.length = k) (hb : b.length = k) : dotP a b k = dot a b := by
  rw [dotP, dot, List.take_of_length_le (by simp; omega)]

theorem vecAt_length (m : Mem) (p : Addr) (k : Nat) : (vecAt m p k).length = k := by simp [vecAt]

theorem vecAt_get (m : Mem) (p : Addr) {k j : Nat} (hj : j < k) :
    (vecAt m p k)[j]! = polyAt m (p + BitVec.ofNat 64 (1024 * j)) := by
  rw [getElem!_pos _ j (by rw [vecAt_length]; exact hj)]
  simp [vecAt]

theorem vecAt_map_get (m : Mem) (p : Addr) {k j : Nat} (hj : j < k) :
    ((vecAt m p k).map ntt)[j]! = ntt (polyAt m (p + BitVec.ofNat 64 (1024 * j))) := by
  rw [getElem!_pos _ j (by rw [List.length_map, vecAt_length]; exact hj), List.getElem_map,
    ← getElem!_pos _ j (by rw [vecAt_length]; exact hj), vecAt_get _ _ hj]

/-! ## The contract, and what it needs of a backend -/

/-- `k` polynomials, at `p`. -/
abbrev vR (p : Addr) (k : Nat) : Region := ⟨p, 1024 * k⟩

/-- `scratch` (4096 bytes), at `p`. -/
abbrev cR (p : Addr) : Region := ⟨p, 4096⟩

/-- `vg_mlkem*_decrypt_mul(w = rdi, s = rsi, u = rdx, scratch = rcx)` of rank `k`. -/
def decMulK (k : Nat) : Contract isa where
  pre s :=
    s.rd = [vR (s.gpr .rsi) k, vR (s.gpr .rdx) k] ∧ s.wr = [pR (s.gpr .rdi), cR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (vR (s.gpr .rsi) k) ∧ (pR (s.gpr .rdi)).Disjoint (vR (s.gpr .rdx) k) ∧
    (pR (s.gpr .rdi)).Disjoint (cR (s.gpr .rcx)) ∧ (vR (s.gpr .rsi) k).Disjoint (cR (s.gpr .rcx)) ∧
    (vR (s.gpr .rdx) k).Disjoint (cR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (vR (s.gpr .rsi) k) ∧
    (retR s).Disjoint (vR (s.gpr .rdx) k) ∧ (retR s).Disjoint (cR (s.gpr .rcx)) ∧
    VecReduced s.mem (s.gpr .rsi) k ∧ VecReduced s.mem (s.gpr .rdx) k
  post s s' :=
    PolyIs s'.mem (s.gpr .rdi) (nttInv (dot (vecAt s.mem (s.gpr .rsi) k) ((vecAt s.mem (s.gpr .rdx) k).map ntt)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace DecMul

/-! ## Regions -/

theorem sub_c {C : Addr} {o n : Nat} (h : o + n ≤ 4096) : Region.Sub ⟨C + BitVec.ofNat 64 o, n⟩ (cR C) :=
  Offset.sub_base C h

theorem sub_c0 (C : Addr) : Region.Sub (pR C) (cR C) := Region.sub_prefix (by decide)

theorem sub_v (p : Addr) {k j : Nat} (hj : j < k) : Region.Sub (pR (p + BitVec.ofNat 64 (1024 * j))) (vR p k) :=
  Offset.sub_base p (by have := Nat.mul_le_mul_left 1024 (show j + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega)

theorem in_c {C : Addr} {o n : Nat} (h : o + n ≤ 4096) : (cR C).Contains (C + BitVec.ofNat 64 o) n :=
  Offset.contains_base C h (by omega)

theorem in_c0 (C : Addr) : (cR C).Contains C 1024 := by
  simpa using in_c (C := C) (o := 0) (n := 1024) (by decide)

theorem in_v (p : Addr) {k j : Nat} (hk : k ≤ 4) (hj : j < k) :
    (vR p k).Contains (p + BitVec.ofNat 64 (1024 * j)) 1024 :=
  Offset.contains_base p (by have := Nat.mul_le_mul_left 1024 (show j + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega)
    (by omega)

/-- Two of the polynomials at `C`, `C + 1024` and `C + 2048` are disjoint. -/
theorem dis_cc {C : Addr} {o e : Nat} (h : o + 1024 ≤ e ∨ e + 1024 ≤ o) (ho : o ≤ 2048) (he : e ≤ 2048) :
    (pR (C + BitVec.ofNat 64 o)).Disjoint (pR (C + BitVec.ofNat 64 e)) :=
  Offset.disjoint C h (by omega) (by omega)

/-! ## The loop -/

section
variable (k : Nat) (s₀ : State)

abbrev wP : Addr := s₀.gpr .rdi
abbrev sP : Addr := s₀.gpr .rsi
abbrev uP : Addr := s₀.gpr .rdx
abbrev cP : Addr := s₀.gpr .rcx
abbrev sv : List Poly := vecAt s₀.mem (sP s₀) k
abbrev uv : List Poly := (vecAt s₀.mem (uP s₀) k).map ntt

/-- After `j` terms, with the accumulator in the form `R` and the table `T`. -/
structure DInv (R : AccRep) (T : TabRep) (j : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = cP s₀
  rbp : s.gpr .rbp = wP s₀
  r12 : s.gpr .r12 = sP s₀ + BitVec.ofNat 64 (1024 * j)
  r13 : s.gpr .r13 = uP s₀ + BitVec.ofNat 64 (1024 * j)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s.mem
  saved : Spill.Saved s.mem (cP s₀) s₀.gpr KpkeMul.slots
  tab : T.is s.mem (cP s₀)
  acc : R.is s.mem (wP s₀) (dotP (sv k s₀) (uv k s₀) j)

end

section
variable {k : Nat} {s₀ : State} (hp : (decMulK k).pre s₀)
include hp

theorem dis_wc {o n : Nat} (h : o + n ≤ 4096) : (pR (wP s₀)).Disjoint ⟨cP s₀ + BitVec.ofNat 64 o, n⟩ :=
  hp.2.2.2.2.1.sub_right (sub_c h)

theorem dis_wc0 : (pR (wP s₀)).Disjoint (pR (cP s₀)) := hp.2.2.2.2.1.sub_right (sub_c0 _)

theorem dis_sc {j o n : Nat} (hj : j < k) (h : o + n ≤ 4096) :
    (pR (sP s₀ + BitVec.ofNat 64 (1024 * j))).Disjoint ⟨cP s₀ + BitVec.ofNat 64 o, n⟩ :=
  (hp.2.2.2.2.2.1.sub_left (sub_v _ hj)).sub_right (sub_c h)

theorem dis_uc {j o n : Nat} (hj : j < k) (h : o + n ≤ 4096) :
    (pR (uP s₀ + BitVec.ofNat 64 (1024 * j))).Disjoint ⟨cP s₀ + BitVec.ofNat 64 o, n⟩ :=
  (hp.2.2.2.2.2.2.1.sub_left (sub_v _ hj)).sub_right (sub_c h)

theorem dis_sc0 {j : Nat} (hj : j < k) : (pR (sP s₀ + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (cP s₀)) :=
  (hp.2.2.2.2.2.1.sub_left (sub_v _ hj)).sub_right (sub_c0 _)

theorem dis_uc0 {j : Nat} (hj : j < k) : (pR (uP s₀ + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (cP s₀)) :=
  (hp.2.2.2.2.2.2.1.sub_left (sub_v _ hj)).sub_right (sub_c0 _)

theorem dis_sw {j : Nat} (hj : j < k) : (pR (sP s₀ + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (wP s₀)) :=
  (hp.2.2.1.sub_right (sub_v _ hj)).symm

theorem dis_uw {j : Nat} (hj : j < k) : (pR (uP s₀ + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (wP s₀)) :=
  (hp.2.2.2.1.sub_right (sub_v _ hj)).symm

theorem ret_c {o n : Nat} (h : o + n ≤ 4096) : (retR s₀).Disjoint ⟨cP s₀ + BitVec.ofNat 64 o, n⟩ :=
  hp.2.2.2.2.2.2.2.2.2.2.1.sub_right (sub_c h)

theorem ret_c0 : (retR s₀).Disjoint (pR (cP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.1.sub_right (sub_c0 _)

theorem ret_s {j : Nat} (hj : j < k) : (retR s₀).Disjoint (pR (sP s₀ + BitVec.ofNat 64 (1024 * j))) :=
  hp.2.2.2.2.2.2.2.2.1.sub_right (sub_v _ hj)

theorem ret_u {j : Nat} (hj : j < k) : (retR s₀).Disjoint (pR (uP s₀ + BitVec.ofNat 64 (1024 * j))) :=
  hp.2.2.2.2.2.2.2.2.2.1.sub_right (sub_v _ hj)

/-- A polynomial of `s` or `u`, as at the start, in any memory that differs
only in `w` and `scratch`. -/
theorem s_frame {m : Mem} (hf : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem m) {j : Nat} (hj : j < k) :
    PolyIs m (sP s₀ + BitVec.ofNat 64 (1024 * j)) ((sv k s₀)[j]!) := by
  rw [vecAt_get _ _ hj]
  refine polyIs_frame hf (fun r hr => ?_) ⟨hp.2.2.2.2.2.2.2.2.2.2.2.1 j hj, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact dis_sw hp hj
  · exact hp.2.2.2.2.2.1.sub_left (sub_v _ hj)

theorem u_frame {m : Mem} (hf : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem m) {j : Nat} (hj : j < k) :
    PolyIs m (uP s₀ + BitVec.ofNat 64 (1024 * j)) (polyAt s₀.mem (uP s₀ + BitVec.ofNat 64 (1024 * j))) := by
  refine polyIs_frame hf (fun r hr => ?_) ⟨hp.2.2.2.2.2.2.2.2.2.2.2.2 j hj, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact dis_uw hp hj
  · exact hp.2.2.2.2.2.2.1.sub_left (sub_v _ hj)

end

theorem sx1024 : BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 := by decide
theorem sx2048 : BitVec.signExtend 64 (2048 : BitVec 32) = BitVec.ofNat 64 2048 := by decide

theorem slots_bound : ∀ p ∈ KpkeMul.slots, 3072 ≤ p.2 ∧ p.2 + 8 ≤ 3120 := by decide

/-- The saved registers stay in their slots across writes that miss them. -/
theorem saved_keep {m m' : Mem} {C : Addr} {g : Reg → BitVec 64} (h : Spill.Saved m C g KpkeMul.slots)
    {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∀ d, 3072 ≤ d → d + 8 ≤ 3120 → Region.Disjoint ⟨C + BitVec.ofNat 64 d, 8⟩ r) :
    Spill.Saved m' C g KpkeMul.slots :=
  h.frame hf fun p hp r hr => hd r hr p.2 (slots_bound p hp).1 (slots_bound p hp).2

theorem slot_dis_c {C : Addr} {d o : Nat} (h3 : 3072 ≤ d) (h8 : d + 8 ≤ 3120) (ho : o ≤ 2048) :
    Region.Disjoint ⟨C + BitVec.ofNat 64 d, 8⟩ (pR (C + BitVec.ofNat 64 o)) :=
  Offset.disjoint C (.inr (by omega)) (by omega) (by omega)

theorem slot_dis_c0 {C : Addr} {d : Nat} (h3 : 3072 ≤ d) (h8 : d + 8 ≤ 3120) :
    Region.Disjoint ⟨C + BitVec.ofNat 64 d, 8⟩ (pR C) :=
  Offset.disjoint_base C (by omega) (by omega)

/-- Covering the regions a piece of code is given. -/
theorem cov_one {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat} (hc : R.Contains a n) :
    Covers [⟨a, n⟩] rs := Covers.one ⟨R, hR, hc⟩

/-- The code inside the MXCSR region. -/
abbrev inner (B : Bodies) : Prog isa :=
  .seq (KpkeMul.start B) (.seq (.loop (KpkeMul.term B) .ne) (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)]) B.inv))

theorem save_eq : KpkeMul.save = Spill.saveCode .rcx KpkeMul.slots := rfl

theorem restore_eq : KpkeMul.restore = Spill.restoreCode .rbx KpkeMul.slots := rfl

theorem sx3328 : BitVec.signExtend 64 (BitVec.ofNat 32 3328) = BitVec.ofNat 64 3328 := by decide

theorem slot_dis_tab {C : Addr} {d : Nat} (h3 : 3072 ≤ d) (h8 : d + 8 ≤ 3120) :
    Region.Disjoint ⟨C + BitVec.ofNat 64 d, 8⟩ (tabR C) :=
  Offset.disjoint C (.inl (by omega)) (by omega) (by omega)

/-- The regions in `scratch` of the products: none overlaps another. -/
theorem prod_dis (C : Addr) :
    (pR (C + BitVec.ofNat 64 1024)).Disjoint (pR C) ∧ (pR (C + BitVec.ofNat 64 1024)).Disjoint (tmpR C) ∧
    (pR C).Disjoint (tmpR C) ∧ (pR C).Disjoint (tabR C) ∧ (tmpR C).Disjoint (tabR C) :=
  ⟨Offset.disjoint_base _ (by decide) (by decide), Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
    Offset.base_disjoint _ (by decide) (by decide), Offset.base_disjoint _ (by decide) (by decide),
    Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)⟩

section
variable {k : Nat} {s₀ : State} (hp : (decMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

set_option linter.unusedSimpArgs false in
/-- A term of the sum: `NTT(u'[j])`, and its product with `ŝ[j]` added to the accumulator. -/
theorem term_ok {j : Nat} (hj : j < k) {s : State} (hI : DInv k s₀ R T j s) :
    WP isa (KpkeMul.term B) s fun s' => DInv k s₀ R T (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hsr : s.rd = [vR (sP s₀) k, vR (uP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [pR (wP s₀), cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have hS := s_frame hp hI.frame hj
  have hU := u_frame hp hI.frame hj
  unfold KpkeMul.term
  -- `NTT(u'[j])` to `scratch + 1024`
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = uP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = cP s₀ + BitVec.ofNat 64 1024 ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hI.r13, hI.rbx, sx1024]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.seq (WP.inline (k := nttOK) hB.nttO (rd := [pR (uP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (cP s₀ + BitVec.ofNat 64 1024), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, dis_uc0 hp hj, Offset.disjoint_base _ (by decide) (by decide),
      ret_c hp (o := 1024) (n := 1024) (by decide), ret_c0 hp, hU.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_v _ hk hj)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttOK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1] at hpost2
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by
    rw [habi2.1 r hr, cs (by decide) k1 r hr]
  rw [hm1] at hf2
  have hf2' : Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s2.mem := hI.frame.trans (by
    refine hf2.sub fun r hr => ⟨cR (cP s₀), by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [sub_c (by decide), sub_c0 _])
  have pd := prod_dis (cP s₀)
  -- its product with `ŝ[j]`, added to the accumulator
  refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = wP s₀ ∧
      s3.gpr .rsi = sP s₀ + BitVec.ofNat 64 (1024 * j) ∧ s3.gpr .rdx = cP s₀ + BitVec.ofNat 64 1024 ∧
      s3.gpr .rcx = cP s₀ ∧ s3.mem = s2.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] s2 s3) (by
        vrunm [g2 .rbx (by decide), g2 .r12 (by decide), g2 .rbp (by decide), hI.rbx, hI.r12, hI.rbp, sx1024]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, h3dx, h3cx, hm3, k3⟩ => ?_)
  have g3 : ∀ r ∈ calleeSaved, s3.gpr r = s.gpr r := fun r hr => by rw [cs (by decide) k3 r hr, g2 r hr]
  have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [g3 .rsp (by decide), hI.rsp]
  have hbx3 : s3.gpr .rbx = cP s₀ := by rw [g3 .rbx (by decide), hI.rbx]
  have hS3 : PolyIs s3.mem (sP s₀ + BitVec.ofNat 64 (1024 * j)) ((sv k s₀)[j]!) := by
    rw [hm3]; exact s_frame hp hf2' hj
  have hT3 : PolyIs s3.mem (cP s₀ + BitVec.ofNat 64 1024) (ntt (polyAt s₀.mem (uP s₀ + BitVec.ofNat 64 (1024 * j)))) := by
    rw [hm3, ← hU.2]; exact hpost2
  have hTab3 : T.is s3.mem (cP s₀) := by
    rw [hm3]
    refine T.frame hf2 (fun r hr => ?_) hI.tab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [Offset.disjoint _ (.inr (by decide)) (by decide) (by decide), pd.2.2.2.1.symm]
  have hAcc3 : R.is s3.mem (wP s₀) (dotP (sv k s₀) (uv k s₀) j) := by
    rw [hm3]
    refine R.frame hf2 (fun r hr => ?_) hI.acc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [dis_wc hp (by decide), dis_wc0 hp]
  have hbp3 : s3.gpr .rbp = wP s₀ := by rw [g3 .rbp (by decide), hI.rbp]
  refine WP.seq (WP.inline (k := mulAccK R T 0) (hB.mulAcc 0 (by decide))
    (rd := [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀ + BitVec.ofNat 64 1024), tabR (cP s₀)])
    (wr := [pR (wP s₀), pR (cP s₀), tmpR (cP s₀)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) (hB.nc.2.2.2 0))
  · simp only [mulAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, h3dx, h3cx, hsp3, hbx3, hbp3, retR]
    exact ⟨trivial, trivial, (dis_sw hp hj).symm, dis_wc hp (by decide), dis_wc0 hp, dis_wc hp (by decide),
      dis_wc hp (by decide), dis_sc0 hp hj, dis_sc hp hj (by decide), pd.1, pd.2.1, pd.2.2.1, pd.2.2.2.1,
      pd.2.2.2.2, hp.2.2.2.2.2.2.2.1, ret_s hp hj, ret_c hp (o := 1024) (n := 1024) (by decide), ret_c0 hp,
      ret_c hp (o := 2048) (n := 1024) (by decide), ret_c hp (o := 3328) (n := 256) (by decide), trivial,
      by rw [Nat.mul_zero, add_ofNat_zero], hS3.1, hT3.1, hTab3, ⟨_, hAcc3⟩⟩
  · rw [k3.2.1, k3.2.2, hrd2, hwr2, k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_v _ hk hj)).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (Region.contains_self _ _)).cons
      ((cov_one (by simp) (in_c0 _)).cons ((cov_one (by simp) (in_c (by decide))).cons Covers.nil)))))
  · rw [k3.2.2, hwr2, k1.2.2, hsw]
    exact (cov_one (by simp) (Region.contains_self _ _)).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_c (by decide))).cons Covers.nil))
  simp only [mulAccK, State.withRegions_gpr, State.withRegions_mem, h3di, h3si, h3dx] at hpost4
  rw [hS3.2, hT3.2] at hpost4
  have hA4 := hpost4 _ hAcc3
  have g4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [habi4.1 r hr, g3 r hr]
  rw [hm3] at hf4
  -- the next term
  vrunm [g4 .r12 (by decide), g4 .r13 (by decide), g4 .r14 (by decide), sx1024]
  have hsv : j < (sv k s₀).length := by rw [vecAt_length]; exact hj
  have huv : j < (uv k s₀).length := by rw [List.length_map, vecAt_length]; exact hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .rbx (by decide), hI.rbx]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .rbp (by decide), hI.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [hI.r12, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [hI.r13, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .rsp (by decide), hI.rsp]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]
    rw [hrd4, k3.2.1, hrd2, k1.2.1, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]
    rw [hwr4, k3.2.2, hwr2, k1.2.2, hI.wr]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine hf2'.trans (hf4.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨_, by simp, fun _ h => h⟩, ⟨_, by simp, sub_c0 _⟩, ⟨_, by simp, sub_c (by decide)⟩]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine saved_keep (saved_keep hI.saved hf2 ?_) hf4 ?_ <;>
      intro r hr d h3 h8 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      exacts [slot_dis_c h3 h8 (by decide), slot_dis_c0 h3 h8]
    · rcases hr with rfl | rfl | rfl
      exacts [(dis_wc hp (o := d) (n := 8) (by omega)).symm, slot_dis_c0 h3 h8, slot_dis_c h3 h8 (by decide)]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine T.frame hf4 (fun r hr => ?_) (by rw [← hm3]; exact hTab3)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [(dis_wc hp (by decide)).symm, pd.2.2.2.1.symm, pd.2.2.2.2.symm]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [dotP_succ hsv huv, vecAt_map_get _ _ hj]
    exact hA4

omit hk in
/-- After the loop: `NTT⁻¹` of the sum to `w`. -/
theorem fin_ok {s : State} (hI : DInv k s₀ R T k s) :
    WP isa (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)]) B.inv) s fun s' =>
      s'.gpr .rbx = cP s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [pR (wP s₀), cR (cP s₀)] s₀.mem s'.mem ∧ Spill.Saved s'.mem (cP s₀) s₀.gpr KpkeMul.slots ∧
      PolyIs s'.mem (wP s₀) (nttInv (dot (sv k s₀) (uv k s₀))) := by
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = wP s₀ ∧ s1.gpr .rsi = cP s₀ ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi] s s1) (by
        vrunm [hI.rbx, hI.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1di, h1si, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  have hsw : s1.wr = [pR (wP s₀), cR (cP s₀)] := by rw [k1.2.2, hI.wr, hp.2.1]
  have hA1 : R.is s1.mem (wP s₀) (dotP (sv k s₀) (uv k s₀) k) := by rw [hm1]; exact hI.acc
  refine WP.inline (k := invAccK R) hB.inv (rd := []) (wr := [pR (wP s₀), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.2.1
  · simp only [invAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, hsp1, retR]
    exact ⟨trivial, trivial, dis_wc0 hp, hp.2.2.2.2.2.2.2.1, ret_c0 hp, ⟨_, hA1⟩⟩
  · rw [hsw]
    exact Covers.right ((cov_one (by simp) (Region.contains_self _ _)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [hsw]
    exact (cov_one (by simp) (Region.contains_self _ _)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [invAccK, State.withRegions_gpr, State.withRegions_mem, h1di] at hpost2
  rw [hm1] at hf2
  refine ⟨by rw [habi2.1 .rbx (by decide), k1.gpr (by decide), hI.rbx],
    by rw [habi2.1 .rsp (by decide), hsp1], by rw [hrd2, k1.2.1, hI.rd], by rw [hwr2, k1.2.2, hI.wr],
    hI.frame.trans (hf2.sub fun r hr => ?_), saved_keep hI.saved hf2 ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨_, by simp, fun _ h => h⟩, ⟨_, by simp, sub_c0 _⟩]
  · intro r hr d h3 h8
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(dis_wc hp (o := d) (n := 8) (by omega)).symm, slot_dis_c0 h3 h8]
  · rw [← dotP_full (vecAt_length _ _ _) (by rw [List.length_map, vecAt_length])]
    exact hpost2 _ hA1

omit hk in
/-- The table, and the accumulator of zero. -/
theorem start_ok {s : State} (hbx : s.gpr .rbx = cP s₀) (hbp : s.gpr .rbp = wP s₀) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hwr : s.wr = s₀.wr) :
    WP isa (KpkeMul.start B) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [pR (wP s₀), tabR (cP s₀)] s.mem s'.mem ∧ T.is s'.mem (cP s₀) ∧
      R.is s'.mem (wP s₀) zero := by
  unfold KpkeMul.start
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧ Keep [.rcx] s s1) (by
      vrunm [hbx]
      refine ⟨fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1cx, hm1, k1⟩ => ?_
  rw [WP.block_append_iff]
  have hin : InRegions s1.wr (s1.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
    rw [k1.2.2, hwr, hp.2.1, h1cx]; exact ⟨cR (cP s₀), by simp, in_c (by decide)⟩
  refine WP.mono (hB.tab s1 hin) fun s2 ⟨hT2, hf2, k2⟩ => ?_
  rw [h1cx] at hT2 hf2
  refine WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = wP s₀ ∧ s3.mem = s2.mem ∧ Keep [.rdi] s2 s3) (by
      vrunm [k2.gpr (by decide : Reg.rbp ∉ [Reg.r9, .r10]), k1.gpr (by decide : Reg.rbp ∉ [Reg.rcx]), hbp]
      refine ⟨fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3di, hm3, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [k13.gpr (by decide), hsp]
  refine WP.inline (k := zeroK R) hB.zero (rd := []) (wr := [pR (wP s₀)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) hB.nc.2.2.1
  · simp only [zeroK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h3di, hsp3, retR]
    exact ⟨trivial, trivial, hp.2.2.2.2.2.2.2.1⟩
  · rw [k13.2.1, k13.2.2, hwr, hp.2.1]
    exact Covers.right ((cov_one (by simp) (Region.contains_self _ _)).cons Covers.nil)
  · rw [k13.2.2, hwr, hp.2.1]
    exact (cov_one (by simp) (Region.contains_self _ _)).cons Covers.nil
  simp only [zeroK, State.withRegions_gpr, State.withRegions_mem, h3di] at hpost4
  rw [hm3] at hf4
  refine ⟨fun r hr => by rw [habi4.1 r hr, k13.gpr (fun h => by simp at h; rcases h with rfl | rfl | rfl | rfl <;>
      simp [calleeSaved] at hr)], by rw [hrd4, k13.2.1], by rw [hwr4, k13.2.2], ?_, ?_, hpost4⟩
  · rw [← hm1]
    exact (hf2.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩).trans
      (hf4.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
  · refine T.frame hf4 (fun r hr => ?_) hT2
    simp only [List.mem_singleton] at hr; subst hr
    exact (dis_wc hp (by decide)).symm

/-- The function but for the restore of the callee-saved registers, inline. -/
theorem body_ok (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (inner B) = true) :
    WP isa (.seq (.block (KpkeMul.save ++ ([.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi),
      .mov .r13 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))] : List Instr)))
      (withMxcsr .rbx oMx (inner B))) s₀ fun s5 => s5.gpr .rbx = cP s₀ ∧ s5.gpr .rsp = s₀.gpr .rsp ∧
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
  · -- the table and the accumulator of zero, the loop, `NTT⁻¹`
    refine WP.seq (WP.mono (start_ok hp hB (s := s2) (by rw [k2.gpr (by decide), h1bx])
      (by rw [k2.gpr (by decide), h1bp]) (by rw [k2.gpr (by decide), h1sp]) (by rw [k2.2.2, h1wr])) fun s3 ⟨g3, hrd3, hwr3, hf3, hT3, hz⟩ => ?_)
    have e3 : ∀ r ∈ calleeSaved, s3.gpr r = s1.gpr r := fun r hr => by
      rw [g3 r hr]; exact k2.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (DInv k s₀ R T)
      (fun j hj u hI _ => term_ok hp hk hB hj hI) (fun u hI => fin_ok hp hB hI) ?_
      (by rw [e3 .r14 (by decide), h114]))
    have hsv : Spill.Saved (Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (cP s₀) s₀.gpr KpkeMul.slots :=
      Spill.saveMem_saved _ _ _ _ (by decide)
    rw [← hm1] at hsv
    refine ⟨by rw [e3 .rbx (by decide), h1bx], by rw [e3 .rbp (by decide), h1bp],
      by rw [e3 .r12 (by decide), h112, Nat.mul_zero, add_ofNat_zero],
      by rw [e3 .r13 (by decide), h113, Nat.mul_zero, add_ofNat_zero], by rw [e3 .rsp (by decide), h1sp],
      by rw [hrd3, k2.2.1, h1rd], by rw [hwr3, k2.2.2, h1wr], ?_, ?_, hT3, by rw [dotP_zero]; exact hz⟩
    · refine (Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots
        (L := 4096) (fun p hp' => by have := slots_bound p hp'; omega) (by decide)).sub
        (fun r hr => ⟨_, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩) |>.trans ?_
      rw [← hm1]
      refine (f2.sub fun r hr => ⟨cR (cP s₀), by simp, ?_⟩).trans
        (hf3.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact sub_c (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [⟨_, by simp, fun _ h => h⟩, ⟨_, by simp, sub_c (by decide)⟩]
    · refine saved_keep (saved_keep hsv f2 ?_) hf3 ?_ <;> intro r hr d h3 h8
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [(dis_wc hp (o := d) (n := 8) (by omega)).symm, slot_dis_tab h3 h8]
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
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (inner B) = true) :
    WP isa (decryptMul B k) s₀ fun s' => gprPreserved s₀ s' ∧ (decMulK k).post s₀ s' := by
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  unfold decryptMul
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
  · -- the table and the accumulator of zero, the loop, `NTT⁻¹`
    refine WP.seq (WP.mono (start_ok hp hB (s := s2) (by rw [k2.gpr (by decide), h1bx])
      (by rw [k2.gpr (by decide), h1bp]) (by rw [k2.gpr (by decide), h1sp]) (by rw [k2.2.2, h1wr])) fun s3 ⟨g3, hrd3, hwr3, hf3, hT3, hz⟩ => ?_)
    have e3 : ∀ r ∈ calleeSaved, s3.gpr r = s1.gpr r := fun r hr => by
      rw [g3 r hr]; exact k2.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (DInv k s₀ R T)
      (fun j hj u hI _ => term_ok hp hk hB hj hI) (fun u hI => fin_ok hp hB hI) ?_
      (by rw [e3 .r14 (by decide), h114]))
    have hsv : Spill.Saved (Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (cP s₀) s₀.gpr KpkeMul.slots :=
      Spill.saveMem_saved _ _ _ _ (by decide)
    rw [← hm1] at hsv
    refine ⟨by rw [e3 .rbx (by decide), h1bx], by rw [e3 .rbp (by decide), h1bp],
      by rw [e3 .r12 (by decide), h112, Nat.mul_zero, add_ofNat_zero],
      by rw [e3 .r13 (by decide), h113, Nat.mul_zero, add_ofNat_zero], by rw [e3 .rsp (by decide), h1sp],
      by rw [hrd3, k2.2.1, h1rd], by rw [hwr3, k2.2.2, h1wr], ?_, ?_, hT3, by rw [dotP_zero]; exact hz⟩
    · refine (Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots
        (L := 4096) (fun p hp' => by have := slots_bound p hp'; omega) (by decide)).sub
        (fun r hr => ⟨_, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩) |>.trans ?_
      rw [← hm1]
      refine (f2.sub fun r hr => ⟨cR (cP s₀), by simp, ?_⟩).trans
        (hf3.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact sub_c (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [⟨_, by simp, fun _ h => h⟩, ⟨_, by simp, sub_c (by decide)⟩]
    · refine saved_keep (saved_keep hsv f2 ?_) hf3 ?_ <;> intro r hr d h3 h8
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [(dis_wc hp (o := d) (n := 8) (by omega)).symm, slot_dis_tab h3 h8]
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

end DecMul

end VG.Proof.MlKem.X86_64
