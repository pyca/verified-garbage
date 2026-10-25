module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncMul
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem*_keygen_mul`

`keygenMul B k` (`Impl/MlKem/X86_64/KpkeMul.lean`), as `encryptMul`
(`EncMul.lean`): the prologue saves the callee-saved registers in `scratch`
and keeps the pointers in registers; after `j` iterations of the first loop,
`s[0], …, s[j - 1]` hold `ŝ = NTT(s)` and `t[0], …, t[j - 1]` hold `NTT(e)`
(`NInv`, `nttStep_ok`); `midK` sets up the table of the products; after `i`
iterations of the second loop, `t[0], …, t[i - 1]` hold `t̂` (`RInv`): an
iteration sums the products `Â[i, j] ×_T ŝ[j]` in the accumulator at
`scratch + 1024` (`prodStep_ok`, unrolled), and adds the sum to `t[i]`
(`rowStep_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open DecMul (sub_c sub_c0 sub_v in_c in_c0 in_v dis_cc cov_one sx1024 sx2048)
open EncMul (hiR hi_dis_c hi_dis_c0 hi_dis_tab sub_hi in_vec)

/-- `vg_mlkem*_keygen_mul(t = rdi, s = rsi, a = rdx, e = rcx, scratch = r8)` of rank `k`, with
`Â` stored at `a` in the region `aR a`, reduced as `aRed` says, as the matrix `aMat`, and `e`
stored at `e` in the region `eR e`, reduced as `eRed` says, as the vector `eVec`. -/
def kgMulKG (k : Nat) (aR : Addr → Region) (aRed : Mem → Addr → Prop) (aMat : Mem → Addr → List (List Poly))
    (eR : Addr → Region) (eRed : Mem → Addr → Prop) (eVec : Mem → Addr → List Poly) : Contract isa where
  pre s :=
    s.rd = [aR (s.gpr .rdx), eR (s.gpr .rcx)] ∧
    s.wr = [vR (s.gpr .rdi) k, vR (s.gpr .rsi) k, cR (s.gpr .r8)] ∧
    (vR (s.gpr .rdi) k).Disjoint (vR (s.gpr .rsi) k) ∧
    (vR (s.gpr .rdi) k).Disjoint (aR (s.gpr .rdx)) ∧
    (vR (s.gpr .rdi) k).Disjoint (eR (s.gpr .rcx)) ∧
    (vR (s.gpr .rdi) k).Disjoint (cR (s.gpr .r8)) ∧
    (vR (s.gpr .rsi) k).Disjoint (aR (s.gpr .rdx)) ∧
    (vR (s.gpr .rsi) k).Disjoint (eR (s.gpr .rcx)) ∧
    (vR (s.gpr .rsi) k).Disjoint (cR (s.gpr .r8)) ∧
    (aR (s.gpr .rdx)).Disjoint (cR (s.gpr .r8)) ∧ (eR (s.gpr .rcx)).Disjoint (cR (s.gpr .r8)) ∧
    (retR s).Disjoint (vR (s.gpr .rdi) k) ∧ (retR s).Disjoint (vR (s.gpr .rsi) k) ∧
    (retR s).Disjoint (aR (s.gpr .rdx)) ∧ (retR s).Disjoint (eR (s.gpr .rcx)) ∧
    (retR s).Disjoint (cR (s.gpr .r8)) ∧
    VecReduced s.mem (s.gpr .rsi) k ∧ aRed s.mem (s.gpr .rdx) ∧ eRed s.mem (s.gpr .rcx)
  post s s' :=
    VecIs s'.mem (s.gpr .rsi) k ((vecAt s.mem (s.gpr .rsi) k).map ntt) ∧
    VecIs s'.mem (s.gpr .rdi) k (addVec (mulMatVec (aMat s.mem (s.gpr .rdx)) ((vecAt s.mem (s.gpr .rsi) k).map ntt))
      ((eVec s.mem (s.gpr .rcx)).map ntt))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `kgMulKG` with `e` as `k` polynomials of `u32`s. -/
abbrev kgMulKA (k : Nat) (aR : Addr → Region) (aRed : Mem → Addr → Prop) (aMat : Mem → Addr → List (List Poly)) :
    Contract isa :=
  kgMulKG k aR aRed aMat (fun p => vR p k) (fun m p => VecReduced m p k) (fun m p => vecAt m p k)

/-- `kgMulKA` with `Â` as `k²` polynomials of `u32`s. -/
abbrev kgMulK (k : Nat) : Contract isa :=
  kgMulKA k (fun p => vR p (k * k)) (fun m p => VecReduced m p (k * k)) (fun m p => matAt m p k)

/-- `kgMulKG` with `Â` as `k²` polynomials of `u16`s and `e` as `k`. -/
abbrev kgMulK16 (k : Nat) : Contract isa :=
  kgMulKG k (fun p => ⟨p, 512 * (k * k)⟩) (fun m p => VecReducedW 16 m p (k * k)) (fun m p => matAtW 16 m p k)
    (fun p => ⟨p, 512 * k⟩) (fun m p => VecReducedW 16 m p k) (fun m p => vecAtW 16 m p k)

namespace KgMul

theorem add_comm_poly (f g : Poly) : add f g = add g f :=
  ext_getElem! fun i hi => by
    rw [add_get _ _ hi, add_get _ _ hi]; exact Fin.ext (by rw [val_add', val_add', Nat.add_comm])

section
variable (k : Nat) (s₀ : State)

abbrev tP : Addr := s₀.gpr .rdi
abbrev sP : Addr := s₀.gpr .rsi
abbrev aP : Addr := s₀.gpr .rdx
abbrev eP : Addr := s₀.gpr .rcx
abbrev cP : Addr := s₀.gpr .r8
abbrev sv : List Poly := (vecAt s₀.mem (sP s₀) k).map ntt
abbrev ev : List Poly := (vecAt s₀.mem (eP s₀) k).map ntt
/-- `ê` of `e` as `u16`s. -/
abbrev ev16 : List Poly := (vecAtW 16 s₀.mem (eP s₀) k).map ntt
/-- Row `i` of `Â`. -/
abbrev rowA (i : Nat) : List Poly := vecAt s₀.mem (aP s₀ + BitVec.ofNat 64 (1024 * (k * i))) k
/-- Entry `i` of `t̂`, with the rows `rA` of `Â` and `ê = Ev`. -/
abbrev tgtG (Ev : List Poly) (rA : Nat → List Poly) (i : Nat) : Poly := add (dot (rA i) (sv k s₀)) (Ev[i]!)
/-- Entry `i` of `t̂`. -/
abbrev tgt (i : Nat) : Poly := tgtG k s₀ (ev k s₀) (rowA k s₀) i

/-- What the loops keep. -/
structure Base (s : State) : Prop where
  rbx : s.gpr .rbx = cP s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem s.mem
  saved : Spill.Saved s.mem (cP s₀) s₀.gpr KpkeMul.slots

/-- After `j` iterations of the first loop, with `ê = Ev` and `e`'s
polynomials `se` bytes apart. -/
structure NInv (Ev : List Poly) (se j : Nat) (s : State) : Prop extends Base k s₀ s where
  r12 : s.gpr .r12 = sP s₀ + BitVec.ofNat 64 (1024 * j)
  r15 : s.gpr .r15 = eP s₀ + BitVec.ofNat 64 (se * j)
  rbp : s.gpr .rbp = tP s₀ + BitVec.ofNat 64 (1024 * j)
  r13 : s.gpr .r13 = aP s₀
  sdone : ∀ j' < j, PolyIs s.mem (sP s₀ + BitVec.ofNat 64 (1024 * j')) ((sv k s₀)[j']!)
  srest : ∀ j', j ≤ j' → j' < k →
    PolyIs s.mem (sP s₀ + BitVec.ofNat 64 (1024 * j')) (polyAt s₀.mem (sP s₀ + BitVec.ofNat 64 (1024 * j')))
  tdone : ∀ j' < j, PolyIs s.mem (tP s₀ + BitVec.ofNat 64 (1024 * j')) (Ev[j']!)

/-- After `i` iterations of the second loop, with `ê = Ev` and the rows `rA`
of `Â`, `ra` bytes between their polynomials. -/
structure RInvG (Ev : List Poly) (ra : Nat) (rA : Nat → List Poly) (R : AccRep) (T : TabRep) (i : Nat) (s : State) :
    Prop extends Base k s₀ s where
  rbp : s.gpr .rbp = cP s₀ + BitVec.ofNat 64 1024
  r12 : s.gpr .r12 = sP s₀
  r13 : s.gpr .r13 = aP s₀ + BitVec.ofNat 64 (ra * (k * i))
  r15 : s.gpr .r15 = tP s₀ + BitVec.ofNat 64 (1024 * i)
  tab : T.is s.mem (cP s₀)
  shat : ∀ j < k, PolyIs s.mem (sP s₀ + BitVec.ofNat 64 (1024 * j)) ((sv k s₀)[j]!)
  tdone : ∀ i' < i, PolyIs s.mem (tP s₀ + BitVec.ofNat 64 (1024 * i')) (tgtG k s₀ Ev rA i')
  trest : ∀ i', i ≤ i' → i' < k → PolyIs s.mem (tP s₀ + BitVec.ofNat 64 (1024 * i')) (Ev[i']!)

/-- `RInvG` of `Â` and `e` as `u32`s. -/
abbrev RInv (R : AccRep) (T : TabRep) (i : Nat) (s : State) : Prop := RInvG k s₀ (ev k s₀) 1024 (rowA k s₀) R T i s

/-- After the products `0, …, j - 1` of row `i`, accumulated. -/
structure PInv (R : AccRep) (T : TabRep) (i j : Nat) (c14 : BitVec 64) (s : State) : Prop
    extends RInvG k s₀ (ev k s₀) 1024 (rowA k s₀) R T i s where
  r14 : s.gpr .r14 = c14
  acc : R.is s.mem (cP s₀ + BitVec.ofNat 64 1024) (dotP (rowA k s₀ i) (sv k s₀) j)

end

/-! ## Regions of the arguments -/

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} {eR : Addr → Region} {eRed : Mem → Addr → Prop}
  {eVec : Mem → Addr → List Poly} (hp : (kgMulKG k aR aRed aMat eR eRed eVec).pre s₀)
include hp

theorem dTS : (vR (tP s₀) k).Disjoint (vR (sP s₀) k) := hp.2.2.1
theorem dTA : (vR (tP s₀) k).Disjoint (aR (aP s₀)) := hp.2.2.2.1
theorem dTE : (vR (tP s₀) k).Disjoint (eR (eP s₀)) := hp.2.2.2.2.1
theorem dTC : (vR (tP s₀) k).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.1
theorem dSA : (vR (sP s₀) k).Disjoint (aR (aP s₀)) := hp.2.2.2.2.2.2.1
theorem dSE : (vR (sP s₀) k).Disjoint (eR (eP s₀)) := hp.2.2.2.2.2.2.2.1
theorem dSC : (vR (sP s₀) k).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.1
theorem dAC : (aR (aP s₀)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.2.1
theorem dEC : (eR (eP s₀)).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.1
theorem rT : (retR s₀).Disjoint (vR (tP s₀) k) := hp.2.2.2.2.2.2.2.2.2.2.2.1
theorem rS : (retR s₀).Disjoint (vR (sP s₀) k) := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rA : (retR s₀).Disjoint (aR (aP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rE : (retR s₀).Disjoint (eR (eP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rC : (retR s₀).Disjoint (cR (cP s₀)) := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem redS : VecReduced s₀.mem (sP s₀) k := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem redA : aRed s₀.mem (aP s₀) := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem redE : eRed s₀.mem (eP s₀) := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

omit hp in
/-- A polynomial of `a` or `e`, as at the start, in memory that differs only in `t`, `s` and `scratch`. -/
theorem ro_frame {m : Mem} (hf : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem m) {p : Addr} {n e : Nat}
    (he : e < n) (hT : (vR (tP s₀) k).Disjoint (vR p n)) (hS : (vR (sP s₀) k).Disjoint (vR p n))
    (hC : (vR p n).Disjoint (cR (cP s₀))) (hr : VecReduced s₀.mem p n) :
    PolyIs m (p + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (p + BitVec.ofNat 64 (1024 * e))) := by
  refine polyIs_frame hf (fun r hr' => ?_) ⟨hr e he, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact (hT.sub_right (sub_v _ he)).symm
  · exact (hS.sub_right (sub_v _ he)).symm
  · exact hC.sub_left (sub_v _ he)

end

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} (hp : (kgMulKA k aR aRed aMat).pre s₀)
include hp

theorem e_frame {m : Mem} (hf : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k) :
    PolyIs m (eP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (eP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  ro_frame hf he (dTE hp :) (dSE hp :) (dEC hp :) (redE hp :)

end

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK k).pre s₀)
include hp

theorem a_frame {m : Mem} (hf : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem m) {e : Nat} (he : e < k * k) :
    PolyIs m (aP s₀ + BitVec.ofNat 64 (1024 * e)) (polyAt s₀.mem (aP s₀ + BitVec.ofNat 64 (1024 * e))) :=
  ro_frame hf he (dTA hp :) (dSA hp :) (dAC hp :) (redA hp :)

end

/-! ## Steps -/

theorem vv_dis (p : Addr) {n i i' : Nat} (hn : n ≤ 16) (hi : i < n) (hi' : i' < n) (hne : i ≠ i') :
    (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint (pR (p + BitVec.ofNat 64 (1024 * i'))) :=
  Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem vr_dis {p p' : Addr} {n n' i i' : Nat} (h : (vR p n).Disjoint (vR p' n')) (hi : i < n) (hi' : i' < n') :
    (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint (pR (p' + BitVec.ofNat 64 (1024 * i'))) :=
  (h.sub_left (sub_v _ hi)).sub_right (sub_v _ hi')

theorem vc_dis {p C : Addr} {n i o m : Nat} (h : (vR p n).Disjoint (cR C)) (hi : i < n) (ho : o + m ≤ 4096) :
    (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint ⟨C + BitVec.ofNat 64 o, m⟩ :=
  (h.sub_left (sub_v _ hi)).sub_right (sub_c ho)

theorem vc0_dis {p C : Addr} {n i : Nat} (h : (vR p n).Disjoint (cR C)) (hi : i < n) :
    (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint (pR C) :=
  (h.sub_left (sub_v _ hi)).sub_right (sub_c0 _)

theorem Base.step {k : Nat} {s₀ s s' : State} (hb : Base k s₀ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, Region.Sub r (vR (tP s₀) k) ∨ Region.Sub r (vR (sP s₀) k) ∨ Region.Sub r (cR (cP s₀)))
    (hhi : ∀ r ∈ rs, (hiR (cP s₀)).Disjoint r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : Base k s₀ s' :=
  ⟨by rw [hcs .rbx (by decide), hb.rbx], by rw [hcs .rsp (by decide), hb.rsp], hrd.trans hb.rd, hwr.trans hb.wr,
    hb.frame.trans (hf.sub fun r hr => (hsub r hr).elim (fun h => ⟨_, by simp, h⟩)
      fun h => h.elim (fun h => ⟨_, by simp, h⟩) fun h => ⟨_, by simp, h⟩),
    hb.saved.frame hf fun p hp' r hr => (hhi r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1 (by
      have := (DecMul.slots_bound p hp').2; omega_arith))⟩

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} (hp : (kgMulKA k aR aRed aMat).pre s₀) (hk : k ≤ 4) {B : Bodies}
  {R : AccRep} {T : TabRep} (hB : BodiesOk B R T)
include hp hk hB

omit hp hk hB in
theorem dChi {p : Addr} {n i : Nat} (h : (vR p n).Disjoint (cR (cP s₀))) (hi : i < n) :
    (hiR (cP s₀)).Disjoint (pR (p + BitVec.ofNat 64 (1024 * i))) :=
  ((h.sub_left (sub_v _ hi)).sub_right (sub_c (by decide))).symm

set_option linter.unusedSimpArgs false in
/-- An iteration of the first loop: `NTT(s[j])` in place, and `NTT(e[j])` to `t[j]`. -/
theorem nttStep_ok {j : Nat} (hj : j < k) {s : State} (hI : NInv k s₀ (ev k s₀) 1024 j s) :
    WP isa (KpkeMul.nttK B) s fun s' => NInv k s₀ (ev k s₀) 1024 (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hsr : s.rd = [aR (aP s₀), vR (eP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hS := hI.srest j (Nat.le_refl _) hj
  unfold KpkeMul.nttK KpkeMul.nttKg
  -- `NTT(s[j])` in place
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = sP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = cP s₀ ∧ s1.gpr .r10 = sP s₀ + BitVec.ofNat 64 (1024 * j) ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [hI.r12, hI.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  refine WP.seq (WP.inline (k := nttOK) hB.nttO (rd := [pR (sP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, vc0_dis (dSC hp :) hj, vc0_dis (dSC hp :) hj, (rS hp :).sub_right (sub_v _ hj),
      (rC hp :).sub_right (sub_c0 _), hS.1⟩
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
      exacts [dChi (dSC hp :) hj, hi_dis_c0 _]) (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) g2
  have hE := e_frame hp hb2.frame hj
  -- `NTT(e[j])` to `t[j]`
  refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = eP s₀ + BitVec.ofNat 64 (1024 * j) ∧
      s3.gpr .rsi = cP s₀ ∧ s3.gpr .r10 = tP s₀ + BitVec.ofNat 64 (1024 * j) ∧ s3.mem = s2.mem ∧
      Keep [.rdi, .rsi, .r10] s2 s3) (by
        vrunm [g2 .r15 (by decide), g2 .rbx (by decide), g2 .rbp (by decide), hI.r15, hI.rbx, hI.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, h3r10, hm3, k3⟩ => ?_)
  have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [k3.gpr (by decide), hb2.rsp]
  have hsr2 : s3.rd = [aR (aP s₀), vR (eP s₀) k] := by rw [k3.2.1, hb2.rd, hp.1]
  have hsw2 : s3.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [k3.2.2, hb2.wr, hp.2.1]
  refine WP.seq (WP.inline (k := nttOK) hB.nttO (rd := [pR (eP s₀ + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (tP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) hB.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, h3r10, hsp3, hm3, retR]
    exact ⟨trivial, trivial, vc0_dis (dEC hp :) hj, vc0_dis (dTC hp :) hj, (rT hp :).sub_right (sub_v _ hj),
      (rC hp :).sub_right (sub_c0 _), hE.1⟩
  · rw [hsr2, hsw2]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons ((cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons
      ((cov_one (by simp) (in_c0 _)).cons Covers.nil))
  · rw [hsw2]
    exact (cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons ((cov_one (by simp) (in_c0 _)).cons Covers.nil)
  simp only [nttOK, State.withRegions_gpr, State.withRegions_mem, h3di, h3r10, hm3, hE.2] at hpost4
  rw [← vecAt_map_get _ _ hj] at hpost4
  rw [hm3] at hf4
  have g4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by
    rw [habi4.1 r hr, cs (by decide) k3 r hr, g2 r hr]
  have hb4 : Base k s₀ s4 := hb2.step hf4 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inl (sub_v _ hj), .inr (.inr (sub_c0 _))]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dChi (dTC hp :) hj, hi_dis_c0 _]) (by rw [hrd4, k3.2.1]) (by rw [hwr4, k3.2.2])
    (fun r hr => by rw [habi4.1 r hr, cs (by decide) k3 r hr])
  -- what the two writes keep
  have fS2 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (sP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega_arith) hj' hj hne, vc0_dis (dSC hp :) hj']
  have fS4 : ∀ {j'}, j' < k → ∀ r ∈ [pR (tP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (sP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis (dTS hp :).symm hj' hj, vc0_dis (dSC hp :) hj']
  have fT2 : ∀ {j'}, j' < k → ∀ r ∈ [pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (tP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis (dTS hp :) hj' hj, vc0_dis (dTC hp :) hj']
  have fT4 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (tP s₀ + BitVec.ofNat 64 (1024 * j)), pR (cP s₀)],
      (pR (tP s₀ + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega_arith) hj' hj hne, vc0_dis (dTC hp :) hj']
  -- the next `j`
  vrunm [g4 .r12 (by decide), g4 .r15 (by decide), g4 .rbp (by decide), g4 .r14 (by decide), hI.r12, hI.r15,
    hI.rbp, sx1024]
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

/-! ## The second loop -/

/-- What a product writes: the accumulator, and `scratch`'s working spaces. -/
abbrev wrP (C : Addr) : List Region := [pR (C + BitVec.ofNat 64 1024), pR C, tmpR C]

theorem wrP_dis {p C : Addr} {n i : Nat} (h : (vR p n).Disjoint (cR C)) (hi : i < n) :
    ∀ r ∈ wrP C, (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [vc_dis h hi (by decide), vc0_dis h hi, vc_dis h hi (by decide)]

theorem wrP_tab (C : Addr) : ∀ r ∈ wrP C, (tabR C).Disjoint r := fun r hr => by
  have pd := DecMul.prod_dis C
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [Offset.disjoint C (.inr (by decide)) (by decide) (by decide), pd.2.2.2.1.symm, pd.2.2.2.2.symm]

theorem wrP_hi (C : Addr) : ∀ r ∈ wrP C, (hiR C).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [hi_dis_c (by decide), hi_dis_c0 _, hi_dis_c (by decide)]

theorem wrP_sub {k : Nat} {s₀ : State} : ∀ r ∈ wrP (cP s₀),
    Region.Sub r (vR (tP s₀) k) ∨ Region.Sub r (vR (sP s₀) k) ∨ Region.Sub r (cR (cP s₀)) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [.inr (.inr (sub_c (by decide))), .inr (.inr (sub_c0 _)), .inr (.inr (sub_c (by decide)))]

theorem rowA_get (m : Mem) (p : Addr) {k i j : Nat} (hj : j < k) :
    (vecAt m (p + BitVec.ofNat 64 (1024 * (k * i))) k)[j]! = polyAt m (p + BitVec.ofNat 64 (1024 * (k * i + j))) := by
  rw [vecAt_get _ _ hj, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]

/-- `RInv`, after writes to `wrP`. -/
theorem RInvG.step {k : Nat} {s₀ : State} (hp : (kgMulK k).pre s₀) {R : AccRep} {T : TabRep} {i : Nat}
    (hik : i ≤ k) {s s' : State} (hI : RInv k s₀ R T i s) (hf : Frame (wrP (cP s₀)) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : RInv k s₀ R T i s' :=
  ⟨hI.toBase.step hf wrP_sub (wrP_hi _) hrd hwr hcs, by rw [hcs .rbp (by decide), hI.rbp],
    by rw [hcs .r12 (by decide), hI.r12], by rw [hcs .r13 (by decide), hI.r13], by rw [hcs .r15 (by decide), hI.r15],
    T.frame hf (wrP_tab _) hI.tab, fun j hj => polyIs_frame hf (wrP_dis (dSC hp :) hj) (hI.shat j hj),
    fun i' hi' => polyIs_frame hf (wrP_dis (dTC hp :) (by omega_arith)) (hI.tdone i' hi'),
    fun i' h1 h2 => polyIs_frame hf (wrP_dis (dTC hp :) h2) (hI.trest i' h1 h2)⟩

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

set_option linter.unusedSimpArgs false in
/-- Term `j` of row `i`. -/
theorem prodStep_ok {i j : Nat} {c14 : BitVec 64} (hi : i < k) (hj : j < k) {s : State}
    (hI : PInv k s₀ R T i j c14 s) :
    WP isa (KpkeMul.prodK B j) s (PInv k s₀ R T i (j + 1) c14) := by
  have e : k * i + j < k * k := by
    have := Nat.mul_le_mul_left k (show i + 1 ≤ k by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  have hkk : k * k ≤ 64 := Nat.le_trans (Nat.mul_le_mul hk hk) (by decide)
  have hsr : s.rd = [vR (aP s₀) (k * k), vR (eP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hA := a_frame hp hI.frame e
  have hS := hI.shat j hj
  have hj31 : 1024 * j < 2 ^ 31 := by omega_arith
  have pd := DecMul.prod_dis (cP s₀)
  unfold KpkeMul.prodK
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = cP s₀ + BitVec.ofNat 64 1024 ∧
      s1.gpr .rsi = aP s₀ + BitVec.ofNat 64 (1024 * (k * i + j)) ∧
      s1.gpr .rdx = sP s₀ + BitVec.ofNat 64 (1024 * j) ∧ s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx] s s1) (by
        vrunm [hI.rbp, hI.r13, hI.r12, hI.rbx, sx_ofNat hj31]
        refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
        · rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1dx, h1cx, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  have hbx1 : s1.gpr .rbx = cP s₀ := by rw [k1.gpr (by decide), hI.rbx]
  have hbp1 : s1.gpr .rbp = cP s₀ + BitVec.ofNat 64 1024 := by rw [k1.gpr (by decide), hI.rbp]
  refine WP.inline (k := mulAccK R T 0) (hB.mulAcc 0 (by decide))
    (rd := [pR (aP s₀ + BitVec.ofNat 64 (1024 * (k * i + j))), pR (sP s₀ + BitVec.ofNat 64 (1024 * j)), tabR (cP s₀)])
    (wr := wrP (cP s₀)) ?_ ?_ ?_ (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) (hB.nc.2.2.2 0)
  · simp only [mulAccK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1dx, h1cx, hsp1, hbx1, hbp1, hm1, retR]
    exact ⟨trivial, trivial, (vc_dis (dAC hp :) e (by decide)).symm, (vc_dis (dSC hp :) hj (by decide)).symm,
      pd.1, pd.2.1, Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
      vc0_dis (dAC hp :) e, vc_dis (dAC hp :) e (by decide), vc0_dis (dSC hp :) hj, vc_dis (dSC hp :) hj (by decide),
      pd.2.2.1, pd.2.2.2.1, pd.2.2.2.2, (rC hp :).sub_right (sub_c (by decide)), (rA hp :).sub_right (sub_v _ e),
      (rS hp :).sub_right (sub_v _ hj), (rC hp :).sub_right (sub_c0 _), (rC hp :).sub_right (sub_c (by decide)),
      (rC hp :).sub_right (sub_c (by decide)), trivial, by rw [Nat.mul_zero, add_ofNat_zero], hA.1, hS.1, hI.tab,
      ⟨_, hI.acc⟩⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_vec _ hkk e)).cons ((cov_one (by simp) (in_vec _ (by omega_arith) hj)).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c0 _)).cons ((cov_one (by simp) (in_c (by decide))).cons Covers.nil)))))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_c (by decide))).cons Covers.nil))
  simp only [mulAccK, State.withRegions_gpr, State.withRegions_mem, h1di, h1si, h1dx, hm1] at hpost2
  rw [hm1] at hf2
  have hP := hpost2 _ hI.acc
  rw [hA.2, hS.2, ← rowA_get _ _ hj, ← dotP_succ (by rw [vecAt_length]; exact hj)
    (by rw [List.length_map, vecAt_length]; exact hj)] at hP
  have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by rw [habi2.1 r hr, cs (by decide) k1 r hr]
  exact ⟨hI.toRInvG.step hp (by omega_arith) hf2 (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) g2,
    by rw [g2 .r14 (by decide), hI.r14], hP⟩

/-- Term `0` of row `i`, stored to the accumulator. -/
theorem setStep_ok {i : Nat} (hi : i < k) {s : State} (hI : RInv k s₀ R T i s) :
    WP isa (KpkeMul.prodSetK B) s (PInv k s₀ R T i 1 (s.gpr .r14)) := by
  have h0 : 0 < k := by omega_arith
  have e : k * i + 0 < k * k := by
    have := Nat.mul_le_mul_left k (show i + 1 ≤ k by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  have hkk : k * k ≤ 64 := Nat.le_trans (Nat.mul_le_mul hk hk) (by decide)
  have hsr : s.rd = [vR (aP s₀) (k * k), vR (eP s₀) k] := by rw [hI.rd, hp.1]
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  have hA := a_frame hp hI.frame e
  have hS := hI.shat 0 h0
  have pd := DecMul.prod_dis (cP s₀)
  unfold KpkeMul.prodSetK
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = cP s₀ + BitVec.ofNat 64 1024 ∧
      s1.gpr .rsi = aP s₀ + BitVec.ofNat 64 (1024 * (k * i + 0)) ∧
      s1.gpr .rdx = sP s₀ + BitVec.ofNat 64 (1024 * 0) ∧ s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx] s s1) (by
        vrunm [hI.rbp, hI.r13, hI.r12, hI.rbx]
        refine ⟨by rw [Nat.add_zero], by rw [Nat.mul_zero, add_ofNat_zero], fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h1di, h1si, h1dx, h1cx, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = s₀.gpr .rsp := by rw [k1.gpr (by decide), hI.rsp]
  have hbx1 : s1.gpr .rbx = cP s₀ := by rw [k1.gpr (by decide), hI.rbx]
  refine WP.inline (k := mulSetK R T) hB.mulSet
    (rd := [pR (aP s₀ + BitVec.ofNat 64 (1024 * (k * i + 0))), pR (sP s₀ + BitVec.ofNat 64 (1024 * 0)),
      tabR (cP s₀)])
    (wr := wrP (cP s₀)) ?_ ?_ ?_ (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) hB.ncSet
  · simp only [mulSetK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1dx, h1cx, hsp1, hbx1, hm1, retR]
    exact ⟨trivial, trivial, (vc_dis (dAC hp :) e (by decide)).symm, (vc_dis (dSC hp :) h0 (by decide)).symm,
      pd.1, pd.2.1, Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
      vc0_dis (dAC hp :) e, vc_dis (dAC hp :) e (by decide), vc0_dis (dSC hp :) h0, vc_dis (dSC hp :) h0 (by decide),
      pd.2.2.1, pd.2.2.2.1, pd.2.2.2.2, (rC hp :).sub_right (sub_c (by decide)), (rA hp :).sub_right (sub_v _ e),
      (rS hp :).sub_right (sub_v _ h0), (rC hp :).sub_right (sub_c0 _), (rC hp :).sub_right (sub_c (by decide)),
      (rC hp :).sub_right (sub_c (by decide)), trivial, hA.1, hS.1, hI.tab⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact (cov_one (by simp) (in_vec _ hkk e)).cons ((cov_one (by simp) (in_vec _ (by omega_arith) h0)).cons
      ((cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c (by decide))).cons
      ((cov_one (by simp) (in_c0 _)).cons ((cov_one (by simp) (in_c (by decide))).cons Covers.nil)))))
  · rw [k1.2.2, hsw]
    exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_c0 _)).cons
      ((cov_one (by simp) (in_c (by decide))).cons Covers.nil))
  simp only [mulSetK, State.withRegions_gpr, State.withRegions_mem, h1di, h1si, h1dx, hm1] at hpost2
  rw [hm1] at hf2
  rw [hA.2, hS.2, ← rowA_get _ _ h0, ← zero_add_poly (multiplyNTTs _ _), ← dotP_zero (rowA k s₀ i) (sv k s₀),
    ← dotP_succ (by rw [vecAt_length]; exact h0) (by rw [List.length_map, vecAt_length]; exact h0)] at hpost2
  have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by rw [habi2.1 r hr, cs (by decide) k1 r hr]
  exact ⟨hI.step hp (by omega_arith) hf2 (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) g2,
    by rw [g2 .r14 (by decide)], hpost2⟩

/-- The terms `j, …, k - 1` of row `i`. -/
theorem innerK_ok {i : Nat} {c14 : BitVec 64} (hi : i < k) :
    ∀ n j, j + n = k → ∀ {s : State}, PInv k s₀ R T i j c14 s →
      WP isa (KpkeMul.innerK B j n) s (PInv k s₀ R T i k c14)
  | 0, j, h, _, hI => WP.block_nil (by rwa [show j = k by omega_arith] at hI)
  | n + 1, j, h, _, hI => WP.seq (WP.mono (prodStep_ok hp hk hB hi (by omega_arith) hI) fun _ h' =>
      innerK_ok hi n (j + 1) (by omega_arith) h')

end

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

set_option linter.unusedSimpArgs false in
/-- Row `i`: its sum of products, added to `t[i] = NTT(e[i])`. -/
theorem rowStep_ok {i : Nat} (hi : i < k) {s : State} (hI : RInv k s₀ R T i s) :
    WP isa (KpkeMul.rowK B k) s fun s' => RInv k s₀ R T (i + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  have cs : ∀ {rs : List Reg}, (∀ r ∈ calleeSaved, r ∉ rs) → ∀ {a b : State}, Keep rs a b → ∀ r ∈ calleeSaved,
      b.gpr r = a.gpr r := fun h _ _ kk r hr => kk.gpr (h r hr)
  unfold KpkeMul.rowK
  -- the products
  refine WP.seq (WP.mono (setStep_ok hp hk hB hi hI) fun s2 hz => ?_)
  refine WP.seq (WP.mono (innerK_ok hp hk hB hi (k - 1) 1 (by omega_arith) hz) fun u hP => ?_)
  -- added to `t[i]`
  have hT := hP.trest i (Nat.le_refl _) hi
  have hF : WP isa (.seq (.block [.mov .rdi (.reg .r15), .mov .rsi (.reg .rbp)]) B.fin) u fun s4 =>
      Base k s₀ s4 ∧ (∀ r ∈ calleeSaved, s4.gpr r = u.gpr r) ∧
        PolyIs s4.mem (tP s₀ + BitVec.ofNat 64 (1024 * i)) (tgt k s₀ i) ∧
        Frame [pR (tP s₀ + BitVec.ofNat 64 (1024 * i))] u.mem s4.mem := by
    refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = tP s₀ + BitVec.ofNat 64 (1024 * i) ∧
        s3.gpr .rsi = cP s₀ + BitVec.ofNat 64 1024 ∧ s3.mem = u.mem ∧ Keep [.rdi, .rsi] u s3) (by
          vrunm [hP.r15, hP.rbp]
          refine ⟨fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s3 ⟨h3di, h3si, hm3, k3⟩ => ?_)
    have hsp3 : s3.gpr .rsp = s₀.gpr .rsp := by rw [k3.gpr (by decide), hP.rsp]
    have usw : s3.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [k3.2.2, hP.wr, hp.2.1]
    refine WP.inline (k := finK R) hB.fin (rd := [pR (cP s₀ + BitVec.ofNat 64 1024)])
      (wr := [pR (tP s₀ + BitVec.ofNat 64 (1024 * i))]) ?_ ?_ ?_
      (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) hB.ncFin
    · simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        h3di, h3si, hsp3, hm3, retR]
      exact ⟨trivial, trivial, vc_dis (dTC hp :) hi (by decide), (rT hp :).sub_right (sub_v _ hi),
        (rC hp :).sub_right (sub_c (by decide)), hT.1, ⟨_, hP.acc⟩⟩
    · rw [usw]
      exact (cov_one (by simp) (in_c (by decide))).cons ((cov_one (by simp) (in_vec _ (by omega_arith) hi)).cons
        Covers.nil)
    · rw [usw]
      exact (cov_one (by simp) (in_vec _ (by omega_arith) hi)).cons Covers.nil
    simp only [finK, State.withRegions_gpr, State.withRegions_mem, h3di, h3si, hm3] at hpost4
    have hR := hpost4 _ hP.acc
    rw [hT.2, dotP_full (vecAt_length _ _ _) (by rw [List.length_map, vecAt_length]), add_comm_poly] at hR
    rw [hm3] at hf4
    exact (⟨hP.toBase.step hf4 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl (sub_v _ hi))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dChi (dTC hp :) hi)
      (by rw [hrd4, k3.2.1]) (by rw [hwr4, k3.2.2]) (fun r hr => by rw [habi4.1 r hr, cs (by decide) k3 r hr]),
      fun r hr => by rw [habi4.1 r hr, cs (by decide) k3 r hr], hR, hf4⟩ :
      Base k s₀ s4 ∧ (∀ r ∈ calleeSaved, s4.gpr r = u.gpr r) ∧
        PolyIs s4.mem (tP s₀ + BitVec.ofNat 64 (1024 * i)) (tgt k s₀ i) ∧
        Frame [pR (tP s₀ + BitVec.ofNat 64 (1024 * i))] u.mem s4.mem)
  refine WP.seq (WP.mono hF fun s4 h4 => ?_)
  -- the next row
  obtain ⟨hb4, g4, hR4, hf4⟩ := h4
  have hk31 : 1024 * k < 2 ^ 31 := by omega_arith
  have fo : ∀ r ∈ [pR (tP s₀ + BitVec.ofNat 64 (1024 * i))], (tabR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (vc_dis (dTC hp :) hi (by decide)).symm
  vrunm [g4 .r13 (by decide), g4 .r15 (by decide), g4 .r14 (by decide), hP.r13, hP.r15, hP.r14, sx1024,
    sx_ofNat hk31]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun i' hi' => ?_, fun i' h1 h2 => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb4.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb4.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.frame
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.saved
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .rbp (by decide), hP.rbp]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    rw [g4 .r12 (by decide), hP.r12]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ, Nat.mul_add]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact T.frame hf4 fo hP.tab
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf4 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vr_dis (dTS hp :).symm hj hi) (hP.shat j hj)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases h : i' = i
    · subst h; exact hR4
    · exact polyIs_frame hf4 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact vv_dis _ (by omega_arith) (by omega_arith) hi h)
        (hP.tdone i' (by omega_arith))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf4 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vv_dis _ (by omega_arith) h2 hi (by omega_arith))
      (hP.trest i' (by omega_arith) h2)

end

/-- A row of `B`'s `keygen_mul`, for the representations `R` and `T` of its
bodies: from `RInv i` to `RInv (i + 1)`, counting `r14` down. -/
def RowOk (B : Bodies) (R : AccRep) (T : TabRep) : Prop :=
  ∀ {k : Nat} {s₀ : State}, (kgMulK k).pre s₀ → k ≤ 4 → ∀ {i : Nat}, i < k → ∀ {s : State}, RInv k s₀ R T i s →
    WP isa (KpkeMul.rowOf B k) s fun s' => RInv k s₀ R T (i + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0)

/-- A backend without a row of its own: its row through the accumulator. -/
theorem RowOk.ofAcc {B : Bodies} {R : AccRep} {T : TabRep} (hB : BodiesOk B R T) (hn : B.kgRow = none) :
    RowOk B R T := fun hp hk _ hi _ hI => by
  unfold KpkeMul.rowOf
  rw [hn]
  exact rowStep_ok hp hk hB hi hI

/-! ## The whole function -/

/-- The code inside the MXCSR region. -/
abbrev innerG (term row : Prog isa) (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.loop term .ne) (.seq (.block (KpkeMul.midK B k)) (.loop row .ne))

/-- The code inside the MXCSR region of `keygenMul B k`. -/
abbrev inner (B : Bodies) (k : Nat) : Prog isa := innerG (KpkeMul.nttK B) (KpkeMul.rowOf B k) B k

theorem tgt_eqG (M : List (List Poly)) {k i : Nat} (hi : i < k) (hM : M.length = k) (v w : List Poly)
    (hw : w.length = k) : (addVec (mulMatVec M v) w).getD i zero = add (dot (M.getD i []) v) (w[i]!) := by
  rw [getElem!_pos w i (by omega_arith)]
  simp [addVec, mulMatVec, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map,
    List.getElem?_eq_getElem (show i < M.length by omega_arith), List.getElem?_eq_getElem (show i < w.length by omega_arith)]

theorem tgt_eq (m : Mem) (aP : Addr) {k i : Nat} (hi : i < k) (v w : List Poly) (hw : w.length = k) :
    (addVec (mulMatVec (matAt m aP k) v) w).getD i zero =
      add (dot (vecAt m (aP + BitVec.ofNat 64 (1024 * (k * i))) k) v) (w[i]!) := by
  rw [getElem!_pos w i (by omega_arith)]
  simp [addVec, mulMatVec, matAt, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map,
    List.getElem?_range hi, List.getElem?_eq_getElem (show i < w.length by omega_arith)]

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} {eR : Addr → Region} {eRed : Mem → Addr → Prop}
  {eVec : Mem → Addr → List Poly} (hp : (kgMulKG k aR aRed aMat eR eRed eVec).pre s₀) (hk : k ≤ 4) {B : Bodies}
  {R : AccRep} {T : TabRep} (hB : BodiesOk B R T)
include hp hk hB

set_option linter.unusedSimpArgs false in
/-- Between the loops: `ŝ` and `t` again, the accumulator's address, the table. -/
theorem mid_ok {Ev : List Poly} {se ra : Nat} {rA : Nat → List Poly} {s : State} (hI : NInv k s₀ Ev se k s) :
    WP isa (.block (KpkeMul.midK B k)) s fun s' => RInvG k s₀ Ev ra rA R T 0 s' ∧
      s'.gpr .r14 = BitVec.ofNat 64 k := by
  have hk31 : 1024 * k < 2 ^ 31 := by omega_arith
  have hsw : s.wr = [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] := by rw [hI.wr, hp.2.1]
  unfold KpkeMul.midK
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .r12 = sP s₀ ∧ s1.gpr .r15 = tP s₀ ∧
      s1.gpr .rbp = cP s₀ + BitVec.ofNat 64 1024 ∧ s1.gpr .rcx = cP s₀ ∧ s1.mem = s.mem ∧
      Keep [.r12, .r15, .rbp, .rcx] s s1) (by
        vrunm [hI.r12, hI.rbp, hI.rbx, sx1024, sx_ofNat hk31]
        refine ⟨BitVec.add_sub_cancel _ _, BitVec.add_sub_cancel _ _, fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h112, h115, h1bp, h1cx, hm1, k1⟩ => ?_
  rw [WP.block_append_iff]
  have hin : InRegions s1.wr (s1.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
    rw [k1.2.2, hsw, h1cx]; exact ⟨cR (cP s₀), by simp, in_c (by decide)⟩
  refine WP.mono (hB.tab s1 hin) fun s2 ⟨hT2, hf2, k2⟩ => ?_
  rw [h1cx] at hT2 hf2
  rw [hm1] at hf2
  have k12 := k1.trans k2
  have hb2 : Base k s₀ s2 := ⟨by rw [k12.gpr (by decide), hI.rbx], by rw [k12.gpr (by decide), hI.rsp],
    by rw [k12.2.1, hI.rd], by rw [k12.2.2, hI.wr],
    hI.frame.trans (hf2.sub fun r hr => ⟨cR (cP s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩),
    hI.saved.frame hf2 fun p hp' r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hi_dis_tab _).sub_left (sub_hi (DecMul.slots_bound p hp').1 (by
        have := (DecMul.slots_bound p hp').2; omega_arith))⟩
  have ftab : ∀ {p : Addr} {n i : Nat}, (vR p n).Disjoint (cR (cP s₀)) → i < n →
      ∀ r ∈ [tabR (cP s₀)], (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint r := fun h hi r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact vc_dis h hi (by decide)
  vrunm
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun i' hi' => ?_, fun i' _ h2 => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, ite_false, reduceCtorEq]; exact hb2.rbx
  · simp only [RegUpd.gpr_setReg, ite_false, reduceCtorEq]; exact hb2.rsp
  · simp only [RegUpd.rd_setReg]; exact hb2.rd
  · simp only [RegUpd.wr_setReg]; exact hb2.wr
  · simp only [RegUpd.mem_setReg]; exact hb2.frame
  · simp only [RegUpd.mem_setReg]; exact hb2.saved
  · simp only [RegUpd.gpr_setReg, ite_false, reduceCtorEq]; rw [k2.gpr (by decide), h1bp]
  · simp only [RegUpd.gpr_setReg, ite_false, reduceCtorEq]; rw [k2.gpr (by decide), h112]
  · simp only [RegUpd.gpr_setReg, ite_false, reduceCtorEq]
    rw [k12.gpr (by decide), hI.r13, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero]
  · simp only [RegUpd.gpr_setReg, ite_false, reduceCtorEq]
    rw [k2.gpr (by decide), h115, Nat.mul_zero, add_ofNat_zero]
  · simp only [RegUpd.mem_setReg]; exact hT2
  · simp only [RegUpd.mem_setReg]; exact polyIs_frame hf2 (ftab (dSC hp :) hj) (hI.sdone j hj)
  · exact absurd hi' (Nat.not_lt_zero _)
  · simp only [RegUpd.mem_setReg]; exact polyIs_frame hf2 (ftab (dTC hp :) h2) (hI.tdone i' h2)
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

end

theorem getD_get (l : List Poly) {i : Nat} (h : i < l.length) : l.getD i zero = l[i]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some, getElem!_pos l i h]

section
variable {k : Nat} {s₀ : State} {aR : Addr → Region} {aRed : Mem → Addr → Prop}
  {aMat : Mem → Addr → List (List Poly)} {eR : Addr → Region} {eRed : Mem → Addr → Prop}
  {eVec : Mem → Addr → List Poly} (hp : (kgMulKG k aR aRed aMat eR eRed eVec).pre s₀) (hk : k ≤ 4) {B : Bodies}
  {R : AccRep} {T : TabRep} (hB : BodiesOk B R T)
include hp hk hB

/-- `keygenMulg term row B k`, given that `term` computes the `NTT`s of `s` and
`e` and `row` the rows of `Â` (`rA`, `ra` bytes between their polynomials). -/
theorem wp_allg (hk0 : 0 < k) {term row : Prog isa} {se ra : Nat} {rA : Nat → List Poly}
    (hEl : (eVec s₀.mem (eP s₀)).length = k)
    (hterm : ∀ j < k, ∀ s, NInv k s₀ ((eVec s₀.mem (eP s₀)).map ntt) se j s → WP isa term s fun s' =>
      NInv k s₀ ((eVec s₀.mem (eP s₀)).map ntt) se (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
        s'.zf = some (s.gpr .r14 - 1 == 0))
    (hM : (aMat s₀.mem (aP s₀)).length = k) (hrA : ∀ i < k, (aMat s₀.mem (aP s₀)).getD i [] = rA i)
    (hrow : ∀ i < k, ∀ s, RInvG k s₀ ((eVec s₀.mem (eP s₀)).map ntt) ra rA R T i s → WP isa row s fun s' =>
      RInvG k s₀ ((eVec s₀.mem (eP s₀)).map ntt) ra rA R T (i + 1) s' ∧
      s'.gpr .r14 = s.gpr .r14 - 1 ∧ s'.zf = some (s.gpr .r14 - 1 == 0))
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (innerG term row B k) = true) :
    WP isa (keygenMulg term row B k) s₀ fun s' => gprPreserved s₀ s' ∧
      (kgMulKG k aR aRed aMat eR eRed eVec).post s₀ s' := by
  have hcw : cR (cP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  unfold keygenMulg
  refine WP.seq ?_
  rw [EncMul.saveE_eq]
  refine Spill.save_then .r8 KpkeMul.slots (fun p hp' => ⟨_, hcw, in_c (by
    have := DecMul.slots_bound p hp'; omega_arith)⟩) ?_
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rbx = cP s₀ ∧ s1.gpr .rbp = tP s₀ ∧ s1.gpr .r12 = sP s₀ ∧
      s1.gpr .r13 = aP s₀ ∧ s1.gpr .r15 = eP s₀ ∧ s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.gpr .rsp = s₀.gpr .rsp ∧
      s1.rd = s₀.rd ∧ s1.wr = s₀.wr ∧ s1.mem = Spill.saveMem s₀.mem (cP s₀) s₀.gpr KpkeMul.slots) (by
        vrunm
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega_arith) fun s1 ⟨h1bx, h1bp, h112, h113, h115, h114, h1sp, h1rd, h1wr, hm1⟩ => ?_
  have h0 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 768) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s1.wr (cP s₀ + BitVec.ofNat 64 772) 4 := by rw [h1wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have hsv : Spill.Saved s1.mem (cP s₀) s₀.gpr KpkeMul.slots := by
    rw [hm1]; exact Spill.saveMem_saved _ _ _ _ (by decide)
  have hfC : Frame [cR (cP s₀)] s₀.mem s1.mem := by
    rw [hm1]
    exact Spill.saveMem_frame_base s₀.mem (cP s₀) s₀.gpr KpkeMul.slots (L := 4096)
      (fun p hp' => by have := DecMul.slots_bound p hp'; omega_arith) (by decide)
  have hmx : ∀ r ∈ [mxR (cP s₀)], (hiR (cP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have hmxv : ∀ {p : Addr} {n i : Nat}, (vR p n).Disjoint (cR (cP s₀)) → i < n →
      ∀ r ∈ [mxR (cP s₀)], (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint r := fun h hi r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact vc_dis h hi (by decide)
  refine WP.seq (WP.mono (withMxcsr_ok' (r := .rbx) (by decide) _ (by decide) h1bx h0 h4 hwo
    (Q := fun s' => Base k s₀ s' ∧ (∀ j < k, PolyIs s'.mem (sP s₀ + BitVec.ofNat 64 (1024 * j)) ((sv k s₀)[j]!)) ∧
      ∀ i < k, PolyIs s'.mem (tP s₀ + BitVec.ofNat 64 (1024 * i)) (tgtG k s₀ ((eVec s₀.mem (eP s₀)).map ntt) rA i))
    (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, ⟨hb4, hs4, ht4⟩, hf5, k5⟩ => ?_)
  · -- the loops
    have hfC2 : Frame [cR (cP s₀)] s₀.mem s2.mem :=
      hfC.trans (f2.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩)
    have hb2 : Base k s₀ s2 := ⟨by rw [k2.gpr (by decide), h1bx], by rw [k2.gpr (by decide), h1sp],
      by rw [k2.2.1, h1rd], by rw [k2.2.2, h1wr],
      hfC2.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr (.inr hr), fun _ h => h⟩,
      hsv.frame f2 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega_arith))⟩
    refine WP.seq (wp_countdown (cnt := .r14) (N := k) (by omega_arith) hk0 (NInv k s₀ ((eVec s₀.mem (eP s₀)).map ntt) se)
      (fun j hj u hI _ => hterm j hj u hI) (fun u hN => ?_)
      ⟨hb2, by rw [k2.gpr (by decide), h112, Nat.mul_zero, add_ofNat_zero],
        by rw [k2.gpr (by decide), h115, Nat.mul_zero, add_ofNat_zero],
        by rw [k2.gpr (by decide), h1bp, Nat.mul_zero, add_ofNat_zero], by rw [k2.gpr (by decide), h113],
        fun _ h => absurd h (Nat.not_lt_zero _),
        fun j' _ hj' => polyIs_frame hfC2 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (dSC hp :).sub_left (sub_v _ hj'))
          ⟨redS hp j' hj', rfl⟩,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
      (by rw [k2.gpr (by decide), h114]))
    refine WP.seq (WP.mono (mid_ok hp hk hB (R := R) (T := T) (ra := ra) (rA := rA) hN) fun u2 ⟨hR0, h14⟩ => ?_)
    exact wp_countdown (cnt := .r14) (N := k) (by omega_arith) hk0 (RInvG k s₀ ((eVec s₀.mem (eP s₀)).map ntt) ra rA R T)
      (fun i hi u hR _ => hrow i hi u hR) (fun u hR => ⟨hR.toBase, hR.shat, hR.tdone⟩) hR0 h14
  · -- the epilogue
    have h5bx : s5.gpr .rbx = cP s₀ := by rw [k5.gpr (by decide), hb4.rbx]
    have hf : Frame [vR (tP s₀) k, vR (sP s₀) k, cR (cP s₀)] s₀.mem s5.mem :=
      hb4.frame.trans (hf5.sub fun r hr => ⟨cR (cP s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_c (by decide)⟩)
    have hs5 : Spill.Saved s5.mem (s5.gpr .rbx) s₀.gpr KpkeMul.slots := by
      rw [h5bx]
      exact hb4.saved.frame hf5 fun p hp' r hr => (hmx r hr).sub_left (sub_hi (DecMul.slots_bound p hp').1
        (by have := (DecMul.slots_bound p hp').2; omega_arith))
    rw [DecMul.restore_eq]
    refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots s₀.gpr s5 (by decide) (fun p hp' => ?_) hs5)
      fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by rw [k5.gpr (by decide), hb4.rsp]), ?_⟩,
        ⟨by rw [List.length_map, vecAt_length], fun j hj => ?_⟩, ⟨?_, fun i hi => ?_⟩⟩
    · rw [h5bx, k5.2.1, k5.2.2, hb4.rd, hb4.wr]
      exact ⟨_, List.mem_append_right _ hcw, in_c (by have := DecMul.slots_bound p hp'; omega_arith)⟩
    · rw [hm']
      refine hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [rT hp, rS hp, rC hp]
    · rw [hm', getD_get _ (by rw [List.length_map, vecAt_length]; exact hj)]
      exact polyIs_frame hf5 (hmxv (dSC hp :) hj) (hs4 j hj)
    · simp [addVec, mulMatVec, hM, hEl]
    · rw [hm', tgt_eqG _ hi hM _ _ (by rw [List.length_map, hEl]), hrA i hi]
      exact polyIs_frame hf5 (hmxv (dTC hp :) hi) (ht4 i hi)


end

section
variable {k : Nat} {s₀ : State} (hp : (kgMulK k).pre s₀) (hk : k ≤ 4) {B : Bodies} {R : AccRep} {T : TabRep}
  (hB : BodiesOk B R T)
include hp hk hB

theorem wp_all (hk0 : 0 < k) (hrow : RowOk B R T)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp] (inner B k) = true) :
    WP isa (keygenMul B k) s₀ fun s' => gprPreserved s₀ s' ∧ (kgMulK k).post s₀ s' :=
  wp_allg hp hk hB hk0 (term := KpkeMul.nttK B) (row := KpkeMul.rowOf B k) (ra := 1024) (rA := rowA k s₀)
    (vecAt_length _ _ _) (fun _ hj _ hI => nttStep_ok hp hk hB hj hI) (by simp [matAt])
    (fun i hi => by simp [matAt, List.getD_eq_getElem?_getD, List.getElem?_range hi])
    (fun _ hi _ hR => hrow hp hk hi hR) hwo
end

end KgMul

end VG.Proof.MlKem.X86_64
