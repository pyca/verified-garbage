module

import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Proof.Sha3.X2Contract
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Proof.Sha3.X2Contract
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound

/-! ### `Sha3.AArch64.Neon.Pair`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

theorem roundsProg_ok {n : Nat} (hn : n ≤ 24) {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) : WP isa (Impl.Sha3.AArch64.Neon.Pair.roundsProg n) s fun t =>
      CoreKeep s t ∧ Pairs t ((List.range n).foldl Spec.Sha3.rnd A) ((List.range n).foldl Spec.Sha3.rnd B) := by
  induction n generalizing s A B with
  | zero => exact WP.block_nil_iff.mpr ⟨CoreKeep.refl _,hp⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_using [hn]) hp) fun u ⟨hu,hpu⟩ => ?_)
    refine WP.mono (Hw.round2_ok hpu (by omega_using [hn])) fun t ⟨ht,hpt⟩ => ⟨hu.trans ht,?_⟩
    simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpt

end VG.Proof.Sha3.AArch64.Neon

end

end

/-!
# `vg_keccak_f1600_x2` on AArch64

Untrusted: everything here is checked by Lean. `vector_ok`
(`vg_keccak_f1600_x2_sha3`): from the states at `x0` (`PairAt`, the layout of
the inlined two-lane code) and 128 bytes of working space at `x1`, the
function saves `q8`–`q15` there, runs the inlined code's load, rounds
(`roundsProg_ok`) and store, and restores `q8`–`q15`; it changes nothing else
but `x16`, the vector registers and those two regions. `scalar_ok`
(`vg_keccak_f1600_x2`): the scalar permutation's rounds (`Lazy.core_state_keep`)
on the lanes of each state in turn (`loadLanes_ok`, `storeLanes_ok`), between
its save and restore of the callee-saved registers; it writes only the states.
`verified`: the contract of both (`Proof/Sha3/X2Contract.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.X2

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg save restore saveReg restoreReg)
open VG.Impl.Sha3.AArch64.Neon.X2 (code vector scalar loadLanes storeLanes)
open VG.Impl.Sha3.AArch64.Scalar (laneReg)
open VG.Proof.Sha3.AArch64.Scalar (Boundary.Keep Boundary.Lanes Boundary.CoreState Boundary.laneReg_inj
  Boundary.laneReg_ne_x30)
open VG.Proof.Sha3.AArch64.Sha3.Vector (exec_strq exec_ldrq read_write16 vreg_inj CoreKeep)
open VG.Spec.Sha3 (keccakF)
open VG.Proof.Sha3 (stateX2At)

/-- The function's working space. -/
def scrR (q : Addr) : Region := ⟨q, 128⟩

theorem scr_contains (q : Addr) {i : Nat} (hi : i < 8) :
    (scrR q).Contains (q + BitVec.ofNat 64 (16*i)) 16 := Offset.contains_base q (by omega_using [hi]) (by omega_using [hi])

/-- `q8`–`q15` saved at `q`. -/
def Saved (s₀ : State) (q : Addr) (m : Mem) : Prop :=
  ∀ i < 8, m.read (q + BitVec.ofNat 64 (16*i)) 16 = s₀.v (vreg (8+i))

/-- What the function changes, and where. -/
structure Keeps (p q : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x16 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [pairR p, scrR q] s.mem s'.mem
  vlow : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem save_ok {s : State} {q : Addr} (hq : s.gpr .x1 = q)
    (hw : ∀ i < 8, InRegions s.wr (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block save) s fun s' => s'.gpr = s.gpr ∧ s'.v = s.v ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [scrR q] s.mem s'.mem ∧ Saved s q s'.mem := by
  refine wp_range_flatMap (M := isa)
    (fun k s' => s'.gpr = s.gpr ∧ s'.v = s.v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [scrR q] s.mem s'.mem ∧
      ∀ i < k, s'.mem.read (q + BitVec.ofNat 64 (16*i)) 16 = s.v (vreg (8+i)))
    (fun k u hk ⟨hg,hv,hr,hwr,hsp,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨rfl,rfl,rfl,rfl,rfl,Frame.refl _ _,fun _ h => absurd h (by omega_using [])⟩
  unfold saveReg
  refine WP.cons (exec_strq ⟨by omega_using [],by omega_using [hk]⟩ (by rw [hwr,hg,hq]; exact hw k hk))
    (WP.block_nil_iff.mpr ⟨hg,hv,hr,hwr,hsp,?_,fun i hi => ?_⟩)
  · change Frame _ _ (u.mem.write _ 16 _)
    rw [hg,hq]
    exact hf.write (List.mem_singleton_self _) _ (scr_contains q hk)
  · change (u.mem.write _ 16 _).read _ 16 = _
    rw [hg,hq,hv]
    by_cases he : i = k
    · subst i
      exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep _ (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])) (by decide)]
      exact hvals i (by omega_using [hi, he])

theorem restore_ok {s₀ s : State} {q : Addr} (hq : s.gpr .x1 = q) (hs : Saved s₀ q s.mem)
    (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 := by
  have hh : WP isa (.block restore) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ i < 8, s'.v (vreg (8+i)) = s₀.v (vreg (8+i)) := by
    refine wp_range_flatMap (M := isa)
      (fun k s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        ∀ i < k, s'.v (vreg (8+i)) = s₀.v (vreg (8+i)))
      (fun k u hk ⟨hg,hm,hr,hwr,hsp,hvals⟩ => ?_) 8 (Nat.le_refl _) s
      ⟨rfl,rfl,rfl,rfl,rfl,fun _ h => absurd h (by omega_using [])⟩
    unfold restoreReg
    refine WP.cons (exec_ldrq ⟨by omega_using [],by omega_using [hk]⟩ ?_) (WP.block_nil ?_)
    · rw [hr,hwr,hg,hq]; exact hin k hk
    refine ⟨by rw [RegUpd.gpr_setV,hg],by rw [RegUpd.mem_setV,hm],by rw [RegUpd.rd_setV,hr],
      by rw [RegUpd.wr_setV,hwr],by rw [RegUpd.sp_setV,hsp],fun i hi => ?_⟩
    rw [RegUpd.v_setV]
    simp only [vreg_inj (8+i) (by omega_using [hk, hi]) (8+k) (by omega_using [hk]),Nat.add_left_cancel_iff]
    by_cases he : i = k
    · subst i
      simp only [ite_true,hm,hg,hq]
      exact hs k hk
    · rw [ite_eq_right (by omega_using [he])]
      exact hvals i (by omega_using [hi, he])
  refine hh.mono fun s' ⟨hg,hm,hr,hwr,hsp,hv⟩ => ⟨hg,hm,hr,hwr,hsp,fun r hr' => ?_⟩
  have hv' : ∀ r ∈ preservedV, ∃ i : Fin 8, r = vreg (8+i.val) := by decide
  obtain ⟨i,rfl⟩ := hv' r hr'
  exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv i.val i.isLt)

/-- `vg_keccak_f1600_x2_sha3`, from the states at `p` (`x0`) and its working space at `q` (`x1`). -/
theorem vector_ok {s : State} {p q : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x0 = p) (hq : s.gpr .x1 = q) (hpq : (pairR p).Disjoint (scrR q))
    (hpair : PairAt s.mem p A B)
    (hwp : ∀ i < 25, InRegions s.wr (wordAddr p i) 16)
    (hwq : ∀ i < 8, InRegions s.wr (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa vector s fun t => Keeps p q s t ∧ PairAt t.mem p (keccakF A) (keccakF B) := by
  have hall : ∀ {a : Addr} {n : Nat}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n :=
    fun ⟨r,hr,hc⟩ => ⟨r,List.mem_append.mpr (.inr hr),hc⟩
  unfold vector
  rw [WP.seq_iff,WP.block_append_iff]
  refine (save_ok hq hwq).mono fun s₁ ⟨g₁,v₁,r₁,w₁,sp₁,f₁,sv₁⟩ => ?_
  have hpair₁ : PairAt s₁.mem p A B := fun i hi => by
    rw [f₁.read (pair_contains p hi) (by simpa using hpq) (by decide)]; exact hpair i hi
  refine (load_ok (by rw [g₁,hp]) hpair₁ (fun i hi => by rw [r₁,w₁]; exact hall (hwp i hi))).mono
    fun s₂ ⟨c₂,ps₂⟩ => ?_
  refine WP.seq (WP.mono (roundsProg_ok (by decide : 24 ≤ 24) ps₂) fun s₃ ⟨k₃,ps₃⟩ => ?_)
  rw [WP.block_append_iff]
  have gp₃ : ∀ r, r ≠ .x16 → s₃.gpr r = s.gpr r := fun r h => by rw [k₃.gpr r h,c₂.gpr,g₁]
  refine (store_ok (p := p) (by rw [gp₃ .x0 (by decide),hp]) ps₃
    (fun i hi => by rw [k₃.wr,c₂.wr,w₁]; exact hwp i hi)).mono fun s₄ ⟨m₄,pa₄,f₄⟩ => ?_
  have sv₄ : Saved s q s₄.mem := fun i hi => by
    rw [f₄.read (scr_contains q hi) (by simpa using hpq.symm) (by decide),k₃.mem,c₂.mem]
    exact sv₁ i hi
  refine (restore_ok (s₀ := s) (by rw [m₄.gpr,gp₃ .x1 (by decide),hq]) sv₄
    (fun i hi => by rw [m₄.rd,m₄.wr,k₃.rd,k₃.wr,c₂.rd,c₂.wr,r₁,w₁]; exact hall (hwq i hi))).mono
    fun t ⟨g₅,m₅,r₅,w₅,sp₅,v₅⟩ => ⟨⟨fun r h => by rw [g₅,m₄.gpr,gp₃ r h],
      by rw [r₅,m₄.rd,k₃.rd,c₂.rd,r₁], by rw [w₅,m₄.wr,k₃.wr,c₂.wr,w₁],
      by rw [sp₅,m₄.sp,k₃.sp,c₂.sp,sp₁], ?_, v₅⟩, by rw [m₅]; exact pa₄⟩
  rw [m₅,m₄.mem]
  refine (f₁.mono (fun r hr => ?_)).trans ?_
  · simp only [List.mem_singleton] at hr; subst r; simp
  · rw [← c₂.mem,← k₃.mem]
    exact f₄.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst r; simp)

/-! ## Without a CPU feature: the scalar rounds on each state in turn -/

/-- Lane `i` of state `k` of the two at `p` is in the states' region. -/
theorem lane_contains (p : Addr) {i k : Nat} (hi : i < 25) (hk : k < 2) :
    (pairR p).Contains (p + BitVec.ofNat 64 (16 * i + 8 * k)) 8 :=
  Offset.contains_base p (by omega_using [hi, hk]) (by omega_using [hi, hk])

theorem stateX2At_lane (m : Mem) (p : Addr) (k : Nat) {i : Nat} (hi : i < 25) :
    (stateX2At m p k)[i] = m.readW (p + BitVec.ofNat 64 (16 * i + 8 * k)) 64 := by
  simp only [stateX2At, Vector.getElem_ofFn]
  rw [show 8 * (2 * i + k) = 16 * i + 8 * k by omega_arith]

theorem stateX2At_eq {m : Mem} {p : Addr} {k : Nat} {A : Spec.Sha3.State}
    (h : ∀ i (hi : i < 25), m.readW (p + BitVec.ofNat 64 (16 * i + 8 * k)) 64 = A[i]) :
    stateX2At m p k = A :=
  Vector.ext fun i hi => (stateX2At_lane m p k hi).trans (h i hi)

/-- A state of the two at `p`, after writes elsewhere. -/
theorem stateX2At_frame {m m' : Mem} {p : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (pairR p).Disjoint r) {k : Nat} (hk : k < 2) :
    stateX2At m' p k = stateX2At m p k :=
  stateX2At_eq fun i hi => (hf.readW (lane_contains p hi hk) hd (by decide)).trans
    (stateX2At_lane m p k hi).symm

/-- The lanes of state `k` of the two at `p` (`x30`), to their registers. -/
theorem loadLanes_ok {k : Nat} (hk : k < 2) (s₀ : State) {p : Addr} (hb : s₀.gpr .x30 = p)
    (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 (16 * i + 8 * k)) 8) :
    WP isa (.block (loadLanes k)) s₀ fun s' => Boundary.Keep s₀ s' ∧ s'.mem = s₀.mem ∧
      s'.v = s₀.v ∧ Boundary.Lanes s' (stateX2At s₀.mem p k) := by
  unfold loadLanes
  rw [List.map_eq_flatMap]
  refine (wp_range_flatMap (M := isa)
    (fun j s => Boundary.Keep s₀ s ∧ s.mem = s₀.mem ∧ s.v = s₀.v ∧ s.gpr .x30 = p ∧
      ∀ i < j, s.gpr (laneReg i) = s₀.mem.readW (p + BitVec.ofNat 64 (16 * i + 8 * k)) 64)
    (fun i s hi ⟨hkeep,hm,hv,hx,hl⟩ => ?_) 25 (Nat.le_refl _) s₀
    ⟨⟨rfl,rfl,rfl⟩,rfl,rfl,hb,fun _ h => absurd h (by omega_using [])⟩).mono
    fun s ⟨hkeep,hm,hv,_,hl⟩ => ⟨hkeep,hm,hv,fun i hi =>
      (hl i hi).trans (stateX2At_lane _ _ _ hi).symm⟩
  · refine WP.cons (exec_ldr_x ⟨by omega_using [],by omega_using [hi, hk]⟩ ?_) (WP.block_nil ?_)
    · rw [hkeep.rd,hkeep.wr,hx]
      exact hin i hi
    · refine ⟨⟨hkeep.rd,hkeep.wr,hkeep.sp⟩,hm,hv,?_,fun j hj => ?_⟩
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          Ne.symm (Boundary.laneReg_ne_x30 i hi),ite_false,hx]
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          Boundary.laneReg_inj j (by omega_using [hi, hj]) i hi]
        split
        · rename_i he; subst j
          rw [hm,hx]
        · exact hl j (by omega_arith)

/-- The lanes, from their registers to state `k` of the two at `p` (the
pointer kept in `v30`): the other state stays. -/
theorem storeLanes_ok {k : Nat} (hk : k < 2) (s₀ : State) {p : Addr} (A : Spec.Sha3.State)
    (hA : Boundary.Lanes s₀ A) (hptr : vdword (s₀.v .v30) 0 = p)
    (hin : ∀ i < 25, InRegions s₀.wr (p + BitVec.ofNat 64 (16 * i + 8 * k)) 8) :
    WP isa (.block (storeLanes k)) s₀ fun s' => Boundary.Keep s₀ s' ∧ s'.v = s₀.v ∧
      s'.gpr .x30 = p ∧ Frame [pairR p] s₀.mem s'.mem ∧ stateX2At s'.mem p k = A ∧
      stateX2At s'.mem p (1 - k) = stateX2At s₀.mem p (1 - k) := by
  change (s₀.v .v30).extractLsb' (64*0) 64 = p at hptr
  unfold storeLanes
  rw [List.singleton_append]
  refine WP.cons rfl ?_
  rw [List.map_eq_flatMap]
  refine (wp_range_flatMap (M := isa)
    (fun j s => Boundary.Keep s₀ s ∧ s.v = s₀.v ∧ s.gpr .x30 = p ∧ Boundary.Lanes s A ∧
      Frame [pairR p] s₀.mem s.mem ∧
      (∀ i < j, ∀ h25 : i < 25, s.mem.readW (p + BitVec.ofNat 64 (16 * i + 8 * k)) 64 = A[i]) ∧
      ∀ i < 25, s.mem.readW (p + BitVec.ofNat 64 (16 * i + 8 * (1 - k))) 64 =
        s₀.mem.readW (p + BitVec.ofNat 64 (16 * i + 8 * (1 - k))) 64)
    (fun i s hi ⟨hkeep,hv,hx,hl,hf,hvals,ho⟩ => ?_) 25 (Nat.le_refl _)
    (s₀.write .x .x30 ((s₀.v .v30).extractLsb' (64*0) 64))
    ⟨⟨rfl,rfl,rfl⟩,rfl,?_,?_,Frame.refl _ _,fun _ h => absurd h (by omega_using []),fun _ _ => rfl⟩).mono
    fun s ⟨hkeep,hv,hx,_,hf,hvals,ho⟩ => ⟨hkeep,hv,hx,hf,stateX2At_eq fun i hi => hvals i hi hi,
      stateX2At_eq fun i hi => (ho i hi).trans (stateX2At_lane _ _ _ hi).symm⟩
  · simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr
  · intro i hi
    simpa only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,Boundary.laneReg_ne_x30 i hi,ite_false]
      using hA i hi
  · refine WP.cons (exec_str_x ⟨by omega_using [],by omega_using [hi, hk]⟩ ?_) (WP.block_nil ?_)
    · rw [hkeep.wr,hx]
      exact hin i hi
    · refine ⟨⟨hkeep.rd,hkeep.wr,hkeep.sp⟩,hv,hx,hl,?_,fun j hj h25 => ?_,fun j hj => ?_⟩
      · change Frame _ _ (s.mem.writeW _ _)
        rw [hx]
        exact hf.writeW (List.mem_singleton_self _) _ (lane_contains p hi hk)
      · change (s.mem.writeW _ _).readW _ 64 = _
        rw [hx]
        by_cases he : j = i
        · subst j
          rw [Mem.readW_writeW_self64]
          exact hl i hi
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he]) (by omega_using [h25, hk])
            (by omega_using [hi, hk])) (by decide)]
          exact hvals j (by omega_using [hj, he]) h25
      · change (s.mem.writeW _ _).readW _ 64 = _
        rw [hx, Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hk]) (by omega_using [hj, hk])
          (by omega_using [hi, hk])) (by decide)]
        exact ho j hj

/-- The scalar functions' first block: the registers saved, and the lanes of
state 0 of the two at `p` (`x0`) in their registers. -/
theorem scalarFirst_ok {s : State} {p : Addr} (hp : s.gpr .x0 = p)
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * i + 8 * 0)) 8) :
    WP isa (.block (Impl.Sha3.AArch64.Scalar.Boundary.save ++
      ([.addImm .x .x30 .x0 0] : List Instr) ++ loadLanes 0)) s fun t =>
      Boundary.CoreState s (stateX2At s.mem p 0) t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff,WP.block_append_iff]
  refine (Scalar.Boundary.save_ok s).mono fun s₁ ⟨k₁,g₁,m₁,sv₁,pt₁,v₁⟩ => ?_
  refine WP.cons (exec_addImm_x (by decide)) (WP.block_nil ?_)
  refine (loadLanes_ok (k := 0) (by decide) _ (p := p) ?_ ?_).mono fun s₂ ⟨k₂,m₂,v₂,l₂⟩ => ?_
  · simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
      show BitVec.ofNat 64 0 = 0 by rfl,g₁,hp]
    exact BitVec.add_zero _
  · intro i hi
    change InRegions (s₁.rd ++ s₁.wr) _ _
    rw [k₁.rd,k₁.wr]
    exact hin i hi
  have v₂' : s₂.v = s₁.v := v₂
  exact ⟨⟨⟨k₂.rd.trans k₁.rd,k₂.wr.trans k₁.wr,k₂.sp.trans k₁.sp⟩,
      by simpa only [Scalar.Boundary.Ptrs,v₂'] using pt₁,
      fun i hi => by rw [v₂']; exact sv₁ i hi,fun r hr => by rw [v₂']; exact v₁ r hr,
      by rw [← m₁]; exact l₂⟩,m₂.trans m₁⟩

/-- Between two runs of the rounds: the lanes to state 0 of the two at `p`,
and state 1's to the registers. -/
theorem scalarNext_ok {s u : State} {p : Addr} {A : Spec.Sha3.State} (hp : s.gpr .x0 = p)
    (hc : Boundary.CoreState s A u)
    (hw : ∀ i < 25, InRegions s.wr (p + BitVec.ofNat 64 (16 * i + 8 * 0)) 8)
    (hr : ∀ i < 25, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * i + 8 * 1)) 8) :
    WP isa (.block (storeLanes 0 ++ loadLanes 1)) u fun t =>
      Boundary.CoreState s (stateX2At u.mem p 1) t ∧ Frame [pairR p] u.mem t.mem ∧
        stateX2At t.mem p 0 = A := by
  rw [WP.block_append_iff]
  refine (storeLanes_ok (k := 0) (by decide) u (p := p) _ hc.lanes (hc.ptrs.1.trans hp)
    (fun i hi => by rw [hc.keep.wr]; exact hw i hi)).mono fun s₄ ⟨k₄,v₄,x₄,f₄,a₄,b₄⟩ => ?_
  refine (loadLanes_ok (k := 1) (by decide) s₄ x₄ (fun i hi => by
    rw [k₄.rd,k₄.wr,hc.keep.rd,hc.keep.wr]; exact hr i hi)).mono fun s₅ ⟨k₅,m₅,v₅,l₅⟩ => ?_
  have b₄' : stateX2At s₄.mem p 1 = stateX2At u.mem p 1 := b₄
  exact ⟨⟨⟨k₅.rd.trans (k₄.rd.trans hc.keep.rd),k₅.wr.trans (k₄.wr.trans hc.keep.wr),
        k₅.sp.trans (k₄.sp.trans hc.keep.sp)⟩,
      by simpa only [Scalar.Boundary.Ptrs,v₅,v₄] using hc.ptrs,
      fun i hi => by rw [v₅,v₄]; exact hc.saved i hi,fun r hr => by rw [v₅,v₄]; exact hc.vec r hr,
      by rw [← b₄']; exact l₅⟩,by rw [m₅]; exact f₄,by rw [m₅]; exact a₄⟩

/-- `vg_keccak_f1600_x2`, from the states at `p` (`x0`): it writes only them. -/
theorem scalar_ok {s : State} {p : Addr} (hp : s.gpr .x0 = p)
    (hwp : ∀ i < 25, ∀ k < 2, InRegions s.wr (p + BitVec.ofNat 64 (16 * i + 8 * k)) 8) :
    WP isa scalar s fun t => abiPreserved s t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [pairR p] s.mem t.mem ∧ stateX2At t.mem p 0 = keccakF (stateX2At s.mem p 0) ∧
      stateX2At t.mem p 1 = keccakF (stateX2At s.mem p 1) := by
  have hall : ∀ {a : Addr} {n : Nat}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n :=
    fun ⟨r,hr,hc⟩ => ⟨r,List.mem_append.mpr (.inr hr),hc⟩
  unfold scalar
  rw [WP.seq_iff]
  refine (scalarFirst_ok hp fun i hi => hall (hwp i hi 0 (by decide))).mono fun s₂ ⟨c₂,m₂⟩ => ?_
  refine WP.seq (WP.mono (Scalar.Lazy.core_state_keep s _ s₂ c₂) fun s₃ ⟨c₃,r₃⟩ => ?_)
  have m₃ : s₃.mem = s.mem := r₃.mem.trans m₂
  rw [WP.seq_iff]
  refine (scalarNext_ok hp c₃ (fun i hi => hwp i hi 0 (by decide))
    fun i hi => hall (hwp i hi 1 (by decide))).mono fun s₅ ⟨c₅,f₅,a₅⟩ => ?_
  rw [m₃] at c₅ f₅
  refine WP.seq (WP.mono (Scalar.Lazy.core_state_keep s _ s₅ c₅) fun s₆ ⟨c₆,r₆⟩ => ?_)
  rw [WP.block_append_iff]
  refine (storeLanes_ok (k := 1) (by decide) s₆ (p := p) _ c₆.lanes (c₆.ptrs.1.trans hp)
    (fun i hi => by rw [c₆.keep.wr]; exact hwp i hi 1 (by decide))).mono
    fun s₇ ⟨k₇,v₇,_,f₇,a₇,b₇⟩ => ?_
  have b₇' : stateX2At s₇.mem p 0 = keccakF (stateX2At s.mem p 0) := by rw [← a₅,← r₆.mem]; exact b₇
  refine (Scalar.Boundary.restore_ok s s₇ (fun i hi => by rw [v₇]; exact c₆.saved i hi)).mono
    fun t ⟨k₈,m₈,v₈,g₈⟩ => ⟨⟨g₈,k₈.sp.trans (k₇.sp.trans c₆.keep.sp),fun r hr => by
      rw [v₈,v₇,c₆.vec r hr]⟩,k₈.rd.trans (k₇.rd.trans c₆.keep.rd),
      k₈.wr.trans (k₇.wr.trans c₆.keep.wr),?_,by rw [m₈]; exact b₇',by rw [m₈]; exact a₇⟩
  rw [m₈]
  rw [r₆.mem] at f₇
  exact f₅.trans f₇

/-! ## The contract -/

/-- Lane `i` of state `k` of the two interleaved at `p`. -/
theorem stateX2At_get (m : Mem) (p : Addr) (k : Nat) {i : Nat} (hi : i < 25) :
    (stateX2At m p k)[i]! = m.readW (p + BitVec.ofNat 64 (8 * (2 * i + k))) 64 := by
  rw [getElem!_pos (stateX2At m p k) i hi]
  simp only [stateX2At, Vector.getElem_ofFn]

/-- The interleaved states, as the two-lane code's pairs. -/
theorem pairAt_stateX2 (m : Mem) (p : Addr) : PairAt m p (stateX2At m p 0) (stateX2At m p 1) := by
  intro i hi
  rw [stateX2At_get m p 0 hi,stateX2At_get m p 1 hi,read16_dwords]
  unfold wordAddr
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8 * (2 * i + 0) = 16 * i by omega_using [],
    show 8 * (2 * i + 1) = 16 * i + 8 by omega_using []]

/-- The pairs, as the interleaved states. -/
theorem stateX2_of_pairAt {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) :
    stateX2At m p 0 = A ∧ stateX2At m p 1 = B := by
  have hk : ∀ k < 2, ∀ i < 25, m.readW (p + BitVec.ofNat 64 (8 * (2 * i + k))) 64 =
      vdword (ofVDwords A[i]! B[i]!) k := fun k hk i hi => by
    rw [← h i hi,vdword_read16 _ _ hk]
    unfold wordAddr
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 16 * i + 8 * k = 8 * (2 * i + k) by omega_using []]
  refine ⟨Vector.ext fun i hi => ?_,Vector.ext fun i hi => ?_⟩
  · rw [← getElem!_pos (stateX2At m p 0) i hi,← getElem!_pos A i hi,stateX2At_get m p 0 hi,
      hk 0 (by decide) i hi,vdword_ofVDwords_0]
  · rw [← getElem!_pos (stateX2At m p 1) i hi,← getElem!_pos B i hi,stateX2At_get m p 1 hi,
      hk 1 (by decide) i hi,vdword_ofVDwords_1]

/-- The contract on the states at `x0` and the working space at `x1`. -/
def K : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pairR (s.gpr .x0), scrR (s.gpr .x1)] ∧
    (pairR (s.gpr .x0)).Disjoint (scrR (s.gpr .x1))
  post s s' := stateX2At s'.mem (s.gpr .x0) 0 = keccakF (stateX2At s.mem (s.gpr .x0) 0) ∧
    stateX2At s'.mem (s.gpr .x0) 1 = keccakF (stateX2At s.mem (s.gpr .x0) 1)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

theorem in_pair {s : State} (hw : s.wr = [pairR (s.gpr .x0), scrR (s.gpr .x1)]) {i : Nat} (hi : i < 25) :
    InRegions s.wr (wordAddr (s.gpr .x0) i) 16 := ⟨_,by rw [hw]; simp,pair_contains _ hi⟩

theorem in_scr {s : State} (hw : s.wr = [pairR (s.gpr .x0), scrR (s.gpr .x1)]) {i : Nat} (hi : i < 8) :
    InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 := ⟨_,by rw [hw]; simp,scr_contains _ hi⟩

/-- From `K`'s precondition, `vector_ok`'s postcondition. -/
theorem wp_K {s : State} (hs : K.pre s) :
    WP isa vector s fun t => Keeps (s.gpr .x0) (s.gpr .x1) s t ∧ K.post s t := by
  obtain ⟨_,hw,hd⟩ := hs
  refine (vector_ok rfl rfl hd (pairAt_stateX2 _ _) (fun i hi => in_pair hw hi)
    (fun i hi => in_scr hw hi)).mono fun t ⟨hk,ht⟩ => ⟨hk,?_⟩
  obtain ⟨h0,h1⟩ := stateX2_of_pairAt ht
  exact ⟨h0,h1⟩

theorem code_true : code true = vector := rfl
theorem code_false : code false = scalar := rfl

theorem correct (sha3 : Bool) (s : State) (hs : K.pre s) :
    ∃ tr t, Exec isa (code sha3) s tr t ∧ abiPreserved s t ∧ K.post s t := by
  cases sha3
  · rw [code_false]
    obtain ⟨tr,t,he,habi,_,_,_,h0,h1⟩ := scalar_ok (s := s) rfl fun i hi k hk =>
      ⟨_,by rw [hs.2.1]; simp,lane_contains _ hi hk⟩
    exact ⟨tr,t,he,habi,h0,h1⟩
  · rw [code_true]
    obtain ⟨tr,t,he,hk,hp⟩ := wp_K hs
    exact ⟨tr,t,he,⟨fun r hr => hk.gpr r (by revert hr; cases r <;> decide),hk.sp,hk.vlow⟩,hp⟩

theorem ct (sha3 : Bool) : ConstantTime isa K.pre K.pub (code sha3) := by
  have agree : ∀ s₁ s₂ : State, K.pre s₁ → K.pre s₂ → K.pub s₁ s₂ →
      AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1]) s₁ s₂ := by
    intro s₁ s₂ _ _ ⟨h1,h2,hsp⟩
    refine ⟨hsp,fun r hr => ?_⟩
    simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  cases sha3
  · exact VectorTaint.constantTime (AArch64.Taint.ofRegs [.x0,.x1]) agree (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (AArch64.Taint.ofRegs [.x0,.x1]) agree (by taint_decide)

/-- A state the precondition holds in. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 400⟩, ⟨0x2000, 128⟩]

theorem verified (sha3 : Bool) :
    Verified AArch64.target (code sha3) (Proof.Sha3.permuteX2Contract AArch64.abi) :=
  Verified.of_correct (correct sha3) (ct sha3) (by
    sig_implies [Proof.Sha3.permuteX2Contract, Proof.Sha3.permuteX2Sig, K, pairR, scrR,
      AArch64.abi, AArch64.argRegs] [satState] using satState)


end VG.Proof.Sha3.AArch64.Neon.X2
