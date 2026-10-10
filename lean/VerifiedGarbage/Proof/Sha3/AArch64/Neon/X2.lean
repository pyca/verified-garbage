import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
import VerifiedGarbage.Proof.Framework.Sig

/-!
# `vg_keccak_f1600_x2` on AArch64

Untrusted: everything here is checked by Lean. `code_ok`: from the states at
`x0` (`PairAt`, the layout of the inlined two-lane code) and 128 bytes of
working space at `x1`, the function saves `q8`–`q15` there, runs the inlined
code's load, rounds (`roundsProg_ok`) and store, and restores `q8`–`q15`;
it changes nothing else but `x16`, the vector registers and those two
regions. `verified`: its contract (`Spec/Sha3/X2.lean`), from `PairAt` of the
states read as two `stateX2At`.
-/

namespace VG.Proof.Sha3.AArch64.Neon.X2

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg save restore saveReg restoreReg)
open VG.Impl.Sha3.AArch64.Neon.X2 (code)
open VG.Proof.Sha3.AArch64.Sha3.Vector (exec_strq exec_ldrq read_write16 vreg_inj CoreKeep)
open VG.Spec.Sha3 (stateX2At keccakF)

/-- The function's working space. -/
def scrR (q : Addr) : Region := ⟨q, 128⟩

theorem scr_contains (q : Addr) {i : Nat} (hi : i < 8) :
    (scrR q).Contains (q + BitVec.ofNat 64 (16*i)) 16 := Offset.contains_base q (by omega) (by omega)

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
    ⟨rfl,rfl,rfl,rfl,rfl,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
  unfold saveReg
  refine WP.cons (exec_strq ⟨by omega,by omega⟩ (by rw [hwr,hg,hq]; exact hw k hk))
    (WP.block_nil_iff.mpr ⟨hg,hv,hr,hwr,hsp,?_,fun i hi => ?_⟩)
  · change Frame _ _ (u.mem.write _ 16 _)
    rw [hg,hq]
    exact hf.write (List.mem_singleton_self _) _ (scr_contains q hk)
  · change (u.mem.write _ 16 _).read _ 16 = _
    rw [hg,hq,hv]
    by_cases he : i = k
    · subst i
      exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hvals i (by omega)

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
      ⟨rfl,rfl,rfl,rfl,rfl,fun _ h => absurd h (by omega)⟩
    unfold restoreReg
    refine WP.cons (exec_ldrq ⟨by omega,by omega⟩ ?_) (WP.block_nil ?_)
    · rw [hr,hwr,hg,hq]; exact hin k hk
    refine ⟨by rw [RegUpd.gpr_setV,hg],by rw [RegUpd.mem_setV,hm],by rw [RegUpd.rd_setV,hr],
      by rw [RegUpd.wr_setV,hwr],by rw [RegUpd.sp_setV,hsp],fun i hi => ?_⟩
    rw [RegUpd.v_setV]
    simp only [vreg_inj (8+i) (by omega) (8+k) (by omega),Nat.add_left_cancel_iff]
    by_cases he : i = k
    · subst i
      simp only [ite_true,hm,hg,hq]
      exact hs k hk
    · rw [ite_eq_right (by omega)]
      exact hvals i (by omega)
  refine hh.mono fun s' ⟨hg,hm,hr,hwr,hsp,hv⟩ => ⟨hg,hm,hr,hwr,hsp,fun r hr' => ?_⟩
  have hv' : ∀ r ∈ preservedV, ∃ i : Fin 8, r = vreg (8+i.val) := by decide
  obtain ⟨i,rfl⟩ := hv' r hr'
  exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv i.val i.isLt)

/-- The function, from the states at `p` (`x0`) and its working space at `q` (`x1`). -/
theorem code_ok (sha3 : Bool) {s : State} {p q : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x0 = p) (hq : s.gpr .x1 = q) (hpq : (pairR p).Disjoint (scrR q))
    (hpair : PairAt s.mem p A B)
    (hwp : ∀ i < 25, InRegions s.wr (wordAddr p i) 16)
    (hwq : ∀ i < 8, InRegions s.wr (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (code sha3) s fun t => Keeps p q s t ∧ PairAt t.mem p (keccakF A) (keccakF B) := by
  have hall : ∀ {a : Addr} {n : Nat}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n :=
    fun ⟨r,hr,hc⟩ => ⟨r,List.mem_append.mpr (.inr hr),hc⟩
  unfold code
  rw [WP.seq_iff,WP.block_append_iff]
  refine (save_ok hq hwq).mono fun s₁ ⟨g₁,v₁,r₁,w₁,sp₁,f₁,sv₁⟩ => ?_
  have hpair₁ : PairAt s₁.mem p A B := fun i hi => by
    rw [f₁.read (pair_contains p hi) (by simpa using hpq) (by decide)]; exact hpair i hi
  refine (load_ok (by rw [g₁,hp]) hpair₁ (fun i hi => by rw [r₁,w₁]; exact hall (hwp i hi))).mono
    fun s₂ ⟨c₂,ps₂⟩ => ?_
  refine WP.seq (WP.mono (roundsProg_ok sha3 (by decide : 24 ≤ 24) ps₂) fun s₃ ⟨k₃,ps₃⟩ => ?_)
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
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8 * (2 * i + 0) = 16 * i by omega,
    show 8 * (2 * i + 1) = 16 * i + 8 by omega]

/-- The pairs, as the interleaved states. -/
theorem stateX2_of_pairAt {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) :
    stateX2At m p 0 = A ∧ stateX2At m p 1 = B := by
  have hk : ∀ k < 2, ∀ i < 25, m.readW (p + BitVec.ofNat 64 (8 * (2 * i + k))) 64 =
      vdword (ofVDwords A[i]! B[i]!) k := fun k hk i hi => by
    rw [← h i hi,vdword_read16 _ _ hk]
    unfold wordAddr
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 16 * i + 8 * k = 8 * (2 * i + k) by omega]
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

/-- From `K`'s precondition, `code_ok`'s postcondition. -/
theorem wp_K (sha3 : Bool) {s : State} (hs : K.pre s) :
    WP isa (code sha3) s fun t => Keeps (s.gpr .x0) (s.gpr .x1) s t ∧ K.post s t := by
  obtain ⟨_,hw,hd⟩ := hs
  refine (code_ok sha3 rfl rfl hd (pairAt_stateX2 _ _) (fun i hi => in_pair hw hi)
    (fun i hi => in_scr hw hi)).mono fun t ⟨hk,ht⟩ => ⟨hk,?_⟩
  obtain ⟨h0,h1⟩ := stateX2_of_pairAt ht
  exact ⟨h0,h1⟩

theorem correct (sha3 : Bool) (s : State) (hs : K.pre s) :
    ∃ tr t, Exec isa (code sha3) s tr t ∧ abiPreserved s t ∧ K.post s t := by
  obtain ⟨tr,t,he,hk,hp⟩ := wp_K sha3 hs
  exact ⟨tr,t,he,⟨fun r hr => hk.gpr r (by revert hr; cases r <;> decide),hk.sp,hk.vlow⟩,hp⟩

theorem ct (sha3 : Bool) : ConstantTime isa K.pre K.pub (code sha3) := by
  cases sha3 <;> refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) ?_
    (by taint_decide) <;>
  intro s₁ s₂ _ _ ⟨h1,h2,hsp⟩ <;>
  refine ⟨hsp,fun r hr => ?_⟩ <;>
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr <;>
  rcases hr with rfl | rfl <;> with_reducible assumption

/-- A state the precondition holds in. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 400⟩, ⟨0x2000, 128⟩]

theorem verified (sha3 : Bool) :
    Verified AArch64.target (code sha3) (Spec.Sha3.permuteX2Contract AArch64.abi) :=
  Verified.of_correct (correct sha3) (ct sha3) (by
    sig_implies [Spec.Sha3.permuteX2Contract, Spec.Sha3.permuteX2Sig, K, pairR, scrR,
      AArch64.abi, AArch64.argRegs] [satState] using satState)

#assert_standard_axioms verified

end VG.Proof.Sha3.AArch64.Neon.X2
