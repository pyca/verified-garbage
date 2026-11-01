module

public import VerifiedGarbage.Proof.P256.VerifyTable.Copies
public import VerifiedGarbage.Proof.P256.VerifyTable.StoreInv
import VerifiedGarbage.Proof.P256.EcdhJac.Masks
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! The co-Z table's build on the field invariant: the environment after each
phase, as a function of the one before it. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- `E = Q`, `Z² = Z³ = 1`. -/
def l1 : List (Nat × Nat) := [(704,1280),(736,1440),(768,224),(5400,224),(5432,224)]
/-- `D = 2Q` and `E = Q` at the same `Z`. -/
def l2 : List (Nat × Nat) := [(608,704),(640,736),(704,896),(736,864)]
/-- `2Q` into entry 9 and `D`, `R = E`. -/
def l4 : List (Nat × Nat) := [(3616,608),(3648,640),(3680,768),(672,768),(512,704),(544,736),(576,768)]

/-- The read-only inputs: `a`, `b3`, the zero, and `Q` with `Z = 1`. -/
def V0 : List Nat := [256,288,160,1280,1440,224]
/-- The co-Z state: `D`, `E` and the powers of its `Z`. -/
def W : List Nat := [608,640,704,736,768,5400,5432]
/-- The slots of the first `n` entries. -/
def entries (n : Nat) : List Nat := (List.range n).flatMap fun a => dsts (a+1)
def Vl (k : Nat) : List Nat := W ++ entries (k+1) ++ V0

/-- What the build writes. -/
def buildW : List (Nat × Nat) := Proof.P256.EcdhJac.work ++ [(2848,864),(6000,512)]
def regs : List Reg := .x19 :: allocatedRegs

def ops (doubling : Bool) : List FOp := Impl.P256.EcdhTable.operations doubling

def startEnv {F : Type _} (E : Nat → F) : Nat → F := storeEnv 1 (copiesEnv l1 E)
def dbluEnv {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) : Nat → F :=
  copiesEnv l2 (runOps (ops true) (startEnv E))
def stepEnv {F : Type _} [Lean.Grind.CommRing F] (m : Nat) (E : Nat → F) : Nat → F :=
  storeEnv m (runOps (ops false) E)
def loopEnv {F : Type _} [Lean.Grind.CommRing F] : Nat → (Nat → F) → Nat → F
  | 0, E => E
  | k+1, E => stepEnv (k+2) (loopEnv k E)
def buildEnv {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) : Nat → F :=
  copiesEnv l4 (loopEnv 7 (dbluEnv E))

/-- The slots the build names. -/
def buildSlots : List Nat := slots ++ entries 8 ++ [3616,3648,3680,512,544,576,672] ++ V0

theorem mem_entries {n x : Nat} : x∈entries n ↔ ∃ a<n,∃ j<5,x=dst (a+1) j := by
  simp only [entries,dsts,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨a,ha,j,hj,rfl⟩; exact ⟨a,ha,j,hj,rfl⟩
  · rintro ⟨a,ha,j,hj,rfl⟩; exact ⟨a,ha,j,hj,rfl⟩

theorem entries_succ (n : Nat) : entries (n+1)=entries n ++ dsts (n+1) := by
  simp only [entries,List.range_succ,List.flatMap_append,List.flatMap_singleton]

theorem dst_slot {Sl : Nat → Prop} (hs : ∀ x∈buildSlots,Sl x) {m j : Nat} (hm : 1≤m) (hm8 : m≤8)
    (hj : j<5) : Sl (dst m j) := by
  apply hs
  have h : ∀ a<8,∀ j<5,dst (a+1) j∈buildSlots := by decide
  have := h (m-1) (by omega) j hj
  rwa [show m-1+1=m by omega] at this

theorem entries_obs {n : Nat} (hn : n≤9) {x : Nat} (hx : x∈entries n) (d : Bool) :
    ∀ i<4,observe d (x+8*i) := by
  obtain ⟨a,ha,j,hj,rfl⟩ := mem_entries.mp hx
  have h : ∀ d : Bool,∀ a<9,∀ j<5,∀ i<4,observe d (dst (a+1) j+8*i) := by decide
  exact h d a (by omega) j hj

theorem store_frame {base : Addr} {s t : State} {m : Nat} (hm : 1≤m) (hm8 : m≤8)
    (k : KeepRegs [.x1,.x2,.x16] s t)
    (u : Unch base [(2848+96*(m-1),96),(6000+64*(m-1),64)] s.mem t.mem) :
    AllocatedFrame regs base buildW s t := by
  refine ⟨k.mono (by decide),u.cover ?_⟩
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · exact ⟨(2848,864),by simp [buildW],by dsimp only; omega,by dsimp only; omega⟩
  · exact ⟨(6000,512),by simp [buildW],by dsimp only; omega,by dsimp only; omega⟩

theorem copies_frame {base : Addr} {s t : State} {l : List (Nat × Nat)}
    (k : ProgKeep M base (l.map Prod.fst) s t)
    (hl : ∀ w∈(l.map Prod.fst).map (·,8*M.n)++[(M.tmp,8*M.n)],
      ∃ w'∈buildW,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2) :
    AllocatedFrame regs base buildW s t :=
  AllocatedFrame.of_prog k (fun r hr => List.mem_cons_of_mem _ (clob4_allocatedRegs r hr)) hl

theorem field_frame {base : Addr} {s t : State}
    (k : AllocatedFrame allocatedRegs base Proof.P256.EcdhJac.work s t) :
    AllocatedFrame regs base buildW s t :=
  k.mono (fun _ hr => List.mem_cons_of_mem _ hr)
    (fun w hw => ⟨w,List.mem_append_left _ hw,Nat.le_refl _,Nat.le_refl _⟩)

theorem movz19_ok (s : State) :
    WP isa (.block [.movz .x .x19 1 0]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 1 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem test_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x19 8]) s fun t =>
      t.gpr .x4=s.gpr .x19-8 ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 8<4096 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

section
variable {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
  (hs : ∀ x∈buildSlots,Sl x)
include layout aligned hs

theorem start_ok {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V0 E s) :
    WP isa (.block Impl.P256.VerifyTable.start) s fun t =>
      AllocatedFrame regs base buildW s t ∧ t.gpr .x19=BitVec.ofNat 64 1 ∧
      Inv M base 8192 C.p Sl (dsts 1 ++ copiesV l1 V0) (startEnv E) t := by
  rw [show Impl.P256.VerifyTable.start=copies l1 ++ [.movz .x .x19 1 0] ++
    Impl.P256.VerifyTable.storeEntry from rfl,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copies_ok layout aligned l1 hi (fun p hp => hs _ (by revert p; decide))
    (by decide)) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movz19_ok a) fun b ⟨cb,kb⟩ => ?_
  have ib := ia.of_keeps kb (by decide)
  refine WP.mono (storeEntry_inv layout ib (m:=1) (by decide) (by decide) cb
    (fun j hj => by revert j; decide) (fun j hj => dst_slot hs (by decide) (by decide) hj))
    fun t ⟨kt,ut,it⟩ => ⟨?_,?_,it⟩
  · exact (copies_frame ka (by decide)).trans
      ((AllocatedFrame.of_keeps kb).widenRegs (by decide) |>.trans (store_frame (by decide) (by decide) kt ut))
  · rw [kt.gpr _ (by decide),cb]

theorem dblu_ok {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl (dsts 1 ++ copiesV l1 V0) E s) :
    WP isa (Impl.P256.EcdhTable.program true) s fun t =>
      AllocatedFrame regs base buildW s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl ([704,736,768,864,896,5400,5432] ++ dsts 1 ++ V0)
        (runOps (ops true) E) t := by
  refine WP.mono (program_ok layout aligned (fun x hx => hs x (by
      simp only [buildSlots,List.mem_append]; exact Or.inl (Or.inl (Or.inl hx)))) true hi
    (by decide) (by decide) (by decide)) fun t ⟨kt,it⟩ => ⟨field_frame kt,?_,it⟩
  exact kt.regs.gpr _ allocatedRegs_x19

theorem swap_ok {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl ([704,736,768,864,896,5400,5432] ++ dsts 1 ++ V0) E s) :
    WP isa (.block Impl.P256.VerifyTable.swap) s fun t =>
      AllocatedFrame regs base buildW s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (Vl 0) (copiesEnv l2 E) t := by
  rw [show Impl.P256.VerifyTable.swap=copies l2 from rfl]
  refine WP.mono (copies_ok layout aligned l2 hi (fun p hp => hs _ (by revert p; decide))
    (by decide)) fun t ⟨kt,it⟩ => ⟨copies_frame kt (by decide),kt.gpr _ (by decide),it.sub ?_⟩
  decide

theorem zaddu_ok {base : Addr} {F : Nat → Fe C} {s : State} {k : Nat} (hk : k≤6)
    (hi : Inv M base 8192 C.p Sl (Vl k) F s) :
    WP isa (Impl.P256.EcdhTable.program false) s fun t =>
      AllocatedFrame regs base buildW s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (Vl k) (runOps (ops false) F) t := by
  have hW : ∀ x∈W,x∈Vl k := fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
  refine WP.mono (program_ok layout aligned (fun x hx => hs x (by
      simp only [buildSlots,List.mem_append]; exact Or.inl (Or.inl (Or.inl hx)))) false hi
    (readsOk_mono (by decide : readsOk (ops false) W=true) hW)
    (fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)) ?_) fun t ⟨kt,it⟩ =>
      ⟨field_frame kt,kt.regs.gpr _ allocatedRegs_x19,it⟩
  intro x hx
  simp only [Vl,List.mem_append] at hx
  rcases hx with (hx|hx)|hx
  · revert x; decide
  · exact entries_obs (by omega) hx false
  · revert x; decide

omit aligned in
theorem store_ok {base : Addr} {F : Nat → Fe C} {s : State} {k : Nat} (hk : k≤6)
    (hi : Inv M base 8192 C.p Sl (Vl k) F s) (h19 : s.gpr .x19=BitVec.ofNat 64 (k+2)) :
    WP isa (.block (Impl.P256.VerifyTable.storeEntry ++ ([.subImm .x .x4 .x19 8] : List Instr))) s fun t =>
      AllocatedFrame regs base buildW s t ∧ t.gpr .x19=BitVec.ofNat 64 (k+2) ∧
      t.gpr .x4=BitVec.ofNat 64 (k+2)-8 ∧
      Inv M base 8192 C.p Sl (Vl (k+1)) (storeEnv (k+2) F) t := by
  have hW : ∀ x∈W,x∈Vl k := fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
  rw [WP.block_append_iff]
  refine WP.mono (storeEntry_inv layout hi (m:=k+2) (by omega) (by omega) h19
    (fun j hj => hW _ (by revert j; decide)) (fun j hj => dst_slot hs (by omega) (by omega) hj))
    fun d ⟨kd,ud,id⟩ => ?_
  refine WP.mono (test_ok d) fun t ⟨ct,kt⟩ => ?_
  have cd : d.gpr .x19=BitVec.ofNat 64 (k+2) := by rw [kd.gpr _ (by decide),h19]
  refine ⟨(store_frame (by omega) (by omega) kd ud).trans ((AllocatedFrame.of_keeps kt).widenRegs (by decide)),
    by rw [kt.gpr _ (by decide),cd],by rw [ct,cd],(id.of_keeps kt (by decide)).sub ?_⟩
  intro x hx
  rw [Vl,entries_succ (k+1)] at hx
  simp only [Vl,List.mem_append] at hx ⊢
  grind

theorem step_ok {base : Addr} {F : Nat → Fe C} {s : State} {k : Nat} (hk : k≤6)
    (hi : Inv M base 8192 C.p Sl (Vl k) F s) (h19 : s.gpr .x19=BitVec.ofNat 64 (k+1)) :
    WP isa Impl.P256.VerifyTable.step s fun t =>
      AllocatedFrame regs base buildW s t ∧ t.gpr .x19=BitVec.ofNat 64 (k+2) ∧
      t.gpr .x4=BitVec.ofNat 64 (k+2)-8 ∧
      Inv M base 8192 C.p Sl (Vl (k+1)) (stepEnv (k+2) F) t := by
  unfold Impl.P256.VerifyTable.step
  refine WP.seq (WP.mono (Proof.P256.EcdhJac.buildIncrement_ok s h19) fun a ⟨ca,ka⟩ => ?_)
  refine WP.seq (WP.mono (zaddu_ok layout aligned hs hk (hi.of_keeps ka (by decide)))
    fun b ⟨kb,cb,ib⟩ => ?_)
  refine WP.mono (store_ok layout hs hk ib (cb.trans ca)) fun t ⟨kt,ct,xt,it⟩ =>
    ⟨((AllocatedFrame.of_keeps ka).widenRegs (by decide)).trans (kb.trans kt),ct,xt,it⟩

theorem loop_ok {base : Addr} {F : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl (Vl 0) F s) (h19 : s.gpr .x19=BitVec.ofNat 64 1) :
    WP isa (.loop Impl.P256.VerifyTable.step (.nonzero .x .x4)) s fun t =>
      AllocatedFrame regs base buildW s t ∧ Inv M base 8192 C.p Sl (Vl 7) (loopEnv 7 F) t := by
  refine WP.loop (M:=isa)
    (fun n t => n≤6 ∧ AllocatedFrame regs base buildW s t ∧ t.gpr .x19=BitVec.ofNat 64 (7-n) ∧
      Inv M base 8192 C.p Sl (Vl (6-n)) (loopEnv (6-n) F) t)
    (fun n a ⟨hn,fa,ca,ia⟩ => ?_) 6 s ⟨by decide,AllocatedFrame.refl _ _ _ _,h19,hi⟩
  refine WP.mono (step_ok layout aligned hs (k:=6-n) (by omega) ia (by rw [ca]; congr 1; omega))
    fun t ⟨kt,ct,xt,it⟩ => ?_
  have e : 6-n+1=7-n := by omega
  have e2 : 6-n+2=8-n := by omega
  rw [e] at it
  rw [e2] at ct xt
  have hz : (t.read .x .x4 != 0)=decide (n≠0) := by
    rw [read_x,xt]
    by_cases h : n=0
    · rw [h]; rfl
    · rw [decide_eq_true h,bne_iff_ne,ne_eq]
      intro he
      have hh : BitVec.ofNat 64 (8-n) = (8 : BitVec 64) := by bv_omega_arith
      have he' := congrArg BitVec.toNat hh
      simp only [BitVec.toNat_ofNat,show (8 : BitVec 64).toNat=8 from rfl,
        Nat.mod_eq_of_lt (show 8-n<2^64 by omega)] at he'
      omega
  by_cases h : n=0
  · subst h
    refine Or.inl ⟨?_,fa.trans kt,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz]; rfl
    · exact it
  · refine Or.inr ⟨?_,n-1,by omega,by omega,fa.trans kt,?_,?_⟩
    · show some (t.read .x .x4 != 0)=some true
      rw [hz,decide_eq_true h]
    · rw [ct]; congr 1; omega
    · rw [show 6-(n-1)=7-n by omega]
      have : loopEnv (7-n) F=stepEnv (6-n+2) (loopEnv (6-n) F) := by
        rw [show 7-n=(6-n)+1 by omega]; rfl
      rw [this]; exact it

theorem finish_ok {base : Addr} {F : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl (Vl 7) F s) :
    WP isa (.block Impl.P256.VerifyTable.finish) s fun t =>
      AllocatedFrame regs base buildW s t ∧
      Inv M base 8192 C.p Sl (copiesV l4 (Vl 7)) (copiesEnv l4 F) t := by
  rw [show Impl.P256.VerifyTable.finish=copies l4 from rfl]
  refine WP.mono (copies_ok layout aligned l4 hi (fun p hp => hs _ (by revert p; decide))
    (by decide)) fun t ⟨kt,it⟩ => ⟨copies_frame kt (by decide),it⟩

/-- The whole build on the field invariant. -/
theorem build_field {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V0 E s) :
    WP isa Impl.P256.VerifyTable.build s fun t =>
      AllocatedFrame regs base buildW s t ∧
      Inv M base 8192 C.p Sl (copiesV l4 (Vl 7)) (buildEnv E) t := by
  unfold Impl.P256.VerifyTable.build
  refine WP.seq (WP.mono (start_ok layout aligned hs hi) fun a ⟨ka,ca,ia⟩ => ?_)
  refine WP.seq (WP.mono (dblu_ok layout aligned hs ia) fun b ⟨kb,cb,ib⟩ => ?_)
  refine WP.seq (WP.mono (swap_ok layout aligned hs ib) fun d ⟨kd,cd,id⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok layout aligned hs id (by rw [cd,cb,ca])) fun e ⟨ke,ie⟩ => ?_)
  refine WP.mono (finish_ok layout aligned hs ie) fun t ⟨kt,it⟩ =>
    ⟨ka.trans (kb.trans (kd.trans (ke.trans kt))),it⟩

end

end VG.Proof.P256.VerifyTable
