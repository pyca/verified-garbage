module

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.P256.VerifyTable
import VerifiedGarbage.Proof.P256.VerifyTable.Store
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.P256.EcdhJac.Masks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
public import VerifiedGarbage.Proof.P256.EcdhJac.Dblu
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract

/-! ### `P256.VerifyTable.Field`, which only this module used -/

section

/-! ECDH's allocated DBLU and ZADDU blocks on any slot predicate holding their
slots: the raw field programs' contract, carried to the allocated code through
their certificates on the observed slots. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

abbrev C := Spec.P256.curve
abbrev M := VG.Impl.P256.EcdhJac.K.M

/-- The slots DBLU and ZADDU name. -/
def slots : List Nat := Proof.P256.EcdhJac.tblW ++ [1280,1440,224]

def observe (doubling : Bool) (off : Nat) : Prop :=
  if doubling then Proof.P256.EcdhTable.Dblu.observe off else Proof.P256.EcdhTable.Zaddu.observe off
instance (doubling : Bool) (off : Nat) : Decidable (observe doubling off) := by
  unfold observe; split <;> infer_instance

theorem raw_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hs : ∀ x∈slots,Sl x) (doubling : Bool)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hreads : readsOk (Impl.P256.EcdhTable.operations doubling) V=true) :
    WP isa (.block (Impl.P256.EcdhTable.raw doubling)) s fun t =>
      ProgKeep M base ((Impl.P256.EcdhTable.operations doubling).map FOp.out) s t ∧
      Inv M base 8192 C.p Sl (validAfter (Impl.P256.EcdhTable.operations doubling) V)
        (runOps (Impl.P256.EcdhTable.operations doubling) E) t := by
  have hsl : ∀ op∈Impl.P256.EcdhTable.operations doubling,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    apply hs
    cases doubling <;>
      exact (show ∀ op∈Impl.P256.EcdhTable.operations _,∀ x∈op.out::op.ins,x∈slots by decide +kernel) op hop x hx
  exact VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned (unitMod_pow_two (by decide) _)
    _ hi hsl hreads

theorem refine (doubling : Bool) {base : Addr} {s : State} (hs : Scr s base 8192)
    {Q : State → Prop} (hq : WP isa (.block (Impl.P256.EcdhTable.raw doubling)) s Q) :
    WP isa (Impl.P256.EcdhTable.program doubling) s fun t => ∃ u,Q u ∧
      (∀ off,observe doubling off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧
      AllocatedFrame allocatedRegs base Proof.P256.EcdhJac.work s t := by
  cases doubling
  · exact Proof.P256.EcdhTable.Zaddu.refine hs hq
  · exact Proof.P256.EcdhTable.Dblu.refine hs hq

/-- The allocated block's field contract on observed output slots `Out`. -/
theorem program_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hs : ∀ x∈slots,Sl x) (doubling : Bool)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hreads : readsOk (Impl.P256.EcdhTable.operations doubling) V=true)
    (hout : ∀ x∈Out,x∈validAfter (Impl.P256.EcdhTable.operations doubling) V)
    (hobs : ∀ x∈Out,∀ i<4,observe doubling (x+8*i)) :
    WP isa (Impl.P256.EcdhTable.program doubling) s fun t =>
      AllocatedFrame allocatedRegs base Proof.P256.EcdhJac.work s t ∧
      Inv M base 8192 C.p Sl Out (runOps (Impl.P256.EcdhTable.operations doubling) E) t := by
  refine WP.mono (refine doubling hi.scr (raw_ok layout aligned hs doubling hi hreads))
    fun t ⟨u,⟨_,hu⟩,ho,hk⟩ => ⟨hk,?_⟩
  have ht := hk.scr allocatedRegs_x0 hi.scr
  have hm := hi.mod.unch hk.unch
    (show ∀ w∈Proof.P256.EcdhJac.work,M.mo+8*M.n≤w.1 ∨ w.1+w.2≤M.mo by decide) hi.scr.nowrap
  refine (hu.sub hout).of_observed ht hm fun x hx i him => ?_
  apply ho (x+8*i) (hobs x hx i him)
  · have ha := aligned.sl x (hu.sl x (hout x hx))
    omega_using [ha]
  · have hb := layout.le x (hu.sl x (hout x hx))
    change i<4 at him
    change x+32≤8192 at hb
    omega_using [him, hb]

end VG.Proof.P256.VerifyTable

end

end

/-! ### `P256.VerifyTable.Copies`, which only this module used -/

section

/-! Runs of field-slot copies: each copy `(o, a)` updates the environment at
`o` with its value at `a`. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def copies (l : List (Nat × Nat)) : List Instr := l.flatMap fun p => copy 4 p.1 p.2

/-- The environment after the copies `l`. -/
def copiesEnv {F : Type _} : List (Nat × Nat) → (Nat → F) → Nat → F
  | [], E => E
  | p :: l, E => copiesEnv l (Function.update E p.1 (E p.2))

/-- The live slots after the copies `l` from the live slots `V`. -/
def copiesV : List (Nat × Nat) → List Nat → List Nat
  | [], V => V
  | p :: l, V => copiesV l (p.1 :: V)

/-- Each copy reads a live slot. -/
def copiesOk : List (Nat × Nat) → List Nat → Bool
  | [], _ => true
  | p :: l, V => decide (p.2 ∈ V) && copiesOk l (p.1 :: V)

theorem copies_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl) :
    ∀ (l : List (Nat × Nat)) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State},
    Inv M base 8192 C.p Sl V E s → (∀ p∈l,Sl p.1) → copiesOk l V=true →
    WP isa (.block (copies l)) s fun t =>
      ProgKeep M base (l.map Prod.fst) s t ∧ Inv M base 8192 C.p Sl (copiesV l V) (copiesEnv l E) t
  | [], _, _, _, s, hi, _, _ => by
    apply WP.of_runBlock
    exact ⟨s,rfl,ProgKeep.refl _ _ _ _,hi⟩
  | p :: l, base, V, E, s, hi, hs, hok => by
    simp only [copiesOk,Bool.and_eq_true,decide_eq_true_eq] at hok
    change WP isa (.block (copy 4 p.1 p.2 ++ copies l)) s _
    rw [WP.block_append_iff]
    refine WP.mono (copyField_ok layout aligned hi (hs p (List.mem_cons_self ..)) hok.1)
      fun a ⟨ka,ia⟩ => ?_
    refine WP.mono (copies_ok layout aligned l ia (fun q hq => hs q (List.mem_cons_of_mem _ hq)) hok.2)
      fun t ⟨kt,it⟩ => ⟨?_,it⟩
    exact (progKeep_of_op ka (List.mem_cons_self ..)).trans
      (kt.mono fun w hw => List.mem_cons_of_mem _ hw)

end VG.Proof.P256.VerifyTable

end

end

/-! ### `P256.VerifyTable.StoreInv`, which only this module used -/

section

/-! A co-Z table entry's stores in the field invariant: entry `m`'s point and
cache slots take the values of `E` and the powers of its `Z`. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- Entry `m`'s five slots: its point's coordinates, then its `Z²` and `Z³`. -/
def dst (m j : Nat) : Nat := if j<3 then 2848+96*(m-1)+32*j else 6000+64*(m-1)+32*(j-3)
/-- What they are copied from: `E` and the powers of its `Z`. -/
def src (j : Nat) : Nat := if j<3 then 704+32*j else 5400+32*(j-3)
def dsts (m : Nat) : List Nat := (List.range 5).map (dst m)

/-- The field values after entry `m`'s stores. -/
def storeEnv {F : Type _} (m : Nat) (E : Nat → F) (x : Nat) : F :=
  if x=dst m 0 then E (src 0) else if x=dst m 1 then E (src 1) else
  if x=dst m 2 then E (src 2) else if x=dst m 3 then E (src 3) else
  if x=dst m 4 then E (src 4) else E x

theorem dst_inj {m : Nat} {i j : Nat} (hi : i<5) (hj : j<5) :
    dst m i=dst m j ↔ i=j :=
  ⟨fun h => by unfold dst at h; split at h <;> split at h <;> omega_arith,fun h => h ▸ rfl⟩

theorem storeEnv_dst {F : Type _} {m : Nat} (E : Nat → F) {j : Nat} (hj : j<5) :
    storeEnv m E (dst m j)=E (src j) := by
  unfold storeEnv
  have : j=0∨j=1∨j=2∨j=3∨j=4 := by omega_using [hj]
  rcases this with rfl|rfl|rfl|rfl|rfl <;>
    simp (disch := decide) only [dst_inj,Nat.reduceEqDiff,↓reduceIte]

theorem storeEnv_other {F : Type _} {m : Nat} (E : Nat → F) {x : Nat} (hx : x∉dsts m) :
    storeEnv m E x=E x := by
  simp only [dsts,List.mem_map,List.mem_range,not_exists,not_and] at hx
  have h0 : x≠dst m 0 := fun h => hx 0 (by decide) h.symm
  have h1 : x≠dst m 1 := fun h => hx 1 (by decide) h.symm
  have h2 : x≠dst m 2 := fun h => hx 2 (by decide) h.symm
  have h3 : x≠dst m 3 := fun h => hx 3 (by decide) h.symm
  have h4 : x≠dst m 4 := fun h => hx 4 (by decide) h.symm
  simp only [storeEnv,h0,h1,h2,h3,h4,↓reduceIte]

theorem storeEntry_inv {Sl : Nat → Prop} (layout : Lay M 8192 Sl)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State} {m : Nat}
    (hi : Inv M base 8192 C.p Sl V E s) (hm : 1≤m) (hm9 : m≤9)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m)
    (hsrc : ∀ j<5,src j∈V) (hdst : ∀ j<5,Sl (dst m j)) :
    WP isa (.block VG.Impl.P256.VerifyTable.storeEntry) s fun t =>
      KeepRegs [.x1,.x2,.x16] s t ∧
      Unch base [(2848+96*(m-1),96),(6000+64*(m-1),64)] s.mem t.mem ∧
      Inv M base 8192 C.p Sl (dsts m++V) (storeEnv m E) t := by
  have hn := hi.scr.nowrap
  refine WP.mono (storeEntry_ok hi.scr hm hm9 h19) fun t ⟨we,wc,kt,ut⟩ => ⟨kt,ut,?_⟩
  have hsd (j : Nat) (hj : j<5) :
      wordsVal t.mem base (dst m j) 4=wordsVal s.mem base (src j) 4 := by
    apply wordsVal_of_words
    intro k hk
    by_cases h3 : j<3
    · have := we (4*j+k) (by omega_using [hk, h3])
      simp only [dst,src,h3,ite_true]
      rw [show 2848+96*(m-1)+32*j+8*k=2848+96*(m-1)+8*(4*j+k) by omega_using [],
        show 704+32*j+8*k=704+8*(4*j+k) by omega_using []]
      exact this
    · have := wc (4*(j-3)+k) (by omega_using [hj, hk])
      simp only [dst,src,h3,ite_false]
      rw [show 6000+64*(m-1)+32*(j-3)+8*k=6000+64*(m-1)+8*(4*(j-3)+k) by omega_using [],
        show 5400+32*(j-3)+8*k=5400+8*(4*(j-3)+k) by omega_using []]
      exact this
  have hkeep (x : Nat) (hx : x∈V) (hnd : x∉dsts m) :
      wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    simp only [dsts,List.mem_map,List.mem_range,not_exists,not_and] at hnd
    have ap (j : Nat) (hj : j<5) := layout.apart x (dst m j) (hi.sl x hx) (hdst j hj)
      (fun h => hnd j hj h.symm)
    have a0 := ap 0 (by decide); have a1 := ap 1 (by decide); have a2 := ap 2 (by decide)
    have a3 := ap 3 (by decide); have a4 := ap 4 (by decide)
    simp only [dst,show M.n=4 from rfl,Nat.reduceLT,ite_true,ite_false] at a0 a1 a2 a3 a4
    have hb := layout.le x (hi.sl x hx)
    change x+32≤8192 at hb
    refine ut.wordsVal (fun w hw => ?_) (by omega_using [hb])
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> dsimp only <;> omega_arith
  refine ⟨hi.scr.of_keepRegs kt (by decide),hi.mod.unch ut (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> (change 64+32≤_ ∨ _; omega_using [])) hn,?_,?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · simp only [dsts,List.mem_map,List.mem_range] at hx
      obtain ⟨j,hj,rfl⟩ := hx
      exact hdst j hj
    · exact hi.sl x hx
  · intro x hx
    by_cases hd : x∈dsts m
    · simp only [dsts,List.mem_map,List.mem_range] at hd
      obtain ⟨j,hj,rfl⟩ := hd
      change wordsVal t.mem base (dst m j) 4<_
      rw [hsd j hj]; exact hi.lt _ (hsrc j hj)
    · have hv := (List.mem_append.mp hx).resolve_left hd
      change wordsVal t.mem base x 4<_
      rw [hkeep x hv hd]; exact hi.lt x hv
  · intro x hx
    by_cases hd : x∈dsts m
    · simp only [dsts,List.mem_map,List.mem_range] at hd
      obtain ⟨j,hj,rfl⟩ := hd
      change toM _ _ (wordsVal t.mem base (dst m j) 4)=_
      rw [hsd j hj,storeEnv_dst E hj]; exact hi.val _ (hsrc j hj)
    · have hv := (List.mem_append.mp hx).resolve_left hd
      change toM _ _ (wordsVal t.mem base x 4)=_
      rw [hkeep x hv hd,storeEnv_other E hd]; exact hi.val x hv

end VG.Proof.P256.VerifyTable

end

end


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
  have := h (m-1) (by omega_using [hm8]) j hj
  rwa [show m-1+1=m by omega_using [hm]] at this

theorem entries_obs {n : Nat} (hn : n≤9) {x : Nat} (hx : x∈entries n) (d : Bool) :
    ∀ i<4,observe d (x+8*i) := by
  obtain ⟨a,ha,j,hj,rfl⟩ := mem_entries.mp hx
  have h : ∀ d : Bool,∀ a<9,∀ j<5,∀ i<4,observe d (dst (a+1) j+8*i) := by decide
  exact h d a (by omega_using [hn, ha]) j hj

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
  · exact entries_obs (by omega_using [hk]) hx false
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
  refine WP.mono (storeEntry_inv layout hi (m:=k+2) (by omega_using []) (by omega_using [hk]) h19
    (fun j hj => hW _ (by revert j; decide)) (fun j hj => dst_slot hs (by omega_using []) (by omega_using [hk]) hj))
    fun d ⟨kd,ud,id⟩ => ?_
  refine WP.mono (test_ok d) fun t ⟨ct,kt⟩ => ?_
  have cd : d.gpr .x19=BitVec.ofNat 64 (k+2) := by rw [kd.gpr _ (by decide),h19]
  refine ⟨(store_frame (by omega_using []) (by omega_using [hk]) kd ud).trans ((AllocatedFrame.of_keeps kt).widenRegs (by decide)),
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
  refine WP.mono (step_ok layout aligned hs (k:=6-n) (by omega_using []) ia (by rw [ca]; congr 1; omega_using [hn]))
    fun t ⟨kt,ct,xt,it⟩ => ?_
  have e : 6-n+1=7-n := by omega_using [hn]
  have e2 : 6-n+2=8-n := by omega_using [hn]
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
        Nat.mod_eq_of_lt (show 8-n<2^64 by omega_using [])] at he'
      omega_using [h, he']
  by_cases h : n=0
  · subst h
    refine Or.inl ⟨?_,fa.trans kt,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz]; rfl
    · exact it
  · refine Or.inr ⟨?_,n-1,by omega_using [h],by omega_using [hn],fa.trans kt,?_,?_⟩
    · show some (t.read .x .x4 != 0)=some true
      rw [hz,decide_eq_true h]
    · rw [ct]; congr 1; omega_using [h]
    · rw [show 6-(n-1)=7-n by omega_using [h]]
      have : loopEnv (7-n) F=stepEnv (6-n+2) (loopEnv (6-n) F) := by
        rw [show 7-n=(6-n)+1 by omega_using [hn]]; rfl
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
