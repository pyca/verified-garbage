module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations

/-! ### `MlDsa.AArch64.Optimized.BoundedFourBatchGeometry`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

def outputAt (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (1024*i)
def countAt (b : Addr) (i : Nat) : Addr := b+BitVec.ofNat 64 (7904+8*i)
def inputAt (b : Addr) (i off : Nat) : Addr := b+BitVec.ofNat 64 (840+544*i+off)
def batchWrites (b p : Addr) : List Region := [⟨p,4096⟩,⟨b+7904,32⟩]

theorem outputAt_sub (p : Addr) {i : Nat} (hi : i<4) :
    Region.Sub (polyR (outputAt p i)) ⟨p,4096⟩ := Offset.sub_base p (by omega_using [hi])

theorem countAt_sub (b : Addr) {i : Nat} (hi : i<4) :
    Region.Sub ⟨countAt b i,8⟩ ⟨b+7904,32⟩ := by
  have he : countAt b i=b+7904#64+BitVec.ofNat 64 (8*i) := by
    simp only [countAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [he]
  exact Offset.sub_base _ (by omega_using [hi])

theorem outputs_apart (p : Addr) {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) :
    (polyR (outputAt p i)).Disjoint (polyR (outputAt p j)) :=
  Offset.disjoint p (by omega_using [hne]) (by omega_using [hi]) (by omega_using [hj])

theorem counts_apart (b : Addr) {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) :
    (⟨countAt b i,8⟩ : Region).Disjoint ⟨countAt b j,8⟩ :=
  Offset.disjoint b (by omega_using [hne]) (by omega_using [hi]) (by omega_using [hj])

theorem parseFrame_batch {b p : Addr} {i : Nat} (hi : i<4) {m m' : Mem}
    (hf : Frame [polyR (outputAt p i),⟨countAt b i,8⟩] m m') :
    Frame (batchWrites b p) m m' := by
  refine hf.sub ?_
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨⟨p,4096⟩,by simp [batchWrites],outputAt_sub p hi⟩
  · exact ⟨⟨b+7904,32⟩,by simp [batchWrites],countAt_sub b hi⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourFlags`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def foldedFlags (C : Nat→BitVec 64) (n : Nat) : BitVec 64 :=
 (List.range n).foldl (fun a i=>a|||C (i+1)) (C 0)

theorem foldedFlags_succ (C : Nat→BitVec 64) (n : Nat) :
    foldedFlags C (n+1)=foldedFlags C n|||C (n+1) := by
  simp only [foldedFlags,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

def flagStep (i : Nat) : List Instr :=
 [.ldr .x .x6 .x19 (7904+8*(i+1)),.logic .orr .x .x27 .x27 .x6]

theorem flagStep_ok {s : State} {i : Nat} (hi : i<3) {b : Addr} (hb : s.gpr .x19=b)
    (hr : InRegions (s.rd++s.wr) (countAt b (i+1)) 8) :
    WP isa (.block (flagStep i)) s fun t=>Only [.x6,.x27] s t ∧
      t.gpr .x27=s.gpr .x27|||s.mem.readW (countAt b (i+1)) 64 := by
  unfold flagStep
  refine wp_ldrx (by omega_using [hi]) (by rw [hb]; rfl) hr fun a ha h6=>
    wp_orr fun t ht h27=>wp_nil ⟨(ha.trans ht).mono (by decide),?_⟩
  rw [h27,h6,ha.get .x27]

theorem flagsTailN_ok {n : Nat} (hn : n≤3) {s : State} {b : Addr} (hb : s.gpr .x19=b) {C : Nat→BitVec 64}
    (hc : ∀i<n+1,s.mem.readW (countAt b i) 64=C i) (h27 : s.gpr .x27=C 0)
    (hr : ∀i<n+1,InRegions (s.rd++s.wr) (countAt b i) 8) :
    WP isa (.block ((List.range n).flatMap flagStep)) s fun t=>Only [.x6,.x27] s t ∧
      t.gpr .x27=foldedFlags C n := by
  refine wp_range_flatMap (M := isa) (N := n)
    (fun k t=>Only [.x6,.x27] s t ∧ t.gpr .x27=foldedFlags C k)
    (fun k t hk ht=>?_) n (Nat.le_refl _) s ⟨Only.refl _ _,h27⟩
  refine WP.mono (flagStep_ok (s := t) (i := k) (b := b) (by omega_using [hn, hk]) (by rw [ht.1.get .x19]; exact hb)
    (by rw [ht.1.rd,ht.1.wr]; exact hr (k+1) (by omega_using [hk]))) fun u ⟨hu,he⟩=>?_
  refine ⟨(ht.1.trans hu).mono (by decide),?_⟩
  rw [he,ht.2,ht.1.mem,hc (k+1) (by omega_using [hk]),foldedFlags_succ]

theorem flags_ok {s : State} {b : Addr} (hb : s.gpr .x19=b) {C : Nat→BitVec 64}
    (hc : ∀i<4,s.mem.readW (countAt b i) 64=C i)
    (hr : ∀i<4,InRegions (s.rd++s.wr) (countAt b i) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) s fun t=>
      (Only [.x6,.x27] s t ∧ t.gpr .x27=foldedFlags C 3) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  change WP isa (.block (.ldr .x .x27 .x19 7904::(List.range 3).flatMap flagStep)) s _
  refine wp_ldrx (by decide) (by rw [hb]; rfl) (hr 0 (by decide)) fun a ha h27=>?_
  refine WP.mono (flagsTailN_ok (n := 3) (by decide) (s := a) (b := b) (C := C) (by rw [ha.get .x19]; exact hb)
    (fun i hi=>by rw [ha.mem]; exact hc i hi) (by rw [h27,hc 0 (by decide)])
    (fun i hi=>by rw [ha.rd,ha.wr]; exact hr i hi)) fun t ⟨ht,he⟩=>
    ⟨(ha.trans ht).mono (by decide),he⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (foldedFlags foldedFlags_succ)

theorem foldedFlags_zero (C : Nat → BitVec 64) (n : Nat) :
    foldedFlags C n=0#64 ↔ ∀i<n+1,C i=0#64 := by
  induction n with
  | zero =>
    change C 0=0#64 ↔ ∀i<1,C i=0#64
    constructor
    · intro h i hi
      have hi0 : i=0 := by omega_using [hi]
      subst i
      exact h
    · intro h; exact h 0 (by decide)
  | succ n ih =>
    rw [foldedFlags_succ,BitVec.or_eq_zero_iff,ih]
    constructor
    · rintro ⟨h,hLast⟩ i hi
      by_cases he : i=n+1
      · subst i; exact hLast
      · exact h i (by omega_using [hi, he])
    · intro h
      exact ⟨fun i hi => h i (by omega_using [hi]),h (n+1) (by omega_using [])⟩

theorem foldedFlags_bound (C : Nat → BitVec 64) (n : Nat)
    (hc : ∀i<n+1,(C i).toNat≤256) : (foldedFlags C n).toNat<512 := by
  induction n with
  | zero => change (C 0).toNat<512; have:=hc 0 (by decide); omega_using [this]
  | succ n ih =>
    rw [foldedFlags_succ,BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 9) (ih (fun i hi => hc i (by omega_using [hi])))
      (by have:=hc (n+1) (by omega_using []); omega_using [this])

theorem smallFlag_status (x : BitVec 64) (hx : x.toNat<512) :
    (x-1#64)>>>63 = if x=0#64 then 1#64 else 0#64 := by
  by_cases hz : x=0#64
  · subst x; decide
  · rw [ite_eq_right hz]
    have hn : x.toNat≠0 := by intro h; exact hz (BitVec.eq_of_toNat_eq h)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub,BitVec.toNat_ofNat]
    omega

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
