module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Sq
public import VerifiedGarbage.Proof.MillerRabin.Arm.Scan
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.RvBase
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.FiosFastChoice

/-! # The Miller–Rabin round on ARMv7: the table

`tv P σ k` is power `k` in Montgomery form. After `i` steps, entries
0 through `i + 1` are complete, and each remaining entry retains its input
value. Each product is copied once to its final public slot.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The table's entry `k`. -/
abbrev tv (P : MP) (σ : State) (k : Nat) : Nat := tp (cOf P σ.mem) P.w (xOf P σ) (oOf P σ) k

/-- Entry `k` of the table after `i` iterations. -/
def tabEnt (P : MP) (σ : State) (i k : Nat) : Nat :=
  if k = 0 then oOf P σ else if k = 1 then xOf P σ else
    if k ≤ i + 1 then tv P σ k else num σ.mem P.B P.W (aT0 + k)

/-- The arrays after `i` iterations. -/
def AT (P : MP) (i : Nat) (σ : State) (j : Nat) : Nat :=
  if j = aY then tv P σ (i + 1) else if j = aX then xOf P σ else tabEnt P σ i (j - aT0)

/-- `y`, `x` and the table. -/
abbrev LT : List Nat := [aY, aX, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The table's loop with `k` iterations left. -/
def TS (P : MP) (k : Nat) (σ s : State) : Prop :=
  k ≤ 14 ∧ St P (In P) (AT P (14 - k)) LT (fun _ => upd (fun _ => 0) sK k) [sK] σ s

theorem LT_tab : ∀ k < 16, aT0 + k ∈ LT := by decide

theorem tv_lt {P : MP} {σ : State} (h : In P σ) (k : Nat) : tv P σ k < cOf P σ.mem := by
  have := h.c3
  exact tp_lt (by omega) h.x5 (by show numAt σ.mem (State.addr P.ws) P.w 9 < _; rw [h.one]; exact Nat.mod_lt _ (by omega)) k

/-- A product and one final-slot copy advance the completed prefix. -/
theorem AT_step {P : MP} {σ : State} {i : Nat} (hi : i < 14) :
    ∀ j ∈ LT,
      upd (upd (AT P i σ) aY
        (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX)))
        (aT0 + i + 2) (tv P σ (i + 2)) j = AT P (i + 1) σ j := by
  have ey : mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX) = tv P σ (i + 2) := rfl
  rw [ey]
  have e0 : aT0 = 11 := rfl
  have eY : aY = 6 := rfl
  have eX : aX = 5 := rfl
  intro j hj
  have hj' : j = aY ∨ j = aX ∨ (aT0 ≤ j ∧ j < aT0 + 16) := by
    simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  rcases hj' with rfl | rfl | hj
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · have hY : j ≠ aY := by omega
    have hX : j ≠ aX := by omega
    by_cases he : j = aT0 + i + 2
    · subst j
      have hsub : aT0 + i + 2 - aT0 = i + 2 := by omega
      simp (disch := omega) only [upd, AT, tabEnt, hsub, ↓ite_eq_left, ↓ite_eq_right]
    · have hidx : j - aT0 ≠ i + 2 := by omega
      have hbound : (j - aT0 ≤ i + 1) = (j - aT0 ≤ (i + 1) + 1) := by apply propext; omega
      simp only [upd, he, hY, hX, AT, tabEnt, ↓reduceIte, hbound]


/-- Select one final slot from the public count, without duplicating products. -/
private theorem tab_copy_from {P : MP} {σ s : State} {A : Nat → Nat} {L : List Nat}
    {V : Nat → Nat} {LS : List Nat} (h : KS P σ A L V LS s) (hw : Ws s P.B P.Z P.W nArr)
    (ha : aY ∈ L) (i j n : Nat) (lo : j ≤ i) (hi : i ≤ j+n) (bound : j+n < 14)
    (count : s.gpr .lr = BitVec.ofNat 32 (14-i)) :
    WP isa (tabCopyFrom j n) s fun t =>
      KS P σ (upd A (aT0+i+2) (num s.mem P.B P.W aY)) ((aT0+i+2)::L) V LS t ∧
      Ws t P.B P.Z P.W nArr := by
  induction n generalizing j s with
  | zero =>
    have eq : j=i := by omega
    subst j
    exact WP.mono (h.copy_ok hw (by simp [wJs,aT0]; omega) (h.live_lt _ ha)
      (by simp only [aT0,aY]; omega)) fun _ ht => ⟨ht.1,ht.2.1⟩
  | succ n ih =>
    rw [tabCopyFrom,WP.seq_iff]
    have enc : encodable (BitVec.ofNat 32 (14-j)) = true := by
      have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    refine WP.mono (VG.Proof.Bignum.Arm.FiosFast.choose_ok s (14-i) (14-j)
      (by omega) (by omega) enc count) ?_
    rintro u ⟨z,mem,rest⟩
    have hu := h.of_rest rest mem
    have hwu := hw.rest rest
    refine WP.ite u.z rfl ?_ ?_
    · intro yes
      have eq : j=i := by have := of_decide_eq_true (z.symm.trans yes); omega
      subst j
      exact WP.mono (hu.copy_ok hwu (by simp [wJs,aT0]; omega) (hu.live_lt _ ha)
        (by simp only [aT0,aY]; omega)) fun t ht => by simpa only [mem] using And.intro ht.1 ht.2.1
    · intro no
      have ne : j ≠ i := by intro eq; subst j; simp at z; simp [z] at no
      exact WP.mono (ih hu hwu (j+1) (by omega) (by omega) (by omega)
        (by rw [rest.gpr .lr (by simp),count])) fun t ht => by simpa only [mem] using ht

private theorem St.ptabCopy {P : MP} {E : State → Prop} {A : State → Nat → Nat}
    {L : List Nat} {V : State → Nat → Nat} {LS : List Nat} (i : Nat) (hi : i<14)
    (ha : aY ∈ L) (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK=14-i) :
    VP (St P E A L V LS) tabCopy
      (St P E (fun σ => upd (A σ) (aT0+i+2) (A σ aY)) ((aT0+i+2)::L) V LS) := by
  rw [tabCopy]
  refine VP.seq (G := fun σ s => St P E A L V LS σ s ∧ s.gpr .lr=BitVec.ofNat 32 (14-i)) ?_ ?_
  · refine VP.kv tabCopyLoad_taint (fun _ _ h => h.2.2) fun σ s ⟨e,h,hw⟩ => ?_
    refine h.ldr hw hk (r := .lr) (by decide) fun t ht hwt u => WP.block_nil ⟨⟨e,ht,hwt⟩,?_⟩
    rw [u.gpr,vk σ e]
  · refine VP.taint [.lr,.r7,.r8,.r9] tabCopyFrom_taint ?_ ?_
    · intro σ₁ σ₂ s₁ s₂ h₁ h₂ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · rw [h₁.2,h₂.2]
      · rw [h₁.1.2.2.r7,h₂.1.2.2.r7]
      · rw [h₁.1.2.2.r8,h₂.1.2.2.r8]
      · rw [h₁.1.2.2.r9,h₂.1.2.2.r9]
    · intro σ s ⟨⟨e,h,hw⟩,count⟩
      exact WP.mono (tab_copy_from h hw ha i 0 13 (by omega) (by omega) (by decide) count)
        fun t ⟨ht,hwt⟩ => ⟨e,by rwa [h.arrs aY ha] at ht,hwt⟩

/-- One fixed, public entry index. -/
theorem tab_step {P : MP} (i : Nat) (hi : i < 14) (fios : Bool := false) :
    VP (TS P (14 - i)) (tabStep (fios := fios)) (fun σ s => TS P (13-i) σ s ∧ s.z=decide (13-i=0)) := by
  let V := fun (_ : State) => upd (fun _ => 0) sK (14 - i)
  refine VP.mono (F := St P (In P) (AT P i) LT V [sK]) ?_
    (fun σ s h => by simpa only [TS, Nat.sub_sub_self (by omega : i ≤ 14)] using h.2)
    (fun _ _ h => h)
  simp only [tabStep, seqs]
  refine VP.seq (St.pmulY (fios := fios) (P := P) (A := AT P i) (L := LT.tail) (.inr rfl)
    (by decide) (by decide) (by decide) (by decide) (fun σ e => tv_lt e _) (fun σ e => e.x5)) ?_
  refine VP.seq (St.ptabCopy i hi (by simp) (by simp) (fun _ _ => rfl)) ?_
  refine (St.pcnt (n := 13 - i) (by simp) (fun σ _ => by simp [V, upd]; omega) (by omega)).mono
    (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  refine ⟨⟨by omega, h.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩)
    (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], by
      simp only [List.mem_singleton] at hd; subst d; simp only [upd_self]⟩)⟩,z⟩
  change upd (upd (AT P i σ) aY _) (aT0 + i + 2) _ j = _
  rw [show (upd (AT P i σ) aY
      (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX))) aY = tv P σ (i + 2) from rfl]
  rw [AT_step hi j hj]
  congr 1
  omega

/-- The compact loop advances the completed prefix. -/
theorem tab_loop {P : MP} (fios : Bool := false) :
    VP (TS P 14) (tabBuild (fios := fios)) (TS P 0) := by
  refine VP.loop (fun n => ?_) 13
  by_cases hn : n+1 ≤ 14
  · have hi : 14-(n+1)<14 := by omega
    have eq1 : 14-(14-(n+1))=n+1 := by omega
    have eq2 : 13-(14-(n+1))=n := by omega
    refine (tab_step (P := P) (14-(n+1)) hi (fios := fios)).mono ?_ ?_
    · intro σ s h
      simpa only [eq1] using h
    · intro σ s h
      have ts : TS P n σ s := by simpa only [eq2] using h.1
      refine ⟨?_,fun h0 => h0 ▸ ts,fun _ => ts⟩
      show some (!s.z) = _
      rw [h.2,eq2]
      by_cases h0 : n=0 <;> simp [h0] <;> omega
  · exact VP.of_false fun _ _ h => hn h.1

end VG.Proof.MillerRabin.Arm
