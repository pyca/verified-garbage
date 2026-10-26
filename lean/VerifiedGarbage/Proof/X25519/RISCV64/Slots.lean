module
public import VerifiedGarbage.Proof.X25519.RISCV64.Field

import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.Cswap
import VerifiedGarbage.Proof.X25519.RISCV64.AddSub
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on RISCV64: the field elements the working space holds

`SlotsOk m B qs v`: each slot `q` of `qs` holds the element `v q`. The field
operations as updates of `v` (`mulS`, `addS`, `subS`, `cswapS`), for slots
whose separation from the output is decided on their offsets (`Sep1`), and
writing only the field area `[0, ACC + 64)` of the working space (`FA`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P Fe)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub)

/-- Each slot `q` of `qs` holds `v q`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsOk m B qs w := fun q hq => (h q hq).trans (hs q hq)

/-- `v` with the element `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : upd v o x o = x := by simp [upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : upd v o x q = v q := by simp [upd, h]

/-- `o` is a multiple of 4, and every slot of `qs` is `o` or separate from
it, below `ACC`, and a multiple of 4 (for the alignment of words). -/
def Sep1 (o : Nat) (qs : List Nat) : Bool :=
  o % 4 == 0 && qs.all fun q => (q == o || q + 32 ≤ o || o + 32 ≤ q) && q + 32 ≤ ACC && q % 4 == 0

theorem sep1_o {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) : o % 4 = 0 := by
  simp only [Sep1, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem sep1_get {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 32 ≤ o ∨ o + 32 ≤ q) ∧ q + 32 ≤ ACC ∧ q % 4 = 0 := by
  simp only [Sep1, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)),
    this.1.2, this.2⟩

/-- The field area `[0, ACC + 64)` of the working space: the elements and
the product at `ACC`. -/
abbrev FA (b : Addr) : Region := ⟨b, ACC + 64⟩

section
variable {b : Addr}

/-- The slots of `qs` other than `o` after a write of `o` (and `ACC`). -/
theorem slots_after {o : Nat} {qs : List Nat} (hq : Sep1 o qs = true)
    (ho : o + 32 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] m m')
    {v : Nat → Fe} (hS : SlotsOk m b qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    FS m' b q = v q := by
  obtain ⟨h1, h3, -⟩ := sep1_get hq hq'
  have hA := ACC_eq
  have e : ∀ k < 8, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hqo, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, ho])
      · exact Offset.disjoint _ (.inl (by omega_using [h3, hk])) (by omega_using [hA, h3, hk]) (by omega_using [hA])
  rw [FS, V, val32_congr e]; exact hS q hq'

theorem frame_FA {o : Nat} (ho : o + 32 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] m m') :
    Frame [FA b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_using [ho])

theorem mulS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 32 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (mul o x y) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x * v y)) := by
  refine WP.mono (mul_ok (by decide) ho (sep1_get hq hx).2.1 (sep1_get hq hy).2.1 (by decide) (sep1_o hq)
    (sep1_get hq hx).2.2 (sep1_get hq hy).2.2 hc)
    fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m m') :
    Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem addS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 32 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (add o x y)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x + v y)) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  have hA := ACC_eq
  refine WP.mono (add_ok (by omega_using [hA, ho]) (by omega_using [hA, hx']) (by omega_using [hA, hy'])
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    (sep1_o hq) hx'.2.2 hy'.2.2 hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_add hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem subS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 32 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (sub o x y)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x - v y)) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  have hA := ACC_eq
  refine WP.mono (sub_ok (by omega_using [hA, ho]) (by omega_using [hA, hx']) (by omega_using [hA, hy'])
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    (sep1_o hq) hx'.2.2 hy'.2.2 hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_sub hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

theorem cswapS {x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : Sep1 x qs = true) (hq' : Sep1 y qs = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x + 32 ≤ y ∨ y + 32 ≤ x) {s : State} (hc : Ctx b s) {sw : Nat}
    (hsw : sw ≤ 1) (h11 : s.gpr .t0 = 0 - BitVec.ofNat 64 sw) (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.a2, .a4, .a5] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b qs (swapV x y sw v) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  have hA := ACC_eq
  refine WP.mono (cswap_ok (b := b) (by omega_using [hA, hx']) (by omega_using [hA, hy']) hxy hx'.2.2 hy'.2.2
    hc hsw h11)
    fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_using [hA, hx', hy'])
  · intro q hq''
    have hlx : ∀ k < 8, limb s'.mem b x k = sel sw (limb s.mem b x k) (limb s.mem b y k) := h.lx
    have hly : ∀ k < 8, limb s'.mem b y k = sel sw (limb s.mem b y k) (limb s.mem b x k) := h.ly
    by_cases hqx : q = x
    · subst hqx
      simp only [swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 8, limb s'.mem b q k = limb s.mem b q k := fun k hk => by rw [hlx k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS q hx
      · have e : ∀ k < 8, limb s'.mem b q k = limb s.mem b y k := fun k hk => by rw [hlx k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS y hy
    by_cases hqy : q = y
    · subst hqy
      simp only [swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 8, limb s'.mem b q k = limb s.mem b q k := fun k hk => by rw [hly k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS q hy
      · have e : ∀ k < 8, limb s'.mem b q k = limb s.mem b x k := fun k hk => by rw [hly k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS x hx
    · simp only [swapV, hqx, hqy, ite_false]
      obtain ⟨h1, h3, -⟩ := sep1_get hq hq''
      obtain ⟨h1', -⟩ := sep1_get hq' hq''
      have e : ∀ k < 8, limb s'.mem b q k = limb s.mem b q k :=
        limb_frame h.frame fun r hr k hk => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega_using [hqx, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, hx'])
          · exact Offset.disjoint _ (by omega_using [hqy, h1', hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, hy'])
      rw [FS, V, val32_congr e]; exact hS q hq''

end

end VG.Proof.X25519.RISCV64
