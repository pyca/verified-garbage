module

public import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
public import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Ed25519.X86.AccumulateStep`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.X86.PointAccumulate`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.BitMask`. -/

/-! Merged from `Proof.Ed25519.X86.PointSelect`. -/
section
/-! Field and point selection by a fixed sequence of masked swaps. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapsEnv (pairs : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  pairs.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a b : Slot) (hab : a ≠ b)
    (sw : Bool) (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block (VG.Impl.X25519.X86.cswap (offset a) (offset b))) s fun t =>
      FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ env t.mem x = swapEnv a b sw (env s.mem x) := by
  have sep := slot_ne (slot_valid b) (slot_valid a) (fun h => hab (offset_inj h))
  refine WP.mono (cswap_ok hc (slot_below (slot_valid a)) (slot_below (slot_valid b)) sep
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ⟨hk, hm', hf, ha, hb⟩ => ?_
  have wide : Frame [sub x 64 864] s.mem t.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨sub x 64 864, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact sub_sub hc.fit (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using [])
        (by simp only [offset]; omega_using [])
    · exact sub_sub hc.fit (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using [])
        (by simp only [offset]; omega_using [])
  refine ⟨⟨hk, wide⟩, hm', ?_⟩
  have hfit := hc.fit
  funext i
  by_cases hia : i = a
  · subst i
    rw [swapEnv, Function.update_of_ne hab, Function.update_self]
    change VG.Proof.X25519.toFe (fe t.mem x (offset a)) = _
    rw [ha]
    cases sw <;> rfl
  · by_cases hib : i = b
    · subst i
      rw [swapEnv, Function.update_self]
      change VG.Proof.X25519.toFe (fe t.mem x (offset b)) = _
      rw [hb]
      cases sw <;> rfl
    · rw [swapEnv, Function.update_of_ne hib, Function.update_of_ne hia]
      apply congrArg VG.Proof.X25519.toFe
      apply fe_frame
      intro k hk'
      apply wd_frame hf
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hs := slot_ne (slot_valid a) (slot_valid i) (fun h => hia (offset_inj h))
        exact sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])
      · have hs := slot_ne (slot_valid b) (slot_valid i) (fun h => hib (offset_inj h))
        exact sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])

theorem swapsEnv_step (pairs : List (Slot × Slot)) (a b : Slot) (sw : Bool)
    {e f g : Env} (h : f = swapEnv a b sw e) (k : g = swapsEnv pairs sw f) :
    g = swapsEnv ((a, b) :: pairs) sw e := by
  rw [k, h]; rfl

theorem swapFields_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (pairs : List (Slot × Slot)) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    (sw : Bool) (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block (swapFields pairs)) s fun t =>
      FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ env t.mem x = swapsEnv pairs sw (env s.mem x) := by
  induction pairs generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl, rfl⟩
  | cons pair pairs ih =>
    rcases pair with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hc a b (hpairs _ List.mem_cons_self) sw hm) fun t ⟨kt, mt, et⟩ => ?_
    refine WP.mono (ih (kt.ctx hc) (fun p hp => hpairs p (List.mem_cons_of_mem _ hp)) (mt.trans hm))
      fun u ⟨ku, mu, eu⟩ => ?_
    exact ⟨kt.trans ku, mu.trans mt, swapsEnv_step pairs a b sw et eu⟩

end VG.Proof.Ed25519.X86
end

/-! One exact scalar-multiplication bit, including masked selection. -/
end

/-! Descending bits follow the exact pointMul recursion. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def scalarBit (s n : Nat) : Bool := decide ((s / 2 ^ n) % 2 ≠ 0)

theorem scalarBit_nat (s n : Nat) : (scalarBit s n).toNat = (s / 2 ^ n) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ n) with h | h <;> simp only [scalarBit, h] <;> decide

/-- A bit of the scalar, through a frame of the slots and the stack a call uses. -/
theorem bit_frame {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem}
    (hf : Frame [sub x 64 960, callStk s] m m')
    (i : Nat) (hi : i < 512) : m' (addr x (7168 + i)) = m (addr x (7168 + i)) := by
  apply hf
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
      (Or.inr (by omega_using [])) : (sub x (7168 + i) 1).Disjoint (sub x 64 960)) _ (Region.contains_self _ _)
  · exact stk_apart hc (d := 7168 + i) (n := 1) (by omega_using [hi]) (by decide) _ (Region.contains_self _ _)

theorem IKeep.word {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : wd t.mem x o = wd s.mem x o :=
  wd_frame1s hc h.frame (by decide) (by omega_using [ho]) (Or.inl ho)

theorem IKeep.bit {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) :=
  bit_frame hc h.frame i hi

end VG.Proof.Ed25519.X86

end

end

/-! Merged from `Proof.Ed25519.X86.PointMulBatch`. -/

@[expose] public section

/-! Complete point multiplication preserves API pointers and scalar bits. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 24 7144, callStk s] s.mem t.mem

theorem MulKeep.ctx {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr h.esp
theorem MulKeep.trans {x : BitVec 32} {s t u : State} (h : MulKeep x s t) (k : MulKeep x t u) :
    MulKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans (by rw [callStk, ← h.esp]; exact k.frame)⟩

theorem MulKeep.of_powers {x : BitVec 32} {s t : State} {o n : Nat} (hc : Ctx x s)
    (h : PowersKeep x o n s t) (ho : 24 ≤ o) (hn : o + n ≤ 7168) : MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨sub x 24 7144, List.mem_cons_self .., sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨sub x 24 7144, List.mem_cons_self .., sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨sub x 24 7144, List.mem_cons_self .., sub_sub hc.fit ho (by omega_using [hn]) (by omega_using [hn])⟩
  · exact ⟨callStk s, by simp, fun _ ha => ha⟩

theorem MulKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : IKeep x s t) :
    MulKeep x s t := MulKeep.of_powers hc (PowersKeep.of_ikeep h 24 0) (by decide) (by decide)

theorem MulKeep.bit {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
      (Or.inr (by omega_using [])) : (sub x (7168 + i) 1).Disjoint (sub x 24 7144)) _ (Region.contains_self _ _)
  · exact stk_apart hc (d := 7168 + i) (n := 1) (by omega_using [hi]) (by decide) _ (Region.contains_self _ _)

end VG.Proof.Ed25519.X86
