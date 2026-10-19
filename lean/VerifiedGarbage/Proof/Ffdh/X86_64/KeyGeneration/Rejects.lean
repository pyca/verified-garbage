module
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Exits
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # The key-generation controller's rejections: one fewer scalar or key -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word controllerValue
  controllerValue_unchanged)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- `rax`, a status, compared with 1, 2 or 3. -/
theorem rax_guard {s : State} {status : Nat} (hs : s.gpr .rax = BitVec.ofNat 64 status)
    (h64 : status < 2 ^ 64) (n : BitVec 32) (k : Nat) (hn : BitVec.signExtend 64 n = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) :
    WP isa (.block [.alu .cmp .rax (.imm n)]) s fun t =>
      (eval .e t = some (decide (status = k)) ∧ t.mem = s.mem ∧ t.gpr .rax = s.gpr .rax) ∧
        Keep [.rax] s t := by
  have he : (BitVec.ofNat 64 status == BitVec.ofNat 64 k) = decide (status = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hk]
  refine WP.keep [.rax] ?_ rfl
  xrun [hs, eval, sub_beq_zero, hn, he]

def scalarValues (scalars : Nat) : List (Nat × BitVec 64) :=
  [(1, BitVec.ofNat 64 (scalars - 1)), (14, 4)]

def publicValues (keys : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (keys - 1)), (1, 128), (14, 4)]

theorem scalarValues_bound (scalars : Nat) : ∀ e ∈ scalarValues scalars, e.1 < 16 := by
  simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem publicValues_bound (keys : Nat) : ∀ e ∈ publicValues keys, e.1 < 16 := by
  simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_rejected_scalar {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : 0 < scalars) :
    WP isa (.block rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ word t.mem p.control 112 = 4 := by
  have scr := h.input.control_scr (t := s) h.wr
  have hst : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv1
  have e1 : BitVec.ofNat 64 scalars - BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (scalars - 1) := by
    have := h.scalars_le
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from by decide,
      BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    omega
  have e1' : BitVec.ofNat 64 scalars - 1 = BitVec.ofNat 64 (scalars - 1) := by
    rw [← e1]; rfl
  have h4 : BitVec.setWidth 64 (4 : BitVec 32) = 4 := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = writeController s.mem p.control (scalarValues scalars)) ?_ rfl) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedScalar writeController scalarValues
    simp only [List.foldl_cons, List.foldl_nil]
    xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, hv1, e1, e1', h4,
      hl 8 (by decide), hst 8 (by decide), hst 112 (by decide)]
  have hh : Slots t.mem p.control (p.headers used keys (scalars - 1)) := by
    refine headers_after _ (scalarValues_bound scalars) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le h.keys_le (by have := h.scalars_le; omega) _ (scalarValues_bound scalars)
    (by simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by cases r <;> simp_all [calleeSaved])) hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (scalarValues_bound scalars) 14 (by decide)]
  simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

theorem key_rejected_public {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hk : 0 < keys) :
    WP isa (.block rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ word t.mem p.control 112 = 4 := by
  have scr := h.input.control_scr (t := s) h.wr
  have hst : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hl0 : InRegions (s.rd ++ s.wr) p.control 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hs0 : InRegions s.wr p.control 8 := by simpa only [BitVec.add_zero] using hst 0 (by decide)
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.mul_zero, BitVec.add_zero] at hv0
  have e0 : BitVec.ofNat 64 keys - BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (keys - 1) := by
    have := h.keys_le
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from by decide,
      BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    omega
  have e0' : BitVec.ofNat 64 keys - 1 = BitVec.ofNat 64 (keys - 1) := by
    rw [← e0]; rfl
  have h4 : BitVec.setWidth 64 (4 : BitVec 32) = 4 := by decide
  have h128 : BitVec.setWidth 64 (128 : BitVec 32) = 128 := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = writeController s.mem p.control (publicValues keys)) ?_ rfl) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedPublic writeController publicValues
    simp only [List.foldl_cons, List.foldl_nil]
    xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, Nat.mul_zero,
      BitVec.add_zero, hv0, e0, e0', h4, h128, hl0, hs0, hst 8 (by decide), hst 112 (by decide)]
  have hh : Slots t.mem p.control (p.headers used (keys - 1) 128) := by
    refine headers_after _ (publicValues_bound keys) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le (by have := h.keys_le; omega) (by decide) _ (publicValues_bound keys)
    (by simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by cases r <;> simp_all [calleeSaved])) hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (publicValues_bound keys) 14 (by decide)]
  simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

end VG.Proof.Ffdh.X86_64.KeyGeneration
