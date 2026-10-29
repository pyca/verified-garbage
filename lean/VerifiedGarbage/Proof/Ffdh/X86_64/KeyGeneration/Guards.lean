module
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live

/-! # The key-generation controller's tests of its budgets and tape -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64.Generation (loop_guard)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- A budget, at the controller's word `j`, compared with zero. -/
theorem budget_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {j n : Nat} (hj : j < 16)
    (hv : (j, BitVec.ofNat 64 n) ∈ p.headers used keys scalars) (hn : n ≤ 128) :
    WP isa (.block [.mov .rax (.mem (field j)), .alu .test .rax (.reg .rax)]) s fun t =>
      KeyLive p original used keys scalars t ∧ eval .e t = some (decide (n = 0)) := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 (8 * j)) 8 :=
    scr.ld (by omega)
  have hw : s.mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = BitVec.ofNat 64 n := by
    simpa only [Bignum.word, off] using h.header hv
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    eval .e t = some (decide (n = 0)) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm (by decide), he⟩
  xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, hl, hw, eval, BitVec.and_self,
    ofNat64_beq_zero (show n < 2 ^ 64 by omega)]

theorem keys_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s fun t =>
      KeyLive p original used keys scalars t ∧ eval .e t = some (decide (keys = 0)) :=
  budget_guard h (j := 0) (by decide) (by simp [KeyPublic.headers]) h.keys_le

theorem scalars_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [.mov .rax (.mem (field 1)), .alu .test .rax (.reg .rax)]) s fun t =>
      KeyLive p original used keys scalars t ∧ eval .e t = some (decide (scalars = 0)) :=
  budget_guard h (j := 1) (by decide) (by simp [KeyPublic.headers]) h.scalars_le

/-- Whether the tape holds less than an attempt. -/
theorem room_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [.mov .rax (.mem (field 10)), .alu .cmp .rax (.mem (field 2))]) s fun t =>
      KeyLive p original used keys scalars t ∧
        eval .b t = some (decide (p.randLen - used < p.len)) := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv2 hv10
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hk : p.len < 2 ^ 64 := by have := h.input.len_lt; omega
  have hb : (BitVec.ofNat 64 (p.randLen - used)).toNat < (BitVec.ofNat 64 p.len).toNat ↔
      p.randLen - used < p.len := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.randLen - used < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hk]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    eval .b t = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm (by decide), he⟩
  xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, hl 16 (by decide),
    hl 80 (by decide), hv2, hv10, eval]
  simp only [decide_eq_decide]
  exact hb

theorem done_loop_guard {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some false ∧ KeyDone p original r t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hb : r.status < 2 ^ 64 := by
    unfold Spec.Ffdh.KeySearchResult.status; split <;> decide
  refine WP.mono (loop_guard scr h.r12 h.status hb) fun t ⟨⟨he, hm⟩, k⟩ => ?_
  refine ⟨?_, h.keep k hm (by decide)⟩
  rw [he]
  congr 1
  unfold Spec.Ffdh.KeySearchResult.status
  split <;> rfl

theorem live_loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some true ∧ KeyLive p original used keys scalars t := by
  refine WP.mono (loop_guard (status := 4) (h.input.control_scr (t := s) h.wr) h.r12 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm (by decide)⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
