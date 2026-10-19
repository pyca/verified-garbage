module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Public native loop guards and normalized u32 candidate statuses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem remaining_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s fun t =>
      SearchLive p original used remaining t ∧
      eval .e t = some (decide (remaining = 0)) := by
  have scr := h.input.control_scr h.wr
  have hl : InRegions (s.rd ++ s.wr) p.control 8 := by
    simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide)
  have hv : s.mem.readW p.control 64 = BitVec.ofNat 64 remaining := by
    have hh : word s.mem p.control 0 = BitVec.ofNat 64 remaining :=
      h.headers (0, BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
    simpa only [Bignum.word, off, BitVec.add_zero] using hh
  have h64 : remaining < 2 ^ 64 := by
    have hb : p.remaining < 2 ^ 64 := by
      cases h.input.2
      exact (original.mem.readW (stackArg original 3) 64).isLt
    omega_using [hb, h.remaining_le]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    eval .e t = some (decide (remaining = 0)) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm (by decide), he⟩
  xrun [State.ea, field, off, h.r12, Nat.mul_zero, BitVec.ofInt_natCast, BitVec.add_zero,
    hl, hv, eval, BitVec.and_self, ofNat64_beq_zero h64]

theorem candidate_status_guard (s : State) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)]) s fun t =>
      (eval .e t = some (decide (((s.gpr .rax).setWidth 32).toNat = 1)) ∧
        t.gpr .rax = ((s.gpr .rax).setWidth 32).setWidth 64 ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have he : ((((s.gpr .rax).setWidth 32).setWidth 64) == (1 : BitVec 64)) =
      decide (((s.gpr .rax).setWidth 32).toNat = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_setWidth]
    have hb := ((s.gpr .rax).setWidth 32).isLt
    change (((s.gpr .rax).setWidth 32).toNat % 2 ^ 64 = 1) ↔ _
    rw [Nat.mod_eq_of_lt (by omega_using [hb])]
    simp only [BitVec.toNat_setWidth]
  xrun [eval, sub_beq_zero, he]

theorem loop_guard {s : State} {B : Addr} {status : Nat}
    (scr : Scr s B 128) (hb : s.gpr .r12 = B)
    (hs : word s.mem B 112 = BitVec.ofNat 64 status) (h64 : status < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      (eval .e t = some (decide (status = 4)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 112) 8 := scr.ld (by decide)
  have he : (BitVec.ofNat 64 status == (4 : BitVec 64)) = decide (status = 4) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [State.ea, field, off, hb, hs, hl, Nat.reduceMul, BitVec.ofInt_natCast, eval, sub_beq_zero, he]

theorem second_status_guard {s : State} {status : Nat}
    (hs : s.gpr .rax = BitVec.ofNat 64 status) (h64 : status < 2 ^ 64) :
    WP isa (.block [.alu .cmp .rax (.imm 2)]) s fun t =>
      (eval .e t = some (decide (status = 2)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have he : (BitVec.ofNat 64 status == (2 : BitVec 64)) = decide (status = 2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [hs, eval, sub_beq_zero, he]

end VG.Proof.Ffdh.X86_64.Generation
