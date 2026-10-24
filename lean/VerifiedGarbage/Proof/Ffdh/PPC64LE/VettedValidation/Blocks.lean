module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.State
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! Register-only width checking and constant-table address setup. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem header_ok {s : State} {src : Addr} {k : Nat} {dom : List Byte}
    (h : Context src k dom s) (g : Group) (fit : g.len < 2 ^ 15) :
    WP isa (.block [.subi .r0 .r5 g.len]) s fun t =>
      (t.gpr .r0 = 0 ↔ g.len = k) ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_subi (h := by omega)
    (fun t o value => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨?_, o.mem,
      (show Keep [.r0] s t from ⟨o.gpr, o.rd, o.wr⟩).mono (by decide)⟩)
  rw [value, h.width]
  have hk : k < 2 ^ 64 := by have := h.upper; omega
  constructor
  · intro zero
    change BitVec.ofNat 64 k - BitVec.ofNat 64 g.len = 0#64 at zero
    have same := congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 g.len) zero
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at same
    have hn := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
      Nat.mod_eq_of_lt (show g.len < 2 ^ 64 by omega)] at hn
    exact hn.symm
  · intro same
    rw [same, BitVec.sub_self]
    rfl

theorem args_ok {s : State} {table : Addr} {offset : Nat}
    (sym : s.syms tableSym = table) (fit : offset + 8 < 2 ^ 15) :
    WP isa (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) s fun t =>
      t.gpr .r8 = table + BitVec.ofNat 64 (offset + 8) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.r8] (Q := fun t =>
    t.gpr .r8 = table + BitVec.ofNat 64 (offset + 8) ∧ t.mem = s.mem) ?_ rfl rfl) ?_
  · crun [sym, fit]
  · rintro t ⟨⟨ptr, mem⟩, rest⟩
    exact ⟨ptr, mem, rest.mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation
