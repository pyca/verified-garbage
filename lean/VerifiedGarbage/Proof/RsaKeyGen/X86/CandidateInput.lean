module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateGeometry

/-! # The candidate header keeps native public arguments across every prefilter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Input.out_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 0) 32 = E.out := I.header 0 (by decide)

theorem Input.exponent_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 12) 32 = E.exponent := I.header 3 (by decide)

theorem Input.other_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 20) 32 = E.other := I.header 5 (by decide)

theorem Input.rand_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 28) 32 = E.rand := I.header 7 (by decide)

theorem native_word {m : Mem} {base : Addr} {offset value : Nat}
    (H : m.readW (off base offset) 32 = BitVec.ofNat 32 value) (bound : value < 2 ^ 32) :
    w32 m base offset = value := by rw [w32, H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem Input.length_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 4 = E.length :=
  native_word (I.header 1 (by decide)) (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega)

theorem Input.exponentLength_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 16 = E.exponentLength :=
  native_word (I.header 4 (by decide)) (by have := v.exponentLength; omega)

theorem Input.otherLength_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 24 = E.otherLength :=
  native_word (I.header 6 (by decide)) (by
    have bounds := v.length; unfold Spec.RsaKeyGen.primeLenValid at bounds
    have := v.otherLength; omega)

theorem Input.randLength_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 32 = E.randLength :=
  native_word (I.header 8 (by decide)) v.randLengthFit

theorem Input.capacity_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 40 = E.capacity :=
  native_word (I.header 10 (by decide)) v.capacityFit

theorem Input.keepWorkspace {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (I : Input E eBytes pBytes entropy s) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (F : WorkFrame E s.mem t.mem)
    {ranges : List (Nat × Nat)} (W : WorkspaceFrame E.geometry ranges s.mem t.mem)
    (headerFar : ∀ r ∈ ranges, 48 ≤ r.1)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Input E eBytes pBytes entropy t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  refine I.keep v K base sp F ?_ ?_ symbol
  · intro i index
    exact (W.read32 (by change 4 * i + 4 ≤ E.size; omega)
      (fun r mem => Or.inl (by have := headerFar r mem; omega))).trans (I.header i index)
  · exact (W.read32 (by change 44 + 4 ≤ E.size; omega)
      (fun r mem => Or.inl (by have := headerFar r mem; omega))).trans I.usedPointer

theorem count_low {E : Environment} (v : E.Valid) {m : Mem}
    (H : word m E.base 152 = BitVec.ofNat 64 E.length) : w32 m E.base 152 = E.length := by
  have lengthBound : E.length < 2 ^ 32 := CandidateGeometry.native_length_bound v.length
  have pair := word_eq_w32 m E.base 152
  rw [H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans lengthBound (by decide : 2 ^ 32 < 2 ^ 64))] at pair
  have lo : w32 m E.base 152 < 2 ^ 32 := (m.readW _ 32).isLt
  omega

end VG.Proof.RsaKeyGen.X86.Candidate
