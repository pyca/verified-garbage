module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import Aesop.BuiltinRules

/-! # Fixed-length bytewise zero tests for DSA acceptance masks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev zeroByte : List Instr := [.movzx8 .rax (at0 .rsi), .alu .or .r8 (.reg .rax),
  .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]

theorem byte_widen_zero (b : Byte) : b.zeroExtend 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (b.setWidth 64).toNat = 0 at he
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; subst b; rfl

theorem zeroByte_ok {s : State} {p : Addr} {n : Nat}
    (hp : s.gpr .rsi = p) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hr : InRegions (s.rd ++ s.wr) p 1) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block zeroByte) s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ s.mem p = 0) ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧ Keep [.rax, .r8, .rsi, .rcx] s t := by
  have hsub := ofNat64_pred h1 h64
  have hz : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.rax, .r8, .rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .r8 = s.gpr .r8 ||| (s.mem p).zeroExtend 64 ∧ t.zf = some (decide (n = 1)) ∧ t.mem = s.mem)
    ?_ rfl) fun t ⟨⟨htp, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold zeroByte
    xrun [State.ea, at0, hp, hn, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hr, hsub, hz]
  · exact ⟨htp, htn, by rw [ht8]; exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (byte_widen_zero _)), htz, htm, hk⟩

/-- A positive-length zero scan reads every byte, including leading zeros. -/
theorem zeroLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .rsi = p) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (h1 : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop (.block zeroByte) .ne) s fun t =>
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ ∀ b ∈ bs, b = 0) ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .rsi, .rcx] s t := by
  let target := s.gpr .r8 = 0 ∧ ∀ b ∈ bs, b = 0
  let Inv := fun n t => ∃ (ptr : Addr) (rest : List Byte),
    rest.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ t.gpr .rsi = ptr ∧
    t.gpr .rcx = BitVec.ofNat 64 rest.length ∧ Src t B Z ptr rest ∧
    ((t.gpr .r8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.rax, .r8, .rsi, .rcx] s t
  refine WP.loop (M := isa) (body := .block zeroByte) (c := .ne) Inv ?_ bs.length s ?_
  · intro n u ⟨ptr, rest, hlen, hpos, hbnd, hup, hun, hus, htarget, hum, hku⟩
    cases rest with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons b rest =>
      have hr : InRegions (u.rd ++ u.wr) ptr 1 := by simpa using hus.rd 0 (by simp)
      have hbyte : u.mem ptr = b := by
        have he := hus.val 0 (by simp)
        change u.mem (ptr + 0) = b at he
        exact (congrArg u.mem (BitVec.add_zero ptr)).symm.trans he
      refine WP.mono (zeroByte_ok hup hun hr (by simp) (by omega))
        fun t ⟨htp, htn, ht8, htz, htm, hkt⟩ => ?_
      rw [hbyte] at ht8
      have htarget' : (t.gpr .r8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target := by
        rw [ht8, ← htarget]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact and_assoc
      have hk : Keep [.rax, .r8, .rsi, .rcx] s t := (hku.trans hkt).mono (by decide)
      by_cases he : rest.length = 0
      · left
        refine ⟨?_, ?_, htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some false
          simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
        · simpa only [List.length_eq_zero_iff.mp he, List.not_mem_nil, forall_const, false_implies, implies_true, and_true] using htarget'
      · right
        refine ⟨?_, rest.length, by simp only [List.length_cons] at hlen; omega,
          ptr + 1, rest, rfl, by omega, by simp only [List.length_cons] at hlen; omega,
          htp, ?_, source_tail (hus.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some true
          simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he, decide_false, Option.map_some, Bool.not_false]
        · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, bs, rfl, h1, h64, hp, hn, hs, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64
