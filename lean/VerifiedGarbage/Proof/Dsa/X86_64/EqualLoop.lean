module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc

/-! # Fixed-length equality scans for DSA signatures and keys -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev equalByte : List Instr := [.movzx8 .rax (at0 .rsi), .movzx8 .r9 (at0 .rdx),
  .alu .xor .rax (.reg .r9), .alu .or .r8 (.reg .rax),
  .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]

theorem byte_widen_eq (a b : Byte) : a.zeroExtend 64 = b.zeroExtend 64 ↔ a = b := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (a.setWidth 64).toNat = (b.setWidth 64).toNat at he
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; rw [h]

theorem equalByte_ok {s : State} {p q : Addr} {n : Nat}
    (hp : s.gpr .rsi = p) (hq : s.gpr .rdx = q) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block equalByte) s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rdx = q + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ s.mem p = s.mem q) ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧ Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := by
  have hsub := ofNat64_pred h1 h64
  have hz : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rdx = q + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .r8 = s.gpr .r8 ||| ((s.mem p).zeroExtend 64 ^^^ (s.mem q).zeroExtend 64) ∧
    t.zf = some (decide (n = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨htp, htq, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold equalByte
    xrun [State.ea, at0, hp, hq, hn, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hrp, hrq, hsub, hz]
  · refine ⟨htp, htq, htn, ?_, htz, htm, hk⟩
    rw [ht8]
    exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (BitVec.xor_eq_zero_iff.trans (byte_widen_eq _ _)))

/-- Both buffers are read completely, even after the first unequal byte. -/
theorem equalLoop_ok {s : State} {B p q : Addr} {Z : Nat} {as bs : List Byte}
    (hp : s.gpr .rsi = p) (hq : s.gpr .rdx = q) (hn : s.gpr .rcx = BitVec.ofNat 64 as.length)
    (ha : Src s B Z p as) (hb : Src s B Z q bs) (hlen : as.length = bs.length)
    (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64) :
    WP isa (.loop (.block equalByte) .ne) s fun t =>
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ as = bs) ∧ t.mem = s.mem ∧
      Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := by
  let target := s.gpr .r8 = 0 ∧ as = bs
  let Inv := fun n t => ∃ (pa pb : Addr) (aa bb : List Byte),
    aa.length = n ∧ bb.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧
    t.gpr .rsi = pa ∧ t.gpr .rdx = pb ∧ t.gpr .rcx = BitVec.ofNat 64 aa.length ∧
    Src t B Z pa aa ∧ Src t B Z pb bb ∧
    ((t.gpr .r8 = 0 ∧ aa = bb) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t
  refine WP.loop (M := isa) (body := .block equalByte) (c := .ne) Inv ?_ as.length s ?_
  · intro n u ⟨pa, pb, aa, bb, hla, hlb, hpos, hbnd, hup, huq, hun, hua, hub, htarget, hum, hku⟩
    cases aa with
    | nil => simp only [List.length_nil] at hla; omega
    | cons a aa =>
      cases bb with
      | nil => simp only [List.length_nil] at hlb; omega
      | cons b bb =>
        have hrp : InRegions (u.rd ++ u.wr) pa 1 := by simpa using hua.rd 0 (by simp)
        have hrq : InRegions (u.rd ++ u.wr) pb 1 := by simpa using hub.rd 0 (by simp)
        have va : u.mem pa = a := by
          have he := hua.val 0 (by simp)
          change u.mem (pa + 0) = a at he
          exact (congrArg u.mem (BitVec.add_zero pa)).symm.trans he
        have vb : u.mem pb = b := by
          have he := hub.val 0 (by simp)
          change u.mem (pb + 0) = b at he
          exact (congrArg u.mem (BitVec.add_zero pb)).symm.trans he
        refine WP.mono (equalByte_ok hup huq hun hrp hrq (by simp) (by omega))
          fun t ⟨htp, htq, htn, ht8, htz, htm, hkt⟩ => ?_
        rw [va, vb] at ht8
        have htarget' : (t.gpr .r8 = 0 ∧ aa = bb) ↔ target := by
          rw [ht8, ← htarget, List.cons.injEq]
          exact and_assoc
        have hk : Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := (hku.trans hkt).mono (by decide)
        by_cases he : aa.length = 0
        · left
          refine ⟨?_, ?_, htm.trans hum, hk⟩
          · change VG.X86_64.eval .ne t = some false
            simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
          · have heb : bb.length = 0 := by simp only [List.length_cons] at hla hlb; omega
            simpa only [List.length_eq_zero_iff.mp he, List.length_eq_zero_iff.mp heb, and_true] using htarget'
        · right
          refine ⟨?_, aa.length, by simp only [List.length_cons] at hla; omega,
            pa + 1, pb + 1, aa, bb, rfl, by simp only [List.length_cons] at hla hlb; omega,
            by omega, by simp only [List.length_cons] at hla; omega, htp, htq, ?_,
            source_tail (hua.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt),
            source_tail (hub.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
          · change VG.X86_64.eval .ne t = some true
            simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he, decide_false, Option.map_some, Bool.not_false]
          · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, q, as, bs, rfl, hlen.symm, h1, h64, hp, hq, hn, ha, hb, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64
