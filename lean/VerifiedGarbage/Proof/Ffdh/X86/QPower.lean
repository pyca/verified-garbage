module

public import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# FFDH on i686: a power to q, over its bytes from the first nonzero one

`qScan_ok`: the scan leaves, in the header's words `qpOff` and `qlOff`, the
address of q's first nonzero byte (of its last byte, if all are zero) and
the number of bytes from it on, `lead` of q's bytes past q's address and
short of `p_len` (`Proof/Ffdh/Lead.lean`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.QPower

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86 VG.Proof.Ffdh
open VG.Impl.Ffdh.X86
open VG.Proof.Ffdh.X86.KeyScan (wp_movzx8 word_room bytesAt_getD)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- q's bytes: the domain's third component. -/
abbrev qBytes (m : Mem) (args : Nat → BitVec 32) (len : Nat) : List Byte :=
  Spec.Rsa.bytesAt m (byteAddr (args 2) + BitVec.ofNat 64 (2 * len)) len

/-- The carry of `n + 0xFFFFFFFE`: whether `n` is at least two. -/
theorem carry_two {n : Nat} (hn : n < 2 ^ 31) :
    decide (2 ^ 32 ≤ (BitVec.ofNat 32 n).toNat + (0xFFFFFFFE : BitVec 32).toNat) = decide (2 ≤ n) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  show decide (2 ^ 32 ≤ n + 4294967294) = _
  by_cases h : 2 ≤ n
  · rw [decide_eq_true h, decide_eq_true (by omega_arith)]
  · rw [decide_eq_false h, decide_eq_false (by omega_arith)]

/-- Before byte `i` of q. -/
structure ScanAt (s : State) (len i : Nat) (args : Nat → BitVec 32) (u : State) : Prop where
  esi : u.gpr .esi = args 6 + BitVec.ofNat 32 i
  ecx : u.gpr .ecx = BitVec.ofNat 32 (len - i)
  mem : u.mem = s.mem
  keeps : Keeps [.eax, .ecx, .edx, .esi] s u

/-- One byte of the scan: on to the next while it is before `lead`, and ZF set at `lead`. -/
theorem qScanStep_ok (G : DomGeo args base bytes len (3 * len) s.rd s.wr) {i : Nat} {u : State}
    (hi : i ≤ lead (qBytes s.mem args len)) (I : ScanAt s len i args u) :
    WP isa (.block qScanStep) u fun v =>
      ScanAt s len (if i < lead (qBytes s.mem args len) then i + 1 else i) args v ∧
      v.zf = some (decide (¬ i < lead (qBytes s.mem args len))) := by
  have fit := G.fit
  have lw := G.lower
  have up := G.upper
  obtain ⟨a6, n6⟩ : byteAddr (args 6) = byteAddr (args 2) + BitVec.ofNat 64 (2 * len) ∧
      (args 6).toNat = (args 2).toNat + 2 * len := G.addr (k := 2) (by decide) (by omega_arith)
  generalize hbs : qBytes s.mem args len = bs at hi ⊢
  obtain bl : bs.length = len := by rw [← hbs]; exact VG.Proof.Bignum.bytesAt_length _ _ _
  obtain ne : bs ≠ [] := fun e => by rw [e] at bl; simp at bl; omega_arith
  obtain ll := lead_lt ne
  obtain il : i < len := by omega_arith
  -- The byte.
  obtain ea : u.ea ⟨.esi, 0⟩ = byteAddr (args 2) + BitVec.ofNat 64 (2 * len) + BitVec.ofNat 64 i := by
    change addr (u.gpr .esi) 0 = _
    rw [I.esi, addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith), BitVec.add_zero, ← a6]
    exact addr_eq (by omega_arith)
  obtain rdB : InRegions (u.rd ++ u.wr)
      (byteAddr (args 2) + BitVec.ofNat 64 (2 * len) + BitVec.ofNat 64 i) 1 := by
    rw [I.keeps.2.1, I.keeps.2.2, VG.Offset.add_add]
    exact VG.CallLay.inRegions_sub G.rd (by omega_arith) (by omega_arith)
  obtain byte : u.mem (byteAddr (args 2) + BitVec.ofNat 64 (2 * len) + BitVec.ofNat 64 i) = bs.getD i 0 := by
    rw [← hbs, I.mem, bytesAt_getD _ _ il]
  generalize hb : bs.getD i 0 = b at byte
  obtain bi : bs[i]'(by omega_arith) = b := by rw [← hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_arith), Option.getD_some]
  refine wp_movzx8 ea rdB fun u1 a1 => ?_
  refine wp_addS rfl fun u2 a2 c2 => ?_
  refine wp_sbbS rfl c2 fun u3 a3 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u4 a4 => ?_
  refine wp_movS rfl fun u5 a5 _ => ?_
  refine wp_addS rfl fun u6 a6' c6 => ?_
  refine wp_sbbS rfl c6 fun u7 a7 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u8 a8 => ?_
  refine wp_logicS (.inl rfl) rfl fun u9 a9 => ?_
  refine wp_addS rfl fun u10 a10 _ => ?_
  refine wp_subS rfl fun u11 a11 _ => ?_
  refine wp_testS rfl fun v T z => WP.block_nil ?_
  obtain E4 : u4.gpr .eax = cmask (!(b != 0)) := by
    rw [a4.gpr, ite_eq_right (by decide), a3.gpr, KeyScan.sbb_self, a1.gpr, byte, KeyScan.carry_ne, KeyScan.cmask_not]
  obtain X5 : u5.gpr .edx = BitVec.ofNat 32 (len - i) := by
    rw [a5.gpr, a4.other _ (by decide), a3.other _ (by decide), a2.other _ (by decide), a1.other _ (by decide), I.ecx]
  obtain E7 : u7.gpr .edx = cmask (decide (2 ≤ len - i)) := by
    rw [a7.gpr, KeyScan.sbb_self, X5, carry_two (by omega_arith)]
  generalize hc : (!(b != 0) && decide (2 ≤ len - i)) = c
  obtain E9 : u9.gpr .eax = BitVec.ofNat 32 c.toNat := by
    rw [a9.gpr, ite_eq_left rfl, a8.gpr, ite_eq_left rfl, a7.other _ (by decide), a6'.other _ (by decide),
      a5.other _ (by decide), E4, E7, KeyScan.cmask_and, hc]
    exact cmask_and_one c
  obtain cl : c = decide (i < lead bs) := by
    rw [← hc]
    by_cases h : i < lead bs
    · obtain ⟨_, z⟩ := lead_zero i h
      rw [decide_eq_true h, show b = 0 by rw [← bi]; exact z, decide_eq_true (by omega_arith)]
      rfl
    · rw [decide_eq_false h]
      obtain e : i = lead bs := by omega_arith
      by_cases hl : lead bs + 1 < bs.length
      · obtain nz : b ≠ 0 := by rw [← bi]; subst e; exact lead_nonzero ne hl
        rw [show (b != 0) = true from bne_iff_ne.mpr nz]
        rfl
      · rw [decide_eq_false (by omega_arith), Bool.and_false]
  obtain K : Keeps [.eax, .ecx, .edx, .esi] u v :=
    ((((((((((((a1.keeps.mono (by decide) : Keeps [.eax, .ecx, .edx, .esi] u u1).widen a2.keeps).widen
      a3.keeps).widen a4.keeps).widen a5.keeps).widen a6'.keeps).widen a7.keeps).widen a8.keeps).widen
      a9.keeps).widen a10.keeps).widen a11.keeps).widen (T.keeps []))
  obtain M : v.mem = s.mem := by
    rw [T.mem, a11.mem, a10.mem, a9.mem, a8.mem, a7.mem, a6'.mem, a5.mem, a4.mem, a3.mem, a2.mem, a1.mem, I.mem]
  obtain esi9 : u9.gpr .esi = args 6 + BitVec.ofNat 32 i := by
    rw [a9.other _ (by decide), a8.other _ (by decide), a7.other _ (by decide), a6'.other _ (by decide),
      a5.other _ (by decide), a4.other _ (by decide), a3.other _ (by decide), a2.other _ (by decide),
      a1.other _ (by decide), I.esi]
  obtain ecx10 : u10.gpr .ecx = BitVec.ofNat 32 (len - i) := by
    rw [a10.other _ (by decide), a9.other _ (by decide), a8.other _ (by decide), a7.other _ (by decide),
      a6'.other _ (by decide), a5.other _ (by decide), a4.other _ (by decide), a3.other _ (by decide),
      a2.other _ (by decide), a1.other _ (by decide), I.ecx]
  obtain eax11 : u11.gpr .eax = BitVec.ofNat 32 c.toNat := by
    rw [a11.other _ (by decide), a10.other _ (by decide), E9]
  refine ⟨⟨?_, ?_, M, I.keeps.trans K⟩, ?_⟩
  · rw [congrFun T.gpr .esi, a11.other _ (by decide), a10.gpr, esi9, E9, cl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    by_cases h : i < lead bs
    · rw [decide_eq_true h, ite_eq_left h]; rfl
    · rw [decide_eq_false h, ite_eq_right h]; rfl
  · rw [congrFun T.gpr .ecx, a11.gpr, ecx10, a10.other _ (by decide), E9, cl]
    by_cases h : i < lead bs
    · rw [decide_eq_true h, ite_eq_left h,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by show 1 ≤ len - i; omega_arith)]
      congr 1
    · rw [decide_eq_false h, ite_eq_right h]
      show BitVec.ofNat 32 (len - i) - 0 = _
      rw [BitVec.sub_zero]
  · rw [z, eax11, cl]
    by_cases h : i < lead bs
    · rw [decide_eq_true h, decide_eq_false (not_not.mpr h)]; rfl
    · rw [decide_eq_false h, decide_eq_true h]; rfl

end VG.Proof.Ffdh.X86.QPower
