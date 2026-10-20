module

public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The masks controlling the recovery squaring loop -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

theorem sqMasks_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    {k t : Nat} {dn ok e1 e2 : Bool}
    (h : KS g s0 A live AW liveW V ls s)
    (lk : sK ∈ ls) (lt : sTc ∈ ls) (ld : sDone ∈ ls) (lo : sOk ∈ ls)
    (l1 : sE1 ∈ ls) (l2 : sE2 ∈ ls)
    (hk : k + 1 < 2 ^ 31) (ht : t < 2 ^ 31)
    (vk : V sK = k) (vt : V sTc = t) (vd : V sDone = b2n dn)
    (vo : V sOk = b2n ok) (v1 : V sE1 = b2n e1) (v2 : V sE2 = b2n e2) :
    WP isa (.block sqMasks) s fun u =>
      KS g s0 A live AW liveW
        (upd (upd (upd V sOk (b2n (ok || (!dn && decide (k < t) && e1))))
          sDone (b2n (dn || (!dn && decide (k < t) && (e1 || (e2 || decide (k + 1 = t)))))))
          sLive (b2n (!dn && decide (k < t) && !e1 && !(e2 || decide (k + 1 = t)))))
        (sLive :: sDone :: sOk :: ls) u := by
  unfold sqMasks
  refine wp_movS (h.readSlot lk) fun s1 U1 _ => ?_
  have h1 := h.of_rest U1.keeps (by decide) U1.mem
  have E1 : s1.gpr .eax = BitVec.ofNat 32 k := by
    rw [U1.gpr, vk]
  refine wp_movS (h1.readSlot lt) fun s2 U2 _ => ?_
  have h2 := h1.of_rest U2.keeps (by decide) U2.mem
  have E2 : s2.gpr .edx = BitVec.ofNat 32 t := by
    rw [U2.gpr, vt]
  refine wp_movS rfl fun s3 U3 _ => ?_
  have h3 := h2.of_rest U3.keeps (by decide) U3.mem
  have E3 : s3.gpr .ebx = BitVec.ofNat 32 k := by
    rw [U3.gpr, U2.other .eax (by decide), E1]
  refine wp_subS rfl fun s4 U4 _ => ?_
  have h4 := h3.of_rest U4.keeps (by decide) U4.mem
  have E4 : s4.gpr .ebx = (BitVec.ofNat 32 k - BitVec.ofNat 32 t) := by
    rw [U4.gpr, E3, U3.other .edx (by decide), E2]
  refine wp_shr (by decide) fun s5 U5 _ => ?_
  have h5 := h4.of_rest U5.keeps (by decide) U5.mem
  have E5 : s5.gpr .ebx = BitVec.ofNat 32 (b2n (decide (k < t))) := by
    rw [U5.gpr, E4, VG.Proof.Rsa.lt_bv (by omega) ht]
  refine wp_movS (h5.readSlot ld) fun s6 U6 _ => ?_
  have h6 := h5.of_rest U6.keeps (by decide) U6.mem
  have E6 : s6.gpr .ecx = BitVec.ofNat 32 (b2n dn) := by
    rw [U6.gpr, vd]
  refine wp_movS rfl fun s7 U7 _ => ?_
  have h7 := h6.of_rest U7.keeps (by decide) U7.mem
  have E7 : s7.gpr .ebp = BitVec.ofNat 32 (b2n dn) := by
    rw [U7.gpr, E6]
  refine wp_logicS (.inr rfl) rfl fun s8 U8 => ?_
  have h8 := h7.of_rest U8.keeps (by decide) U8.mem
  have E8 : s8.gpr .ebp = (BitVec.ofNat 32 (b2n dn) ^^^ 1) := by
    rw [U8.gpr, ite_eq_right (by decide), E7]
  refine wp_logicS (.inl rfl) rfl fun s9 U9 => ?_
  have h9 := h8.of_rest U9.keeps (by decide) U9.mem
  have E9 : s9.gpr .ebx = (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)) := by
    rw [U9.gpr, ite_eq_left rfl, U8.other .ebx (by decide), U7.other .ebx (by decide), U6.other .ebx (by decide), E5, E8]
  refine wp_addS rfl fun s10 U10 _ => ?_
  have h10 := h9.of_rest U10.keeps (by decide) U10.mem
  have E10 : s10.gpr .eax = (BitVec.ofNat 32 k + 1) := by
    rw [U10.gpr, U9.other .eax (by decide), U8.other .eax (by decide), U7.other .eax (by decide), U6.other .eax (by decide), U5.other .eax (by decide), U4.other .eax (by decide), U3.other .eax (by decide), U2.other .eax (by decide), E1]
  refine wp_logicS (.inr rfl) rfl fun s11 U11 => ?_
  have h11 := h10.of_rest U11.keeps (by decide) U11.mem
  have E11 : s11.gpr .eax = ((BitVec.ofNat 32 k + 1) ^^^ BitVec.ofNat 32 t) := by
    rw [U11.gpr, ite_eq_right (by decide), E10, U10.other .edx (by decide), U9.other .edx (by decide), U8.other .edx (by decide), U7.other .edx (by decide), U6.other .edx (by decide), U5.other .edx (by decide), U4.other .edx (by decide), U3.other .edx (by decide), E2]
  refine wp_subS rfl fun s12 U12 _ => ?_
  have h12 := h11.of_rest U12.keeps (by decide) U12.mem
  have E12 : s12.gpr .eax = (((BitVec.ofNat 32 k + 1) ^^^ BitVec.ofNat 32 t) - 1) := by
    rw [U12.gpr, E11]
  refine wp_shr (by decide) fun s13 U13 _ => ?_
  have h13 := h12.of_rest U13.keeps (by decide) U13.mem
  have E13 : s13.gpr .eax = BitVec.ofNat 32 (b2n (decide (k + 1 = t))) := by
    rw [U13.gpr, E12, VG.Proof.Rsa.eq1_bv hk ht]
  refine wp_orS (h13.readSlot l2) fun s14 U14 => ?_
  have h14 := h13.of_rest U14.keeps (by decide) U14.mem
  have E14 : s14.gpr .eax = (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2)) := by
    rw [U14.gpr, E13, v2]
  refine wp_movS (h14.readSlot l1) fun s15 U15 _ => ?_
  have h15 := h14.of_rest U15.keeps (by decide) U15.mem
  have E15 : s15.gpr .edx = BitVec.ofNat 32 (b2n e1) := by
    rw [U15.gpr, v1]
  refine wp_movS rfl fun s16 U16 _ => ?_
  have h16 := h15.of_rest U16.keeps (by decide) U16.mem
  have E16 : s16.gpr .ebp = (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)) := by
    rw [U16.gpr, U15.other .ebx (by decide), U14.other .ebx (by decide), U13.other .ebx (by decide), U12.other .ebx (by decide), U11.other .ebx (by decide), U10.other .ebx (by decide), E9]
  refine wp_logicS (.inl rfl) rfl fun s17 U17 => ?_
  have h17 := h16.of_rest U17.keeps (by decide) U17.mem
  have E17 : s17.gpr .ebp = ((BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)) &&& BitVec.ofNat 32 (b2n e1)) := by
    rw [U17.gpr, ite_eq_left rfl, E16, U16.other .edx (by decide), E15]
  refine wp_orS (h17.readSlot lo) fun s18 U18 => ?_
  have h18 := h17.of_rest U18.keeps (by decide) U18.mem
  have E18 : s18.gpr .ebp = (((BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)) &&& BitVec.ofNat 32 (b2n e1)) ||| BitVec.ofNat 32 (b2n ok)) := by
    rw [U18.gpr, E17, vo]
  refine WP.block_append (WP.mono (h18.storeSlot (d := sOk) (by decide) .ebp)
    fun s19 ⟨h19, _, R19⟩ => ?_)
  have E19 : (s18.gpr .ebp).toNat = ((((BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)) &&& BitVec.ofNat 32 (b2n e1)) ||| BitVec.ofNat 32 (b2n ok))).toNat := by
    rw [E18]
  rw [E19] at h19
  refine wp_movS rfl fun s20 U20 _ => ?_
  have h20 := h19.of_rest U20.keeps (by decide) U20.mem
  have E20 : s20.gpr .ebp = BitVec.ofNat 32 (b2n e1) := by
    rw [U20.gpr, R19.1 .edx (by decide), U18.other .edx (by decide), U17.other .edx (by decide), U16.other .edx (by decide), E15]
  refine wp_orS rfl fun s21 U21 => ?_
  have h21 := h20.of_rest U21.keeps (by decide) U21.mem
  have E21 : s21.gpr .ebp = (BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) := by
    rw [U21.gpr, E20, U20.other .eax (by decide), R19.1 .eax (by decide), U18.other .eax (by decide), U17.other .eax (by decide), U16.other .eax (by decide), U15.other .eax (by decide), E14]
  refine wp_logicS (.inl rfl) rfl fun s22 U22 => ?_
  have h22 := h21.of_rest U22.keeps (by decide) U22.mem
  have E22 : s22.gpr .ebp = ((BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1))) := by
    rw [U22.gpr, ite_eq_left rfl, E21, U21.other .ebx (by decide), U20.other .ebx (by decide), R19.1 .ebx (by decide), U18.other .ebx (by decide), U17.other .ebx (by decide), U16.other .ebx (by decide), U15.other .ebx (by decide), U14.other .ebx (by decide), U13.other .ebx (by decide), U12.other .ebx (by decide), U11.other .ebx (by decide), U10.other .ebx (by decide), E9]
  refine wp_orS rfl fun s23 U23 => ?_
  have h23 := h22.of_rest U23.keeps (by decide) U23.mem
  have E23 : s23.gpr .ecx = (BitVec.ofNat 32 (b2n dn) ||| ((BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)))) := by
    rw [U23.gpr, U22.other .ecx (by decide), U21.other .ecx (by decide), U20.other .ecx (by decide), R19.1 .ecx (by decide), U18.other .ecx (by decide), U17.other .ecx (by decide), U16.other .ecx (by decide), U15.other .ecx (by decide), U14.other .ecx (by decide), U13.other .ecx (by decide), U12.other .ecx (by decide), U11.other .ecx (by decide), U10.other .ecx (by decide), U9.other .ecx (by decide), U8.other .ecx (by decide), U7.other .ecx (by decide), E6, E22]
  refine WP.block_append (WP.mono (h23.storeSlot (d := sDone) (by decide) .ecx)
    fun s24 ⟨h24, _, R24⟩ => ?_)
  have E24 : (s23.gpr .ecx).toNat = ((BitVec.ofNat 32 (b2n dn) ||| ((BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1))))).toNat := by
    rw [E23]
  rw [E24] at h24
  refine wp_logicS (.inr rfl) rfl fun s25 U25 => ?_
  have h25 := h24.of_rest U25.keeps (by decide) U25.mem
  have E25 : s25.gpr .ebp = (((BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1))) ^^^ 1) := by
    rw [U25.gpr, ite_eq_right (by decide), R24.1 .ebp (by decide), U23.other .ebp (by decide), E22]
  refine wp_logicS (.inl rfl) rfl fun s26 U26 => ?_
  have h26 := h25.of_rest U26.keeps (by decide) U26.mem
  have E26 : s26.gpr .ebp = ((((BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1))) ^^^ 1) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1))) := by
    rw [U26.gpr, ite_eq_left rfl, E25, U25.other .ebx (by decide), R24.1 .ebx (by decide), U23.other .ebx (by decide), U22.other .ebx (by decide), U21.other .ebx (by decide), U20.other .ebx (by decide), R19.1 .ebx (by decide), U18.other .ebx (by decide), U17.other .ebx (by decide), U16.other .ebx (by decide), U15.other .ebx (by decide), U14.other .ebx (by decide), U13.other .ebx (by decide), U12.other .ebx (by decide), U11.other .ebx (by decide), U10.other .ebx (by decide), E9]
  refine WP.block_append (WP.mono (h26.storeSlot (d := sLive) (by decide) .ebp)
    fun s27 ⟨h27, _, R27⟩ => ?_)
  have E27 : (s26.gpr .ebp).toNat = (((((BitVec.ofNat 32 (b2n e1) ||| (BitVec.ofNat 32 (b2n (decide (k + 1 = t))) ||| BitVec.ofNat 32 (b2n e2))) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1))) ^^^ 1) &&& (BitVec.ofNat 32 (b2n (decide (k < t))) &&& (BitVec.ofNat 32 (b2n dn) ^^^ 1)))).toNat := by
    rw [E26]
  rw [E27] at h27
  obtain ⟨mo, md, ml⟩ := VG.Proof.Rsa.masks_bv (decide (k < t)) (decide (k + 1 = t)) dn ok e1 e2
  have tn (b : Bool) : (BitVec.ofNat 32 (b2n b)).toNat = b2n b := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le b; omega)]
  refine WP.block_nil ?_
  rw [BitVec.or_comm (BitVec.ofNat 32 (b2n (decide (k < t))) &&&
    (BitVec.ofNat 32 (b2n dn) ^^^ 1) &&& BitVec.ofNat 32 (b2n e1)), mo, md, ml, tn, tn, tn] at h27
  exact h27

end VG.Proof.Rsa.X86.Recover
