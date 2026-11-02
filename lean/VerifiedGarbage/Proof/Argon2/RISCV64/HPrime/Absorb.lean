module

import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! # H′ on RISCV64: absorbing the length prefix, the previous digest or the input -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (Upd wp_mv wp_addi wp_li)
open VG.Spec.Blake2 (b Repr bytesAt)

/-! ## A fixed workspace buffer -/

structure FixedArgs (s t : State) (offset size : Nat) : Prop where
  count : t.gpr .a1 = 0
  data : t.gpr .a2 = s.gpr .s4 + BitVec.ofNat 64 offset
  size : t.gpr .a3 = BitVec.ofNat 64 size
  other : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem fixedArgs_ok (s : State) (offset size : Nat) (ho : offset < 2048) (hn : size < 2048) :
    WP isa (.block (fixedArgs offset size)) s fun t =>
      FixedArgs s t offset size :=
  wp_li (by decide) fun a ha => wp_addi ho fun c hc => wp_li hn fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr]; rfl,
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)],
      ht.gpr,
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

theorem absorbFixed_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (offset size : Nat)
    (offsetUpper : offset < 2048) (sizeUpper : size < 2048)
    (offsetLower : 768 ≤ offset) (sizeBound : offset + size ≤ 16384)
    (repr : Repr b h0 s.mem (s.gpr .s4) [])
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (s.gpr .s4) (bytesAt s.mem (s.gpr .s4 + BitVec.ofNat 64 offset) size) ∧
      Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetUpper sizeUpper).mono fun u hu => ?_)
  have p : u.gpr .s4 = s.gpr .s4 := hu.other _ (by decide) (by decide) (by decide)
  have sp := hu.sp
  have len : (u.gpr .a3).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wr : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .s4) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .a1 = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .a3).toNat < 2 ^ 64 := by
    simp only [List.length_nil, Nat.zero_add, len]; omega
  have cover : Covers [⟨u.gpr .a2, (u.gpr .a3).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .s4, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .a3).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .a2, (u.gpr .a3).toNat⟩ : Region).Disjoint ⟨u.gpr .s4, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  have dw : (⟨u.gpr .a2, (u.gpr .a3).toNat⟩ : Region).Disjoint ⟨u.gpr .s4 + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  refine (update_ok u h0 [] hr hc hb wr cover ds dw).mono ?_
  rintro t ⟨repr', regs, rd, wr', sp', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr => (regs r hr).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · exact hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)
  · simpa only [p, sp, hu.mem] using update_frame (u.gpr .s4) frame

/-! ## The caller's input -/

structure InputArgs (s t : State) : Prop where
  count : t.gpr .a1 = 4
  data : t.gpr .a2 = s.gpr .s0
  size : t.gpr .a3 = s.gpr .s1
  other : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem inputArgs_ok (s : State) :
    WP isa (.block inputArgs) s (InputArgs s) :=
  wp_li (by decide) fun a ha => wp_mv fun c hc => wp_mv fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr]; rfl,
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)],
      by rw [ht.gpr, hc.other _ (by decide), ha.other _ (by decide)],
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

theorem InputArgs.keeps {s t : State} (h : InputArgs s t) : Keeps s t := by
  refine ⟨fun r hr => h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr),
    h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem]; exact Frame.refl _ _

theorem absorbInput_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (headBytes : List Byte) (prefixLen : headBytes.length = 4)
    (repr : Repr b h0 s.mem (s.gpr .s4) headBytes) (len : (s.gpr .s1).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .s0, (s.gpr .s1).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .s0, (s.gpr .s1).toNat⟩ : Region).Disjoint ⟨s.gpr .s4, 16384⟩) :
    WP isa absorbInput s fun t =>
      Repr b h0 t.mem (s.gpr .s4) (headBytes ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat) ∧
      Keeps s t := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .s4) headBytes := by rw [hu.mem, ku.s4]; exact repr
  have count : u.gpr .a1 = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .a3).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega
  have wr : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ku.s4, ku.wr]; exact hwr
  have cover : Covers [⟨u.gpr .a2, (u.gpr .a3).toNat⟩] (u.rd ++ u.wr) := by
    rw [hu.data, hu.size, hu.rd, hu.wr]; exact hdata
  have ds : (⟨u.gpr .a2, (u.gpr .a3).toNat⟩ : Region).Disjoint ⟨u.gpr .s4, 192⟩ := by
    rw [hu.data, hu.size, ku.s4]
    exact dataWork.sub_right (Region.sub_prefix (by decide))
  have dw : (⟨u.gpr .a2, (u.gpr .a3).toNat⟩ : Region).Disjoint ⟨u.gpr .s4 + 192, 576⟩ := by
    rw [hu.data, hu.size, ku.s4]
    exact dataWork.sub_right (Offset.sub_base _ (by decide))
  refine (update_ok u h0 headBytes repr' count bound wr cover ds dw).mono ?_
  rintro t ⟨result, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', update_frame _ frame⟩⟩
  simpa only [ku.s4, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.RISCV64.HPrime
