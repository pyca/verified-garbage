module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Expanded-bit lookahead, read once from high to low. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off read1_eq)
open VG.Proof.Ed448.WnafWide (bit look)

private theorem byte_zext (b : BitVec 8) :
    (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h := b.isLt
  omega

theorem loadByte_ok {s : State} {base : Addr} (hs : Scr s base) {i j : Nat}
    (hi : i < 456) (hj : j < 8) (hp : s.gpr .x2 = off base i) (d : Reg) :
    WP isa (.block [.ldrb d .x2 (BITS+j)]) s fun u =>
      u.gpr d = BitVec.ofNat 64 (s.mem (off base (BITS+i+j))).toNat ∧
      Keeps [d] s u ∧ u.mem = s.mem := by
  have enc : (BITS+j)%1=0 ∧ BITS+j<4096 := ⟨Nat.mod_one _,by simp only [BITS]; omega⟩
  have ea : off base i + BitVec.ofNat 64 (BITS+j) = off base (BITS+i+j) := by
    rw [off, off, Offset.add_add]
    congr 2
    omega
  have hr := hs.read (d := BITS+i+j) (n := 1) (by simp only [BITS]; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self,
    hp, ea, State.load, hr, read1_eq, ite_true, Option.map_some, Option.bind_some,
    RegUpd.gpr_write_self, byte_zext, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hn => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hn
  exact RegUpd.gpr_write_of_ne _ _ _ hn

/-- The independent lower-bit suffix of loadBits. -/
def readLow (n : Nat) : List Instr :=
  (List.range n).reverse.flatMap fun j =>
    [.ldrb .x5 .x2 (BITS+j), .lsl .x .x4 .x4 1, .add .x .x4 .x4 .x5]

theorem appendBit_ok {s : State} {a b : Nat}
    (ha : s.gpr .x4 = BitVec.ofNat 64 a) (hb : s.gpr .x5 = BitVec.ofNat 64 b) :
    WP isa (.block [.lsl .x .x4 .x4 1, .add .x .x4 .x4 .x5]) s fun u =>
      u.gpr .x4 = BitVec.ofNat 64 (a*2+b) ∧ Keeps [.x4] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ha, hb, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 1 = BitVec.ofNat 64 2 from rfl,
      ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

def readOne (j : Nat) : List Instr :=
  [.ldrb .x5 .x2 (BITS+j), .lsl .x .x4 .x4 1, .add .x .x4 .x4 .x5]

theorem readOne_ok {s : State} {base : Addr} (hs : Scr s base) {i j k a : Nat}
    (hi : i < 456) (hj : j < 8) (hp : s.gpr .x2 = off base i)
    (hm : s.mem (off base (BITS+i+j)) = BitVec.ofNat 8 (bit k (i+j)))
    (ha : s.gpr .x4 = BitVec.ofNat 64 a) :
    WP isa (.block (readOne j)) s fun u =>
      u.gpr .x4 = BitVec.ofNat 64 (a*2+bit k (i+j)) ∧
      u.gpr .x5 = BitVec.ofNat 64 (bit k (i+j)) ∧
      Keeps [.x4,.x5] s u ∧ u.mem=s.mem := by
  change WP isa (.block (([.ldrb .x5 .x2 (BITS+j)] : List Instr) ++
    [.lsl .x .x4 .x4 1, .add .x .x4 .x4 .x5])) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadByte_ok hs hi hj hp .x5) fun t ⟨ht,hk,hm'⟩ => ?_
  have hbit : t.gpr .x5 = BitVec.ofNat 64 (bit k (i+j)) := by
    rw [ht,hm,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := WnafWide.bit_lt k (i+j); omega)]
  refine WP.mono (appendBit_ok ((hk.1 _ (by decide)).trans ha) hbit) fun u ⟨ua,uk,um⟩ => ?_
  exact ⟨ua,(uk.1 _ (by decide)).trans hbit,(hk.mono (by decide)).trans (uk.mono (by decide)),um.trans hm'⟩

theorem readLow_ok {n : Nat} (hn : n < 8) {s : State} {base : Addr} (hs : Scr s base)
    {i k a : Nat} (hi : i < 456) (hp : s.gpr .x2 = off base i)
    (hm : ∀ j < 8, s.mem (off base (BITS+i+j)) = BitVec.ofNat 8 (bit k (i+j)))
    (ha : s.gpr .x4 = BitVec.ofNat 64 a) :
    WP isa (.block (readLow n)) s fun u =>
      u.gpr .x4 = BitVec.ofNat 64 (a*2^n+look k i n) ∧
      u.gpr .x5 = (if n=0 then s.gpr .x5 else BitVec.ofNat 64 (bit k i)) ∧
      Keeps [.x4,.x5] s u ∧ u.mem=s.mem := by
  induction n generalizing s a with
  | zero =>
    apply WP.block_nil
    refine ⟨?_,rfl,Keeps.refl _ _,rfl⟩
    simpa only [Nat.pow_zero,Nat.mul_one,WnafWide.look_zero,Nat.add_zero] using ha
  | succ n ih =>
    have he : readLow (n+1) = readOne n ++ readLow n := by
      simp only [readLow,readOne,List.range_succ,List.reverse_append,List.reverse_singleton,
        List.singleton_append,List.flatMap_cons]
    rw [he,WP.block_append_iff]
    refine WP.mono (readOne_ok hs hi (by omega) hp (hm n (by omega)) ha) fun t ⟨ta,tb,tk,tm⟩ => ?_
    refine WP.mono (ih (by omega) (hs.of_keeps tk (by decide))
      ((tk.1 _ (by decide)).trans hp) (fun j hj => by rw [tm]; exact hm j hj) ta)
      fun u ⟨ua,ub,uk,um⟩ => ?_
    refine ⟨?_,?_,tk.trans uk,um.trans tm⟩
    · rw [ua,WnafWide.look_step]
    · simp only [Nat.add_one_ne_zero,ite_false]
      by_cases hz : n=0
      · subst n
        simpa only [ite_true,Nat.add_zero] using ub.trans tb
      · simpa only [hz,ite_false] using ub

theorem readPointer_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat}
    (hi : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block [.add .x .x2 .x3 .x19]) s fun u =>
      u.gpr .x2 = off base i ∧ Keeps [.x2] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    RegUpd.gpr_write_self,BitVec.setWidth_eq,hs.x3,hi,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem loadBits_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base) {i k : Nat}
    (hi : i<456) (hc : s.gpr .x19 = BitVec.ofNat 64 i)
    (hm : ∀ j<8, s.mem (off base (BITS+i+j)) = BitVec.ofNat 8 (bit k (i+j))) :
    WP isa (.block (loadBits wide)) s fun u =>
      u.gpr .x4 = BitVec.ofNat 64 (look k i (width wide)) ∧
      u.gpr .x5 = BitVec.ofNat 64 (bit k i) ∧ u.gpr .x2=off base i ∧
      Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem := by
  have hw : width wide - 1 < 8 := by cases wide <;> decide
  have hw0 : width wide - 1 ≠ 0 := by cases wide <;> decide
  have hw1 : width wide-1+1=width wide := by cases wide <;> rfl
  change WP isa (.block (([.add .x .x2 .x3 .x19] : List Instr) ++
    ([.ldrb .x4 .x2 (BITS+width wide-1)] : List Instr) ++ readLow (width wide-1))) s _
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (readPointer_ok hs hc) fun a ⟨ap,ak,am⟩ => ?_
  rw [WP.block_append_iff]
  have hoff : BITS+width wide-1=BITS+(width wide-1) := by
    cases wide <;> rfl
  rw [hoff]
  refine WP.mono (loadByte_ok (hs.of_keeps ak (by decide)) hi hw ap .x4) fun b ⟨ba,bk,bm⟩ => ?_
  have head : b.gpr .x4=BitVec.ofNat 64 (bit k (i+(width wide-1))) := by
    rw [ba,am,hm _ hw,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := WnafWide.bit_lt k (i+(width wide-1));omega)]
  have kAB : Keeps [.x2,.x4,.x5] s b :=
    (ak.mono (by decide)).trans (bk.mono (by decide))
  refine WP.mono (readLow_ok (k:=k) hw (hs.of_keeps kAB (by decide)) hi
    ((bk.1 _ (by decide)).trans ap) (fun j hj => by rw [bm,am];exact hm j hj) head)
    fun u ⟨ua,ub,uk,um⟩ => ?_
  refine ⟨?_,?_,?_,kAB.trans (uk.mono (by decide)),um.trans (bm.trans am)⟩
  · have he := WnafWide.look_succ k i (width wide-1)
    rw [hw1] at he
    rw [ua]
    congr 1
    have hm := Nat.mul_comm (2^(width wide-1)) (bit k (i+(width wide-1)))
    omega
  · simpa only [hw0,ite_false] using ub
  · exact (uk.1 _ (by decide)).trans ((bk.1 _ (by decide)).trans ap)

end VG.Proof.Ed448.AArch64.Sparse
