module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed448.WnafWide.Word

/-! ### `Ed448.AArch64.Sparse.Read`, which only this module used -/

section

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
  omega_using []

theorem loadByte_ok {s : State} {base : Addr} (hs : Scr s base) {i j : Nat}
    (hi : i < 456) (hj : j < 8) (hp : s.gpr .x2 = off base i) (d : Reg) :
    WP isa (.block [.ldrb d .x2 (BITS+j)]) s fun u =>
      u.gpr d = BitVec.ofNat 64 (s.mem (off base (BITS+i+j))).toNat ∧
      Keeps [d] s u ∧ u.mem = s.mem := by
  have enc : (BITS+j)%1=0 ∧ BITS+j<4096 := ⟨Nat.mod_one _,by simp only [BITS]; omega_using [hj]⟩
  have ea : off base i + BitVec.ofNat 64 (BITS+j) = off base (BITS+i+j) := by
    rw [off, off, Offset.add_add]
    congr 2
    omega_using []
  have hr := hs.read (d := BITS+i+j) (n := 1) (by simp only [BITS]; omega_using [hi, hj])
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
    rw [ht,hm,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := WnafWide.bit_lt k (i+j); omega_using [this])]
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
    refine WP.mono (readOne_ok hs hi (by omega_using [hn]) hp (hm n (by omega_using [hn])) ha) fun t ⟨ta,tb,tk,tm⟩ => ?_
    refine WP.mono (ih (by omega_using [hn]) (hs.of_keeps tk (by decide))
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
      Nat.mod_eq_of_lt (by have := WnafWide.bit_lt k (i+(width wide-1));omega_using [this])]
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
    omega_using [he, hm]
  · simpa only [hw0,ite_false] using ub
  · exact (uk.1 _ (by decide)).trans ((bk.1 _ (by decide)).trans ap)

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! ### `Ed448.AArch64.Sparse.Write`, which only this module used -/

section

/-! Store one signed digit and advance its bounded public counter. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off write1_eq)

theorem encode_digit {d : Int} (hd : -127≤d ∧ d≤127) :
    (BitVec.ofInt 64 d).setWidth 8 = BitVec.ofInt 8 d := by
  have hc : ∀ (n : Nat), n<255 → (BitVec.ofInt 64 ((n : Int)-127)).setWidth 8 =
      BitVec.ofInt 8 ((n : Int)-127) := by decide +kernel
  obtain ⟨n,hn,he⟩ : ∃ (n : Nat), n<255 ∧ d=(n : Int)-127 := by
    refine ⟨(d+127).toNat,?_,?_⟩ <;> omega_using [hd]
  rw [he]
  exact hc n hn

theorem writeDigit_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat}
    (hi : i<464) (hp : s.gpr .x2=off base i) (hc : s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block writeDigit) s fun u =>
      u.gpr .x19=BitVec.ofNat 64 (i+1) ∧ Keeps [.x19] s u ∧
      u.mem=s.mem.writeW (off base (BITS+i)) ((s.gpr .x7).setWidth 8) := by
  have enc : BITS%1=0 ∧ BITS<4096 := ⟨Nat.mod_one _,by decide⟩
  have ea : off base i + BitVec.ofNat 64 BITS=off base (BITS+i) := by
    rw [off,off,Offset.add_add]
    congr 2
    omega_using []
  have hw := hs.write (d:=BITS+i) (n:=1) (by simp only [BITS];omega_using [hi])
  apply WP.of_runBlock
  simp only [writeDigit,runBlock_cons,runStep_some,runBlock_nil,exec,addr,enc,and_self,
    hp,ea,State.store,State.read,Size.bits,BitVec.setWidth_setWidth_of_le _ (by decide : 8≤32),
    hw,ite_true,Option.bind_some,write1_eq,Nat.reduceLT,RegUpd.gpr_write,
    BitVec.setWidth_eq,hc,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  · exact (BitVec.ofNat_add i 1).symm
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

private theorem counter_fact : ∀ i<456,
    (BitVec.ofNat 64 (i+1)-BitVec.ofNat 64 456 == 0)=decide (i+1=456) := by decide +kernel

theorem counter_ok {s : State} {i : Nat} (hi:i<456) (hc:s.gpr .x19=BitVec.ofNat 64 (i+1)) :
    WP isa (.block [.subImm .x .x9 .x19 456]) s fun u =>
      (u.gpr .x9==0)=decide (i+1=456) ∧ Keeps [.x9] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,hc,
    Option.some.injEq,exists_eq_left']
  exact ⟨counter_fact i hi,⟨fun r hr => by
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false],rfl,rfl⟩,rfl⟩

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! A signed digit and the exact next biased carry, framed to one byte. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Digit.lean`, which only this module imported.
section

/-! One bounded arithmetic step of the public signed recoder. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Proof.X448.AArch64 (Keeps)

private theorem half_enc (wide : Bool) : half wide < 4096 := by cases wide <;> decide
private theorem radix_enc (wide : Bool) : radix wide < 4096 := by cases wide <;> decide
private theorem half_word (wide : Bool) :
    (BitVec.ofNat 16 (half wide)).setWidth 64 = BitVec.ofNat 64 (half wide) := by cases wide <;> rfl
private theorem mask_word (wide : Bool) :
    (BitVec.ofNat 16 (radix wide-1)).setWidth 64 = BitVec.ofNat 64 (radix wide-1) := by cases wide <;> rfl

theorem digitStep_ok (wide : Bool) {s : State} {bits c : Nat}
    (hb : bits < radix wide) (hc : c ≤ radix wide)
    (h4 : s.gpr .x4 = BitVec.ofNat 64 bits)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (bits%2))
    (h6 : s.gpr .x6 = BitVec.ofNat 64 c) :
    WP isa (.block (digitStep wide)) s fun u =>
      u.gpr .x7 = BitVec.ofInt 64 (localDigit wide bits c) ∧
      u.gpr .x6 = BitVec.ofNat 64 (carryNext wide bits c) ∧
      Keeps [.x4,.x6,.x7,.x8,.x9] s u ∧ u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [digitStep, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    half_enc, radix_enc, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, RegUpd.zf_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    CondCode.holds, h4, h5, h6, half_word, mask_word, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · have he := WnafWide.rawDigit_ok wide hb hc
    simpa only [WnafWide.rawDigit, BitVec.ofNat_add, show (BitVec.setWidth 64 (1 : BitVec 16)) = 1 from rfl, show (BitVec.setWidth 64 (0 : BitVec 16)) = 0 from rfl] using he
  · have he := WnafWide.rawCarry_ok wide hb hc
    simpa only [WnafWide.rawDigit, BitVec.ofNat_add, show (BitVec.setWidth 64 (1 : BitVec 16)) = 1 from rfl, show (BitVec.setWidth 64 (0 : BitVec 16)) = 0 from rfl] using he
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)

/-- All general-purpose registers the recoder may write. -/
def recClob : List Reg := [.x2,.x4,.x5,.x6,.x7,.x8,.x9,.x19]

def Enc (wide : Bool) (k i : Nat) : Byte := BitVec.ofInt 8 (digitAt wide k i)

structure StepOut (base : Addr) (wide : Bool) (k i : Nat) (s u : State) : Prop where
  scr : Scr u base
  x19 : u.gpr .x19=BitVec.ofNat 64 (i+1)
  carry : ∃ c≤radix wide, u.gpr .x6=BitVec.ofNat 64 c ∧
    residual wide k (i+1)+half wide=k/2^(i+1)+c
  keep : Keeps recClob s u
  mem : u.mem=s.mem.writeW (off base (BITS+i)) (Enc wide k i)

theorem signedStep_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base)
    {k i c : Nat} (hi:i<464) (hc:c≤radix wide)
    (hr:s.gpr .x19=BitVec.ofNat 64 i) (h6:s.gpr .x6=BitVec.ofNat 64 c)
    (hrel:residual wide k i+half wide=k/2^i+c)
    {p : List Instr}
    (hp:WP isa (.block p) s fun u =>
      u.gpr .x4=BitVec.ofNat 64 (k/2^i%radix wide) ∧
      u.gpr .x5=BitVec.ofNat 64 (k/2^i%2) ∧ u.gpr .x2=off base i ∧
      Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem) :
    WP isa (.block (p ++ digitStep wide ++ writeDigit)) s (StepOut base wide k i s) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono hp fun a ⟨a4,a5,a2,ak,am⟩ => ?_
  rw [WP.block_append_iff]
  have hb:k/2^i%radix wide<radix wide := Nat.mod_lt _ (by cases wide <;> decide)
  have he:k/2^i%radix wide%2=k/2^i%2 := by
    cases wide <;> simp only [radix,half,Bool.false_eq_true,↓reduceIte] <;> omega_using []
  have ac:a.gpr .x6=BitVec.ofNat 64 c := (ak.1 _ (by decide)).trans h6
  refine WP.mono (digitStep_ok wide hb hc a4 (by rw [he];exact a5) ac)
    fun b ⟨b7,b6,bk,bm⟩ => ?_
  have kAB:Keeps recClob s b := (ak.mono (by decide)).trans (bk.mono (by decide))
  have bs:Scr b base := hs.of_keeps kAB (by decide)
  have br:b.gpr .x19=BitVec.ofNat 64 i := (bk.1 _ (by decide)).trans ((ak.1 _ (by decide)).trans hr)
  have bp:b.gpr .x2=off base i := (bk.1 _ (by decide)).trans a2
  refine WP.mono (writeDigit_ok bs hi bp br) fun u ⟨ur,uk,um⟩ => ?_
  have kSU:Keeps recClob s u := kAB.trans (uk.mono (by decide))
  refine ⟨hs.of_keeps kSU (by decide),ur,?_,kSU,?_⟩
  · refine ⟨carryNext wide (k/2^i%radix wide) c,WnafWide.carry_bounds wide hc,
      (uk.1 _ (by decide)).trans b6,?_⟩
    have h:=WnafWide.carry_step wide hrel
    change next wide (residual wide k i)+half wide=k/2^(i+1)+_
    rw [Nat.pow_succ,←Nat.div_div_eq_div_mul]
    exact h
  · have hd:=WnafWide.digit_bounds wide (residual wide k i)
    have hd':-127≤digitAt wide k i ∧ digitAt wide k i≤127 := by
      cases wide <;> simp only [half,Bool.false_eq_true,↓reduceIte] at hd <;>
        change -127≤digit _ _ ∧ digit _ _≤127 <;> omega_using [hd]
    have h7:b.gpr .x7=BitVec.ofInt 64 (digitAt wide k i) := by
      rw [b7,WnafWide.local_digit wide hrel]
      rfl
    rw [um,h7,encode_digit hd',bm,am]
    rfl

theorem recodeBody_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base)
    {k i c : Nat} (hi:i<456) (hc:c≤radix wide)
    (hr:s.gpr .x19=BitVec.ofNat 64 i) (h6:s.gpr .x6=BitVec.ofNat 64 c)
    (hrel:residual wide k i+half wide=k/2^i+c)
    (hb:∀ j<8,s.mem (off base (BITS+i+j))=BitVec.ofNat 8 (WnafWide.bit k (i+j))) :
    WP isa (.block (recodeBody wide)) s fun u => StepOut base wide k i s u ∧
      (u.gpr .x9==0)=decide (i+1=456) := by
  have hwidth:2^(width wide)=radix wide := by cases wide <;> rfl
  have hp:=loadBits_ok wide hs hi hr hb
  simp only [WnafWide.look,WnafWide.bit,hwidth] at hp
  have hg:=signedStep_ok wide hs (by omega_using [hi]) hc hr h6 hrel hp
  change WP isa (.block ((loadBits wide ++ digitStep wide ++ writeDigit) ++
    [.subImm .x .x9 .x19 456])) s _
  rw [WP.block_append_iff]
  refine WP.mono hg fun t ht => ?_
  refine WP.mono (counter_ok hi ht.x19) fun u ⟨uz,uk,um⟩ => ?_
  have ku:=uk.mono (show ∀ r∈[Reg.x9],r∈recClob by decide)
  refine ⟨⟨ht.scr.of_keeps uk (by decide),(uk.1 _ (by decide)).trans ht.x19,?_,ht.keep.trans ku,?mem⟩,uz⟩
  case mem => rw [um];exact ht.mem
  obtain ⟨c,hc,h6,hr⟩:=ht.carry
  exact ⟨c,hc,(uk.1 _ (by decide)).trans h6,hr⟩

theorem zeroHead_ok {s : State} {base : Addr} (hs:Scr s base) {i : Nat}
    (hr:s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block [.add .x .x2 .x3 .x19,.movz .x .x4 0 0,.movz .x .x5 0 0]) s fun u =>
      u.gpr .x4=0 ∧ u.gpr .x5=0 ∧ u.gpr .x2=off base i ∧
      Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    RegUpd.gpr_write,BitVec.setWidth_eq,hs.x3,hr,Nat.reduceMul,Nat.reduceLT,
    ite_true,BitVec.shiftLeft_zero,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,by trivial,by trivial,⟨fun r hn => ?_,rfl,rfl⟩,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  simp only [RegUpd.gpr_write,hn.1,hn.2.1,hn.2.2,ite_false]

theorem zeroStep_ok (wide : Bool) {s : State} {base : Addr} (hs:Scr s base)
    {k i c : Nat} (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit) (hi:i<464) (h456:456≤i) (hc:c≤radix wide)
    (hr:s.gpr .x19=BitVec.ofNat 64 i) (h6:s.gpr .x6=BitVec.ofNat 64 c)
    (hrel:residual wide k i+half wide=k/2^i+c) :
    WP isa (.block (zeroStep wide)) s (StepOut base wide k i s) := by
  have hdiv:k/2^i=0 := WnafWide.tail_quotient hk h456
  have hz:=zeroHead_ok hs hr
  have hp:WP isa (.block [.add .x .x2 .x3 .x19,.movz .x .x4 0 0,.movz .x .x5 0 0]) s
      (fun u => u.gpr .x4=BitVec.ofNat 64 (k/2^i%radix wide) ∧
        u.gpr .x5=BitVec.ofNat 64 (k/2^i%2) ∧ u.gpr .x2=off base i ∧
        Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem) := by
    simpa only [hdiv,Nat.zero_mod,show BitVec.ofNat 64 0=(0 : BitVec 64) from rfl] using hz
  exact signedStep_ok wide hs hi hc hr h6 hrel hp

end VG.Proof.Ed448.AArch64.Sparse
