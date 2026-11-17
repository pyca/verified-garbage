module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Bignum.Arm.CombDigitLoad`, which this module and modules that import it used -/

section

/-! Big-endian exponent bytes are read at public, bounded bit positions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev loadClobbers : List Reg := [.r2,.r11,.r12]

structure Source (src : BitVec 32) (bs : List Byte) (s : State) : Prop where
  fits : src.toNat + bs.length ≤ 2^32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) bs.length
  bytes : ∀ j (hj : j < bs.length), s.mem (State.addr src + BitVec.ofNat 64 j) = bs[j]'hj

theorem load_ok (s : State) {src : BitVec 32} {bs : List Byte} {k : Nat}
    (source : Source src bs s) (bound : k < 8*bs.length) (size : bs.length < 2^32)
    (ptr : s.gpr .r4 = src) (length : s.gpr .r5 = BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9 = BitVec.ofNat 32 k) (indexFit : k < 2^32) :
    WP isa (.block VG.Impl.Bignum.Arm.CombDigit.load) s fun t =>
      t.gpr .r11 = (bs[bs.length-1-k/8]'(by omega_using [bound])).setWidth 32 ∧
      t.gpr .r2 = BitVec.ofNat 32 (k%8) ∧ t.z = decide (k%8=0) ∧
      t.mem = s.mem ∧ Rest loadClobbers s t := by
  have quotient : BitVec.ofNat 32 k >>> 3 = BitVec.ofNat 32 (k/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexFit]
    rw [Nat.shiftRight_eq_div_pow]
    change k/8 = k/8%2^32
    rw [Nat.mod_eq_of_lt (by omega_using [indexFit])]
  have rem : BitVec.ofNat 32 k &&& 7 = BitVec.ofNat 32 (k%8) := by
    change BitVec.ofNat 32 k &&& BitVec.ofNat 32 (2^3-1) = _
    rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]
  have offset : (BitVec.ofNat 32 bs.length - BitVec.ofNat 32 (k/8)) - 1 =
      BitVec.ofNat 32 (bs.length-1-k/8) := by
    rw [BitVec.ofNat_sub_ofNat_of_le bs.length (k/8) (by omega_using [indexFit]) (by omega_using [bound])]
    change BitVec.ofNat 32 (bs.length-k/8) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (bs.length-k/8) 1 (by decide) (by omega_using [bound])]
    congr 1
    omega_using []
  unfold VG.Impl.Bignum.Arm.CombDigit.load
  refine wp_mov (by rfl) fun a one => ?_
  refine wp_dp (op2_reg _ _) fun b two => ?_
  refine wp_dp (op2_imm (by decide)) fun c three => ?_
  refine wp_dp (op2_reg _ _) fun d four => ?_
  have kept : Rest loadClobbers s d :=
    (((one.rest (by decide)).trans (two.rest (by decide))).trans
      (three.rest (by decide))).trans (four.rest (by decide))
  have address : d.gpr .r12 = src + BitVec.ofNat 32 (bs.length-1-k/8) := by
    rw [four.gpr,three.gpr,two.gpr,one.gpr]
    change c.gpr .r4 + (a.gpr .r5 - (s.gpr .r9 >>> 3) - 1) = _
    rw [three.other .r4 (by decide),two.other .r4 (by decide),one.other .r4 (by decide),
      one.other .r5 (by decide),ptr,length,index,quotient,offset]
  have addr : State.addr (d.gpr .r12 + BitVec.ofNat 32 0) =
      State.addr src + BitVec.ofNat 64 (bs.length-1-k/8) := by
    rw [address,BitVec.add_zero]
    exact VG.Arm.addr_add (by have := source.fits; omega_using [this])
  have read : InRegions (d.rd ++ d.wr) (State.addr src + BitVec.ofNat 64 (bs.length-1-k/8)) 1 := by
    rw [kept.rd,kept.wr]
    exact VG.CallLay.inRegions_sub source.readable (by omega_using [bound]) (by have := source.fits; omega_using [size])
  refine wp_ldrb (by decide) addr read fun e five => ?_
  refine wp_dp (op2_imm (by decide)) fun f six => ?_
  refine wp_cmp (op2_imm (by decide)) fun t seven zero => WP.block_nil ?_
  have count : f.gpr .r2 = BitVec.ofNat 32 (k%8) := by
    rw [six.gpr]
    change e.gpr .r9 &&& 7 = _
    rw [five.other .r9 (by decide),kept.gpr .r9 (by decide),index,rem]
  refine ⟨?_,(congrArg (fun f => f .r2) seven.gpr).trans count,?_,?_,?_⟩
  · rw [seven.gpr,six.other .r11 (by decide),five.gpr]
    rw [four.mem,three.mem,two.mem,one.mem,source.bytes _ (by omega_using [bound])]
  · rw [zero,count]
    change (BitVec.ofNat 32 (k%8) - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero,ofNat_beq_zero (by omega_using [])]
  · exact seven.mem.trans (six.mem.trans (five.mem.trans (four.mem.trans (three.mem.trans (two.mem.trans one.mem)))))
  · exact ((kept.trans (five.rest (by decide))).trans
      (six.rest (by decide))).trans (seven.rest _)

end VG.Proof.Bignum.Arm.CombDigit

end

end

/-! ### `Bignum.Arm.CombExpShared`, which only this module used -/

section

/-! Read-only context and exponent facts persist through the shared arithmetic calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def withInvariant {base : BitVec 32} {len w : Nat} {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (Q : State→Prop)
    (stableQ : ∀ {s t : State}, Frame regions s.mem t.mem → Rest roundClobbers s t → Q s → Q t) :
    TwoExp.Montgomery base len w (fun s=>P s ∧ Q s) regions where
  op := A.op
  workspace := A.workspace
  stable := by
    intro s t frame rest h
    exact ⟨A.stable frame rest h.1,stableQ (frame.mono (by simpa using A.workspace)) rest h.2⟩
  op_ok := by
    intro s o a b ready h ho ha hb ho0 operand
    refine WP.mono (A.op_ok s o a b ready h.1 ho ha hb ho0 operand) ?_
    rintro t ⟨readyT,modulus,bound,value,keeps,pt,frame,rest⟩
    exact ⟨readyT,modulus,bound,value,keeps,⟨pt,stableQ frame rest h.2⟩,frame,rest⟩

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! Every callable RSA Montgomery backend supports the same immutable comb context. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpReadOnly.lean`, which only this module imported.
section

/-! The immutable exponent and table lie outside every arithmetic write region. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure ReadOnly (source table : BitVec 32) (w M g N : Nat) (bs : List Byte)
    (regions : List Region) (s : State) : Prop where
  exponent : CombDigit.Source source bs s
  entries : CombTable table w M g N s
  sourceSeparate : ∀ r∈regions, (⟨State.addr source,bs.length⟩:Region).Disjoint r
  tableSeparate : ∀ r∈regions, (⟨State.addr table,32*(8*w)⟩:Region).Disjoint r

theorem ReadOnly.after_frame {source table : BitVec 32} {w M g N : Nat} {bs : List Byte}
    {regions : List Region} {s t : State} {rs : List Reg}
    (h : ReadOnly source table w M g N bs regions s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t) :
    ReadOnly source table w M g N bs regions t := by
  have entryFits (digit : Nat) (hd : digit<32) (j : Nat) (hj : j<2*w) :
      8*w*digit+4*j+4≤32*(8*w) := by
    have last := Nat.mul_le_mul_left (8*w) (show digit+1≤32 by omega_using [hd])
    have limb := Nat.mul_le_mul_left 4 (show j+1≤2*w by omega_using [hj])
    rw [Nat.mul_add,Nat.mul_one] at last
    omega_using [hj, last]
  refine ⟨⟨h.exponent.fits,?_,?_⟩,⟨h.entries.positive,h.entries.fits,?_,?_⟩,
    h.sourceSeparate,h.tableSeparate⟩
  · rw [rest.rd,rest.wr]; exact h.exponent.readable
  · intro j hj
    exact (frame.bytes h.sourceSeparate (by change bs.length≤2^64; have := h.exponent.fits; omega_using [this]) hj).trans (h.exponent.bytes j hj)
  · rw [rest.rd,rest.wr]; exact h.entries.readable
  · intro digit hd
    rw [←h.entries.values digit hd]
    apply val32_congr
    intro j hj
    apply congrArg BitVec.toNat
    apply frame.readW (r:=⟨State.addr table,32*(8*w)⟩) _ h.tableSeparate (by decide)
    exact Offset.contains_base _ (entryFits digit hd j hj) (by
      have := entryFits digit hd j hj
      have := h.entries.fits
      omega_arith)

end VG.Proof.Bignum.Arm.CombExp
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Arm.FrameStack

def writeRegions (base sp : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr base,8*len⟩,belowA sp 48]

abbrev Persistent (base source table sp : BitVec 32) (len w M g N : Nat) (bs : List Byte) (s : State) : Prop :=
  TwoExp.CallReady base sp len s ∧ ReadOnly source table w M g N bs (writeRegions base sp len) s

def arithmetic (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) :
    TwoExp.Montgomery base len w (Persistent base source table sp len w M g N bs)
      (writeRegions base sp len) :=
  withInvariant (TwoExp.sharedMontgomery base sp len w backend.name backend.mul
    (fun _ _ _ ho ha hb s h=>backend.correct s h ho ha hb) backend.stackOk)
    (ReadOnly source table w M g N bs (writeRegions base sp len))
    (by intro s t frame rest h; exact h.after_frame frame rest)

end VG.Proof.Bignum.Arm.CombExp
