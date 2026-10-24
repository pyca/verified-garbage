module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Framework.Omega

/-! The private scalar and canonical table are outside the writable Montgomery workspace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ReadEnv (p : Parameters) (bs : List Byte) (s : State) : Prop where
 source : Source p.src bs s
 length : bs.length=p.k
 scalarOutside : ∀ i<bs.length, p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i)
 tableRead : ∀ j<32, ∀ i<p.w, InRegions (s.rd++s.wr) (off p.table (8*p.w*j+8*i)) 8
 tableOutside : ∀ j<32, ∀ i<p.w, ∀ b<8, p.Z≤ofs p.B (off p.table (8*p.w*j+8*i)+BitVec.ofNat 64 b)
 table : ∀ j<32, wv s.mem p.table (8*p.w*j) p.w=
  Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent p.N j) p.P*2^(64*p.w)%p.P

theorem ReadEnv.after_inscr {p : Parameters} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ReadEnv p bs s) (frame : InScr p.B p.Z s.mem t.mem) (rest : Keep rs s t) : ReadEnv p bs t := by
 refine ⟨⟨?_,?_,⟩,h.length,h.scalarOutside,?_,h.tableOutside,?_⟩
 · intro i hi;rw [rest.rd,rest.wr];exact h.source.readable i hi
 · intro i hi;rw [frame _ (h.scalarOutside i hi)];exact h.source.bytes i hi
 · intro j hj i hi;rw [rest.rd,rest.wr];exact h.tableRead j hj i hi
 · intro j hj
   have same : wv t.mem p.table (8*p.w*j) p.w=wv s.mem p.table (8*p.w*j) p.w :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => frame _ (h.tableOutside j hj i hi b hb)
   exact same.trans (h.table j hj)

theorem ReadEnv.after_arrays {p : Parameters} {bs : List Byte} {s t : State} {rs : List Reg} {js : List Nat}
 (h : ReadEnv p bs s) (frame : Arrays p.B p.w js s.mem t.mem) (rest : Keep rs s t)
 (within : ∀ j∈js,j<8) : ReadEnv p bs t :=
 h.after_inscr (InScr.of_arrays frame p.room within) rest

theorem ReadEnv.after_header {p : Parameters} {bs : List Byte} {s t : State} {rs : List Reg} {i : Nat}
 (h : ReadEnv p bs s) (frame : Outside p.B (8*i) 8 s.mem t.mem) (rest : Keep rs s t)
 (within : i<32) : ReadEnv p bs t :=
 h.after_inscr (InScr.of_outside frame (by have := hdr_lt_slot p.w 8 within;have := p.room;omega)) rest

end VG.Proof.Ffdh.AArch64.Cached
