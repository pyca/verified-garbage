module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Gather

/-! Public comb controls remain fixed while arrays, the row counter and the digit change. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure Controls (B src ctx : Addr) (k N : Nat) (s : State) : Prop where
 context : word s.mem B (8*sCtx)=ctx
 source : word s.mem B (8*sX)=src
 length : word s.mem B (8*sLen)=BitVec.ofNat 64 k
 bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N
 rows : word s.mem B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)

def Counter (B : Addr) (i : Nat) (s : State) : Prop := word s.mem B (8*sI)=BitVec.ofNat 64 i

def TablePointer (B table : Addr) (s : State) : Prop := word s.mem B (8*sTab)=table

theorem arrays_header {B : Addr} {w i : Nat} {m m' : Mem} {js : List Nat}
 (frame : Arrays B w js m m') (hi : i<32) : word m' B (8*i)=word m B (8*i) :=
 frame.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega)

theorem Controls.after_arrays {B src ctx : Addr} {k N w : Nat} {s t : State} {js : List Nat}
 (h : Controls B src ctx k N s) (frame : Arrays B w js s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (arrays_header frame (by decide)).trans h.context
 · exact (arrays_header frame (by decide)).trans h.source
 · exact (arrays_header frame (by decide)).trans h.length
 · exact (arrays_header frame (by decide)).trans h.bits
 · exact (arrays_header frame (by decide)).trans h.rows

theorem Controls.after_counter {B src ctx : Addr} {k N : Nat} {s t : State}
 (h : Controls B src ctx k N s) (frame : Outside B (8*sI) 8 s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.context
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.source
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.length
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.bits
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.rows

theorem Controls.after_digit {B src ctx : Addr} {k N : Nat} {s t : State}
 (h : Controls B src ctx k N s) (frame : Outside B (8*sD) 8 s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.context
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.source
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.length
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.bits
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.rows


theorem Controls.after_table {B src ctx : Addr} {k N : Nat} {s t : State}
 (h : Controls B src ctx k N s) (frame : Outside B (8*sTab) 8 s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.context
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.source
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.length
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.bits
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.rows

end VG.Proof.Ffdh.AArch64.Cached
