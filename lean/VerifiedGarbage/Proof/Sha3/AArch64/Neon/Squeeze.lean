module

public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64 (Upd Mupd wp_str)

structure OutKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem OutKeep.refl (s : State) : OutKeep s s := ⟨fun _ _ _ => rfl,rfl,rfl,rfl,rfl⟩
theorem OutKeep.trans {s t u : State} (h : OutKeep s t) (k : OutKeep t u) : OutKeep s u :=
  ⟨fun r h6 h7 => (k.gpr r h6 h7).trans (h.gpr r h6 h7), k.vec.trans h.vec,
    k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem OutKeep.upd {s t : State} {r : Reg} {v : BitVec 64}
    (h : Upd s t r v) (hr : r = .x6 ∨ r = .x7) : OutKeep s t :=
  ⟨fun q h6 h7 => h.other q (by rcases hr with h | h <;> subst r <;> with_reducible assumption),h.vec,h.rd,h.wr,h.sp⟩
theorem OutKeep.mem {s t : State} {m : Mem} (h : Mupd s t m) : OutKeep s t :=
  ⟨fun _ _ _ => congrFun h.gpr _,h.vec,h.rd,h.wr,h.sp⟩

def outAddr (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (8*i)
def outR (p : Addr) : Region := ⟨p,168⟩
def RateAt (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 21, m.readW (outAddr p i) 64 = A[i]!

theorem squeeze_step {s : State} {a b : Addr} {ra rb : Reg} {i : Nat} (hi : i < 21)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hwa : InRegions s.wr (outAddr a i) 8) (hwb : InRegions s.wr (outAddr b i) 8) :
    WP isa (.block ([.umov .x .x6 (vreg i) 0,.umov .x .x7 (vreg i) 1,
      .str .x .x6 ra (8*i),.str .x .x7 rb (8*i)] : List Instr)) s fun t =>
      OutKeep s t ∧ t.mem = (s.mem.writeW (outAddr a i) (vdword (s.v (vreg i)) 0)).writeW
        (outAddr b i) (vdword (s.v (vreg i)) 1) := by
  refine WP.cons (s' := s.write .x .x6 (vdword (s.v (vreg i)) 0)) (by rfl) ?_
  have h1 := Upd.write64 s .x6 (vdword (s.v (vreg i)) 0)
  let s1 := s.write .x .x6 (vdword (s.v (vreg i)) 0)
  refine WP.cons (s' := s1.write .x .x7 (vdword (s1.v (vreg i)) 1)) (by rfl) ?_
  have h2 := Upd.write64 s1 .x7 (vdword (s1.v (vreg i)) 1)
  refine wp_str ⟨by omega,by omega⟩
    (by rw [h2.other ra ha7,h1.other ra ha6,ha])
    (by rw [h2.wr,h1.wr]; exact hwa) fun s3 h3 => ?_
  refine wp_str ⟨by omega,by omega⟩
    (by rw [h3.gpr,h2.other rb hb7,h1.other rb hb6,hb])
    (by rw [h3.wr,h2.wr,h1.wr]; exact hwb) fun s4 h4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((OutKeep.upd h1 (Or.inl rfl)).trans (OutKeep.upd h2 (Or.inr rfl))).trans
      ((OutKeep.mem h3).trans (OutKeep.mem h4))
  · rw [h4.mem,h3.mem,h3.gpr,h2.gpr,h2.other .x6 (by decide),h1.gpr,h2.mem,h1.mem,h1.vec]
    rfl

/-- Word-wise output is the SHA-3 specification's byte serialization. -/
theorem RateAt.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : RateAt m p A)
    {j : Nat} (hj : j < 168) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega] at he
  exact he
end VG.Proof.Sha3.AArch64.Neon
