import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.X86_64.Target

/-!
# GHASH with PCLMULQDQ: what the instruction groups compute, as bits

Untrusted: everything here is checked by Lean. The 256-bit carry-less product
(`Prod`), its reduction (`reduce`), and what each group of instructions of
`Impl.Gcm.X86_64.Pclmul` does to the state, each proved by one symbolic
execution for any registers it is used with. What they compute in the field
is in `Pclmul/Ghash.lean` (`Prod.val`, `φ_reduce`), which needs the algebra
of `Proof/Gcm/Poly.lean`; this module does not, so that proofs about where
the products go import it alone.
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly xInv)

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

def xor (p q : Prod) : Prod := ⟨p.lo ^^^ q.lo, p.mid ^^^ q.mid, p.hi ^^^ q.hi⟩

/-- The four products of `acc`, added to `p`. -/
def acc (p : Prod) (a b : BitVec 128) : Prod :=
  ⟨p.lo ^^^ pclmul a b 0x00,
   p.mid ^^^ pclmul a b 0x01 ^^^ pclmul a b 0x10,
   p.hi ^^^ pclmul a b 0x11⟩

def zero : Prod := ⟨0, 0, 0⟩

end Prod

/-- One step of the reduction: `swap(v) ⊕ clmul(v₀, c)`. -/
def fold (v : BitVec 128) : BitVec 128 := shufDwords v 0x4e ^^^ pclmul v poly 0x10

/-- The block `reduce` computes from a product. -/
def reduce (p : Prod) : BitVec 128 :=
  (p.hi ^^^ p.mid >>> 64) ^^^ fold (fold (p.lo ^^^ p.mid <<< 64))

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem psrldq8 (v : BitVec 128) : XShiftOp.eval .psrldq v 8 = v >>> 64 := rfl

theorem pslldq8 (v : BitVec 128) : XShiftOp.eval .pslldq v 8 = v <<< 64 := rfl

theorem rev_eq : Impl.Gcm.X86_64.Pclmul.revMask = revMask := rfl

/-- `s'` differs from `s` at most in `rax` and the SSE registers `rs`. -/
structure Only (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem Only.trans {rs rs' : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs' s' s'') :
    Only (rs ++ rs') s s'' :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Only.weaken {rs rs' : List XReg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Only rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- The product registers. -/
def prod (s : State) : Prod := ⟨s.xmm .xmm8, s.xmm .xmm9, s.xmm .xmm10⟩

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Pclmul.zero) s fun s' =>
      prod s' = Prod.zero ∧ Only [.xmm8, .xmm9, .xmm10] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.zero]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_pxor, BitVec.xor_self, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (a b : XReg) (s : State) (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10)
    (ha11 : a ≠ .xmm11) (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc a b)) s fun s' =>
      prod s' = (prod s).acc (s.xmm a) (s.xmm b) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.acc]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_pxor, eval_movdqa, ha8, ha9, ha10, ha11, hb8, hb9,
    hb10, hb11, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [prod, Prod.acc, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (d : XReg) (s : State) (hd8 : d ≠ .xmm8) (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10)
    (hd11 : d ≠ .xmm11) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.reduce d)) s fun s' =>
      s'.xmm d = reduce (prod s) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11, d] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.reduce, Impl.Gcm.X86_64.Pclmul.fold, List.cons_append,
    List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_pxor, eval_movdqa, hd8, hd9, hd10, hd11, h1,
    Ne.symm hd8,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [psrldq8, pslldq8]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- A block, loaded from `[b + d]` into `x` and byte-reversed. -/
theorem ldrev_ok (x : XReg) (b : Reg) (d : Nat) (s : State) (hx : x ≠ .xmm0)
    (h0 : s.xmm .xmm0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad x (at_ b d), .xop (.bin .pshufb x .xmm0)]) s fun s' =>
      s'.xmm x = Spec.Gcm.blockAt s.mem (s.gpr b + BitVec.ofInt 64 (d : Int)) ∧ Only [x] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, ea_at, hin, Ne.symm hx, h0,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

/-- A 128-bit constant into `x`. -/
theorem const_ok (x : XReg) (c : BitVec 128) (s : State) (hx : x ≠ .xmm12) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.const x c)) s fun s' =>
      s'.xmm x = c ∧ Only [x, .xmm12] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.const]
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.setReg, hx, movq_const, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, fun r hr => by simp only [hr, ↓reduceIte], rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

/-- `pxor xmm7, xmm2`. -/
theorem pxor72_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm7 .xmm2)]) s fun s' =>
      s'.xmm .xmm7 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ Only [.xmm7] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_pxor, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [BitVec.xor_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

theorem Only.prod {rs : List XReg} {s s' : State} (h : Only rs s s') (h8 : .xmm8 ∉ rs)
    (h9 : .xmm9 ∉ rs) (h10 : .xmm10 ∉ rs) : prod s' = prod s := by
  simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, h.xmm _ h8, h.xmm _ h9, h.xmm _ h10]

/-! ## Addresses -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `rcx − k`, for `rcx` counting blocks down. -/
theorem ofNat_sub_ofNat {n k : Nat} (hk : k ≤ n) (_hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := Offset.ofNat_sub_ofNat hk

end VG.Proof.Gcm.X86_64.Pclmul
