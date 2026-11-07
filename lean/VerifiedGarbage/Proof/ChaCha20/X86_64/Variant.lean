module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512VL
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Callee
public import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Implementations of `vg_chacha20_xor` on x86-64

An `XorImpl` is what a function that calls `vg_chacha20_xor` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `ChaCha20Xor` on x86-64 (`Variants/ChaCha20Xor/X86_64/`), and each
caller (in `Generic/ChaCha20Xor/X86_64/`) is emitted once for each of them
(see `TCB/Emit.lean`). Callers leave room for 16 bytes of stack below its
return address (`stack_le`), and for two levels of calls (`depth_le`), which
take at most those 16 bytes (`xdepth`).

Every implementation takes the destination in `r8` (`xorTo`); each is proven
called in place (`xorIn`: `r8` is `rsi`): the baseline, SSSE3 and AVX2 ones
from their proofs from a source to a destination (`okIn_of_okTo`,
`ctIn_of_ctTo`), the AVX-512 one, which still works in place, from its
in-place proof (`okIn_of_stack`), and the AVX-512VL one, which runs the AVX2
kernel (from a source to a destination) or the AVX-512 kernel (in place),
called in place (`Avx512VL.xor_in`). Callers call one in place with
`Callee.inPlace` (`mov r8, rsi`, then the call), through `XorImpl.wpIn` and
`XorImpl.relIn` (`wpCallIn`, `relCallIn`), which take what `WP.call` and
`RelCT.callEx` take with the in-place contract `xorStack`.

An implementation also names the implementation of `vg_poly1305_blocks` for
the same CPUs (`poly`), which ChaCha20-Poly1305's instance for it calls: so
each instance needs the CPU features of both.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64

open VG.X86_64

/-- An implementation of `vg_chacha20_xor` on x86-64. -/
structure XorImpl where
  /-- Its symbol and code. -/
  callee : Impl.ChaCha20.X86_64.Callee
  /-- ChaCha20-Poly1305 keeps the keystream for `64 + fold` bytes in its
  working space. -/
  fold_le : callee.fold ≤ 960
  /-- The stack its calls use below its return address. -/
  stack : Nat
  stack_le : stack ≤ 16
  depth_le : callee.code.depth ≤ 2
  /-- Its calls take at most 16 bytes of stack below its return address. -/
  xdepth : callee.code.x86_64Depth ≤ 16
  /-- It is correct called in place, and returns with `rsi` pointing at `buf`. -/
  ok : ∀ s, (xorIn stack).pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ (xorIn stack).post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa (xorIn stack).pre (xorIn stack).pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_poly1305_blocks` that callers of this one
  which also call `vg_poly1305_blocks` (ChaCha20-Poly1305) call: the one
  for the same CPUs. -/
  poly : Impl.Poly1305.X86_64.Blocks
  /-- Its `fold`, `pass` and `wide` with the implementation of
  `vg_poly1305_blocks` it comes with: one of the combinations whose
  ChaCha20-Poly1305 the constant-time analysis checks (it runs on code with
  the comparisons against `fold`, the mask `pass - 1` and the loops of
  `2 ^ wide` bytes in it). -/
  fold_poly : (callee.fold = 0 ∧ callee.pass = 0 ∧ callee.wide = 4 ∧ poly = .scalar) ∨
    (callee.fold = 448 ∧ callee.pass = 0 ∧ callee.wide = 5 ∧ poly = .avx2) ∨
    (callee.fold = 960 ∧ callee.pass = 1024 ∧ callee.wide = 6 ∧ (poly = .avx512 ∨ poly = .ifma))

/-- An implementation proven in place, with `r8` unused, called in place. -/
theorem okIn_of_stack {c : Prog isa} {k : Nat}
    (hv : ∀ s, (xorStack k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorStack k).post s s') :
    ∀ s, (xorIn k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xorIn k).post s s' :=
  fun s hs => hv s hs.1

theorem ctIn_of_stack {c : Prog isa} {k : Nat} (h : ConstantTime isa (xorStack k).pre (xorStack k).pub c) :
    ConstantTime isa (xorIn k).pre (xorIn k).pub c :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => h _ _ _ _ _ _ h₁.1 h₂.1 hp e₁ e₂

namespace XorImpl


/-- The scalar implementation, `vg_chacha20_xor`, in the baseline ISA. -/
def scalar : XorImpl where
  callee := .scalar
  fold_le := by decide
  stack := 8
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := Xor.xor_in
  ct := Xor.xor_ct
  nosp := Avx2.xor_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  poly := .scalar
  fold_poly := Or.inl ⟨rfl, rfl, rfl, rfl⟩

theorem ssse3_nosp : NoSp Impl.ChaCha20.X86_64.Callee.ssse3.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.ssse3.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem ssse3_ok : ∀ s, (xorIn 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.ssse3.code s t s' ∧
    abiPreserved s s' ∧ (xorIn 16).post s s' :=
  okIn_of_okTo Ssse3.xor_to

theorem ssse3_ct : ConstantTime isa (xorIn 16).pre (xorIn 16).pub Impl.ChaCha20.X86_64.Callee.ssse3.code :=
  ctIn_of_ctTo Ssse3.xor_to Ssse3.xor_ctTo

/-- The SSSE3 implementation, `vg_chacha20_xor_ssse3`, for CPUs without
AVX2: its callers that also call `vg_poly1305_blocks` call the baseline
`vg_poly1305_blocks`, as the baseline implementation's do. -/
def ssse3 : XorImpl where
  callee := .ssse3
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := ssse3_ok
  ct := ssse3_ct
  nosp := ssse3_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ssse3"
  features := ["ssse3"]
  poly := .scalar
  fold_poly := Or.inl ⟨rfl, rfl, rfl, rfl⟩

theorem avx2_ok : ∀ s, (xorIn 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx2.code s t s' ∧
    abiPreserved s s' ∧ (xorIn 16).post s s' :=
  okIn_of_okTo Avx2.xor_to

theorem avx2_ct : ConstantTime isa (xorIn 16).pre (xorIn 16).pub Impl.ChaCha20.X86_64.Callee.avx2.code :=
  ctIn_of_ctTo Avx2.xor_to Avx2.xor_ctTo

theorem avx2_nosp : NoSp Impl.ChaCha20.X86_64.Callee.avx2.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.avx2.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The AVX2 implementation, `vg_chacha20_xor_avx2`. -/
def avx2 : XorImpl where
  callee := .avx2
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := avx2_ok
  ct := avx2_ct
  nosp := avx2_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2"]
  poly := .avx2
  fold_poly := Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)

theorem avx512_ok : ∀ s, (xorStack 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx512.code s t s' ∧
    abiPreserved s s' ∧ (xorStack 16).post s s' :=
  fun s hs => Avx512.xor_rsi s hs

theorem avx512_ct : ConstantTime isa (xorStack 16).pre (xorStack 16).pub Impl.ChaCha20.X86_64.Callee.avx512.code :=
  Avx512.xor_ct

theorem avx512_nosp : NoSp Impl.ChaCha20.X86_64.Callee.avx512.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.avx512.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The AVX-512 implementation, `vg_chacha20_xor_avx512`. -/
def avx512 : XorImpl where
  callee := .avx512
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := okIn_of_stack avx512_ok
  ct := ctIn_of_stack avx512_ct
  nosp := avx512_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx512"
  features := ["avx", "avx512f"]
  poly := .avx512
  fold_poly := Or.inr (Or.inr ⟨rfl, rfl, rfl, .inl rfl⟩)

/-- `vg_chacha20_xor_avx512`, for CPUs with AVX-512 IFMA too: its callers
that also call `vg_poly1305_blocks` (ChaCha20-Poly1305) call
`vg_poly1305_blocks_ifma`. -/
def ifma : XorImpl where
  callee := .avx512
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := okIn_of_stack avx512_ok
  ct := ctIn_of_stack avx512_ct
  nosp := avx512_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ifma"
  features := ["avx", "avx512f"]
  poly := .ifma
  fold_poly := Or.inr (Or.inr ⟨rfl, rfl, rfl, .inr rfl⟩)

theorem avx512vl_ok : ∀ s, (xorIn 16).pre s →
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx512vl.code s t s' ∧ abiPreserved s s' ∧ (xorIn 16).post s s' :=
  Avx512VL.xor_in

theorem avx512vl_ct :
    ConstantTime isa (xorIn 16).pre (xorIn 16).pub Impl.ChaCha20.X86_64.Callee.avx512vl.code :=
  Avx512VL.xor_ct

theorem avx512vl_nosp : NoSp Impl.ChaCha20.X86_64.Callee.avx512vl.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.avx512vl.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_chacha20_xor_avx512vl`: the AVX-512 implementation with fewer than 513
bytes in `ymm` registers, for CPUs with AVX-512 but not IFMA, whose clock a
512-bit instruction lowers: its callers that also call `vg_poly1305_blocks`
call `vg_poly1305_blocks_avx512`. -/
def avx512vl : XorImpl where
  callee := .avx512vl
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := avx512vl_ok
  ct := avx512vl_ct
  nosp := avx512vl_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx512vl"
  features := ["avx", "avx2", "avx512f", "avx512vl"]
  poly := .avx512
  fold_poly := Or.inr (Or.inr ⟨rfl, rfl, rfl, .inl rfl⟩)

/-- `v` called as the AVX2 instances call `vg_chacha20_xor_avx2`, with
`vg_poly1305_blocks_avx2`. -/
def asAvx2 (v : XorImpl) : XorImpl where
  callee := { v.callee with fold := 448, pass := 0, wide := 5 }
  fold_le := show 448 ≤ 960 by decide
  stack := v.stack
  stack_le := v.stack_le
  depth_le := v.depth_le
  xdepth := v.xdepth
  ok := v.ok
  ct := v.ct
  nosp := v.nosp
  mxcsr := v.mxcsr
  spSafe := v.spSafe
  suffix := v.suffix
  features := v.features
  poly := .avx2
  fold_poly := Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)

/-- The implementation `v`'s ChaCha20-Poly1305 calls from its AVX2 code for
short data (`Callee.small`). -/
def small (v : XorImpl) : XorImpl := if v.callee.vl then v.asAvx2 else .avx2

theorem small_poly (v : XorImpl) : v.small.poly = .avx2 := by
  by_cases h : v.callee.vl = true
  · simp only [small, h, ite_true]; rfl
  · simp only [small, h, ite_false, Bool.false_eq_true]; rfl

theorem small_callee (v : XorImpl) : v.small.callee = v.callee.small := by
  by_cases h : v.callee.vl = true
  · simp only [small, Impl.ChaCha20.X86_64.Callee.small, h, ite_true, asAvx2]
  · simp only [small, Impl.ChaCha20.X86_64.Callee.small, h, ite_false, Bool.false_eq_true]; rfl

end XorImpl

/-! ## Calling an implementation in place

A caller calls an implementation in place with `Callee.inPlace`: `r8` (the
destination) set to `rsi` (the source), then the call. `wpIn` and `relIn`
take what `WP.call` and `RelCT.callEx` take for the call of the code with the
in-place contract `xorStack` (`wpCallIn`, `relCallIn`). -/

namespace XorImpl

/-- A call of `v` in place (`Callee.inPlace`): as `WP.call` with the in-place
contract `xorStack`. -/
theorem wpIn (v : XorImpl) {s : State} {rd wr : List Region}
    (hpre : (xorStack v.stack).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (v.callee.code.depth + 1))]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs v.callee.inPlace, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (xorStack v.stack).post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa v.callee.inPlace s Q := by
  have hd := v.depth_le
  exact wpCallIn v.ok v.nosp (by omega) hpre hc hw hQ

/-- Two runs that call `v` in place (`Callee.inPlace`) with the in-place
contract's public arguments agreeing: as `RelCT.callEx`. -/
theorem relIn (v : XorImpl) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      (xorStack v.stack).pre (s₁.callEntry.withRegions rd₁ wr₁) ∧
      (xorStack v.stack).pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      (xorStack v.stack).pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P v.callee.inPlace fun _ _ => True :=
  relCallIn v.ok v.ct hP

end XorImpl

end VG.Proof.ChaCha20.X86_64
