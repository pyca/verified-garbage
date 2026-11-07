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

Every implementation takes the destination in `r8` and is proven from a
source to a destination (`xorTo`). Callers call one in place with
`Callee.inPlace` (`mov r8, rsi`, then the call), through `XorImpl.wpIn` and
`XorImpl.relIn` (`wpCallIn`, `relCallIn`, from the proofs called in place
that `okIn_of_okTo` and `ctIn_of_ctTo` give), which take what `WP.call` and
`RelCT.callEx` take with the in-place contract `xorStack`; or from a source
to a destination with `Xor.callTo` (`r8` set to `rsi + r11`), through
`XorImpl.wpTo` and `XorImpl.relTo` (`wpCallTo`, `relCallTo`).

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
  /-- It is correct from a source to a destination, and returns with `rsi`
  pointing at `buf`. -/
  ok : ∀ s, (xorTo stack).pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ (xorTo stack).post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa (xorTo stack).pre (xorTo stack).pub callee.code
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
  /-- Whether it differs from another only in `poly`: the callers that do not
  call `vg_poly1305_blocks` (`vg_chacha20_apply`) are not instantiated for it,
  as they would be that other's. -/
  polyOnly : Bool := false
  /-- Its `fold`, `pass` and `wide` with the implementation of
  `vg_poly1305_blocks` it comes with: one of the combinations whose
  ChaCha20-Poly1305 the constant-time analysis checks (it runs on code with
  the comparisons against `fold`, the mask `pass - 1` and the loops of
  `2 ^ wide` bytes in it). -/
  fold_poly : (callee.fold = 0 ∧ callee.pass = 0 ∧ callee.wide = 4 ∧ poly = .scalar) ∨
    (callee.fold = 448 ∧ callee.pass = 0 ∧ callee.wide = 5 ∧ poly = .avx2) ∨
    (callee.fold = 960 ∧ callee.pass = 1024 ∧ callee.wide = 6 ∧ (poly = .avx512 ∨ poly = .ifma))

namespace XorImpl


/-- The scalar implementation, `vg_chacha20_xor`, in the baseline ISA. -/
def scalar : XorImpl where
  callee := .scalar
  fold_le := by decide
  stack := 8
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := Xor.xor_to
  ct := Xor.xor_ctTo
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

theorem ssse3_ok : ∀ s, (xorTo 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.ssse3.code s t s' ∧
    abiPreserved s s' ∧ (xorTo 16).post s s' :=
  Ssse3.xor_to

theorem ssse3_ct : ConstantTime isa (xorTo 16).pre (xorTo 16).pub Impl.ChaCha20.X86_64.Callee.ssse3.code :=
  Ssse3.xor_ctTo

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

theorem avx2_ok : ∀ s, (xorTo 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx2.code s t s' ∧
    abiPreserved s s' ∧ (xorTo 16).post s s' :=
  Avx2.xor_to

theorem avx2_ct : ConstantTime isa (xorTo 16).pre (xorTo 16).pub Impl.ChaCha20.X86_64.Callee.avx2.code :=
  Avx2.xor_ctTo

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

theorem avx512_ok : ∀ s, (xorTo 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx512.code s t s' ∧
    abiPreserved s s' ∧ (xorTo 16).post s s' :=
  Avx512.xor_to

theorem avx512_ct : ConstantTime isa (xorTo 16).pre (xorTo 16).pub Impl.ChaCha20.X86_64.Callee.avx512.code :=
  Avx512.xor_ctTo

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
  ok := avx512_ok
  ct := avx512_ct
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
  ok := avx512_ok
  ct := avx512_ct
  nosp := avx512_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ifma"
  features := ["avx", "avx512f"]
  poly := .ifma
  polyOnly := true
  fold_poly := Or.inr (Or.inr ⟨rfl, rfl, rfl, .inr rfl⟩)

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
  ok := Avx512VL.xor_to
  ct := Avx512VL.xor_ctTo
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
  exact wpCallIn (okIn_of_okTo v.ok) v.nosp (by omega) hpre hc hw hQ

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
  relCallIn (okIn_of_okTo v.ok) (ctIn_of_ctTo v.ok v.ct) hP

/-- A call of `v` from a source to a destination (`Xor.callTo`, `r8` at
`rsi + r11`): as `WP.call` with `xorTo`, for the state with `r8` set. -/
theorem wpTo (v : XorImpl) {s : State} {rd wr : List Region}
    (hpre : (xorTo v.stack).pre ((toR8 s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (v.callee.code.depth + 1))]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs (Impl.ChaCha20.X86_64.Xor.callTo v.callee.name v.callee.code),
        Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (xorTo v.stack).post ((toR8 s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (Impl.ChaCha20.X86_64.Xor.callTo v.callee.name v.callee.code) s Q := by
  have hd := v.depth_le
  exact wpCallTo v.ok v.nosp (by omega) hpre hc hw hQ

/-- Two runs that call `v` from a source to a destination (`Xor.callTo`)
with `xorTo`'s public arguments agreeing: as `RelCT.callEx`. -/
theorem relTo (v : XorImpl) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      (xorTo v.stack).pre ((toR8 s₁).callEntry.withRegions rd₁ wr₁) ∧
      (xorTo v.stack).pre ((toR8 s₂).callEntry.withRegions rd₂ wr₂) ∧
      (xorTo v.stack).pub ((toR8 s₁).callEntry.withRegions rd₁ wr₁) ((toR8 s₂).callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (Impl.ChaCha20.X86_64.Xor.callTo v.callee.name v.callee.code) fun _ _ => True :=
  relCallTo v.ok v.ct hP

end XorImpl

end VG.Proof.ChaCha20.X86_64
