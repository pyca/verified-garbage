module

import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkLoop
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Hmac
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Gpr
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Contract
public import VerifiedGarbage.Impl.Mgf1.X86_64.Table
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.HmacTable.X86_64
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-! ### `Ecdsa.Rfc6979.X86_64.Curve`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86-64: the curve

What the proof needs of the curve (`RfcCurve`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.X86_64.Cfg`),
the instance of ECDSA it is, its sizes: scalars of `Q` bytes in 4, 5, 6 or 8 words
(32, 48 or 64 bytes, or P-192's 24 and P-224's 28 in 4) whose order `n` has
exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that `bits2octets` is one
conditional subtraction), or, if `big`, P-521's (9 words, 66 bytes, 521
bits: longer than any digest); the bits `sh` the signature drops from its
digest; the facts of its blocks (`RfcT`); and what is proven of the code:
that it meets the contract the proof of each curve is written against
(`coreK`: each curve's `signX86_64` at its sizes), in constant time, and the
facts of every instruction the proof of the whole function needs. Each
curve's file builds one, so that the heavy algebra of its proof stays out
of the modules generic over the curve and the hash function.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.X86_64.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, with the
comb's tables (`E.combConsts`, if any) at their statics, as each curve's
proof states it (`Proof.Ecdsa.X86_64.signX86_64` for P-256). -/
def coreK (E : Impl.Ecdsa.X86_64.Cfg) : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 2 * E.C.len⟩
    let d : Region := ⟨s.gpr .rsi, E.C.len⟩
    let digest : Region := ⟨s.gpr .rdx, E.C.len⟩
    let k : Region := ⟨s.gpr .rcx, E.C.len⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ++ Abi.constRegions (fun n => s.syms n) E.combConsts ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 2 * E.C.len ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧
      TblsOk E.combConsts s [out, scratch, ret]
  post s s' :=
    match coreSigOf E s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) (2 * E.C.len) = encode E.C rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) (2 * E.C.len) =
        List.replicate (2 * E.C.len) 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    ∀ c ∈ E.combConsts, s₁.syms c.1 = s₂.syms c.1

/-- The code's blocks for scalars of `E` (with `h = X` and `core`'s digest
shifted if `big`, by `sh` bits), without the functions it calls. -/
def cfgC (E : Impl.Ecdsa.X86_64.Cfg) (big : Bool) (sh : Nat) : Impl.Ecdsa.Rfc6979.X86_64.Cfg where
  f := ⟨[], [], []⟩
  w := E.n
  len := E.C.len
  big := big
  sh := sh
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- None of the instructions of the block `is` writes `rsp` or loads MXCSR. -/
abbrev OkB (is : List Instr) : Prop :=
  (Code.block is : Prog isa).allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true

open Impl.Ecdsa.Rfc6979.X86_64 in
/-- The blocks whose contents depend on the curve: each addresses memory
only from the registers that hold the frame's base and the pointers the code
put there (the taint analysis), and none of their instructions writes `rsp`
or loads MXCSR. -/
structure RfcT (c : Impl.Ecdsa.Rfc6979.X86_64.Cfg) : Prop where
  xArgs : TaintOk [.rsp] c.xArgs
  reduce : c.big = false → TaintOk [.rsp] c.reduce
  msgF : TaintOk [.rsp, .rdi, .rsi] (c.msg 0 true)
  msgN : TaintOk [.rsp, .rdi, .rsi] (c.msg 0 false)
  updM : TaintOk [.rsp] (Cfg.updMArgs (1 + 2 * c.len))
  finM : TaintOk [.rsp] (Cfg.finArgs (1 + 2 * c.len) fK)
  tStep : TaintOk [.rsp] c.tStep
  coreArgs : TaintOk [.rsp] c.coreArgs
  xcArgs : c.big = true → TaintOk [.rsp] c.xcArgs
  convC : c.big = true → TaintOk [.rsp, .rdi] (c.conv fXc (8 - c.sh))
  convT : c.big = true → TaintOk [.rsp, .rdi] (c.conv fT c.sh)
  iXArgs : OkB c.xArgs
  iReduce : OkB c.reduce
  iMsgF₀ : OkB (c.msg 0 true)
  iMsgF₁ : OkB (c.msg 1 true)
  iMsgN : OkB (c.msg 0 false)
  iUpdM : OkB (Cfg.updMArgs (1 + 2 * c.len))
  iFinM : OkB (Cfg.finArgs (1 + 2 * c.len) fK)
  iTStep : OkB c.tStep
  iCandTop : OkB c.candTop
  iCoreArgs : OkB c.coreArgs
  iXcArgs : OkB c.xcArgs
  iConvC : OkB (Cfg.scrPtr ++ c.conv fXc (8 - c.sh))

/-- `RfcT` of a curve's blocks, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { xArgs := ⟨_, by taint_decide⟩, reduce := by exact (Function.const _ ⟨_, by taint_decide⟩),
    msgF := ⟨_, by taint_decide⟩, msgN := ⟨_, by taint_decide⟩, updM := ⟨_, by taint_decide⟩,
    finM := ⟨_, by taint_decide⟩, tStep := ⟨_, by taint_decide⟩, coreArgs := ⟨_, by taint_decide⟩,
    xcArgs := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convC := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convT := by exact (Function.const _ ⟨_, by taint_decide⟩),
    iXArgs := by decide +kernel, iReduce := by decide +kernel, iMsgF₀ := by decide +kernel,
    iMsgF₁ := by decide +kernel, iMsgN := by decide +kernel, iUpdM := by decide +kernel,
    iFinM := by decide +kernel, iTStep := by decide +kernel, iCandTop := by decide +kernel,
    iCoreArgs := by decide +kernel, iXcArgs := by decide +kernel, iConvC := by decide +kernel })

/-- A curve, for RFC 6979 on x86-64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.X86_64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output and
  `n` has fewer bits than they do (P-521's), so that `h` is the digest's
  integer and `core` takes it shifted (`Impl.Ecdsa.Rfc6979.X86_64.Cfg.big`). -/
  big : Bool
  /-- Scalars of 4, 5, 6 or 8 words, `8 n` bytes (or 24 or 28 in 4 words), and `n` of
  exactly `8 len` bits, with `2^(8 len) < 2 n`; or, if `big`, of 9 words and
  66 bytes, and `n` of 521 bits. -/
  sizes : if big then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6 ∨ E.n = 8 ∨ E.n = 5) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ (E.C.len = 28 ∨ E.C.len = 24)) ∧
      nBits E.C = 8 * E.C.len ∧ 2 ^ (8 * E.C.len) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : E.sh = sh
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct (with the 8
  bytes below `rsp` apart from its buffers, for the return addresses of its
  own calls) and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → Clear (hole (s.gpr .rsp)) s →
    ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- Its instructions: none writes `rsp` (or loads MXCSR), and the functions
  it calls call nothing. -/
  coreNs : coreC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  coreSp : coreC.allInstrs (fun i => !isa.writesSp i) = true
  coreMx : coreC.allInstrs (fun i => !loadsMxcsr i) = true
  coreD : coreC.depth ≤ 1
  /-- The taint checks and instruction facts of the curve's blocks. -/
  blk : RfcT (cfgC E big sh)

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.big = false) :
    (R.E.n = 4 ∨ R.E.n = 6 ∨ R.E.n = 8 ∨ R.E.n = 5) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ (R.E.C.len = 28 ∨ R.E.C.len = 24)) ∧
      nBits R.E.C = 8 * R.E.C.len ∧ 2 ^ (8 * R.E.C.len) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.big = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n4 : 4 ≤ R.E.n := by
  cases h : R.big
  · rcases (R.sizesA h).1 with h | h | h | h <;> omega_using [h]
  · rw [(R.sizesW h).1]; omega_using []

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.big
  · rcases (R.sizesA h).1 with h | h | h | h <;> omega_using [h]
  · rw [(R.sizesW h).1]

/-- The scalars' bytes fill their words, the last possibly zero. -/
theorem len_words : 8 ≤ R.E.C.len ∧ 8 * R.E.n ≤ R.E.C.len + 8 ∧ R.E.C.len ≤ 8 * R.E.n := by
  cases h : R.big
  · have := R.sizesA h; have := R.n4; omega_arith
  · have := R.sizesW h; omega_using [this]

/-- `nBits` is within the scalars' last byte, and `sh` the bits beyond it. -/
theorem nBits_len : 8 * R.E.C.len < nBits R.E.C + 8 ∧ nBits R.E.C ≤ 8 * R.E.C.len ∧
    R.sh = 8 * R.E.C.len - nBits R.E.C := by
  rw [← R.sh_eq]
  cases h : R.big
  · have := R.sizesA h; exact ⟨by omega_using [this], by omega_using [this], rfl⟩
  · have := R.sizesW h; exact ⟨by omega_using [this], by omega_using [this], rfl⟩

theorem n_ne : R.E.C.n ≠ 0 := fun h => by
  have h₁ := R.nBits_len; have h₂ := R.len_words
  have : nBits R.E.C = 1 := by show R.E.C.n.log2 + 1 = 1; rw [h]; rfl
  omega_using [h₁, h₂, this]

end RfcCurve

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

section

/-! ### `Ecdsa.Rfc6979.X86_64.Layout`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86-64: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`) and the `240 + 8 e` bytes of stack below its return address, from
`B` up (`Lay dn`): the 24 bytes the calls use (a call's return address, and
the 16 bytes HMAC's functions use below theirs), then the frame of `27 + e`
words, from `B + 24`: `K` and `V` (64 bytes each), `h` (48 bytes, of which
`q` are used), the number of candidates left, the pointers to `scratch`,
`digest`, `d` and `out`, and `e` more words (`HIGH`, 18 if two `V`s make a
candidate: the digest for `core` and the candidate). `Ctx` is what holds
between the frame's push and pop: the permissions, `rsp`, the callee-saved
registers, the pointers in the frame, that memory changed only in `out`,
`scratch` and the stack, and where the tables of constants `core` reads are
(`TBLs`, the comb's). Code that writes only regions apart from the
pointers (`Safe`) keeps it (`Ctx.keep`). The contract gives 8 more bytes of
stack, below `B`, which nothing writes: HMAC's `init` for a key of any
length, which the table holds, takes the 24 bytes below its return address
to be apart from its buffers (`Lay.Ok.x8`, `Lay.Ok.low32_SCR`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.HmacTable.X86_64 (TabOK TabMem)

/-- The buffers and the lowest byte of the stack used (`rsp - (240 + 8 e)` on
entry), for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  /-- The table of HMAC. -/
  tab : Addr
  B : Addr
  q : Nat
  /-- The words above the frame's pointers. -/
  e : Nat
  he : e = 48
  /-- The tables of constants `core` reads, and their statics' addresses. -/
  cs : List (String × List (BitVec 64))
  sy : String → Addr
  /-- The hash function's code, whose HMAC functions the table holds, and
  the functions an indirect call of a table's functions may reach. -/
  H : Hash
  f : Fns
  /-- The addresses of `H`'s HMAC functions, public. -/
  fa : String → Addr

namespace Lay

variable {dn : Nat} (L : Lay dn)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨L.tab, 48⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 248 + 8 * L.e⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 24, 224 + 8 * L.e⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 (248 + 8 * L.e), 8⟩
/-- The frame's slot of the table's address, its top word. -/
abbrev TS : Region := ⟨L.B + BitVec.ofNat 64 (240 + 8 * L.e), 8⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `h` and the count. -/
abbrev LOW : Region := ⟨L.B, 208⟩
/-- The frame above its pointers and the slots of `D` and `B`. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 256, 8 * L.e - 16⟩
/-- The tables of constants. -/
abbrev TBLs : List Region := Abi.constRegions L.sy L.cs

/-- What the contract says of where the buffers and the stack are (`d` and
`digest`, which are only read, may overlap). -/
structure Ok : Prop where
  od : L.OUT.Disjoint L.D
  og : L.OUT.Disjoint L.DG
  oc : L.OUT.Disjoint L.SCR
  dc : L.D.Disjoint L.SCR
  gc : L.DG.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  kd : L.STK.Disjoint L.D
  kg : L.STK.Disjoint L.DG
  kc : L.STK.Disjoint L.SCR
  ro : L.RET.Disjoint L.OUT
  rd : L.RET.Disjoint L.D
  rg : L.RET.Disjoint L.DG
  rc : L.RET.Disjoint L.SCR
  no : L.out.toNat + 2 * L.q ≤ 2 ^ 64
  nd : L.d.toNat + L.q ≤ 2 ^ 64
  ng : L.dg.toNat + dn ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  /-- The table does not wrap around, and is apart from what the code writes. -/
  nt : L.tab.toNat + 48 ≤ 2 ^ 64
  to : L.TAB.Disjoint L.OUT
  tc : L.TAB.Disjoint L.SCR
  tk : L.TAB.Disjoint L.STK
  /-- The stack used does not wrap around. -/
  nb : L.B.toNat + (248 + 8 * L.e) ≤ 2 ^ 64
  /-- The tables do not wrap around, and are apart from what the code writes. -/
  tbl : ∀ T ∈ L.TBLs, T.base.toNat + T.len ≤ 2 ^ 64 ∧ T.Disjoint L.OUT ∧ T.Disjoint L.SCR ∧ T.Disjoint L.STK
  /-- The 8 bytes below the stack used are apart from `scratch`: HMAC's
  `init` for a key of any length, which the table holds, takes the 24 bytes
  below its return address to be apart from its buffers, though it writes
  only 16 (`Proof.Pbkdf2.Md.X86_64.Any.AnyArgs`). -/
  x8 : Region.Disjoint ⟨L.B - BitVec.ofNat 64 8, 8⟩ L.SCR

end Lay

theorem constRegions_congr {f f' : String → Addr} {cs : List (String × List (BitVec 64))}
    (h : ∀ c ∈ cs, f c.1 = f' c.1) : Abi.constRegions f cs = Abi.constRegions f' cs :=
  List.map_congr_left fun c hc => by rw [h c hc]

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n x : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 248 + x) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 24, 224 + x⟩ :=
  ⟨d - 24, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below or above the frame's pointers. -/
def Safe {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 208) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem Safe.of_sub {dn : Nat} {L : Lay dn} {r r' : Region} (hs : Safe L r') (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

theorem safe_high {dn : Nat} (L : Lay dn) {d n : Nat} (h₁ : 256 ≤ d) (h₂ : d + n ≤ 240 + 8 * L.e) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ (by have := L.he; omega_arith))))

theorem safe_scr {dn : Nat} (L : Lay dn) {d n : Nat} (h : d + n ≤ 8192) : Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {L : Lay dn}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

/-- The 32 bytes below the frame's calls' area (`x8`, then the 24 of the
calls) are apart from `scratch`. -/
theorem low32_SCR (h : L.Ok) : Region.Disjoint ⟨L.B - BitVec.ofNat 64 8, 32⟩ L.SCR := by
  intro a ha hs
  by_cases hlt : (a - (L.B - BitVec.ofNat 64 8)).toNat < 8
  · exact h.x8 a (show (a - (L.B - BitVec.ofNat 64 8)).toNat + 1 ≤ 8 by omega_using [hlt]) hs
  · have e : a - L.B = a - (L.B - BitVec.ofNat 64 8) - BitVec.ofNat 64 8 := by
      rw [BitVec.sub_sub, BitVec.sub_add_cancel]
    have hle : BitVec.ofNat 64 8 ≤ a - (L.B - BitVec.ofNat 64 8) := by
      rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hlt]
    refine h.stk_SCR (d := 0) (n := 24) (by have := L.he; omega_using [this]) a ?_ hs
    show (a - (L.B + BitVec.ofNat 64 0)).toNat + 1 ≤ 24
    have ha' : (a - (L.B - BitVec.ofNat 64 8)).toNat + 1 ≤ 32 := ha
    rw [BitVec.add_zero, e, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
    omega_using [ha', hlt]

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_D (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.D := h.kd.sub_left (Offset.sub_base _ h₁)

theorem stk_d (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 248 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.d, L.q⟩ := h.stk_D h₁

/-- The frame's pointers are apart from every safe region. -/
theorem ptrs_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 208, 32⟩ r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by omega_arith)).sub_right hs
  · exact (h.stk_SCR (by omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The frame's slots of `D` and `B` are apart from every safe region. -/
theorem db_safe (h : L.Ok) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 240, 16⟩ r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT (by have := L.he; omega_arith)).sub_right hs
  · exact (h.stk_SCR (by have := L.he; omega_arith)).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

/-- The frame's slot of the table's address is apart from every safe region. -/
theorem ts_safe (h : L.Ok) {r : Region} (hs : Safe L r) : L.TS.Disjoint r := by
  rcases hs with hs | hs | hs | hs
  · exact (h.ko.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hs
  · exact (h.kc.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hs
  · exact (Offset.disjoint_base _ (by omega_arith) (by have := L.he; omega_arith)).sub_right hs
  · have := L.he
    exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

end Lay.Ok

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB] ++ L.TBLs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.out
  pTab : t.mem.readW (L.B + BitVec.ofNat 64 (240 + 8 * L.e)) 64 = L.tab
  /-- `D` and `B`, above the pointers. -/
  pDl : t.mem.readW (L.B + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 L.H.D
  pBl : t.mem.readW (L.B + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 L.H.P.B
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : ∀ c ∈ L.cs, t.syms c.1 = L.sy c.1
  held : Abi.constsHeld m₀ L.sy L.cs
  tabOk : TabOK L.H L.f t.syms
  tabMem : TabMem L.H t.syms L.tab m₀
  fsy : ∀ n ∈ [L.H.hmacInitAnyN, L.H.updN, L.H.hmacFinN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {L : Lay dn} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 256) (n := 8 * L.e - 16)
      (by have := L.he; omega_arith) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `rsp` and the callee-saved registers,
and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' := by
  have keep : ∀ d, 208 ≤ d → d + 8 ≤ 240 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 208, 32⟩)
      (Offset.contains _ h₁ (by omega_arith) (by omega_arith)) (fun r hr => hL.ptrs_safe (hs r hr)) (by decide)
  have keepDB : ∀ d, 240 ≤ d → d + 8 ≤ 256 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 240, 16⟩)
      (Offset.contains _ h₁ (by omega_arith) (by have := hL.nb; have := L.he; omega_arith))
      (fun r hr => hL.db_safe (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.rsp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 208 (by omega_arith) (by omega_arith)).trans hc.pScr, (keep 216 (by omega_arith) (by omega_arith)).trans hc.pDg,
    (keep 224 (by omega_arith) (by omega_arith)).trans hc.pD, (keep 232 (by omega_arith) (by omega_arith)).trans hc.pOut,
    (hf.readW (r := L.TS) (Offset.contains _ (Nat.le_refl _) (by have := L.he; omega_arith) (by have := hL.nb; have := L.he; omega_arith))
      (fun r hr => hL.ts_safe (hs r hr)) (by decide)).trans hc.pTab,
    (keepDB 240 (by omega_arith) (by omega_arith)).trans hc.pDl, (keepDB 248 (by omega_arith) (by omega_arith)).trans hc.pBl,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), by rw [hsy]; exact hc.sy, hc.held,
    by rw [hsy]; exact hc.tabOk, by rw [hsy]; exact hc.tabMem, by rw [hsy]; exact hc.fsy⟩

/-- Code that writes only caller-saved registers. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  hc.keep hL hrd hwr (hg .rsp (by decide)) (fun r hr _ => hg r hr) (ws := []) (by rw [hm]; exact Frame.refl _ _)
    (by simp) hsy

/-- A byte of `d`, as on entry. -/
theorem d_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.q) :
    t.mem (L.d + BitVec.ofNat 64 i) = m₀ (L.d + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.D) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.od.symm
    · exact hL.dc
    · exact hL.kd.symm) (by show L.q ≤ 2 ^ 64; have := hL.nd; omega_arith) hi

/-- A byte of `digest`, as on entry. -/
theorem dg_byte (hL : L.Ok) (hc : Ctx L g m₀ t) {i : Nat} (hi : i < dn) :
    t.mem (L.dg + BitVec.ofNat 64 i) = m₀ (L.dg + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.DG) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.og.symm
    · exact hL.gc
    · exact hL.kg.symm) (by show dn ≤ 2 ^ 64; have := hL.ng; omega_arith) hi

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 248 + 8 * L.e) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  have := L.he
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 248 + 8 * L.e) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  have := L.he
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩

theorem inScr (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inScrW (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ 8192) :
    InRegions t.wr (L.scr + BitVec.ofNat 64 o) n :=
  ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inTab (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (h : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (L.tab + BitVec.ofNat 64 o) 8 :=
  ⟨L.TAB, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by have := hL.nt; omega_arith)⟩

theorem inD (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ L.q) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.d + BitVec.ofNat 64 o) n :=
  ⟨L.D, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem inDg (hc : Ctx L g m₀ t) {o n : Nat} (h : o + n ≤ dn) (ho : o ≤ 64) :
    InRegions (t.rd ++ t.wr) (L.dg + BitVec.ofNat 64 o) n :=
  ⟨L.DG, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega_arith)⟩

/-- Regions within the buffers and the frame are permitted. -/
theorem mem_regions {R : Region} (h : R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR]) :
    R ∈ [L.D, L.DG, L.TAB] ++ L.TBLs ++ [L.FR, L.OUT, L.SCR] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact mem_regions hR, hw⟩

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    exact ⟨R, by rw [hc.wr]; exact hR, hw⟩

end Ctx

/-! ## The frame's push -/

/-- The registers the frame's push stores, with `e` words above the pointers:
the table's address, copies of `rax`, then `B` (`r11`) and `D` (`r10`) just
above the pointers. -/
abbrev pushRs (e : Nat) : List Reg :=
  .r9 :: ((List.replicate (e - 2) .rax ++ ([.r11, .r10] : List Reg)) ++ ([.rdi, .rsi, .rdx, .rcx] : List Reg) ++
    List.replicate 23 .rax)

theorem pushRs_length {e : Nat} (he : 2 ≤ e) : (pushRs e).length = 28 + e := by
  simp only [pushRs, List.length_cons, List.length_append, List.length_replicate, List.length_nil]; omega_arith

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, `e` words above the pointers, the tables `cs` (the statics' addresses,
public, of those tables only), and the hash function `H`'s HMAC through the
table, whose functions an indirect call reaches among `f`'s. -/
def lay (dn q e : Nat) (he : e = 48) (cs : List (String × List (BitVec 64))) (H : Hash) (f : Fns)
    (s : State) : Lay dn :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r9, s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * e), q, e,
    he, cs, fun n => if n ∈ cs.map Prod.fst then s.syms n else 0, H, f,
    fun n => if n ∈ [H.hmacInitAnyN, H.updN, H.hmacFinN] then s.syms n else 0⟩

/-- What the contract says of the table at `r9`, after the entry: it holds
`H`'s HMAC functions, which an indirect call of `f`'s reaches, and `r10` and
`r11` hold its digest length and HMAC's block size. -/
def tabFacts (H : Hash) (f : Fns) (s : State) : Prop :=
  TabOK H f s.syms ∧ TabMem H s.syms (s.gpr .r9) s.mem ∧ s.gpr .r10 = BitVec.ofNat 64 H.D ∧
    s.gpr .r11 = BitVec.ofNat 64 H.P.B

theorem lay_ret (dn q e : Nat) (he : e = 48) (cs : List (String × List (BitVec 64))) (H : Hash) (f : Fns)
    (s : State) :
    (lay dn q e he cs H f s).B + BitVec.ofNat 64 (248 + 8 * e) = s.gpr .rsp :=
  BitVec.sub_add_cancel _ _

theorem lay_sy (dn q e : Nat) (he : e = 48) {cs : List (String × List (BitVec 64))} {H : Hash} {f : Fns}
    (s : State) :
    ∀ c ∈ cs, (lay dn q e he cs H f s).sy c.1 = s.syms c.1 := fun c hc => by
  simp only [lay, List.mem_map_of_mem (f := Prod.fst) hc, ite_true]

theorem lay_tbls (dn q e : Nat) (he : e = 48) (cs : List (String × List (BitVec 64))) {H : Hash} {f : Fns}
    (s : State) :
    (lay dn q e he cs H f s).TBLs = Abi.constRegions (fun n => s.syms n) cs :=
  constRegions_congr (lay_sy dn q e he (H := H) (f := f) s)

theorem lay_ok {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {e : Nat}
    (he : e = 48) {H : Hash} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86_64 cs I (256 + 8 * e) (tabFacts H f) ns).pre s) :
    (lay I.hashLen I.ecdsa.curve.len e he cs H f s).Ok := by
  obtain ⟨hsp, -, -, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, ht, nt, tout, tsc, -,
    tstk, -⟩ := h
  have e' : (lay I.hashLen I.ecdsa.curve.len e he cs H f s).RET = ⟨s.gpr .rsp, 8⟩ := by
    show (⟨_ + BitVec.ofNat 64 (248 + 8 * e), 8⟩ : Region) = _; rw [lay_ret]
  -- The stack the frame uses, and the 8 bytes below it, within the stack the contract gives.
  have hS : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * e), 248 + 8 * e⟩
      ⟨s.gpr .rsp - BitVec.ofNat 64 (256 + 8 * e), 256 + 8 * e⟩ :=
    Offset.sub_below _ (by omega_arith) (by omega_arith)
  have h8 : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * e) - BitVec.ofNat 64 8, 8⟩
      ⟨s.gpr .rsp - BitVec.ofNat 64 (256 + 8 * e), 256 + 8 * e⟩ := by
    rw [Offset.sub_sub_ofNat, show 248 + 8 * e + 8 = 256 + 8 * e by omega_arith]
    exact Region.sub_prefix (by omega_arith)
  refine ⟨od, og, oc, dc, gc, ko.sub_left hS, kd.sub_left hS, kg.sub_left hS, kc.sub_left hS, e' ▸ ro, e' ▸ rd,
    e' ▸ rg, e' ▸ rc, no, nd, ng, nc, nt, tout, tsc, tstk.sub_right hS, ?_, ?_, kc.sub_left h8⟩
  · show (s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * e)).toNat + (248 + 8 * e) ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]
    have := (s.gpr .rsp).isLt
    omega_arith
  · intro T hT
    rw [lay_tbls] at hT
    obtain ⟨hn, hd⟩ := ht.2 T hT
    exact ⟨hn, hd _ (List.mem_cons_self ..), hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      (hd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_singleton_self _))))).sub_right hS⟩

theorem push_base (sp : Addr) (e : Nat) :
    sp - BitVec.ofNat 64 (8 * (28 + e)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 24 := by
  rw [show 8 * (28 + e) = 248 + 8 * e - 24 by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith), Offset.sub_sub_eq]

theorem push_slot (sp : Addr) (e j : Nat) (hj : j < 4) :
    sp - BitVec.ofNat 64 (8 * (1 + e + j + 1)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 (232 - 8 * j) := by
  rw [show 8 * (1 + e + j + 1) = 248 + 8 * e - (232 - 8 * j) by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith),
    Offset.sub_sub_eq]

theorem push_top (sp : Addr) (e : Nat) :
    sp - BitVec.ofNat 64 (8 * (0 + 1)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 (240 + 8 * e) := by
  rw [show 8 * (0 + 1) = 248 + 8 * e - (240 + 8 * e) by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith),
    Offset.sub_sub_eq]

/-- The places of `D` and `B`, the `j`th word just above the pointers. -/
theorem push_db (sp : Addr) (e j : Nat) (hj : j < 2) (he : 2 ≤ e) :
    sp - BitVec.ofNat 64 (8 * (e - j + 1)) = sp - BitVec.ofNat 64 (248 + 8 * e) + BitVec.ofNat 64 (240 + 8 * j) := by
  rw [show 8 * (e - j + 1) = 248 + 8 * e - (240 + 8 * j) by omega_arith, ← Offset.ofNat_sub_ofNat (by omega_arith),
    Offset.sub_sub_eq]

theorem push_ctx {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {e : Nat}
    (he : e = 48) {H : Hash} {f : Fns} {ns : List String} {s : State}
    (h : (rfcX86_64 cs I (256 + 8 * e) (tabFacts H f) ns).pre s) :
    Ctx (lay I.hashLen I.ecdsa.curve.len e he cs H f s) s.gpr s.mem (pushed (pushRs e) s) := by
  have he2 : 2 ≤ e := by omega_arith
  have hn : 8 * (pushRs e).length ≤ (s.gpr .rsp).toNat := by rw [pushRs_length he2]; have := h.1; omega_arith
  obtain ⟨hf, hw⟩ := pushRegs_mem s (pushRs e) (by simp [pushRs]) hn
  have hw' : ∀ j (hj : j < 4), (pushed (pushRs e) s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len e he cs H f s).B + BitVec.ofNat 64 (232 - 8 * j)) 64 =
        s.gpr ([Reg.rdi, .rsi, .rdx, .rcx][j]'hj) :=
    fun j hj => by
      have hj' : 1 + e + j < (pushRs e).length := by rw [pushRs_length he2]; omega_arith
      have hr : (pushRs e)[1 + e + j]'hj' = [Reg.rdi, .rsi, .rdx, .rcx][j]'hj := by
        simp only [pushRs, List.append_assoc, show 1 + e + j = (e + j) + 1 by omega_arith, List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp <;> omega_arith)]
        simp only [List.length_replicate]
        rw [List.getElem_append_right (by simp <;> omega_arith)]
        simp only [List.length_cons, List.length_nil]
        rw [List.getElem_append_left (by simp <;> omega_arith)]
        congr 1; omega_arith
      rw [← hr, ← hw (1 + e + j) hj']; simp only [lay]; rw [push_slot _ e j hj]; rfl
  have hdb : ∀ j (hj : j < 2), (pushed (pushRs e) s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len e he cs H f s).B + BitVec.ofNat 64 (240 + 8 * j)) 64 =
        s.gpr ([Reg.r10, .r11][j]'hj) :=
    fun j hj => by
      have hj' : e - j < (pushRs e).length := by rw [pushRs_length he2]; omega_arith
      have hr : (pushRs e)[e - j]'hj' = [Reg.r10, .r11][j]'hj := by
        simp only [pushRs, List.append_assoc, show e - j = (e - 1 - j) + 1 by omega_arith, List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp <;> omega_arith)]
        simp only [List.length_replicate]
        rw [List.getElem_append_left (by simp <;> omega_arith)]
        rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
        · simp only [show e - 1 - 0 - (e - 2) = 1 by omega_arith]; rfl
        · simp only [show e - 1 - 1 - (e - 2) = 0 by omega_arith]; rfl
      rw [← hr, ← hw (e - j) hj']; simp only [lay]; rw [push_db _ e j hj he2]; rfl
  have hwt : (pushed (pushRs e) s).mem.readW
      ((lay I.hashLen I.ecdsa.curve.len e he cs H f s).B + BitVec.ofNat 64 (240 + 8 * e)) 64 = s.gpr .r9 := by
    have := hw 0 (by rw [pushRs_length he2]; omega_arith)
    simp only [pushRs, List.getElem_cons_zero] at this
    rw [← this]; simp only [lay]; rw [push_top _ e]; rfl
  have ht := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htf : tabFacts H f s := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨by rw [pushed_rd, h.2.1, lay_tbls]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    hw' 3 (by omega_arith), hw' 2 (by omega_arith), hw' 1 (by omega_arith), hw' 0 (by omega_arith), hwt,
    (hdb 0 (by omega_arith)).trans htf.2.2.1, (hdb 1 (by omega_arith)).trans htf.2.2.2, ?_,
    fun c hc => (congrFun (pushRegs_syms s _) c.1).trans
      (lay_sy I.hashLen I.ecdsa.curve.len e he (cs := cs) (H := H) (f := f) s c hc).symm,
    fun c hc i hi => ?_, ?_, ?_, ?_⟩
  · rw [pushed_wr, h.2.2.1, pushRs_length he2, push_base, show 8 * (28 + e) = 224 + 8 * e by omega_arith]; rfl
  · rw [pushed_rsp, pushRs_length he2, push_base]; rfl
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay I.hashLen I.ecdsa.curve.len e he cs H f s).STK, by simp, ?_⟩
    rw [pushRs_length he2, push_base]
    exact Offset.sub_base (n := 8 * (28 + e)) (k := 248 + 8 * e) _ (by omega_arith)
  · rw [lay_sy I.hashLen I.ecdsa.curve.len e he (cs := cs) (H := H) (f := f) s c hc]
    exact ht.1 c hc i hi
  · show TabOK H f (pushRegs s (pushRs e)).syms
    rw [pushRegs_syms]; exact htf.1
  · show TabMem H (pushRegs s (pushRs e)).syms (s.gpr .r9) s.mem
    rw [pushRegs_syms]; exact htf.2.1
  · intro n hn
    show (pushRegs s (pushRs e)).syms n = (if n ∈ [H.hmacInitAnyN, H.updN, H.hmacFinN] then s.syms n else 0)
    have hn' : n ∈ [H.hmacInitAnyN, H.updN, H.hmacFinN] := hn
    rw [pushRegs_syms, ite_eq_left_of_eq_true _ _ (eq_true hn')]

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-!
# Deterministic ECDSA on x86-64: addresses and registers

The effective addresses of the code's memory operands, the immediates it
sign- or zero-extends, the stack below `rsp` the calls use, and the bytes of
a region a frame of writes misses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem ea_at (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_using [h]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The 24 bytes below the frame, which the calls use. -/
theorem below24 (B : Addr) : below (B + BitVec.ofNat 64 24) 24 = ⟨B, 24⟩ := by
  show (⟨B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24, 24⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-- Callee-saved registers, through writes of others. -/
macro "cs_tac" : tactic => `(tactic| plain_simp_names (
                   intro r hr
                   revert hr
                   simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
                   rintro (h | h | h | h | h | h | h) <;> subst h <;>
                     simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, reduceCtorEq, ite_false]))

/-- A fact `simp` has reduced to `True`, or an equation of definitionally equal sides. -/
macro "triv" : tactic => `(tactic| first | trivial | rfl)

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

/-- The bytes of a region a frame of writes misses. -/
theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem _root_.VG.Region.Sub.trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `p + d` does not wrap. -/
theorem toNat_add_of {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The stack below `rsp` a call nested `n / 8 - 1` deep uses, within the 24 bytes below the frame. -/
theorem Ctx.below_sub {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {u : State} (hc : Ctx L g m₀ u) {n : Nat}
    (hn : n ≤ 24) : Region.Sub (below (u.gpr .rsp) n) ⟨L.B, 24⟩ := by
  rw [hc.rsp, ← below24]; exact VG.X86_64.below_sub hn (by omega_using [])

theorem Lay.Ok.low_scr {dn : Nat} {L : Lay dn} (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 24⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Offset.sub_base _ h₂)

/-- Code that writes no callee-saved register keeps them (`hc` is checked
by evaluating the code). -/
theorem WP.keepCs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he⟩
  have h₁ := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using h₁

/-- Code that keeps the permissions and the callee-saved registers, and
writes only safe regions, keeps `Ctx`. -/
theorem Ctx.of_keep {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {is : List Instr} {ws : List Region} {Q : State → Prop}
    (h : WP isa (.block is) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ Frame ws t.mem t'.mem ∧ Q t')
    (hk : (instrs (.block is : Prog isa)).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true)
    (hs : ∀ r ∈ ws, Safe L r) :
    WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Frame ws t.mem t'.mem ∧ Q t' :=
  WP.mono_syms (WP.keepCs h hk) fun _ ⟨⟨hrd, hwr, hf, hq⟩, hcs⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf hs hsy, hf, hq⟩

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the caller-saved register `d` (and the flags)
changed, to `v`. -/
structure Upd {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 64)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hsy : u'.syms = u.syms)
    (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) : Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm hsy fun r hr => hk r (ne_cs hr hd)

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {a : Nat}
    (ha : a < 2 ^ 31) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.scr + BitVec.ofNat 64 a)) := by
  have h192 := hc.inFr (d := 208) (by omega_using []) (by omega_using [])
  have hrsp : d ≠ .rsp := fun h => hd (h ▸ by decide)
  apply WP.of_runBlock
  simp only [Cfg.scr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h192, ite_true, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg_self, hc.pScr, sx32 ha, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d ← rsp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o < 2 ^ 31) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.B + BitVec.ofNat 64 (24 + o))) := by
  apply WP.of_runBlock
  simp only [Cfg.fr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self, hc.rsp, sx32 ho, Offset.add_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d ← n`, zero-extended from 32 bits. -/
theorem mov32_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {n : Nat}
    (hn : n < 2 ^ 32) :
    WP isa (.block [.mov32 d (.imm (BitVec.ofNat 32 n))]) u (Upd L g m₀ u d (BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, zx32 hn, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-! ### `Ecdsa.Rfc6979.X86_64.Hash`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86-64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`):
the curve (`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`,
which each candidate calls), the instance of the contract it implements (the
curve's, the hash function's HMAC, its output length, the bound on
candidates), its code and what the proofs of HMAC's functions know of it
(`Hash`, `HashOK`, `CoreOK`, `Callees`: HMAC's `init` and `finalize` and the
streaming `update`, which the table holds), the functions an indirect call
of a table's functions may reach (`f`, of which the table's are, `TabOK`, a
fact of the state), and the sizes the frame and `scratch` hold: the output
and block sizes of one of the hash functions of `shapes` (MD5's, SHA-1's or
the SHA-2 family's), and states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the frame holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK CoreOK Callees core hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin
  core_hmacInit_depth core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- The digest lengths and block sizes of the hash functions with HMAC on
x86-64: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on x86-64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.X86_64.Hash
  ok : HashOK H
  C : CoreOK (core H)
  K : Callees H
  satI : ∃ s, (Proof.Hmac.initScratchContract ok.SH H.W X86_64.abi 16).pre s
  satF : ∃ s, (Proof.Hmac.finalizeScratchContract ok.SH H.W X86_64.abi 16).pre s
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 32-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (H.D, H.P.B) ∈ shapes
  hS : H.S ≤ 192
  hW : 8 * H.W ≤ 1872
  hWb : ok.stream.Wb ≤ 1872
  /-- HMAC's `init` for a key of any length (`initAny`), which the tables
hold, with `W + S` words of working space, which `scratch` holds. -/
  A : Verified X86_64.target H.hmacInitAny (Proof.Pbkdf2.Md.X86_64.Any.anyG ok.SH (H.W + H.S))
  Asp : NoSp H.hmacInitAny
  Ad : H.hmacInitAny.depth ≤ 2
  hWA : 8 * (H.W + H.S) ≤ 3104

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

theorem hI : Verified X86_64.target P.H.hmacInit (initG P.ok.SH P.H.W) := hmacInit_ok P.ok P.C P.K P.satI

theorem hIsp : NoSp P.H.hmacInit := nosp_of (core_hmacInit P.K.iNs P.K.b.bNs P.C.hinitNs)

theorem hId : P.H.hmacInit.depth ≤ 2 := core_hmacInit_depth P.K.iD P.K.b.bD P.C.hinitD

theorem hF : Verified X86_64.target P.H.hmacFin (finG P.ok.SH P.H.W) := hmacFin_ok P.ok P.C P.K P.satF

theorem hFsp : NoSp P.H.hmacFin := nosp_of (core_hmacFin P.K.cNs P.C.hfinNs)

theorem hFd : P.H.hmacFin.depth ≤ 2 := core_hmacFin_depth P.K.cD P.C.hfinD

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

theorem shape (h : (P.H.D, P.H.P.B) ∈ shapes) :
    16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧ P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega_using [h, h']

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ 8 * P.H.W ≤ 1872 ∧ P.ok.stream.Wb ≤ 1872 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B ∧ 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧
    P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hs := P.shape P.hDB
  have hQ : P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb; simp only [Q]; omega_using [this]
    · have := P.R.sizesW hb; simp only [Q]; omega_using [this]
  refine ⟨P.hS, P.hS, P.hW, P.hWb, P.hS, rfl, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2,
    P.R.n4, hn9, hw.1, hQ, hw.2.2, hw.2.1⟩

/-- Unless `big`, the scalars are `8 w` bytes (or 24 or 28 in 4 words), at most 8 words. -/
theorem sizesA (h : P.R.big = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, w] <;> omega_using [this]

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.Q = 66 ∧ P.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := P.sizes.2.2.2.2.2.2.2.1
  exact ⟨h₁.1, h₁.2.1, by simp only [Q]; omega_using [h₁, h₂]⟩

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, for the curve of `P` and the functions an indirect call may reach. -/
def cfgOf (P : RfcHash) : Cfg where
  f := P.f
  w := P.R.E.n
  len := P.R.E.C.len
  big := P.R.big
  sh := P.R.sh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-!
# Deterministic ECDSA on x86-64: `h = bits2octets(digest)`

`X`'s `Q` bytes (in the frame at `xa`: the digest's leftmost bytes, or the
digest after zero bytes, `Prep.lean`), a word at a time from the least
significant (a top word of four bytes, if `Q = 8 w - 4`, by a 32-bit load:
`loadWord_ok`): each to `V`'s place, and it minus the word of `n` (with the
borrow of the words before) to `K`'s (`subs_ok`); then, by the mask of the
last borrow, the number's words or the difference's, big-endian to the `Q`
bytes at `h` (`sels_ok`, at `hB`), the top word's zero bytes below them.
The number is below `2^(8 Q) < 2n`, so this is it modulo `n` (`mod_mathK`,
`reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.X25519.X86_64 (sub_borrow sbb_borrow)
open VG.Proof.Mont (word wordsVal wordsVal_lt wordsVal_succ_top Outside off ofs writeW_outside)

theorem sel_mask (x d : BitVec 64) (y : BitVec 64) (c : Bool) :
    ((x ^^^ d) &&& (y - y - (BitVec.ofBool c).setWidth 64)) ^^^ d = if c then x else d := by
  cases c
  · simp
  · have : y - y - (BitVec.ofBool true).setWidth 64 = BitVec.allOnes 64 := by simp
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp

/-- The low `k + 1` words of `n`: its low `k`, and word `k`. -/
theorem n_split (n k : Nat) :
    n % 2 ^ (64 * (k + 1)) = n % 2 ^ (64 * k) + 2 ^ (64 * k) * (BitVec.ofNat 64 (n >>> (64 * k))).toNat := by
  rw [show 64 * (k + 1) = 64 * k + 64 by omega_using [], Nat.pow_add, Nat.mod_mul, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  obtain h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  obtain h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_using [h₁, h₂])

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- Where `X` is, in the frame: `rsp + fX`. -/
abbrev xa {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (24 + fX)

/-- Where `h` is, from the stack's lowest byte: `rsp + fH`. -/
abbrev hB : Nat := 24 + fH


/-- Word `j` of the number at `X`, least significant first: a top word of
four bytes is zero-extended. -/
def xw (P : RfcHash) (L : Lay dn) (m : Mem) (j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ P.Q then bswap64 (m.readW (xa L + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
  else if P.Q ≤ 8 * j then 0
  else (bswap32 (m.readW (xa L) 32)).setWidth 64

theorem cat8_shr (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) >>> 32 =
      (b0 ++ b1 ++ b2 ++ b3 : BitVec 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  obtain h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  obtain h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp only [← Nat.shiftLeft_add_eq_or_of_lt h1, ← Nat.shiftLeft_add_eq_or_of_lt h2,
    ← Nat.shiftLeft_add_eq_or_of_lt h3, ← Nat.shiftLeft_add_eq_or_of_lt h4, ← Nat.shiftLeft_add_eq_or_of_lt h5,
    ← Nat.shiftLeft_add_eq_or_of_lt h6, ← Nat.shiftLeft_add_eq_or_of_lt h7]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_using []

/-- The first four bytes at `a`, big-endian: the eight bytes', shifted right. -/
theorem bswap32_readW (m : Mem) (a : Addr) :
    (bswap32 (m.readW a 32)).setWidth 64 = byteRev64 (m.readW a 64) >>> 32 := by
  rw [show bswap32 (m.readW a 32) = byteRev32 (m.readW a 32) from rfl, byteRev32_readW, byteRev64_readW,
    cat8_shr]

/-- The words, as `loadBytes` reads them (`Proof.Weierstrass.X86_64.ldWord`). -/
theorem xw_eq (P : RfcHash) (L : Lay dn) (m : Mem) {j : Nat} (h : 8 * (j + 1) ≤ P.Q ∨ 8 * (j + 1) = P.Q + 4 ∨ 8 * (j + 1) = P.Q + 8) :
    xw P L m j = if 8 * (j + 1) ≤ P.Q then byteRev64 (m.readW (xa L + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
      else byteRev64 (m.readW (xa L) 64) >>> (8 * (8 * (j + 1) - P.Q)) := by
  unfold xw
  split
  · rfl
  · split
    · rw [BitVec.ushiftRight_eq_zero (by omega_arith)]; rfl
    · rw [bswap32_readW, show 8 * (8 * (j + 1) - P.Q) = 32 by omega_arith]

/-- Only `rax`, `rcx` and `rdx` (and the flags and memory) changed since `t`. -/
structure RK (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.gpr r = t.gpr r

theorem RK.refl (t : State) : RK t t := ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem RK.trans {t u v : State} (h₁ : RK t u) (h₂ : RK u v) : RK t v :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b c => (h₂.gpr r a b c).trans (h₁.gpr r a b c)⟩

/-! ## The subtraction -/

/-- Word `j` of the number at `digest`, in `rax`, the flags kept. -/
theorem loadWord_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = xa L)
    {u : State} (hk : RK t u) {j : Nat} (_hj : j < P.w) :
    WP isa (.block ((cfgOf P).loadWord j)) u fun u' => RK u u' ∧ u'.mem = u.mem ∧ u'.cf = u.cf ∧
      u'.gpr .rax = xw P L u.mem j := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  have he := L.he
  obtain hrsi : u.gpr .rsi = xa L := by rw [hk.gpr _ (by decide) (by decide) (by decide), hsi]
  apply WP.of_runBlock
  by_cases h : 8 * (j + 1) ≤ P.Q
  · have hr : InRegions (u.rd ++ u.wr) (xa L + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 8 := by
      rw [hk.rd, hk.wr, xa, Offset.add_add]; exact hc.inFr (by simp only [fX]; omega_using [])
        (by simp only [fX]; omega_using [hQ, h6, h, he])
    have h' : 8 * (j + 1) ≤ (cfgOf P).len := h
    rw [Cfg.loadWord, ite_eq_left_of_eq_true _ _ (eq_true h'), show (cfgOf P).len = P.Q from rfl]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, ea_at, hrsi, hr, ite_true, Option.map_some, RegUpd.gpr_setReg,
      RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
    refine ⟨⟨by triv, by triv, fun r h₁ _ _ => ?_⟩, by triv, by triv, ?_⟩
    · simp only [RegUpd.gpr_setReg, h₁, ite_false]
    · simp only [xw, h, ite_true]
  · by_cases hz : P.Q ≤ 8 * j
    · rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 8 * (j + 1) ≤ (cfgOf P).len from h)),
        ite_eq_left_of_eq_true _ _ (eq_true (show (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, fun r hr _ _ => ?_⟩, trivial, trivial, ?_⟩
      · simp only [RegUpd.gpr_setReg, hr, ite_false]
      · simp [xw, h, hz]
    · have hr : InRegions (u.rd ++ u.wr) (xa L + BitVec.ofNat 64 0) 4 := by
        rw [hk.rd, hk.wr, xa, Offset.add_add]
        obtain ⟨r, hr, hcr⟩ := hc.inFrW (d := 24 + fX + 0) (n := 4) (by simp only [fX]; omega_using [])
          (by simp only [fX]; omega_using [he])
        exact ⟨r, List.mem_append_right _ hr, hcr⟩
      have h' : ¬ 8 * (j + 1) ≤ (cfgOf P).len := h
      rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
        State.load32, State.setReg32, ea_at, hrsi, hr, ite_true, Option.map_some, RegUpd.gpr_setReg,
        RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
      refine ⟨⟨by triv, by triv, fun r h₁ _ _ => ?_⟩, by triv, by triv, ?_⟩
      · simp only [RegUpd.gpr_setReg, h₁, ite_false]
      · simp only [xw, h, hz, ite_false, add_ofNat_zero, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          BitVec.setWidth_eq]

/-- Word `j`: of the number to `V`'s place, of the difference to `K`'s. -/
theorem subWord_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = xa L)
    {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) {c : Bool}
    (hcf : j = 0 ∨ u.cf = some c) :
    WP isa (.block ((cfgOf P).subWord j)) u fun u' => RK u u' ∧
      u'.mem = (u.mem.writeW (off L.B (88 + 8 * j)) (xw P L u.mem j)).writeW (off L.B (24 + 8 * j))
        (xw P L u.mem j - (cfgOf P).nWord j - (BitVec.ofBool (j != 0 && c)).setWidth 64) ∧
      u'.cf = some (decide ((xw P L u.mem j).toNat < ((cfgOf P).nWord j).toNat + (j != 0 && c).toNat)) := by
  obtain h6 : P.w ≤ 8 := (P.sizesA hA).2.1
  rw [Cfg.subWord, WP.block_append_iff]
  refine WP.mono (loadWord_ok hA hc hsi hk hj) fun u₁ ⟨k₁, m₁, cf₁, ax₁⟩ => ?_
  obtain hk₁ := hk.trans k₁
  obtain hrsp : u₁.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hk₁.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  obtain hV : InRegions u₁.wr (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk₁.wr]; exact hc.inFrW (by omega_using []) (by omega_using [hj, h6])
  obtain hK : InRegions u₁.wr (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk₁.wr]; exact hc.inFrW (by omega_using []) (by omega_using [hj, h6])
  obtain e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega_using []
  rw [← m₁] at ax₁ ⊢
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [fV, fK, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, ea_stk, hrsp, ax₁, Offset.add_add, e88,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      Option.bind_some, reduceCtorEq, ite_false, hV, hK, Nat.mul_zero, Nat.add_zero,
      Option.some.injEq, exists_eq_left']
    have hb : (0 != 0 && c) = false := rfl
    refine ⟨⟨k₁.rd, k₁.wr, fun r h₁ h₂ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]; exact k₁.gpr r h₁ h₂ h₃
    · have h0 : ∀ a : BitVec 64, a - (BitVec.ofBool false).setWidth 64 = a := fun a => by simp
      rw [hb, h0]
    · simp only [hb, Bool.toNat_false, Nat.add_zero]
  · have hcf' : u₁.cf = some c := cf₁.trans (hcf.resolve_left (by omega_using [hj0]))
    obtain hj' : j ≠ 0 := by omega_using [hj0]
    simp only [fV, fK, hj', ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, ea_stk, hrsp, ax₁, Offset.add_add, e88, Nat.zero_add,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      hcf', Option.map_some, Option.bind_some, reduceCtorEq, hV, hK, ite_true, Option.some.injEq,
      exists_eq_left']
    obtain hb : (j != 0 && c) = c := by simp [hj']
    refine ⟨⟨k₁.rd, k₁.wr, fun r h₁ h₂ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]; exact k₁.gpr r h₁ h₂ h₃
    · rw [hb]
    · simp only [hb]

/-- `X` is apart from `K` and `V`, so code that writes only there keeps its words. -/
theorem x_kept {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240) {d : Nat}
    (hd : d + 8 ≤ 72) : m'.readW (xa L + BitVec.ofNat 64 d) 64 = m.readW (xa L + BitVec.ofNat 64 d) 64 :=
  Proof.Weierstrass.readW_keep fun i hi =>
    Proof.Weierstrass.keep_of_disjoint (k := 72) h (Offset.disjoint _ (by simp only [fX]; omega_using [hn])
      (by simp only [fX]; omega_using []) (by omega_using [hn])) (by omega_using [hn])
      (by omega_using [hd, hi]) (by omega_using [])

/-- The words of the number at `X`, kept by code that writes only `K` and `V`. -/
theorem xw_kept {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240)
    (h8 : 8 ≤ P.Q) (hQ : P.Q ≤ 72) (j : Nat) : xw P L m' j = xw P L m j := by
  unfold xw
  split
  · rw [x_kept h hn (by omega_arith)]
  · split
    · rfl
    · refine congrArg (fun x => (bswap32 x).setWidth 64) (Mem.readW_congr fun i hi => ?_)
      obtain e := Proof.Weierstrass.keep_of_disjoint (k := 72) (p := xa L) h (Offset.disjoint _
        (by simp only [fX]; omega_using [hn]) (by simp only [fX]; omega_using []) (by omega_using [hn]))
        (by omega_using [hn]) (i := i) (by omega_using [hi]) (by omega_using [])
      exact e

/-- One more word of a subtraction with borrow: the words below `k` (`hs`)
and word `k` (`e`), weighted by `Q = 2^(64 k)`. -/
private theorem borrow_step {a b r x y z c d Q : Nat} (hs : a + r = b + Q * c)
    (e : x + y + c = z + 2 ^ 64 * d) : a + Q * x + (r + Q * y) = b + Q * z + 2 ^ 64 * Q * d := by
  grind

/-- After `k` words: the number's in `V`'s place, and the difference in
`K`'s with the borrow. -/
theorem subs_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) (hsi : t.gpr .rsi = xa L) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).subWord)) t fun u =>
      RK t u ∧ Outside L.B 24 128 t.mem u.mem ∧ (∀ j < k, word u.mem L.B (88 + 8 * j) = xw P L t.mem j) ∧
      ∃ c : Bool, (k = 0 → c = false) ∧ (0 < k → u.cf = some c) ∧
        wordsVal u.mem L.B 24 k + P.R.E.C.n % 2 ^ (64 * k) = wordsVal u.mem L.B 88 k + 2 ^ (64 * k) * c.toNat
  | 0, _ => WP.block_nil ⟨RK.refl _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      false, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _), by simp [wordsVal, Nat.mod_one]⟩
  | k + 1, hk => by
    obtain h6 : P.w ≤ 8 := (P.sizesA hA).2.1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (subs_ok hA hc hL hsi k (by omega_using [hk])) fun u₁ ⟨k₁, O₁, e₁, c, hc0, hcf, hs⟩ => ?_
    refine WP.mono (subWord_ok (P := P) hA hc hsi k₁ (j := k) (by omega_using [hk]) (c := c)
      (by rcases Nat.eq_zero_or_pos k with h | h; exacts [.inl h, .inr (hcf h)])) fun u₂ ⟨k₂, m₂, cf₂⟩ => ?_
    obtain hx : xw P L u₁.mem k = xw P L t.mem k :=
      xw_kept O₁ (by omega_using []) P.R.len_words.1 (by have := P.sizes; omega_arith) k
    obtain hb : (k != 0 && c) = c := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; rw [hc0 rfl]; rfl
      · simp [show k ≠ 0 by omega_using [h]]
    rw [hx, hb] at m₂ cf₂
    -- Each write is outside the other's word, and outside the words below `k`.
    obtain oK : Outside L.B (24 + 8 * k) 8 _ _ := writeW_outside (u₁.mem.writeW (off L.B (88 + 8 * k)) (xw P L t.mem k))
      L.B (xw P L t.mem k - (cfgOf P).nWord k - (BitVec.ofBool c).setWidth 64) (d := 24 + 8 * k) (by omega_using [hk, h6])
    obtain oV : Outside L.B (88 + 8 * k) 8 _ _ := writeW_outside u₁.mem L.B (xw P L t.mem k) (d := 88 + 8 * k)
      (by omega_using [hk, h6])
    rw [← m₂] at oK
    obtain wK : ∀ d, d + 8 ≤ 24 + 8 * k ∨ 24 + 8 * k + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
        d + 8 ≤ 88 + 8 * k ∨ 88 + 8 * k + 8 ≤ d → word u₂.mem L.B d = word u₁.mem L.B d := fun d h₁ h₂ h₃ => by
      rw [Proof.Mont.Outside.word oK h₁ h₂, Proof.Mont.Outside.word oV h₃ h₂]
    obtain wsK : wordsVal u₂.mem L.B 24 k = wordsVal u₁.mem L.B 24 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inl (by omega_using [])) (by omega_using [hk, h6]),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega_using [])) (by omega_using [hk, h6])]
    obtain wsV : wordsVal u₂.mem L.B 88 k = wordsVal u₁.mem L.B 88 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inr (by omega_using [hk, h6])) (by omega_using [hk, h6]),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega_using [])) (by omega_using [hk, h6])]
    obtain hV : word u₂.mem L.B (88 + 8 * k) = xw P L t.mem k := by
      rw [Proof.Mont.Outside.word oK (.inr (by omega_using [])) (by omega_using [hk, h6]), Proof.Mont.word_writeW_self]
    obtain hK : word u₂.mem L.B (24 + 8 * k) =
        xw P L t.mem k - (cfgOf P).nWord k - (BitVec.ofBool c).setWidth 64 := by
      rw [m₂, Proof.Mont.word_writeW_self]
    refine ⟨k₁.trans k₂, O₁.trans ?_, fun j hj => ?_, _, fun h => absurd h (by omega_using []), fun _ => cf₂, ?_⟩
    · rw [m₂]
      exact ((writeW_outside _ _ _ (by omega_using [hk, h6])).mono (by omega_using []) (by omega_using [hk, h6])).trans
        ((writeW_outside _ _ _ (by omega_using [hk, h6])).mono (by omega_using []) (by omega_using [hk, h6]))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wK _ (.inr (by omega_using [hk, h6])) (by omega_arith) (.inl (by omega_arith)), e₁ j hj]
      · exact hV
    · rw [wordsVal_succ_top, wordsVal_succ_top, wsK, wsV, hK, hV, n_split]
      obtain e := sbb_borrow (xw P L t.mem k) ((cfgOf P).nWord k) c
      have hn : (cfgOf P).nWord k = BitVec.ofNat 64 (P.R.E.C.n >>> (64 * k)) := rfl
      rw [hn] at e ⊢
      rw [Proof.Mont.pow64_succ]
      generalize 2 ^ (64 * k) = Q at *
      exact borrow_step hs e

/-! ## The selection -/

/-- Where `h`'s `8 w` bytes are (from `hB + Q - 8 w`, its top word's zero
bytes first): above `K` and `V`, in the frame above its pointers and the
slots of `D` and `B`. -/
theorem hb_facts (hA : P.R.big = false) :
    88 + 8 * P.w ≤ hB + P.Q - 8 * P.w ∧ 8 * P.w ≤ hB + P.Q ∧ hB + P.Q ≤ 240 + 8 * L.e ∧
      256 ≤ hB + P.Q - 8 * P.w ∧ P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 ∧ hB + P.Q ≤ 24 + fX := by
  obtain ⟨hQ, h8, h64⟩ := P.sizesA hA
  have := L.he
  have := P.R.len_words
  simp only [hB, fH, fX, RfcHash.w, RfcHash.Q] at *
  omega_arith

/-- Word `j` of the result, by the mask `rdx`, to `h`. -/
theorem selWord_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u)
    {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).selWord j)) u fun u' => RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧
      u'.mem = u.mem.writeW (off L.B (hB + P.Q - 8 * (j + 1)))
        (bswap64 (((word u.mem L.B (88 + 8 * j) ^^^ word u.mem L.B (24 + 8 * j)) &&& u.gpr .rdx) ^^^
          word u.mem L.B (24 + 8 * j))) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  obtain ⟨hb₁, hb₂, hb₃, -, -, -, -⟩ := hb_facts (L := L) hA
  obtain hrsp : u.gpr .rsp = L.B + BitVec.ofNat 64 24 := by rw [hk.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  obtain hV : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega_using []) (by omega_using [hj, h6])
  obtain hK : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega_using []) (by omega_using [hj, h6])
  obtain hH : InRegions u.wr (L.B + BitVec.ofNat 64 (hB + P.Q - 8 * (j + 1))) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega_using [hj, hb₁]) (by omega_using [hj, hb₁, hb₃])
  obtain e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega_using []
  have hwn : P.Q = P.R.E.C.len := rfl
  obtain eH : 24 + (fH + P.R.E.C.len - 8 * (j + 1)) = hB + P.Q - 8 * (j + 1) := by
    simp only [hB, fH] at hb₂ ⊢; omega_using [hj, hb₂, hwn, h6]
  apply WP.of_runBlock
  rw [Cfg.selWord]
  simp only [cfgOf, fV, fK, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, State.store64, ea_stk, hrsp, Offset.add_add, e88, eH, Nat.zero_add,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hV, hK, hH, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by trivial, by trivial, fun r h₁ h₂ _ => ?_⟩, by trivial, by trivial⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₂, ite_false]

/-- After `k` words of the result, with the mask of the borrow `c` in `rdx`. -/
theorem sels_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u)
    {c : Bool} {y : BitVec 64} (hm : u.gpr .rdx = y - y - (BitVec.ofBool c).setWidth 64) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).selWord)) u fun u' =>
      RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧ Outside L.B (hB + P.Q - 8 * P.w) (8 * P.w) u.mem u'.mem ∧
      ∀ j < k, word u'.mem L.B (hB + P.Q - 8 * (j + 1)) = bswap64 (word u.mem L.B ((if c then 88 else 24) + 8 * j))
  | 0, _ => WP.block_nil ⟨RK.refl _, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk' => by
    obtain ⟨hQ, h6, -⟩ := P.sizesA hA
    obtain ⟨hb₁, hb₂, hb₃, -, -, -, -⟩ := hb_facts (L := L) hA
    have he := L.he
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sels_ok hA hc hk hm k (by omega_using [hk'])) fun u₁ ⟨k₁, d₁, O₁, e₁⟩ => ?_
    refine WP.mono (selWord_ok (P := P) hA hc (hk.trans k₁) (j := k) (by omega_using [hk'])) fun u₂ ⟨k₂, d₂, m₂⟩ => ?_
    obtain oH : Outside L.B (hB + P.Q - 8 * (k + 1)) 8 u₁.mem u₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_using [hb₁, hb₃, he])
    obtain hV : word u₁.mem L.B (88 + 8 * k) = word u.mem L.B (88 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega_using [hk', hb₁])) (by omega_using [hk', h6])
    obtain hK : word u₁.mem L.B (24 + 8 * k) = word u.mem L.B (24 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega_using [hk', hb₁])) (by omega_using [hk', h6])
    refine ⟨k₁.trans k₂, d₂.trans d₁, O₁.trans (oH.mono (by omega_using [hk', hb₂]) (by omega_using [hk', hb₂])),
      fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Proof.Mont.Outside.word oH (by omega_arith) (by omega_using [hb₁, hb₃, he]), e₁ j hj]
    · rw [m₂, Proof.Mont.word_writeW_self, hV, hK, d₁, hm, sel_mask]
      cases c <;> rfl

/-! ## The whole of it -/

/-- `h`: `X`'s `Q` bytes modulo `n`, big-endian in the frame at `hB`. -/
theorem reduce_ok (hA : P.R.big = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩, ⟨L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w), 8 * P.w⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 hB) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (xa L) P.Q) % P.R.E.C.n) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -, -, -⟩ := hb_facts (L := L) hA
  have he := L.he
  have h4 : 4 ≤ P.w := P.R.n4
  refine WP.of_syms ?_
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := fX) (by decide)) fun t₀ h₀ => ?_
  have hc₀ := h₀.ctx
  have hsi : t₀.gpr .rsi = xa L := h₀.val
  rw [← h₀.mem]
  refine WP.mono (subs_ok hA hc₀ hL hsi P.w (Nat.le_refl _)) fun u₁ ⟨k₁, O₁, e₁, c, _, hcf, hs⟩ => ?_
  obtain hcf₁ : u₁.cf = some c := hcf (by omega_using [h4])
  -- The mask of the borrow.
  refine WP.mono (show WP isa (.block ([.alu .sbb .rdx (.reg .rdx)] : List Instr)) u₁ fun u₂ =>
      RK u₁ u₂ ∧ u₂.mem = u₁.mem ∧ u₂.gpr .rdx = u₁.gpr .rdx - u₁.gpr .rdx - (BitVec.ofBool c).setWidth 64 by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, hcf₁, Option.map_some,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨by trivial, by trivial, fun r _ _ h₃ => ?_⟩, by trivial, by trivial⟩
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₃, ite_false]) fun u₂ ⟨k₂, m₂, d₂⟩ => ?_
  refine WP.mono (sels_ok (P := P) hA hc₀ (k₁.trans k₂) d₂ P.w (Nat.le_refl _)) fun t' ⟨k₃, _, O₃, e₃⟩ hsy => ?_
  obtain k' : RK t₀ t' := (k₁.trans k₂).trans k₃
  obtain f₁ : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] t₀.mem u₂.mem := by
    rw [m₂]; exact frame_of_outside O₁ (by omega_using [])
  obtain f₃ : Frame [⟨L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w), 8 * P.w⟩] u₂.mem t'.mem :=
    frame_of_outside O₃ (by omega_using [hb₂, hb₃, he])
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩, ⟨L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w), 8 * P.w⟩]
      t₀.mem t'.mem :=
    (f₁.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  obtain hk₀ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r := fun r h₁ h₂ h₃ h₄ =>
    (k'.gpr r h₁ h₂ h₃).trans (h₀.keep r h₄)
  refine ⟨hc.keep hL (k'.rd.trans (hc₀.rd.trans hc.rd.symm)) (k'.wr.trans (hc₀.wr.trans hc.wr.symm))
    (hk₀ _ (by decide) (by decide) (by decide) (by decide))
    (fun r hr _ => hk₀ r (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide)))
    (h₀.mem ▸ hf)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact safe_low L (by omega_using [])
      · exact safe_high L hb₄ (by omega_using [hb₂, hb₃])) hsy, hf, ?_⟩
  -- The number, the difference, and the one selected.
  obtain ⟨w', hw'⟩ : ∃ w', P.w = w' + 1 := ⟨P.w - 1, by omega_using [h4]⟩
  obtain hX : wordsVal u₁.mem L.B 88 P.w = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t₀.mem (xa L) P.Q) := by
    rw [hw']
    exact Proof.Weierstrass.wordsVal_eq_ofBytes_len _ _ _ _ 88 w' P.Q (by omega_using [hQ, hw']) (by omega_using [hQ, hw']) fun j hj => by
      rw [e₁ j (by omega_using [hw', hj]), xw_eq P L t₀.mem (by omega_using [hQ, hw', hj])]
  obtain hsel := Proof.Weierstrass.bytesAt_eq_toBytes t'.mem u₂.mem L.B (L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w))
    (a := if c then 88 else 24) (n := P.w) true fun j hj => by
      rw [Offset.add_add, show hB + P.Q - 8 * P.w + 8 * (P.w - 1 - j) = hB + P.Q - 8 * (j + 1) by
        omega_using [hb₂, hj]]
      simp only [ite_true, BitVec.and_allOnes]
      exact e₃ j hj
  simp only [ite_true] at hsel
  rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl] at hX ⊢
  obtain hu : ∀ d, wordsVal u₂.mem L.B d P.w = wordsVal u₁.mem L.B d P.w := fun d => by rw [m₂]
  obtain hn : P.R.E.C.n % 2 ^ (64 * P.w) = P.R.E.C.n := Nat.mod_eq_of_lt P.R.n_lt
  rw [hn] at hs
  obtain hN := (P.R.sizesA hA).2.2.2
  obtain hXl : wordsVal u₁.mem L.B 88 P.w < 2 * P.R.E.C.n := by
    rw [hX]
    have := Proof.Ecdsa.Rfc6979.ofBytes_lt (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q)
    rw [Proof.Weierstrass.length_bytesAt] at this
    exact Nat.lt_trans this hN
  obtain key := Proof.Ecdsa.Rfc6979.mod_math2 _ _ _ _ c hs (wordsVal_lt _ _ _ _) hXl
  -- `h`'s `Q` bytes are the last of the `8 w` the words were stored to.
  obtain hv : (if c then wordsVal u₂.mem L.B 88 P.w else wordsVal u₂.mem L.B 24 P.w) =
      Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q) % P.R.E.C.n := by
    rw [← hX, ← key, hu, hu]
  obtain hlt : Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q) % P.R.E.C.n < 2 ^ (8 * P.Q) := by
    have := Nat.mod_lt (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q)) (Nat.pos_of_ne_zero P.R.n_ne)
    obtain hb : P.R.E.C.n < 2 ^ (8 * P.R.E.C.len) := by
      have := Nat.lt_log2_self (n := P.R.E.C.n)
      rwa [show P.R.E.C.n.log2 + 1 = 8 * P.R.E.C.len from (P.R.sizesA hA).2.2.1] at this
    show _ < 2 ^ (8 * P.R.E.C.len)
    omega_using [this, hb]
  obtain hsel' : Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w)) (8 * P.w) =
      Spec.Weierstrass.toBytes (8 * P.w) (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q) % P.R.E.C.n) := by
    rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl, hsel]
    refine congrArg _ ?_
    rw [← hv]; cases c <;> rfl
  rw [show 8 * P.w = (8 * P.w - P.Q) + P.Q by omega_using [hQ], Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show hB + P.Q - ((8 * P.w - P.Q) + P.Q) + (8 * P.w - P.Q) = hB by omega_using [hQ, hb₂],
    Proof.Ecdsa.Rfc6979.toBytes_pad _ _ _ hlt] at hsel'
  exact (List.append_inj' hsel' (by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range, Proof.Weierstrass.length_toBytes])).2

end VG.Proof.Ecdsa.Rfc6979.X86_64
