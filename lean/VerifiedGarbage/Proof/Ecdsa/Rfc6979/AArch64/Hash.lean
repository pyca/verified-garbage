module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Hmac.Contract
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1.Table
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-! ### `Ecdsa.Rfc6979.AArch64.Curve`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on AArch64: the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`): the code of
`vg_ecdsa_<curve>_sign_k` for curves of `n` words (`Impl.Ecdsa.AArch64.Cfg`),
the instance of ECDSA it is, its sizes: scalars of `Q` bytes in 4, 6 or 8
words (32, 48 or 64 bytes, or P-192's 24 and P-224's 28 in 4) whose order
`n` has exactly `8 Q` bits and `2^(8 Q) < 2 n` (so that `bits2octets` is one
conditional subtraction), or, if `big`, P-521's (9 words, 66 bytes, 521
bits: longer than any digest); the bits `sh` the signature drops from its
digest; the facts of its blocks (`RfcT`); and what is proven of the code:
that it meets the contract the proof of each curve is written against
(`coreK`: P-256's `signAArch64`, the others' at the curve's sizes), in
constant time, that it pushes no frame and writes no callee-saved SIMD
register. Each curve's file builds one, so that the heavy algebra of its
proof stays out of the modules generic over the curve and the hash
function.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.AArch64.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, with the
comb's tables at the static `E.tsym`, as each curve's proof states it
(`Proof.Ecdsa.AArch64.signAArch64` for P-256). -/
def coreK (E : Impl.Ecdsa.AArch64.Cfg) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 2 * E.C.len⟩
    let d : Region := ⟨s.gpr .x1, E.C.len⟩
    let digest : Region := ⟨s.gpr .x2, E.C.len⟩
    let k : Region := ⟨s.gpr .x3, E.C.len⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k] ++ tableRegions E (tableAddr E s.syms) ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 2 * E.C.len ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblOk E s [out, scratch]
  post s s' :=
    match coreSigOf E s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) (2 * E.C.len) = encode E.C rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) (2 * E.C.len) =
        List.replicate (2 * E.C.len) 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧ tableAddr E s₁.syms = tableAddr E s₂.syms

/-- The code's blocks for scalars of `E` (with `h = X` and `core`'s digest
shifted if `big`, by `sh` bits), without the functions it calls. -/
def cfgC (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh : Nat) : Impl.Ecdsa.Rfc6979.AArch64.Cfg where
  f := ⟨[], [], []⟩
  w := E.n
  len := E.C.len
  big := big
  sh := sh
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- The taint check of a block whose addresses depend only on `sp` and `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- None of the instructions of the block `is` writes a callee-saved SIMD register. -/
abbrev OkB (is : List Instr) : Prop := (Code.block is : Prog isa).allInstrs keepsV = true

open Impl.Ecdsa.Rfc6979.AArch64 in
/-- The blocks whose contents depend on the curve: each addresses memory
only from `sp` and the registers that hold the pointers the code put there
(the taint analysis), and none of their instructions writes a callee-saved
SIMD register. -/
structure RfcT (c : Impl.Ecdsa.Rfc6979.AArch64.Cfg) : Prop where
  xArgs : TaintOk [] c.xArgs
  reduce : c.big = false → TaintOk [] c.reduce
  msgF₀ : TaintOk [.x9, .x10, .x15] (c.msg 0 true)
  msgF₁ : TaintOk [.x9, .x10, .x15] (c.msg 1 true)
  updM : TaintOk [] (Cfg.updMArgs (1 + 2 * c.len))
  finM : TaintOk [] (Cfg.finArgs (1 + 2 * c.len) fK)
  tStep : TaintOk [] c.tStep
  coreArgs : TaintOk [] c.coreArgs
  xcArgs : c.big = true → TaintOk [] c.xcArgs
  convC : c.big = true → TaintOk [.x0] (c.convB fXc (8 - c.sh))
  convT : c.big = true → TaintOk [.x0] (c.convB fT c.sh)
  iXArgs : OkB c.xArgs
  iReduce : OkB c.reduce
  iMsgF₀ : OkB (c.msg 0 true)
  iMsgF₁ : OkB (c.msg 1 true)
  iUpdM : OkB (Cfg.updMArgs (1 + 2 * c.len))
  iFinM : OkB (Cfg.finArgs (1 + 2 * c.len) fK)
  iTStep : OkB c.tStep
  iCoreArgs : OkB c.coreArgs
  iXcArgs : OkB c.xcArgs
  iConvC : OkB (c.convB fXc (8 - c.sh))
  iConvT : OkB (c.convB fT c.sh)

/-- `RfcT` of a curve's blocks, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { xArgs := ⟨_, by taint_decide⟩, reduce := by exact (Function.const _ ⟨_, by taint_decide⟩),
    msgF₀ := ⟨_, by taint_decide⟩, msgF₁ := ⟨_, by taint_decide⟩, updM := ⟨_, by taint_decide⟩,
    finM := ⟨_, by taint_decide⟩, tStep := ⟨_, by taint_decide⟩, coreArgs := ⟨_, by taint_decide⟩,
    xcArgs := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convC := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convT := by exact (Function.const _ ⟨_, by taint_decide⟩),
    iXArgs := by decide +kernel, iReduce := by decide +kernel, iMsgF₀ := by decide +kernel,
    iMsgF₁ := by decide +kernel, iUpdM := by decide +kernel, iFinM := by decide +kernel,
    iTStep := by decide +kernel, iCoreArgs := by decide +kernel, iXcArgs := by decide +kernel,
    iConvC := by decide +kernel, iConvT := by decide +kernel })

/-- A curve, for RFC 6979 on AArch64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign_k` has it. -/
  E : Impl.Ecdsa.AArch64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output and
  `n` has fewer bits than they do (P-521's), so that `h` is the digest's
  integer and `core` takes it shifted (`Impl.Ecdsa.Rfc6979.AArch64.Cfg.big`). -/
  big : Bool
  /-- Scalars of 4, 6 or 8 words, `8 n` bytes (or 24 or 28 in 4 words), and `n` of
  exactly `8 len` bits, with `2^(8 len) < 2 n`; or, if `big`, of 9 words and
  66 bytes, and `n` of 521 bits. -/
  sizes : if big then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6 ∨ E.n = 8) ∧ (E.C.len = 8 * E.n ∨ E.n = 4 ∧ (E.C.len = 28 ∨ E.C.len = 24)) ∧
      nBits E.C = 8 * E.C.len ∧ 2 ^ (8 * E.C.len) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : E.sh = sh
  /-- `vg_ecdsa_<curve>_sign_k`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It pushes no frame, and none of its instructions writes a callee-saved SIMD register. -/
  coreNoFrames : coreC.noFrames = true
  coreKeepsV : coreC.allInstrs keepsV = true
  /-- The taint checks and instruction facts of the curve's blocks. -/
  blk : RfcT (cfgC E big sh)

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.big = false) :
    (R.E.n = 4 ∨ R.E.n = 6 ∨ R.E.n = 8) ∧ (R.E.C.len = 8 * R.E.n ∨ R.E.n = 4 ∧ (R.E.C.len = 28 ∨ R.E.C.len = 24)) ∧
      nBits R.E.C = 8 * R.E.C.len ∧ 2 ^ (8 * R.E.C.len) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.big = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n4 : 4 ≤ R.E.n := by
  cases h : R.big
  · rcases (R.sizesA h).1 with h | h | h <;> omega_using [h]
  · rw [(R.sizesW h).1]; omega_using []

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.big
  · rcases (R.sizesA h).1 with h | h | h <;> omega_using [h]
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

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-! ### `Ecdsa.Rfc6979.AArch64.Regs`, which the modules that import this one used -/

section

/-! ### `HmacTable.AArch64`, which this module and modules that import it used -/

section

/-!
# Tables of the interface `Hmac` on AArch64

The table of a hash function's variant (`tableOf`, `VG_HMAC_<HASH><SUFFIX>`):
the addresses of HMAC's `init` and `finalize` and of the streaming `update`,
in the forms that take their working space as an argument (`_scratch`, in
`x4`: `Hash.hmacInit`, `Hash.updC`, `Hash.hmacFin`), then its data
(`Spec.HmacTable.dataOf`: the hash function's index in `Mgf1.hashes`, its
digest length and HMAC's block size); the tables of a list of variants
(`tables`, one for each), which a function taking a table of `Hmac` lists
as those it may be given; and the functions an indirect call of each of a
table's functions may reach (`fnsOf`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`).

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
variants' functions of the same name have the same code (`Coh`, which the
registration checks). `held_tableOf` reads a table's words, and
`hashAt_tableOf` the hash function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.HashTable (pw_ne find_name)

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH><SUFFIX>`. -/
def tableOf (w : MdHash) : FnTable where
  name := s!"VG_HMAC_{w.mgf.G.rust.toUpper}{w.suffix.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.H.hmacInitN, w.H.updN, w.H.hmacFinN]
  data := Spec.HmacTable.dataOf w.mgf.G

/-- The tables of the variants `vs`. -/
def tables (vs : List MdHash) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List MdHash) : Fns :=
  ⟨vs.map fun w => (w.H.hmacInitN, w.H.hmacInit), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.H.hmacFinN, w.H.hmacFin)⟩

/-- The functions of `tables vs`. -/
def names (vs : List MdHash) : List String := ((tables vs).map (·.fns)).flatten

/-- The variants' functions of the same name have the same code. -/
def Coh (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.H.hmacInitN = w'.H.hmacInitN → w.H.hmacInit = w'.H.hmacInit) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.H.hmacFinN = w'.H.hmacFinN → w.H.hmacFin = w'.H.hmacFin)

instance (vs : List MdHash) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `H`'s HMAC functions reaches it. -/
structure TabOK (H : Hash) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy H.hmacInitN) = some (H.hmacInitN, H.hmacInit)
  u : f.upd.find? (fun q => sy q.1 == sy H.updN) = some (H.updN, H.updC)
  f : f.fin.find? (fun q => sy q.1 == sy H.hmacFinN) = some (H.hmacFinN, H.hmacFin)

/-- At `p` in `m`, the addresses `sy` gives `H`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (H : Hash) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW (p + BitVec.ofNat 64 0) 64 = sy H.hmacInitN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy H.hmacFinN

theorem mem_names {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) :
    w.H.hmacInitN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.H.hmacFinN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List MdHash} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : MdHash} (hw : w ∈ vs) :
    TabOK w.H (fnsOf vs) sy := by
  have hn := mem_names hw
  refine ⟨find_name (List.mem_map_of_mem hw) ?_ ?_, find_name (List.mem_map_of_mem hw) ?_ ?_,
    find_name (List.mem_map_of_mem hw) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd _ (mem_names hw').2.1 _ hn.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd _ (mem_names hw').2.2 _ hn.2.2
  · exact (hc w' hw' w hw).2.2

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : MdHash) :
    FnTable.words isa s (tableOf w) = [s.syms w.H.hmacInitN, s.syms w.H.updN, s.syms w.H.hmacFinN,
      BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w.H s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G) := by
  rw [words_tableOf] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_, h 5 (by simp)⟩
  exact (h 4 (by simp)).trans (by rw [w.mgf.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : MdHash}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    Spec.HmacTable.hashAt 64 m p = some w.mgf.G := by
  have hm := w.mgf.mem
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h]
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> rfl

end VG.Proof.HmacTable.AArch64

end

end

/-! ### `Ecdsa.Rfc6979.AArch64.Layout`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on AArch64: where everything is

The function's buffers (`out` of `2 q` bytes, `d` of `q`, `digest` of `dn`,
`scratch`), the table `hmac` (48 bytes) and the `256 + 8 e` bytes of stack
below the stack pointer, from `B` up (`Lay dn E`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`): the 16 bytes the calls use
(HMAC's functions' frames), then the frame of `224 + 8 e` bytes, from
`B + 16`: `K` and `V` (64 bytes each), the length of `T`, the number of
candidates left, the pointers to `scratch`, `digest`, `d` and `out`, and
`e` more words (`D`, `B`, then `HIGH`: `h`, `X`, `core`'s digest and `T`),
the table's address at its top; then the frame holding our return
address (`LR`). `Ctx` is what holds between the frames' pushes and pops: the
permissions, `sp`, the callee-saved registers, the return address, the
pointers, `D`, `B` and the table's address in the frame, that memory changed
only in `out`, `scratch` and the stack, where the comb's tables `core`
reads are, and what the table `hmac` holds. Code that writes only regions
apart from those words (`Safe`) keeps it (`Ctx.keep`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.HmacTable.AArch64 (TabOK TabMem)

/-- The buffers and the lowest byte of the stack used (`sp - (256 + 8 e)` on
entry), for a digest of `dn` bytes and scalars of `q`. -/
structure Lay (dn : Nat) (E : Impl.Ecdsa.AArch64.Cfg) where
  out : Addr
  d : Addr
  dg : Addr
  scr : Addr
  /-- The table of HMAC. -/
  tab : Addr
  B : Addr
  q : Nat
  /-- The comb's tables (the static `E.tsym`), which `core` reads. -/
  T : Addr
  /-- The words above the frame's pointers. -/
  e : Nat
  he : e = 48
  /-- The hash function's code, whose HMAC functions the table holds, and
  the functions an indirect call of a table's functions may reach. -/
  H : Hash
  f : Fns
  /-- The addresses of `H`'s HMAC functions, public. -/
  fa : String → Addr

namespace Lay

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E)

abbrev OUT : Region := ⟨L.out, 2 * L.q⟩
abbrev D : Region := ⟨L.d, L.q⟩
abbrev DG : Region := ⟨L.dg, dn⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The table of HMAC. -/
abbrev TAB : Region := ⟨L.tab, 48⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 256 + 8 * L.e⟩
/-- The frames: our words, and our return address. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 224 + 8 * L.e⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 (240 + 8 * L.e), 16⟩
/-- The stack below the frame's pointers: the calls' and `K`, `V`, `|T|` and the count. -/
abbrev LOW : Region := ⟨L.B, 200⟩
/-- The frame above its pointers and the slots of `D` and `B`, below the table's address. -/
abbrev HIGH : Region := ⟨L.B + BitVec.ofNat 64 248, 8 * L.e - 16⟩
/-- The comb's tables. -/
abbrev TBL : Region := ⟨L.T, 8 * E.combWords.length⟩
abbrev tables : List Region := tableRegions E L.T

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
  nB : L.B.toNat + (256 + 8 * L.e) ≤ 2 ^ 64
  tOut : L.TBL.Disjoint L.OUT
  tScr : L.TBL.Disjoint L.SCR
  tStk : L.TBL.Disjoint L.STK
  nT : L.T.toNat + 8 * E.combWords.length ≤ 2 ^ 64

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A region of the frame. -/
theorem within_fr (B : Addr) {d n x : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 240 + x) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 224 + x⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega_arith⟩

theorem covers_of {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, off, hb, hl⟩ := h r hr
    exact ⟨R, hR, off, hb, hl⟩

/-- A region the code may write without disturbing `Ctx`: within `out`,
`scratch` or the stack below or above the frame's pointers. -/
def Safe {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (r : Region) : Prop :=
  Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW ∨ Region.Sub r L.HIGH

theorem safe_low {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) {d n : Nat} (h : d + n ≤ 200) :
    Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inl (Offset.sub_base _ h)))

theorem safe_high {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) {d n : Nat} (h₁ : 248 ≤ d)
    (h₂ : d + n ≤ 232 + 8 * L.e) : Safe L ⟨L.B + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr (Offset.sub _ h₁ (by have := L.he; omega_arith))))

theorem Safe.of_sub {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {r r' : Region} (hs : Safe L r')
    (h : Region.Sub r r') : Safe L r := by
  rcases hs with hs | hs | hs | hs
  exacts [.inl fun x hx => hs x (h x hx), .inr (.inl fun x hx => hs x (h x hx)),
    .inr (.inr (.inl fun x hx => hs x (h x hx))), .inr (.inr (.inr fun x hx => hs x (h x hx)))]

theorem safe_scr {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) {d n : Nat} (h : d + n ≤ 8192) :
    Safe L ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inl (Offset.sub_base _ h))

namespace Lay.Ok

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 256 + 8 * L.e) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_scr0 (h : L.Ok) {d n k : Nat} (h₁ : d + n ≤ 256 + 8 * L.e) (h₂ : k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Region.sub_prefix h₂)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 256 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 256 + 8 * L.e) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

/-- The 16 bytes the calls use, apart from `scratch`. -/
theorem low_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ h₂)

/-- A region at an offset of the stack apart from every safe region: at or
above the pointers and below `h`'s place, or above the table's slot. -/
theorem stk_safe (h : L.Ok) {d n : Nat} (h₁ : 200 ≤ d) (h₂ : d + n ≤ 248 ∨ 232 + 8 * L.e ≤ d)
    (h₃ : d + n ≤ 256 + 8 * L.e) {r : Region} (hs : Safe L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := h.nB
  have := L.he
  rcases hs with hs | hs | hs | hs
  · exact (h.stk_OUT h₃).sub_right hs
  · exact (h.stk_SCR h₃).sub_right hs
  · exact (Offset.disjoint_base _ h₁ (by omega_arith)).sub_right hs
  · exact (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)).sub_right hs

end Lay.Ok

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem)
    (t : State) : Prop where
  rd : t.rd = [L.D, L.DG, L.TAB] ++ L.tables
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SCR]
  sp : t.sp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 200) 64 = L.scr
  pDg : t.mem.readW (L.B + BitVec.ofNat 64 208) 64 = L.dg
  pD : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.d
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.out
  pTab : t.mem.readW (L.B + BitVec.ofNat 64 (232 + 8 * L.e)) 64 = L.tab
  /-- `D` and `B`, above the pointers. -/
  pDl : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 L.H.D
  pBl : t.mem.readW (L.B + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 L.H.P.B
  lr : t.mem.readW (L.B + BitVec.ofNat 64 (240 + 8 * L.e)) 64 = g .x30
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sy : tableAddr E t.syms = L.T
  held : ∀ i < E.combWords.length,
    m₀.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = E.combWords.getD i 0
  tabOk : TabOK L.H L.f t.syms
  tabMem : TabMem L.H t.syms L.tab m₀
  fsy : ∀ n ∈ [L.H.hmacInitN, L.H.updN, L.H.hmacFinN], t.syms n = L.fa n

theorem Safe.sub_frame {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {r : Region} (h : Safe L r) :
    ∃ R ∈ [L.OUT, L.SCR, L.STK], Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨L.STK, by simp, fun a ha => Region.sub_prefix (base := L.B) (by omega_arith) a (h a ha)⟩
  · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base (p := L.B) (d := 248) (n := 8 * L.e - 16)
      (by have := L.he; omega_arith) a (h a ha)⟩

namespace Ctx

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}

/-- Code that keeps the permissions, `sp` and the callee-saved registers
but `x30`, and writes only safe regions. -/
theorem keep (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r)
    (hsy : t'.syms = t.syms) : Ctx L g m₀ t' := by
  have := hL.nB
  have := L.he
  have keep : ∀ d, 200 ≤ d → d + 8 ≤ 248 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => hL.stk_safe h₁ (.inl h₂) (by omega_arith) (hs r hr)) (by decide)
  have keepHi : ∀ d, 232 + 8 * L.e ≤ d → d + 8 ≤ 256 + 8 * L.e →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨L.B + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => hL.stk_safe (by omega_arith) (.inr h₁) h₂ (hs r hr)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 200 (by omega_arith) (by omega_arith)).trans hc.pScr, (keep 208 (by omega_arith) (by omega_arith)).trans hc.pDg,
    (keep 216 (by omega_arith) (by omega_arith)).trans hc.pD, (keep 224 (by omega_arith) (by omega_arith)).trans hc.pOut,
    (keepHi _ (Nat.le_refl _) (by omega_arith)).trans hc.pTab,
    (keep 232 (by omega_arith) (by omega_arith)).trans hc.pDl, (keep 240 (by omega_arith) (by omega_arith)).trans hc.pBl,
    (keepHi _ (by omega_arith) (by omega_arith)).trans hc.lr,
    hc.frame.trans (hf.sub fun r hr => (hs r hr).sub_frame), by rw [hsy]; exact hc.sy, hc.held,
    by rw [hsy]; exact hc.tabOk, by rw [hsy]; exact hc.tabMem, by rw [hsy]; exact hc.fsy⟩

/-- Code that writes only registers but the callee-saved ones. -/
theorem regs (hL : L.Ok) (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) (hsy : t'.syms = t.syms) :
    Ctx L g m₀ t' :=
  hc.keep hL hrd hwr hsp hg (ws := []) (by rw [hm]; exact Frame.refl _ _) (by simp) hsy

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

/-- A word of the table, as on entry. -/
theorem tab_word (hL : L.Ok) (hc : Ctx L g m₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (L.tab + BitVec.ofNat 64 o) 64 = m₀.readW (L.tab + BitVec.ofNat 64 o) 64 :=
  hc.frame.readW (r := L.TAB) (Offset.contains_base _ ho (by have := hL.nt; omega_arith)) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.to
    · exact hL.tc
    · exact hL.tk) (by decide)

theorem inFr (hc : Ctx L g m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 240 + 8 * L.e) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  have := L.he
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩

theorem inFrW (hc : Ctx L g m₀ t) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 240 + 8 * L.e) :
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
theorem covers (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within r R) : Covers rs (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl <;> simp

theorem coversW (hc : Ctx L g m₀ t) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) : Covers rs t.wr :=
  covers_of fun r hr => by
    obtain ⟨R, hR, hw⟩ := h r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp

end Ctx

/-! ## The layout of a call, and the frames' entry -/

/-- The layout of a call from `s`, with a digest of `dn` bytes, scalars of
`q`, `e` words above the pointers, and the hash function `H`'s HMAC through
the table, whose functions an indirect call reaches among `f`'s. -/
def lay (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (e : Nat) (he : e = 48) (H : Hash) (f : Fns) (s : State) :
    Lay dn E :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x4, s.gpr .x5, s.sp - BitVec.ofNat 64 (256 + 8 * e), q,
    tableAddr E s.syms, e, he, H, f, fun n => if n ∈ [H.hmacInitN, H.updN, H.hmacFinN] then s.syms n else 0⟩

/-- What the contract says of the table at `x5`, after the entry: it holds
`H`'s HMAC functions, which an indirect call of `f`'s reaches, and `x6` and
`x7` hold its digest length and HMAC's block size. -/
def tabFacts (H : Hash) (f : Fns) (s : State) : Prop :=
  TabOK H f s.syms ∧ TabMem H s.syms (s.gpr .x5) s.mem ∧ s.gpr .x6 = BitVec.ofNat 64 H.D ∧
    s.gpr .x7 = BitVec.ofNat 64 H.P.B

theorem lay_top (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (e : Nat) (he : e = 48) (H : Hash) (f : Fns)
    (s : State) : (lay dn q E e he H f s).B + BitVec.ofNat 64 (256 + 8 * e) = s.sp :=
  BitVec.sub_add_cancel _ _

theorem lay_ok {E : Impl.Ecdsa.AArch64.Cfg} {I : Proof.Ecdsa.Rfc6979.Instance} {e : Nat} (he : e = 48)
    {H : Hash} {f : Fns} {ns : List String} {s : State}
    (h : (rfcAArch64 E I (256 + 8 * e) (tabFacts H f) ns).pre s) :
    (lay I.hashLen I.ecdsa.curve.len E e he H f s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, ⟨-, nT, hdw⟩, nt, tout, tsc, tstk, -⟩ := h
  have nB : (lay I.hashLen I.ecdsa.curve.len E e he H f s).B.toNat + (256 + 8 * e) ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp (256 + 8 * e)]
    omega_arith
  exact ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nt, tout, tsc, tstk, nB,
    hdw _ (List.mem_cons_self ..), hdw _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    hdw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))), nT⟩

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State :=
  allocated Impl.Ecdsa.Rfc6979.AArch64.frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_syms (s : State) : (entered s).syms = s.syms := rfl

theorem entered_sp (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (H : Hash) (f : Fns) (s : State) :
    (entered s).sp = (lay dn q E 48 rfl H f s).B + BitVec.ofNat 64 16 := by
  show s.sp - 16 - BitVec.ofNat 64 608 = s.sp - BitVec.ofNat 64 (256 + 8 * 48) + BitVec.ofNat 64 16
  bv_omega

theorem lr_slot (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (H : Hash) (f : Fns) (s : State) :
    s.sp - 16 = (lay dn q E 48 rfl H f s).B + BitVec.ofNat 64 (240 + 8 * (lay dn q E 48 rfl H f s).e) := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 (256 + 8 * 48) + BitVec.ofNat 64 (240 + 8 * 48)
  bv_omega

theorem entered_wr (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (H : Hash) (f : Fns) (s : State) :
    (entered s).wr = (lay dn q E 48 rfl H f s).FR :: (lay dn q E 48 rfl H f s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 608, 608⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 608 = (lay dn q E 48 rfl H f s).B + BitVec.ofNat 64 16 from
    entered_sp dn q E H f s, lr_slot dn q E H f]
  rfl

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem entered_mem (dn q : Nat) (E : Impl.Ecdsa.AArch64.Cfg) (H : Hash) (f : Fns) (s : State) :
    (entered s).mem =
      s.mem.writeW ((lay dn q E 48 rfl H f s).B + BitVec.ofNat 64 (240 + 8 * (lay dn q E 48 rfl H f s).e))
        (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot dn q E H f, write8]

/-- A word read at `B + x` past a write at `B + y`, apart from it. -/
theorem rdW_sep (B : Addr) (m : Mem) (v : BitVec 64) {x y : Nat}
    (h : (x + 8 ≤ y ∨ y + 8 ≤ x) ∧ x + 8 ≤ 2 ^ 64 ∧ y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h.1 h.2.1 h.2.2) (by decide)

/-- The memory `saveArgs` leaves: seven words stored in the frame. -/
abbrev saved (B : Addr) (m : Mem) (o d g c l b t : BitVec 64) : Mem :=
  ((((((m.writeW (B + BitVec.ofNat 64 224) o).writeW (B + BitVec.ofNat 64 216) d).writeW
    (B + BitVec.ofNat 64 208) g).writeW (B + BitVec.ofNat 64 200) c).writeW (B + BitVec.ofNat 64 232) l).writeW
    (B + BitVec.ofNat 64 240) b).writeW (B + BitVec.ofNat 64 616) t

/-- What `saved` writes, and what it reads back. -/
theorem saved_ok (B : Addr) (m : Mem) (o d g c l b t : BitVec 64) :
    Frame [⟨B + BitVec.ofNat 64 200, 48⟩, ⟨B + BitVec.ofNat 64 616, 8⟩] m (saved B m o d g c l b t) ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 224) 64 = o ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 216) 64 = d ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 208) 64 = g ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 200) 64 = c ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 232) 64 = l ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 240) 64 = b ∧
      (saved B m o d g c l b t).readW (B + BitVec.ofNat 64 616) 64 = t := by
  have ct : ∀ x, 200 ≤ x → x + 8 ≤ 248 →
      (⟨B + BitVec.ofNat 64 200, 48⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega_arith) (by omega_arith)
  have m₁ : (⟨B + BitVec.ofNat 64 200, 48⟩ : Region) ∈ [⟨B + BitVec.ofNat 64 200, 48⟩, ⟨B + BitVec.ofNat 64 616, 8⟩] :=
    List.mem_cons_self ..
  refine ⟨((((((((Frame.refl _ _).writeW m₁ _ (ct 224 (by omega_arith) (by omega_arith))).writeW m₁ _
    (ct 216 (by omega_arith) (by omega_arith))).writeW m₁ _ (ct 208 (by omega_arith) (by omega_arith))).writeW m₁ _
    (ct 200 (by omega_arith) (by omega_arith))).writeW m₁ _ (ct 232 (by omega_arith) (by omega_arith))).writeW m₁ _
    (ct 240 (by omega_arith) (by omega_arith))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
    (Region.contains_self _ _)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := decide) only [saved, rdW_sep, Mem.readW_writeW_self64]

/-- The arguments, `D`, `B` and the table's address saved in the frame: `Ctx` holds. -/
theorem save_ctx {E : Impl.Ecdsa.AArch64.Cfg} {I : Proof.Ecdsa.Rfc6979.Instance} {H : Hash} {f : Fns}
    {ns : List String} {s : State} (h : (rfcAArch64 E I (256 + 8 * 48) (tabFacts H f) ns).pre s) :
    WP isa (.block Impl.Ecdsa.Rfc6979.AArch64.Cfg.saveArgs) (entered s)
      (Ctx (lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s) s.gpr s.mem) := by
  have hL := lay_ok rfl h
  have hnB := hL.nB
  have he48 : (lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).e = 48 := rfl
  rw [he48] at hnB
  have hw : ∀ d, 16 ≤ d → d + 8 ≤ 624 →
      InRegions (entered s).wr ((lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).FR,
      by rw [entered_wr I.hashLen I.ecdsa.curve.len E H f]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩
  have w200 := hw 200 (by omega_arith) (by omega_arith)
  have w208 := hw 208 (by omega_arith) (by omega_arith)
  have w216 := hw 216 (by omega_arith) (by omega_arith)
  have w224 := hw 224 (by omega_arith) (by omega_arith)
  have w232 := hw 232 (by omega_arith) (by omega_arith)
  have w240 := hw 240 (by omega_arith) (by omega_arith)
  have w616 := hw 616 (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Impl.Ecdsa.Rfc6979.AArch64.Cfg.saveArgs, Impl.Ecdsa.Rfc6979.AArch64.fOut,
    Impl.Ecdsa.Rfc6979.AArch64.fD, Impl.Ecdsa.Rfc6979.AArch64.fDigest, Impl.Ecdsa.Rfc6979.AArch64.fScratch,
    Impl.Ecdsa.Rfc6979.AArch64.fDl, Impl.Ecdsa.Rfc6979.AArch64.fBl, Impl.Ecdsa.Rfc6979.AArch64.fTab,
    Impl.Ecdsa.Rfc6979.AArch64.extra,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read,
    Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    entered_sp I.hashLen I.ecdsa.curve.len E H f,
    Offset.add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w200, w208, w216, w224,
    w232, w240, w616, write8, Option.some.injEq, exists_eq_left', BitVec.add_zero, entered_gpr]
  obtain ⟨fr, k224, k216, k208, k200, k232, k240, k616⟩ := saved_ok (lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).B
    (entered s).mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7) (s.gpr .x5)
  rw [entered_mem I.hashLen I.ecdsa.curve.len E H f] at fr k224 k216 k208 k200 k232 k240 k616
  rw [entered_mem I.hashLen I.ecdsa.curve.len E H f]
  simp only [he48, Nat.reduceMul, Nat.reduceAdd] at fr k224 k216 k208 k200 k232 k240 k616 ⊢
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -, -, -, -, htf⟩ := h
  have hsep : ∀ x, x + 8 ≤ 248 ∨ (616 ≤ x ∧ x + 8 ≤ 624) → x + 8 ≤ 624 →
      ∀ r ∈ [(⟨(lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).B + BitVec.ofNat 64 200, 48⟩ : Region),
        ⟨(lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).B + BitVec.ofNat 64 616, 8⟩],
        Region.Disjoint ⟨(lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).B + BitVec.ofNat 64 624, 16⟩ r := by
    intro _ _ _ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨?_, ?_, rfl, ?_, k200, k208, k216, k224, k616, k232.trans htf.2.2.1, k240.trans htf.2.2.2, ?_, ?_, rfl,
    hT.1, htf.1, htf.2.1, ?_⟩
  · simp only [entered_rd]; rw [hrd]; rfl
  · rw [entered_wr I.hashLen I.ecdsa.curve.len E H f, hwr]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ _ (by intro e; subst e; simp [preserved] at hr), entered_gpr]
  · dsimp only
    simp only [he48, Nat.reduceMul, Nat.reduceAdd]
    rw [fr.readW (r := ⟨(lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).B + BitVec.ofNat 64 624, 16⟩)
      (Offset.contains (n := 64 / 8) _ (Nat.le_refl 624) (by omega_arith) (by omega_arith))
      (hsep 616 (.inr ⟨by omega_arith, by omega_arith⟩) (by omega_arith)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · refine Frame.trans (Frame.writeW (Frame.refl _ _) (r := (lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).STK)
      (by simp) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))) (Frame.sub fr fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact ⟨(lay I.hashLen I.ecdsa.curve.len E 48 rfl H f s).STK, by simp, Offset.sub_base _ (by omega_arith)⟩
  · intro n hn
    show s.syms n = (if n ∈ [H.hmacInitN, H.updN, H.hmacFinN] then s.syms n else 0)
    simp only [show n ∈ [H.hmacInitN, H.updN, H.hmacFinN] from hn, ite_true]

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-!
# Deterministic ECDSA on AArch64: addresses and registers

The code that sets one register to an address in `scratch` or the frame or
to a constant (`Upd`), the stack below `sp` the calls use, and the bytes of
a region a frame of writes misses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- The 16 bytes below the frame, which the calls use. -/
theorem below16 (B : Addr) : below (B + BitVec.ofNat 64 16) 16 = ⟨B, 16⟩ := by
  show (⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 16, 16⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-- A fact `simp` has reduced to `True`, or an equation of definitionally equal sides. -/
macro "atriv" : tactic => `(tactic| first | trivial | rfl)

theorem ne_cs {r d : Reg} (hr : r ∈ preserved) (hd : d ∉ preserved) : r ≠ d :=
  fun e => hd (e ▸ hr)

theorem not_pres {r : Reg} (hr : r ∈ preserved) (rs : List Reg) (h : ∀ q ∈ rs, q ∉ preserved) : r ∉ rs :=
  fun h' => h r h' hr

/-- The bytes of a region a frame of writes misses. -/
theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `p + d` does not wrap. -/
theorem toNat_add_of {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h]), Nat.mod_eq_of_lt h]

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The stack below `sp` a call with at most one frame uses: the 16 bytes below the frame. -/
theorem Ctx.below_eq {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem} {u : State}
    (hc : Ctx L g m₀ u) : below u.sp 16 = ⟨L.B, 16⟩ := by
  rw [hc.sp, below16]

/-- Code that writes no callee-saved register and calls nothing keeps them. -/
theorem WP.keepCs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => preserved.all fun r => !clobbers i r) = true)
    (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, Exec.sp he, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn)⟩
  have h₁ := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using h₁

/-- Code that keeps the permissions and the callee-saved registers, and
writes only safe regions, keeps `Ctx`. -/
theorem Ctx.of_keep {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem} (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {is : List Instr} {ws : List Region} {Q : State → Prop}
    (h : WP isa (.block is) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ Frame ws t.mem t'.mem ∧ Q t')
    (hk : (instrs (.block is : Prog isa)).all (fun i => preserved.all fun r => !clobbers i r) = true)
    (hs : ∀ r ∈ ws, Safe L r) :
    WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Frame ws t.mem t'.mem ∧ Q t' :=
  WP.mono_syms (WP.keepCs h hk rfl) fun _ ⟨⟨hrd, hwr, hf, hq⟩, hsp, hcs⟩ hsy =>
    ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hcs r hr) hf hs hsy, hf, hq⟩

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the register `d`, not callee-saved, (and the
flags) changed, to `v`. -/
structure Upd {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (g : Reg → BitVec 64) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 64)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hsp : u'.sp = u.sp)
    (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) (hsy : u'.syms = u.syms) : Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm hsp (fun r hr _ => hk r (ne_cs hr hd)) hsy

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {a : Nat}
    (ha : a < 4096) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.scr + BitVec.ofNat 64 a)) := by
  have h200 := hc.inFr (d := 200) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [Cfg.scr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, hc.sp, Offset.add_add, Nat.reduceAdd, Nat.reduceMod, Nat.reduceLT, and_self,
    h200, ite_true, Option.map_some, read8, hc.pScr, RegUpd.gpr_write_self, ha, Option.some.injEq,
    exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => ?_) rfl, rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]
  · rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]

/-- `d ← sp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {o : Nat}
    (ho : o < 4096) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.B + BitVec.ofNat 64 (16 + o))) := by
  apply WP.of_runBlock
  simp only [Cfg.fr, runBlock_cons, runStep_some, runBlock_nil, exec, ho, ite_true, hc.sp, Offset.add_add,
    Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

theorem movz_val {n : Nat} (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth Size.x.bits <<< (16 * 0) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  show n % 2 ^ 16 % 2 ^ 64 = n % 2 ^ 64
  omega_using [hn]

/-- `d ← n`. -/
theorem movz_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {n : Nat}
    (hn : n < 2 ^ 16) :
    WP isa (.block [.movz .x d (BitVec.ofNat 16 n) 0]) u (Upd L g m₀ u d (BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide, ite_true,
    movz_val hn, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-!
# Deterministic ECDSA on AArch64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, the bound on candidates), its
code and what the proofs of HMAC's functions know of it (`Hash`, `HashOK`,
`CoreOK`: HMAC's `init` and `finalize` and the streaming `update`, which the
table holds), the functions an indirect call of a table's functions may
reach (`f`, of which the table's are, `TabOK`, a fact of the state), and the
sizes the frame and `scratch` hold: the output and block sizes of one of the
hash functions of `shapes` (MD5's, SHA-1's or the SHA-2 family's), and
states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the frame holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK CoreOK core hmacInit_ok hmacFin_ok hmacInit_fdepth hmacFin_fdepth)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- The digest lengths and block sizes of the hash functions with HMAC on
AArch64: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on AArch64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.AArch64.Hash
  ok : HashOK H
  C : CoreOK (core H)
  satI : ∃ s, (Proof.Hmac.initScratchContract ok.SH H.W AArch64.abi 16).pre s
  satF : ∃ s, (Proof.Hmac.finalizeScratchContract ok.SH H.W AArch64.abi 16).pre s
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 16-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 16
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (H.D, H.P.B) ∈ shapes
  hS : H.S ≤ 192
  hW : 8 * H.W ≤ 1872
  hWb : ok.stream.Wb ≤ 1872

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

theorem hI : Verified AArch64.target P.H.hmacInit (initG P.ok.SH P.H.W) := hmacInit_ok P.ok P.C P.satI

theorem hId : P.H.hmacInit.aarch64Depth ≤ 1 := hmacInit_fdepth P.ok.stream.initDepth P.ok.comp.noFrames

theorem hF : Verified AArch64.target P.H.hmacFin (finG P.ok.SH P.H.W) := hmacFin_ok P.ok P.C P.satF

theorem hFd : P.H.hmacFin.aarch64Depth ≤ 1 := hmacFin_fdepth P.ok.stream.finDepth P.ok.comp.noFrames

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
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] <;> omega_using [this]

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
tactic_template "anums" : tactic => `(tactic| first | omega |
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

end VG.Proof.Ecdsa.Rfc6979.AArch64
