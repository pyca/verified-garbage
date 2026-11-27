module

public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Words
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MdStream.Arm
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Pbkdf2.Md.Arm.Compress`, which this module and modules that import it used -/

section

/-!
# A Merkle–Damgård compression function on ARMv7, called on one block

As on AArch64 (`Proof/Pbkdf2/AArch64/Iterate.lean`): the contract of a
compression function with blocks of any size `B` (`compK`, which is that of
the streaming proofs, `Proof/MdStream/Arm/Common.lean`, for any block size,
and each hash function's own, `Proof.Sha1.compressArm` and the others, at its
sizes), what its callers need of an implementation (`CompOk`: correct,
constant time, without calls, never writing `r0` or `r3`), and the call of it
on the block at `r6` (`compressBlock`), in one run (`compressBlock_ok`) and in
two (`compressBlock_rel`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm VG.Proof.MdStream
open VG.Impl.MdStream.Arm (compressAt compressWith)
open VG.Proof.MdStream.Arm (Upd wp_mov op2_imm op2_reg)

section
variable {B N L : Nat} (H : Md B N L) (so : Nat)

/-- The contract of the compression function: updates the `N`-byte hash
value at `r0` with the `r2` blocks of `B` bytes at `r1`, with scratch space
`r3` (`so` bytes). -/
def compK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), N⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), B * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + N ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + B * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + so ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem (State.addr (s.gpr .r0)) =
      H.compressBlocks (H.stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

/-- What a caller needs of an implementation of the compression function:
that it is correct and constant time, makes no calls, and never writes `r0`
or `r3`. -/
structure CompOk (code : Prog isa) : Prop where
  verified : ∀ s, (compK H so).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compK H so).post s s'
  ct : ConstantTime isa (compK H so).pre (compK H so).pub code
  noCalls : code.noCalls = true
  keeps : ((instrs code).all fun i => !clobbers i .r0 && !clobbers i .r3) = true

end

/-- The call of the compression function on the block at `r6`. -/
abbrev compressBlock (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .r1 (.reg .r6)]) (compressAt name code)

section
variable {B N L : Nat} {H : Md B N L} {so : Nat}

/-- What the call of the compression function on the block at `r6` (`src`),
into the hash value at `r0` (`st`), with scratch space at `r3` (`scr`),
needs. -/
structure CallOk (s : State) (N B so : Nat) (st scr src : BitVec 32) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  r6 : s.gpr .r6 = src
  f₀ : st.toNat + N ≤ 2 ^ 32
  f₁ : src.toNat + B ≤ 2 ^ 32
  f₃ : scr.toNat + so ≤ 2 ^ 32
  st_scr : Region.Disjoint ⟨State.addr st, N⟩ ⟨State.addr scr, so⟩
  src_st : Region.Disjoint ⟨State.addr src, B⟩ ⟨State.addr st, N⟩
  src_scr : Region.Disjoint ⟨State.addr src, B⟩ ⟨State.addr scr, so⟩
  cov : Covers [⟨State.addr src, B⟩, ⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] (s.rd ++ s.wr)
  covW : Covers [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] s.wr

/-- The state after the instructions that set up the call. -/
structure CSetup (s t : State) : Prop where
  r1 : t.gpr .r1 = s.gpr .r6
  r2 : t.gpr .r2 = 1
  other : ∀ r, r ≠ .r1 → r ≠ .r2 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem csetup_ok {name : String} {code : Prog isa} (s : State) {Q : State → Prop} (k : ∀ t, CSetup s t → WP isa (.call name code) t Q) :
    WP isa (compressBlock name code) s Q := by
  unfold compressBlock compressAt compressWith
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil (k s₂ ?_))
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr, fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

theorem one32 : (1 : BitVec 32).toNat = 1 := rfl

theorem call_pre {s t : State} {st scr src : BitVec 32} (h : CallOk s N B so st scr src) (hs : CSetup s t) :
    (compK H so).pre (t.callEntry.withRegions [⟨State.addr src, B⟩] [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩]) := by
  have c0 : t.callEntry.gpr .r0 = st :=
    (State.callEntry_gpr _ (by decide)).trans ((hs.other _ (by decide) (by decide)).trans h.r0)
  have c1 : t.callEntry.gpr .r1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.r1.trans h.r6)
  have c2 : t.callEntry.gpr .r2 = 1 := (State.callEntry_gpr _ (by decide)).trans hs.r2
  have c3 : t.callEntry.gpr .r3 = scr :=
    (State.callEntry_gpr _ (by decide)).trans ((hs.other _ (by decide) (by decide)).trans h.r3)
  simp only [compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1, c2, c3, one32,
    Nat.mul_one]
  exact ⟨trivial, trivial, h.st_scr, h.src_st, h.src_scr, h.f₀, h.f₁, h.f₃⟩

/-- Compressing the block at `r6` into the hash value at `r0`, with scratch
space at `r3`: the callee-saved registers other than `lr`, and `r0` and `r3`,
are kept. -/
theorem compressBlock_ok {name : String} {code : Prog isa} (hf : CompOk H so code) {s : State}
    {st scr src : BitVec 32} (h : CallOk s N B so st scr src) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] s.mem s'.mem →
      H.stateAt s'.mem (State.addr st) =
        H.compress (H.stateAt s.mem (State.addr st)) (H.blockAt s.mem (State.addr src)) → Q s') :
    WP isa (compressBlock name code) s Q := by
  have hk : ∀ i ∈ instrs code, clobbers i .r0 = false ∧ clobbers i .r3 = false := by
    intro i hi
    have := List.all_eq_true.mp hf.keeps i hi
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this
  refine csetup_ok s fun t hs => ?_
  refine WP.call (k := compK H so) hf.verified (call_pre h hs) ?_ ?_ ?_ hf.noCalls
  · rw [hs.rd, hs.wr]; simpa using h.cov
  · rw [hs.wr]; exact h.covW
  · intro s' hrd hwr hsp hfr hcs hg hpost
    have c0 : t.callEntry.gpr .r0 = st :=
      (State.callEntry_gpr _ (by decide)).trans ((hs.other _ (by decide) (by decide)).trans h.r0)
    have c1 : t.callEntry.gpr .r1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.r1.trans h.r6)
    have c2 : (t.callEntry.gpr .r2).toNat = 1 := by rw [State.callEntry_gpr _ (by decide), hs.r2]; rfl
    simp only [compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      hs.mem] at hpost
    rw [hs.mem] at hfr
    refine hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr hlr => ?_)
      (by rw [hg _ (fun i hi => (hk i hi).1) (by decide), hs.other _ (by decide) (by decide), h.r0])
      (by rw [hg _ (fun i hi => (hk i hi).2) (by decide), hs.other _ (by decide) (by decide), h.r3])
      (hsp.trans hs.sp) hfr ?_
    · have : r ≠ .r1 ∧ r ≠ .r2 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hcs r hr hlr, hs.other r this.1 this.2]
    · rw [hpost, Md.compressBlocks_one]

/-- `compressBlock` is constant time, in runs that call it on the same regions. -/
theorem compressBlock_rel {name : String} {code : Prog isa} (hf : CompOk H so code) {st scr src : BitVec 32}
    {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → CallOk s₁ N B so st scr src ∧ CallOk s₂ N B so st scr src) :
    RelCT isa P' (compressBlock name code) fun _ _ => True := by
  unfold compressBlock compressAt compressWith
  let M₁ : State → Prop := fun a => ∃ s, CallOk s N B so st scr src ∧ Upd s a .r1 (s.gpr .r6)
  let M₂ : State → Prop := fun b => ∃ s, CallOk s N B so st scr src ∧ CSetup s b
  have w₁ : ∀ s, CallOk s N B so st scr src → WP isa (.block [.mov .r1 (.reg .r6)]) s M₁ :=
    fun s h => wp_mov (op2_reg _ _) fun a u => WP.block_nil ⟨s, h, u⟩
  have w₂ : ∀ a, M₁ a → WP isa (.block [.mov .r2 (.imm 1)]) a M₂ := fun a ⟨s, h, u₁⟩ =>
    wp_mov (op2_imm (by decide)) fun b u₂ => WP.block_nil ⟨s, h, by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr,
      fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  have su₁ : RelCT isa P' (.block [.mov .r1 (.reg .r6)]) fun a b => M₁ a ∧ M₁ b :=
    ((RelCT.taint (A := taint) (P := P') (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by
      simp at hr) (by taint_decide)).wp fun s₁ s₂ hp => ⟨w₁ s₁ (hP s₁ s₂ hp).1, w₁ s₂ (hP s₁ s₂ hp).2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have su₂ : RelCT isa (fun a b => M₁ a ∧ M₁ b) (.block [.mov .r2 (.imm 1)]) fun a b => M₂ a ∧ M₂ b :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by
      simp at hr) (by taint_decide)).wp fun a b h => ⟨w₂ a h.1, w₂ b h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  refine su₁.seq (su₂.seq (RelCT.call (k := compK H so) hf.verified hf.ct [⟨State.addr src, B⟩]
    [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] fun t₁ t₂ ⟨⟨σ₁, c₁, h₁⟩, ⟨σ₂, c₂, h₂⟩⟩ => ?_))
  refine ⟨call_pre c₁ h₁, call_pre c₂ h₂, ?_, by rw [h₁.rd, h₁.wr]; simpa using c₁.cov, by rw [h₁.wr]; exact c₁.covW,
    by rw [h₂.rd, h₂.wr]; simpa using c₂.cov, by rw [h₂.wr]; exact c₂.covW⟩
  simp only [compK, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r1, h₂.r1, h₁.r2, h₂.r2, h₁.other .r0 (by decide) (by decide), h₂.other .r0 (by decide) (by decide),
    h₁.other .r3 (by decide) (by decide), h₂.other .r3 (by decide) (by decide), c₁.r0, c₂.r0, c₁.r3, c₂.r3,
    c₁.r6, c₂.r6]
  exact ⟨trivial, trivial, trivial, trivial⟩

end

end VG.Proof.Pbkdf2.Md.Arm

end

end

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on ARMv7: the hash function

As on AArch64 (`Proof/Pbkdf2/Md/AArch64/Hash.lean`), `HashOK H` is what the
proofs know of the hash function whose code `H` describes: it is a
Merkle–Damgård hash function `md` (`Md`) whose digest code does what it should
(`OutOk`) and whose length field for a `B + D`-byte message is the constant
words the code stores (`len`), with a verified compression function
(`CompOk`); its streaming functions are verified against the contracts HMAC's
generic proofs call them with (`stream`); its specification is `md` from the
initial hash value `iv` (a state represents a message as the specification
has it exactly when it does as `md` has it: `repr`, `back`), with the digest
the first `D` bytes of `md`'s; and
its sizes fit (`Sizes`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm

open VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash lenWords)
open Spec.Hmac (StreamingHash)

/-- The sizes the proofs support, checked for each hash function by
`decide`: words of 4 bytes, a digest of at most the hash value, room for the
padding in the block after the digest and after the hash value, the
streaming state as the hash value followed by a block, `finalize` writing
the whole hash value, and the compression function's scratch space within
the working space of the functions we call. -/
structure Sizes (H : Hash) : Prop where
  B : H.B = 64 ∨ H.B = 128
  N4 : H.N % 4 = 0
  D4 : H.D % 4 = 0
  L4 : H.L % 4 = 0
  D0 : 0 < H.D
  DN : H.D ≤ H.N
  NL : H.N + H.L ≤ H.B
  pad : H.D + 4 ≤ H.B - H.L
  N64 : H.N ≤ 64
  L16 : H.L ≤ 16
  so : H.so ≤ 8 * H.st.W
  W : H.st.W ≤ 64
  S : H.st.S = H.N + H.B
  F : H.st.F = H.N

namespace Sizes

variable {H : Hash} (hz : Sizes H)
include hz

/-! Facts about the sizes, each proved once for the many places that need it
(each an `omega` call of its own otherwise). -/

theorem B_range : 64 ≤ H.B ∧ H.B ≤ 128 := by
  rcases hz.B with h | h <;> rw [h] <;> decide

theorem B4 : H.B % 4 = 0 := by
  rcases hz.B with h | h <;> rw [h] <;> decide

theorem D_lt64 : H.D < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_trans hz.DN hz.N64) (by decide)

theorem D_le64 : H.D ≤ 2 ^ 64 := Nat.le_of_lt hz.D_lt64

theorem N_lt64 : H.N < 2 ^ 64 := Nat.lt_of_le_of_lt hz.N64 (by decide)

theorem B_lt64 : H.B < 2 ^ 64 := Nat.lt_of_le_of_lt hz.B_range.2 (by decide)

theorem NB_le64 : H.N + H.B ≤ 2 ^ 64 := Nat.le_trans (Nat.add_le_add hz.N64 hz.B_range.2) (by decide)

theorem BLD_lt64 : H.B - H.L - H.D < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) hz.B_lt64

theorem buf_le : 8 * H.st.W + 36 ≤ 8 * 64 + 36 := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hz.W) 36

theorem buf_le64 : 8 * H.st.W + 36 ≤ 2 ^ 64 := Nat.le_trans hz.buf_le (by decide)

theorem bufN_le64 : 8 * H.st.W + 36 + H.N ≤ 2 ^ 64 := Nat.le_trans (Nat.add_le_add hz.buf_le hz.N64) (by decide)

theorem bufNB_le64 : 8 * H.st.W + 36 + H.N + H.B ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add (Nat.add_le_add hz.buf_le hz.N64) hz.B_range.2) (by decide)

end Sizes

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the proofs see it. -/
  md : Md H.B H.N H.L
  out : OutOk md H.out
  /-- The compression function is verified. -/
  comp : CompOk md H.so H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : md.Reloc
  /-- The constant length field is that of a `B + D`-byte message. -/
  len : wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)
  /-- The streaming functions, verified. -/
  stream : Pbkdf2.Stream.Arm.HashOK H.st
  /-- The specification is `md` from `iv`, with a `D`-byte digest. -/
  iv : md.HV
  repr : ∀ mem p m, stream.SH.Repr mem p m → md.Repr iv mem p m
  back : ∀ mem p m, md.Repr iv mem p m → stream.SH.Repr mem p m
  hash : ∀ m, stream.SH.H.hash m = (md.hash iv m).take H.D
  sizes : Sizes H

namespace HashOK

variable {H : Hash} (hH : HashOK H)

/-- The specification. -/
abbrev SH : StreamingHash := hH.stream.SH

theorem hB : hH.SH.H.blockSize = H.B := hH.stream.hB
theorem hS : hH.SH.stateBytes = H.N + H.B := hH.stream.hS.trans hH.sizes.S
theorem hD : hH.SH.digestBytes = H.D := hH.stream.hD

include hH in
theorem B_le : H.B ≤ 128 := by rcases hH.sizes.B with h | h <;> omega_using [h]

include hH in
theorem B_ge : 64 ≤ H.B := by rcases hH.sizes.B with h | h <;> omega_using [h]

/-- The hash function of the specification is `md` from `iv`. -/
theorem link : hH.md.Link hH.SH hH.iv H.D :=
  ⟨hH.hB, hH.hS, hH.hD, hH.repr, hH.hash, hH.sizes.DN, by have := hH.sizes.pad; have := hH.sizes.NL; omega_arith⟩

theorem lenWords_length : (lenWords H.be H.L (H.B + H.D)).length = H.L / 4 := by simp [lenWords]

end HashOK

end VG.Proof.Pbkdf2.Md.Arm
