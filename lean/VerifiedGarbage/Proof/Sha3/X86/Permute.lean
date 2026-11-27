module

public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Sha3.Lanes
public import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.Sha3.X86.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Sha512.X86.Compress
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha3.Lanes
meta import VerifiedGarbage.Proof.Sha512.X86.Rounds
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Spec.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Impl.Sha3.X86.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

section

/-!
# SHA-3: the x86 (32-bit) contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`), with
the arguments on the stack (cdecl).

The streaming functions call the permutation, each call pushing its two
arguments and storing its return address in the 12 bytes of stack below
the return address; they may overwrite their own arguments (`writeArgs`),
which the code does not do.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open X86 in
/-- x86 (32-bit) contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read the arguments (8 bytes above the return address), and read
and write `state` (200 bytes) and `scratch` (512 bytes, whose contents on
exit are unspecified), which may not overlap each other, the arguments or
the return address, or wrap around the end of the (32-bit) address space.
`esp` and the pointers are public; the state is secret. -/
def permuteX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let scratch : Region := ⟨(arg s 1).setWidth 64, 512⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) = keccakF (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_absorb(state, rate, pos, data, len,
scratch) -> eax`, whose arguments are on the stack: absorbs `data` into the
streaming state (`Repr`) and returns the new position in the block.

The code may read `data` (`len` bytes), and read and write `state` (200
bytes), `scratch` (640 bytes) and the arguments (24 bytes above the return
address). None of these may overlap another; none of the buffers may
overlap the return address or the 12 bytes of stack below it; nothing may
wrap around the end of the (32-bit) address space. `rate` is one of
`rates`, and `pos < rate`. `esp` and the arguments are public; the state and
the data are secret. -/
def absorbX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat < (arg s 1).toNat
  post s s' :=
    (∀ msg, Repr s.mem ((arg s 0).setWidth 64) (arg s 1).toNat msg →
      (arg s 2).toNat = msg.length % (arg s 1).toNat →
      Repr s'.mem ((arg s 0).setWidth 64) (arg s 1).toNat
        (msg ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)) ∧
    (s'.gpr .eax).toNat = ((arg s 2).toNat + (arg s 4).toNat) % (arg s 1).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_pad(state, rate, pos, suffix,
scratch)`, whose arguments are on the stack: absorbs the padding (with the
low byte of `suffix`) into the streaming state.

The code may read and write `state` (200 bytes), `scratch` (640 bytes) and
the arguments (20 bytes above the return address). None of these may
overlap another; neither buffer may overlap the return address or the 12
bytes of stack below it; nothing may wrap around the end of the (32-bit)
address space. `rate` is one of `rates`, and `pos < rate`. `esp` and the
arguments are public; the state is secret. -/
def padX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat < (arg s 1).toNat
  post s s' := ∀ msg, Repr s.mem ((arg s 0).setWidth 64) (arg s 1).toNat msg →
    (arg s 2).toNat = msg.length % (arg s 1).toNat →
    stateAt s'.mem ((arg s 0).setWidth 64) =
      absorb (arg s 1).toNat (pad (arg s 1).toNat ((arg s 3).setWidth 8) msg)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_squeeze(state, rate, pos, out,
outlen, scratch) -> eax`, whose arguments are on the stack: writes `outlen`
bytes of output from byte `pos` on to `out`, and returns the position after
them, leaving a state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes),
`scratch` (640 bytes) and the arguments (24 bytes above the return address).
None of these may overlap another; none of the buffers may overlap the
return address or the 12 bytes of stack below it; nothing may wrap around
the end of the (32-bit) address space. `rate` is one of `rates`, and
`pos ≤ rate`. `esp` and the arguments are public; the state is secret. -/
def squeezeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let out : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat ≤ (arg s 1).toNat
  post s s' :=
    bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      squeezeFrom (arg s 1).toNat (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat
        (arg s 4).toNat ∧
    (s'.gpr .eax).toNat ≤ (arg s 1).toNat ∧
    ∀ d, squeezeFrom (arg s 1).toNat (stateAt s'.mem ((arg s 0).setWidth 64)) (s'.gpr .eax).toNat d =
      squeezeFrom (arg s 1).toNat (stateAt s.mem ((arg s 0).setWidth 64))
        ((arg s 2).toNat + (arg s 4).toNat) d
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Sha3

end

section

section

/-!
# SHA-3 on x86 (32-bit): single instructions

Weakest-precondition rules for the general registers' loads, stores and
operations with a memory operand, each proved once for any registers and
offsets, in continuation-passing style: the prologue, the epilogue and the
streaming functions use them. The 64-bit words in memory are those of the
SHA-512 proofs (`Proof/Sha512/X86/Rounds.lean`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha512.X86 (readSrc_mem wp_movS wp_xorS ea_of)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_store)

abbrev Lane := Spec.Sha3.Lane

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]` -/
theorem wp_ldm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b o)) :: rest)) s Q :=
  wp_movS (readSrc_mem hb hin) k

/-- `xor d, [b + o]` -/
theorem wp_xorm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: rest)) s Q :=
  wp_xorS (readSrc_mem hb hin) k

/-- `mov [b + o], r` -/
theorem wp_stm {b r : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B) (hout : InRegions s.wr (addr B o) 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) (s.gpr r)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.store (at_ b o) r :: rest)) s Q :=
  wp_store (ea_of hb o) hout k

/-- The two words of a 64-bit word at `[B + o]` are writable. -/
def Wr2 (s : State) (B : BitVec 32) (o : Nat) : Prop :=
  InRegions s.wr (addr B o) 4 ∧ InRegions s.wr (addr B (o + 4)) 4

end

end VG.Proof.Sha3.X86

end

/-!
# Keccak-f[1600] on x86 (32-bit): one round

One round (`round p src dst`) from the state at `src` to the state at `dst`
(`src`, `dst` being `esi`, `edi` or `edi`, `esi`), with the registers of the
plan `p`.

A round's lanes are straight-line code on the XMM registers' low quadwords
and on words of memory: the lanes of the two states, the five `D` and the
round constant. Which register holds what, and when, is the plan's, so the
proof does not follow the code by hand: it runs it on *expressions*
(`Run.Ex`) in the lanes of the state at `src`, the round constant and what
the registers held. `Run.step` is what an instruction does to the
expressions of the registers and of the words written so far (`Run.Sym`); it
refuses an instruction or an address the rounds do not use, and it is sound
for the model (`Run.step_ok`): if it accepts an instruction, the instruction
runs, and the registers and those words then hold the values of their new
expressions (`Run.Rel`). So a run of a round's code (`Run.run`,
`Run.run_ok`) says what the state at `dst` holds. `Run.check p src dst`,
which the kernel evaluates for each round of an iteration (`planA_ok`,
`planB_ok`, below), is that the code runs and leaves each lane of the state
at `dst` holding the expression `Run.refOut` of it, the same whatever the
plan: the round of the specification, lane by lane (`Run.refOut_eval`,
`Proof.Sha3.out`). A plan that took a register still in use, or any other
code, would leave another expression somewhere and fail the check.
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86 VG.Impl.Sha3.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha512.X86 (rd64 write64 mem_rd qword_append_0 q_pxor q_psllq q_psrlq rd64_eq_readW
  readW64_write_ne)
open VG.Proof.Sha256.X86.Stream (Upd wp_addi contains_addr)
open VG.Proof.Sha3 (C D B out outState rotl rotl_eq rhoOff_lt rotateLeft_zero)

abbrev KState := Spec.Sha3.State

/-! ## Regions -/

theorem addr_zero (b : BitVec 32) : addr b 0 = b.setWidth 64 := by simp [addr]

/-- The `n` bytes at offset `o` of a region at `b` are within its part at offset `a`. -/
theorem sub_contains {b : BitVec 32} {N a k o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hak : a + k ≤ N)
    (h1 : a ≤ o) (h2 : o + n ≤ a + k) (hn : 0 < n) : (⟨addr b a, k⟩ : Region).Contains (addr b o) n := by
  simp only [Region.Contains]
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith)]
  obtain hE : (b.setWidth 64).toNat = b.toNat := VG.Proof.Sha256.X86.Stream.addr_toNat b
  generalize b.setWidth 64 = E at *
  bv_omega

/-- Two parts of a region at `b` that do not overlap. -/
theorem sub_disj {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ha : a + n ≤ N)
    (hc : c + k ≤ N) (hn : 0 < n) (hk : 0 < k) (h : a + n ≤ c ∨ c + k ≤ a) :
    Region.Disjoint ⟨addr b a, n⟩ ⟨addr b c, k⟩ := by
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith)]
  exact Proof.Sha3.off_disjoint _ (by omega_arith) (by omega_arith) h

/-- The region of `n` bytes at a 32-bit pointer. -/
abbrev reg32 (b : BitVec 32) (n : Nat) : Region := ⟨b.setWidth 64, n⟩

/-- The part of the scratch space at `W` that a round writes besides a
state: within it, the five `D`. -/
abbrev workR (W : BitVec 32) : Region := ⟨addr W 408, 80⟩

theorem Frame.write64' {rs : List Region} {m m' : Mem} (h : Frame rs m m') {R : Region} (hr : R ∈ rs)
    {b : BitVec 32} {o : Nat} (hc0 : R.Contains (addr b o) 4) (hc4 : R.Contains (addr b (o + 4)) 4)
    (v : Lane) : Frame rs m (write64 m' b o v) :=
  (h.writeW hr _ hc0).writeW hr _ hc4

/-- A 64-bit word in a region, after one is written in another. -/
theorem readW_writeW_regions (m : Mem) {R R' : Region} {a a' : Addr} (v : BitVec 64)
    (hc : R.Contains a 8) (hc' : R'.Contains a' 8) (hd : R'.Disjoint R) :
    (m.writeW a v).readW a' 64 = m.readW a' 64 :=
  ((Frame.refl [R] m).writeW (List.mem_singleton_self R) v hc).readW hc'
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)

/-! ## States in memory -/

/-- The state at `b` holds `K`, lane `i` as the 64-bit word at `b + 8i`. -/
def Lanes32 (m : Mem) (b : BitVec 32) (K : KState) : Prop := ∀ i < 25, rd64 m b (8 * i) = K[i]!

/-- Every 8 bytes `[B + o, B + o + 8)` with `o + 8 ≤ N` are writable. -/
def Acc8 (wr : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 8 ≤ N → InRegions wr (addr B o) 8

theorem Acc8.of_mem {wr : List Region} {B : BitVec 32} {N : Nat} (h : ⟨B.setWidth 64, N⟩ ∈ wr)
    (hfit : B.toNat + N ≤ 2 ^ 32) : Acc8 wr B N :=
  fun _ ho => ⟨_, h, contains_addr ho (by omega_arith) hfit⟩

/-- Where a round reads and writes: the state at `S`, the scratch space at
`W` (its `D`), the round constant at `P`, and the state at `Dd`, which
overlaps none of the others. -/
structure Env (wr : List Region) (S Dd W P : BitVec 32) : Prop where
  fitS : S.toNat + 200 ≤ 2 ^ 32
  fitD : Dd.toNat + 200 ≤ 2 ^ 32
  fitW : W.toNat + 512 ≤ 2 ^ 32
  fitP : P.toNat + 8 ≤ 2 ^ 32
  accS : Acc8 wr S 200
  accD : Acc8 wr Dd 200
  accW : Acc8 wr W 512
  accP : Acc8 wr P 8
  sd : (reg32 S 200).Disjoint (reg32 Dd 200)
  sw : (reg32 S 200).Disjoint (workR W)
  dw : (reg32 Dd 200).Disjoint (workR W)
  pd : (reg32 P 8).Disjoint (reg32 Dd 200)
  pw : (reg32 P 8).Disjoint (workR W)

/-! ## Expressions -/

namespace Run

/-- What a register's low quadword or a word of memory holds in a round, from
what the round starts with. -/
inductive Ex
  /-- Lane `i` of the state at `src`. -/
  | lane (i : Nat)
  /-- The round constant. -/
  | rc
  /-- What the register held. -/
  | junk (r : XReg)
  | xor (a b : Ex)
  /-- `¬a ∧ b` -/
  | andn (a b : Ex)
  | or (a b : Ex)
  | shl (a : Ex) (n : Nat)
  | shr (a : Ex) (n : Nat)
  deriving DecidableEq

/-- An expression's value, with the state `K` at `src`, the round constant
`rc`, and the registers holding `J`. -/
def Ex.eval (K : KState) (rc : Lane) (J : XReg → Lane) : Ex → Lane
  | .lane i => K[i]!
  | .rc => rc
  | .junk r => J r
  | .xor a b => a.eval K rc J ^^^ b.eval K rc J
  | .andn a b => ~~~(a.eval K rc J) &&& b.eval K rc J
  | .or a b => a.eval K rc J ||| b.eval K rc J
  | .shl a n => a.eval K rc J <<< n
  | .shr a n => a.eval K rc J >>> n

/-- The expressions of the eight registers. -/
structure Regs where
  x0 : Ex
  x1 : Ex
  x2 : Ex
  x3 : Ex
  x4 : Ex
  x5 : Ex
  x6 : Ex
  x7 : Ex

def Regs.get : Regs → XReg → Ex
  | ⟨a, _, _, _, _, _, _, _⟩, .xmm0 => a
  | ⟨_, a, _, _, _, _, _, _⟩, .xmm1 => a
  | ⟨_, _, a, _, _, _, _, _⟩, .xmm2 => a
  | ⟨_, _, _, a, _, _, _, _⟩, .xmm3 => a
  | ⟨_, _, _, _, a, _, _, _⟩, .xmm4 => a
  | ⟨_, _, _, _, _, a, _, _⟩, .xmm5 => a
  | ⟨_, _, _, _, _, _, a, _⟩, .xmm6 => a
  | ⟨_, _, _, _, _, _, _, a⟩, .xmm7 => a

def Regs.set : Regs → XReg → Ex → Regs
  | ⟨_, b, c, d, e, f, g, h⟩, .xmm0, v => ⟨v, b, c, d, e, f, g, h⟩
  | ⟨a, _, c, d, e, f, g, h⟩, .xmm1, v => ⟨a, v, c, d, e, f, g, h⟩
  | ⟨a, b, _, d, e, f, g, h⟩, .xmm2, v => ⟨a, b, v, d, e, f, g, h⟩
  | ⟨a, b, c, _, e, f, g, h⟩, .xmm3, v => ⟨a, b, c, v, e, f, g, h⟩
  | ⟨a, b, c, d, _, f, g, h⟩, .xmm4, v => ⟨a, b, c, d, v, f, g, h⟩
  | ⟨a, b, c, d, e, _, g, h⟩, .xmm5, v => ⟨a, b, c, d, e, v, g, h⟩
  | ⟨a, b, c, d, e, f, _, h⟩, .xmm6, v => ⟨a, b, c, d, e, f, v, h⟩
  | ⟨a, b, c, d, e, f, g, _⟩, .xmm7, v => ⟨a, b, c, d, e, f, g, v⟩

theorem Regs.get_set (ρ : Regs) (r r' : XReg) (v : Ex) :
    (ρ.set r v).get r' = if r' = r then v else ρ.get r' := by
  cases ρ; cases r <;> cases r' <;> rfl

/-- The registers' expressions, and those of the words written so far, by
their offsets (the latest first): a lane of the state at `dst` (an offset
under 200), or a `D` (an offset in the scratch space). -/
structure Sym where
  regs : Regs
  mem : List (Nat × Ex)

/-- The expression of the word at offset `o`, if it was written. -/
def look (o : Nat) : List (Nat × Ex) → Option Ex
  | [] => none
  | (k, e) :: l => if k = o then some e else look o l

/-- The offset of a lane of a state. -/
def isLane (o : Nat) : Bool := decide (o < 200) && decide (o % 8 = 0)

/-- The offset in the scratch space of a `D`. -/
def isD (o : Nat) : Bool := decide (448 ≤ o) && decide (o < 488) && decide (o % 8 = 0)

theorem isLane_iff {o : Nat} : isLane o = true ↔ o < 200 ∧ o % 8 = 0 := by simp [isLane]

theorem isD_iff {o : Nat} : isD o = true ↔ 448 ≤ o ∧ o < 488 ∧ o % 8 = 0 := by simp [isD, and_assoc]

/-- What a load from `m` gives: the round constant (`[ebp]`), a `D` that was
stored, or a lane of the state at `src`. -/
def ldEx (src : Reg) (σ : Sym) (m : MemOp) : Option Ex :=
  if m.base = .ebp ∧ m.disp = 0 then some .rc
  else if m.base = .edi ∧ isD m.disp = true then look m.disp σ.mem
  else if m.base = src ∧ isLane m.disp = true then some (.lane (m.disp / 8))
  else none

/-- A store to `m` is of a lane of the state at `dst` or of a `D`. -/
def stOk (dst : Reg) (m : MemOp) : Bool :=
  decide (m.base = dst) && isLane m.disp || decide (m.base = .edi) && isD m.disp

/-- What an instruction of a round's lanes does to the expressions; `none`
for any other instruction or address. -/
def step (src dst : Reg) (σ : Sym) : Instr → Option Sym
  | .movqLoad d m => (ldEx src σ m).map fun e => ⟨σ.regs.set d e, σ.mem⟩
  | .movqStore m r => if stOk dst m = true then some ⟨σ.regs, (m.disp, σ.regs.get r) :: σ.mem⟩ else none
  | .xop (.bin .movdqa a b) => some ⟨σ.regs.set a (σ.regs.get b), σ.mem⟩
  | .xop (.bin .pxor a b) => some ⟨σ.regs.set a (.xor (σ.regs.get a) (σ.regs.get b)), σ.mem⟩
  | .xop (.bin .por a b) => some ⟨σ.regs.set a (.or (σ.regs.get a) (σ.regs.get b)), σ.mem⟩
  | .xop (.bin .pandn a b) => some ⟨σ.regs.set a (.andn (σ.regs.get a) (σ.regs.get b)), σ.mem⟩
  | .xop (.shift .psllq r n) =>
    if n.toNat ≤ 63 then some ⟨σ.regs.set r (.shl (σ.regs.get r) n.toNat), σ.mem⟩ else none
  | .xop (.shift .psrlq r n) =>
    if n.toNat ≤ 63 then some ⟨σ.regs.set r (.shr (σ.regs.get r) n.toNat), σ.mem⟩ else none
  | _ => none

/-- The expressions after a block. -/
def run (src dst : Reg) : Sym → List Instr → Option Sym
  | σ, [] => some σ
  | σ, i :: is =>
    match step src dst σ i with
    | some σ' => run src dst σ' is
    | none => none

/-- Before a round: the registers hold what they hold, and nothing is written. -/
def sym₀ : Sym :=
  ⟨⟨.junk .xmm0, .junk .xmm1, .junk .xmm2, .junk .xmm3, .junk .xmm4, .junk .xmm5, .junk .xmm6, .junk .xmm7⟩, []⟩

/-! ## The round's expressions -/

/-- `C[x]`, as the code computes it. -/
def refC (x : Nat) : Ex :=
  .xor (.xor (.xor (.xor (.lane x) (.lane (x + 5))) (.lane (x + 10))) (.lane (x + 15))) (.lane (x + 20))

/-- A rotation left by `n`, as `rol` computes it. -/
def refRol (e : Ex) (n : Nat) : Ex := if n = 0 then e else .or (.shl e n) (.shr e (64 - n))

def refD (x : Nat) : Ex := .xor (refRol (refC ((x + 1) % 5)) 1) (refC ((x + 4) % 5))

def refB (x y : Nat) : Ex :=
  refRol (.xor (.lane (piSrc x y)) (refD ((x + 3 * y) % 5))) (rhoOff (piSrc x y))

/-- Lane `(x, y)` of the round's output. -/
def refOut (x y : Nat) : Ex :=
  if x = 0 ∧ y = 0 then .xor (.xor (.andn (refB ((x + 1) % 5) y) (refB ((x + 2) % 5) y)) (refB x y)) .rc
  else .xor (.andn (refB ((x + 1) % 5) y) (refB ((x + 2) % 5) y)) (refB x y)

section
variable (K : KState) (rc : Lane) (J : XReg → Lane)

theorem refC_eval (x : Nat) : (refC x).eval K rc J = C K x := rfl

theorem refRol_eval (e : Ex) {n : Nat} (hn : n < 64) :
    (refRol e n).eval K rc J = rotl (e.eval K rc J) n := by
  rw [rotl_eq _ hn]
  unfold refRol
  split
  · subst_vars; rw [rotateLeft_zero]
  · show e.eval K rc J <<< n ||| e.eval K rc J >>> (64 - n) = _
    rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]

theorem refD_eval (x : Nat) : (refD x).eval K rc J = D K x := by
  show (refRol (refC ((x + 1) % 5)) 1).eval K rc J ^^^ (refC ((x + 4) % 5)).eval K rc J = _
  rw [refRol_eval K rc J _ (by decide), refC_eval, refC_eval]
  rfl

theorem refB_eval {x y : Nat} (hx : x < 5) (hy : y < 5) : (refB x y).eval K rc J = B K x y := by
  unfold refB
  rw [refRol_eval K rc J _ (rhoOff_lt _ (by simp only [piSrc]; omega_using [hx, hy]))]
  show rotl (K[piSrc x y]! ^^^ (refD ((x + 3 * y) % 5)).eval K rc J) _ = _
  rw [refD_eval]
  rfl

theorem refOut_eval {x y : Nat} (hx : x < 5) (hy : y < 5) : (refOut x y).eval K rc J = out K rc x y := by
  obtain e : ∀ b : Lane, b ^^^ 0xffffffffffffffff = ~~~b := fun b => by
    rw [show (0xffffffffffffffff : Lane) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]
  rw [show out K rc x y = if x = 0 ∧ y = 0 then
      ((B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^ B K x y) ^^^ rc
    else (B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^ B K x y from rfl]
  unfold refOut
  by_cases hc : x = 0 ∧ y = 0
  · rw [ite_eq_left hc, ite_eq_left hc]
    show (~~~((refB ((x + 1) % 5) y).eval K rc J) &&& (refB ((x + 2) % 5) y).eval K rc J ^^^
      (refB x y).eval K rc J) ^^^ rc = _
    rw [refB_eval K rc J (Nat.mod_lt _ (by decide)) hy, refB_eval K rc J (Nat.mod_lt _ (by decide)) hy,
      refB_eval K rc J hx hy, e]
  · rw [ite_eq_right hc, ite_eq_right hc]
    show ~~~((refB ((x + 1) % 5) y).eval K rc J) &&& (refB ((x + 2) % 5) y).eval K rc J ^^^
      (refB x y).eval K rc J = _
    rw [refB_eval K rc J (Nat.mod_lt _ (by decide)) hy, refB_eval K rc J (Nat.mod_lt _ (by decide)) hy,
      refB_eval K rc J hx hy, e]

end

/-- Every lane of the state at `dst` was written, with the round's expression. -/
def outsOk (σ : Sym) : Bool :=
  (List.range 25).all fun i => decide (look (8 * i) σ.mem = some (refOut (i % 5) (i / 5)))

/-- The lanes of a round with the plan `p` run, and leave the round's output
in the state at `dst`. -/
def check (p : List XReg) (src dst : Reg) : Bool :=
  match run src dst sym₀ (lanes p src dst) with
  | some σ => outsOk σ
  | none => false

/-! ## The expressions and the model -/

/-- The registers' low quadwords. -/
abbrev low (s : State) : XReg → Lane := fun r => qword (s.xmm r) 0

/-- Where the word of offset `o` is: in the state at `Dd`, or in the scratch
space at `W`. -/
def cad (Dd W : BitVec 32) (o : Nat) : Addr := if o < 200 then addr Dd o else addr W o

/-- The state `s`, in a round that started in `s₁` with `K` at `src` and
the round constant `rc`, holds what `σ` says. -/
structure Rel (Dd W : BitVec 32) (K : KState) (rc : Lane) (s₁ : State) (σ : Sym) (s : State) : Prop where
  regs : ∀ r, qword (s.xmm r) 0 = (σ.regs.get r).eval K rc (low s₁)
  mem : ∀ o e, look o σ.mem = some e →
    (isLane o = true ∨ isD o = true) ∧ s.mem.readW (cad Dd W o) 64 = e.eval K rc (low s₁)
  frame : Frame [reg32 Dd 200, workR W] s₁.mem s.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem q_por (a b : BitVec 128) : qword (XBinOp.eval .por a b) 0 = qword a 0 ||| qword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hi, decide_true,
    Bool.true_and]

theorem q_pandn (a b : BitVec 128) : qword (XBinOp.eval .pandn a b) 0 = ~~~qword a 0 &&& qword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and, show 64 * 0 + i < 128 by omega_using [hi]]

section
variable {src dst : Reg} {S Dd W P : BitVec 32} {K : KState} {rc : Lane} {s₁ : State}

theorem Rel.init : Rel Dd W K rc s₁ sym₀ s₁ :=
  ⟨fun r => by cases r <;> rfl, fun _ _ h => by simp [sym₀, look] at h, Frame.refl _ _, rfl, rfl, rfl⟩

/-- A register written. -/
theorem Rel.setX {σ : Sym} {s : State} (h : Rel Dd W K rc s₁ σ s) (d : XReg) {v : BitVec 128} {e : Ex}
    (hv : qword v 0 = e.eval K rc (low s₁)) :
    Rel Dd W K rc s₁ ⟨σ.regs.set d e, σ.mem⟩ (s.setXmm d v) where
  regs r := by
    rw [VG.X86.RegUpd.xmm_setXmm, Regs.get_set]
    split
    · exact hv
    · exact h.regs r
  mem := h.mem
  frame := h.frame
  gpr := h.gpr
  rd := h.rd
  wr := h.wr

/-- A register loaded from memory. -/
theorem Rel.load {σ : Sym} {s : State} (h : Rel Dd W K rc s₁ σ s) (d : XReg) {m : MemOp} {e : Ex}
    (hin : InRegions s.wr (s.ea m) 8) (hv : s.mem.readW (s.ea m) 64 = e.eval K rc (low s₁)) :
    ∃ s', isa.exec (.movqLoad d m) s = some s' ∧ Rel Dd W K rc s₁ ⟨σ.regs.set d e, σ.mem⟩ s' := by
  refine ⟨s.setXmm d ((0 : BitVec 64) ++ s.mem.readW (s.ea m) 64), ?_, h.setX d (by rw [qword_append_0, hv])⟩
  show (s.load64 (s.ea m)).map _ = _
  rw [State.load64, ite_eq_left (mem_rd hin)]
  rfl

theorem cad_lane {o : Nat} (h : isLane o = true) : cad Dd W o = addr Dd o :=
  ite_eq_left (isLane_iff.mp h).1

theorem cad_d {o : Nat} (h : isD o = true) : cad Dd W o = addr W o :=
  ite_eq_right (by have := (isD_iff.mp h).1; omega_using [this])

section
variable (E : Env s₁.wr S Dd W P)
include E

theorem cad_in {o : Nat} (ho : isLane o = true ∨ isD o = true) :
    ∃ R ∈ [reg32 Dd 200, workR W], R.Contains (cad Dd W o) 8 := by
  rcases ho with ho | ho
  · obtain ⟨h1, h2⟩ := isLane_iff.mp ho
    refine ⟨_, List.mem_cons_self, ?_⟩
    rw [cad_lane ho]
    exact contains_addr (by omega_using [h1, h2]) (by decide) E.fitD
  · obtain ⟨h1, h2, h3⟩ := isD_iff.mp ho
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rw [cad_d ho]
    exact sub_contains E.fitW (by decide) (by omega_using [h1]) (by omega_using [h2, h3]) (by decide)

theorem cad_acc {o : Nat} (ho : isLane o = true ∨ isD o = true) : InRegions s₁.wr (cad Dd W o) 8 := by
  rcases ho with ho | ho
  · obtain ⟨h1, h2⟩ := isLane_iff.mp ho
    rw [cad_lane ho]
    exact E.accD _ (by omega_using [h1, h2])
  · obtain ⟨h1, h2, h3⟩ := isD_iff.mp ho
    rw [cad_d ho]
    exact E.accW _ (by omega_using [h2, h3])

/-- A word of a round, after another is written. -/
theorem cad_sep {o o₀ : Nat} (ho : isLane o = true ∨ isD o = true) (ho₀ : isLane o₀ = true ∨ isD o₀ = true)
    (hne : o₀ ≠ o) (m : Mem) (v : BitVec 64) :
    (m.writeW (cad Dd W o₀) v).readW (cad Dd W o) 64 = m.readW (cad Dd W o) 64 := by
  have fD := E.fitD
  have fW := E.fitW
  rcases ho with ho | ho <;> rcases ho₀ with ho₀ | ho₀
  · obtain ⟨h1, h2⟩ := isLane_iff.mp ho
    obtain ⟨k1, k2⟩ := isLane_iff.mp ho₀
    rw [cad_lane ho, cad_lane ho₀]
    exact readW64_write_ne _ _ (by omega_using [fD, k1, k2]) (by omega_using [fD, h1, h2])
      (by omega_using [h2, k2, hne])
  · obtain ⟨h1, h2⟩ := isLane_iff.mp ho
    obtain ⟨k1, k2, k3⟩ := isD_iff.mp ho₀
    rw [cad_lane ho, cad_d ho₀]
    exact readW_writeW_regions _ _
      (sub_contains fW (by decide) (by omega_using [k1]) (by omega_using [k2, k3]) (by decide))
      (contains_addr (by omega_using [h1, h2]) (by decide) fD) E.dw
  · obtain ⟨h1, h2, h3⟩ := isD_iff.mp ho
    obtain ⟨k1, k2⟩ := isLane_iff.mp ho₀
    rw [cad_d ho, cad_lane ho₀]
    exact readW_writeW_regions _ _ (contains_addr (by omega_using [k1, k2]) (by decide) fD)
      (sub_contains fW (by decide) (by omega_using [h1]) (by omega_using [h2, h3]) (by decide)) E.dw.symm
  · obtain ⟨h1, h2, h3⟩ := isD_iff.mp ho
    obtain ⟨k1, k2, k3⟩ := isD_iff.mp ho₀
    rw [cad_d ho, cad_d ho₀]
    exact readW64_write_ne _ _ (by omega_using [fW, k2, k3]) (by omega_using [fW, h2, h3])
      (by omega_using [h3, k3, hne])

/-- A register stored. -/
theorem Rel.store {σ : Sym} {s : State} (h : Rel Dd W K rc s₁ σ s) (r : XReg) {m : MemOp}
    (ho : isLane m.disp = true ∨ isD m.disp = true) (hea : s.ea m = cad Dd W m.disp) :
    ∃ s', isa.exec (.movqStore m r) s = some s' ∧
      Rel Dd W K rc s₁ ⟨σ.regs, (m.disp, σ.regs.get r) :: σ.mem⟩ s' := by
  obtain ⟨R, hR, hc⟩ := cad_in E ho
  refine ⟨{ s with mem := s.mem.writeW (cad Dd W m.disp) (qword (s.xmm r) 0) }, ?_, fun x => h.regs x,
    fun o e he => ?_, h.frame.writeW hR _ hc, h.gpr, h.rd, h.wr⟩
  · show s.store64 (s.ea m) ((s.xmm r).extractLsb' 0 64) = _
    rw [State.store64, hea, ite_eq_left (h.wr ▸ cad_acc E ho)]
    rfl
  · show _ ∧ (s.mem.writeW (cad Dd W m.disp) (qword (s.xmm r) 0)).readW (cad Dd W o) 64 = _
    change look o ((m.disp, σ.regs.get r) :: σ.mem) = some e at he
    rw [look] at he
    split at he
    · rename_i hk
      cases he
      subst hk
      exact ⟨ho, by rw [Mem.readW_writeW_self64, h.regs r]⟩
    · rename_i hk
      obtain ⟨hv, hr⟩ := h.mem o e he
      exact ⟨hv, by rw [cad_sep E hv ho hk, hr]⟩

end

section
variable (E : Env s₁.wr S Dd W P) (hS : s₁.gpr src = S) (hD : s₁.gpr dst = Dd) (hW : s₁.gpr .edi = W)
  (hP : s₁.gpr .ebp = P) (hK : Lanes32 s₁.mem S K) (hrc : rd64 s₁.mem P 0 = rc)
include E hS hW hP hK hrc

/-- What a load reads. -/
theorem ldEx_ok {σ : Sym} {s : State} (h : Rel Dd W K rc s₁ σ s) {m : MemOp} {e : Ex}
    (he : ldEx src σ m = some e) :
    InRegions s.wr (s.ea m) 8 ∧ s.mem.readW (s.ea m) 64 = e.eval K rc (low s₁) := by
  obtain hea : s.ea m = addr (s₁.gpr m.base) m.disp := by rw [← h.gpr]; rfl
  unfold ldEx at he
  split at he
  · rename_i hm
    cases he
    rw [hea, hm.1, hm.2, hP, h.wr]
    refine ⟨E.accP 0 (by decide), ?_⟩
    rw [h.frame.readW (r := reg32 P 8) (contains_addr (by decide) (by decide) E.fitP) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> [exact E.pd; exact E.pw]) (by decide),
      ← rd64_eq_readW _ (by omega_using [E.fitP]), hrc]
    rfl
  · split at he
    · rename_i hm
      obtain ⟨h1, h2, h3⟩ := isD_iff.mp hm.2
      obtain ⟨_, hr⟩ := h.mem _ _ he
      rw [cad_d hm.2] at hr
      rw [hea, hm.1, hW, h.wr]
      exact ⟨E.accW _ (by omega_using [h2, h3]), hr⟩
    · split at he <;> [skip; cases he]
      rename_i hm
      cases he
      obtain ⟨h1, h2⟩ := isLane_iff.mp hm.2
      have fS := E.fitS
      rw [hea, hm.1, hS, h.wr]
      refine ⟨E.accS _ (by omega_using [h1, h2]), ?_⟩
      rw [h.frame.readW (r := reg32 S 200) (contains_addr (by omega_using [h1, h2]) (by decide) fS)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> [exact E.sd; exact E.sw]) (by decide),
        ← rd64_eq_readW _ (by omega_using [fS, h1, h2])]
      have hk := hK (m.disp / 8) (by omega_using [h1])
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)] at hk
      exact hk

include hD

/-- `step` is sound: an instruction it accepts runs, and what it says of
the registers and of the words written holds after it. -/
theorem step_ok {σ σ' : Sym} {i : Instr} {s : State} (hs : step src dst σ i = some σ')
    (h : Rel Dd W K rc s₁ σ s) : ∃ s', isa.exec i s = some s' ∧ Rel Dd W K rc s₁ σ' s' := by
  unfold step at hs
  split at hs
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨hin, hv⟩ := ldEx_ok E hS hW hP hK hrc h he
    exact h.load _ hin hv
  · split at hs <;> [skip; cases hs]
    rename_i m r hok
    cases hs
    obtain hea : s.ea m = addr (s₁.gpr m.base) m.disp := by rw [← h.gpr]; rfl
    simp only [stOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨hb, ho⟩ | ⟨hb, ho⟩
    · exact h.store E r (.inl ho) (by rw [hea, hb, hD, cad_lane ho])
    · exact h.store E r (.inr ho) (by rw [hea, hb, hW, cad_d ho])
  · cases hs
    exact ⟨_, rfl, h.setX _ (h.regs _)⟩
  · cases hs
    exact ⟨_, rfl, h.setX _ (by rw [q_pxor, h.regs, h.regs]; rfl)⟩
  · cases hs
    exact ⟨_, rfl, h.setX _ (by rw [q_por, h.regs, h.regs]; rfl)⟩
  · cases hs
    exact ⟨_, rfl, h.setX _ (by rw [q_pandn, h.regs, h.regs]; rfl)⟩
  · split at hs <;> [skip; cases hs]
    rename_i hn
    cases hs
    exact ⟨_, rfl, h.setX _ (by rw [q_psllq, ite_eq_right (Nat.not_lt.mpr hn), h.regs]; rfl)⟩
  · split at hs <;> [skip; cases hs]
    rename_i hn
    cases hs
    exact ⟨_, rfl, h.setX _ (by rw [q_psrlq, ite_eq_right (Nat.not_lt.mpr hn), h.regs]; rfl)⟩
  · cases hs

/-- A block that `run` accepts runs, to a state that holds what it says. -/
theorem run_ok : ∀ (is : List Instr) {σ σ' : Sym} {s : State}, run src dst σ is = some σ' →
    Rel Dd W K rc s₁ σ s → WP isa (.block is) s (Rel Dd W K rc s₁ σ')
  | [], _, _, _, hr, h => by cases hr; exact WP.block_nil h
  | i :: is, σ, σ', s, hr, h => by
    unfold run at hr
    split at hr <;> [skip; cases hr]
    rename_i σ₂ hs
    obtain ⟨s', he, h'⟩ := step_ok E hS hD hW hP hK hrc hs h
    exact WP.block_cons_iff.mpr ⟨s', he, run_ok is hr h'⟩

end

end

end Run

/-! ## The round -/

theorem round_ok {p : List XReg} {src dst : Reg} (hck : Run.check p src dst = true) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S)
    (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P) (hK : Lanes32 s.mem S K)
    (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (round p src dst)) s fun s' =>
      Lanes32 s'.mem Dd (outState K rc) ∧ Frame [reg32 Dd 200, workR W] s.mem s'.mem ∧
      s'.gpr .ebp = P + 8 ∧ (∀ r, r ∉ [Reg.eax, .edx, .ecx, .ebp] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Run.check at hck
  split at hck <;> [skip; cases hck]
  rename_i σ hrun
  unfold round
  rw [WP.block_append_iff]
  refine WP.mono (Run.run_ok E hS hd hW hP hK hrc _ hrun Run.Rel.init) fun s₁ h₁ => ?_
  refine wp_addi fun s₂ u₂ => WP.block_nil ⟨fun i hi => ?_, by rw [u₂.mem]; exact h₁.frame,
    by rw [u₂.gpr, h₁.gpr, hP], fun r hr => ?_, by rw [u₂.rd, h₁.rd], by rw [u₂.wr, h₁.wr]⟩
  · have fD := E.fitD
    obtain ho := of_decide_eq_true (List.all_eq_true.mp hck i (List.mem_range.mpr hi))
    obtain ⟨_, hv⟩ := h₁.mem _ _ ho
    rw [Run.cad_lane (Run.isLane_iff.mpr ⟨by omega_using [hi], by omega_using []⟩)] at hv
    rw [u₂.mem, rd64_eq_readW _ (by omega_using [fD, hi]), hv,
      Run.refOut_eval K rc _ (Nat.mod_lt _ (by decide)) (by omega_using [hi])]
    simp [outState, hi]
  · have e : r ≠ .ebp := by rintro rfl; simp at hr
    rw [u₂.other r e, h₁.gpr]

end VG.Proof.Sha3.X86

end

/-!
# Keccak-f[1600] on x86 (32-bit): the whole function

The prologue loads the arguments, saves the callee-saved registers and stores
the round constants in the scratch space; each iteration of the loop runs two
rounds (`round_ok`), from the state to the second state in the scratch space
and back; the epilogue restores the registers.
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86 VG.Impl.Sha3.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha512.X86 (Only Wrote rd64 write64 mem_rd Acc rd64_write64_self rd64_write64_ne
  rd64_frame)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_addi wp_sub wp_cmpi eval_ne sub_beq
  addr_toNat)
open VG.Proof.Sha3 (outState_eq foldl_succ)
open VG.Proof.Sha512.Word64 (lo hi readW64)

/-! ## Addresses -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := arg s₀ 0
abbrev scp : BitVec 32 := arg s₀ 1
abbrev A₀ : KState := stateAt s₀.mem ((stp s₀).setWidth 64)
abbrev stR : Region := reg32 (stp s₀) 200
abbrev scR : Region := reg32 (scp s₀) 512
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : BitVec 32 := if r % 2 = 0 then stp s₀ else scp s₀
def oth (r : Nat) : BitVec 32 := if r % 2 = 0 then scp s₀ else stp s₀

/-- The address of the constant of round `r`. -/
abbrev rcp (r : Nat) : BitVec 32 := scp s₀ + BitVec.ofNat 32 (200 + 8 * r)

end

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | omega_arith | rfl

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = stp s₀ ∧ oth s₀ r = scp s₀) ∨ (cur s₀ r = scp s₀ ∧ oth s₀ r = stp s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem cur_even (s₀ : State) (t : Nat) : cur s₀ (2 * t) = stp s₀ ∧ oth s₀ (2 * t) = scp s₀ := by
  simp only [cur, oth]; split
  · exact ⟨rfl, rfl⟩
  · omega_arith

theorem cur_odd (s₀ : State) (t : Nat) : cur s₀ (2 * t + 1) = scp s₀ ∧ oth s₀ (2 * t + 1) = stp s₀ := by
  simp only [cur, oth]; split
  · omega_arith
  · exact ⟨rfl, rfl⟩

theorem addr_add (b : BitVec 32) (a o : Nat) : addr (b + BitVec.ofNat 32 a) o = addr b (a + o) := by
  simp only [addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rcp_succ (s₀ : State) (r : Nat) : rcp s₀ r + 8 = rcp s₀ (r + 1) := by
  simp only [rcp]
  bv_omega

theorem rd64_rcp (m : Mem) (s₀ : State) (r : Nat) :
    rd64 m (rcp s₀ r) 0 = rd64 m (scp s₀) (200 + 8 * r) := by
  simp only [rd64, rcp, addr_add, Nat.zero_add, Nat.add_zero]

theorem reg32_eq (b : BitVec 32) (n : Nat) : reg32 b n = ⟨addr b 0, n⟩ := by rw [addr_zero]

/-- A part of a region at `b`. -/
theorem sub32 {b : BitVec 32} {N a k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : a + k ≤ N) (hk : 0 < k) :
    Region.Sub ⟨addr b a, k⟩ (reg32 b N) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [addr_eq (by omega_arith)] at hx
  obtain hE := addr_toNat b
  generalize b.setWidth 64 = E at *
  bv_omega

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  disj : (stR s₀).Disjoint (scR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_sc : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_sc : (retR s₀).Disjoint (scR s₀)
  fitS : (stp s₀).toNat + 200 ≤ 2 ^ 32
  fitC : (scp s₀).toNat + 512 ≤ 2 ^ 32
  fitSp : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem accS : Acc s₀.wr (stp s₀) 200 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [h.wr]; simp) h.fitS

theorem accC : Acc s₀.wr (scp s₀) 512 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [h.wr]; simp) h.fitC

theorem accC200 : Acc s₀.wr (scp s₀) 200 := fun o ho => h.accC o (by omega_arith)

theorem accS8 : Acc8 s₀.wr (stp s₀) 200 := Acc8.of_mem (by rw [h.wr]; simp) h.fitS

theorem accC8 : Acc8 s₀.wr (scp s₀) 512 := Acc8.of_mem (by rw [h.wr]; simp) h.fitC

theorem accC2008 : Acc8 s₀.wr (scp s₀) 200 := fun o ho => h.accC8 o (by omega_arith)

/-- A part of the scratch space beyond the second state, and the state being written. -/
theorem sc_dst {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {d n : Nat} (hd₀ : 200 ≤ d)
    (hd : d + n ≤ 512) (hn : 0 < n) : Region.Disjoint ⟨addr (scp s₀) d, n⟩ (reg32 Dd 200) := by
  rcases hD with rfl | rfl
  · exact h.disj.symm.sub_left (sub32 h.fitC hd hn)
  · rw [reg32_eq]; exact sub_disj h.fitC hd (by omega_arith) hn (by omega_arith) (.inr hd₀)

/-- A part of the scratch space outside its work area. -/
theorem sc_work {d n : Nat} (hd : d + n ≤ 512) (hn : 0 < n) (hs : d + n ≤ 408 ∨ 488 ≤ d) :
    Region.Disjoint ⟨addr (scp s₀) d, n⟩ (workR (scp s₀)) :=
  sub_disj h.fitC hd (by omega_arith) hn (by omega_arith) hs

theorem st_work : (stR s₀).Disjoint (workR (scp s₀)) :=
  h.disj.sub_right (sub32 h.fitC (by omega_arith) (by omega_arith))

theorem state_work {S : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) :
    (reg32 S 200).Disjoint (workR (scp s₀)) := by
  rcases hS with rfl | rfl
  · exact h.st_work
  · rw [reg32_eq]; exact h.sc_work (by omega_arith) (by omega_arith) (.inl (by omega_arith))

theorem st_sc200 : (stR s₀).Disjoint (reg32 (scp s₀) 200) :=
  h.disj.sub_right (Region.sub_prefix (by omega_arith))

theorem env_of {S Dd : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    (hSD : (reg32 S 200).Disjoint (reg32 Dd 200)) {r : Nat} (hr : r < 24) :
    Env s₀.wr S Dd (scp s₀) (rcp s₀ r) := by
  have fS := h.fitS
  have fC := h.fitC
  obtain hP : (rcp s₀ r).toNat = (scp s₀).toNat + (200 + 8 * r) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 200 + 8 * r) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  refine ⟨?_, ?_, fC, by omega_arith, ?_, ?_, h.accC8, fun o ho => ?_, hSD, h.state_work hS,
    h.state_work hD, ?_, ?_⟩
  · rcases hS with rfl | rfl <;> omega_arith
  · rcases hD with rfl | rfl <;> omega_arith
  · rcases hS with rfl | rfl
    · exact h.accS8
    · exact h.accC2008
  · rcases hD with rfl | rfl
    · exact h.accS8
    · exact h.accC2008
  · rw [addr_add]; exact h.accC8 _ (by omega_arith)
  · show Region.Disjoint ⟨addr (scp s₀) (200 + 8 * r), 8⟩ _
    exact h.sc_dst hD (by omega_arith) (by omega_arith) (by omega_arith)
  · show Region.Disjoint ⟨addr (scp s₀) (200 + 8 * r), 8⟩ _
    exact h.sc_work (by omega_arith) (by omega_arith) (.inl (by omega_arith))

theorem env {r : Nat} (hr : r < 24) : Env s₀.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := by
  rcases cur_cases s₀ r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.env_of (.inl rfl) (.inr rfl) h.st_sc200 hr
  · exact h.env_of (.inr rfl) (.inl rfl) h.st_sc200.symm hr

/-- Words of the scratch space that a round does not write. -/
theorem keep_round {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {m m' : Mem}
    (hf : Frame [reg32 Dd 200, workR (scp s₀)] m m') {d : Nat} (hd : 200 ≤ d) (hd' : d + 4 ≤ 408) :
    m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (scp s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.sc_dst hD hd (by omega_arith) (by decide)
  · exact h.sc_work (by omega_arith) (by decide) (.inl hd')

end Pre

/-! ## What the scratch space holds -/

/-- The round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, rd64 m (scp s₀) (200 + 8 * j) = RC j

/-- The saved registers. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scp s₀)) s₀.gpr saved

theorem saved_ok : ∀ p ∈ saved, 392 ≤ p.2 ∧ p.2 + 4 ≤ 404 := by decide

theorem saved_fits : Spill.Fits 404 saved := by decide

theorem Aux.keep {s₀ : State} {m m' : Mem} (ha : Aux s₀ m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32) :
    Aux s₀ m' := fun j hj => by
  simp only [rd64]
  rw [hk _ (by omega_arith) (by omega_arith), hk _ (by omega_arith) (by omega_arith)]
  exact ha j hj

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 392 ≤ d → d + 4 ≤ 404 → m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32) :
    Saved s₀ m' :=
  hs.of_readW fun p hp => hk _ (saved_ok p hp).1 (saved_ok p hp).2

/-! ## The state in memory -/

theorem stateAt_get {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) (m : Mem) {i : Nat} (hi : i < 25) :
    (stateAt m (b.setWidth 64))[i] = rd64 m b (8 * i) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, show b.setWidth 64 + BitVec.ofNat 64 (8 * i) + 4 =
      b.setWidth 64 + BitVec.ofNat 64 (8 * i + 4) by bv_omega,
    ← addr_eq (by omega_arith), ← addr_eq (by omega_arith)]

theorem stateAt_eq {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) {m : Mem} {K : KState}
    (h : Lanes32 m b K) : stateAt m (b.setWidth 64) = K := by
  apply Vector.ext
  intro i hi
  rw [stateAt_get hfit m hi, h i hi]
  exact getElem!_pos K i hi

/-! ## The rounds -/

/-- The loop's invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  esi : s.gpr .esi = stp s₀
  edi : s.gpr .edi = scp s₀
  ebp : s.gpr .ebp = rcp s₀ r
  keep : ∀ q, q ∉ [Reg.eax, .edx, .ecx, .esi, .edi, .ebp] → s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes32 s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  saved : Saved s₀ s.mem
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {p : List XReg} {src dst : Reg}
    (hck : Run.check p src dst = true) {s : State} (hL : LInv s₀ r s) (h0 : s.gpr src = cur s₀ r)
    (hd : s.gpr dst = oth s₀ r) : WP isa (.block (round p src dst)) s (LInv s₀ (r + 1)) := by
  obtain hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := (cur_cases s₀ r).symm.imp (·.2) (·.2)
  obtain E : Env s.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env hr
  refine WP.mono (round_ok hck (rc := RC r) s E h0 hd hL.edi hL.ebp hL.state
    (by rw [rd64_rcp]; exact hL.aux r hr)) fun s' ⟨hl, hf, hbp, hq, hrd, hwr⟩ => ?_
  obtain g : ∀ q ∈ [Reg.esi, .edi], s'.gpr q = s.gpr q := fun q hq' => hq q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl <;> decide)
  refine ⟨by rw [g _ (by simp), hL.esi], by rw [g _ (by simp), hL.edi], by rw [hbp, rcp_succ],
    fun q hq' => ?_, hrd.trans hL.rd, hwr.trans hL.wr, ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega_arith),
    hL.saved.keep fun d hd hd' => hp.keep_round hD hf (by omega_arith) (by omega_arith), ?_⟩
  · have ⟨a, b, c, _, _, e⟩ : q ≠ .eax ∧ q ≠ .edx ∧ q ≠ .ecx ∧ q ≠ .esi ∧ q ≠ .edi ∧ q ≠ .ebp := by
      simpa using hq'
    rw [hq q (by simp [a, b, c, e]), hL.keep q hq']
  · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · rcases hD with e | e <;> rw [e]
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨scR s₀, by simp, sub32 hp.fitC (by omega_arith) (by omega_arith)⟩

/-- The first round of an iteration, with its plan, runs to the round's
output: the kernel evaluates it. -/
theorem planA_ok : Run.check planA .esi .edi = true := by lit_decide

/-- The second round, with its plan. -/
theorem planB_ok : Run.check planB .edi .esi = true := by lit_decide

theorem body_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 12) {s : State} (hL : LInv s₀ (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega_arith) planA_ok (src := .esi) (dst := .edi) hL
    (by rw [hL.esi, (cur_even s₀ t).1]) (by rw [hL.edi, (cur_even s₀ t).2]))
    fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega_arith) planB_ok (src := .edi) (dst := .esi) h₁
    (by rw [h₁.edi, (cur_odd s₀ t).1]) (by rw [h₁.esi, (cur_odd s₀ t).2]))
    fun s₂ h₂ => ?_
  obtain h₂' : LInv s₀ (2 * (t + 1)) s₂ := by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega_arith]; exact h₂
  refine wp_mov fun s₃ u₃ => wp_sub fun s₄ u₄ _ => wp_cmpi fun s₅ u₅ _ hz => WP.block_nil ?_
  obtain hT : s₄.gpr .eax = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .edi (by decide), h₂'.ebp, h₂'.edi]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega_arith]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    VG.Proof.Sha256.X86.Stream.sub_beq (by omega_arith) (by omega_arith)] at hz
  obtain g : ∀ q, q ≠ .eax → s₅.gpr q = s₂.gpr q := fun q hq => by
    rw [u₅.gpr, u₄.other q hq, u₃.other q hq]
  obtain hs₅ : LInv s₀ (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g _ (by decide), h₂'.esi]
    · rw [g _ (by decide), h₂'.edi]
    · rw [g _ (by decide), h₂'.ebp]
    · rw [g _ (by rintro rfl; simp at hq), h₂'.keep q hq]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.saved
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.frame
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega_arith)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega_arith]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega_arith)]; rfl, by omega_arith, hs₅⟩

/-! ## The prologue -/

/-- Round constant `k`, stored in the scratch space at `edi`. -/
theorem rcStore_ok (k : Nat) (_hk : k < 24) {W : BitVec 32} (s : State) (hW : s.gpr .edi = W)
    (hin : Wr2 s W (200 + 8 * k)) :
    WP isa (.block (rcStore k)) s fun s' =>
      Wrote [.eax] s s' (write64 s.mem W (200 + 8 * k) (RC k)) := by
  unfold rcStore
  refine wp_movi fun s₁ u₁ => wp_stm (by rw [u₁.other _ (by decide), hW]) (by rw [u₁.wr]; exact hin.1)
    fun s₂ u₂ => ?_
  refine wp_movi fun s₃ u₃ => ?_
  rw [show 204 + 8 * k = 200 + 8 * k + 4 by omega_arith]
  refine wp_stm (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hW])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin.2) fun s₄ u₄ =>
      WP.block_nil ⟨fun r hr => ?_, ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · have hr' : r ≠ .eax := by simpa using hr
    rw [u₄.gpr, u₃.other r hr', u₂.gpr, u₁.other r hr']
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl

/-- During the stores of the round constants. -/
structure RcInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨addr (scp s₀) 200, 192⟩] s₁.mem s.mem
  rcs : ∀ j < k, rd64 s.mem (scp s₀) (200 + 8 * j) = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s₁ : State) (hW : s₁.gpr .edi = scp s₀) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 24).flatMap rcStore)) s₁ (RcInv s₀ s₁ 24) := by
  have fC := hp.fitC
  refine wp_range_flatMap (M := isa) (RcInv s₀ s₁) (fun k s hk hI => ?_) 24 (Nat.le_refl _) s₁
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  refine WP.mono (rcStore_ok k hk s (by rw [hI.gpr _ (by decide), hW])
    ⟨by rw [hI.wr, hwr]; exact hp.accC _ (by omega_arith), by rw [hI.wr, hwr]; exact hp.accC _ (by omega_arith)⟩)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun j hj => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _)
      (sub_contains fC (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
      (sub_contains fC (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) _
  · rw [w.mem]
    by_cases e : j = k
    · subst e; exact rd64_write64_self _ _ (by omega_arith)
    · rw [rd64_write64_ne _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hI.rcs j (by omega_arith)

theorem prologue_eq : prologue = (.mov .eax (.mem (at_ .esp 8)) :: .mov .ecx (.mem (at_ .esp 4)) ::
    (Spill.saveCode .eax saved ++ ([.mov .edi (.reg .eax), .mov .esi (.reg .ecx)] : List Instr))) ++
    ((List.range 24).flatMap rcStore ++
      ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 200)] : List Instr)) := rfl

theorem arg_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 2) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  have := hp.fitSp
  show (⟨addr (s₀.gpr .esp) 4, 8⟩ : Region).Contains _ _
  exact sub_contains (N := 12) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  have fC := hp.fitC
  have fS := hp.fitS
  rw [prologue_eq, WP.block_append_iff]
  refine wp_ldm (B := s₀.gpr .esp) rfl (arg_in hp (i := 1) (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_ldm (B := s₀.gpr .esp) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact arg_in hp (i := 0) (by omega_arith)) fun s₂ u₂ => ?_
  obtain e1 : s₂.gpr .eax = scp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  obtain e2 : s₂.gpr .ecx = stp s₀ := by rw [u₂.gpr, u₁.mem]; rfl
  obtain w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  obtain sin : ∀ (t : State), t.wr = s₀.wr → ∀ d, 392 ≤ d → d + 4 ≤ 404 →
      InRegions t.wr (addr (scp s₀) d) 4 := fun t ht d _ _ => by rw [ht]; exact hp.accC _ (by omega_arith)
  refine Spill.save_ok saved (fun p h => by
    rw [e1]; exact sin _ w₂ _ (saved_ok p h).1 (saved_ok p h).2) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  obtain g₅ : ∀ r, s₅.gpr r = s₂.gpr r := fun r => by rw [u₅.gpr]
  obtain g₂ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₂.other r h2, u₁.other r h1]
  obtain hW₇ : s₇.gpr .edi = scp s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e1]
  obtain w₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, w₂]
  -- The saved registers, and the memory the saves changed.
  obtain hm₇ : s₇.mem = Spill.saveMem s₀.mem (addr (scp s₀)) s₀.gpr saved := by
    rw [u₇.mem, u₆.mem, u₅.mem, e1, u₂.mem, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => g₂ _ (by revert p h; decide) (by revert p h; decide)
  obtain fr₇ : Frame [⟨addr (scp s₀) 392, 12⟩] s₀.mem s₇.mem := by
    rw [hm₇]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      sub_contains fC (by omega_arith) (saved_ok p h).1 (saved_ok p h).2 (by omega_arith)
  obtain sv₇ : Saved s₀ s₇.mem := by
    rw [hm₇]; exact Spill.saveMem_saved_addr _ _ saved_fits (by omega_arith)
  have hwr₇ := w₇
  -- The round constants.
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₇ hW₇ w₇) fun s₈ h₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain g₈ : ∀ r, r ≠ .eax → s₈.gpr r = s₇.gpr r := fun r hr => h₈.gpr r (by simpa using hr)
  obtain keep : ∀ d, 392 ≤ d → d + 4 ≤ 404 →
      s₁₀.mem.readW (addr (scp s₀) d) 32 = s₇.mem.readW (addr (scp s₀) d) 32 := fun d h1 h2 => by
    rw [u₁₀.mem, u₉.mem]
    exact h₈.frame.readW (Region.contains_self _ _) (by
      simpa using sub_disj fC (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (.inr h1)) (by decide)
  obtain fr₁₀ : Frame [⟨addr (scp s₀) 392, 12⟩, ⟨addr (scp s₀) 200, 192⟩] s₀.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem]
    exact (fr₇.mono (by simp)).trans (h₈.frame.mono (by simp))
  refine ⟨?_, ?_, ?_, fun q hq => ?_, by rw [u₁₀.rd, u₉.rd, h₈.rd, u₇.rd, u₆.rd, u₅.rd,
    u₂.rd, u₁.rd], by rw [u₁₀.wr, u₉.wr, h₈.wr, w₇], fun i hi => ?_, ?_,
    sv₇.keep fun d h1 h2 => keep d h1 h2, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), g₈ _ (by decide), u₇.gpr, u₆.other _ (by decide),
      g₅, e2]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), g₈ _ (by decide), hW₇]
  · rw [u₁₀.gpr, u₉.gpr, g₈ _ (by decide), hW₇]; rfl
  · have ⟨a, _, c', d', e', f⟩ : q ≠ .eax ∧ q ≠ .edx ∧ q ≠ .ecx ∧ q ≠ .esi ∧ q ≠ .edi ∧ q ≠ .ebp := by
      simpa using hq
    rw [u₁₀.other q f, u₉.other q f, g₈ q a, u₇.other q d', u₆.other q e', g₅,
      g₂ q a c']
  · -- The state is untouched.
    obtain hc : cur s₀ 0 = stp s₀ := by simp [cur]
    rw [hc, rd64_frame fr₁₀ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.disj.sub_right (sub32 fC (by omega_arith) (by omega_arith))
      · exact hp.disj.sub_right (sub32 fC (by omega_arith) (by omega_arith))) fS (by omega_arith),
      ← stateAt_get fS _ hi]
    simp only [List.range_zero, List.foldl_nil]
    exact (getElem!_pos _ i hi).symm
  · rw [u₁₀.mem, u₉.mem]; exact h₈.rcs
  · refine fr₁₀.sub fun R hR => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨scR s₀, by simp, sub32 fC (by omega_arith) (by omega_arith)⟩
    · exact ⟨scR s₀, by simp, sub32 fC (by omega_arith) (by omega_arith)⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block restore) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.permuteX86.post s₀ s' := by
  have fC := hp.fitC
  obtain hin : ∀ d, 392 ≤ d → d + 4 ≤ 404 → InRegions (s.rd ++ s.wr) (addr (scp s₀) d) 4 :=
    fun d _ _ => mem_rd (by rw [hL.wr]; exact hp.accC _ (by omega_arith))
  rw [show restore = Spill.restoreCode .edi ([(.esi, 392), (.ebp, 400)] ++ [(.edi, 396)]) ++ [] from rfl]
  refine Spill.restoreBase_ok _ (by decide)
    (fun p h => have hb := saved_ok p (by revert p h; decide); by rw [hL.edi]; exact hin _ hb.1 hb.2)
    (by rw [hL.edi]; exact hL.saved.sub (by decide)) fun s₃ r₃ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases h : r ∈ ([(.esi, 392), (.ebp, 400)] ++ [(.edi, 396)] : Spill.Slots).map Prod.fst
    · exact r₃.regs r h
    · rw [r₃.other r h, hL.keep r (by revert h; revert hr; revert r; decide)]
  · rw [r₃.mem]
    exact hL.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_sc⟩) (by decide)
  · show stateAt s₃.mem ((stp s₀).setWidth 64) = keccakF (A₀ s₀)
    rw [r₃.mem]
    obtain hc : cur s₀ 24 = stp s₀ := by simp [cur]
    exact stateAt_eq hp.fitS (hc ▸ hL.state)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.permuteX86.post s₀ s' := by
  unfold permute
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 24) ?_ fun s₂ h₂ => restore_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ t, n = 12 - t ∧ t < 12 ∧ LInv s₀ (2 * t) s
  refine WP.loop (M := isa) Inv (fun n s ⟨t, hn, ht, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega_arith, h₁⟩
  refine WP.mono (body_ok hp ht hL) fun s' h => ?_
  rcases h with ⟨he, hL'⟩ | ⟨he, ht', hL'⟩
  · exact .inl ⟨he, hL'⟩
  · exact .inr ⟨he, 12 - (t + 1), by omega_arith, t + 1, rfl, ht', hL'⟩

/-! ## Constant time -/

/-- The constant-time analysis's taint without the round constants that the
prologue stores at `[200, 392)` of the scratch space: public, but no
address or branch depends on them, and the kernel checks the analysis much
faster without them (`taint_decide_weak`). -/
def dropRC (τ : VG.X86.Taint.T) : VG.X86.Taint.T :=
  { τ with slots := τ.slots.removeAll 200 192 }

/-- The taint analysis starts with `esp` public, and the words holding
`state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 512], argLen := 12,
    argBases := [(4, 0), (8, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  obtain hst := hp.fitS; have hsc := hp.fitC; have hs := hp.fitSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega_arith) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega_arith) hp.ret_sc hp.arg_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.permuteX86.pre s₁)
    (h₂ : Proof.Sha3.permuteX86.pre s₂) (hpub : Proof.Sha3.permuteX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  obtain hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stp, scp, a0, a1]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.fitSp h4 hk, VG.X86.Taint.argByte_eq hp₂.fitSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega_arith
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def satMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem sat_pre : Proof.Sha3.permuteX86.pre satState := by
  obtain a0 : arg satState 0 = 0x1000 := by decide
  obtain a1 : arg satState 1 = 0x2000 := by decide
  obtain e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha3.permuteX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem permute_verified : Verified X86.target permute Proof.Sha3.permuteX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := VG.X86.sseTaint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
      (by taint_decide_weak dropRC),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sha3.X86

section

section

/-!
# SHA-3 on x86 (32-bit): calling the permutation

A call of `vg_keccak_f1600` in a frame of its two arguments (`permuteCall`),
from its proof of `Verified` (`WP.callWith`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_nosp : NoSp Impl.Sha3.X86.permute := NoSp.of_all (by lit_decide)

theorem permute_stack : stackUse Impl.Sha3.X86.permute = 0 := by lit_decide

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-- Calling `vg_keccak_f1600(st, scr)` on the state at `S` with the first 512
bytes of the scratch space at `C` (of 640 bytes): the call uses the 12 bytes
below `esp` (`E`), for its arguments and return address. -/
theorem permuteCall_ok {st scr : Reg} (hst : st ≠ .esp) (hscr : scr ≠ .esp) {s : State}
    {S C E : BitVec 32} (hesp : s.gpr .esp = E) (hS : s.gpr st = S) (hC : s.gpr scr = C)
    (hE : 12 ≤ E.toNat) (fS : S.toNat + 200 ≤ 2 ^ 32) (fC : C.toNat + 512 ≤ 2 ^ 32)
    (d : (reg32 S 200).Disjoint (reg32 C 512)) (dS : (below E 12).Disjoint (reg32 S 200))
    (dC : (below E 12).Disjoint (reg32 C 512)) (wS : reg32 S 200 ∈ s.wr) (wC : reg32 C 640 ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 S 200, reg32 C 512, below E 12] s.mem s'.mem →
      stateAt s'.mem (S.setWidth 64) = keccakF (stateAt s.mem (S.setWidth 64)) → Q s') :
    WP isa (Impl.Sha3.X86.Stream.permuteCall st scr) s Q := by
  obtain fit : 4 * [scr, st].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain hrs : Reg.esp ∉ [scr, st] := by simp [Ne.symm hst, Ne.symm hscr]
  obtain a0 : arg (pushed [scr, st] s).callEntry 0 = S := by
    rw [callEntry_arg fit hrs (by simp)]; exact hS
  obtain a1 : arg (pushed [scr, st] s).callEntry 1 = C := by
    rw [callEntry_arg fit hrs (by simp)]; exact hC
  obtain eA : argAddr (pushed [scr, st] s).callEntry 0 = (E - BitVec.ofNat 32 8).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  obtain eSp : (pushed [scr, st] s).callEntry.gpr .esp = E - BitVec.ofNat 32 12 := by
    rw [callEntry_esp', hesp]; rfl
  obtain b8 : Region.Sub (below E 8) (below E 12) := below_sub (by omega_arith) hE
  obtain r4 : Region.Sub ⟨(E - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below E 12) := by
    have := below_inner (sp := E) (a := 4) (b := 12) (k := 8) (by omega_arith) hE
    rw [show E - BitVec.ofNat 32 12 = E - BitVec.ofNat 32 8 - BitVec.ofNat 32 4 by bv_omega]
    exact this
  refine WP.callWith (k := Proof.Sha3.permuteX86) permute_verified.1 permute_nosp (by simp) hrs
    (by rw [permute_stack, hesp]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (rd := [⟨argAddr (pushed [scr, st] s).callEntry 0, 8⟩]) (wr := [reg32 S 200, reg32 C 512])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · simp only [Proof.Sha3.permuteX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, d, dS.sub_left b8, dC.sub_left b8, dS.sub_left r4, dC.sub_left r4, fS, fC, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega_arith
  · rw [hesp]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (below E (4 * [scr, st].length)) (by simp) 0 (by rw [eA]; simp) (by simp)
    · exact within (reg32 S 200) (by simp [wS]) 0 (by simp) (by simp)
    · exact within (reg32 C 640) (by simp [wC]) 0 (by simp) (by simp)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact within (reg32 S 200) (by simp [wS]) 0 (by simp) (by simp)
    · exact within (reg32 C 640) (by simp [wC]) 0 (by simp) (by simp)
  · rw [permute_stack, hesp] at f'
    obtain hsE : Frame [below E 12] s.mem (pushed [scr, st] s).callEntry.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    simp only [Proof.Sha3.permuteX86, arg_withRegions, State.withRegions_mem, a0] at post
    refine hQ s' rd' wr' cs' f' ?_
    -- The pop loses the arguments' frame, below `esp`, apart from the state.
    obtain fL : Frame [below E 12] s₂.mem s'.mem := by
      rw [hesp] at m₂; exact Frame.below_mono (wr := []) m₂ (by simp) hE
    rw [Proof.Sha3.stateAt_congr fun i hi =>
      fL.bytes (R := reg32 S 200) (by simpa using dS.symm) (by simp) hi, post]
    refine congrArg keccakF (Proof.Sha3.stateAt_congr fun i hi => ?_)
    exact hsE.bytes (R := reg32 S 200) (by simpa using dS.symm) (by simp) hi

end VG.Proof.Sha3.X86

end

/-!
# The SHA-3 sponge on x86 (32-bit): common lemmas

Facts about bytes, the stack and the variables `absorb` and `squeeze` keep in
their scratch space, which the proofs of the streaming functions share.
-/

namespace VG.Proof.Sha3.X86.Stream

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (addr_add_ofNat addr_toNat)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The low byte of a word in memory is its first byte. -/
theorem low_byte (m : Mem) (a : Addr) : (m.readW a 32).setWidth 8 = m a := by
  have := Mem.readW_byte m a (i := 0) (by omega_arith)
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  rw [this]
  ext i hi
  simp

theorem xor_low (b : Byte) (w : BitVec 32) : (b.setWidth 32 ^^^ w).setWidth 8 = b ^^^ w.setWidth 8 := by
  ext i hi; simp

theorem byte_low (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

/-- The contract's stack region. -/
theorem stk_eq {E : BitVec 32} (h : 12 ≤ E.toNat) : below E 12 = ⟨E.setWidth 64 - 12, 12⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

/-- `[x + k]`, where nothing wraps around the 32-bit address space. -/
theorem ptr_addr {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) 0 = x.setWidth 64 + BitVec.ofNat 64 k := by
  rw [addr_add_ofNat (by omega_arith), Nat.add_zero]

theorem ofNat_add_one (x : BitVec 32) (k : Nat) :
    x + BitVec.ofNat 32 k + 1 = x + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem add_sub_self (x y : BitVec 32) : x + y - x = y := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- A part of a region at a 32-bit pointer. -/
theorem sub_word {b : BitVec 32} {N d : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hd : d + 4 ≤ N) :
    Region.Sub ⟨addr b d, 4⟩ ⟨b.setWidth 64, N⟩ := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [addr_eq (by omega_arith)] at hx
  obtain hE := addr_toNat b
  generalize b.setWidth 64 = B at *
  bv_omega

/-- Two words of a region at a 32-bit pointer that do not overlap. -/
theorem word_sep {b : BitVec 32} {N d e : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hd : d + 4 ≤ N)
    (he : e + 4 ≤ N) (h : d + 4 ≤ e ∨ e + 4 ≤ d) (m : Mem) (v : BitVec 32) :
    (m.writeW (addr b e) v).readW (addr b d) 32 = m.readW (addr b d) 32 :=
  VG.Proof.Sha256.X86.Stream.readW_writeW_addr m v (by omega_arith) (by omega_arith) h

/-- A word of the argument area. -/
theorem arg_word {E : BitVec 32} {n d : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ n + 4) : Region.Sub ⟨addr E d, 4⟩ ⟨addr E 4, n⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega_arith)] at ha ⊢
  obtain hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem arg_contains {E : BitVec 32} {n d : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ n + 4) : (⟨addr E 4, n⟩ : Region).Contains (addr E d) 4 := by
  simp only [Region.Contains]
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith)]
  obtain hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

/-- The arguments are above the return address, the stack the calls use below it. -/
theorem arg_stk {E : BitVec 32} {n : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hlo : 12 ≤ E.toNat) :
    Region.Disjoint ⟨addr E 4, n⟩ (below E 12) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega_arith)] at h₁
  rw [Taint.sub_setWidth (by omega_arith)] at h₂
  obtain hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem ret_stk {E : BitVec 32} (hfit : E.toNat + 4 ≤ 2 ^ 32) (hlo : 12 ≤ E.toNat) :
    Region.Disjoint ⟨E.setWidth 64, 4⟩ (below E 12) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega_arith)] at h₂
  obtain hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem argWord_eq {s : State} {n : Nat} (hsp : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {k : Nat}
    (hk : k < n) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega_arith), addr_eq (by omega_arith), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega_arith

end VG.Proof.Sha3.X86.Stream

end
