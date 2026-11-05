module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on RISC-V: the contract, the invariant and a modulus's working space

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{Contract,Base,Phase}.lean`):

* `pcContract`: `vg_ffdh_parameter_candidate(out = a0, out_len = a1,
  used = a2, bits = a3, generator = a4, rand = a5, rand_len = a6,
  scratch = a7, scratch_len)`, the last on the stack, with 96 bytes of stack
  below `sp` for the round it calls (`pc_implies`).
* `PP`: what the candidate's run depends on, all of it public; `Args`: the
  header words holding the arguments; `mutR`: the ranges of the working
  space the pieces may change (header word 1, words 6–15 and 19–31, and the
  arrays, up to the save area); `St`: what holds between the pieces.
* `phase_ok`: for the modulus of `mb` bits, `w = ⌈mb / 64⌉`, the header
  (`Ph`) and the registers of the arrays.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64.Search (rw_self frm_writeW)
open VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)

/-! ## The contract -/

def pcPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
  let used : Region := ⟨s.gpr .a2, 8⟩
  let rand : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  let below : Region := ⟨s.sp - BitVec.ofNat 64 96, 96⟩
  96 ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    s.rd = [rand, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0 ∧
    512 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 8192 ∧
    (s.gpr .a1).toNat = ((s.gpr .a3).toNat + 7) / 8 ∧
    (((s.gpr .a4).setWidth 32).toNat = 2 ∨ ((s.gpr .a4).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 0).toNat

abbrev pcRand (s : State) : List Byte := bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat

def pcResult (s : State) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  parameterCandidate (s.gpr .a3).toNat ((s.gpr .a4).setWidth 32).toNat (pcRand s)

def pcPost (s t : State) : Prop :=
  ((t.gpr .a0).setWidth 32).toNat = Proof.Ffdh.candidateStatus (pcResult s) ∧
    bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
      (match pcResult s with
        | some (some p, _) => i2osp p (s.gpr .a1).toNat
        | _ => List.replicate (s.gpr .a1).toNat 0) ∧
    wordsAt t.mem (s.gpr .a2) 1 =
      [BitVec.ofNat 64 (match pcResult s with
        | some (_, rest) => (s.gpr .a6).toNat - rest.length
        | none => 0)]

def pcPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat) ∧
    s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧
    s.gpr .a3 = t.gpr .a3 ∧ (s.gpr .a4).setWidth 32 = (t.gpr .a4).setWidth 32 ∧ s.gpr .a5 = t.gpr .a5 ∧
    s.gpr .a6 = t.gpr .a6 ∧ s.gpr .a7 = t.gpr .a7 ∧ stackArg s 0 = stackArg t 0

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting the precondition: a 64-byte p of 512 bits, no randomness,
the working space at `0xA000`, its length on the stack at `0x9000`. -/
def pcSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 512 | .a4 => 2 | .a5 => 0x3000
    | .a7 => 0xA000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 0x20 else bif Nat.beq a.toNat 0x9001 then 0x04 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0xA000, 1056 * 8⟩]

theorem pc_implies : pcContract.Implies (Proof.Ffdh.parameterCandidateContract abi 96) where
  pre := by
    intro s h
    sig_pre [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq] at h
    sig_pre [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by
    sig_implies_post [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
      pcContract, pcPost, pcResult, pcRand, stackArgs_one, List.append_eq]
  pub := by
    intro s t _ _ h
    sig_pub [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Ffdh.parameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
      stackBelow, pcContract, pcPre, stackArgs_one, List.append_eq]
      [pcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using pcSat

/-! ## The public data and the invariant -/

/-- What the candidate depends on: the working space (`n` words at `B`),
`out`, `used`, `bits`, the generator, and the tape at `rp`. -/
structure PP where
  B : Addr
  n : Nat
  op : Addr
  up : Addr
  bits : Nat
  g : Nat
  rp : Addr
  r : List Byte
  /-- The stack pointer, which the candidate keeps. -/
  sp : Addr
  /-- The save area's words on entry: the callee-saved registers and `ra`. -/
  sv : Nat → BitVec 64

/-- `out_len`. -/
abbrev PP.L (p : PP) : Nat := (p.bits + 7) / 8

/-- The working space's bytes. -/
abbrev PP.Z (p : PP) : Nat := 8 * p.n

/-- The bounds. -/
structure Dims (p : PP) : Prop where
  b1 : 512 ≤ p.bits
  b2 : p.bits ≤ 8192
  g : p.g = 2 ∨ p.g = 5
  n : 16 * p.L + 32 ≤ p.n
  n' : 8 * p.n ≤ 2 ^ 64
  rl : p.r.length < 2 ^ 64

/-- The header words holding the arguments. -/
structure Args (m : Mem) (p : PP) : Prop where
  wsLen : word m p.B (8 * hWsLen) = BitVec.ofNat 64 p.n
  out : word m p.B (8 * hOut) = p.op
  len : word m p.B (8 * hLen) = BitVec.ofNat 64 p.L
  usedP : word m p.B (8 * hUsedP) = p.up
  bits : word m p.B (8 * hBits) = BitVec.ofNat 64 p.bits
  gen : word m p.B (8 * hGen) = BitVec.ofNat 64 p.g
  rand : word m p.B (8 * hRand) = p.rp
  rlen : word m p.B (8 * hRandLen) = BitVec.ofNat 64 p.r.length

/-- The ranges of the working space the pieces may change. -/
def mutR (n : Nat) : List (Nat × Nat) := [(8, 8), (48, 80), (152, 104), (256, 8 * n - saveBytes - 256)]

/-- A range within one of `mutR`. -/
def InMut (n : Nat) (r : Nat × Nat) : Prop := ∃ r' ∈ mutR n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2

theorem InMut.arrays {n o k : Nat} (h1 : 256 ≤ o) (h2 : o + k + saveBytes ≤ 8 * n) : InMut n (o, k) :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))), h1,
    by simp only [saveBytes] at h2 ⊢; omega_arith⟩

theorem InMut.hdr {n i : Nat} (h : i = 1 ∨ (6 ≤ i ∧ i < 16) ∨ (19 ≤ i ∧ i < 32)) : InMut n (8 * i, 8) := by
  rcases h with rfl | h | h
  · exact ⟨_, List.mem_cons_self, by decide, by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by omega_arith, by omega_arith⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by omega_arith, by omega_arith⟩

/-- A change within ranges of `mutR` is within `mutR`. -/
theorem Frm.toMut {B : Addr} {n : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, InMut n r) : Frm B (mutR n) m m' := h.widen hr

/-- The argument words are not in `mutR`. -/
theorem Args.frm {m m' : Mem} {p : PP} {B' : Addr} (h : Args m p) (hf : Frm B' (mutR p.n) m m') (hB : B' = p.B) :
    Args m' p := by
  subst hB
  have k : ∀ {i : Nat}, i = 0 ∨ (2 ≤ i ∧ i ≤ 5) ∨ (16 ≤ i ∧ i ≤ 18) →
      word m' p.B (8 * i) = word m p.B (8 * i) := fun hi =>
    hf.word_eq (fun r hr => by
      simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  exact ⟨(k (by decide)).trans h.wsLen, (k (by decide)).trans h.out, (k (by decide)).trans h.len,
    (k (by decide)).trans h.usedP, (k (by decide)).trans h.bits, (k (by decide)).trans h.gen,
    (k (by decide)).trans h.rand, (k (by decide)).trans h.rlen⟩

/-- The stack the round's frame uses. -/
abbrev stk (sp : Addr) : Region := below sp 96

/-- The buffers: the tape, readable and apart from the working space; `out`
and `used`, writable and apart from the working space and the tape. -/
structure Bufs (p : PP) (s : State) : Prop where
  rdR : ∀ i < p.r.length, InRegions (s.rd ++ s.wr) (off p.rp i) 1
  sepR : ∀ i < p.r.length, ∀ x, ofs p.B x < p.Z → off p.rp i ≠ x
  bR : Spec.Rsa.bytesAt s.mem p.rp p.r.length = p.r
  /-- `out` is zeroed first. -/
  bO : Spec.Rsa.bytesAt s.mem p.op p.L = List.replicate p.L 0
  oW : (⟨p.op, p.L⟩ : Region) ∈ s.wr
  oNW : p.op.toNat + p.L ≤ 2 ^ 64
  sepO : ∀ x, ofs p.op x < p.L → p.Z ≤ ofs p.B x
  scrU : Scr s p.up 8
  sepU : ∀ x, ofs p.up x < 8 → p.Z ≤ ofs p.B x
  stkR : (stk p.sp).Disjoint ⟨p.rp, p.r.length⟩
  stkO : (stk p.sp).Disjoint ⟨p.op, p.L⟩
  stkU : (stk p.sp).Disjoint ⟨p.up, 8⟩
  dOU : (⟨p.op, p.L⟩ : Region).Disjoint ⟨p.up, 8⟩

/-- The tape's bytes are kept by a change in the working space. -/
theorem bytes_frm {p : PP} {m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm p.B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hsep : ∀ i < p.r.length, ∀ x, ofs p.B x < p.Z → off p.rp i ≠ x) :
    Spec.Rsa.bytesAt m' p.rp p.r.length = Spec.Rsa.bytesAt m p.rp p.r.length := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr' => Or.inr ?_
  have := hsep i (List.mem_range.mp hi) (off p.rp i)
  have h2 := hr r hr'
  show r.1 + r.2 ≤ ofs p.B (off p.rp i)
  by_contra hc
  exact this (by omega_arith) rfl

/-- `out`'s bytes are kept by a change in the working space. -/
theorem out_frm {p : PP} {m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm p.B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hsep : ∀ x, ofs p.op x < p.L → p.Z ≤ ofs p.B x) (hL : p.L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p.op p.L = Spec.Rsa.bytesAt m p.op p.L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr' => Or.inr ?_
  have hi' := List.mem_range.mp hi
  have := hsep (p.op + BitVec.ofNat 64 i) (by simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; exact hi')
  have h2 := hr r hr'
  omega_arith

theorem Bufs.step {p : PP} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : Bufs p s)
    (hf : Frm p.B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (k : Keep regs s t) : Bufs p t where
  rdR := by rw [k.2.1, k.2.2]; exact h.rdR
  sepR := h.sepR
  bR := by rw [bytes_frm hf hr h.sepR]; exact h.bR
  bO := by rw [out_frm hf hr h.sepO (by have := h.oNW; omega_arith)]; exact h.bO
  oW := by rw [k.2.2]; exact h.oW
  oNW := h.oNW
  sepO := h.sepO
  scrU := h.scrU.congr k.2.2
  sepU := h.sepU
  stkR := h.stkR
  stkO := h.stkO
  stkU := h.stkU
  dOU := h.dOU

/-- Between the pieces: the working space at `s6`, the arguments, the
buffers and the bounds. -/
structure St (p : PP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  s6 : s.gpr .s6 = p.B
  args : Args s.mem p
  bufs : Bufs p s
  dims : Dims p
  ws : (⟨p.B, p.Z⟩ : Region) ∈ s.wr
  sp : s.sp = p.sp
  sp96 : 96 ≤ p.sp.toNat
  sp16 : p.sp.toNat % 16 = 0
  stkB : (stk p.sp).Disjoint ⟨p.B, p.Z⟩
  save : ∀ i < 13, word s.mem p.B (8 * p.n - saveBytes + 8 * i) = p.sv i

theorem mutR_le {p : PP} (h : Dims p) : ∀ r ∈ mutR p.n, r.1 + r.2 ≤ p.Z := by
  have := h.n
  intro r hr
  simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> dsimp only [PP.Z, saveBytes] <;> omega_arith

/-- `St` survives a piece that keeps `s6` and the stack pointer and changes
only `mutR` ranges of the working space. -/
theorem St.step {p : PP} {s t : State} {regs : List Reg} (h : St p s) (hf : Frm p.B (mutR p.n) s.mem t.mem)
    (k : Keep regs s t) (hsp : t.sp = s.sp) (h6 : Reg.s6 ∉ regs := by decide) : St p t where
  scr := h.scr.congr k.2.2
  s6 := (k.gpr h6).trans h.s6
  args := h.args.frm hf rfl
  bufs := h.bufs.step hf (mutR_le h.dims) k
  dims := h.dims
  ws := by rw [k.2.2]; exact h.ws
  sp := hsp.trans h.sp
  sp96 := h.sp96
  sp16 := h.sp16
  stkB := h.stkB
  save := fun i hi => by
    have := h.dims.n; have := h.dims.n'; have := h.dims.b1
    refine (hf.word_eq (fun r hr => .inr ?_) (by simp only [saveBytes]; omega_arith)).trans (h.save i hi)
    simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [saveBytes, PP.L] at * <;> omega_arith

/-- A header word of `St`'s working space: its load, its store and its
alignment. -/
theorem St.ld {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 d) 8 :=
  h.scr.ld (d := d) (by have := h.dims.n; simp only [PP.Z]; omega_arith)

theorem St.st {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s.wr (p.B + BitVec.ofNat 64 d) 8 :=
  h.scr.st (d := d) (by have := h.dims.n; simp only [PP.Z]; omega_arith)

theorem St.al {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) (h8 : d % 8 = 0) :
    (p.B + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  h.scr.al8 (d := d) (by have := h.dims.n; simp only [PP.Z]; omega_arith) h8

/-- The tape's first `k` bytes in memory. -/
theorem St.take_bytes {p : PP} {s : State} (h : St p s) {k : Nat} (hk : k ≤ p.r.length) :
    Spec.Rsa.bytesAt s.mem p.rp k = p.r.take k := by
  rw [← h.bufs.bR, Proof.Ffdh.take_bytesAt _ _ hk]

/-! ## The arguments, at their literal offsets -/

theorem Args.wsLen' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 p.n :=
  h.wsLen
theorem Args.out' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 16) 64 = p.op := h.out
theorem Args.len' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 p.L :=
  h.len
theorem Args.usedP' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 32) 64 = p.up := h.usedP
theorem Args.bits' {m : Mem} {p : PP} (h : Args m p) :
    m.readW (p.B + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 p.bits := h.bits
theorem Args.gen' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 p.g :=
  h.gen
theorem Args.rand' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 136) 64 = p.rp := h.rand
theorem Args.rlen' {m : Mem} {p : PP} (h : Args m p) :
    m.readW (p.B + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 p.r.length := h.rlen

/-! ## Words of the working space read through stores -/

theorem rw_off (m : Mem) (B : Addr) {a b : Nat} (v : BitVec 64) (hab : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a + 8 ≤ 2 ^ 64) (hb : b + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 a) v).readW (B + BitVec.ofNat 64 b) 64 = m.readW (B + BitVec.ofNat 64 b) 64 :=
  Mem.readW_writeW_sep (Offset.sep B (d := b) (e := a) (by simp only [Nat.reduceDiv]; omega) (by omega) (by omega))
    (by decide)

/-! ## A modulus's working space -/

/-- The working space of a modulus of `mb` bits: `w = ⌈mb / 64⌉`. -/
abbrev wOf (mb : Nat) : Nat := (mb + 63) / 64

/-- The header and the registers after `phase`. -/
structure Ph (p : PP) (mb : Nat) (s : State) : Prop where
  a7 : s.gpr .a7 = off p.B (slot (wOf mb) 0)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (wOf mb)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (wOf mb + 2))
  mbW : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb
  kW : word s.mem p.B (8 * hK) = BitVec.ofNat 64 ((mb + 7) / 8)
  wW : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)
  strideW : word s.mem p.B (8 * hStride) = BitVec.ofNat 64 (8 * (wOf mb + 2))
  arrW : ∀ j < 8, word s.mem p.B (8 * (8 + j)) = off p.B (slot (wOf mb) j)
  checksW : word s.mem p.B (8 * hChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb)
  topW : word s.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1)

/-- The bit length of the modulus: `bits − 1` for q, `bits` for p. -/
abbrev mbOf (p : PP) (q : Bool) : Nat := if q then p.bits - 1 else p.bits

theorem add_shr (x a k : Nat) (h : x + a < 2 ^ 64) :
    (BitVec.ofNat 64 x + BitVec.ofNat 64 a) >>> k = BitVec.ofNat 64 ((x + a) / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem checks_eq {mb : Nat} (h : mb ≤ 8192) :
    BitVec.ofNat 64 128 - ((BitVec.ofNat 64 mb - BitVec.ofNat 64 2048 - BitVec.ofNat 64 1) >>> 63) <<< 6 =
      BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb) := by
  unfold Spec.Ffdh.primeChecks
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have hm : mb % 2 ^ 64 = mb := Nat.mod_eq_of_lt (by omega_arith)
  rw [hm]
  split
  · have e : (2 ^ 64 - 1 % 2 ^ 64 + (2 ^ 64 - 2048 % 2 ^ 64 + mb) % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 1 := by
      omega_arith
    rw [e]; rfl
  · have e : (2 ^ 64 - 1 % 2 ^ 64 + (2 ^ 64 - 2048 % 2 ^ 64 + mb) % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 0 := by
      omega_arith
    rw [e]; rfl

/-- The registers `phaseHead` writes. -/
def phRegs : List Reg := [.t3, .t4, .t5, .t6, .t0, .s5, .a7]

/-- The ranges `phaseHead` changes: words 6–15, 21, 27, 28 and 31. -/
def phRanges : List (Nat × Nat) := [(48, 80), (168, 8), (216, 16), (248, 8)]

/-- `phaseHead`'s stores, for the modulus of `mb` bits in `t3`. -/
def phaseTail : List Instr :=
  [sth .t3 hMb, .addi .t4 .t3 7, .shift .srl .d .t4 .t4 3, sth .t4 hK, .addi .t4 .t3 63,
    .shift .srl .d .t4 .t4 6, sth .t4 hW, .addi .t0 .t4 0, .shift .sll .d .s5 .t4 3, .addi .s5 .s5 16,
    sth .s5 hStride, .addi .a7 .s6 hdrBytes, .addi .t5 .a7 0] ++
  (List.range 8).flatMap (fun j => [sth .t5 (8 + j), .add .t5 .t5 .s5]) ++
  [.addi .t5 .t3 (-2048), .addi .t5 .t5 (-1), .shift .srl .d .t5 .t5 63, .shift .sll .d .t5 .t5 6, .li .t6 128,
    .sub .t5 .t6 .t5, sth .t5 hChecks]

theorem phaseHead_eq (q : Bool) :
    phaseHead q = ([ldh .t3 hBits] ++ (if q then [.addi .t3 .t3 (-1)] else [])) ++ phaseTail := by
  simp only [phaseHead, phaseTail, List.append_assoc]

/-- What `phaseHead` leaves, for the modulus of `mb` bits. -/
def PhH (p : PP) (mb : Nat) (s t : State) : Prop :=
  (t.gpr .a7 = off p.B (slot (wOf mb) 0) ∧ t.gpr .t0 = BitVec.ofNat 64 (wOf mb) ∧
    t.gpr .s5 = BitVec.ofNat 64 (8 * (wOf mb + 2)) ∧
    word t.mem p.B (8 * hMb) = BitVec.ofNat 64 mb ∧
    word t.mem p.B (8 * hK) = BitVec.ofNat 64 ((mb + 7) / 8) ∧
    word t.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb) ∧
    word t.mem p.B (8 * hStride) = BitVec.ofNat 64 (8 * (wOf mb + 2)) ∧
    (∀ j < 8, word t.mem p.B (8 * (8 + j)) = off p.B (slot (wOf mb) j)) ∧
    word t.mem p.B (8 * hChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb) ∧
    Frm p.B phRanges s.mem t.mem) ∧ Keep phRegs s t

theorem phaseTail_ok {p : PP} {s : State} (h : St p s) {mb : Nat} (h3 : s.gpr .t3 = BitVec.ofNat 64 mb)
    (hm : mb ≤ 8192) : WP isa (.block phaseTail) s (PhH p mb s) := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold phaseTail
  simp only [List.flatMap, List.range, List.range.loop, List.map, List.flatten, List.cons_append, List.nil_append,
    List.append_eq, sth, hMb, hK, hW, hStride, hChecks, hdrBytes]
  have ew : (BitVec.ofNat 64 mb + BitVec.ofNat 64 63) >>> 6 = BitVec.ofNat 64 (wOf mb) :=
    add_shr _ _ _ (by omega_arith)
  have ek : (BitVec.ofNat 64 mb + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((mb + 7) / 8) :=
    add_shr _ _ _ (by omega_arith)
  have e5 : BitVec.ofNat 64 (wOf mb) <<< 3 + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (wOf mb + 2)) := by
    rw [VG.Proof.MillerRabin.RISCV64.Search.shl3_ofNat, BitVec.ofNat_add_ofNat]; congr 1
  brun [h.s6, h3, BitVec.add_zero,
    h.st (d := 248) (by decide), h.al (d := 248) (by decide) (by decide),
    h.st (d := 216) (by decide), h.al (d := 216) (by decide) (by decide),
    h.st (d := 48) (by decide), h.al (d := 48) (by decide) (by decide),
    h.st (d := 224) (by decide), h.al (d := 224) (by decide) (by decide),
    h.st (d := 64) (by decide), h.al (d := 64) (by decide) (by decide),
    h.st (d := 72) (by decide), h.al (d := 72) (by decide) (by decide),
    h.st (d := 80) (by decide), h.al (d := 80) (by decide) (by decide),
    h.st (d := 88) (by decide), h.al (d := 88) (by decide) (by decide),
    h.st (d := 96) (by decide), h.al (d := 96) (by decide) (by decide),
    h.st (d := 104) (by decide), h.al (d := 104) (by decide) (by decide),
    h.st (d := 112) (by decide), h.al (d := 112) (by decide) (by decide),
    h.st (d := 120) (by decide), h.al (d := 120) (by decide) (by decide),
    h.st (d := 168) (by decide), h.al (d := 168) (by decide) (by decide), ew, ek, e5,
    exec_li (show imm12 128 by decide), checks_eq hm]
  refine ⟨by simp [off, slot, hdrBytes], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  any_goals simp (disch := decide) only [word, off, rw_off, rw_self]
  · intro j hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    all_goals first
      | (simp (disch := decide) only [rw_off, rw_self, Nat.reduceMul, Nat.reduceAdd, VG.Proof.Mont.off, slot,
           hdrBytes]
         congr 2; omega_arith)
      | omega_arith
  · iterate 13 refine frm_writeW ?_ _ (by decide) (by decide)
    exact Frm.refl _ _ _

theorem phaseHead_ok {p : PP} {s : State} (h : St p s) (q : Bool) :
    WP isa (.block (phaseHead q)) s (PhH p (mbOf p q) s) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  rw [phaseHead_eq, WP.block_append_iff]
  have e1 : BitVec.ofNat 64 p.bits - BitVec.ofNat 64 1 = BitVec.ofNat 64 (p.bits - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have hld : WP isa (.block ([ldh .t3 hBits] ++ (if q then [.addi .t3 .t3 (-1)] else []))) s fun u =>
      (u.gpr .t3 = BitVec.ofNat 64 (mbOf p q) ∧ u.mem = s.mem) ∧ Keep [.t3] s u := by
    cases q
    · refine WP.keep _ ?_ (by rfl) (by rfl)
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, ldh, hBits, mbOf]
      brun [h.s6, h.ld (d := 40) (by decide), h.al (d := 40) (by decide) (by decide), h.args.bits']
    · refine WP.keep _ ?_ (by rfl) (by rfl)
      simp only [↓reduceIte, List.cons_append, List.nil_append, ldh, hBits, mbOf]
      brun [h.s6, h.ld (d := 40) (by decide), h.al (d := 40) (by decide) (by decide), h.args.bits', e1]
  refine WP.mono (WP.rdwr hld) fun u ⟨⟨⟨u3, um⟩, ku⟩, _, _, usp⟩ => ?_
  have hu := h.step (by rw [um]; exact Frm.refl _ _ _) ku usp
  refine WP.mono (phaseTail_ok hu u3 (by simp only [mbOf]; split <;> omega_arith))
    fun t ⟨⟨a, b, c, d, e, f, g, i, j, hf⟩, kt⟩ => ⟨⟨a, b, c, d, e, f, g, i, j, by rw [← um]; exact hf⟩,
      (ku.trans kt).mono (by decide)⟩

/-- `topMask`'s first block: its count `k = mb + 64 − 64 w` in `t3`. -/
theorem topT1_ok {p : PP} {s : State} (h : St p s) {mb : Nat}
    (hm : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb) (hw : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)) :
    WP isa (.block [ldh .t3 hMb, ldh .t4 hW, .shift .sll .d .t4 .t4 6, .sub .t3 .t3 .t4, .addi .t3 .t3 64, .li .t5 0]) s
      fun u => (u.gpr .t3 = BitVec.ofNat 64 (mb + 64 - 64 * wOf mb) ∧ u.gpr .t5 = BitVec.ofNat 64 0 ∧
        u.mem = s.mem) ∧ Keep [.t3, .t4, .t5] s u := by
  have hk1 : 1 ≤ mb + 64 - 64 * wOf mb := by simp only [wOf]; omega_arith
  have hk2 : mb + 64 - 64 * wOf mb ≤ 64 := by simp only [wOf]; omega_arith
  generalize hkd : mb + 64 - 64 * wOf mb = k at hk1 hk2 ⊢
  have ek : BitVec.ofNat 64 mb - BitVec.ofNat 64 (wOf mb) <<< 6 + BitVec.ofNat 64 64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [wOf] at hkd ⊢
    omega_arith
  refine WP.keep [.t3, .t4, .t5] ?_ (by rfl) (by rfl)
  simp only [ldh, hMb, hW]
  brun [h.s6, h.ld (d := 248) (by decide), h.al (d := 248) (by decide) (by decide), h.ld (d := 48) (by decide),
    h.al (d := 48) (by decide) (by decide),
    show s.mem.readW (p.B + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 mb from hm,
    show s.mem.readW (p.B + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (wOf mb) from hw, ek,
    exec_li (show imm12 0 by decide)]

/-- `topMask`: `hTop := 2^k − 1` for `k = mb + 64 − 64 w`, in 1..=64. -/
theorem topMask_ok {p : PP} {s : State} (h : St p s) {mb : Nat}
    (hm : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb) (hw : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)) :
    WP isa topMask s fun t =>
      (word t.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1) ∧
        Frm p.B [(8 * hTop, 8)] s.mem t.mem) ∧ Keep [.t3, .t4, .t5] s t := by
  have hk1 : 1 ≤ mb + 64 - 64 * wOf mb := by simp only [wOf]; omega_arith
  have hk2 : mb + 64 - 64 * wOf mb ≤ 64 := by simp only [wOf]; omega_arith
  unfold topMask
  refine WP.seq (WP.mono (topT1_ok h hm hw) fun u ⟨⟨u3, u5, um⟩, ku⟩ => ?_)
  generalize hkd : mb + 64 - 64 * wOf mb = k at hk1 hk2 u3 ⊢
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .t5 = BitVec.ofNat 64 (2 ^ i - 1) ∧ t.mem = s.mem) ∧ Keep [.t3, .t4, .t5] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .t3) (N := k) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t5, tm⟩, kt⟩ _ => ?_) ⟨⟨u5, um⟩, ku⟩ u3) fun t ⟨⟨t5, tm⟩, kt⟩ => ?_)
  · refine WP.mono (WP.keep [.t3, .t5] (Q := fun t' => t'.gpr .t5 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧
      t'.mem = t.mem ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
      fun t' ⟨⟨a, b, c⟩, k'⟩ => ⟨⟨⟨a, b.trans tm⟩, (kt.trans k').mono (by decide)⟩, c⟩
    brun [t5]
    apply BitVec.eq_of_toNat_eq
    have : 2 ^ i ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.pow_succ]
    omega_arith
  · have hs := h.scr.congr kt.2.2
    have hst : InRegions t.wr (p.B + BitVec.ofNat 64 192) 8 := by rw [kt.2.2]; exact h.st (d := 192) (by decide)
    have hal : (p.B + BitVec.ofNat 64 192).toNat % 8 = 0 := h.al (d := 192) (by decide) (by decide)
    refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (p.B + BitVec.ofNat 64 192) (t.gpr .t5)) ?_
      (by rfl) (by rfl)) fun t' ⟨e, k'⟩ => ⟨⟨?_, ?_⟩, (kt.trans k').mono (by decide)⟩
    · simp only [sth, hTop]
      brun [(kt.gpr (by decide)).trans h.s6, hst, hal]
    · show (t'.mem).readW (p.B + BitVec.ofNat 64 192) 64 = _
      rw [e, rw_self, t5]
    · rw [e, ← tm]; exact (frm_writeW (Frm.refl _ _ _) _ (by decide) (by decide))

theorem phRanges_mut (n : Nat) : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], InMut n r := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩
  all_goals exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide, by decide⟩

/-- `phase`: `Ph` for the modulus of `mbOf p q` bits. -/
theorem phase_ok {p : PP} {s : State} (h : St p s) (q : Bool) :
    WP isa (phase q) s fun t => ((St p t ∧ Ph p (mbOf p q) t ∧ Frm p.B (phRanges ++ [(8 * hTop, 8)]) s.mem t.mem) ∧
      Keep phRegs s t) ∧ t.sp = s.sp := by
  unfold phase
  refine WP.rdwr (WP.seq (WP.mono (WP.rdwr (phaseHead_ok h q))
    fun u ⟨⟨⟨u7, u0, u5, um, uk, uw, us, ua, uc, uf⟩, ku⟩, _, _, usp⟩ => ?_)) |>.mono fun t ⟨h, _, _, hsp⟩ => ⟨h, hsp⟩
  have fu : Frm p.B (mutR p.n) s.mem u.mem := Frm.toMut (uf.mono fun r hr => List.mem_append_left _ hr)
    (phRanges_mut p.n)
  have hu := h.step fu ku usp
  refine WP.mono (WP.rdwr (topMask_ok hu um uw)) fun t ⟨⟨⟨tt, tf⟩, kt⟩, _, _, tsp⟩ => ?_
  have ft : Frm p.B (mutR p.n) u.mem t.mem := Frm.toMut (tf.mono fun r hr => List.mem_append_right _ hr)
    (phRanges_mut p.n)
  have e : ∀ {d : Nat}, d + 8 ≤ 192 ∨ (200 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word u.mem p.B d := fun hd =>
    tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp only [hTop]; omega_arith) (by omega_arith)
  refine ⟨⟨hu.step ft kt tsp, ⟨(kt.gpr (by decide)).trans u7, (kt.gpr (by decide)).trans u0,
    (kt.gpr (by decide)).trans u5, (e (by simp only [hMb]; omega_arith)).trans um,
    (e (by simp only [hK]; omega_arith)).trans uk, (e (by simp only [hW]; omega_arith)).trans uw,
    (e (by simp only [hStride]; omega_arith)).trans us, fun j hj => (e (by omega_arith)).trans (ua j hj),
    (e (by simp only [hChecks]; omega_arith)).trans uc, tt⟩,
    (uf.mono fun r hr => List.mem_append_left _ hr).trans (tf.mono fun r hr => List.mem_append_right _ hr)⟩,
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
