module

import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Impl.Sha256.X86_64.Stream
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Sha256.X86_64.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.Sha256.X86_64.Stream
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Sha256.X86_64.Contract
meta import VerifiedGarbage.Proof.Sha256.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming SHA-256 on x86-64: common lemmas

What the streaming code needs of the compression function it calls, for
either `Callee`, and memory written byte by byte.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset contains_offset' toNat_ofNat_lt compress_verified)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## The compression functions -/

/-- What the streaming code needs of the compression function it calls: that
it is correct and constant time, does not touch `rsp` or the stack, and keeps
`rdi` and `rcx`. -/
structure _root_.VG.Impl.Sha256.X86_64.Stream.Callee.Ok (f : Callee) : Prop where
  verified : ∀ s, Proof.Sha256.compressX86_64.pre s →
    ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ Proof.Sha256.compressX86_64.post s s'
  ct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub f.code
  nosp : NoSp f.code
  depth : f.code.depth = 0
  keeps_rdi : ∀ i ∈ instrs f.code, Taint.clobbers i .rdi = false
  keeps_rcx : ∀ i ∈ instrs f.code, Taint.clobbers i .rcx = false

/-- The facts about the instructions of `f`, from one kernel check each. -/
theorem _root_.VG.Impl.Sha256.X86_64.Stream.Callee.Ok.of_verified {f : Callee} (hv : ∀ s, Proof.Sha256.compressX86_64.pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ Proof.Sha256.compressX86_64.post s s')
    (hct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub f.code)
    (hk : ((instrs f.code).all fun i => !Taint.clobbers i .rdi && !Taint.clobbers i .rcx &&
      !Taint.clobbers i .rsp) = true)
    (hd : f.code.depth = 0) : f.Ok := by
  have h := fun i hi => List.all_eq_true.mp hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨hv, hct, fun i hi => (h i hi).2, hd, fun i hi => (h i hi).1.1, fun i hi => (h i hi).1.2⟩

theorem scalar_ok : Callee.scalar.Ok :=
  .of_verified compress_verified.1 compress_verified.2.1
    (by change (instrs Impl.Sha256.X86_64.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha256.X86_64.compress.depth = 0; lit_decide)

theorem shani_ok : Callee.shani.Ok :=
  .of_verified Proof.Sha256.X86_64.ShaNi.compress_verified.1
    Proof.Sha256.X86_64.ShaNi.compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-! ## One instruction at a time

Weakest-precondition rules for the instruction forms used here, exposing
only what changes, so that proofs about a block stay small. -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.zf = s.zf → s'.cf = s.cf →
    WP isa (.block is) s' Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.zf = s.zf →
    s'.cf = s.cf → WP isa (.block is) s' Q) : WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

end

/-! ## Lemmas shared by `update` and `finalize` -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

end VG.Proof.Sha256.X86_64.Stream
