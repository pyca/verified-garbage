module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops

/-! The word-at-a-time tail of short gather encryption. Both source words
are read before either write, so both stores carry exactly the same ciphertext. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64

abbrev advance (k : Nat) : List Instr :=
  [ptr .x0 .x0 k, ptr .x1 .x1 k, ptr .x2 .x2 k, ptr .x3 .x3 k]

abbrev blockData : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x1 0, .vop (.logic .eor .v0 .v0 .v1),
   .strq .v0 .x2 0, .strq .v0 .x3 0]

abbrev byteData : List Instr :=
  [.ldrb .x14 .x0 0, .ldrb .x15 .x1 0, .logic .eor .w .x14 .x14 .x15,
   .strb .x14 .x2 0, .strb .x14 .x3 0]

abbrev blockStep := blockData ++ advance 16 ++ [.subImm .x .x13 .x13 1]
abbrev byteStep := byteData ++ advance 1 ++ [.subImm .x .x12 .x12 1]

/-- Memory and register obligations of all four XOR widths. -/
structure Access (s : State) (n : Nat) : Prop where
  src : InRegions (s.rd ++ s.wr) (s.gpr .x0) n
  key : InRegions (s.rd ++ s.wr) (s.gpr .x1) n
  dst : InRegions s.wr (s.gpr .x2) n
  auth : InRegions s.wr (s.gpr .x3) n

def putBoth (s : State) (n : Nat) : Mem :=
  let ct := s.mem.read (s.gpr .x0) n ^^^ s.mem.read (s.gpr .x1) n
  (s.mem.write (s.gpr .x2) n ct).write (s.gpr .x3) n ct

structure Kept (s t : State) (regs : List Reg) : Prop where
  gpr : ∀ r, r ∉ regs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

structure Wrote (s : State) (n : Nat) (regs : List Reg) (t : State) : Prop extends Kept s t regs where
  mem : t.mem = putBoth s n

set_option linter.unusedSimpArgs false in
theorem blockData_ok (s : State) (h : Access s 16) :
    WP isa (.block blockData) s (Wrote s 16 []) := by
  apply WP.of_runBlock
  simp only [blockData, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, ↓reduceIte, BitVec.add_zero,
    h.src, h.key, h.dst, h.auth, Option.map_some, Option.bind_some,
    rd_setV, wr_setV, mem_setV, gpr_setV, VOp.eval, v_setV, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, ?_⟩
  simp [putBoth, State.setV]

set_option linter.unusedSimpArgs false in
theorem byteData_ok (s : State) (h : Access s 1) :
    WP isa (.block byteData) s (Wrote s 1 [.x14, .x15]) := by
  apply WP.of_runBlock
  simp only [byteData, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, ↓reduceIte, BitVec.add_zero,
    h.src, h.key, h.dst, h.auth, Option.map_some, Option.bind_some, gpr_write, mem_write, rd_write, wr_write,
    BitVec.setWidth_eq, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2]
  · simp [putBoth, State.write, State.read, Size.bits, byte_xor]

/-- Permissions for the second word in a potentially overlapping pair. -/
structure OffsetAccess (s : State) (d : Addr) (n : Nat) : Prop where
  src : InRegions (s.rd ++ s.wr) (s.gpr .x0 + d) n
  key : InRegions (s.rd ++ s.wr) (s.gpr .x1 + d) n
  dst : InRegions s.wr (s.gpr .x2 + d) n
  auth : InRegions s.wr (s.gpr .x3 + d) n

def wordAt (s : State) (n : Nat) (d : Addr) :=
  s.mem.read (s.gpr .x0 + d) n ^^^ s.mem.read (s.gpr .x1 + d) n

def placeWord (s : State) (m : Mem) (d : Addr) (n : Nat) (v : BitVec (8*n)) : Mem :=
  (m.write (s.gpr .x2 + d) n v).write (s.gpr .x3 + d) n v

abbrev endRegs : List Reg := [.x0,.x1,.x2,.x3,.x12,.x13,.x14,.x15]

/-- Both XORs use entry memory, including when the plaintext occupies the
output buffer. The two writes then agree on the bytes the words share. -/
theorem xorEnds_ok (sz : Size) (s : State) (d : Addr)
    (h : Access s (sz.bits/8)) (q : OffsetAccess s d (sz.bits/8))
    (delta : s.gpr .x12 - BitVec.ofNat 64 (sz.bits/8) = d) :
    let n := sz.bits/8
    WP isa (.block (DirectGather.xorEnds sz n)) s fun t =>
      Kept s t endRegs ∧ (∀ r ∈ ([.x0,.x1,.x2,.x3] : List Reg), t.gpr r = s.gpr r + d) ∧
      t.mem = placeWord s (placeWord s s.mem 0 n (wordAt s n 0)) d n (wordAt s n d) := by
  cases sz <;> apply WP.of_runBlock
  all_goals
    simp only [Size.bits,Nat.reduceDiv] at h q delta
    simp only [DirectGather.xorEnds,runBlock_cons,runStep_some,runBlock_nil,exec,addr,State.load,
      State.store,State.read,Size.bits,Size.bytes,Nat.reduceDiv,Nat.reduceMod,Nat.reduceMul,
      Nat.reduceLT,and_self,↓reduceIte,BitVec.add_zero,h.src,h.key,h.dst,h.auth,
      Option.map_some,Option.bind_some,gpr_write,mem_write,rd_write,wr_write,BitVec.setWidth_eq,
      reduceCtorEq,Option.some.injEq,exists_eq_left',delta,q.src,q.key,q.dst,q.auth]
  all_goals
    refine ⟨⟨?_, rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro r hr
      simp only [endRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp_all only [gpr_write, ite_false]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
    · simp [placeWord, wordAt,
        BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide)]

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment
