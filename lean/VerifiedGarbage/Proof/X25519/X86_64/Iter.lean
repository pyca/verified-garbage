module

public import VerifiedGarbage.Proof.X25519.X86_64.Env
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64: an iteration of the ladder

The start of an iteration (`stepPre`): the counter `rbx` counts down to the
bit `t`, whose byte of the array `BITS` is `k_t`; `swap ^ k_t` becomes the
mask in `rcx`, and `k_t` the new `swap` (a word at `SWAP`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)]

theorem ea_bits {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    s.ea { base := .rdi, index := some .rbx, disp := BITS } = off base (BITS + t) := by
  simp only [State.ea, hr, hb, off, BITS, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t 768]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 255)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block stepPre) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rcx = mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.rbx, .rax, .rdx, .rcx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  apply WP.of_runBlock
  simp only [stepPre, runBlock_cons, runStep_some, exec, readSrc, execAlu, State.load8,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hb', Option.bind_some]
  rw [ea_bits (base := base) (t := t) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_false, reduceCtorEq, hs.rdi]) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_true])]
  have hswap' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, hin, hbit, hr, hw, hswap', ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', State.setReg32]
  have e0 : BitVec.setWidth 64 (0 : BitVec 32) = 0 := rfl
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek], rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem cmp_eq : ∀ a < 2, ∀ b < 2,
    ((BitVec.ofNat 8 a).setWidth 64 - BitVec.ofNat 64 b == 0) = decide (a = b) := by decide

/-- `bitCmp`: the counter `rbx` down to the bit `t`, ZF set if `k_t` equals
the old `swap`, and `k_t` the new `swap`. -/
theorem bitCmp_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 255)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block bitCmp) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.zf = some (decide (kt = sw0)) ∧
      (∀ r, r ∉ [.rbx, .rax] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  apply WP.of_runBlock
  simp only [bitCmp, runBlock_cons, runStep_some, exec, readSrc, execAlu, State.load8,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hb', Option.bind_some]
  rw [ea_bits (base := base) (t := t) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_false, reduceCtorEq, hs.rdi]) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_true])]
  have hswap' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, RegUpd.zf_arithFlags, hs.rdi, hin, hbit, hr, hw,
    hswap', ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [cmp_eq kt hk sw0 hsw], fun r hr => ?_, trivial, trivial, by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

variable {fld : Field} (hf : FieldOk fld)

/-- The sums and differences of both points, then `dmsn`. -/
def ops1 (fld : Field) : List Instr :=
  subCmov (32 * (8 : Fin 128).val) (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  addCmov (32 * (7 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  subCmov (32 * (4 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  addCmov (32 * (6 : Fin 128).val) (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.mul (32 * (9 : Fin 128).val) (32 * (7 : Fin 128).val) (32 * (8 : Fin 128).val)

/-- The rest of the iteration, from the choice of the point to double. -/
def ops2 (fld : Field) : List Instr :=
  mux (32 * (10 : Fin 128).val) (32 * (8 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  mux (32 * (3 : Fin 128).val) (32 * (6 : Fin 128).val) (32 * (7 : Fin 128).val) ++
  fld.mul (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  fld.sqr (32 * (10 : Fin 128).val) (32 * (10 : Fin 128).val) ++
  subCmov (32 * (6 : Fin 128).val) (32 * (9 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  fld.sqr (32 * (3 : Fin 128).val) (32 * (3 : Fin 128).val) ++
  addCmov (32 * (5 : Fin 128).val) (32 * (9 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  fld.sqr (32 * (6 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  subCmov (32 * (9 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (10 : Fin 128).val) ++
  fld.sqr (32 * (5 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  fld.a24add (32 * (4 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (9 : Fin 128).val) ++
  fld.mul (32 * (3 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (10 : Fin 128).val) ++
  fld.mul (32 * (6 : Fin 128).val) (32 * (6 : Fin 128).val) (32 * (2 : Fin 128).val) ++
  fld.mul (32 * (4 : Fin 128).val) (32 * (9 : Fin 128).val) (32 * (4 : Fin 128).val)

theorem step_eq : step fld =
    ops1 fld ++ (bitCmp ++ (ops2 fld ++ ([.alu .cmp .rbx (.imm 3)] : List Instr))) := by
  simp only [step, ops1, ops2, List.append_assoc]
  rfl

/-- The slots after `ops1`. -/
def env1 (e : Env) : Env :=
  opMul 9 7 8 (opAdd 6 5 6 (opSub 4 3 4 (opAdd 7 3 4 (opSub 8 5 6 e))))

/-- The slots after `ops2`, with ZF `zf`. -/
def env2 (zf : Bool) (e : Env) : Env :=
  opMul 4 9 4 (opMul 6 6 2 (opMul 3 3 10 (opA24Add 4 3 9 (opMul 5 5 5 (opSub 9 3 10
    (opMul 6 6 6 (opAdd 5 9 5 (opMul 3 3 3 (opSub 6 9 5 (opMul 10 10 10 (opMul 5 6 4
    (opMux 3 6 7 zf (opMux 10 8 4 zf e)))))))))))))

include hf in
theorem ops1_ok {s1 : State} {base : Addr} (hs1 : Scr s1 base)
    (hz2 : fe s1.mem base 128 ≤ 2 * Spec.X25519.P) (hz3 : fe s1.mem base 192 ≤ 2 * Spec.X25519.P) :
    WP isa (.block (ops1 fld)) s1 fun s' =>
      Keep base s1 s' ∧ E s'.mem base = env1 (E s1.mem base) := by
  simp only [ops1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (subCmovE hs1 8 5 6 ⟨by decide, by decide⟩ hz3) fun s2 ⟨k2, e2, o2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (addCmovE hs2 7 3 4 ⟨by decide, by decide⟩
    (.inr (by change fe s2.mem base 128 ≤ _; rw [o2.fe (by decide) (by decide)]; exact hz2)))
    fun s3 ⟨k3, e3, o3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (subCmovE hs3 4 3 4 ⟨by decide, by decide⟩
    (by change fe s3.mem base 128 ≤ _
        rw [o3.fe (by decide) (by decide), o2.fe (by decide) (by decide)]; exact hz2))
    fun s4 ⟨k4, e4, o4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (addCmovE hs4 6 5 6 ⟨by decide, by decide⟩
    (.inr (by change fe s4.mem base 192 ≤ _
              rw [o4.fe (by decide) (by decide), o3.fe (by decide) (by decide),
                o2.fe (by decide) (by decide)]; exact hz3)))
    fun s5 ⟨k5, e5, _⟩ => ?_
  have hs5 := k5.scr hs4
  refine WP.mono (mulE hf hs5 9 7 8 ⟨by decide, by decide⟩) fun s6 ⟨k6, e6⟩ => ?_
  exact ⟨k2.trans (k3.trans (k4.trans (k5.trans k6))), by rw [e6, e5, e4, e3, e2]; rfl⟩

include hf in
theorem ops2_ok {s1 : State} {base : Addr} (hs1 : Scr s1 base) {zf : Bool}
    (hz : s1.zf = some zf) :
    WP isa (.block (ops2 fld)) s1 fun s' =>
      Keep base s1 s' ∧ E s'.mem base = env2 zf (E s1.mem base) ∧
        fe s'.mem base 128 ≤ 2 * Spec.X25519.P ∧ fe s'.mem base 192 ≤ 2 * Spec.X25519.P := by
  simp only [ops2, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (muxEB hs1 10 8 4 ⟨by decide, by decide⟩ hz) fun s2 ⟨k2, e2, _, _, z2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (muxEB hs2 3 6 7 ⟨by decide, by decide⟩ (z2.trans hz))
    fun s3 ⟨k3, e3, _, _, _⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (mulEB hf hs3 5 6 4 ⟨by decide, by decide⟩) fun s4 ⟨k4, e4, _, b4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf hs4 10 10 ⟨by decide, by decide⟩) fun s5 ⟨k5, e5, o5, b5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (subCmovE hs5 6 9 5 ⟨by decide, by decide⟩
    (by change fe s5.mem base 160 ≤ _; rw [o5.fe (by decide) (by decide)]; exact b4))
    fun s6 ⟨k6, e6, o6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf hs6 3 3 ⟨by decide, by decide⟩) fun s7 ⟨k7, e7, o7, _⟩ => ?_
  have hs7 := k7.scr hs6
  rw [WP.block_append_iff]
  refine WP.mono (addCmovE hs7 5 9 5 ⟨by decide, by decide⟩
    (.inr (by change fe s7.mem base 160 ≤ _
              rw [o7.fe (by decide) (by decide), o6.fe (by decide) (by decide),
                o5.fe (by decide) (by decide)]; exact b4)))
    fun s8 ⟨k8, e8, o8⟩ => ?_
  have hs8 := k8.scr hs7
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf hs8 6 6 ⟨by decide, by decide⟩) fun s9 ⟨k9, e9, o9, _⟩ => ?_
  have hs9 := k9.scr hs8
  rw [WP.block_append_iff]
  refine WP.mono (subCmovE hs9 9 3 10 ⟨by decide, by decide⟩
    (by change fe s9.mem base 320 ≤ _
        rw [o9.fe (by decide) (by decide), o8.fe (by decide) (by decide),
          o7.fe (by decide) (by decide), o6.fe (by decide) (by decide)]; exact b5))
    fun s10 ⟨k10, e10, _⟩ => ?_
  have hs10 := k10.scr hs9
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf hs10 5 5 ⟨by decide, by decide⟩) fun s11 ⟨k11, e11, _, _⟩ => ?_
  have hs11 := k11.scr hs10
  rw [WP.block_append_iff]
  refine WP.mono (a24AddEB hf hs11 4 3 9 ⟨by decide, by decide⟩) fun s12 ⟨k12, e12, _⟩ => ?_
  have hs12 := k12.scr hs11
  rw [WP.block_append_iff]
  refine WP.mono (mulEB hf hs12 3 3 10 ⟨by decide, by decide⟩) fun s13 ⟨k13, e13, _, _⟩ => ?_
  have hs13 := k13.scr hs12
  rw [WP.block_append_iff]
  refine WP.mono (mulEB hf hs13 6 6 2 ⟨by decide, by decide⟩) fun s14 ⟨k14, e14, _, b14⟩ => ?_
  have hs14 := k14.scr hs13
  refine WP.mono (mulEB hf hs14 4 9 4 ⟨by decide, by decide⟩) fun s15 ⟨k15, e15, o15, b15⟩ => ?_
  refine ⟨k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans (k9.trans
    (k10.trans (k11.trans (k12.trans (k13.trans (k14.trans k15)))))))))))), ?_, b15, ?_⟩
  · rw [e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2]
    rfl
  · rw [o15.fe (by decide) (by decide)]; exact b14

/-- The ladder's loop invariant, with the counter `rbx = n`: the slots
`x1, x2, z2, x3, z3` (2–6) and the word `swap` hold the ladder's state after
the bits 254 down to `n`, and since the loop's start (`s₀`) nothing else
changed but the registers `clob` and the bytes `[64, 648)`. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 584 s₀.mem s.mem
  x1 : E s.mem base 2 = u
  x2 : E s.mem base 3 = (ladderAfter k u n).x2
  z2 : E s.mem base 4 = (ladderAfter k u n).z2
  x3 : E s.mem base 5 = (ladderAfter k u n).x3
  z3 : E s.mem base 6 = (ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap
  /-- `z_2` and `z_3` are at most `2p` (`addCmov`, `subCmov`). -/
  z2b : fe s.mem base 128 ≤ 2 * Spec.X25519.P
  z3b : fe s.mem base 192 ≤ 2 * Spec.X25519.P

theorem cswap_fst (sw : Nat) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X25519.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X25519.cswap, decide_eq_true_eq]; split <;> rfl

theorem cmp3_eq (n : Nat) (hn : n < 255) :
    (BitVec.ofNat 64 n - (3 : BitVec 32).signExtend 64 == 0) = decide (n = 3) := by
  have e3 : (3 : BitVec 32).signExtend 64 = BitVec.ofNat 64 3 := by decide
  rw [e3]
  by_cases h : n = 3
  · subst h; rfl
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro h'
    have h2 := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at h2
    omega

/-- The slots of the ladder's variables after an iteration (with the word
`swap`, slot 20, written in between) are those of `ladderStep`: whichever point
`mux` chooses to double, the addition of the two is the same. -/
theorem stepEnv_eval (e : Env) (st : Spec.X25519.Ladder) (k : Nat) (u : Spec.X25519.Fe) (t : Nat)
    (hsw : st.swap ≤ 1) (v : Spec.X25519.Fe)
    (h2 : e 2 = u) (h3 : e 3 = st.x2) (h4 : e 4 = st.z2) (h5 : e 5 = st.x3) (h6 : e 6 = st.z3) :
    env2 (decide (bit k t = st.swap)) (Function.update (env1 e) 20 v) 2 = u ∧
    env2 (decide (bit k t = st.swap)) (Function.update (env1 e) 20 v) 3 =
      (Spec.X25519.ladderStep k u st t).x2 ∧
    env2 (decide (bit k t = st.swap)) (Function.update (env1 e) 20 v) 4 =
      (Spec.X25519.ladderStep k u st t).z2 ∧
    env2 (decide (bit k t = st.swap)) (Function.update (env1 e) 20 v) 5 =
      (Spec.X25519.ladderStep k u st t).x3 ∧
    env2 (decide (bit k t = st.swap)) (Function.update (env1 e) 20 v) 6 =
      (Spec.X25519.ladderStep k u st t).z3 := by
  have hb := bit_le k t
  rw [ladderStep_eq]
  rcases (by omega : st.swap = 0 ∨ st.swap = 1) with hs | hs <;>
    rcases (by omega : bit k t = 0 ∨ bit k t = 1) with hk | hk <;>
    simp only [hs, hk, env1, env2, opMul, opAdd, opSub, opA24Add, opMux, Function.update_apply,
      Spec.X25519.cswap, h2, h3, h4, h5, h6, ↓reduceIte, decide_true, decide_false,
      Fin.reduceEq, Nat.reduceXor, reduceCtorEq] <;>
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> grind

include hf in
/-- One iteration of the ladder: from the state after the bits down to
`n + 1` to the state after the bits down to `n`. -/
theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {n : Nat} (hn : n < 255)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : LInv base k u s₀ s (n + 1)) :
    WP isa (.block (step fld)) s fun s' => LInv base k u s₀ s' n ∧ s'.zf = some (decide (n = 3)) := by
  have hs := hi.scr
  rw [step_eq, WP.block_append_iff]
  refine WP.mono (ops1_ok hf hs hi.z2b hi.z3b) fun s1 ⟨K1, e1⟩ => ?_
  have hs1 := K1.scr hs
  have hbit : s1.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    have hx : ofs base (off base (BITS + n)) = BITS + n :=
      ofs_off' base (by simp only [BITS]; omega)
    rw [K1.mem _ (by rw [hx]; simp only [BITS]; omega),
      hi.mem _ (by rw [hx]; simp only [BITS]; omega)]
    exact hbits n hn
  have hswap : word s1.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u (n + 1)).swap := by
    rw [K1.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega)]; exact hi.swap
  have hsw := ladderAfter_swap_le k u (n := n + 1) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (bitCmp_ok hs1 hn ((K1.gpr _ (by decide)).trans hi.rbx)
    (by have := bit_le k n; omega) (by omega) hbit hswap)
    fun s2 ⟨b2, z2, g2, rd2, wr2, mem2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have o8 : Outside base 640 8 s1.mem s2.mem := by
    rw [mem2]; exact writeW_outside _ _ _ (by omega)
  have e2 : E s2.mem base = Function.update (E s1.mem base) 20 (F s2.mem base (32 * 20)) :=
    E_update (o := 20) (o8.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (ops2_ok hf hs2 z2) fun s3 ⟨K3, e3, bz2, bz3⟩ => ?_
  have hs3 := K3.scr hs2
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  obtain ⟨v2, v3, v4, v5, v6⟩ := stepEnv_eval (E s.mem base) (ladderAfter k u (n + 1)) k u n hsw
    (F s2.mem base (32 * 20)) hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  rw [← ladderAfter_step k u hn, ← e1, ← e2, ← e3] at v3 v4 v5 v6
  rw [← e1, ← e2, ← e3] at v2
  refine ⟨⟨⟨hs3.rdi, hs3.wr, hs3.nowrap⟩, fun r hr hb => ?_, ?_, ?_, ?_, ?_, v2, v3, v4, v5, v6, ?_,
    by rw [RegUpd.mem_arithFlags]; exact bz2, by rw [RegUpd.mem_arithFlags]; exact bz3⟩, ?_⟩
  · have h' : r ∉ [Reg.rbx, .rax] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hb, fun h => hr (h ▸ by decide)⟩
    rw [RegUpd.gpr_arithFlags, K3.gpr r hr, g2 r h', K1.gpr r hr, hi.gpr r hr hb]
  · rw [RegUpd.gpr_arithFlags, K3.gpr _ (by decide), b2]
  · rw [RegUpd.rd_arithFlags, K3.rd, rd2, K1.rd, hi.rd]
  · rw [RegUpd.wr_arithFlags, K3.wr, wr2, K1.wr, hi.wr]
  · rw [RegUpd.mem_arithFlags]
    exact hi.mem.trans ((K1.mem.mono (by omega) (by omega)).trans
      ((o8.mono (by omega) (by omega)).trans (K3.mem.mono (by omega) (by omega))))
  · rw [RegUpd.mem_arithFlags, K3.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega),
      mem2, ladderAfter_step k u hn]
    simp only [X86_64.word, Mem.readW_writeW_self64]
    rfl
  · rw [RegUpd.zf_arithFlags, K3.gpr .rbx (by decide), b2, cmp3_eq n hn]

include hf in
/-- The ladder's loop, from the counter `n ≥ 4` down to 3. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 4 ≤ n → n ≤ 255 → LInv base k u s₀ s n →
      WP isa (.loop (.block (step fld)) .ne) s fun s' => LInv base k u s₀ s' 3 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block (step fld)) (c := .ne)
    (Q := fun s' => LInv base k u s₀ s' 3)
    (fun m (s : State) => 4 ≤ m ∧ m ≤ 255 ∧ LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (step_ok hf (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  by_cases hm : m = 3
  · subst hm; exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false hm, Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-- What a ladder leaves (`ladder`'s, or `vg_x25519_ifma`'s): the slots
`x2, z2, x3, z3` (3–6) and the word `swap` hold the ladder's final state,
and since its start (`s₀`) nothing else changed but the registers `clob` and
`rbx`, and the bytes `[64, 2216)`. -/
structure LPost (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s₀ s : State) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 2152 s₀.mem s.mem
  /-- The word `swap` is some `sw`, by which the last swap of the slots makes
  `(x_2, z_2)` the ladder's result: the final state's, or (`sw = 0`) the
  result itself. -/
  res : ∃ sw < 2, word s.mem base SWAP = BitVec.ofNat 64 sw ∧
    (Spec.X25519.cswap sw (E s.mem base 3) (E s.mem base 5)).1 =
      (Spec.X25519.cswap (ladderAfter k u 0).swap (ladderAfter k u 0).x2
        (ladderAfter k u 0).x3).1 ∧
    (Spec.X25519.cswap sw (E s.mem base 4) (E s.mem base 6)).1 =
      (Spec.X25519.cswap (ladderAfter k u 0).swap (ladderAfter k u 0).z2
        (ladderAfter k u 0).z3).1

/-- `LPost` from the ladder's final state in the slots 3–6 and `swap`. -/
theorem LPost.of {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {s₀ s : State} (scr : Scr s base)
    (gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr)
    (mem : Outside base 64 2152 s₀.mem s.mem)
    (x2 : E s.mem base 3 = (ladderAfter k u 0).x2) (z2 : E s.mem base 4 = (ladderAfter k u 0).z2)
    (x3 : E s.mem base 5 = (ladderAfter k u 0).x3) (z3 : E s.mem base 6 = (ladderAfter k u 0).z3)
    (swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u 0).swap) :
    LPost base k u s₀ s :=
  ⟨scr, gpr, rd, wr, mem, _, by have := ladderAfter_swap_le k u (n := 0) (by omega); omega, swap,
    by rw [x2, x3], by rw [z2, z3]⟩

theorem LInv.post {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {s₀ s : State} (h : LInv base k u s₀ s 0) :
    LPost base k u s₀ s :=
  LPost.of h.scr h.gpr h.rd h.wr (h.mem.mono (by decide) (by decide)) h.x2 h.z2 h.x3 h.z3 h.swap

/-- What a ladder starts from: the bits of `k` in `BITS`, `x1 = u` and the
ladder's first state in the slots 2–6, and `swap = 0`. -/
structure LPre (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s : State) : Prop where
  scr : Scr s base
  bits : ∀ t < 255, s.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)
  x1 : E s.mem base 2 = u
  x2 : E s.mem base 3 = 1
  z2 : E s.mem base 4 = 0
  x3 : E s.mem base 5 = u
  z3 : E s.mem base 6 = 1
  swap : word s.mem base SWAP = 0
  /-- `z_2` and `z_3` are at most `2p`, as `ladder`'s sums need. -/
  z2b : fe s.mem base 128 ≤ 2 * Spec.X25519.P
  z3b : fe s.mem base 192 ≤ 2 * Spec.X25519.P
  /-- The bits clamping clears (RFC 7748 §5, `decodeScalar25519`). -/
  low : bit k 0 = 0 ∧ bit k 1 = 0 ∧ bit k 2 = 0

/-! ## The iterations for bits 2, 1 and 0 -/

/-- The doubling of RFC 7748's ladder, of `(x, z)`. -/
def dblPt (x z : Spec.X25519.Fe) : Spec.X25519.Fe × Spec.X25519.Fe :=
  let A := x + z
  let AA := A * A
  let B := x - z
  let BB := B * B
  let E := AA - BB
  (AA * BB, E * (AA + Spec.X25519.a24 * E))

/-- An iteration for a clear bit doubles the point the swap chooses, and
leaves the swap clear. -/
theorem ladderStep_zero (k : Nat) (x1 : Spec.X25519.Fe) (st : Spec.X25519.Ladder) (t : Nat)
    (hb : bit k t = 0) :
    (Spec.X25519.ladderStep k x1 st t).x2 =
        (dblPt (Spec.X25519.cswap st.swap st.x2 st.x3).1
          (Spec.X25519.cswap st.swap st.z2 st.z3).1).1 ∧
      (Spec.X25519.ladderStep k x1 st t).z2 =
        (dblPt (Spec.X25519.cswap st.swap st.x2 st.x3).1
          (Spec.X25519.cswap st.swap st.z2 st.z3).1).2 ∧
      (Spec.X25519.ladderStep k x1 st t).swap = 0 := by
  rw [ladderStep_eq, hb, Nat.xor_zero]
  exact ⟨rfl, rfl, rfl⟩

def dblList (fld : Field) : List Instr :=
  addCmov (32 * (7 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  subCmov (32 * (8 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  fld.sqr (32 * (7 : Fin 128).val) (32 * (7 : Fin 128).val) ++
  fld.sqr (32 * (8 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  subCmov (32 * (9 : Fin 128).val) (32 * (7 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  fld.a24add (32 * (4 : Fin 128).val) (32 * (7 : Fin 128).val) (32 * (9 : Fin 128).val) ++
  fld.mul (32 * (3 : Fin 128).val) (32 * (7 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  fld.mul (32 * (4 : Fin 128).val) (32 * (9 : Fin 128).val) (32 * (4 : Fin 128).val)

theorem dbl_eq : dbl fld = dblList fld := by
  simp only [dbl, dblList]
  rfl

/-- The slots after `dbl`. -/
def dblEnv (e : Env) : Env :=
  opMul 4 9 4 (opMul 3 7 8 (opA24Add 4 7 9 (opSub 9 7 8 (opMul 8 8 8 (opMul 7 7 7
    (opSub 8 3 4 (opAdd 7 3 4 e)))))))

theorem dblEnv_vals (e : Env) :
    dblEnv e 3 = (dblPt (e 3) (e 4)).1 ∧ dblEnv e 4 = (dblPt (e 3) (e 4)).2 := by
  simp only [dblEnv, opMul, opAdd, opSub, opA24Add, Function.update_apply, Fin.reduceEq,
    ↓reduceIte, dblPt]
  exact ⟨trivial, trivial⟩

include hf in
/-- `dbl`, for `z_2` at most `2p`, which it leaves so. -/
theorem dbl_ok {s1 : State} {base : Addr} (hs1 : Scr s1 base)
    (hz2 : fe s1.mem base 128 ≤ 2 * Spec.X25519.P) :
    WP isa (.block (dbl fld)) s1 fun s' =>
      Keep base s1 s' ∧ E s'.mem base = dblEnv (E s1.mem base) ∧
        fe s'.mem base 128 ≤ 2 * Spec.X25519.P := by
  rw [dbl_eq]
  simp only [dblList, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addCmovE hs1 7 3 4 ⟨by decide, by decide⟩ (.inr hz2)) fun s2 ⟨k2, e2, o2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (subCmovE hs2 8 3 4 ⟨by decide, by decide⟩
    (by change fe s2.mem base 128 ≤ _; rw [o2.fe (by decide) (by decide)]; exact hz2))
    fun s3 ⟨k3, e3, _⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf hs3 7 7 ⟨by decide, by decide⟩) fun s4 ⟨k4, e4, _, _⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (sqrEB hf hs4 8 8 ⟨by decide, by decide⟩) fun s5 ⟨k5, e5, _, b5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (subCmovE hs5 9 7 8 ⟨by decide, by decide⟩ b5) fun s6 ⟨k6, e6, _⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (a24AddEB hf hs6 4 7 9 ⟨by decide, by decide⟩) fun s7 ⟨k7, e7, _⟩ => ?_
  have hs7 := k7.scr hs6
  rw [WP.block_append_iff]
  refine WP.mono (mulEB hf hs7 3 7 8 ⟨by decide, by decide⟩) fun s8 ⟨k8, e8, _, _⟩ => ?_
  have hs8 := k8.scr hs7
  refine WP.mono (mulEB hf hs8 4 9 4 ⟨by decide, by decide⟩) fun s9 ⟨k9, e9, _, b9⟩ => ?_
  exact ⟨k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans k9)))))),
    by rw [e9, e8, e7, e6, e5, e4, e3, e2]; rfl, b9⟩

theorem cmp0_eq : ∀ a < 2, (BitVec.ofNat 64 a - (0 : BitVec 32).signExtend 64 == 0) =
    decide (a = 0) := by decide

/-- The start of `tail`: ZF set if `swap = 0`. -/
theorem tailPre_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block ([.mov .rax (.mem (sc SWAP)), .alu .cmp .rax (.imm 0)] : List Instr)) s
      fun s' => s'.zf = some (decide (sw = 0)) ∧ s'.mem = s.mem ∧ Keep base s s' := by
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hw' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw := hw
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64, ea_sc,
    RegUpd.gpr_setReg_self, RegUpd.zf_arithFlags, hs.rdi, hr, hw', ite_true, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [cmp0_eq sw hsw], rfl, fun r hr' => ?_, rfl, rfl, Outside.refl _ _ _ _⟩
  have : r ≠ .rax := fun h => hr' (h ▸ by decide)
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, this, ite_false]

/-- The end of `tail`: `swap = 0`. -/
theorem clrSwap_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.mov32 .rax (.imm 0), .store (sc SWAP) .rax] : List Instr)) s fun s' =>
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    hs.rdi, hw, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, trivial, trivial⟩
  simp only [hr, ite_false]

theorem E_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Fin 128)
    (hi : 32 * i.val + 32 ≤ o ∨ o + n ≤ 32 * i.val) : E m' base i = E m base i := by
  simp only [E, F]; rw [h.fe hi (by omega)]

theorem cswap_fst' {sw : Nat} (hsw : sw < 2) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).1 = if decide (sw = 0) then a else b := by
  rcases (by omega : sw = 0 ∨ sw = 1) with rfl | rfl <;> rfl

include hf in
/-- `tail`, from the state after bit 3, for a scalar whose bits 2, 1, 0 are
clear: `(x_2, z_2)` the ladder's result, and `swap = 0`. -/
theorem tail_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}
    (hi : LInv base k u s₀ s 3) (h0 : bit k 0 = 0) (h1 : bit k 1 = 0) (h2 : bit k 2 = 0) :
    WP isa (.block (tail fld)) s (LPost base k u s₀) := by
  have hs := hi.scr
  have hsw := ladderAfter_swap_le k u (n := 3) (by omega)
  simp only [tail, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tailPre_ok hs (by omega) hi.swap) fun s1 ⟨z1, m1, K1⟩ => ?_
  have hs1 := K1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (muxEB hs1 3 5 3 ⟨by decide, by decide⟩ z1) fun s2 ⟨K2, e2, o2, _, z2⟩ => ?_
  have hs2 := K2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (muxEB hs2 4 6 4 ⟨by decide, by decide⟩ (z2.trans z1))
    fun s3 ⟨K3, e3, _, f3, _⟩ => ?_
  have hs3 := K3.scr hs2
  have b3 : fe s3.mem base 128 ≤ 2 * Spec.X25519.P := by
    change fe s3.mem base (32 * (4 : Fin 128).val) ≤ _
    rw [f3, o2.fe (by decide) (by decide), o2.fe (by decide) (by decide), m1]
    split
    · exact hi.z2b
    · exact hi.z3b
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok hf hs3 b3) fun s4 ⟨K4, e4, b4⟩ => ?_
  have hs4 := K4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok hf hs4 b4) fun s5 ⟨K5, e5, b5⟩ => ?_
  have hs5 := K5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok hf hs5 b5) fun s6 ⟨K6, e6, _⟩ => ?_
  have hs6 := K6.scr hs5
  refine WP.mono (clrSwap_ok hs6) fun s7 ⟨m7, g7, rd7, wr7⟩ => ?_
  have o7 : Outside base 640 8 s6.mem s7.mem := by
    rw [m7]; exact writeW_outside _ _ _ (by omega)
  have K := K1.trans (K2.trans (K3.trans (K4.trans (K5.trans K6))))
  -- The point chosen, then doubled three times.
  have c3 : E s3.mem base 3 = (Spec.X25519.cswap (ladderAfter k u 3).swap
      (ladderAfter k u 3).x2 (ladderAfter k u 3).x3).1 := by
    rw [e3, opMux, Function.update_of_ne (by decide), e2, opMux, Function.update_self,
      cswap_fst' (by omega), m1, hi.x2, hi.x3]
  have c4 : E s3.mem base 4 = (Spec.X25519.cswap (ladderAfter k u 3).swap
      (ladderAfter k u 3).z2 (ladderAfter k u 3).z3).1 := by
    rw [e3, opMux, Function.update_self, e2, opMux, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), cswap_fst' (by omega), m1, hi.z2, hi.z3]
  obtain ⟨a2, b2', w2⟩ := ladderStep_zero k u (ladderAfter k u 3) 2 h2
  obtain ⟨a1, b1', w1⟩ := ladderStep_zero k u (ladderAfter k u 2) 1 h1
  obtain ⟨a0, b0, w0⟩ := ladderStep_zero k u (ladderAfter k u 1) 0 h0
  rw [← ladderAfter_step k u (n := 2) (by decide)] at a2 b2' w2
  rw [← ladderAfter_step k u (n := 1) (by decide)] at a1 b1' w1
  rw [← ladderAfter_step k u (n := 0) (by decide)] at a0 b0 w0
  simp only [w2, w1, Spec.X25519.cswap, Nat.zero_ne_one, ite_false] at a1 b1' a0 b0
  obtain ⟨v4x, v4z⟩ := dblEnv_vals (E s3.mem base)
  obtain ⟨v5x, v5z⟩ := dblEnv_vals (E s4.mem base)
  obtain ⟨v6x, v6z⟩ := dblEnv_vals (E s5.mem base)
  have x7 : E s7.mem base 3 = (ladderAfter k u 0).x2 := by
    rw [E_out o7 3 (Or.inl (by decide)), e6, v6x, e5, v5x, v5z, e4, v4x, v4z, c3, c4, a0, a1,
      b1', a2, b2']
  have z7 : E s7.mem base 4 = (ladderAfter k u 0).z2 := by
    rw [E_out o7 4 (Or.inl (by decide)), e6, v6z, e5, v5x, v5z, e4, v4x, v4z, c3, c4, b0, a1,
      b1', a2, b2']
  refine ⟨⟨(g7 _ (by decide)).trans hs6.rdi, wr7 ▸ hs6.wr, hs.nowrap⟩, fun r hr hb => ?_, ?_, ?_,
    ?_, 0, by decide, by rw [m7]; simp only [X86_64.word, Mem.readW_writeW_self64], ?_, ?_⟩
  · rw [g7 r (fun h => hr (h ▸ by decide)), K.gpr r hr, hi.gpr r hr hb]
  · rw [rd7, K.rd, hi.rd]
  · rw [wr7, K.wr, hi.wr]
  · exact (hi.mem.mono (by decide) (by decide)).trans ((K.mem.mono (by decide) (by decide)).trans
      (o7.mono (by decide) (by decide)))
  · simp only [Spec.X25519.cswap, Nat.zero_ne_one, ite_false, w0]; exact x7
  · simp only [Spec.X25519.cswap, Nat.zero_ne_one, ite_false, w0]; exact z7

include hf in
/-- `ladder`, as a ladder: from `LPre` to `LPost`. -/
theorem ladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} (h : LPre base k u s) :
    WP isa (ladder fld) s (LPost base k u s) := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 255)]) s (fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 255 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s' ⟨hb, g, m, rd, wr⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hf h.bits 255 s' (by omega) (by omega)
    ⟨⟨by rw [g _ (by decide)]; exact h.scr.rdi, by rw [wr]; exact h.scr.wr, h.scr.nowrap⟩,
      fun r _ hr => g r hr, hb, rd, wr, by rw [m]; exact Outside.refl _ _ _ _, by rw [m, h.x1],
      by rw [m, h.x2]; rfl, by rw [m, h.z2]; rfl, by rw [m, h.x3]; rfl, by rw [m, h.z3]; rfl,
      by rw [m, h.swap]; rfl, by rw [m]; exact h.z2b, by rw [m]; exact h.z3b⟩)
    fun _ hl => tail_ok hf hl h.low.1 h.low.2.1 h.low.2.2)

end VG.Proof.X25519.X86_64
