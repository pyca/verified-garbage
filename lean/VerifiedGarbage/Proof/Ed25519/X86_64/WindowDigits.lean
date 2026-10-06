import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Ed25519.X86_64.RecodeStep

/-!
# Verification's digits at the counter's position

`digitAt dst` loads the digit's byte at the counter's position `p` (byte `2048 + 2p + dst`) into
`rbx` and tests it; `digitsAt` tests both digits at once (`rbx` = their bytes' `or`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps)

theorem counter_ok {s : State} {base : Addr} (hs : Scratch s base) {p : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) :
    WP isa (.block [.mov .rax (.mem (Impl.X25519.X86_64.sc 56)), .alu .add .rax (.reg .rax)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (2 * p) ∧ Keeps [.rax] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hs.rdi, hr, hc, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [← BitVec.ofNat_add]; congr 1; omega, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

private theorem byte_ofNat : ∀ b : BitVec 8, b.setWidth 64 = BitVec.ofNat 64 b.toNat := by decide

private theorem byte_zero : ∀ b : BitVec 8, (b.setWidth 64 == 0) = decide (b.toNat = 0) := by decide

theorem bytes_or_zero (b c : BitVec 8) :
    (b.setWidth 64 ||| c.setWidth 64 == 0) = decide (b.toNat = 0 ∧ c.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at this
    have hb := b.isLt
    have hc := c.isLt
    omega
  · intro ⟨hb, hc⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_setWidth, hb, hc]
    rfl

theorem ea_dig {s : State} {base : Addr} (hs : s.gpr .rdi = base) {p : Nat}
    (hr : s.gpr .rax = BitVec.ofNat 64 (2 * p)) {d0 : Int} {d : Nat}
    (hd : BitVec.ofInt 64 d0 = BitVec.ofNat 64 d) :
    s.ea { base := .rdi, index := some .rax, disp := d0 } = off base (d + 2 * p) := by
  simp only [State.ea, hs, hr, hd]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm (2 * p)]

/-- The digit's byte at the counter's position `p`, tested. -/
theorem digitAt_ok {s : State} {base : Addr} (hs : Scratch s base) {p dst : Nat} (hp : p < 528)
    (hdst : dst < 2) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) :
    WP isa (.block (digitAt dst)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (dig s.mem base dst p) ∧
      t.zf = some (decide (dig s.mem base dst p = 0)) ∧ Keeps [.rax, .rbx] s t := by
  rw [show digitAt dst = [.mov .rax (.mem (Impl.X25519.X86_64.sc 56)), .alu .add .rax (.reg .rax)] ++
    [.movzx8 .rbx { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) },
      .alu .test .rbx (.reg .rbx)] from rfl, WP.block_append_iff]
  refine WP.mono (counter_ok hs hc) fun a ⟨ar, ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  have he := ea_dig ha.rdi ar (d0 := ((2048 + dst : Nat) : Int)) (d := 2048 + dst) (BitVec.ofInt_natCast _ _)
  rw [show 2048 + dst + 2 * p = 2048 + 2 * p + dst by omega] at he
  generalize ((2048 + dst : Nat) : Int) = d0 at he ⊢
  have hrg : InRegions (a.rd ++ a.wr) (off base (2048 + 2 * p + dst)) 1 :=
    ⟨_, List.mem_append_right _ ha.wr, Offset.contains_base _ (show 2048 + 2 * p + dst + 1 ≤ 8192 by omega)
      (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, he,
    RegUpd.gpr_setReg, RegUpd.zf_arithFlags, RegUpd.gpr_arithFlags, hrg, BitVec.and_self, byte_zero,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ka.2.1]
  refine ⟨byte_ofNat _, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2, ite_false]
  exact ka.1 r (by simpa using hr.1)

/-- Both digits' bytes at the counter's position `p`, ZF set if both are zero. -/
theorem digitsAt_ok {s : State} {base : Addr} (hs : Scratch s base) {p : Nat} (hp : p < 528)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) :
    WP isa (.block digitsAt) s fun t =>
      t.zf = some (decide (dig s.mem base 0 p = 0 ∧ dig s.mem base 1 p = 0)) ∧
        Keeps [.rax, .rbx, .rcx] s t := by
  rw [show digitsAt = [.mov .rax (.mem (Impl.X25519.X86_64.sc 56)), .alu .add .rax (.reg .rax)] ++
    [.movzx8 .rbx { base := .rdi, index := some .rax, disp := 2048 },
      .movzx8 .rcx { base := .rdi, index := some .rax, disp := 2049 },
      .alu .or .rbx (.reg .rcx)] from rfl, WP.block_append_iff]
  refine WP.mono (counter_ok hs hc) fun a ⟨ar, ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  have he0 := ea_dig ha.rdi ar (d0 := 2048) (d := 2048) rfl
  have he1 := ea_dig (s := a.setReg .rbx ((a.mem (off base (2048 + 2 * p))).setWidth 64))
    (by simp only [RegUpd.gpr_setReg, reduceCtorEq, ite_false]; exact ha.rdi)
    (by simp only [RegUpd.gpr_setReg, reduceCtorEq, ite_false]; exact ar) (d0 := 2049) (d := 2049) rfl
  generalize (2048 : Int) = d0 at he0 ⊢
  generalize (2049 : Int) = d1 at he1 ⊢
  have hrg (d : Nat) (hd : d < 2050) : InRegions (a.rd ++ a.wr) (off base (d + 2 * p)) 1 :=
    ⟨_, List.mem_append_right _ ha.wr, Offset.contains_base _ (show d + 2 * p + 1 ≤ 8192 by omega)
      (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, he0, he1,
    RegUpd.gpr_setReg, RegUpd.zf_arithFlags, RegUpd.zf_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, hrg 2048 (by decide), hrg 2049 (by decide), reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', bytes_or_zero]
  refine ⟨by rw [ka.2.1]; simp only [dig, show 2048 + 2 * p + 0 = 2048 + 2 * p by omega,
      show 2048 + 2 * p + 1 = 2049 + 2 * p by omega], fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2.1, hr.2.2, ite_false]
  exact ka.1 r (by simpa using hr.1)

/-- ZF set if the counter `p` is zero. -/
theorem counterTest_ok {s : State} {base : Addr} (hs : Scratch s base) {p : Nat} (hp : p < 2 ^ 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) :
    WP isa (.block batchTest) s fun t => t.zf = some (decide (p = 0)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by omega)⟩
  have hz : (BitVec.ofNat 64 p == 0) = decide (p = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hp]
  apply WP.of_runBlock
  simp only [batchTest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc,
    BitVec.and_self, hz, ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.Ed25519.X86_64
