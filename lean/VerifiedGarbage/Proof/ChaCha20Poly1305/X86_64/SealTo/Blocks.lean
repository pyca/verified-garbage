import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealTo
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ

/-!
# ChaCha20-Poly1305 encryption with part of the data read from elsewhere, x86-64: the blocks

`sealTo` (`Impl/ChaCha20Poly1305/X86_64/SealTo.lean`) runs as `seal` with two
more stack arguments, `src` (`sp`) and `src_len` (`SL`): what its entry
state must satisfy besides `seal`'s `APre` (`ToPre`), the bytes it encrypts
(`PTat`: `[mm, mm + PP)` from `src`, the rest from the data), and the
straight-line blocks of `oop`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

section
variable (s₀ : State)
/-- `src` and `src_len`, `[rsp + 24]` and `[rsp + 32]`. -/
abbrev sp : Addr := stackArg s₀ 2
abbrev SL : Nat := (stackArg s₀ 3).toNat
abbrev spR : Region := ⟨sp s₀, SL s₀⟩
/-- The two stack arguments. -/
abbrev arg2R : Region := ⟨stackArgAddr s₀ 2, 16⟩
/-- The bytes encrypted with the keystream from the prologue, and those read
from `src`. -/
abbrev mm : Nat := mOf 960 1024 (L s₀)
abbrev PP : Nat := if 960 < L s₀ ∧ mm s₀ < SL s₀ then (SL s₀ - mm s₀) / 1024 * 1024 else 0
end

/-- The bytes encrypted, in memory `m`: `[mm, mm + PP)` from `src`, the rest
from the data. -/
def PTat (s₀ : State) (m : Mem) : List Byte :=
  (List.range (L s₀)).map fun k =>
    if mm s₀ ≤ k ∧ k < mm s₀ + PP s₀ then m (sp s₀ + BitVec.ofNat 64 k) else m (dp s₀ + BitVec.ofNat 64 k)

/-- What `sealTo` needs besides `seal`'s precondition: `src_len` at most the
length, `src` and the stack arguments readable, and apart from what the code
writes. -/
structure ToPre (s₀ : State) : Prop where
  hp : APre true s₀
  g2 : arg2R s₀ ∈ s₀.rd
  s_rd : spR s₀ ∈ s₀.rd
  le : SL s₀ ≤ L s₀
  s_c : (spR s₀).Disjoint (ctxR s₀)
  s_d : (spR s₀).Disjoint (dR s₀)
  s_k : (spR s₀).Disjoint (stkR s₀)
  g_c : (arg2R s₀).Disjoint (ctxR s₀)
  g_d : (arg2R s₀).Disjoint (dR s₀)
  g_t : (arg2R s₀).Disjoint (tR s₀)
  g_k : (arg2R s₀).Disjoint (stkR s₀)
  wrap_s : (sp s₀).toNat + SL s₀ ≤ 2 ^ 64

theorem PP_le (s₀ : State) (hle : SL s₀ ≤ L s₀) : mm s₀ + PP s₀ ≤ L s₀ := by
  have := mOf_le_len 960 1024 (L s₀)
  simp only [PP]
  split <;> omega

theorem PP_le_SL (s₀ : State) (hpos : 0 < PP s₀) : mm s₀ + PP s₀ ≤ SL s₀ := by
  simp only [PP] at hpos ⊢
  split at hpos
  · rw [ite_eq_left ‹_›]; have := Nat.div_mul_le_self (SL s₀ - mm s₀) 1024; omega
  · omega

theorem PP_dvd (s₀ : State) : 1024 ∣ PP s₀ := by
  simp only [PP]; split
  · exact Nat.dvd_mul_left _ _
  · exact Nat.dvd_zero _

theorem mm_dvd {s₀ : State} (hbig : 960 < L s₀) : 64 ∣ mm s₀ := by
  rw [mm, mOf_big (by omega)]; exact splitOf_dvd _ _ _

/-! ## The first block of `oop` -/

theorem sub_ofNat_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 (a - b) = BitVec.ofNat 64 b := by
  rw [Offset.ofNat_sub_ofNat (by omega), show a - (a - b) = b by omega]

/-- `m` (the bytes before the call's) into `rbx`, `src_len` into `rax`, and
`CF` set if `src_len < m`. -/
theorem oop1_ok {s₀ : State} (hT : ToPre s₀) {m : Nat} {s : State} (h : XArgsM s₀ m s)
    (hrd : s.rd = s₀.rd) (hS : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa (.block [.mov .rbx (.reg .r13), .alu .sub .rbx (.reg .rdx), .mov .rax (.mem (at_ .rsp 32)),
      .alu .cmp .rax (.reg .rbx)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 m ∧ s'.gpr .rax = BitVec.ofNat 64 (SL s₀) ∧
      (∀ q, q ≠ .rbx → q ≠ .rax → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      s'.cf = some (decide (SL s₀ < m)) := by
  have hL9 := (s₀.gpr .r9).isLt
  have hle := h.le
  have ea : off (s.gpr .rsp) 32 = stackArgAddr s₀ 3 := by
    rw [h.rsp, off_eq]; rfl
  have i₁ : InRegions (s.rd ++ s.wr) (stackArgAddr s₀ 3) 8 := by
    refine ⟨arg2R s₀, by rw [hrd]; simp [hT.g2], ?_⟩
    simp only [stackArgAddr]
    rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1)) = s₀.gpr .rsp + BitVec.ofNat 64 (8 * (2 + 1)) +
      BitVec.ofNat 64 8 by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.contains_base _ (by lit_omega) (by lit_omega)
  have hrbx : s.gpr .r13 - s.gpr .rdx = BitVec.ofNat 64 m := by
    rw [h.r13, h.rdx, hL s₀]; exact sub_ofNat_ofNat hle hL9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, ea_at, ea, i₁, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.cf_arithFlags, reduceCtorEq, ↓reduceIte,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', hS, hrbx]
  refine ⟨trivial, by simp [SL], fun q h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial, ?_⟩
  simp [SL, toNat_ofNat_lt (show m < 2 ^ 64 by simp only [L] at hle; omega)]


theorem shr_shl10 (r : Nat) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r >>> 10 <<< 10 = BitVec.ofNat 64 (r / 1024 * 1024) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hr]

/-- `P`, `src_len - m` rounded down to a multiple of 1024, into `rax`, with
`ZF` set if it is 0. -/
theorem oop2_ok {a m : Nat} (hma : m ≤ a) (ha : a < 2 ^ 64) {s : State} (hrax : s.gpr .rax = BitVec.ofNat 64 a)
    (hrbx : s.gpr .rbx = BitVec.ofNat 64 m) :
    WP isa (.block [.alu .sub .rax (.reg .rbx), .shift .shr .rax 10, .shift .shl .rax 10,
      .alu .test .rax (.reg .rax)]) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 ((a - m) / 1024 * 1024) ∧ (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.zf = some (decide ((a - m) / 1024 * 1024 = 0)) := by
  have hs : BitVec.ofNat 64 a - BitVec.ofNat 64 m = BitVec.ofNat 64 (a - m) := Offset.ofNat_sub_ofNat hma
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift, arithFlags,
    State.setReg, State.setFlags, ↓reduceIte, Nat.reduceLeDiff, and_self, hrax, hrbx, hs,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self,
    shr_shl10 _ (show a - m < 2 ^ 64 by omega)]
  refine ⟨trivial, fun q h => by simp [h], trivial, trivial, trivial, ?_⟩
  rw [← Offset.ofNat_sub_ofNat_beq (x := (a - m) / 1024 * 1024) (y := 0) (by omega) (by decide)]
  simp


/-! ## The loop's arguments -/

theorem zcopy_ok {s : State} {c : Addr} (hr15 : s.gpr .r15 = c) (hi : InRegions (s.rd ++ s.wr) (off c 64) 64)
    (ho : InRegions s.wr (off c 608) 64) :
    WP isa (.block ([.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0] : List Instr)) s
      fun s' => s'.mem = s.mem.writeW (off c 608) (s.mem.readW (off c 64) 512) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at, hr15, hi, ite_true,
    Option.map_some, State.store512_eq, State.setZ_wr, State.setZ_gpr, State.setZ_mem, ho,
    StraightZ.zmm_load, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem oopArgs_eq : oopArgs =
    ([.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0] : List Instr) ++
    (([.mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx), .mov .rcx (.reg .r14),
      .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] : List Instr) ++ ptr .rdi .r15 608 ++
      ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr)) := rfl

/-- The registers of the loop's arguments, and `m + P` in `rbx`. -/
theorem oopG_ok {s₀ : State} {s : State} {m P : Nat}
    (hr15 : s.gpr .r15 = cx s₀) (hr14 : s.gpr .r14 = dp s₀) (hrbx : s.gpr .rbx = BitVec.ofNat 64 m)
    (hrax : s.gpr .rax = BitVec.ofNat 64 P) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hS : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hi : InRegions (s.rd ++ s.wr) (stackArgAddr s₀ 2) 8) :
    WP isa (.block (([.mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx), .mov .rcx (.reg .r14),
      .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] : List Instr) ++ ptr .rdi .r15 608 ++
      ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr))) s fun s' =>
      s'.gpr .rsi = sp s₀ + BitVec.ofNat 64 m ∧ s'.gpr .rcx = dp s₀ + BitVec.ofNat 64 m ∧
      s'.gpr .rdx = BitVec.ofNat 64 P ∧ s'.gpr .rdi = off (cx s₀) 608 ∧ s'.gpr .r9 = off (cx s₀) 128 ∧
      s'.gpr .rbx = BitVec.ofNat 64 (m + P) ∧
      (∀ q, q ≠ .rsi → q ≠ .rcx → q ≠ .rdx → q ≠ .rdi → q ≠ .r9 → q ≠ .rbx → s'.gpr q = s.gpr q) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : off (s.gpr .rsp) 24 = stackArgAddr s₀ 2 := by rw [hrsp, off_eq]; rfl
  apply WP.of_runBlock
  simp only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, State.load64, ea_at, ea, hi, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', hS, hr15, hr14, hrbx, hrax, se_ofNat (show 608 < 2 ^ 31 by omega_using []),
    se_ofNat (show 128 < 2 ^ 31 by omega_using [])]
  refine ⟨trivial, trivial, trivial, by rw [off_eq], by rw [off_eq], by rw [BitVec.ofNat_add], fun q h₁ h₂ h₃ h₄ h₅ h₆ => ?_,
    trivial, trivial, trivial⟩
  simp [h₁, h₂, h₃, h₄, h₅, h₆]

/-- The arguments of the call for the data after its first `m' = rbx`
bytes: as `cryptB_ok`. -/
theorem restArgs_ok {e : Bool} {s₀ : State} (hp : APre e s₀) {s : State} {m : Nat} (hm : m ≤ L s₀)
    (hrbx : s.gpr .rbx = BitVec.ofNat 64 m) (hr15 : s.gpr .r15 = cx s₀) (hr14 : s.gpr .r14 = dp s₀)
    (hr13 : s.gpr .r13 = s₀.gpr .r9) (hwr : s.wr = s₀.wr) :
    WP isa (.block restArgs) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (BitVec.ofNat 32 (m / 64 + 1)) ∧
      s'.gpr .rdi = off (cx s₀) 64 ∧ s'.gpr .rsi = off (dp s₀) m ∧
      s'.gpr .rdx = BitVec.ofNat 64 (L s₀ - m) ∧ s'.gpr .rcx = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← hwr] at o
  simp only [off] at o
  have hL9 := (s₀.gpr .r9).isLt
  have hLl : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hw : (BitVec.ofNat 64 (m / 64) + BitVec.signExtend 64 (1 : BitVec 32)).setWidth 32 =
      BitVec.ofNat 32 (m / 64 + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (show m / 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show m / 64 + 1 < 2 ^ 64 by omega)]
  apply WP.of_runBlock
  simp only [restArgs, ptr, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, ea_at, readSrc, execAlu, execShift, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, hr15, hr14, hr13, hrbx, o, reduceCtorEq,
    ↓reduceIte, Nat.reduceLeDiff, and_self, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 64 < 2 ^ 31 by omega_using []), se_ofNat (show 128 < 2 ^ 31 by omega_using []),
    shr6_ofNat (show m < 2 ^ 64 by simp only [L] at hm; omega), hw]
  refine ⟨trivial, by rw [off_eq], by rw [off_eq], ?_, by rw [off_eq], fun r hr => ?_, trivial⟩
  · rw [hL s₀]; exact Offset.ofNat_sub_ofNat hm
  · have := calleeSaved_ne hr
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

end VG.Proof.ChaCha20Poly1305.X86_64
