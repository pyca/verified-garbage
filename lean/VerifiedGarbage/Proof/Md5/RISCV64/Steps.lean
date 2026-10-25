module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Md5.Spec
public import VerifiedGarbage.Impl.Md5.RISCV64
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# MD5 compression function on RISC-V: the 64 operations

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Md5/PPC64LE/Compress.lean`): each operation is the auxiliary
function of its round, symbolically executed once per round (`fn_ok`),
between the loads and additions before it (`head_ok`) and the rotation and
addition after it (`tail_ok`), each symbolically executed once for all
operations. The words are the low 32 bits of the registers (`Vars`).
-/

@[expose] public section

namespace VG.Proof.Md5.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Md5.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the low 32 bits of the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3]

/-- The pointers, the count, the return address and the callee-saved
registers: never written by the operations. -/
def pubRegs : List Reg := [.a0, .a1, .a2, .a3, .ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8,
  .s9, .s10, .s11]

/-- The words move one register along each operation. -/
theorem var_succ (t k : Nat) (hk : k < 3) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 3 := by
  simp only [var]; congr 1; omega

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 4 - t % 4) % 4]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ .a1 ∧ ∀ p ∈ pubRegs, r ≠ p := by
  decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne' _ (var_mem t k)).1

theorem var_ne_T1 (t k : Nat) : var t k ≠ T1 := (work_ne' _ (var_mem t k)).2.1

theorem var_ne_T2 (t k : Nat) : var t k ≠ T2 := (work_ne' _ (var_mem t k)).2.2.1

theorem var_ne_a1 (t k : Nat) : var t k ≠ .a1 := (work_ne' _ (var_mem t k)).2.2.2.1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne' _ (var_mem t k)).2.2.2.2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .t0 ≠ work.getD ((j + 4 - c) % 4) .t0 := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

theorem pub_ne' : ∀ p ∈ pubRegs, p ≠ T0 ∧ p ≠ T1 ∧ p ≠ T2 := by decide

/-! ## The auxiliary functions -/

/-- The low word of `-1`. -/
theorem lo_m1 : (BitVec.ofInt 64 (-1)).setWidth 32 = 0xffffffff := by decide

theorem fn_ok (r : Nat) (hr : r < 4) (a b c d : Reg) (ha : a ≠ T0) (hb : b ≠ T0) (hc : c ≠ T0)
    (hd : d ≠ T0) (hab : a ≠ b) (had : a ≠ d)
    (s : State) (va vb vc vd : Word) (h₀ : (s.gpr a).setWidth 32 = va) (h₁ : (s.gpr b).setWidth 32 = vb)
    (h₂ : (s.gpr c).setWidth 32 = vc) (h₃ : (s.gpr d).setWidth 32 = vd) :
    WP isa (.block (fn r a b c d)) s fun s' =>
      (s'.gpr a).setWidth 32 = va + roundFn r vb vc vd ∧
      (∀ x, x ≠ a → x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  have hda : d ≠ a := fun h => had h.symm
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp only [fn, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_add,
    exec_logicImm (show imm12 (-1) by decide), RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, ha, hb, hc, hd, hba, hda, ↓reduceIte, Option.some.injEq,
    exists_eq_left'] <;>
  refine ⟨?_, fun x hx hx' => by simp [hx, hx'], trivial, trivial, trivial⟩ <;>
  simp only [lo32_add, lo32_xor, lo32_and, lo32_or, lo_m1, h₀, h₁, h₂, h₃]
  · rw [show roundFn 0 = F from rfl, Proof.Md5.F_eq]
  · rw [show roundFn 1 = G from rfl, Proof.Md5.G_add, BitVec.add_assoc]
  · rw [show roundFn 2 = H from rfl, Proof.Md5.H_eq']
  · rw [show roundFn 3 = I from rfl, Proof.Md5.I_eq]

/-! ## The rest of an operation -/

/-- The instructions of an operation before the auxiliary function. -/
def headI (a : Reg) (k : Nat) (T : Word) : List Instr :=
  loadLE32 T1 T2 .a1 (4 * k) ++ (.add a a T1 :: li32 T1 T ++ [.add a a T1])

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (n : Nat) : List Instr :=
  [.shift .sll .w T0 a n, .shift .srl .w a a (32 - n), .logic .or a a T0, .add a a b]

theorem step_split (t : Nat) :
    step t = headI (var t 0) (ks.getD t 0) (Ts.getD t 0) ++
      (fn (t / 16) (var t 0) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (Proof.Md5.rot t)) := by
  simp only [step, headI, tailI, List.append_assoc, List.cons_append]; rfl

theorem head_ok (a : Reg) (k : Nat) (hk : k < 16) (T : Word) (ha₁ : a ≠ T1) (ha₂ : a ≠ T2)
    (s : State) (va x : Word) (bp : Addr) (h₁ : (s.gpr a).setWidth 32 = va)
    (hr1 : s.gpr .a1 = bp) (hin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4)
    (hx : s.mem.readW (bp + BitVec.ofNat 64 (4 * k)) 32 = x) :
    WP isa (.block (headI a k T)) s fun s' =>
      (s'.gpr a).setWidth 32 = va + x + T ∧
      (∀ r, r ≠ a → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  unfold headI
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega) (by rw [hr1]; exact hin))
    fun s₁ e => ?_
  subst e
  apply WP.of_runBlock
  simp only [li32, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec_add, exec_lui, exec_addiw_lo12, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, ha₁, ha₂, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr hr' hr'' => by simp [hr, hr', hr''], trivial, trivial, trivial⟩
  simp only [lo32_add, lo32_ext, lo32_sext, li32_val, h₁, hx, hr1]

theorem tail_ok (a b : Reg) (n : Nat) (hn0 : 0 < n) (hn : n < 32) (hab : a ≠ b) (ha : a ≠ T0) (hb : b ≠ T0)
    (s : State) (va vb : Word) (h₁ : (s.gpr a).setWidth 32 = va) (h₂ : (s.gpr b).setWidth 32 = vb) :
    WP isa (.block (tailI a b n)) s fun s' =>
      (s'.gpr a).setWidth 32 = va.rotateLeft n + vb ∧
      (∀ r, r ≠ a → r ≠ T0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  have hTa : T0 ≠ a := fun h => ha h.symm
  apply WP.of_runBlock
  simp only [tailI, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
    exec_shift_w hn, exec_shift_w (show 32 - n < 32 by omega), RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, ha, hb, hba, hTa, ↓reduceIte, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr hr' => by simp [hr, hr'], trivial, trivial, trivial⟩
  simp only [lo32_add, lo32_or, lo32_sext, h₁, h₂]
  rw [BitVec.or_comm, rotl_shifts _ hn]

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : Addr)
    (hv : Vars t s v) (hr1 : s.gpr .a1 = bp)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (bp + BitVec.ofNat 64 (4 * k)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := Proof.Md5.ks_lt t ht
  have hr := Proof.Md5.rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (head_ok (var t 0) (ks.getD t 0) hk (Ts.getD t 0) (var_ne_T1 t 0) (var_ne_T2 t 0)
    s v[0] (X ⟨ks.getD t 0, hk⟩) bp h0 hr1 (hin _ hk) (hX _ hk)) fun s₁ ⟨a₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, 0 < k → k < 4 → s₁.gpr (var t k) = s.gpr (var t k) := fun k h0 h4 =>
    e₁ _ (var_ne t h4 (by omega) (by omega)) (var_ne_T1 t k) (var_ne_T2 t k)
  rw [WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega) (var t 0) (var t 1) (var t 2) (var t 3) (var_ne_T0 t 0)
    (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) (var_ne t (by omega) (by omega) (by omega))
    (var_ne t (by omega) (by omega) (by omega)) s₁
    _ v[1] v[2] v[3] a₁ (by rw [e 1 (by omega) (by omega)]; exact h1)
    (by rw [e 2 (by omega) (by omega)]; exact h2) (by rw [e 3 (by omega) (by omega)]; exact h3))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (tail_ok (var t 0) (var t 1) (Proof.Md5.rot t) (by omega) (by omega)
    (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 0) (var_ne_T0 t 1) s₂ _ v[1] a₂
    (by rw [e₂ _ (var_ne t (by omega) (by omega) (by omega)).symm (var_ne_T0 t 1),
      e 1 (by omega) (by omega)]; exact h1)) fun s₃ ⟨a₃, e₃, m₃, rd₃, wr₃⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → r ≠ T1 → r ≠ T2 → s₃.gpr r = s.gpr r :=
    fun r h h' h'' h''' => by rw [e₃ r h h', e₂ r h h', e₁ r h h'' h''']
  refine ⟨?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (pub_ne' r hr).1 (pub_ne' r hr).2.1 (pub_ne' r hr).2.2⟩
  rw [Proof.Md5.step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
    var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), Proof.Md5.stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 3) (var_ne_T1 t 3)
      (var_ne_T2 t 3), h3]
  · rw [a₃, BitVec.add_comm _ (v[1]), Proof.Md5.add_fn]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 1) (var_ne_T1 t 1)
      (var_ne_T2 t 1), h1]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 2) (var_ne_T1 t 2)
      (var_ne_T2 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : Addr) (sB : State) (hr1 : sB.gpr .a1 = bp)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (bp + BitVec.ofNat 64 (4 * k)) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_r1 : s.gpr .a1 = bp := (hs.pub .a1 (by decide)).trans hr1
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_r1
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.RISCV64
