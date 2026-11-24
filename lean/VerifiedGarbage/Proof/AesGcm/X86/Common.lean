module
public import VerifiedGarbage.Proof.AesGcm.X86.Env
meta import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State


/-!
# AES-GCM on x86: pieces shared by GHASH and counter mode

Untrusted: everything here is checked by Lean. The arguments of a piece,
kept in `W` (`dO`, `nO`, `bO`: `PSlots`) and the frame their writes stay in
(`pslotR`); the data a piece reads (`DataOk`); `minLen` (`ecx := min (16 -
b, n)`) and `splitWhole` (the whole blocks and the rest), with their
constant-time proofs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

variable {N : Nat}

/-- The word at `W + o`. -/
abbrev slotv (m : Mem) (W : BitVec 32) (o : Nat) : BitVec 32 := m.readW (w64 W + BitVec.ofNat 64 o) 32

theorem slotv_eq (m : Mem) (W : BitVec 32) (o : Nat) : slotv m W o = m.readW (w64 W + BitVec.ofNat 64 o) 32 := rfl

/-- The arguments of the piece running: the pointer, length and offset at
`W + dO`, `W + nO`, `W + bO`. -/
abbrev pslotR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 dO, 12⟩

/-- The working space, from `W + 240`: the compared tags, the arguments of
the pieces and the callees' working space. -/
abbrev wsR (N : Nat) (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 240, N - 240⟩

theorem pslot_ws (W : BitVec 32) (hN : 768 ≤ N := by wbig) : Region.Sub (pslotR W) (wsR N W) :=
  Offset.sub _ (by decide) (by simp only [dO]; omega_using [hN])

namespace Lay

/-- `[W + d, W + d + n)`, from 240 on, is within `wsR`. -/
theorem wsIn {W : BitVec 32} {d n : Nat} (h₁ : 240 ≤ d) (h₂ : d + n ≤ 768) (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨w64 W + BitVec.ofNat 64 d, n⟩ (wsR N W) :=
  Offset.sub _ h₁ (by omega_using [h₂, hN])

theorem wsSub {W : BitVec 32} (hN : 768 ≤ N := by wbig) : Region.Sub (wsR N W) ⟨w64 W, N⟩ :=
  Offset.sub_base _ (by omega_using [hN])

/-- The working space of the functions called is within `wsR`. -/
theorem hi_ws {W : BitVec 32} (hN : 768 ≤ N := by wbig) :
    Region.Sub ⟨w64 W + BitVec.ofNat 64 512, N - 512⟩ (wsR N W) :=
  Offset.sub _ (by decide) (by omega_using [hN])

/-- What is kept below 240 is apart from `wsR`. -/
theorem w_ws {W : BitVec 32} {a n : Nat} (ha : a + n ≤ 240) (hN : 768 ≤ N := by wbig) (hk : N < 2 ^ 64 := by wlt) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (wsR N W) :=
  Offset.disjoint _ (.inl ha) (by omega_using [ha]) (by omega_using [hN, hk])

variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K)
include L

theorem ctx_ws {a n : Nat} (ha : a + n ≤ 256) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (wsR N W) :=
  (L.cw.sub_left (ctxSub ha)).sub_right (wsSub L.big)

theorem st_ws {a n : Nat} (ha : a + n ≤ 80) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (wsR N W) :=
  (L.sb.sub_left (stSub ha)).sub_right (Offset.sub _ (by decide) (by have h₁ := L.big; omega_using [h₁]))

theorem stk_ws : (below SP K).Disjoint (wsR N W) := L.kw.sub_right (wsSub L.big)

end Lay

/-- A word written to one of the pieces' slots. -/
theorem pslot_write {m m' : Mem} {W : BitVec 32} (h : Frame [pslotR W] m m') {o : Nat} (h₁ : dO ≤ o)
    (h₂ : o + 4 ≤ dO + 12) (v : BitVec 32) : Frame [pslotR W] m (m'.writeW (w64 W + BitVec.ofNat 64 o) v) :=
  h.writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ h₂ (by decide))

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
state, `W` and the stack. -/
structure DataOk (N : Nat) (St W SP : BitVec 32) (K : Nat) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  st : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 St, 80⟩
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, N⟩
  stk : (below SP K).Disjoint ⟨w64 D, n⟩

namespace DataOk

variable {St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat} (h : DataOk N St W SP K s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataOk N St W SP K s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem n_lt : n < 2 ^ 64 := by have := h.fit; omega_using [this]

/-- The bytes `[j, j + k)`. -/
theorem part {j k : Nat} (hk : j + k ≤ n) :
    Covers [⟨w64 D + BitVec.ofNat 64 j, k⟩] (s.rd ++ s.wr) ∧
      (⟨w64 D + BitVec.ofNat 64 j, k⟩ : Region).Disjoint ⟨w64 St, 80⟩ ∧
      (⟨w64 D + BitVec.ofNat 64 j, k⟩ : Region).Disjoint ⟨w64 W, N⟩ ∧
      (below SP K).Disjoint ⟨w64 D + BitVec.ofNat 64 j, k⟩ := by
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 j, k⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hk
  exact ⟨covers_off h.rd hk h.n_lt, h.st.sub_left hs, h.w.sub_left hs, h.stk.sub_right hs⟩

/-- The pointer to byte `j < n`. -/
theorem ptr {j : Nat} (hj : j < n) : w64 (D + BitVec.ofNat 32 j) = w64 D + BitVec.ofNat 64 j :=
  w64_add (by have := h.fit; omega_using [hj, this])

theorem ptrN {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j :=
  toNat_add32 (by have := h.fit; omega_using [hj, this])

end DataOk

/-! ## `minLen` -/

theorem ofNat16_sub {b : Nat} (hb : b ≤ 16) : BitVec.ofNat 32 16 - BitVec.ofNat 32 b = BitVec.ofNat 32 (16 - b) :=
  ofNat_sub32 hb (by decide)

/-- `minLen`'s block: `ecx := 16 - b`, `CF := n < 16 - b`. -/
theorem minLen1_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K) {s : State}
    (he : Env N Ctx St W SP s) {n b : Nat} (hn : slotv s.mem W nO = BitVec.ofNat 32 n)
    (hb : slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16) (hnlt : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (imm 16), .alu .sub .ecx (slot bO), .mov .eax (slot nO), .alu .cmp .eax (.reg .ecx)] s =
      some s' ∧ s'.gpr .ecx = BitVec.ofNat 32 (16 - b) ∧ s'.gpr .eax = BitVec.ofNat 32 n ∧
      s'.cf = some (decide (n < 16 - b)) ∧ (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 := ofNat16_sub hb16
  refine ⟨_, by xrun [he.ebp, L.aW, he.wIn', hn, hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e16]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [cf_setMem, gpr_setMem, cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e16,
      toNat_ofNat32 hnlt, toNat_ofNat32 (show 16 - b < 2 ^ 32 by omega_using [])]
  · intro r h₁ h₂; simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
  all_goals rfl

/-- What `minLen` leaves. -/
structure MinOut (k : Nat) (s s' : State) : Prop where
  ecx : s'.gpr .ecx = BitVec.ofNat 32 k
  other : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem minLen_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K) {s : State}
    (he : Env N Ctx St W SP s) {n b : Nat} (hn : slotv s.mem W nO = BitVec.ofNat 32 n)
    (hb : slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16) (hnlt : n < 2 ^ 32) :
    WP isa minLen s (MinOut (min (16 - b) n) s) := by
  obtain ⟨s₁, run₁, cx, ax, cf, g₁, m₁, rd₁, wr₁⟩ := minLen1_ok L he hn hb hb16 hnlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - b)) cf (fun ht => ?_) (fun hf => ?_)
  · have hlt : n < 16 - b := by simpa using ht
    refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setMem, gpr_setReg, ite_true, ax]; congr 1; omega_using [hlt]
    · intro r h₁ h₂; simp only [gpr_setMem, gpr_setReg, h₂, ite_false]; exact g₁ r h₁ h₂
    · exact m₁
    · exact rd₁
    · exact wr₁
  · have hle : ¬ n < 16 - b := by simpa using hf
    refine WP.block_nil ⟨by rw [cx]; congr 1; omega_using [hle], g₁, m₁, rd₁, wr₁⟩

theorem minLen_ct {I : State → Prop} {W : BitVec 32} {n b : Nat}
    (hp : ∀ s, I s → s.gpr .ebp = W ∧ ∃ Ctx St SP : BitVec 32, ∃ K, Lay N Ctx St W SP K ∧ Env N Ctx St W SP s ∧
      slotv s.mem W nO = BitVec.ofNat 32 n ∧ slotv s.mem W bO = BitVec.ofNat 32 b ∧ b ≤ 16 ∧ n < 2 ^ 32) :
    CT I minLen := by
  refine CT.seq (J := fun s => s.cf = some (decide (n < 16 - b))) ?_ (fun s hs => ?_) ?_
  · exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hp _ h₁).1, (hp _ h₂).1]) (by taint_decide)
  · obtain ⟨-, Ctx, St, SP, K, L, he, hn, hb, hb16, hnlt⟩ := hp s hs
    obtain ⟨s₁, run₁, -, -, cf, -⟩ := minLen1_ok L he hn hb hb16 hnlt
    exact WP.of_runBlock ⟨s₁, run₁, cf⟩
  · refine CT.ite (decide (n < 16 - b)) (fun s h => h) (fun _ => ?_) (fun _ => CT.nil)
    exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)

/-! ## `splitWhole` -/

/-- `splitWhole`, from the slots `dO = D + j` and `nO = n - j`: `ebx = D + j`,
`edi = nb` whole blocks, and the slots the rest; ZF is set if `nb = 0`. -/
theorem splitWhole_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K) {s : State}
    (he : Env N Ctx St W SP s) {P : BitVec 32} {r : Nat} (hd : slotv s.mem W dO = P)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 r) (hr : r < 2 ^ 32) :
    ∃ s', runBlock isa splitWhole s = some s' ∧ s'.gpr .ebx = P ∧ s'.gpr .edi = BitVec.ofNat 32 (r / 16) ∧
      s'.zf = some (decide (r / 16 = 0)) ∧
      (∀ q, q ≠ .eax → q ≠ .ebx → q ≠ .edx → q ≠ .edi → s'.gpr q = s.gpr q) ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 (r % 16))).writeW
        (w64 W + BitVec.ofNat 64 dO) (P + BitVec.ofNat 32 (16 * (r / 16))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := shr4 hr
  have hand := and15 (BitVec.ofNat 32 r)
  rw [toNat_ofNat32 hr] at hand
  have h16 : BitVec.ofNat 32 r - BitVec.ofNat 32 (r % 16) = BitVec.ofNat 32 (16 * (r / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hr]; congr 1; omega_using []
  refine ⟨_, by xrun [splitWhole, he.ebp, L.aW, he.wIn, he.wIn', hd, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsh]
  · simp only [zf_setMem, gpr_setMem, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsh]
    rw [and_self_beq32 (by omega_using [hr])]
  · intro q h₁ h₂ h₃ h₄; simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄, ite_false]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq, hsh, hand, h16]
    rw [BitVec.add_comm (BitVec.ofNat 32 (16 * (r / 16)))]
  all_goals rfl


/-! ## Testing a kept value -/

/-- `mov r, [W + o]; test r, r`: ZF says whether the value kept there is 0. -/
theorem test_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay N Ctx St W SP K) {s : State}
    (he : Env N Ctx St W SP s) (r : Reg) (o : Nat) (ho : o + 4 ≤ 768) {v : Nat}
    (hv : slotv s.mem W o = BitVec.ofNat 32 v) (hvl : v < 2 ^ 32) :
    WP isa (.block [.mov r (slot o), .alu .test r (.reg r)]) s fun s' =>
      s'.zf = some (decide (v = 0)) ∧ s'.gpr r = BitVec.ofNat 32 v ∧ (∀ q, q ≠ r → s'.gpr q = s.gpr q) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a := L.aW (o := o) (by omega_using [ho])
  have i := he.wIn' (d := o) (n := 4) ho
  refine WP.of_runBlock ⟨_, by xrun [he.ebp, a, i, hv], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems []; rw [and_self_beq32 hvl]
  · regs []
  · intro q hq; regs []; exact gpr_setReg_of_ne _ _ hq
  all_goals rfl

end VG.Proof.AesGcm.X86
