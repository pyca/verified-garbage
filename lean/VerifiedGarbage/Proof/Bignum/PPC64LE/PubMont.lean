module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# The RSA public-key operation on PPC64LE: Montgomery multiplications

`base_ok`: an array's base from array 0's and the arrays' size. `montOp_ok`:
the multiplication, a call of the shared kernel (`MontCore.lean`'s
`kernel_ok`), with the bases. `WP.callRaw`: a call of code that need not
keep the registers the ABI preserves, as the kernel, an internal function
that only `montOp` calls, does not.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE

theorem base_cons (rd : Reg) (j : Nat) :
    base rd (j + 1) = base rd j ++ ([.add rd rd .r29] : List Instr) := by
  simp only [base, List.replicate_succ', List.cons_append]

/-- `base rd j`, array 0 at `r10` and the arrays' size in `r29`. -/
theorem base_ok {t : State} {B : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .r0) (hrd29 : rd ≠ .r29)
    (h10 : t.gpr .r10 = off B (slot w 0)) (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (base rd j)) t fun t' =>
      (t'.gpr rd = off B (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    apply WP.of_runBlock
    simp only [base, List.replicate_zero, runBlock_cons, exec_addi (show Reg.r10 ≠ .r0 by decide)
      (show 0 < 2 ^ 15 by decide), runStep_some, runBlock_nil, BitVec.add_zero, h10]
    exact ⟨_, rfl, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
  | j + 1 => by
    rw [base_cons, WP.block_append_iff]
    refine WP.mono (base_ok hrd hrd29 h10 h29 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr .r29 (by simpa using Ne.symm hrd29)).trans h29]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega]

/-- A call (`bl`) of code that keeps `LR`: the code runs from the state the
call enters it in (`State.callEntry`), and returns. -/
theorem WP.callRaw {name : String} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s.callEntry fun s₂ => s₂.lr = s.callEntry.lr ∧ Q s₂) : WP isa (.call name c) s Q := by
  obtain ⟨t, s₂, he, hlr, hq⟩ := h
  have hret : isa.ret s.callEntry s₂ = some s₂ := by
    simp only [isa, ret]
    exact ite_eq_left_of_eq_true _ _ (eq_true hlr)
  exact ⟨_, _, Exec.call (call_callEntry s) he hret, hq⟩

/-- The registers a Montgomery multiplication writes. -/
def montRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9] ++ tailRegs

/-- `montOp o a b`, in the working space at `B` with array 0 at `r10`, the
arrays' size in `r29`, `2 w` in `r11` and `-n⁻¹ mod 2³²` in `r12`. -/
theorem montOpN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (montOp o a b) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep montRegs s t := by
  unfold montOp
  refine WP.seq ?_
  rw [show ([.mflr .r14, .addi .r3 .r12 0] ++ base .r5 o ++ base .r6 a ++ base .r7 b ++ base .r8 2 ++ base .r9 3 ++
      [.addi .r4 .r11 0] : List Instr) = [.mflr .r14, .addi .r3 .r12 0] ++ (base .r5 o ++ (base .r6 a ++
      (base .r7 b ++ (base .r8 2 ++ (base .r9 3 ++ [.addi .r4 .r11 0]))))) by simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r14] (Q := fun t => t.gpr .r14 = s.lr ∧ t.gpr .r3 = s.gpr .r12 ∧ t.mem = s.mem)
    (by prun [exec_mflr, BitVec.add_zero]) (by decide)) fun t₀ ⟨⟨a14, a3, m0⟩, k0⟩ => ?_
  have h10' : t₀.gpr .r10 = off B (slot w 0) := (k0.gpr _ (by decide)).trans h10
  have h29' : t₀.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k0.gpr _ (by decide)).trans h29
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r5) (by decide) (by decide) h10' h29' o) fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r6) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10')
    ((k1.gpr _ (by decide)).trans h29') a) fun t₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r7) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10')
    ((k12.gpr _ (by decide)).trans h29') b) fun t₃ ⟨⟨a7, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r8) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10')
    ((k13.gpr _ (by decide)).trans h29') 2) fun t₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10')
    ((k14.gpr _ (by decide)).trans h29') 3) fun t₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  refine WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧ t.mem = t₅.mem)
    (by prun [(k15.gpr .r11 (by decide)).trans ((k0.gpr .r11 (by decide)).trans h11), BitVec.add_zero])
    (by decide)) fun t₆ ⟨⟨a4, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  have hm : t₆.mem = s.mem := by rw [m6, m5, m4, m3, m2, m1, m0]
  have g5 : t₆.gpr .r5 = off B (slot w o) := by rw [k6.gpr .r5 (by decide), k5.gpr .r5 (by decide),
    k4.gpr .r5 (by decide), k3.gpr .r5 (by decide), k2.gpr .r5 (by decide), a5]
  have g6 : t₆.gpr .r6 = off B (slot w a) := by rw [k6.gpr .r6 (by decide), k5.gpr .r6 (by decide),
    k4.gpr .r6 (by decide), k3.gpr .r6 (by decide), a6]
  have g7 : t₆.gpr .r7 = off B (slot w b) := by rw [k6.gpr .r7 (by decide), k5.gpr .r7 (by decide),
    k4.gpr .r7 (by decide), a7]
  have g8 : t₆.gpr .r8 = off B (slot w 2) := by rw [k6.gpr .r8 (by decide), k5.gpr .r8 (by decide), a8]
  have g9 : t₆.gpr .r9 = off B (slot w 3) := by rw [k6.gpr .r9 (by decide), a9]
  have g3 : t₆.gpr .r3 = s.gpr .r12 := by rw [k16.gpr .r3 (by decide), a3]
  have g14 : t₆.gpr .r14 = s.lr := by rw [k16.gpr .r14 (by decide), a14]
  have g10 : t₆.gpr .r10 = off B (slot w 0) := (k16.gpr _ (by decide)).trans h10'
  -- The call: the kernel runs from the state the call enters it in.
  have ce : ∀ r, r ∉ linkRegs → t₆.callEntry.gpr r = t₆.gpr r := fun r hr => State.callEntry_gpr t₆ hr
  rw [← hm] at hinv hB ⊢
  refine WP.seq (WP.callRaw (WP.mono (kernel_ok (s := t₆.callEntry)
    (hs.congr ((State.callEntry_wr t₆).trans (k16.wr.trans k0.wr))) hn ho ha hb ho2 ho3 ha2 hb2
    hw2 hw' hZ ((ce _ (by decide)).trans g5) ((ce _ (by decide)).trans g6) ((ce _ (by decide)).trans g7)
    ((ce _ (by decide)).trans g8) ((ce _ (by decide)).trans g9) ((ce _ (by decide)).trans g10)
    ((ce _ (by decide)).trans a4) (by rw [ce _ (by decide), g3]; exact h12)
    (by rw [ce _ (by decide), g3, State.callEntry_mem]; exact hinv) (by rw [State.callEntry_mem]; exact hB))
    fun t ⟨⟨tlt, teq, tout, t14, t11, t12⟩, kt⟩ => ⟨kt.lr, ?_⟩))
  simp only [State.callEntry_mem] at tlt teq tout
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_mtlr, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ⟨tlt, teq, tout⟩, ⟨fun r hr => ?_, kt.rd.trans (k16.rd.trans k0.rd), kt.wr.trans (k16.wr.trans k0.wr),
    kt.sp.trans (k16.sp.trans k0.sp), ?_⟩⟩
  · show t.gpr r = s.gpr r
    by_cases e11 : r = .r11
    · subst e11; rw [t11, h11]
    by_cases e12 : r = .r12
    · subst e12; rw [t12, ce _ (by decide), g3]
    have hk : r ∉ kernelRegs := by
      simp only [kernelRegs, List.mem_cons, not_or]
      exact ⟨e11, e12, fun h => hr (List.mem_append_right _ h)⟩
    have hl : r ∉ linkRegs := by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by subst h; decide), e11, e12⟩
    rw [kt.gpr r hk, ce r hl, k16.gpr r (fun h => hr (by
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with ((((h | h) | h) | h) | h) | h <;> subst h <;> decide)), k0.gpr r ?_]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hr (by subst h; decide), fun h => hr (by subst h; decide)⟩
  · show t.gpr .r14 = s.lr
    rw [t14, ce _ (by decide), g14]

/-- `montOpN_ok` for arrays below 8. -/
theorem montOp_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (montOp o a b) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep montRegs s t :=
  montOpN_ok hs (by decide) ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ h10 h29 h11 h12 hinv hB

end VG.Proof.Bignum.PPC64LE.Pub
