module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The odd scalar on x86-64

The mask of a number's parity, `rcx = ([x] ∧ 1) - 1`, all ones for an even
`[x]` (`parityMask_ok`); and `oddScalar n nv k t`: `[t] = nv - [k]` by the
borrow chain (modulo `2^(64 n)`), selected into `[k]` by that mask
(`oddScalar_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

private theorem parity_fact (w : BitVec 64) :
    (w &&& BitVec.signExtend 64 (1 : BitVec 32)) - BitVec.signExtend 64 (1 : BitVec 32) =
      bmask (decide (w.toNat % 2 = 0)) := by
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := by decide
  rw [e1, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  have hb : w.getLsbD 0 = decide (w.toNat % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit_zero]
  rw [hb]
  by_cases h : w.toNat % 2 = 1
  · rw [decide_eq_true h, decide_eq_false (by omega)]; decide
  · rw [decide_eq_false h, decide_eq_true (by omega)]; decide

/-- `rcx` all ones if the word at `x` is even, else zero. -/
theorem parityMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {x : Nat}
    (hx : x + 8 ≤ size) :
    WP isa (.block [.mov .rcx (.mem (sc x)), .alu .and .rcx (.imm 1), .alu .sub .rcx (.imm 1)]) s fun t =>
      t.gpr .rcx = bmask (decide ((word s.mem base x).toNat % 2 = 0)) ∧ Keeps [.rcx] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rcx hx) fun u ⟨lu, _, ku⟩ => ?_
  crun [lu]
  rw [parity_fact]
  refine ⟨rfl, fun r hr => ?_, ku.2.1, ku.2.2.1, ku.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  exact ku.1 r (by simpa using hr)

/-- The low word decides the parity. -/
theorem wordsVal_mod_two (m : Mem) (base : Addr) (d k : Nat) (hk : 0 < k) :
    wordsVal m base d k % 2 = (word m base d).toNat % 2 := by
  obtain ⟨k, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rw [wordsVal]; omega

/-- `[k] = nv - [k]` (modulo `2^(64 n)`) if `[k]` is even, through `[t]`. -/
theorem oddScalar_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n nv k t : Nat}
    (h0 : 0 < n) (hk : k + 8 * n ≤ size) (ht : t + 8 * n ≤ size) (hsep : k + 8 * n ≤ t ∨ t + 8 * n ≤ k)
    (hnv : nv < 2 ^ (64 * n)) :
    WP isa (.block (oddScalar n nv k t)) s fun s' =>
      (∃ tv : Nat, tv < 2 ^ (64 * n) ∧
        (tv + wordsVal s.mem base k n = nv ∨ tv + wordsVal s.mem base k n = nv + 2 ^ (64 * n)) ∧
        wordsVal s'.mem base k n =
          if wordsVal s.mem base k n % 2 = 1 then wordsVal s.mem base k n else tv) ∧
      KeepRegs [.rax, .rcx, .rdx, .r8] s s' ∧
      Unch base [(k, 8 * n), (t, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  rw [oddScalar, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n := n) (o := t) (x := nv) ht hnv) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have vk₁ : wordsVal s₁.mem base k n = wordsVal s.mem base k n := O₁.wordsVal (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (chainWSub_ok n (op := .sub) (c := false) (t := t) (a := t) (b := k) hs₁
    (Or.inl ⟨rfl, rfl⟩) (Or.inl h0) (by omega) (by omega) (by omega) (Or.inl rfl)
    (by unfold Near; omega)) fun s₂ ⟨c', _, e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have vk₂ : wordsVal s₂.mem base k n = wordsVal s.mem base k n := by
    rw [O₂.wordsVal (by omega) (by omega), vk₁]
  have wk₂ : word s₂.mem base k = word s.mem base k := by
    rw [O₂.word (by omega) (by omega), O₁.word (by omega) (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ (x := k) (by omega)) fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have hev : decide ((word s₂.mem base k).toNat % 2 = 0) = decide (wordsVal s.mem base k n % 2 = 0) := by
    rw [wk₂, wordsVal_mod_two _ _ _ _ h0]
  rw [hev] at x₃
  refine WP.mono (sel_ok (decide (wordsVal s.mem base k n % 2 = 0)) n hs₃ x₃ (o := k) (a := k) (b := t)
    hk hk ht (Or.inl (Nat.le_refl _)) (by omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [m₃, vk₂] at e₄
  refine ⟨⟨wordsVal s₂.mem base t n, wordsVal_lt _ _ _ _, ?_, ?_⟩, ?_, ?_⟩
  · rw [vk₁, e₁] at e₂
    simp only [Bool.toNat_false, Nat.add_zero] at e₂
    cases c' <;> simp at e₂ <;> omega
  · rw [e₄]
    by_cases h : wordsVal s.mem base k n % 2 = 1
    · rw [decide_eq_false (by omega), ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
    · rw [decide_eq_true (by omega), ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl
  · have hcl : ∀ r ∈ [Reg.rax], r ∈ [Reg.rax, .rcx, .rdx, .r8] := by decide
    exact (((k₁.mono hcl).trans (k₂.mono (by decide))).trans ((Keeps.regs k₃).mono (by decide))).trans
      (k₄.mono (by decide))
  · rw [m₃] at O₄
    exact ((O₁.unch.trans O₂.unch).trans O₄.unch).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with (h | h) | h <;> simp [h]

/-- `rcx = b - 1` for the byte `b ∈ {0, 1}` at `x`: all ones for `0`. -/
theorem byteMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {x : Nat}
    (hx : x + 1 ≤ size) {b : Bool} (hb : s.mem (off base x) = if b then 1 else 0) :
    WP isa (.block [.movzx8 .rcx (sc x), .alu .sub .rcx (.imm 1)]) s fun t =>
      t.gpr .rcx = bmask (!b) ∧ Keeps [.rcx] s t := by
  have hn := hs.nowrap
  have hr : InRegions (s.rd ++ s.wr) (off base x) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega) (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, ea_sc, hs.rdi, hr, hb,
    ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr' => ?_, rfl, rfl, rfl⟩
  · cases b <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]

end VG.Proof.Weierstrass.X86_64
