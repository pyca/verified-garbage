import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.WideOps

/-!
# The window method on x86-64: the recoded scalar

`addConst n src dst c` writes `c` to `dst`, adds the `n` words at `src` to the
low `n` words of `dst` by the carry chain (`chainWAdd_ok`), and adds the carry
to its top word (`adcTop_ok`): `[dst] = [src] + c` when the sum fits
(`addConst_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- `[d] += CF`, through `r8`. -/
theorem adcTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size)
    {cf : Bool} (hc : s.cf = some cf) :
    WP isa (.block [.mov .r8 (.mem (sc d)), .alu .adc .r8 (.imm 0), .store (sc d) .r8]) s fun t =>
      t.mem = s.mem.writeW (off base d) (word s.mem base d + (BitVec.ofBool cf).setWidth 64) ∧
        KeepRegs [.r8] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 hd) fun u ⟨lu, cu, ku⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have ha : WP isa (.block [.alu .adc .r8 (.imm 0)]) u fun v =>
      v.gpr .r8 = word s.mem base d + (BitVec.ofBool cf).setWidth 64 ∧ Keeps [.r8] u v := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      Option.map_some, cu, hc, lu, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, fun r hr => ?_,
      rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  refine WP.mono ha fun v ⟨av, kv⟩ => ?_
  have hsv := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
  refine WP.mono (storeReg_ok hsv .r8 hd) fun t ⟨mt, _, _, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, av, kv.2.1, ku.2.1]
  · exact ((Keeps.regs ku).trans (Keeps.regs kv)).trans (kt.mono (by decide))

/-- `[dst] = [src] + c`, `n + 1` words from `n`. -/
theorem addConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst c : Nat}
    (h0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 8 * (n + 1) ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 8 * (n + 1) ≤ src) (hc : c < 2 ^ (64 * (n + 1)))
    (hsum : wordsVal s.mem base src n + c < 2 ^ (64 * (n + 1))) :
    WP isa (.block (WinCfg.addConst n src dst c)) s fun t =>
      wordsVal t.mem base dst (n + 1) = wordsVal s.mem base src n + c ∧ KeepRegs [.rax, .r8] s t ∧
      Outside base dst (8 * (n + 1)) s.mem t.mem := by
  have hn := hs.nowrap
  rw [WinCfg.addConst, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n := n + 1) (o := dst) (x := c) hdst hc) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have vs₁ : wordsVal s₁.mem base src n = wordsVal s.mem base src n := O₁.wordsVal (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (chainWAdd_ok n (op := .add) (c := false) (t := dst) (a := dst) (b := src) hs₁
    (Or.inl ⟨rfl, rfl⟩) (Or.inl h0) (by omega) (by omega) (by omega) (Or.inl rfl)
    (by unfold Near; omega)) fun s₂ ⟨c', hc₂, e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (adcTop_ok hs₂ (d := dst + 8 * n) (by omega) hc₂) fun t ⟨mt, kt⟩ => ?_
  -- The words of `c`, and the top word.
  have hc₁ := e₁
  rw [wordsVal_succ_top] at hc₁
  have htop₂ : word s₂.mem base (dst + 8 * n) = word s₁.mem base (dst + 8 * n) := O₂.word (by omega) (by omega)
  have hlow : wordsVal t.mem base dst n = wordsVal s₂.mem base dst n := by
    rw [mt]; exact (writeW_outside _ _ _ (by omega)).wordsVal (by omega) (by omega)
  rw [vs₁] at e₂
  simp only [Bool.toNat_false, Nat.add_zero] at e₂
  have hb : (BitVec.ofBool c').setWidth 64 = BitVec.ofNat 64 c'.toNat := by cases c' <;> rfl
  -- The top word does not wrap.
  have hpow : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  generalize hT : (word s₁.mem base (dst + 8 * n)).toNat = T at hc₁
  generalize hXd : 2 ^ (64 * n) = X at hc₁ e₂ hpow
  have hfit : T + c'.toNat < 2 ^ 64 := by
    have h1 : X * (T + c'.toNat) ≤ wordsVal s.mem base src n + c := by
      rw [Nat.mul_add]; omega
    rw [hpow] at hsum
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 hsum)
  have htop : (word t.mem base (dst + 8 * n)).toNat = T + c'.toNat := by
    rw [mt, word_writeW_self, htop₂, hb, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show c'.toNat < 2 ^ 64 by cases c' <;> decide), hT, Nat.mod_eq_of_lt hfit]
  refine ⟨?_, ?_, ?_⟩
  · rw [wordsVal_succ_top, hlow, htop, hXd, Nat.mul_add]
    omega
  · exact ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (kt.mono (by decide))
  · have O₃ : Outside base (dst + 8 * n) 8 s₂.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by omega)
    exact (O₁.trans ((O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega))))

end VG.Proof.Weierstrass.X86_64
