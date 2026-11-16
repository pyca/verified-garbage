module

public import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddP
public import VerifiedGarbage.Proof.Weierstrass.OddWin
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
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.AddConst
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddState

/-! ### `Weierstrass.X86_64.OddScalar`, which only this module used -/

section

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
  obtain e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := by decide
  rw [e1, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  obtain hb : w.getLsbD 0 = decide (w.toNat % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit_zero]
  rw [hb]
  by_cases h : w.toNat % 2 = 1
  · rw [decide_eq_true h, decide_eq_false (by omega_using [h])]; decide
  · rw [decide_eq_false h, decide_eq_true (by omega_using [h])]; decide

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
  obtain ⟨k, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega_using [hk]⟩
  rw [wordsVal]; omega_using []

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
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain vk₁ : wordsVal s₁.mem base k n = wordsVal s.mem base k n := O₁.wordsVal (by omega_using [hsep]) (by omega_using [hk, hn])
  rw [WP.block_append_iff]
  refine WP.mono (chainWSub_ok n (op := .sub) (c := false) (t := t) (a := t) (b := k) hs₁
    (Or.inl ⟨rfl, rfl⟩) (Or.inl h0) (by omega_using [ht]) (by omega_using [ht]) (by omega_using [hk]) (Or.inl rfl)
    (by unfold Near; omega_using [hsep])) fun s₂ ⟨c', _, e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain vk₂ : wordsVal s₂.mem base k n = wordsVal s.mem base k n := by
    rw [O₂.wordsVal (by omega_using [hsep]) (by omega_using [hk, hn]), vk₁]
  obtain wk₂ : word s₂.mem base k = word s.mem base k := by
    rw [O₂.word (by omega_using [h0, hsep]) (by omega_using [h0, hk, hn]), O₁.word (by omega_using [h0, hsep]) (by omega_using [h0, hk, hn])]
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ (x := k) (by omega_using [h0, hk])) fun s₃ ⟨x₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  obtain hev : decide ((word s₂.mem base k).toNat % 2 = 0) = decide (wordsVal s.mem base k n % 2 = 0) := by
    rw [wk₂, wordsVal_mod_two _ _ _ _ h0]
  rw [hev] at x₃
  refine WP.mono (sel_ok (decide (wordsVal s.mem base k n % 2 = 0)) n hs₃ x₃ (o := k) (a := k) (b := t)
    hk hk ht (Or.inl (Nat.le_refl _)) (by omega_using [hsep])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [m₃, vk₂] at e₄
  refine ⟨⟨wordsVal s₂.mem base t n, wordsVal_lt _ _ _ _, ?_, ?_⟩, ?_, ?_⟩
  · rw [vk₁, e₁] at e₂
    simp only [Bool.toNat_false, Nat.add_zero] at e₂
    cases c' <;> simp at e₂ <;> omega_using [e₂]
  · rw [e₄]
    by_cases h : wordsVal s.mem base k n % 2 = 1
    · rw [decide_eq_false (by omega_using [h]), ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
    · rw [decide_eq_true (by omega_using [h]), ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl
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
  obtain hr : InRegions (s.rd ++ s.wr) (off base x) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [hx]) (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, ea_sc, hs.rdi, hr, hb,
    ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr' => ?_, rfl, rfl, rfl⟩
  · cases b <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]

end VG.Proof.Weierstrass.X86_64

end

end


/-!
# ECDH on x86-64: `[d]P` by odd 5-bit windows in Jacobian coordinates

For four or six words and a curve of prime order `n` with `n` odd and
`n mod 64 < 33` (P-256), killed by `n` (`KilledByN`), the odd window method
(`Cfg.mulQJO`): its slots are the Jacobian window method's (`jwLayQO`, its
table of bits read from bit 1); `mulQJO_ok`: `d` reduced below `2^nbits`
(`maskK`), `k = d` if `d` is odd, else `n - d` (`oddScalar`), `k + 32^J - 1`
and its bits (`jwinPrepO`), the odd window method on the peer's point (or
`G`), its selections woven into its additions where that applies
(`winJacOW_ok`), `R`'s `y` negated for an even `d` (`fixSign`: `[n - d]P = -[d]P`,
`OddWin.mul_oddK`), then the signature's power: `R` represents `[d]P` for
`d < n` (`MulOk`). It writes what the window method and
the power may (`mulQJW`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-- The odd window method's configuration for ECDH. -/
abbrev jwQO (c : Cfg) : JacWinCfg := Impl.Ecdh.X86_64.Cfg.jwinCfgO c

theorem jwLayQO (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) : JacWinLay (jwQO c) size := by
  have hn := hc.n0
  have hJ : (jwQO c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  obtain hJle := jwinJ_le hc
  obtain hJ2 : 2 ≤ Impl.Ecdh.X86_64.Cfg.jwinJ c := by
    unfold Impl.Ecdh.X86_64.Cfg.jwinJ
    have := hc.len8
    by_cases h : c.nbits < 8 * c.C.len
    · have := (hc.mask h).1; omega_arith
    · omega_arith
  have hb : (jwQO c).bits = c.sl WB + 1 := rfl
  have hK : (jwQO c).tbl = c.sl WT := rfl
  have hMn : (jwQO c).M.n = c.n := rfl
  refine ⟨h46, ?_, ?_, ?_, ?_, rfl, ⟨by omega_arith, by omega_arith⟩, ?_, ?_, ?_⟩
  · rw [show jwSlots (jwQO c) = jwSlots (jwQ c) from rfl, jwSlots_eq]; exact lay_jw h46 rfl rfl rfl jwIdx_lt
  · exact map_sl_disj hn (l₁ := roJ) (l₂ := otherJ) (by decide)
  · exact map_sl_nodup hn (l := otherJ) (by decide)
  · intro x hx
    obtain hx' : x ∈ (roJ ++ otherJ).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    obtain key : ∀ i ∈ roJ ++ otherJ, i < WT := by decide
    rw [hK, hMn]; exact Or.inl (sl_lt c (key i hi))
  · rw [hK]; simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WT <;> omega_arith
  · rw [hb, hJ]; simp (disch := sl_ne) only [sl_eq]
    rcases h46 with h4 | h4 <;> rw [h4] <;> show _ ≤ 8192 <;> unfold WB <;> omega_arith
  · intro w hw
    rw [show jwW (jwQO c) = jwW (jwQ c) from rfl, jwW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [hb, hJ]
    obtain key : ∀ i ∈ otherJ ++ gridJ ++ [TMP], i < WB ∨ WT ≤ i := by decide
    rcases key i hi with h | h
    · by_cases h6 : i = TMP ∧ c.n = 6
      · obtain ⟨rfl, h6⟩ := h6
        refine Or.inl ?_
        dsimp only
        rw [sl_tmp6 c h6]; simp (disch := sl_ne) only [sl_eq]; unfold WB
        rw [h6] at hJle ⊢; omega_using [hJle]
      · exact Or.inr (Nat.le_succ_of_le (sl_lt c h (by
          by_cases ht : i = TMP
          · exact .inr (.inr ⟨fun e => h6 ⟨ht, e⟩, by decide⟩)
          · exact .inl ht)))
    · refine Or.inl ?_
      dsimp only
      simp (disch := sl_ne) only [sl_eq]
      unfold WB; unfold WT at h
      rcases h46 with h4 | h4 <;> rw [h4] <;> omega_arith


theorem negPt_negPt {C : Curve} (Q : Point C) : negPt (negPt Q) = Q := by
  cases Q with
  | infinity => rfl
  | affine x y => show Point.affine x (- -y) = _; congr 1; grind

/-- `Cfg.mulQJO` with any code `wnd` for the window method, which may also write `V`, apart from the
constants and the tables of bits: it computes `[d]P` for `d < n` (`MulOk`), for four or six words and a
curve whose order `n` is odd and kills it, whose scalars fit the windows' top digit
(`64 n ≤ 5 (J - 1) + 1`), if `wnd` computes `[k]P` for the odd `k < n` whose bits the table has, as
`windowOW` does (`winJacOW_ok`). -/
theorem mulQJO_with (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) (hC : Law c.C) (hKn : KilledByN c.C)
    (hn2 : c.C.n % 2 = 1) (hJ5 : 64 * c.n ≤ 5 * (Impl.Ecdh.X86_64.Cfg.jwinJ c - 1) + 1)
    {wnd : Prog isa} {V : List (Nat × Nat)} (hV : FixedOk c V)
    (hVt : ∀ j, j < 3 → ∀ t, t < 64 * c.n → ∀ w ∈ V, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t)
    (hwnd : ∀ {P : Point c.C}, onCurve c.C P = true → ∀ {k : Nat}, k ≤ 2 * 32 ^ ((jwQO c).J - 1) →
      ∀ {base : Addr} {s : State}, Scr s base size → ModOkW (jwQO c).M size c.C.p s.mem base →
      JacWinFixedO (jwQO c) c.C base s P k →
      WP isa wnd.inline s fun s' => KeepRegs (powClob (jwQO c).M.n) s s' ∧
        Unch base (jwW (jwQO c) ++ V) s.mem s'.mem ∧ ModOkW (jwQO c).M size c.C.p s'.mem base ∧
        (∀ x ∈ [(jwQO c).R.x, (jwQO c).R.y, (jwQO c).R.z], wordsVal s'.mem base x (jwQO c).M.n < c.C.p) ∧
        (k % 2 = 1 ∧ k < c.C.n → Rep c.C (tmv c.C (jwQO c).M.n base s' (jwQO c).R.x)
          (tmv c.C (jwQO c).M.n base s' (jwQO c).R.y) (tmv c.C (jwQO c).M.n base s' (jwQO c).R.z) (mul k P))) :
    MulOk c (.seq (.block (Impl.Ecdh.X86_64.Cfg.maskK c)) (.seq (Impl.Ecdh.X86_64.Cfg.jwinPrepO c)
      (.seq wnd (.block (Impl.Ecdh.X86_64.Cfg.fixSign c))))) (mulQJW c ++ V) := by
  intro base s hs g F hbp P hP hpx hpy hrep _ _ _ k hk hk8 ht₀ ht₁ rest R h
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hp3 := hc.p_ge
  obtain hJle := jwinJ_le hc
  refine WP.seq (WP.seq (WP.mono (maskK_ok hc hs (hk ▸ hk8)) fun s₁ ⟨hs₁, k₁, e₁, U₁⟩ => ?_))
  obtain F₁ := F.unch h7 hn (fixedOk_slW (l := [K]) (by decide)) U₁
  obtain v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
    sv_unch U₁ h7 hn hi (apart_slW (by simpa using hne))
  have hJ : (jwQO c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  obtain hWK : c.sl WK + 16 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WK <;> omega_arith
  obtain hKW := sl_lt c (show K < WK by decide)
  obtain h32 : (32 : Nat) ^ Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ 2 ^ (64 * c.n + 63) := by
    rw [show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain e82 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := sl_ne) only [sl_eq]; unfold WK WB; omega_arith
  obtain hBs : c.sl WB + 80 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WB <;> omega_arith
  have hnN : c.C.n < 2 ^ (64 * c.n) := hc.n_lt
  rw [Impl.Ecdh.X86_64.Cfg.jwinPrepO]
  refine WP.seq (WP.seq ?_)
  simp only [Code.inline]
  rw [WP.block_append_iff, hK]
  refine WP.mono (oddScalar_ok hs₁ (n := c.n) (nv := c.C.n) (k := c.sl K) (t := c.sl WK) h0
    (sl_le c h7 (by decide)) (by omega_arith) (Or.inl (by omega_arith)) hnN)
    fun s₁' ⟨⟨tv, htv, htv', ek⟩, ko, Uo⟩ => ?_
  obtain hs₁' := hs₁.of_keepRegs ko (by decide)
  obtain hkO : wordsVal s₁'.mem base (c.sl K) c.n < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  refine WP.mono (addConst_ok hs₁' (n := c.n) (src := c.sl K) (dst := c.sl WK)
    (c := 32 ^ Impl.Ecdh.X86_64.Cfg.jwinJ c - 1) h0 (sl_le c h7 (by decide)) (by omega_arith)
    (Or.inl (by omega_arith)) (by
      rw [show 64 * (c.n + 1) = 64 * c.n + 63 + 1 by omega_arith, Nat.pow_succ]
      have := Nat.two_pow_pos (64 * c.n + 63); omega_arith)
    (by rw [show 64 * (c.n + 1) = 64 * c.n + 63 + 1 by omega_arith, Nat.pow_succ]
        have : 2 ^ (64 * c.n) ≤ 2 ^ (64 * c.n + 63) := Nat.pow_le_pow_right (by decide) (by omega_arith)
        omega_arith))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₂ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [e₂] at b₃
  obtain Uo' : Unch base (winX c ++ slW c [K]) s₁.mem s₁'.mem := Uo.cover fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨(c.sl K, 8 * c.n), List.mem_append_right _ (by simp [slW]), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(c.sl WK, 16 * c.n), List.mem_append_left _ (by simp [winX, hK]), Nat.le_refl _, by omega_arith⟩
  obtain U₃ : Unch base (winX c ++ slW c [K]) s₁.mem s₃.mem :=
    (Uo'.trans (((O₂.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₃.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (W' := winX c) (by intro w hw; simpa [winX, hK, hB] using hw))).mono fun w hw => by
        rcases List.mem_append.mp hw with hw | hw
        · exact hw
        · exact List.mem_append_left _ hw
  obtain F₃ := F₁.unch h7 hn (fixedOk_winX.append (fixedOk_slW (l := [K]) (by decide))) U₃
  obtain e₃ : ∀ {i}, i < 45 → i ≠ K → sv c base s₃ i = sv c base s i := fun hi hne =>
    (sv_unch U₃ h7 hn hi (apart_append (apart_winX hi) (apart_slW (by simpa using hne)))).trans (v₁ hi hne)
  obtain hM₃ := modP_of hc F₃.mp
  obtain tv : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hne => by show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _); rw [e₃ hi hne]
  generalize hkv : wordsVal s₁'.mem base (c.sl K) c.n = kO at hkO b₃ ek
  obtain hF : JacWinFixedO (jwQO c) c.C base s₃ P kO := by
    refine ⟨⟨F₃.zero, fun x hx => ?_, ?_, ?_⟩, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt_of_eq_of_lt (e₃ (i := PX) (by decide) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₃ (i := PY) (by decide) (by decide)) hpy
      · exact lt_of_eq_of_lt F₃.onep (Nat.mod_lt _ (by omega_arith))
    · show Rep _ (tmv c.C c.n base s₃ (c.sl PX)) (tmv c.C c.n base s₃ (c.sl PY))
        (tmv c.C c.n base s₃ (c.sl ONEP)) P
      rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl ONEP) c.n) = 1
      rw [F₃.onep, show 2 ^ (64 * c.n) % c.C.p = c.mont 1 by simp [Cfg.mont, Cfg.R], toM_cmont hc]; rfl
    · rw [hJ] at ht
      show s₃.mem (off base (c.sl WB + 1 + t)) = _
      rw [Nat.add_assoc, Nat.add_comm 1 t, b₃ (t + 1) (by omega_arith), OddWin.oq, Nat.testBit_div_two, hJ]
  obtain hkJ : kO ≤ 2 * 32 ^ ((jwQO c).J - 1) := by
    rw [hJ, show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul, ← Nat.pow_succ']
    have : 2 ^ (64 * c.n) ≤ 2 ^ (5 * (Impl.Ecdh.X86_64.Cfg.jwinJ c - 1) + 1) :=
      Nat.pow_le_pow_right (by decide) hJ5
    omega_arith
  refine WP.seq (WP.mono (hwnd hP hkJ hs₃ hM₃ hF) fun s₄ ⟨K₄, U₄, M₄, L₄, R₄⟩ => ?_)
  rw [show jwW (jwQO c) = jwW (jwQ c) from rfl, jwW_eq] at U₄
  obtain hs₄ := hs₃.of_keepRegs K₄ (rdi_not_powClob _)
  obtain F₄ := F₃.unch h7 hn ((fixedOk_slW (by decide)).append hV) U₄
  obtain L := jwLayQO hc h46
  have hRY : (jwQO c).R.y = c.sl RY := rfl
  have hPT : (jwQO c).neg = c.sl PT := rfl
  have hZE : (jwQO c).zero = c.sl ZERO := rfl
  have hMn : (jwQO c).M.n = c.n := rfl
  obtain mRY : c.sl RY ∈ jwSlots (jwQO c) := by rw [← hRY]; jw_mem
  obtain mPT : c.sl PT ∈ jwSlots (jwQO c) := by rw [← hPT]; jw_mem
  obtain mZE : c.sl ZERO ∈ jwSlots (jwQO c) := by rw [← hZE]; jw_mem
  -- `-y` into `PT`.
  simp only [Impl.Ecdh.X86_64.Cfg.fixSign, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sub_ok hs₄ M₄ (o := c.sl PT) (a := c.sl ZERO) (b := c.sl RY) (L.le mPT) (L.le mZE)
    (L.le mRY) (L.lay.tmp _ mPT) (L.lay.tmp _ mZE) (L.lay.tmp _ mRY) (L.lay.mo _ mPT)
    (by rw [hMn, F₄.zero]; omega_arith) (L₄ _ (by rw [← hRY]; simp))) fun s₅ ⟨k₅, e₅⟩ => ?_
  obtain hs₅ := k₅.scr hs₄
  rw [hMn, F₄.zero] at e₅
  obtain nRP : c.sl RY ≠ c.sl PT := by
    rw [← hRY, ← hPT]; exact L.oth_ne (i := 1) (j := 6) (by decide) (by decide) (by decide)
  obtain apRP := L.ap mRY mPT nRP
  obtain y₅ : wordsVal s₅.mem base (c.sl RY) c.n = wordsVal s₄.mem base (c.sl RY) c.n :=
    k₅.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact apRP
      · exact L.lay.tmp _ mRY) (by have := L.le mRY; omega_arith)
  obtain hb₀ : ∀ {m m' : Mem} {W : List (Nat × Nat)}, Unch base W m m' →
      (∀ w ∈ W, bitsAt c.n 0 + 0 + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 0 + 0) →
      m' (off base (bitsAt c.n 0 + 0)) = m (off base (bitsAt c.n 0 + 0)) := fun hu hw =>
    tbl_unch hu h7 hn (j := 0) (t := 0) (by decide) (by omega_arith) hw
  obtain hT0 : s₅.mem (off base (bitsAt c.n 0 + 0)) = if k.testBit 0 then 1 else 0 := by
    rw [hb₀ k₅.unch (by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact (tbl_apart_slW' (c := c) (l := [PT]) (by decide) (j := 0) (t := 0) (by decide) (by omega_arith)) _
            (List.mem_map.mpr ⟨PT, List.mem_singleton_self _, rfl⟩)
        · exact (tbl_apart_slW' (c := c) (l := [TMP]) (by decide) (j := 0) (t := 0) (by decide) (by omega_arith)) _
            (List.mem_map.mpr ⟨TMP, List.mem_singleton_self _, rfl⟩)),
      hb₀ U₄ (fun w hw => (List.mem_append.mp hw).elim
        ((tbl_apart_slW' (c := c) (by decide) (j := 0) (t := 0) (by decide) (by omega_arith)) w)
        (hVt 0 (by decide) 0 (by omega_arith) w)),
      hb₀ U₃ (fun w hw => (List.mem_append.mp hw).elim
        ((tbl_apart_winX (c := c) (j := 0) (t := 0) (by decide) (by omega_arith)) w)
        ((tbl_apart_slW' (c := c) (by decide) (j := 0) (t := 0) (by decide) (by omega_arith)) w)),
      hb₀ U₁ (tbl_apart_slW' (c := c) (by decide) (j := 0) (t := 0) (by decide) (by omega_arith))]
    exact ht₀ 0 (by omega_arith)
  rw [Nat.add_zero] at hT0
  rw [WP.block_append_iff]
  refine WP.mono (byteMask_ok hs₅ (x := bitsAt c.n 0) (by have := bitsAt_le c h7 (j := 0) (by decide); omega_arith)
    hT0) fun s₆ ⟨x₆, k₆⟩ => ?_
  obtain hs₆ := hs₅.of_keeps k₆ (by decide)
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  obtain aRP : c.sl RY ≤ c.sl PT ∨ c.sl PT + 8 * c.n ≤ c.sl RY := by
    rcases apRP with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  refine WP.mono (sel_ok (!k.testBit 0) c.n hs₆ x₆ (o := c.sl RY) (a := c.sl RY) (b := c.sl PT)
    (L.le mRY) (L.le mRY) (L.le mPT) (Or.inl (Nat.le_refl _)) aRP) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_
  obtain hs₇ := hs₆.of_keepRegs k₇ (by decide)
  obtain U47 : Unch base (slW c [PT, TMP, RY]) s₄.mem s₇.mem := by
    refine ((k₅.unch.trans (show Unch base [] s₅.mem s₆.mem by rw [m₆]; exact Unch.refl _ _ _)).trans
      O₇.unch).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | rfl) | rfl
    · exact List.mem_map.mpr ⟨PT, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨TMP, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨RY, by decide, rfl⟩
  obtain F₇ := F₄.unch h7 hn (fixedOk_slW (l := [PT, TMP, RY]) (by decide)) U47
  obtain hM₇ := modP_of hc F₇.mp
  obtain r47 : ∀ {i}, i < 45 → i ∉ [PT, TMP, RY] → sv c base s₇ i = sv c base s₄ i := fun hi h₁ =>
    sv_unch U47 h7 hn hi (apart_slW (by simpa using h₁))
  obtain rz₇ : wordsVal s₇.mem base (c.sl RZ) c.n < c.C.p := by
    show sv c base s₇ RZ < _
    rw [r47 (i := RZ) (by decide) (by decide)]
    exact L₄ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc hs₇ hM₇ rz₇ F₇.onep (fun h9 t ht => by
      rw [tbl_unch U47 h7 hn (j := 1) (by decide) ht
          (tbl_apart_slW' (by decide) (by decide) ht (.inr (.inr (by omega_arith)))),
        tbl_unch U₄ h7 hn (j := 1) (by decide) ht (fun w hw => (List.mem_append.mp hw).elim
          ((tbl_apart_slW' (by decide) (by decide) ht) w) (hVt 1 (by decide) t ht w)),
        tbl_unch U₃ h7 hn (j := 1) (by decide) ht (fun w hw => (List.mem_append.mp hw).elim
          ((tbl_apart_winX (by decide) ht) w) ((tbl_apart_slW' (by decide) (by decide) ht) w)),
        tbl_unch U₁ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht)]
      exact ht₁ h9 t ht)) fun s₈ ⟨K₈, U₈, lt₈, v₈⟩ => h s₈ ?_)
  obtain r₈ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₈ i = sv c base s₇ i := fun hi h₁ =>
    sv_unch U₈ h7 hn hi (apart_pwW hi h₁)
  obtain c₂ : ∀ r ∈ [Reg.rax, .r8], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  obtain c₃ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  obtain c₁ : ∀ r ∈ [Reg.r8], r ∈ powClob c.n := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (r8_mem_clob _)
  obtain c₄ : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [powClob, clob]
    · simp [powClob, clob]
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  obtain K67 : KeepRegs (powClob c.n) s₅ s₇ :=
    ((Keeps.regs k₆).mono (show ∀ r ∈ [Reg.rcx], r ∈ powClob c.n by
      intro r hr; rw [List.mem_singleton.mp hr]; simp [powClob, clob])).trans
    (k₇.mono (show ∀ r ∈ [Reg.rax, .rdx], r ∈ powClob c.n by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [powClob, clob]))
  obtain KK : KeepRegs (powClob c.n) s s₇ :=
    ((((((k₁.mono c₁).trans (ko.mono c₄)).trans (k₂.mono c₂)).trans (k₃.mono c₃)).trans K₄).trans
      ((⟨k₅.gpr, k₅.rd, k₅.wr⟩ : KeepRegs (clob c.n) s₄ s₅).mono clob_powClob)).trans K67
  refine ⟨hs₇.of_keepRegs K₈ (rdi_not_invClob _), by
      rw [K₈.gpr _ (rsi_not_invClob _), KK.gpr _ (rsi_not_powClob _)], by rw [K₈.rd, KK.rd],
    by rw [K₈.wr, KK.wr], ((U₁.trans U₃).trans ((U₄.trans U47).trans U₈)).mono ?_, fun h1 hlt => ?_, lt₈, ?_, ?_⟩
  · intro w hw
    refine (?_ : w ∈ mulQJW c ∨ w ∈ V).elim (List.mem_append_left _) (List.mem_append_right _)
    rcases List.mem_append.mp hw with hw | hw
    · refine Or.inl ?_
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ (List.mem_append_left _ hw)
        · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
    · rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact Or.inl (List.mem_append_left _ (List.mem_append_right _
              (slW_mono (l' := mulJI) (fun _ hi => List.mem_append_left _ hi) hw)))
          · exact Or.inr hw
        · refine Or.inl ?_
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact List.mem_append_right _ (List.mem_append_left _ (by simp [slW]))
          · exact List.mem_append_left _ (List.mem_append_right _ (by simp [slW, mulJI, otherJ, gridJ]))
          · exact List.mem_append_left _ (List.mem_append_right _ (by simp [slW, mulJI, otherJ]))
      · exact Or.inl (List.mem_append_right _ hw)
  · -- `R` represents `[k]P`.
    obtain hk' : k < 2 ^ c.nbits := Nat.lt_of_lt_of_le hlt hc.n_bits
    obtain hkv : wordsVal s₁.mem base (c.sl K) c.n = k := by
      show sv c base s₁ K = k; rw [e₁, hk, Nat.mod_eq_of_lt hk']
    rw [hkv] at htv' ek
    obtain hoK : kO = OddWin.oddK c.C.n k := by
      rw [ek, OddWin.oddK]
      split
      · rfl
      · rcases htv' with h' | h'
        · omega_arith
        · omega_arith
    obtain hodd := OddWin.oddK_odd hn2 (Nat.le_of_lt hlt)
    obtain hlt' := OddWin.oddK_lt h1 hlt
    rw [← hoK] at hodd hlt'
    obtain hq := R₄ ⟨hodd, hlt'.2⟩
    rw [hoK, OddWin.mul_oddK hC hP (hKn P hP) h1 (Nat.le_of_lt hlt)] at hq
    show Rep _ (toM _ _ (sv c base s₈ RX)) (toM _ _ (sv c base s₈ RY)) (toM _ _ (sv c base s₈ RZ)) _
    rw [r₈ (i := RX) (by decide) (by decide), r₈ (i := RY) (by decide) (by decide),
      r₈ (i := RZ) (by decide) (by decide), r47 (i := RX) (by decide) (by decide),
      r47 (i := RZ) (by decide) (by decide)]
    obtain ey : sv c base s₇ RY =
        if k % 2 = 1 then sv c base s₄ RY else (0 + c.C.p - sv c base s₄ RY) % c.C.p := by
      show wordsVal s₇.mem base (c.sl RY) c.n = _
      rw [e₇, m₆, e₅, y₅, Nat.testBit_zero]
      by_cases hk2 : k % 2 = 1
      · simp only [hk2, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · simp only [hk2, decide_false, Bool.not_false, ↓reduceIte]
    rw [ey]
    by_cases hk2 : k % 2 = 1
    · simp only [hk2, ↓reduceIte] at hq ⊢
      exact hq
    · simp only [hk2, ↓reduceIte] at hq ⊢
      obtain hyl : sv c base s₄ RY < c.C.p := L₄ _ (by rw [← hRY]; simp)
      rw [toM_sub (by omega_arith), toM_zero]
      have := hq.negY
      rw [negPt_negPt] at this
      rw [show (0 : Fe c.C) - toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RY) =
        -toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RY) by grind]
      exact this
  · show _ = toM _ _ (sv c base s₈ RZ) ^ _
    rw [r₈ (i := RZ) (by decide) (by decide)]
    exact v₈
  · rw [r₈ (i := RZ) (by decide) (by decide)]; exact rz₇

/-- The odd window method computes `[d]P` for `d < n` (`MulOk`), for four or
six words and a curve of prime order `n`, odd, with `n mod 64 < 33`, killed
by `n`, whose scalars fit the windows' top digit (`64 n ≤ 5 (J - 1) + 1`),
with any doubling `dbl` that doubles a Jacobian triple in place. -/
theorem mulQJO_ok (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hKn : KilledByN c.C) {dbl : Pt → Prog isa} (hD : DblOk c.MP' c.rcbSlots c.C dbl)
    (hn2 : c.C.n % 2 = 1) (hn64 : c.C.n % 64 < 33) (hnb : 128 ≤ c.C.n)
    (hJ5 : 64 * c.n ≤ 5 * (Impl.Ecdh.X86_64.Cfg.jwinJ c - 1) + 1) :
    MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJO c dbl) (mulQJW c) := by
  have hp3 := hc.p_ge
  obtain h : MulOk c (.seq (.block (Impl.Ecdh.X86_64.Cfg.maskK c)) (.seq (Impl.Ecdh.X86_64.Cfg.jwinPrepO c)
      (.seq ((jwQO c).windowOW dbl) (.block (Impl.Ecdh.X86_64.Cfg.fixSign c))))) (mulQJW c ++ []) :=
    mulQJO_with hc h46 hC hKn hn2 hJ5 (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ _ _ _ h => absurd h List.not_mem_nil)
    (fun hP _ hkJ _ _ hs hM hF =>
      WP.mono (winJacOW_ok (jwLayQO hc h46) (unitMod_pow_two hc.p_odd (64 * c.n)) hC hc.am3 hO hD hc.p_lt
        (show c.mont 1 < c.C.p from Nat.mod_lt _ (by omega_arith))
        (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hn2 hn64 hnb hP hkJ hs hM hF)
        fun _ ⟨a, b, r⟩ => ⟨a, b.mono fun _ hw => List.mem_append_left _ hw, r⟩)
  rw [List.append_nil] at h
  exact @h

end VG.Proof.Ecdh.X86_64
