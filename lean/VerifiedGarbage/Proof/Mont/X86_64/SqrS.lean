import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Rounds
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps

/-!
# Montgomery arithmetic on x86-64: P-384's squaring with BMI2 and ADX

`sqrS M o a` (`Impl/Mont/X86_64.lean`): the square `[a]²` in the registers the
operations change and the temporary area, then six of P-384's reductions of
its low half and the high half added (`sqrS_ok`).

* The cross products `C = Σ_{i<j} a_i a_j 2^(64 (i + j - 1))`, row by row:
  row 0 through CF (`accRowS_ok`), its two lowest words then stored, rows 1 to
  4 through OF and CF (`maddRow_ok`), each given that its window does not
  overflow, which the rows' partial sums bound (`sqCross_ok`).
* `C` doubled and the squares `a_i²` added (`sqrDbl_ok`), which makes `[a]²`
  (`sq_eq`).
* The reductions (`redsShortX_ok`, `redShortX_ok` in turn), on six words
  rotating through `sqWin6`, leave `(L + U p) / 2³⁸⁴ ≤ p` for the low half
  `L`, and with the high half `H < p` added, below `2p`.

The powers of two above `2²⁵⁶` are never evaluated: they are split into
factors `2⁶⁴` as soon as they appear (`pow_split`, `pow64x6`, …), or kept
apart from one another.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono mulAcc_ok madd_ok maddLast_ok dblAdd_ok
  carryC_ok clear_ok movRdx_ok movRdxImm_ok mulx_ok of_setReg of_setFlags adc_carry)

/-- `x^c = x^a x^b` for `c = a + b`, stated so that no power is evaluated. -/
theorem pow_split (x a b c : Nat) (h : c = a + b) : x ^ c = x ^ a * x ^ b := h ▸ Nat.pow_add x a b

theorem not_mem_of {r : Reg} {L L' : List Reg} (hr : r ∉ L') (h : ∀ q ∈ L, q ∈ L') : r ∉ L :=
  fun hm => hr (h r hm)

/-- `adc t, 0` with `t = 0`: the carry CF into `t`. -/
theorem adcZero_ok (s : State) (t : Reg) {c : Bool} (hc : s.cf = some c) (h0 : s.gpr t = 0) :
    WP isa (.block [.alu .adc t (.imm 0)]) s fun s' => (s'.gpr t).toNat = c.toNat ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left',
    VG.Proof.X25519.X86_64.se0, h0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## The rows of cross products -/

/-- `mulAcc` along `x :: rs` by `[d …]`, through CF: the carry out pending,
into the last register's word. -/
theorem accRowS_ok {size : Nat} : ∀ (n : Nat) (x : Reg) (rs : List Reg) {s : State} {base : Addr}
    {d : Nat} {c : Bool}, Scr s base size → d + 8 * n ≤ size → rs.length = n → FreshX (x :: rs) →
    s.cf = some c →
    WP isa (.block (accRow (x :: rs) d)) s fun s' => ∃ c', s'.cf = some c' ∧ s'.of = s.of ∧
      regsVal s' (x :: rs) + 2 ^ (64 * n) * c'.toNat =
        (s.gpr x).toNat + c.toNat + (s.gpr .rdx).toNat * wordsVal s.mem base d n ∧
      Keeps (.rax :: x :: rs) s s'
  | 0, x, [], s, _, _, c, _, _, _, _, hc => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, hc, rfl, by simp [regsVal, wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | 0, _, _ :: _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ + 1, _, [], _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | n + 1, x, y :: rs, s, base, d, c, hs, hd, hl, hf, hc => by
    obtain ⟨hxn, hxa, hxc, hxd, hxr⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, hyr⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [accRow, WP.block_append_iff]
    refine WP.mono (mulAcc_ok s (readSrc_sc hs (d := d) (by omega)) (fun _ h => nomatch h) hc hxa hya
      hxy) fun s₁ h₁ => ?_
    obtain ⟨c₁, cf₁, of₁, e₁, k₁⟩ := h₁
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, Ne.symm hxr, Ne.symm hyr⟩)
    refine WP.mono (accRowS_ok n y rs hs₁ (d := d + 8) (by omega) hl hf.tail cf₁) fun s₂ h₂ => ?_
    obtain ⟨c', cf₂, of₂, e₂, k₂⟩ := h₂
    refine ⟨c', cf₂, of₂.trans of₁, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, Ne.symm hxd, Ne.symm hyd⟩)
      have hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxa, hxy, fun h => hxn (List.mem_cons_of_mem _ h)⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [regsVal, wordsVal] at e₁ e₂ ⊢
      rw [hx₂, pow64_succ n]
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      have m₂ := congrArg (2 ^ 64 * ·) e₂
      simp only [Nat.mul_add] at m₂
      simp only [Nat.mul_assoc] at m₂ ⊢
      omega
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- `madd` along `x :: rs` and `maddLast` into the last register, which is
overwritten, by `[d …]`: the low halves through OF and the high halves
through CF, the carries out pending above the last register. -/
theorem maddRow_ok {size : Nat} : ∀ (n : Nat) (x : Reg) (rs : List Reg) {s : State} {base : Addr}
    {d : Nat} {c o : Bool}, Scr s base size → d + 8 * (n + 1) ≤ size → rs.length = n + 1 →
    Fresh (x :: rs) → s.gpr .rbp = 0 → s.cf = some c → s.of = some o →
    WP isa (.block (maddRow (x :: rs) d)) s fun s' => ∃ c' o' : Bool,
      regsVal s' (x :: rs) + 2 ^ (64 * (n + 2)) * (c'.toNat + o'.toNat) =
        regsVal s (x :: rs.take n) + o.toNat + 2 ^ 64 * c.toNat +
          (s.gpr .rdx).toNat * wordsVal s.mem base d (n + 1) ∧
      Keeps (.rcx :: .rax :: x :: rs) s s'
  | _, _, [], _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | 0, x, [y], s, base, d, c, o, hs, hd, _, hf, hz, hc, ho => by
    obtain ⟨hxn, hxa, -, -, hxb, -⟩ := hf.head
    obtain ⟨-, hya, -, -, hyb, -⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    rw [maddRow]
    refine WP.mono (maddLast_ok s (readSrc_sc hs (d := d) (by omega)) (fun _ h => nomatch h) hc ho hz
      hxa hya hxb hyb hxy) fun s' ⟨c', o', _, _, e, k⟩ => ⟨c', o', ?_, k.mono (by sub_regs)⟩
    simp only [regsVal, wordsVal, List.take_zero, Nat.mul_zero, Nat.add_zero] at e ⊢
    rw [show 64 * (0 + 2) = 64 + 64 by rfl, Nat.pow_add]
    omega
  | 0, _, _ :: _ :: _, _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | _ + 1, _, [_], _, _, _, _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | n + 1, x, y :: z :: rs, s, base, d, c, o, hs, hd, hl, hf, hz, hc, ho => by
    obtain ⟨hxn, hxa, hxc, hxd, hxb, hxr⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, hyb, hyr⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [maddRow, WP.block_append_iff]
    refine WP.mono (madd_ok s (readSrc_sc hs (d := d) (by omega)) (fun _ h => nomatch h) hc ho hxc hxa
      hyc hya hxy) fun s₁ h₁ => ?_
    obtain ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ := h₁
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, Ne.symm hxr, Ne.symm hyr⟩)
    have hz₁ : s₁.gpr .rbp = 0 := by
      rw [k₁.1 .rbp (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxb, Ne.symm hyb⟩), hz]
    refine WP.mono (maddRow_ok n y (z :: rs) hs₁ (d := d + 8) (by omega)
      (by simp only [List.length_cons]; omega) hf.tail hz₁ cf₁ of₁) fun s₂ h₂ => ?_
    obtain ⟨c', o', e₂, k₂⟩ := h₂
    refine ⟨c', o', ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxd, Ne.symm hyd⟩)
      have hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        intro h
        rw [List.mem_cons, List.mem_cons, List.mem_cons] at h
        rcases h with h | h | h | h
        · exact hxc h
        · exact hxa h
        · exact hxy h
        · exact hxn (List.mem_cons_of_mem _ h))
      have hR : regsVal s₁ ((z :: rs).take n) = regsVal s ((z :: rs).take n) :=
        regsVal_congr fun q hq => k₁.1 q (by
          have hq' := List.mem_of_mem_take hq
          have := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'))
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨this.2.1, this.1, fun h => hxn (h ▸ List.mem_cons_of_mem _ hq'),
            fun h => hyn (h ▸ hq')⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [List.take_succ_cons, regsVal, hR] at e₂ ⊢
      rw [show wordsVal s.mem base d (n + 1 + 1) = (word s.mem base d).toNat +
        2 ^ 64 * wordsVal s.mem base (d + 8) (n + 1) from rfl]
      rw [hx₂]
      rw [show 64 * (n + 1 + 2) = 64 + 64 * (n + 2) by omega, Nat.pow_add]
      generalize 2 ^ (64 * (n + 2)) = P at e₂ ⊢
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      have m₂ := congrArg (2 ^ 64 * ·) e₂
      simp only [Nat.mul_add] at m₂ e₁
      rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide] at e₁
      simp only [Nat.mul_assoc] at m₂ e₁ ⊢
      omega
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-! ## The squares -/

/-- `adcx x, z`, `adox x, z` with `z = 0`: both carries added into `x`. -/
theorem carriesZ_ok (s : State) {x z : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hz : s.gpr z = 0) (hxz : x ≠ z) :
    WP isa (.block [.adcx x (.reg z), .adox x (.reg z)]) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) = (s.gpr x).toNat + c.toNat + o.toNat ∧
        Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxz), hz, RegUpd.gpr_setFlags, of_setReg, of_setFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) 0 c
    have e2 := adc_carry (s.gpr x + 0 + (BitVec.ofBool c).setWidth 64) 0 o
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e1 e2 ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `mov rdx, [d]`, `mulx rcx, rax, rdx`: `rax + 2⁶⁴ rcx = [d]²`. -/
theorem sqWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rdx (.mem (sc d)), .mulx .rcx .rax (.reg .rdx)]) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rcx).toNat =
        (word s.mem base d).toNat * (word s.mem base d).toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx, .rcx, .rax] s s' := by
  rw [show ([.mov .rdx (.mem (sc d)), .mulx .rcx .rax (.reg .rdx)] : List Instr) =
    [.mov .rdx (.mem (sc d))] ++ [.mulx .rcx .rax (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs hd)) fun s₁ h₁ => ?_
  obtain ⟨d₁, cf₁, of₁, k₁⟩ := h₁
  refine WP.mono (mulx_ok s₁ (src := .reg .rdx) rfl (fun _ h => nomatch h) (by decide))
    fun s₂ h₂ => ?_
  obtain ⟨e₂, cf₂, of₂, k₂⟩ := h₂
  rw [d₁] at e₂
  exact ⟨e₂, cf₂.trans cf₁, of₂.trans of₁, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-- `sqrDiag d x y`: `x + 2⁶⁴ y` doubled and `[d]²` added, with the carries
CF and OF in and out. -/
theorem sqrDiag_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) {x y : Reg} (hf : FreshX [x, y]) {c o : Bool} (hc : s.cf = some c)
    (ho : s.of = some o) :
    WP isa (.block (sqrDiag d x y)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat) +
          (word s.mem base d).toNat * (word s.mem base d).toNat + c.toNat + o.toNat ∧
      Keeps [.rdx, .rcx, .rax, x, y] s s' := by
  obtain ⟨hxn, hxa, hxc, hxd, -⟩ := hf.head
  obtain ⟨-, hya, hyc, hyd, -⟩ := hf.tail.head
  have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
  rw [sqrDiag, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (sqWord_ok hs hd) fun s₁ h₁ => ?_
  obtain ⟨e₁, cf₁, of₁, k₁⟩ := h₁
  refine WP.mono (dblAdd_ok s₁ (cf₁.trans hc) (of₁.trans ho) hxa) fun s₂ h₂ => ?_
  obtain ⟨c₂, o₂, cf₂, of₂, e₂, k₂⟩ := h₂
  refine WP.mono (dblAdd_ok s₂ cf₂ of₂ hyc) fun s₃ h₃ => ?_
  obtain ⟨c₃, o₃, cf₃, of₃, e₃, k₃⟩ := h₃
  refine ⟨c₃, o₃, cf₃, of₃, ?_, (k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans
    (k₃.mono (by sub_regs)))⟩
  have x₁ : s₁.gpr x = s.gpr x := k₁.1 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hxd, hxc, hxa⟩)
  have y₂ : s₂.gpr y = s.gpr y := by
    rw [k₂.1 y (by simpa using Ne.symm hxy), k₁.1 y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hyd, hyc, hya⟩)]
  have c₂' : s₂.gpr .rcx = s₁.gpr .rcx := k₂.1 _ (by simpa using Ne.symm hxc)
  have x₃ : s₃.gpr x = s₂.gpr x := k₃.1 x (by simpa using hxy)
  rw [x₁] at e₂
  rw [y₂, c₂'] at e₃
  rw [x₃]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide]
  have m₃ := congrArg (2 ^ 64 * ·) e₃
  simp only [Nat.mul_add] at m₃ ⊢
  simp only [Nat.mul_assoc] at m₃ ⊢
  omega

/-- The registers of the pairs `ps`, in order. -/
def pairRegs : List (Reg × Reg) → List Reg
  | [] => []
  | (x, y) :: ps => x :: y :: pairRegs ps

/-- `Σ_{j<k} 2^(128 j) [d + 8j]²`. -/
def sqSum (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (word m base d).toNat * (word m base d).toNat + 2 ^ 128 * sqSum m base (d + 8) k

/-- `sqrDiags ps d`: the words of `ps` doubled and the squares of `[d …]`
added, with the carries CF and OF in and out. -/
theorem sqrDiags_ok {size : Nat} : ∀ (ps : List (Reg × Reg)) {s : State} {base : Addr} {d : Nat}
    {c o : Bool}, Scr s base size → d + 8 * ps.length ≤ size → FreshX (pairRegs ps) →
    s.cf = some c → s.of = some o →
    WP isa (.block (sqrDiags ps d)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' (pairRegs ps) + 2 ^ (128 * ps.length) * (c'.toNat + o'.toNat) =
        2 * regsVal s (pairRegs ps) + sqSum s.mem base d ps.length + c.toNat + o.toNat ∧
      Keeps (.rdx :: .rcx :: .rax :: pairRegs ps) s s'
  | [], s, _, _, c, o, _, _, _, hc, ho => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, o, hc, ho, by simp [regsVal, sqSum, pairRegs], fun _ _ => rfl, rfl, rfl, rfl⟩
  | (x, y) :: ps, s, base, d, c, o, hs, hd, hf, hc, ho => by
    simp only [List.length_cons] at hd
    have hf₂ : FreshX [x, y] := by
      have hn := hf.1
      simp only [pairRegs, List.nodup_cons, List.mem_cons, not_or] at hn
      refine ⟨List.nodup_cons.mpr ⟨by simpa using hn.1.1, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩, fun t ht => hf.2 t ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hfp : FreshX (pairRegs ps) := hf.tail.tail
    rw [sqrDiags, WP.block_append_iff]
    refine WP.mono (sqrDiag_ok hs (d := d) (by omega) hf₂ hc ho) fun s₁ h₁ => ?_
    obtain ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ := h₁
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, Ne.symm (hf₂.head.2.2.2.2), Ne.symm (hf₂.tail.head.2.2.2.2)⟩)
    refine WP.mono (sqrDiags_ok ps hs₁ (d := d + 8) (by omega) hfp cf₁ of₁) fun s₂ h₂ => ?_
    obtain ⟨c₂, o₂, cf₂, of₂, e₂, k₂⟩ := h₂
    refine ⟨c₂, o₂, cf₂, of₂, ?_, ?_⟩
    · have hxn : x ∉ pairRegs ps := fun h => (List.nodup_cons.mp hf.1).1 (List.mem_cons_of_mem _ h)
      have hyn : y ∉ pairRegs ps := (List.nodup_cons.mp (List.nodup_cons.mp hf.1).2).1
      have hP : regsVal s₁ (pairRegs ps) = regsVal s (pairRegs ps) := regsVal_congr fun q hq =>
        k₁.1 q (by
          have := hfp.2 q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨this.2.2.1, this.2.1, this.1, fun h => hxn (h ▸ hq), fun h => hyn (h ▸ hq)⟩)
      have x₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hf₂.head.2.2.2.1, hf₂.head.2.2.1, hf₂.head.2.1, hxn⟩)
      have y₂ : s₂.gpr y = s₁.gpr y := k₂.1 y (by
        simp only [List.mem_cons, not_or]
        exact ⟨hf₂.tail.head.2.2.2.1, hf₂.tail.head.2.2.1, hf₂.tail.head.2.1, hyn⟩)
      rw [hP, k₁.2.1] at e₂
      simp only [pairRegs, regsVal, sqSum, List.length_cons, x₂, y₂] at e₂ ⊢
      rw [show 128 * (ps.length + 1) = 128 + 128 * ps.length by omega, Nat.pow_add]
      rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide] at e₁ ⊢
      generalize 2 ^ (128 * ps.length) = P at e₂ ⊢
      have m₂ := congrArg (2 ^ 64 * 2 ^ 64 * ·) e₂
      simp only [Nat.mul_add] at m₂ e₁ ⊢
      simp only [Nat.mul_assoc, Nat.mul_left_comm 2 (2 ^ 64)] at m₂ e₁ ⊢
      omega
    · show Keeps (.rdx :: .rcx :: .rax :: x :: y :: pairRegs ps) s s₂
      exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-! ## The cross products -/

/-- A word times a number below `Q`: `v W + Q ≤ 2⁶⁴ Q`. -/
theorem mul_word_le {v W Q : Nat} (hv : v < 2 ^ 64) (hW : W < Q) : v * W + Q ≤ 2 ^ 64 * Q := by
  have := Nat.mul_le_mul (Nat.le_pred_of_lt hv) (Nat.le_pred_of_lt hW)
  simp only [Nat.pred_eq_sub_one] at this
  have h1 : (2 ^ 64 - 1) * (Q - 1) + Q ≤ 2 ^ 64 * Q := by
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · simp
    · rw [Nat.mul_sub_one, Nat.sub_one_mul]
      have : Q ≤ 2 ^ 64 * Q := Nat.le_mul_of_pos_left Q (by decide)
      omega
  omega

/-- `mov rdx, [d]`, `xor ebp, ebp`. -/
theorem rowStart_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rdx (.mem (sc d)), Impl.X25519.X86_64.clear]) s fun s' =>
      s'.gpr .rdx = word s.mem base d ∧ s'.gpr .rbp = 0 ∧ s'.cf = some false ∧
      s'.of = some false ∧ Keeps [.rdx, .rbp] s s' := by
  rw [show ([.mov .rdx (.mem (sc d)), Impl.X25519.X86_64.clear] : List Instr) =
    [.mov .rdx (.mem (sc d))] ++ [Impl.X25519.X86_64.clear] from rfl, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs hd)) fun s₁ h₁ => ?_
  obtain ⟨d₁, -, -, k₁⟩ := h₁
  refine WP.mono (clear_ok s₁) fun s₂ h₂ => ?_
  obtain ⟨z₂, cf₂, of₂, k₂⟩ := h₂
  exact ⟨(k₂.1 _ (by decide)).trans d₁, z₂, cf₂, of₂,
    (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-- Row 0 of the cross products: `r8–r13 = a₀ · (a₁, …, a₅)`. -/
theorem row0_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 48 ≤ size) :
    WP isa (.block (sqrRow0 a)) s fun s' => regsVal s' [.r8, .r9, .r10, .r11, .r12, .r13] =
          (word s.mem base a).toNat * wordsVal s.mem base (a + 8) 5 ∧
        Keeps [.rdx, .rbp, .rax, .r8, .r9, .r10, .r11, .r12, .r13] s s' := by
  rw [sqrRow0, show ([.mov .rdx (.mem (sc a)), Impl.X25519.X86_64.clear, .mulx .r9 .r8 (.mem (sc (a + 8)))] :
    List Instr) = [.mov .rdx (.mem (sc a)), Impl.X25519.X86_64.clear] ++ [.mulx .r9 .r8 (.mem (sc (a + 8)))]
    from rfl, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (d := a) (by omega)) fun s₁ h₁ => ?_
  obtain ⟨d₁, z₁, cf₁, of₁, k₁⟩ := h₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s₁ (readSrc_sc hs₁ (d := a + 8) (by omega)) (fun _ h => nomatch h) (by decide))
    fun s₂ h₂ => ?_
  obtain ⟨e₂, cf₂, of₂, k₂⟩ := h₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accRowS_ok 4 .r9 [.r10, .r11, .r12, .r13] hs₂ (d := a + 16) (by omega) rfl
    ⟨by decide, by decide⟩ (cf₂.trans cf₁)) fun s₃ h₃ => ?_
  obtain ⟨c₃, cf₃, -, e₃, k₃⟩ := h₃
  have z₃ : s₃.gpr .rbp = 0 := by rw [k₃.1 _ (by decide), k₂.1 _ (by decide), z₁]
  refine WP.mono (carryC_ok s₃ cf₃ z₃) fun s₄ h₄ => ?_
  obtain ⟨c₄, -, -, e₄, k₄⟩ := h₄
  refine ⟨?_, (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))).trans
    (k₄.mono (by sub_regs))⟩
  have r8 : s₄.gpr .r8 = s₂.gpr .r8 := by rw [k₄.1 _ (by decide), k₃.1 _ (by decide)]
  have rdx : s₂.gpr .rdx = word s.mem base a := by rw [k₂.1 _ (by decide), d₁]
  rw [k₁.2.1] at e₂
  rw [k₂.2.1, k₁.2.1, rdx] at e₃
  rw [d₁] at e₂
  have hb := mul_word_le (word s.mem base a).isLt (wordsVal_lt s.mem base (a + 8) 5)
  rw [show wordsVal s.mem base (a + 8) 5 = (word s.mem base (a + 8)).toNat +
    2 ^ 64 * wordsVal s.mem base (a + 16) 4 from rfl] at hb ⊢
  simp only [regsVal, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e₃ ⊢
  rw [r8, k₄.1 .r9 (by decide), k₄.1 .r10 (by decide), k₄.1 .r11 (by decide), k₄.1 .r12 (by decide)]
  generalize (word s.mem base a).toNat = v at *
  generalize wordsVal s.mem base (a + 16) 4 = W at *
  generalize (word s.mem base (a + 8)).toNat = w at *
  rw [show v * (w + 2 ^ 64 * W) = v * w + 2 ^ 64 * (v * W) by
    rw [Nat.mul_add, Nat.mul_left_comm]] at hb ⊢
  have := (s₄.gpr .r13).isLt
  cases c₄ <;> simp only [Bool.toNat_false, Bool.toNat_true] at e₄ <;> omega

/-- A row `i ≥ 1` of the cross products: `x :: rs` (the last register fresh)
`+= [d₀] · [d …]`, if it does not overflow. -/
theorem rowM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d₀ d : Nat}
    (hd₀ : d₀ + 8 ≤ size) (hd : d + 8 * (n + 1) ≤ size) {x : Reg} {rs : List Reg}
    (hl : rs.length = n + 1) (hf : Fresh (x :: rs))
    (hb : regsVal s (x :: rs.take n) + (word s.mem base d₀).toNat * wordsVal s.mem base d (n + 1) <
      2 ^ (64 * (n + 2))) :
    WP isa (.block (([.mov .rdx (.mem (sc d₀)), Impl.X25519.X86_64.clear] : List Instr) ++
        maddRow (x :: rs) d)) s fun s' =>
      regsVal s' (x :: rs) = regsVal s (x :: rs.take n) +
        (word s.mem base d₀).toNat * wordsVal s.mem base d (n + 1) ∧
      Keeps (.rdx :: .rbp :: .rcx :: .rax :: x :: rs) s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (rowStart_ok hs hd₀) fun s₁ h₁ => ?_
  obtain ⟨d₁, z₁, cf₁, of₁, k₁⟩ := h₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (maddRow_ok n x rs hs₁ hd hl hf z₁ cf₁ of₁) fun s₂ h₂ => ?_
  obtain ⟨c₂, o₂, e₂, k₂⟩ := h₂
  have hR : regsVal s₁ (x :: rs.take n) = regsVal s (x :: rs.take n) := regsVal_congr fun q hq => k₁.1 q (by
    have := hf.2 q (by
      simp only [List.mem_cons] at hq ⊢
      exact hq.imp id List.mem_of_mem_take)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this.2.2.1, this.2.2.2.1⟩)
  rw [hR, k₁.2.1, d₁] at e₂
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  generalize 2 ^ (64 * (n + 2)) = P at hb e₂
  have : P * (c₂.toNat + o₂.toNat) = 0 := by
    rcases Nat.eq_zero_or_pos (c₂.toNat + o₂.toNat) with h | h
    · rw [h, Nat.mul_zero]
    · have : P ≤ P * (c₂.toNat + o₂.toNat) := Nat.le_mul_of_pos_right P h
      omega
  omega

/-- The cross products of `[a]`'s six words, `Σ_{i<j} a_i a_j 2^(64 (i + j - 1))`,
by rows. -/
def crossVal (m : Mem) (base : Addr) (a : Nat) : Nat :=
  (word m base a).toNat * wordsVal m base (a + 8) 5 +
    2 ^ 128 * ((word m base (a + 8)).toNat * wordsVal m base (a + 16) 4 +
    2 ^ 128 * ((word m base (a + 16)).toNat * wordsVal m base (a + 24) 3 +
    2 ^ 128 * ((word m base (a + 24)).toNat * wordsVal m base (a + 32) 2 +
    2 ^ 128 * ((word m base (a + 32)).toNat * wordsVal m base (a + 40) 1))))

/-- The rows' sums make the cross products: their equations, weighted. -/
theorem sqCross_arith {B x1 x2 x3 x4 x5 x6 y3 y4 y5 y6 y7 z5 z6 z7 z8 u7 u8 u9 v9 v10
    T0 T1 T2 T3 T4 : Nat}
    (e₀ : x1 + B * (x2 + B * (x3 + B * (x4 + B * (x5 + B * x6)))) = T0)
    (e₁ : y3 + B * (y4 + B * (y5 + B * (y6 + B * y7))) = x3 + B * (x4 + B * (x5 + B * x6)) + T1)
    (e₂ : z5 + B * (z6 + B * (z7 + B * z8)) = y5 + B * (y6 + B * y7) + T2)
    (e₃ : u7 + B * (u8 + B * u9) = z7 + B * z8 + T3)
    (e₄ : v9 + B * v10 = u9 + T4) :
    x1 + B * x2 + B * B * (y3 + B * (y4 + B * (z5 + B * (z6 + B * (u7 + B * (u8 + B * (v9 +
      B * v10))))))) = T0 + B * B * (T1 + B * B * (T2 + B * B * (T3 + B * B * T4))) := by
  have m₁ := congrArg (B * B * ·) e₁
  have m₂ := congrArg (B * B * B * B * ·) e₂
  have m₃ := congrArg (B * B * B * B * B * B * ·) e₃
  have m₄ := congrArg (B * B * B * B * B * B * B * B * ·) e₄
  grind

theorem sqrRows_eq (a : Nat) : sqrRows a =
    (([.mov .rdx (.mem (sc (a + 8))), Impl.X25519.X86_64.clear] : List Instr) ++
        maddRow [.r10, .r11, .r12, .r13, .r14] (a + 16)) ++
    ((([.mov .rdx (.mem (sc (a + 16))), Impl.X25519.X86_64.clear] : List Instr) ++
        maddRow [.r12, .r13, .r14, .r15] (a + 24)) ++
    ((([.mov .rdx (.mem (sc (a + 24))), Impl.X25519.X86_64.clear] : List Instr) ++
        maddRow [.r14, .r15, .r8] (a + 32)) ++
    (([.mov .rdx (.mem (sc (a + 32))), Impl.X25519.X86_64.clear] : List Instr) ++
        maddRow [.r8, .r9] (a + 40)))) := by
  simp only [sqrRows, List.append_assoc]

/-- The cross products: words 1 and 2 at `[t + 8]`, words 3 to 10 in `r10–r15`,
`r8`, `r9`. -/
theorem sqCross_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t a : Nat}
    (ha : a + 48 ≤ size) (ht : t + 24 ≤ size) (hat : a + 48 ≤ t + 8 ∨ t + 24 ≤ a) :
    WP isa (.block (sqrRow0 a ++ (stores ([.r8, .r9] : List Reg) (t + 8) ++ sqrRows a))) s fun s' =>
      wordsVal s'.mem base (t + 8) 2 + 2 ^ 128 * regsVal s' [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] =
        crossVal s.mem base a ∧
      KeepRegs [.rdx, .rbp, .rcx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      Outside base (t + 8) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  have t₀ := mul_word_le (word s.mem base a).isLt (wordsVal_lt s.mem base (a + 8) 5)
  have t₁ := mul_word_le (word s.mem base (a + 8)).isLt (wordsVal_lt s.mem base (a + 16) 4)
  have t₂ := mul_word_le (word s.mem base (a + 16)).isLt (wordsVal_lt s.mem base (a + 24) 3)
  have t₃ := mul_word_le (word s.mem base (a + 24)).isLt (wordsVal_lt s.mem base (a + 32) 2)
  have t₄ := mul_word_le (word s.mem base (a + 32)).isLt (wordsVal_lt s.mem base (a + 40) 1)
  rw [WP.block_append_iff]
  refine WP.mono (row0_ok hs ha) fun s₀ h₀ => ?_
  obtain ⟨e₀, k₀⟩ := h₀
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok [.r8, .r9] hs₀ (o := t + 8) (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide)) fun s₁ h₁ => ?_
  obtain ⟨e₁', k₁', O₁⟩ := h₁
  have hs₁ := hs₀.of_keepRegs k₁' (by decide)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁' O₁
  rw [k₀.2.1] at O₁
  -- The words the rows read, unchanged by the store.
  have w₁ : word s₁.mem base (a + 8) = word s.mem base (a + 8) := O₁.word (by omega) (by omega)
  have w₂ : word s₁.mem base (a + 16) = word s.mem base (a + 16) := O₁.word (by omega) (by omega)
  have w₃ : word s₁.mem base (a + 24) = word s.mem base (a + 24) := O₁.word (by omega) (by omega)
  have w₄ : word s₁.mem base (a + 32) = word s.mem base (a + 32) := O₁.word (by omega) (by omega)
  have W₁ : wordsVal s₁.mem base (a + 16) 4 = wordsVal s.mem base (a + 16) 4 := O₁.wordsVal (by omega) (by omega)
  have W₂ : wordsVal s₁.mem base (a + 24) 3 = wordsVal s.mem base (a + 24) 3 := O₁.wordsVal (by omega) (by omega)
  have W₃ : wordsVal s₁.mem base (a + 32) 2 = wordsVal s.mem base (a + 32) 2 := O₁.wordsVal (by omega) (by omega)
  have W₄ : wordsVal s₁.mem base (a + 40) 1 = wordsVal s.mem base (a + 40) 1 := O₁.wordsVal (by omega) (by omega)
  have g₁ : ∀ r, s₁.gpr r = s₀.gpr r := fun r => k₁'.gpr r (by simp)
  rw [sqrRows_eq, WP.block_append_iff]
  have hb₁ : regsVal s₁ [.r10, .r11, .r12, .r13] + (word s₁.mem base (a + 8)).toNat *
      wordsVal s₁.mem base (a + 16) 4 < 2 ^ (64 * (3 + 2)) := by
    rw [w₁, W₁]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, g₁] at e₀ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    omega
  refine WP.mono (rowM_ok hs₁ (n := 3) (by omega) (by omega) rfl ⟨by decide, by decide⟩ hb₁) fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂⟩ := h₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [w₁, W₁] at e₂
  rw [WP.block_append_iff]
  have hb₂ : regsVal s₂ [.r12, .r13, .r14] + (word s₂.mem base (a + 16)).toNat *
      wordsVal s₂.mem base (a + 24) 3 < 2 ^ (64 * (2 + 2)) := by
    rw [k₂.2.1, w₂, W₂]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.take, Nat.reduceAdd, g₁] at e₀ e₂ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
    omega
  refine WP.mono (rowM_ok hs₂ (n := 2) (by omega) (by omega) rfl ⟨by decide, by decide⟩ hb₂) fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃⟩ := h₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [k₂.2.1, w₂, W₂] at e₃
  rw [WP.block_append_iff]
  have hb₃ : regsVal s₃ [.r14, .r15] + (word s₃.mem base (a + 24)).toNat *
      wordsVal s₃.mem base (a + 32) 2 < 2 ^ (64 * (1 + 2)) := by
    rw [k₃.2.1, k₂.2.1, w₃, W₃]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.take, Nat.reduceAdd, g₁] at e₀ e₂ e₃ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
    have := (s₃.gpr .r12).isLt; have := (s₃.gpr .r13).isLt
    omega
  refine WP.mono (rowM_ok hs₃ (n := 1) (by omega) (by omega) rfl ⟨by decide, by decide⟩ hb₃) fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [k₃.2.1, k₂.2.1, w₃, W₃] at e₄
  have hb₄ : regsVal s₄ [.r8] + (word s₄.mem base (a + 32)).toNat *
      wordsVal s₄.mem base (a + 40) 1 < 2 ^ (64 * (0 + 2)) := by
    rw [k₄.2.1, k₃.2.1, k₂.2.1, w₄, W₄]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.take, Nat.reduceAdd, g₁] at e₀ e₂ e₃ e₄ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
    have := (s₃.gpr .r12).isLt; have := (s₃.gpr .r13).isLt
    have := (s₄.gpr .r14).isLt; have := (s₄.gpr .r15).isLt
    omega
  refine WP.mono (rowM_ok hs₄ (n := 0) (by omega) (by omega) rfl ⟨by decide, by decide⟩ hb₄) fun s₅ h₅ => ?_
  obtain ⟨e₅, k₅⟩ := h₅
  rw [k₄.2.1, k₃.2.1, k₂.2.1, w₄, W₄] at e₅
  have K : KeepRegs [.rdx, .rbp, .rcx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s₅ := by
    clear t₀ t₁ t₂ t₃ t₄ hb₁ hb₂ hb₃ hb₄ e₀ e₂ e₃ e₄ e₅
    exact ⟨fun r hr => by
        rw [k₅.1 r (not_mem_of hr (by decide)), k₄.1 r (not_mem_of hr (by decide)),
          k₃.1 r (not_mem_of hr (by decide)), k₂.1 r (not_mem_of hr (by decide)), g₁,
          k₀.1 r (not_mem_of hr (by decide))],
      by rw [k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁'.rd, k₀.2.2.1],
      by rw [k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁'.wr, k₀.2.2.2]⟩
  have m₅ : s₅.mem = s₁.mem := by rw [k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1]
  refine ⟨?_, K, by rw [m₅]; exact O₁⟩
  rw [m₅, e₁']
  simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.take, g₁] at e₀ e₂ e₃ e₄ e₅ ⊢
  rw [k₅.1 .r10 (by decide), k₄.1 .r10 (by decide), k₃.1 .r10 (by decide),
    k₅.1 .r11 (by decide), k₄.1 .r11 (by decide), k₃.1 .r11 (by decide),
    k₅.1 .r12 (by decide), k₄.1 .r12 (by decide), k₅.1 .r13 (by decide), k₄.1 .r13 (by decide),
    k₅.1 .r14 (by decide), k₅.1 .r15 (by decide)]
  simp only [crossVal]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by rfl]
  exact sqCross_arith e₀ e₂ e₃ e₄ e₅

/-! ## The square -/

/-- `sqSum` with its last square split off. -/
theorem sqSum_snoc (m : Mem) (base : Addr) : ∀ (d k : Nat),
    sqSum m base d (k + 1) = sqSum m base d k +
      2 ^ (128 * k) * ((word m base (d + 8 * k)).toNat * (word m base (d + 8 * k)).toNat)
  | d, 0 => by simp [sqSum]
  | d, k + 1 => by
    rw [sqSum, sqSum_snoc m base (d + 8) k, sqSum]
    rw [show d + 8 + 8 * k = d + 8 * (k + 1) by omega, show 128 * (k + 1) = 128 + 128 * k by omega,
      Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- `(v₀ + B (v₁ + …))² = 2B · (the cross products by rows) + Σ B^(2i) v_i²`. -/
theorem sq_arith {B v0 v1 v2 v3 v4 v5 : Nat} :
    (v0 + B * (v1 + B * (v2 + B * (v3 + B * (v4 + B * v5))))) *
      (v0 + B * (v1 + B * (v2 + B * (v3 + B * (v4 + B * v5))))) =
    2 * B * (v0 * (v1 + B * (v2 + B * (v3 + B * (v4 + B * v5)))) +
      B * B * (v1 * (v2 + B * (v3 + B * (v4 + B * v5))) +
      B * B * (v2 * (v3 + B * (v4 + B * v5)) +
      B * B * (v3 * (v4 + B * v5) +
      B * B * (v4 * v5))))) +
    (v0 * v0 + B * B * (v1 * v1 + B * B * (v2 * v2 + B * B * (v3 * v3 + B * B * (v4 * v4 +
      B * B * (v5 * v5)))))) := by
  grind

/-- `[a]² = 2⁶⁵ C + Σ 2^(128 i) a_i²` for the cross products `C`. -/
theorem sq_eq (m : Mem) (base : Addr) (a : Nat) :
    wordsVal m base a 6 * wordsVal m base a 6 = 2 * 2 ^ 64 * crossVal m base a + sqSum m base a 6 := by
  simp only [wordsVal, crossVal, sqSum, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by rfl]
  exact sq_arith

theorem pow128 (x : Nat) : x ^ 128 = x ^ 64 * x ^ 64 := by
  rw [show 128 = 64 + 64 from rfl, Nat.pow_add]
theorem pow64x3 (x : Nat) : x ^ (64 * 3) = x ^ 64 * x ^ 64 * x ^ 64 := by
  rw [show 64 * 3 = 64 + 64 + 64 from rfl]; simp only [Nat.pow_add]
theorem pow64x6 (x : Nat) : x ^ (64 * 6) = x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 := by
  rw [show 64 * 6 = 64 + 64 + 64 + 64 + 64 + 64 from rfl]; simp only [Nat.pow_add]
theorem pow128x3 (x : Nat) : x ^ (128 * 3) = x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 := by
  rw [show 128 * 3 = 64 + 64 + 64 + 64 + 64 + 64 from rfl]; simp only [Nat.pow_add]
theorem pow64x12 (x : Nat) : x ^ (64 * 12) = x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 *
    x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 * x ^ 64 := by
  rw [show 64 * 12 = 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 from rfl]
  simp only [Nat.pow_add]

/-- The doubling and the squares: the steps' equations, weighted. -/
theorem sqDbl_arith {B m1 m2 x10 X6 x9 v0 v1 v5 S3 lo0 hi0 w0 c3 o3 w1 c5 o5 lo1 hi1 w2 c9 o9 w3 c11 o11
    Y6 c12 o12 lo5 hi5 w10 c14 o14 w11 c15 o15 : Nat}
    (E2 : lo0 + B * hi0 = v0) (E3 : w0 + B * (c3 + o3) = 2 * 0 + lo0 + 0 + 0)
    (E5 : w1 + B * (c5 + o5) = 2 * m1 + hi0 + c3 + o3) (E7 : lo1 + B * hi1 = v1)
    (E9 : w2 + B * (c9 + o9) = 2 * m2 + lo1 + c5 + o5) (E11 : w3 + B * (c11 + o11) = 2 * x10 + hi1 + c9 + o9)
    (E12 : Y6 + B * B * B * B * B * B * (c12 + o12) = 2 * X6 + S3 + c11 + o11)
    (E13 : lo5 + B * hi5 = v5) (E14 : w10 + B * (c14 + o14) = 2 * x9 + lo5 + c12 + o12)
    (E15 : w11 + B * (c15 + o15) = hi5 + c14 + o14) :
    w0 + B * (w1 + B * w2) + B * B * B * (w3 + B * (Y6 + B * B * B * B * B * B * (w10 + B * w11))) +
      B * B * B * B * B * B * B * B * B * B * B * B * (c15 + o15) =
    2 * B * (m1 + B * m2 + B * B * (x10 + B * (X6 + B * B * B * B * B * B * x9))) +
      (v0 + B * B * (v1 + B * B * (S3 + B * B * B * B * B * B * v5))) := by
  have m5 := congrArg (B * ·) E5
  have m7 := congrArg (B * B * ·) E7
  have m9 := congrArg (B * B * ·) E9
  have m11 := congrArg (B * B * B * ·) E11
  have m12 := congrArg (B * B * B * B * ·) E12
  have m13 := congrArg (B * B * B * B * B * B * B * B * B * B * ·) E13
  have m14 := congrArg (B * B * B * B * B * B * B * B * B * B * ·) E14
  have m15 := congrArg (B * B * B * B * B * B * B * B * B * B * B * ·) E15
  grind

/-- `mov [d], r`: the memory with the word, the rest of the state as it was. -/
theorem st1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size)
    (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun s' => s'.mem = s.mem.writeW (off base d) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_sc hs hd, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem sqrDbl_eq (t a : Nat) : sqrDbl t a = [Impl.X25519.X86_64.clear] ++
    (([.mov .rdx (.mem (sc a)), .mulx .rcx .rax (.reg .rdx)] : List Instr) ++
    (Impl.X25519.X86_64.dblAdd .rbp .rax ++ (([.store (sc t) .rbp] : List Instr) ++
    (([.mov .rdx (.mem (sc (t + 8)))] : List Instr) ++ (Impl.X25519.X86_64.dblAdd .rdx .rcx ++
    (([.store (sc (t + 8)) .rdx] : List Instr) ++
    (([.mov .rdx (.mem (sc (a + 8))), .mulx .rcx .rax (.reg .rdx)] : List Instr) ++
    (([.mov .rdx (.mem (sc (t + 16)))] : List Instr) ++ (Impl.X25519.X86_64.dblAdd .rdx .rax ++
    (([.store (sc (t + 16)) .rdx] : List Instr) ++ (Impl.X25519.X86_64.dblAdd .r10 .rcx ++
    (sqrDiags [(.r11, .r12), (.r13, .r14), (.r15, .r8)] (a + 16) ++
    (([.mov .rdx (.mem (sc (a + 40))), .mulx .rcx .rax (.reg .rdx)] : List Instr) ++
    (Impl.X25519.X86_64.dblAdd .r9 .rax ++
    (([.mov32 .rdx (.imm 0)] : List Instr) ++
      ([.adcx .rcx (.reg .rdx), .adox .rcx (.reg .rdx)] : List Instr)))))))))))))))) := by
  simp only [sqrDbl, List.append_assoc]; rfl

/-- The cross products (words 1 and 2 at `[t + 8]`, 3 to 10 in `r10–r15`, `r8`,
`r9`) doubled and the squares added: words 0 to 2 at `[t]`, 3 to 11 in
`r10–r15`, `r8`, `r9`, `rcx`, if it fits. -/
theorem sqrDbl_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t a : Nat}
    (ha : a + 48 ≤ size) (ht : t + 24 ≤ size) (hat : a + 48 ≤ t ∨ t + 24 ≤ a)
    (hC : 2 * 2 ^ 64 * (wordsVal s.mem base (t + 8) 2 +
      2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) + sqSum s.mem base a 6 <
      2 ^ (64 * 12)) :
    WP isa (.block (sqrDbl t a)) s fun s' =>
      wordsVal s'.mem base t 3 + 2 ^ (64 * 3) * regsVal s' [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        2 * 2 ^ 64 * (wordsVal s.mem base (t + 8) 2 +
          2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) + sqSum s.mem base a 6 ∧
      KeepRegs [.rdx, .rcx, .rax, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      Outside base t 24 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [pow64x12 2] at hC
  rw [sqrDbl_eq, WP.block_append_iff]
  refine WP.mono (clear_ok s) fun s₁ h₁ => ?_
  obtain ⟨z₁, cf₁, of₁, k₁⟩ := h₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs₁ (d := a) (by omega)) fun s₂ h₂ => ?_
  obtain ⟨E2, cf₂, of₂, k₂⟩ := h₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s₂ (x := .rbp) (y := .rax) (cf₂.trans cf₁) (of₂.trans of₁) (by decide))
    fun s₃ h₃ => ?_
  obtain ⟨c₃, o₃, cf₃, of₃, E3, k₃⟩ := h₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₃ (d := t) (by omega) .rbp) fun s₄ h₄ => ?_
  obtain ⟨M₄, G₄, cf₄, of₄, rd₄, wr₄⟩ := h₄
  have hs₄ : Scr s₄ base size := ⟨by rw [G₄]; exact hs₃.rdi, wr₄ ▸ hs₃.wr, hs₃.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (movRdx_ok s₄ (readSrc_sc hs₄ (d := t + 8) (by omega))) fun s₅ h₅ => ?_
  obtain ⟨d₅, cf₅, of₅, k₅⟩ := h₅
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s₅ (x := .rdx) (y := .rcx) (cf₅.trans (cf₄.trans cf₃)) (of₅.trans (of₄.trans of₃))
    (by decide))
    fun s₆ h₆ => ?_
  obtain ⟨c₆, o₆, cf₆, of₆, E5, k₆⟩ := h₆
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₆ (d := t + 8) (by omega) .rdx) fun s₇ h₇ => ?_
  obtain ⟨M₇, G₇, cf₇, of₇, rd₇, wr₇⟩ := h₇
  have hs₇ : Scr s₇ base size := ⟨by rw [G₇]; exact hs₆.rdi, wr₇ ▸ hs₆.wr, hs₆.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs₇ (d := a + 8) (by omega)) fun s₈ h₈ => ?_
  obtain ⟨E7, cf₈, of₈, k₈⟩ := h₈
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRdx_ok s₈ (readSrc_sc hs₈ (d := t + 16) (by omega))) fun s₉ h₉ => ?_
  obtain ⟨d₉, cf₉, of₉, k₉⟩ := h₉
  have hs₉ := hs₈.of_keeps k₉ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s₉ (x := .rdx) (y := .rax) (cf₉.trans (cf₈.trans (cf₇.trans cf₆)))
    (of₉.trans (of₈.trans (of₇.trans of₆))) (by decide)) fun s₁₀ h₁₀ => ?_
  obtain ⟨c₁₀, o₁₀, cf₁₀, of₁₀, E9, k₁₀⟩ := h₁₀
  have hs₁₀ := hs₉.of_keeps k₁₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₁₀ (d := t + 16) (by omega) .rdx) fun s₁₁ h₁₁ => ?_
  obtain ⟨M₁₁, G₁₁, cf₁₁, of₁₁, rd₁₁, wr₁₁⟩ := h₁₁
  have hs₁₁ : Scr s₁₁ base size := ⟨by rw [G₁₁]; exact hs₁₀.rdi, wr₁₁ ▸ hs₁₀.wr, hs₁₀.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s₁₁ (x := .r10) (y := .rcx) (cf₁₁.trans cf₁₀) (of₁₁.trans of₁₀) (by decide))
    fun s₁₂ h₁₂ => ?_
  obtain ⟨c₁₂, o₁₂, cf₁₂, of₁₂, E11, k₁₂⟩ := h₁₂
  have hs₁₂ := hs₁₁.of_keeps k₁₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqrDiags_ok [(.r11, .r12), (.r13, .r14), (.r15, .r8)] hs₁₂ (d := a + 16)
    (by simp only [List.length_cons, List.length_nil]; omega) ⟨by decide, by decide⟩ cf₁₂ of₁₂)
    fun s₁₃ h₁₃ => ?_
  obtain ⟨c₁₃, o₁₃, cf₁₃, of₁₃, E12, k₁₃⟩ := h₁₃
  have hs₁₃ := hs₁₂.of_keeps k₁₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs₁₃ (d := a + 40) (by omega)) fun s₁₄ h₁₄ => ?_
  obtain ⟨E13, cf₁₄, of₁₄, k₁₄⟩ := h₁₄
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s₁₄ (x := .r9) (y := .rax) (cf₁₄.trans cf₁₃) (of₁₄.trans of₁₃) (by decide))
    fun s₁₅ h₁₅ => ?_
  obtain ⟨c₁₅, o₁₅, cf₁₅, of₁₅, E14, k₁₅⟩ := h₁₅
  rw [WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s₁₅ 0) fun s₁₆ h₁₆ => ?_
  obtain ⟨z₁₆, cf₁₆, of₁₆, k₁₆⟩ := h₁₆
  refine WP.mono (carriesZ_ok s₁₆ (x := .rcx) (z := .rdx) (cf₁₆.trans cf₁₅) (of₁₆.trans of₁₅)
    (BitVec.eq_of_toNat_eq (by rw [z₁₆]; rfl)) (by decide)) fun s₁₇ h₁₇ => ?_
  obtain ⟨c₁₇, o₁₇, -, -, E15, k₁₇⟩ := h₁₇
  -- Memory: the three words stored, the rest as it was.
  have hm₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have hm₆ : s₆.mem = s₄.mem := by rw [k₆.2.1, k₅.2.1]
  have hm₁₀ : s₁₀.mem = s₇.mem := by rw [k₁₀.2.1, k₉.2.1, k₈.2.1]
  have hm₁₇ : s₁₇.mem = s₁₁.mem := by
    rw [k₁₇.2.1, k₁₆.2.1, k₁₅.2.1, k₁₄.2.1, k₁₃.2.1, k₁₂.2.1]
  have O₄ : Outside base t 8 s.mem s₄.mem := by rw [M₄, hm₃]; exact writeW_outside _ _ _ (by omega)
  have O₇ : Outside base (t + 8) 8 s₄.mem s₇.mem := by rw [M₇, hm₆]; exact writeW_outside _ _ _ (by omega)
  have O₁₁ : Outside base (t + 16) 8 s₇.mem s₁₁.mem := by rw [M₁₁, hm₁₀]; exact writeW_outside _ _ _ (by omega)
  have Ot : Outside base t 24 s.mem s₁₇.mem := by
    rw [hm₁₇]; exact ((O₄.mono (by omega) (by omega)).trans (O₇.mono (by omega) (by omega))).trans
      (O₁₁.mono (by omega) (by omega))
  have wa : ∀ d, (d + 8 ≤ t ∨ t + 24 ≤ d) → d + 8 ≤ size → word s₁₇.mem base d = word s.mem base d :=
    fun d hd hd' => Ot.word hd (by omega)
  -- The words read.
  have rd₅ : s₅.gpr .rdx = word s.mem base (t + 8) := by rw [d₅, O₄.word (by omega) (by omega)]
  have rd₉ : s₉.gpr .rdx = word s.mem base (t + 16) := by
    rw [d₉, k₈.2.1, M₇, hm₆, (writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
      O₄.word (by omega) (by omega)]
  have a₇ : word s₇.mem base (a + 8) = word s.mem base (a + 8) := by
    rw [M₇, hm₆, (writeW_outside _ _ _ (by omega)).word (by omega) (by omega), O₄.word (by omega) (by omega)]
  have a₁₃ : ∀ d, (d + 8 ≤ t ∨ t + 24 ≤ d) → d + 8 ≤ size → word s₁₃.mem base d = word s.mem base d :=
    fun d hd hd' => by rw [← wa d hd hd', hm₁₇, k₁₃.2.1, k₁₂.2.1]
  -- The words stored.
  have hw2 : word s₁₇.mem base (t + 16) = s₁₀.gpr .rdx := by rw [hm₁₇, M₁₁, word_writeW_self]
  have hw1 : word s₁₇.mem base (t + 8) = s₆.gpr .rdx := by
    rw [hm₁₇, M₁₁, (writeW_outside s₁₀.mem base (d := t + 16) _ (by omega)).word (by omega) (by omega),
      hm₁₀, M₇, word_writeW_self]
  have hw0 : word s₁₇.mem base t = s₃.gpr .rbp := by
    rw [hm₁₇, M₁₁, (writeW_outside s₁₀.mem base (d := t + 16) _ (by omega)).word (by omega) (by omega),
      hm₁₀, M₇, (writeW_outside s₆.mem base (d := t + 8) _ (by omega)).word (by omega) (by omega),
      hm₆, M₄, word_writeW_self]
  have st : wordsVal s₁₇.mem base t 3 = (s₃.gpr .rbp).toNat + 2 ^ 64 * ((s₆.gpr .rdx).toNat +
      2 ^ 64 * (s₁₀.gpr .rdx).toNat) := by
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
    rw [hw0, hw1, show t + 8 + 8 = t + 16 from rfl, hw2]
  -- The registers along the way.
  have g₁₁ : ∀ r, r ∉ ([.rdx, .rcx, .rax, .rbp] : List Reg) → s₁₁.gpr r = s.gpr r := fun r hr => by
    rw [G₁₁, k₁₀.1 r (not_mem_of hr (by decide)), k₉.1 r (not_mem_of hr (by decide)),
      k₈.1 r (not_mem_of hr (by decide)), G₇, k₆.1 r (not_mem_of hr (by decide)),
      k₅.1 r (not_mem_of hr (by decide)), G₄, k₃.1 r (not_mem_of hr (by decide)),
      k₂.1 r (not_mem_of hr (by decide)), k₁.1 r (not_mem_of hr (by decide))]
  have hP : regsVal s₁₂ [.r11, .r12, .r13, .r14, .r15, .r8] = regsVal s [.r11, .r12, .r13, .r14, .r15, .r8] :=
    regsVal_congr fun q hq => by
      have h₁ : q ∉ ([.rdx, .rcx, .rax, .rbp] : List Reg) := by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h | h | h <;> cases h
      have h₂ : q ∉ ([.r10] : List Reg) := by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases h
      rw [k₁₂.1 q h₂, g₁₁ q h₁]
  have hP' : regsVal s₁₇ [.r11, .r12, .r13, .r14, .r15, .r8] = regsVal s₁₃ [.r11, .r12, .r13, .r14, .r15, .r8] :=
    regsVal_congr fun q hq => by
      have h : q ∉ ([.rdx, .rcx, .rax, .r9] : List Reg) := by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h | h | h <;> cases h
      rw [k₁₇.1 q (not_mem_of h (by decide)), k₁₆.1 q (not_mem_of h (by decide)),
        k₁₅.1 q (not_mem_of h (by decide)), k₁₄.1 q (not_mem_of h (by decide))]
  have z₂ : (s₂.gpr .rbp).toNat = 0 := by rw [k₂.1 _ (by decide), z₁]; rfl
  rw [k₁.2.1] at E2
  rw [z₂] at E3
  rw [rd₅, k₅.1 .rcx (by decide), G₄, k₃.1 .rcx (by decide)] at E5
  rw [a₇] at E7
  rw [rd₉, k₉.1 .rax (by decide)] at E9
  rw [g₁₁ .r10 (by decide), G₁₁, k₁₀.1 .rcx (by decide), k₉.1 .rcx (by decide)] at E11
  simp only [pairRegs, List.length_cons, List.length_nil, Nat.reduceAdd] at E12
  rw [hP, pow128x3 2] at E12
  rw [a₁₃ (a + 40) (by omega) (by omega)] at E13
  rw [k₁₄.1 .r9 (by decide), k₁₃.1 .r9 (by decide), k₁₂.1 .r9 (by decide), g₁₁ .r9 (by decide)] at E14
  rw [k₁₆.1 .rcx (by decide), k₁₅.1 .rcx (by decide)] at E15
  -- `sqSum` of the words of `a` the steps read.
  have hS3 : sqSum s₁₂.mem base (a + 16) 3 = sqSum s.mem base (a + 16) 3 := by
    have h₁ := a₁₃ (a + 16) (by omega) (by omega); have h₂ := a₁₃ (a + 24) (by omega) (by omega)
    have h₃ := a₁₃ (a + 32) (by omega) (by omega)
    rw [k₁₃.2.1] at h₁ h₂ h₃
    simp only [sqSum, Nat.add_assoc, Nat.reduceAdd, h₁, h₂, h₃]
  rw [hS3] at E12
  have hsq : sqSum s.mem base a 6 = (word s.mem base a).toNat * (word s.mem base a).toNat +
      2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat +
      2 ^ 128 * sqSum s.mem base (a + 16) (3 + 1)) := rfl
  rw [sqSum_snoc s.mem base (a + 16) 3, show a + 16 + 8 * 3 = a + 40 from rfl, pow128x3 2] at hsq
  have K : KeepRegs [.rdx, .rcx, .rax, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s₁₇ := by
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [k₁₇.1 r (not_mem_of hr (by decide)), k₁₆.1 r (not_mem_of hr (by decide)),
        k₁₅.1 r (not_mem_of hr (by decide)), k₁₄.1 r (not_mem_of hr (by decide)),
        k₁₃.1 r (not_mem_of hr (by decide)), k₁₂.1 r (not_mem_of hr (by decide)),
        g₁₁ r (not_mem_of hr (by decide))]
    · rw [k₁₇.2.2.1, k₁₆.2.2.1, k₁₅.2.2.1, k₁₄.2.2.1, k₁₃.2.2.1, k₁₂.2.2.1, rd₁₁, k₁₀.2.2.1, k₉.2.2.1,
        k₈.2.2.1, rd₇, k₆.2.2.1, k₅.2.2.1, rd₄, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₁₇.2.2.2, k₁₆.2.2.2, k₁₅.2.2.2, k₁₄.2.2.2, k₁₃.2.2.2, k₁₂.2.2.2, wr₁₁, k₁₀.2.2.2, k₉.2.2.2,
        k₈.2.2.2, wr₇, k₆.2.2.2, k₅.2.2.2, wr₄, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  refine ⟨?_, K, Ot⟩
  -- The result's registers.
  have hr₁₇ : regsVal s₁₇ [.r10] = (s₁₂.gpr .r10).toNat := by
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    rw [k₁₇.1 .r10 (by decide), k₁₆.1 .r10 (by decide), k₁₅.1 .r10 (by decide), k₁₄.1 .r10 (by decide),
      k₁₃.1 .r10 (by decide)]
  have hr₉ : regsVal s₁₇ [.r9, .rcx] = (s₁₅.gpr .r9).toNat + 2 ^ 64 * (s₁₇.gpr .rcx).toNat := by
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    rw [k₁₇.1 .r9 (by decide), k₁₆.1 .r9 (by decide)]
  have hs₁₀ : regsVal s [.r10] = (s.gpr .r10).toNat := by simp only [regsVal, Nat.mul_zero, Nat.add_zero]
  have hs₉ : regsVal s [.r9] = (s.gpr .r9).toNat := by simp only [regsVal, Nat.mul_zero, Nat.add_zero]
  have hm12 : wordsVal s.mem base (t + 8) 2 =
      (word s.mem base (t + 8)).toNat + 2 ^ 64 * (word s.mem base (t + 16)).toNat := by
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
  rw [st, show ([.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] : List Reg) =
    [.r10] ++ ([.r11, .r12, .r13, .r14, .r15, .r8] ++ [.r9, .rcx]) from rfl, regsVal_append, regsVal_append, hP',
    hr₁₇, hr₉]
  rw [show ([.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] : List Reg) =
    [.r10] ++ ([.r11, .r12, .r13, .r14, .r15, .r8] ++ [.r9]) from rfl, regsVal_append, regsVal_append, hs₁₀, hs₉,
    hm12, hsq] at hC ⊢
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Bool.toNat_false, Nat.add_zero] at hC E3 ⊢
  rw [show 64 * 1 = 64 from rfl, pow64x6 2, pow128 2] at hC
  rw [show 64 * 1 = 64 from rfl, pow64x6 2, pow128 2, pow64x3 2]
  have key := sqDbl_arith E2 E3 E5 E7 E9 E11 E12 E13 E14 E15
  generalize (2 : Nat) ^ 64 = B at hC key ⊢
  generalize B * B * B * B * B * B * B * B * B * B * B * B = Q at hC key
  cases c₁₇ <;> cases o₁₇ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero, Nat.zero_add,
    Nat.mul_zero, Nat.mul_one] at key
  · exact key
  all_goals (rw [← key] at hC; omega)



/-! ## The reductions -/

/-- P-384's `p` against `2³⁸⁴`. -/
theorem p384_bounds {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    m < 2 ^ (64 * 6) ∧ 2 ^ (64 * 6) ≤ 2 ^ 64 * m := by
  rw [pow_split 2 (64 * 3) (64 * 3) (64 * 6) rfl]
  subst hm; omega

/-- The window of round `i`, word by word. -/
theorem sqWins_eq (i : Nat) : sqWins i = [sqW i 0, sqW i 1, sqW i 2, sqW i 3, sqW i 4, sqW i 5] := rfl

/-- The next round's window: the words rotated by one. -/
theorem sqWins_succ (i : Nat) : sqWins (i + 1) = [sqW i 1, sqW i 2, sqW i 3, sqW i 4, sqW i 5, sqW i 0] := by
  simp only [sqWins_eq, sqW]
  have e : ∀ j, (i + 1 + j) % 6 = (i + (j + 1)) % 6 := fun j => by rw [Nat.add_right_comm, Nat.add_assoc]
  rw [e 0, e 1, e 2, e 3, e 4, show (i + 1 + 5) % 6 = (i + 0) % 6 by omega]

theorem sqW_mod (i j : Nat) : sqW i j = sqW (i % 6) j := by
  unfold sqW; rw [show (i + j) % 6 = (i % 6 + j) % 6 by omega]

theorem sqWins_mod (i : Nat) : sqWins i = sqWins (i % 6) := by
  rw [sqWins_eq, sqWins_eq, sqW_mod i 0, sqW_mod i 1, sqW_mod i 2, sqW_mod i 3, sqW_mod i 4, sqW_mod i 5]

theorem six_cases {k : Nat} (h : k < 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega

theorem fresh_sqWins (i : Nat) : Fresh (sqWins i) := by
  rw [sqWins_mod]
  rcases six_cases (Nat.mod_lt i (by decide : 6 > 0)) with h | h | h | h | h | h <;> rw [h] <;>
    exact ⟨by decide, by decide⟩

/-- Every window is `sqWin6`'s registers. -/
theorem sqWins_sub (i : Nat) : ∀ q ∈ sqWins i, q ∈ sqWin6 := by
  rw [sqWins_mod]
  rcases six_cases (Nat.mod_lt i (by decide : 6 > 0)) with h | h | h | h | h | h <;> rw [h] <;> decide

/-- `k` of P-384's reductions on six words from `sqWin6`, from `T < 2³⁸⁴`:
`2^(64k) T' = T + U p` with `U < 2^(64k)`, and `T' < 2³⁸⁴`. -/
theorem redsShortX_ok {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    ∀ k {s : State}, regsVal s (sqWins 0) < 2 ^ (64 * 6) →
      WP isa (.block (redsShortX k)) s fun s' =>
        (∃ U, U < 2 ^ (64 * k) ∧ 2 ^ (64 * k) * regsVal s' (sqWins k) = regsVal s (sqWins 0) + U * m) ∧
        regsVal s' (sqWins k) < 2 ^ (64 * 6) ∧
        Keeps (.rax :: .rcx :: .rdx :: .rbp :: sqWin6) s s'
  | 0, s, h0 => WP.block_nil ⟨⟨0, by simp⟩, h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, s, h0 => by
    obtain ⟨hm1, hm2⟩ := p384_bounds hm
    rw [redsShortX, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (redsShortX_ok hm k h0) fun s₁ h₁ => ?_
    obtain ⟨⟨U, hU, eU⟩, hT, k₁⟩ := h₁
    have hf := fresh_sqWins k
    rw [sqWins_eq] at hf hT
    rw [sqWins_eq]
    refine WP.mono (redShortX_ok hf hm) fun s₂ h₂ => ?_
    obtain ⟨⟨u, hu, eu⟩, k₂⟩ := h₂
    rw [← sqWins_succ] at eu
    rw [← sqWins_eq] at hT eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_, ?_⟩, ?_, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · have : 2 ^ (64 * k) * u ≤ 2 ^ (64 * k) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ, Nat.pow_add]
      rw [Nat.mul_sub_one] at this
      omega
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (sqWins (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (sqWins (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * regsVal s₁ (sqWins k) + 2 ^ (64 * k) * u * m := by
            rw [eu, Nat.mul_add, Nat.mul_assoc]
        _ = _ := by rw [eU, Nat.add_mul]; omega
    · have hm1' := hm1
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_
      rw [eu]
      generalize (2 : Nat) ^ (64 * 6) = Q at hT hm1' ⊢
      generalize (2 : Nat) ^ 64 = B at hu ⊢
      have h1 : u * m ≤ (B - 1) * Q := Nat.mul_le_mul (by omega) (Nat.le_of_lt hm1')
      have h2 : (B - 1) * Q + Q = B * Q := by
        rw [Nat.sub_one_mul]; have : Q ≤ B * Q := Nat.le_mul_of_pos_left Q (by omega); omega
      omega
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (sqWins_sub k q (by rw [sqWins_eq]; simp only [List.mem_cons]; exact h)))))

/-! ## The squaring -/

/-- The values of `[a]` in memories that agree on its words. -/
theorem vals_congr {m m' : Mem} {base : Addr} {a : Nat}
    (h : ∀ i, i < 6 → word m' base (a + 8 * i) = word m base (a + 8 * i)) :
    crossVal m' base a = crossVal m base a ∧ sqSum m' base a 6 = sqSum m base a 6 ∧
      wordsVal m' base a 6 = wordsVal m base a 6 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3 h4 h5
  simp only [crossVal, sqSum, wordsVal, Nat.add_assoc, Nat.reduceAdd, h0, h1, h2, h3, h4, h5]
  exact ⟨trivial, trivial, trivial⟩

/-- `A² < 2⁷⁶⁸` for `A < 2³⁸⁴`. -/
theorem sq_lt {A : Nat} (h : A < 2 ^ (64 * 6)) : A * A < 2 ^ (64 * 12) := by
  rw [pow_split 2 (64 * 6) (64 * 6) (64 * 12) rfl]
  generalize 2 ^ (64 * 6) = P at h ⊢
  exact Nat.mul_lt_mul'' h h

/-- The end of `sqrS`: `2³⁸⁴ V = L + U p` and `[a]² = L + 2³⁸⁴ H` make
`V ≤ p`, `H < p`, and `(V + H) mod p` the result. -/
theorem final_arith {Q L U V H AA m : Nat} (hQ : 0 < Q) (eV : Q * V = L + U * m) (hU : U < Q)
    (hL : L < Q) (eA : AA = L + Q * H) (hA : AA < m * m) (hm : m < Q) :
    V ≤ m ∧ H < m ∧ (V + H) % m * Q % m = AA % m := by
  have hV : V ≤ m := by
    have : Q * V < Q * (m + 1) := by
      rw [eV, Nat.mul_add, Nat.mul_one]
      have : U * m ≤ Q * m - m := by
        have := Nat.mul_le_mul_right m (Nat.le_pred_of_lt hU)
        rw [Nat.pred_eq_sub_one, Nat.sub_one_mul] at this
        exact this
      have : m ≤ Q * m := Nat.le_mul_of_pos_left m hQ
      omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  have hH : H < m := by
    have : Q * H < Q * m := by
      have : m * m ≤ Q * m := Nat.mul_le_mul_right m (Nat.le_of_lt hm)
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨hV, hH, ?_⟩
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.mul_comm V, Nat.mul_comm H, eV, eA, Nat.add_right_comm,
    Nat.add_mul_mod_self_right]

theorem sqrS_eq (M : Mod) (o a : Nat) : sqrS M o a =
    (sqrRow0 a ++ (stores ([.r8, .r9] : List Reg) (M.tmp + 8) ++ sqrRows a)) ++ (sqrDbl M.tmp a ++
    (stores sqHigh6 o ++ (loads ([.r13, .r14, .r15] : List Reg) M.tmp ++ (redsShortX 6 ++
    (([.mov32 .r8 (.imm 0)] : List Instr) ++ (chain .add .adc sqWin6 o ++
    (([.alu .adc .r8 (.imm 0)] : List Instr) ++ (csub M sqWin6 .r8 ++ stores sqWin6 o)))))))) := by
  simp only [sqrS, List.append_assoc]

/-- `[o] = [a]² R⁻¹ mod p` for P-384's `p`, with BMI2 and ADX. -/
theorem sqrS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) (hsp : M.sparse = true) {o a : Nat} (ho : o + 48 ≤ size)
    (ha : a + 48 ≤ size) (hoT : o + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ o)
    (haT : a + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ a) (hoM : o + 48 ≤ M.mo ∨ M.mo + 48 ≤ o)
    (hA : wordsVal s.mem base a 6 < m) :
    WP isa (.block (sqrS M o a)) s fun s' =>
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) →
        (ofs base x < M.tmp ∨ M.tmp + 48 ≤ ofs base x) → s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % m := by
  obtain ⟨hn, hmP⟩ := Mod.ok_sparse hM.red hsp
  obtain ⟨hm1, -⟩ := p384_bounds hmP
  have hnw := hs.nowrap
  have htmp : M.tmp + 48 ≤ size := by have := hM.tmp; rw [hn] at this; exact this
  have hmo : M.mo + 48 ≤ size := by have := hM.mo; rw [hn] at this; exact this
  have hsep : M.mo + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ M.mo := by have := hM.sep; rw [hn] at this; exact this
  rw [sqrS_eq]
  -- The cross products, words 1 and 2 at `[tmp + 8]`.
  rw [WP.block_append_iff]
  refine WP.mono (sqCross_ok hs (t := M.tmp) ha (by omega) (by omega)) fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain ⟨hc₁, hq₁, hv₁⟩ := vals_congr (m := s₁.mem) (m' := s.mem) (a := a) (base := base)
    (fun i hi => (O₁.word (d := a + 8 * i) (by omega) (by omega)).symm)
  have hAA := sq_eq s.mem base a
  have hAl := sq_lt (Nat.lt_trans hA hm1)
  -- The square, words 0 to 2 at `[tmp]`.
  rw [WP.block_append_iff]
  refine WP.mono (sqrDbl_ok hs₁ (t := M.tmp) ha (by omega) (by omega)
    (by rw [e₁, ← hq₁, ← hAA]; exact hAl)) fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  rw [e₁, ← hq₁, ← hAA] at e₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The high half to `[o]`.
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok sqHigh6 hs₂ (o := o) (by simp only [sqHigh6, List.length_cons, List.length_nil]; omega)
    (by decide)) fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  simp only [show sqHigh6.length = 6 from rfl, Nat.reduceMul] at e₃ O₃
  -- The low words into the window `sqWin6`.
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok [.r13, .r14, .r15] hs₃ (a := M.tmp) (by simp only [List.length_cons, List.length_nil]; omega)
    ⟨by decide, by decide⟩) fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  -- `[a]² = L + 2³⁸⁴ H` for the low half `L` in the window and the high half `H` at `[o]`.
  have hL : regsVal s₄ (sqWins 0) = wordsVal s₂.mem base M.tmp 3 + 2 ^ (64 * 3) *
      regsVal s₂ [.r10, .r11, .r12] := by
    have h3 : regsVal s₄ [.r10, .r11, .r12] = regsVal s₂ [.r10, .r11, .r12] :=
      regsVal_congr fun q hq => by
        rw [k₄.1 q (by
          intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h hq
          rcases hq with rfl | rfl | rfl <;> rcases h with h | h | h <;> cases h), k₃.gpr q (by simp)]
    have hw : regsVal s₄ [.r13, .r14, .r15] = wordsVal s₂.mem base M.tmp 3 := by
      rw [e₄]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
      exact O₃.wordsVal (by omega) (by omega)
    rw [show sqWins 0 = [.r13, .r14, .r15] ++ [.r10, .r11, .r12] from rfl, regsVal_append, hw, h3,
      show ([Reg.r13, .r14, .r15] : List Reg).length = 3 from rfl]
  have hAH : wordsVal s.mem base a 6 * wordsVal s.mem base a 6 =
      regsVal s₄ (sqWins 0) + 2 ^ (64 * 3) * 2 ^ (64 * 3) * wordsVal s₃.mem base o 6 := by
    rw [← e₂, hL, e₃, show ([.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] : List Reg) =
      [.r10, .r11, .r12] ++ sqHigh6 from rfl, regsVal_append,
      show ([Reg.r10, .r11, .r12] : List Reg).length = 3 from rfl, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
  rw [← pow_split 2 (64 * 3) (64 * 3) (64 * 6) rfl] at hAH
  have hLt : regsVal s₄ (sqWins 0) < 2 ^ (64 * 6) := by
    have := regsVal_lt s₄ (sqWins 0)
    rw [show (sqWins 0).length = 6 from rfl] at this
    exact this
  -- The reductions.
  rw [WP.block_append_iff]
  refine WP.mono (redsShortX_ok hmP 6 hLt) fun s₆ h₆ => ?_
  obtain ⟨⟨U, hU, eU⟩, -, k₆⟩ := h₆
  have hs₆ := hs₄.of_keeps k₆ (by decide)
  have hAA' := Nat.mul_lt_mul'' hA hA
  generalize hQd : 2 ^ (64 * 6) = Q at eU hU hLt hAH hm1
  have hQ : 0 < Q := by omega
  obtain ⟨hV6, hH, hres⟩ := final_arith hQ eU hU hLt hAH hAA' hm1
  rw [show sqWins 6 = sqWin6 from rfl] at hV6 hres
  -- The carry word.
  rw [WP.block_append_iff]
  refine WP.mono (mov32zero_ok s₆ .r8) fun s₇ h₇ => ?_
  obtain ⟨z₇, -, k₇⟩ := h₇
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have hlow₇ : regsVal s₇ sqWin6 = regsVal s₆ sqWin6 := regsVal_congr fun q hq => k₇.1 q (by
    intro h; simp only [sqWin6, List.mem_cons, List.not_mem_nil, or_false] at h hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases h)
  -- The high half added.
  rw [WP.block_append_iff]
  refine WP.mono (chainAdd_ok hs₇ (t := .r13) (ts := [.r14, .r15, .r10, .r11, .r12]) (b := o)
    (by simp only [List.length_cons, List.length_nil]; omega) ⟨by decide, by decide⟩) fun s₈ h₈ => ?_
  obtain ⟨c₈, cf₈, e₈, k₈⟩ := h₈
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  rw [show (Reg.r13 :: [.r14, .r15, .r10, .r11, .r12] : List Reg) = sqWin6 from rfl, k₇.2.1, k₆.2.1, m₄,
    hlow₇] at e₈
  simp only [show sqWin6.length = 6 from rfl, hQd] at e₈
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₈ .r8 cf₈ (by rw [k₈.1 _ (by decide), z₇])) fun s₉ h₉ => ?_
  obtain ⟨e₉, k₉⟩ := h₉
  have hs₉ := hs₈.of_keeps k₉ (by decide)
  have hlow₉ : regsVal s₉ sqWin6 = regsVal s₈ sqWin6 := regsVal_congr fun q hq => k₉.1 q (by
    intro h; simp only [sqWin6, List.mem_cons, List.not_mem_nil, or_false] at h hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases h)
  have m₉ : s₉.mem = s₃.mem := by rw [k₉.2.1, k₈.2.1, k₇.2.1, k₆.2.1, m₄]
  have hmo₉ : wordsVal s₉.mem base M.mo M.n = m := by
    rw [m₉, O₃.wordsVal (by rw [hn]; omega) (by rw [hn]; omega), O₂.wordsVal (by rw [hn]; omega) (by rw [hn]; omega),
      O₁.wordsVal (by rw [hn]; omega) (by rw [hn]; omega), hM.val]
  -- `csub` and the result.
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₉ (ts := sqWin6) (top := .r8) (by rw [hn]; rfl) (by rw [hn]; decide)
    ⟨by decide, by decide⟩ hM.mo hM.tmp hM.sep (Mod.ok_sparse hM.red) hmo₉
    (by rw [hlow₉, e₉, hn, hQd]; omega)) fun s₁₀ h₁₀ => ?_
  obtain ⟨e₁₀, k₁₀, O₁₀⟩ := h₁₀
  have hs₁₀ := hs₉.of_keepRegs k₁₀ (by decide)
  refine WP.mono (stores_ok sqWin6 hs₁₀ (o := o) (by simp only [sqWin6, List.length_cons, List.length_nil]; omega)
    (by decide)) fun s₁₁ h₁₁ => ?_
  obtain ⟨e₁₁, k₁₁, O₁₁⟩ := h₁₁
  simp only [show sqWin6.length = 6 from rfl, Nat.reduceMul] at e₁₁ O₁₁
  have hval : wordsVal s₁₁.mem base o 6 = (regsVal s₆ sqWin6 + wordsVal s₃.mem base o 6) % m := by
    rw [e₁₁, e₁₀, hlow₉, e₉, hn, hQd, e₈]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_⟩
  · rw [k₁₁.gpr r (by simp), k₁₀.gpr r (not_mem_of hr (by decide)), k₉.1 r (not_mem_of hr (by decide)),
      k₈.1 r (not_mem_of hr (by decide)), k₇.1 r (not_mem_of hr (by decide)), k₆.1 r (not_mem_of hr (by decide)),
      k₄.1 r (not_mem_of hr (by decide)), k₃.gpr r (by simp),
      k₂.gpr r (not_mem_of hr (by decide)), k₁.gpr r (not_mem_of hr (by decide))]
  · rw [k₁₁.rd, k₁₀.rd, k₉.2.2.1, k₈.2.2.1, k₇.2.2.1, k₆.2.2.1, k₄.2.2.1, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₁₁.wr, k₁₀.wr, k₉.2.2.2, k₈.2.2.2, k₇.2.2.2, k₆.2.2.2, k₄.2.2.2, k₃.wr, k₂.wr, k₁.wr]
  · rw [O₁₁ x (by omega), O₁₀ x (by rw [hn]; omega), m₉, O₃ x (by omega), O₂ x (by omega), O₁ x (by omega)]
  · rw [hval]; exact Nat.mod_lt _ (by omega)
  · rw [hval]; exact hres

end VG.Proof.Mont.X86_64
