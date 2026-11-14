module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table2
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.Omega

/-! # The product of two numbers at the modulus's width

`rowLoop_ok`: a row, `[ebp] += [multOff] · [ecx]` over a count of bytes.
`productBy_ok`: the product of the first words of the multiplicand at
`mulAOff` and of a number, as many as code that `Counts` them sets, into the
`2 B + 4` bytes at `prodOff`, row by row; `wideProduct_ok`, of all `B` bytes
of each.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

/-- A row: the `N` words at `ebp = W + w` `+= [W + S + mo] ·` the `N` words at `ecx = W + bx`, the
carry out in `ebx`. -/
theorem rowLoopAt_ok {mo : Nat} {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {S bx w N : Nat} (hN : 0 < N)
    (hedi : PtrAt t₀ W .edi S) (hecx : PtrAt t₀ W .ecx bx) (hebp : PtrAt t₀ W .ebp w)
    (hesi : (t₀.gpr .esi).toNat = 4 * N) (hebx : t₀.gpr .ebx = 0) (hm : S + mo + 4 ≤ L)
    (hb : bx + 4 * N ≤ L) (ht : w + 4 * N ≤ L)
    (hsep : bx + 4 * N ≤ w ∨ w + 4 * N ≤ bx) (hsm : S + mo + 4 ≤ w ∨ w + 4 * N ≤ S + mo) :
    WP isa (rowLoopAt mo) t₀ fun u => Outside W w (4 * N) t₀.mem u.mem ∧
      val32 u.mem W w N + 2 ^ (32 * N) * (u.gpr .ebx).toNat =
        val32 t₀.mem W w N + w32 t₀.mem W (S + mo) * val32 t₀.mem W bx N ∧
      PtrAt u W .ebp (w + 4 * N) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₀ u := by
  have hn := hw.nowrap
  unfold rowLoopAt
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₀ t ∧
      PtrAt t W .ecx (bx + 4 * j) ∧ PtrAt t W .ebp (w + 4 * j) ∧ (t.gpr .esi).toNat = 4 * (N - j) ∧
      Outside W w (4 * j) t₀.mem t.mem ∧
      val32 t.mem W w j + 2 ^ (32 * j) * (t.gpr .ebx).toNat =
        val32 t₀.mem W w j + w32 t₀.mem W (S + mo) * val32 t₀.mem W bx j) ?_
    ⟨Keeps.refl _ _, by simpa using hecx, by simpa using hebp, by simpa using hesi, Outside.refl _ _ _ _,
      by rw [hebx]; simp [val32]⟩)
    fun u ⟨K, _, ebp, _, O, V⟩ => ⟨O, V, ebp, K⟩
  rintro j t hj ⟨K, ecx, ebp, esi, O, V⟩
  have ht' := hw.of_keeps K
  have edi : PtrAt t W .edi S := by rw [PtrAt, K.1 _ (by decide)]; exact hedi
  -- The words the step reads, kept since the start.
  have mk : w32 t.mem W (S + mo) = w32 t₀.mem W (S + mo) :=
    O.w32 (by omega_using [hsm, hj]) (by omega_using [hm, hn])
  have bk : w32 t.mem W (bx + 4 * j) = w32 t₀.mem W (bx + 4 * j) :=
    O.w32 (by omega_using [hsep, hj]) (by omega_using [hb, hj, hn])
  have tk : w32 t.mem W (w + 4 * j) = w32 t₀.mem W (w + 4 * j) :=
    O.w32 (.inr (Nat.le_refl _)) (by omega_using [ht, hj, hn])
  have wfit : w + 4 * j + 4 ≤ 2 ^ 64 := by omega_using [ht, hj, hn]
  refine WP.mono (mulStepAt_ok (mo := mo) ht' edi ecx ebp esi hj (by omega_using [hm])
    (by omega_using [hb, hj]) (by omega_using [ht, hj]))
    fun u ⟨mu, bu, cu, pu, su, zu, Ku⟩ => ?_
  rw [mk, bk, tk] at mu bu
  have Wr := writeW32_outside t.mem W (d := w + 4 * j)
    (BitVec.ofNat 32 (w32 t₀.mem W (S + mo) * w32 t₀.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
      w32 t₀.mem W (w + 4 * j))) wfit
  rw [← mu] at Wr
  refine ⟨⟨K.trans Ku, cu, pu, su, (O.mono (Nat.le_refl _) (by omega_using [])).trans
    (Wr.mono (by omega_using []) (by omega_using [])), ?_⟩, zu⟩
  have hlow : val32 u.mem W w j = val32 t.mem W w j :=
    Wr.val32 (.inl (Nat.le_refl _)) (by omega_using [ht, hj, hn])
  have htop : w32 u.mem W (w + 4 * j) = (w32 t₀.mem W (S + mo) * w32 t₀.mem W (bx + 4 * j) +
      (t.gpr .ebx).toNat + w32 t₀.mem W (w + 4 * j)) % 2 ^ 32 := by
    rw [mu, w32_write_self, BitVec.toNat_ofNat]
  rw [val32_succ, val32_succ, val32_succ, hlow, htop, bu, pow32_succ]
  generalize hxd : w32 t₀.mem W (S + mo) * w32 t₀.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
    w32 t₀.mem W (w + 4 * j) = x at *
  have hx := Nat.div_add_mod x (2 ^ 32)
  generalize 2 ^ (32 * j) = P at *
  grind

/-- `rowLoopAt_ok` with the multiplier at `multOff`. -/
theorem rowLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {S bx w N : Nat} (hN : 0 < N)
    (hedi : PtrAt t₀ W .edi S) (hecx : PtrAt t₀ W .ecx bx) (hebp : PtrAt t₀ W .ebp w)
    (hesi : (t₀.gpr .esi).toNat = 4 * N) (hebx : t₀.gpr .ebx = 0) (hm : S + multOff + 4 ≤ L)
    (hb : bx + 4 * N ≤ L) (ht : w + 4 * N ≤ L)
    (hsep : bx + 4 * N ≤ w ∨ w + 4 * N ≤ bx) (hsm : S + multOff + 4 ≤ w ∨ w + 4 * N ≤ S + multOff) :
    WP isa rowLoop t₀ fun u => Outside W w (4 * N) t₀.mem u.mem ∧
      val32 u.mem W w N + 2 ^ (32 * N) * (u.gpr .ebx).toNat =
        val32 t₀.mem W w N + w32 t₀.mem W (S + multOff) * val32 t₀.mem W bx N ∧
      PtrAt u W .ebp (w + 4 * N) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₀ u :=
  rowLoopAt_ok hw hN hedi hecx hebp hesi hebx hm hb ht hsep hsm

/-- `c r` sets `r` to `4 N` from any state of a run, keeping memory and the
other registers: the bytes of `N` words. -/
def Counts (c : Reg → List Instr) (len : Nat) (args : Nat → BitVec 32) (N : Nat) : Prop :=
  ∀ {Ex : List Region → List Region → Prop} {base : Addr} {bytes : Nat} {s : State} {is : List Instr}
    {Q : State → Prop} (r : Reg), In Ex base bytes len args s →
    (∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (4 * N) → WP isa (.block is) t Q) →
    WP isa (.block (c r ++ is)) s Q

/-- `e` sets `eax` from `4 Nc` to `4 Nr`, from any state of a run, keeping
memory and the other registers. -/
def EndsAt (e : List Instr) (len : Nat) (args : Nat → BitVec 32) (Nc Nr : Nat) : Prop :=
  ∀ {Ex : List Region → List Region → Prop} {base : Addr} {bytes : Nat} {s : State} {is : List Instr}
    {Q : State → Prop}, In Ex base bytes len args s → s.gpr .eax = BitVec.ofNat 32 (4 * Nc) →
    (∀ t, Keeps [.eax] s t → t.mem = s.mem → t.gpr .eax = BitVec.ofNat 32 (4 * Nr) → WP isa (.block is) t Q) →
    WP isa (.block (e ++ is)) s Q

/-- The modulus's width, `B = 4 W` bytes. -/
theorem counts_wide {len : Nat} {args : Nat → BitVec 32} : Counts (widthC 0 .wide) len args (cwc len .wide) :=
  fun _ h kk => widthC_ok (k := 0) (c := .wide) h.width h.upper' fun t K m e =>
    kk t K m (by rw [e, bc_eq_cwc])

/-- Nothing: `eax` already the row count's bytes. -/
theorem endsAt_nil {len : Nat} {args : Nat → BitVec 32} {N : Nat} : EndsAt [] len args N N :=
  fun _ he kk => kk _ (Keeps.refl _ _) rfl he

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A row's multiplier, word `i` of `mulA`, into the header, and the pointers and count of the row. -/
theorem rowSetup_ok (h : In Ex base bytes len args s) {cols : Reg → List Instr} {Nc : Nat}
    (hc : Counts cols len args Nc) {b : Loc} (hb : lo len b + bc len .wide ≤ bytes) {i : Nat}
    (hi : i < cwc len .wide) (hp : PtrAt s base .ebp (prodOff + 4 * i)) {Q : State → Prop}
    (k : ∀ u, Keeps [.eax, .ebx, .ecx, .edx, .esi] s u → Outside base multOff 4 s.mem u.mem →
      w32 u.mem base multOff = w32 s.mem base (mulAOff + 4 * i) → PtrAt u base .ecx (lo len b) →
      u.gpr .esi = BitVec.ofNat 32 (4 * Nc) → u.gpr .ebx = 0 → Q u) :
    WP isa (.block (([.mov .eax (.mem (at_ .ebp (mulAOff - prodOff))), .store (sc multOff) .eax] : List Instr) ++
      ptrTo b .ecx .edx ++ cols .esi ++ ([.mov .ebx (.imm 0)] : List Instr))) s Q := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have bl := h.bytes_lt
  have hbw := bc_le h.upper' .wide
  have nw := h.scratch.nowrap
  have mo : multOff = 48 := rfl
  have po : prodOff = 256 := rfl
  have ma : mulAOff = 2312 := rfl
  simp only [List.cons_append, List.append_assoc]
  refine wp_movS (readSrc_ptr h.ws hp (d := mulAOff - prodOff) (by omega_arith)) fun u₁ a₁ _ => ?_
  have h₁ := h.regs a₁.keeps a₁.mem
  refine wp_storeS (h₁.scratch.ea (d := multOff) (by omega_arith)) (h₁.scratch.write (d := multOff) (n := 4)
    (by omega_arith)) fun u₂ m₂ => ?_
  have O₂ : Outside base multOff 4 s.mem u₂.mem := by
    rw [m₂.mem, a₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  have K₂ : Keeps [.eax] s u₂ := a₁.keeps.trans (m₂.keeps _)
  have h₂ := h.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine ptrTo_ok (r := .ecx) (t := .edx) (x := b) (by decide) (by decide) h₂.edi h₂.width h.upper' (by omega_arith)
    fun u₃ K₃ m₃ p₃ => ?_
  have h₃ := h₂.regs K₃ m₃
  refine hc .esi h₃ fun u₄ K₄ m₄ e₄ => ?_
  refine wp_movS rfl fun u₅ a₅ _ => WP.block_nil ?_
  have mem₅ : u₅.mem = u₂.mem := by rw [a₅.mem, m₄, m₃]
  refine k u₅ ((((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
    (a₅.keeps.mono (by decide))) (by rw [mem₅]; exact O₂) ?_ ?_ ?_ (by rw [a₅.gpr])
  · rw [mem₅, m₂.mem, w32_write_self, a₁.gpr, show prodOff + 4 * i + (mulAOff - prodOff) =
      mulAOff + 4 * i by omega_arith]
  · rw [PtrAt, a₅.other _ (by decide), K₄.1 _ (by decide)]; exact p₃
  · rw [a₅.other _ (by decide), e₄]

/-- The end of a row: its carry word stored, `ebp` at the next row, and ZF after the last. -/
theorem rowTail_ok (h : In Ex base bytes len args s) {cols : Reg → List Instr} {rowsEnd : List Instr}
    {Nc Nr : Nat} (hc : Counts cols len args Nc) (he : EndsAt rowsEnd len args Nc Nr) (hNc : Nc ≤ cwc len .wide)
    (hNr : Nr ≤ cwc len .wide) {i : Nat} (hi : i < Nr) (hp : PtrAt s base .ebp (prodOff + 4 * i + 4 * Nc)) :
    WP isa (.block (([.store (at_ .ebp 0) .ebx] : List Instr) ++ cols .eax ++
      ([.alu .sub .ebp (.reg .eax), .alu .add .ebp (.imm 4)] : List Instr) ++ rowsEnd ++
      ([.alu .add .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 prodOff)), .alu .cmp .ebp (.reg .eax)] :
        List Instr))) s fun u =>
      Outside base (prodOff + 4 * (i + Nc)) 4 s.mem u.mem ∧
      w32 u.mem base (prodOff + 4 * (i + Nc)) = (s.gpr .ebx).toNat ∧
      PtrAt u base .ebp (prodOff + 4 * (i + 1)) ∧ u.zf = some (decide (i + 1 = Nr)) ∧
      Keeps [.eax, .ebp] s u := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have hbw := bc_le h.upper' .wide
  have nw := h.scratch.nowrap
  have po : prodOff = 256 := rfl
  have ma : mulAOff = 2312 := rfl
  simp only [List.cons_append, List.append_assoc]
  refine wp_storeS (ea_ptr h.ws hp (d := 0) (by omega_arith))
    (ws_write h.ws (y := prodOff + 4 * i + 4 * Nc + 0) (n := 4) (by omega_arith)) fun u₁ m₁ => ?_
  have O₁ : Outside base (prodOff + 4 * (i + Nc)) 4 s.mem u₁.mem := by
    rw [m₁.mem, show prodOff + 4 * (i + Nc) = prodOff + 4 * i + 4 * Nc + 0 by omega_arith]
    exact writeW32_outside _ _ _ (by omega_arith)
  have h₁ := h.keep (m₁.keeps []) (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine hc .eax h₁ fun u₂ K₂ m₂ e₂ => ?_
  refine wp_subS rfl fun u₃ a₃ _ => wp_addS rfl fun u₄ a₄ _ => ?_
  have K₄ : Keeps [.eax, .ebp] u₁ u₄ := (K₂.mono (by decide)).trans ((a₃.keeps.trans a₄.keeps).mono (by decide))
  have m₄ : u₄.mem = u₁.mem := by rw [a₄.mem, a₃.mem, m₂]
  have eax₄ : u₄.gpr .eax = BitVec.ofNat 32 (4 * Nc) := by rw [a₄.other _ (by decide), a₃.other _ (by decide), e₂]
  refine he (h₁.regs K₄ m₄) eax₄ fun u₅ K₅ m₅ e₅ => ?_
  refine wp_addS rfl fun u₆ a₆ _ => wp_addS rfl fun u₇ a₇ _ => wp_cmpS rfl fun u₈ f₈ z₈ => WP.block_nil ?_
  have ebp₂ : PtrAt u₂ base .ebp (prodOff + 4 * i + 4 * Nc) := by
    rw [PtrAt, K₂.1 _ (by decide), m₁.gpr]; exact hp
  have eC : (BitVec.ofNat 32 (4 * Nc)).toNat = 4 * Nc := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have eR : (BitVec.ofNat 32 (4 * Nr)).toNat = 4 * Nr := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have ebp₃ : PtrAt u₃ base .ebp (prodOff + 4 * i) := by
    rw [PtrAt, a₃.gpr, e₂, ptr_sub ebp₂ _ (by omega_using [eC]), eC, Nat.add_sub_cancel]
  have ebp₄ : PtrAt u₄ base .ebp (prodOff + 4 * (i + 1)) := by
    rw [PtrAt, a₄.gpr, ptr_add ebp₃]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_arith
  have ebp₈ : PtrAt u₈ base .ebp (prodOff + 4 * (i + 1)) := by
    rw [PtrAt, f₈.gpr, a₇.other _ (by decide), a₆.other _ (by decide), K₅.1 _ (by decide)]; exact ebp₄
  have edi₅ : (u₅.gpr .edi).toNat = base.toNat := by
    rw [K₅.1 _ (by decide), a₄.other _ (by decide), a₃.other _ (by decide), K₂.1 _ (by decide), m₁.gpr]
    exact h.edi
  have eax₈ : PtrAt u₈ base .eax (prodOff + 4 * Nr) := by
    rw [PtrAt, f₈.gpr, a₇.gpr, a₆.gpr, e₅, BitVec.toNat_add,
      BitVec.toNat_add, eR, edi₅, BitVec.toNat_ofNat (x := prodOff)]
    omega_arith
  have mem₈ : u₈.mem = u₁.mem := by rw [f₈.mem, a₇.mem, a₆.mem, m₅, m₄]
  refine ⟨by rw [mem₈]; exact O₁, ?_, ebp₈, ?_, ?_⟩
  · rw [mem₈, m₁.mem, show prodOff + 4 * (i + Nc) = prodOff + 4 * i + 4 * Nc + 0 by omega_arith,
      w32_write_self]
  · have ebp₇ : PtrAt u₇ base .ebp (prodOff + 4 * (i + 1)) := by rw [PtrAt, ← f₈.gpr]; exact ebp₈
    have eax₇ : PtrAt u₇ base .eax (prodOff + 4 * Nr) := by rw [PtrAt, ← f₈.gpr]; exact eax₈
    rw [z₈, ptr_beq ebp₇ eax₇ (by omega_arith) (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)
  · exact (((((m₁.keeps []).mono (by decide)).trans K₄).trans (K₅.mono (by decide))).trans
      ((a₆.keeps.trans a₇.keeps).mono (by decide))).trans (f₈.keeps _)

/-- The ranges a product changes. -/
abbrev prodR (len : Nat) : List (Nat × Nat) := [(multOff, 4), (prodOff, 2 * bc len .wide + 4)]

theorem prodR_fit (h : In Ex base bytes len args s) : ∀ p ∈ prodR len, p.1 + p.2 ≤ bytes := by
  have pf := h.prod_fit
  intro p hp; simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp only [multOff, prodOff, mulAOff, numBase] at * <;> omega_arith

/-- A product keeps everything from the multiplicand up. -/
theorem prodR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (prodR len)) m m') (R : CallRoom sp base bytes) {d k : Nat} (hd : mulAOff ≤ d)
    (hk : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k := by
  have pf := h.prod_fit
  refine frameR_val32 F R h.scratch.nowrap hk ?_ (prodR_fit h)
  intro p hp; simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp only [multOff, prodOff, mulAOff, numBase] at * <;> omega_arith

/-- The product of the first `Nr` words of the multiplicand at `mulAOff` and
the first `Nc` of the number `b` (`Nr, Nc ≤ W`, the words of `B` bytes), into
the `2 B + 4` bytes at `prodOff`. -/
theorem productBy_ok (h : In Ex base bytes len args s) {cols : Reg → List Instr} {rowsEnd : List Instr}
    {Nc Nr : Nat} (hc : Counts cols len args Nc) (he : EndsAt rowsEnd len args Nc Nr) (hNc0 : 0 < Nc)
    (hNr0 : 0 < Nr) (hNc : Nc ≤ cwc len .wide) (hNr : Nr ≤ cwc len .wide) {b : Loc}
    (hb : lo len b + bc len .wide ≤ bytes) (hbn : numBase ≤ lo len b) :
    WP isa (productBy cols rowsEnd b) s fun u =>
      Frame (frameR base (s.gpr .esp) (prodR len)) s.mem u.mem ∧
      val32 u.mem base prodOff (2 * cwc len .wide + 1) =
        val32 s.mem base mulAOff Nr * val32 s.mem base (lo len b) Nc ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have hbw := bc_le h.upper' .wide
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have po : prodOff = 256 := rfl
  have ma : mulAOff = 2312 := rfl
  have mo : multOff = 48 := rfl
  have nb : numBase = 3336 := rfl
  have fitP := prodR_fit h
  have N : CntOk { c := .wide, two := true, extra := 4 } := ⟨show 4 ≤ 64 by decide, show 4 % 4 = 0 from rfl⟩
  have cbn : cb len { c := .wide, two := true, extra := 4 } = 2 * bc len .wide + 4 := by simp [cb]
  have cwn : cw len { c := .wide, two := true, extra := 4 } = 2 * cwc len .wide + 1 := by
    have := cb_eq (len := len) N; omega_arith
  let Bv := val32 s.mem base (lo len b) Nc
  let cn := cwc len .wide
  unfold productBy
  -- The product zeroed, `ebp` at it.
  refine WP.seq (WP.mono (zero_ok h (x := prod) N (by rw [cbn]; simp only [prod, lo]; omega_arith))
    fun u₁ ⟨O₁, Z₁, K₁⟩ => ?_)
  simp only [prod, lo, cbn, cwn] at O₁ Z₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  rw [← List.append_nil (ptrTo prod .ebp .edx)]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (x := prod) (by decide) (by decide) h₁.edi h₁.width h.upper'
    (by simp only [prod, lo]; omega_arith) fun u₂ K₂ m₂ p₂ => WP.block_nil ?_)
  simp only [prod, lo] at p₂
  have F₂ : Frame (frameR base (s.gpr .esp) (prodR len)) s.mem u₂.mem := by
    rw [m₂]; exact frameR_of_outside O₁ (by omega_arith) (by simp)
  have Z₂ : val32 u₂.mem base prodOff (Nc + (2 * cn + 1 - Nc)) = 0 := by
    rw [m₂, show Nc + (2 * cn + 1 - Nc) = 2 * cwc len .wide + 1 by omega_arith]; exact Z₁
  rw [val32_append] at Z₂
  have Zlo : val32 u₂.mem base prodOff Nc = 0 := by omega_arith
  have Zhi : val32 u₂.mem base (prodOff + 4 * Nc) (2 * cn + 1 - Nc) = 0 := by
    have : 0 < 2 ^ (32 * Nc) := Nat.two_pow_pos _
    rcases Nat.eq_zero_of_add_eq_zero Z₂ with ⟨_, z⟩
    exact (Nat.mul_eq_zero.mp z).resolve_left (by omega_arith)
  -- The rows.
  refine WP.mono (countLoop (N := Nr) hNr0 (fun i t =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ In Ex base bytes len args t ∧
      PtrAt t base .ebp (prodOff + 4 * i) ∧ Frame (frameR base (s.gpr .esp) (prodR len)) s.mem t.mem ∧
      val32 t.mem base prodOff (i + Nc) = val32 s.mem base mulAOff i * Bv ∧
      val32 t.mem base (prodOff + 4 * (i + Nc)) (2 * cn + 1 - Nc - i) = 0) ?step
    ⟨((K₁.mono (by decide)).trans (K₂.mono (by decide))), h₁.regs K₂ m₂, by simpa using p₂, F₂,
      by simpa [val32] using Zlo, by simpa using Zhi⟩)
    fun u ⟨K, _, _, F, V₁, V₂⟩ => ⟨F, ?fin, K⟩
  case fin =>
    rw [show 2 * cwc len .wide + 1 = (Nr + Nc) + (2 * cn + 1 - Nc - Nr) by omega_arith, val32_append, V₁, V₂,
      Nat.mul_zero, Nat.add_zero]
  rintro i t hi ⟨Kt, It, pt, Ft, V1, V2⟩
  have room := It.room
  have sp : t.gpr .esp = s.gpr .esp := Kt.1 _ (by decide)
  rw [sp] at room
  -- The multiplier and the pointers.
  refine WP.seq (rowSetup_ok It hc hb (by omega_arith) pt fun u₃ K₃ O₃ M₃ c₃ e₃ b₃ => ?_)
  have I₃ := It.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  have edi₃ : PtrAt u₃ base .edi 0 := by
    rw [PtrAt, I₃.edi, Nat.add_zero, Nat.mod_eq_of_lt (by omega_arith)]
  have ebp₃ : PtrAt u₃ base .ebp (prodOff + 4 * i) := by rw [PtrAt, K₃.1 _ (by decide)]; exact pt
  have e₃' : (u₃.gpr .esi).toNat = 4 * Nc := by rw [e₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  refine WP.seq (WP.mono (rowLoop_ok I₃.ws (S := 0) (bx := lo len b) (w := prodOff + 4 * i) (N := Nc)
    hNc0 edi₃ c₃ ebp₃ e₃' b₃ (by omega_arith) (by omega_arith) (by omega_arith) (.inr (by omega_arith)) (.inl (by omega_arith)))
    fun u₄ ⟨O₄, V₄, p₄, K₄⟩ => ?_)
  have I₄ := I₃.keep K₄ (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega_arith))
  refine WP.mono (rowTail_ok I₄ hc he hNc hNr hi p₄) fun u₅ ⟨O₅, W₅, p₅, z₅, K₅⟩ => ⟨⟨?_, ?_, p₅, ?_, ?_, ?_⟩, z₅⟩
  · exact ((Kt.trans (K₃.mono (by decide))).trans K₄).trans (K₅.mono (by decide))
  · exact I₄.keep K₅ (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by omega_arith))
  · exact Ft.trans ((frameR_of_outside O₃ (by omega_arith) (by simp)).trans
      ((frameR_of_outside (O₄.mono (o' := prodOff) (n' := 2 * bc len .wide + 4) (by omega_arith) (by omega_arith))
        (by omega_arith) (by simp)).trans
      (frameR_of_outside (O₅.mono (o' := prodOff) (n' := 2 * bc len .wide + 4) (by omega_arith) (by omega_arith))
        (by omega_arith) (by simp))))
  · -- The new row's value.
    have a₃ : w32 u₃.mem base (0 + multOff) = w32 s.mem base (mulAOff + 4 * i) := by
      rw [Nat.zero_add, M₃, ← w32_val32_one, ← w32_val32_one,
        prodR_keep h Ft h.room (by omega_arith) (by omega_arith)]
    have b₃ : val32 u₃.mem base (lo len b) Nc = Bv := by
      rw [O₃.val32 (.inr (by omega_arith)) (by omega_arith)]; exact prodR_keep h Ft h.room (by omega_arith) (by omega_arith)
    have lo₅ : val32 u₅.mem base prodOff i = val32 t.mem base prodOff i := by
      rw [O₅.val32 (.inl (by omega_arith)) (by omega_arith), O₄.val32 (.inl (by omega_arith)) (by omega_arith),
        O₃.val32 (.inr (by omega_arith)) (by omega_arith)]
    have w₅ : val32 u₅.mem base (prodOff + 4 * i) Nc = val32 u₄.mem base (prodOff + 4 * i) Nc :=
      O₅.val32 (.inl (by omega_arith)) (by omega_arith)
    have w₃ : val32 u₃.mem base (prodOff + 4 * i) Nc = val32 t.mem base (prodOff + 4 * i) Nc :=
      O₃.val32 (.inr (by omega_arith)) (by omega_arith)
    have top₅ : w32 u₅.mem base (prodOff + 4 * i + 4 * Nc) = (u₄.gpr .ebx).toNat := by
      rw [show prodOff + 4 * i + 4 * Nc = prodOff + 4 * (i + Nc) by omega_arith]; exact W₅
    have split := val32_append t.mem base prodOff i Nc
    rw [V1] at split
    rw [show i + 1 + Nc = i + (Nc + 1) by omega_arith, val32_append, val32_succ, lo₅, w₅, top₅, V₄, a₃, b₃, w₃,
      val32_succ s.mem base mulAOff i]
    rw [Nat.zero_add] at a₃
    generalize val32 t.mem base prodOff i = X at *
    generalize val32 t.mem base (prodOff + 4 * i) Nc = Y at *
    generalize val32 s.mem base mulAOff i = A at *
    generalize w32 s.mem base (mulAOff + 4 * i) = a at *
    generalize 2 ^ (32 * i) = Z at *
    grind
  · -- The words above it.
    have e : 2 * cn + 1 - Nc - i = 1 + (2 * cn + 1 - Nc - (i + 1)) := by omega_arith
    rw [e, val32_append] at V2
    have z : val32 t.mem base (prodOff + 4 * (i + Nc) + 4 * 1) (2 * cn + 1 - Nc - (i + 1)) = 0 := by
      have : 0 < 2 ^ (32 * 1) := Nat.two_pow_pos _
      rcases Nat.eq_zero_of_add_eq_zero V2 with ⟨_, z⟩
      exact (Nat.mul_eq_zero.mp z).resolve_left (by omega_arith)
    rw [show prodOff + 4 * (i + 1 + Nc) = prodOff + 4 * (i + Nc) + 4 * 1 by omega_arith,
      O₅.val32 (.inr (by omega_arith)) (by omega_arith), O₄.val32 (.inr (by omega_arith)) (by omega_arith),
      O₃.val32 (.inr (by omega_arith)) (by omega_arith)]
    exact z


/-- The product of the multiplicand at `mulAOff` and the number `b`, `B` bytes each, into the
`2 B + 4` bytes at `prodOff`. -/
theorem wideProduct_ok (h : In Ex base bytes len args s) {b : Loc} (hb : lo len b + bc len .wide ≤ bytes)
    (hbn : numBase ≤ lo len b) :
    WP isa (wideProduct b) s fun u =>
      Frame (frameR base (s.gpr .esp) (prodR len)) s.mem u.mem ∧
      val32 u.mem base prodOff (2 * cwc len .wide + 1) =
        val32 s.mem base mulAOff (cwc len .wide) * val32 s.mem base (lo len b) (cwc len .wide) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  exact productBy_ok h counts_wide endsAt_nil (by omega_arith) (by omega_arith) (Nat.le_refl _) (Nat.le_refl _) hb hbn
end

end VG.Proof.Bignum.X86.CrtRt
