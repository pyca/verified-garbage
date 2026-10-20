module
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Reloc

import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! # Eight-word Montgomery products through shared functions -/

@[expose] public section
namespace VG.Proof.Weierstrass.X86_64.Mont.Wide8

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont VG.Impl.Weierstrass.X86_64.Mont.Wide8
open VG.Proof.Weierstrass (Unch)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

variable (order : Bool)

theorem mo_eq : mo = 3968 := rfl

theorem modulus_lt : modulus order < 2 ^ (64 * 8) := by cases order <;> decide +kernel

abbrev relocOperands (o a b : Nat) : Instr → Instr :=
  Instr.mapMem (unptr [(.rbx, a), (.r12, b), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mB, .r12), (mO, .rsi)])

/-! The relocated operands: an operand `[rdi + d]` within 4096 bytes past a
marker is `[rdi + d']` at the same distance past its offset, and one below
the markers is kept. -/

theorem reloc_A {o a b e : Nat} (h : e < 4096) :
    (unptr [(.rbx, a), (.r12, b), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mB, .r12), (mO, .rsi)])
      (sc (mA + e)) = sc (a + e) := by
  simp only [Function.comp_apply, relocTo, unptr, sc, List.find?, mA, mB, mO]
  simp (disch := omega_using [h]) only [decide_eq_true, ite_true,
    show List.lookup Reg.rbx [(Reg.rbx, a), (Reg.r12, b), (Reg.rsi, o)] = some a from rfl, MemOp.mk.injEq,
    true_and, Int.natCast_add]
  omega_using []

theorem reloc_B {o a b e : Nat} (h : e < 4096) :
    (unptr [(.rbx, a), (.r12, b), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mB, .r12), (mO, .rsi)])
      (sc (mB + e)) = sc (b + e) := by
  simp only [Function.comp_apply, relocTo, unptr, sc, List.find?, mA, mB, mO]
  simp (disch := omega_using [h]) only [decide_eq_true, decide_eq_false, ite_true,
    show List.lookup Reg.r12 [(Reg.rbx, a), (Reg.r12, b), (Reg.rsi, o)] = some b from rfl, MemOp.mk.injEq,
    true_and, Int.natCast_add]
  omega_using []

theorem reloc_O {o a b e : Nat} (h : e < 4096) :
    (unptr [(.rbx, a), (.r12, b), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mB, .r12), (mO, .rsi)])
      (sc (mO + e)) = sc (o + e) := by
  simp only [Function.comp_apply, relocTo, unptr, sc, List.find?, mA, mB, mO]
  simp (disch := omega_using [h]) only [decide_eq_true, decide_eq_false, ite_true,
    show List.lookup Reg.rsi [(Reg.rbx, a), (Reg.r12, b), (Reg.rsi, o)] = some o from rfl, MemOp.mk.injEq,
    true_and, Int.natCast_add]
  omega_using []

theorem reloc_low {o a b d : Nat} (h : d < mA) :
    (unptr [(.rbx, a), (.r12, b), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mB, .r12), (mO, .rsi)])
      (sc d) = sc d := by
  simp only [Function.comp_apply, relocTo, unptr, sc, List.find?, mA, mB, mO] at *
  simp (disch := omega) only [decide_eq_false]
  rfl

theorem memSteps_low (o a b : Nat) : ∀ (k t d : Nat), t + 8 * k ≤ mA → d + 8 * k ≤ mA →
    (memSteps k t d).map (relocOperands o a b) = memSteps k t d
  | 0, _, _, _, _ => rfl
  | k + 1, t, d, ht, hd => by
    simp only [memSteps, memStep, mulStep, List.map_cons, Instr.mapMem, Src.mapMem,
      List.cons_append, List.nil_append]
    rw [reloc_low (by omega_using [ht]), reloc_low (by omega_using [hd]), memSteps_low o a b k (t + 8) (d + 8) (by omega_using [ht]) (by omega_using [hd])]

theorem memSteps_B (o a b : Nat) : ∀ (k t e : Nat), t + 8 * k ≤ mA → e + 8 * k ≤ 4096 →
    (memSteps k t (mB + e)).map (relocOperands o a b) = memSteps k t (b + e)
  | 0, _, _, _, _ => rfl
  | k + 1, t, e, ht, he => by
    simp only [memSteps, memStep, mulStep, List.map_cons, Instr.mapMem, Src.mapMem,
      List.cons_append, List.nil_append]
    rw [reloc_low (by omega_using [ht]), reloc_B (by omega_using [he]), Nat.add_assoc,
      memSteps_B o a b k (t + 8) (e + 8) (by omega_using [ht]) (by omega_using [he]), Nat.add_assoc]

theorem moveDown_low (o a b : Nat) : ∀ (k t : Nat), t + 8 * k + 8 ≤ mA →
    (moveDown k t).map (relocOperands o a b) = moveDown k t
  | 0, _, _ => rfl
  | k + 1, t, ht => by
    simp only [moveDown, List.map_cons, Instr.mapMem, Src.mapMem,
      List.cons_append, List.nil_append]
    rw [reloc_low (by omega_using [ht]), reloc_low (by omega_using [ht]), moveDown_low o a b k (t + 8) (by omega_using [ht])]

theorem chainW_O (o a b : Nat) (op op' : AluOp) : ∀ (k e t d : Nat), e + 8 * k ≤ 4096 → t + 8 * k ≤ mA →
    d + 8 * k ≤ mA → (chainW op op' k (mO + e) t d).map (relocOperands o a b) = chainW op op' k (o + e) t d
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, e, t, d, he, ht, hd => by
    simp only [chainW, List.map_cons, Instr.mapMem, Src.mapMem,
      List.cons_append, List.nil_append]
    rw [reloc_low (by omega_using [ht]), reloc_low (by omega_using [hd]), reloc_O (by omega_using [he]), Nat.add_assoc,
      chainW_O o a b op' op' k (e + 8) (t + 8) (d + 8) (by omega_using [he]) (by omega_using [ht]) (by omega_using [hd]), Nat.add_assoc]

theorem selectsW_O (o a b : Nat) : ∀ (k x e : Nat), e + 8 * k ≤ 4096 → x + 8 * k ≤ mA →
    (selectsW k x (mO + e)).map (relocOperands o a b) = selectsW k x (o + e)
  | 0, _, _, _, _ => rfl
  | k + 1, x, e, he, hx => by
    simp only [selectsW, List.map_cons, Instr.mapMem, Src.mapMem,
      List.cons_append, List.nil_append]
    rw [reloc_O (by omega_using [he]), reloc_low (by omega_using [hx]), Nat.add_assoc,
      selectsW_O o a b k (x + 8) (e + 8) (by omega_using [he]) (by omega_using [hx]), Nat.add_assoc]

theorem round_reloc (o a b i : Nat) (hi : i < 8) :
    (roundW (mod order) mA mB i).map (relocOperands o a b) = roundW (mod order) a b i := by
  have hB := memSteps_B o a b 8 4032 0 (by decide) (by decide)
  rw [Nat.add_zero, Nat.add_zero] at hB
  simp only [roundW, memRow, shiftDown, carryUp, show (mod order).n = 8 from rfl,
    show (mod order).tmp = 4032 from rfl, show (mod order).mo = 3968 from rfl, List.map_append, List.map_cons,
    List.map_nil, Instr.mapMem, Src.mapMem, reloc_A (show 8 * i < 4096 by omega_using [hi]), hB, Nat.reduceSub,
    memSteps_low o a b 8 4032 3968 (by decide) (by decide), moveDown_low o a b 7 4032 (by decide),
    reloc_low (show 4032 + 8 * 7 < mA by decide), reloc_low (show 4032 < mA by decide)]

theorem csub_reloc (o a b : Nat) :
    (csubW (mod order) mO).map (relocOperands o a b) = csubW (mod order) o := by
  kernel_rfl

theorem mulW_reloc (o a b : Nat) :
    (mulW (mod order) mO mA mB).map (relocOperands o a b) = mulW (mod order) o a b := by
  kernel_rfl

theorem body_keeps :
    (reloc [(mA, .rbx), (mB, .r12), (mO, .rsi)] (mulW (mod order) mO mA mB)).all
      (keepsPtrs [.rbx, .r12, .rsi]) = true := by cases order <;> decide +kernel

theorem store_scal : scalCode (.block (store order)) = true := by cases order <;> decide +kernel

theorem mulWR_scal : scalCode (.block (reloc [(mA, .rbx), (mB, .r12), (mO, .rsi)]
    (mulW (mod order) mO mA mB))) = true := by cases order <;> decide +kernel

theorem mod_ok {Z : Nat} (hZ : 4096 ≤ Z) {mem : Mem} {base : Addr}
    (hv : wordsVal mem base mo 8 = modulus order) : ModOkW (mod order) Z (modulus order) mem base where
  n0 := by show 0 < 8; decide
  mo := by simp only [mod, mo]; omega_using [hZ]
  tmp := by simp only [mod, tmp]; omega_using [hZ]
  sep := by show 3968 + 64 ≤ 4032 ∨ 4032 + 64 ≤ 3968; decide
  val := hv
  inv := by cases order <;> decide +kernel
  red := by cases order <;> decide +kernel

theorem ptrs_ok (s : State) :
    WP isa (.block [.mov .r12 (.reg .rcx), .alu .add .rsi (.reg .rdi)]) s fun s' =>
      s'.gpr .r12 = s.gpr .rcx ∧ s'.gpr .rsi = s.gpr .rdi + s.gpr .rsi ∧ Keeps [.r12, .rsi] s s' ∧
        s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, BitVec.add_comm _ _, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1]

theorem body_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b : Nat} (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : o + 64 ≤ 3584) (ha : a + 64 ≤ 3584) (hb : b + 64 ≤ 3584) (hB : wordsVal s.mem base b 8 < (modulus order)) :
    WP isa (.block (body order)) s fun s' =>
      KeepRegs (.r12 :: .rsi :: clob 8) s s' ∧
      (∀ x, (ofs base x < o ∨ o + 64 ≤ ofs base x) → (ofs base x < tmp ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      (∀ x, (∀ i < 8, x ≠ keepX i) → s'.xmm x = s.xmm x) ∧
      wordsVal s'.mem base o 8 < (modulus order) ∧
      wordsVal s'.mem base o 8 * 2 ^ (64 * 8) % (modulus order) = wordsVal s.mem base a 8 * wordsVal s.mem base b 8 % (modulus order) := by
  have hnw := hs.nowrap
  simp only [body, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ptrs_ok s) fun s₁ ⟨bp₁, si₁, k₁, xs₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (saveSteps_ok (d := mo) keepX 8 s₁ hs₁ (by rw [mo_eq]; omega_using [hZ]) (fun i j hi hj => keepX_ne i j hi (by omega_using [hj])))
    fun s₁' ⟨x₁', o₁', m₁', k₁'⟩ => ?_
  have hs₁' := hs₁.of_keepRegs k₁' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (store_scal order)
    (setConst_ok (n := 8) (o := mo) (x := (modulus order)) hs₁' (by rw [mo_eq]; omega_using [hZ]) (modulus_lt order)))
    fun s₂ ⟨⟨v₂, k₂, O₂⟩, x₂, _⟩ => ?_
  have hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  have far : ∀ x, x + 64 ≤ 3584 → wordsVal s₂.mem base x 8 = wordsVal s.mem base x 8 := fun x hx => by
    rw [(show Unch base [(mo, 8 * 8)] s₁'.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [mo_eq]; omega_using [hx]) (by omega_using [hx]), m₁', hm₁]
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r := fun r hr => by
    rw [k₂.gpr r (by simpa using hr), k₁'.gpr r (by simpa using hr)]
  have hp₂ : PtrsAt [(.rbx, a), (.r12, b), (.rsi, o)] s₂ := .three
    (by rw [g₂ _ (by decide), k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [g₂ _ (by decide), bp₁, hcx, hs₂.rdi])
    (by rw [g₂ _ (by decide), si₁, hsi, hs.rdi, hs₂.rdi])
  have w₃ := mulW_ok hs₂ (mod_ok order hZ v₂) (o := o) (a := a) (b := b)
    (by simp only [mod]; omega_using [hZ, ho]) (by simp only [mod]; omega_using [hZ, ha]) (by simp only [mod]; omega_using [hZ, hb])
    (by simp only [mod, tmp]; omega_using [ho]) (by simp only [mod, tmp]; omega_using [ha])
    (by simp only [mod, tmp]; omega_using [hb]) (by simp only [mod, mo, tmp]; omega_using [ho])
    (by simp only [mod]; rw [far b hb]; exact hB)
  rw [← mulW_reloc order, ← reloc_unptr] at w₃
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mulWR_scal order) (wp_unptr (rs := [.rbx, .r12, .rsi]) (by simp) _ (body_keeps order) hp₂ w₃))
    fun s₃ ⟨⟨k₃, lt₃, e₃⟩, x₃, _⟩ => ?_
  simp only [show (mod order).n = 8 from rfl] at k₃ lt₃ e₃
  have hs₃ : Scr s₃ base Z := ⟨(k₃.gpr _ (by show Reg.rdi ∉ clob 8; decide)).trans hs₂.rdi, k₃.wr ▸ hs₂.wr, hnw⟩
  refine WP.mono (restoreSteps_ok (d := mo) keepX 8 s₃ hs₃ (by rw [mo_eq]; omega_using [hZ]))
    fun s₄ ⟨e₄, O₄, x₄, k₄⟩ => ?_
  have hm₄ : ∀ x, ofs base x < 3968 ∨ 4032 ≤ ofs base x → s₄.mem x = s₃.mem x := fun x hx =>
    O₄ x (by rw [mo_eq]; omega_using [hx])
  refine ⟨⟨fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁'.rd, k₁.2.2.1],
      by rw [k₄.wr, k₃.wr, k₂.wr, k₁'.wr, k₁.2.2.2]⟩,
    fun x hx hx' => ?_, fun x hx => ?_, by rw [O₄.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [mo_eq]; omega_using [ho]) (by omega_using [ho])]; exact lt₃, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    have hra : r ≠ .rax := fun h => hr.2.2 (h ▸ by decide)
    rw [k₄.gpr r (by simpa using hra), k₃.gpr r hr.2.2, g₂ r hra,
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩)]
  · by_cases hin : 3968 ≤ ofs base x ∧ ofs base x < 4032
    · -- A byte of the words restored.
      have hp : ∃ i < 8, ∃ j < 8, x = off base (mo + 8 * i) + BitVec.ofNat 64 j := by
        refine ⟨(ofs base x - 3968) / 8, by omega_using [hin], (ofs base x - 3968) % 8, Nat.mod_lt _ (by decide), ?_⟩
        rw [off, Offset.add_add, mo_eq, show 3968 + 8 * ((ofs base x - 3968) / 8) + (ofs base x - 3968) % 8 =
          ofs base x by omega_using [hin], BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      obtain ⟨i, hi, j, hj, rfl⟩ := hp
      have hw : word s₄.mem base (mo + 8 * i) = word s.mem base (mo + 8 * i) := by
        rw [e₄ i hi, x₃, x₂, x₁' i hi, qword_lo, hm₁]
      exact byte_of_word hw hj
    · rw [hm₄ x (by omega_using [hin]), k₃.mem x hx (by simp only [mod, tmp] at hx' ⊢; omega_using [hx']),
        O₂ x (by rw [mo_eq]; omega_using [hin]), m₁', hm₁]
  · rw [x₄, x₃, x₂, o₁' x hx, xs₁]
  · rw [O₄.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [mo_eq]; omega_using [ho]) (by omega_using [ho]), e₃, far a ha, far b hb]

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻⁵¹² mod m`, the offsets the low halves of
`rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]` and its
temporary area, bytes `tmp` to 4095. -/
theorem fn_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : argOf s .rsi + 64 ≤ 3584) (ha : argOf s .rdx + 64 ≤ 3584) (hb : argOf s .rcx + 64 ≤ 3584)
    (hB : wordsVal s.mem base (argOf s .rcx) 8 < (modulus order)) :
    WP isa (fn order) s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 8 < (modulus order) ∧
      wordsVal s'.mem base (argOf s .rsi) 8 * (2 ^ 64) ^ 8 % (modulus order) =
        wordsVal s.mem base (argOf s .rdx) 8 * wordsVal s.mem base (argOf s .rcx) 8 % (modulus order) ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 64 ≤ ofs base x) →
        (ofs base x < tmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, _, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  have hQ : (2 : Nat) ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
  refine WP.seq (WP.mono (body_ok order hs₁ hZ bx₁ cx₁ si₁ ho ha hb (by rw [m₁]; exact hB))
    fun s₂ ⟨k₂, O₂, xm₂, lt₂, e₂⟩ => ?_)
  have xk : ∀ x, x ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] → s₂.xmm x = s₁.xmm x := fun x hx =>
    xm₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (restores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃⟩ => ?_
  rw [m₁] at e₂ O₂
  refine ⟨by rw [k₃.2.1]; exact lt₂, by rw [k₃.2.1, ← hQ]; exact e₂,
    ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.rd], by rw [k₃.2.2.2, k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xk _ (by simp), x0, qword_lo]
      · rw [p₃, xk _ (by simp), x1, qword_lo]
      · rw [r12₃, xk _ (by simp), x2, qword_lo]
      · rw [r13₃, xk _ (by simp), x3, qword_lo]
      · rw [r14₃, xk _ (by simp), x4, qword_lo]
      · rw [r15₃, xk _ (by simp), x5, qword_lo]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [k₃.2.1, O₂ x hx hx']


end VG.Proof.Weierstrass.X86_64.Mont.Wide8
