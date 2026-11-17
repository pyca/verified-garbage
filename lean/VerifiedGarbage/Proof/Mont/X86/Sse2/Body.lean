module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Column
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Mcdt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Mont.X86.Sse2.Columns
import VerifiedGarbage.Proof.Mont.X86.ArgWs

/-! ### `Mont.X86.Sse2.Kernel`, which only this module used -/

section

/-! ### `Mont.X86.Sse2.Final`, which only this module used -/

section

/-! # The reduction

After the columns, `T`: the result's `N` words in reverse at `S + 24`
(`rvalT`) and the last carry's low word at `S + 16`, is below `2 M`. `subM`
writes `T - M` after them, over `A'`, reading `T` down from its end
(`subLoopR_ok`), `mask` makes the mask from the borrow and `T`'s top word
(`maskS_ok`), and `select` writes `T mod M` to `O` (`selLoopR_ok`,
`reduction_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

theorem Params.of_keeps {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat}
    (h : Params s W L V d) {rs : List Reg} (K : Keeps rs s t) (O : Outs W [(0, L)] s.mem t.mem)
    (hsp : .esp ∉ rs := by decide) : Params t W L V d :=
  h.keep O (K.1 _ hsp) K.2.1 K.2.2

theorem Params.of_upd {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat}
    (h : Params s W L V d) {r : Reg} {v : BitVec 32} (u : Upd s t r v) (hr : r ≠ .esp := by decide) :
    Params t W L V d :=
  h.keep (by rw [u.mem]; exact Outs.refl _ _ _) (u.other _ (Ne.symm hr)) u.rd u.wr

/-- `ptrs`: `ebp` and `ebx` at `S + 24 + 4 N`, the end of `T`. -/
theorem ptrs_ok {p : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (PV : PVals V W N S mo inv o a b) (P : Params p W L V 0) :
    WP isa (.block ptrs) p fun u =>
      PtrAt u W .ebx (S + 24 + 4 * N) ∧ PtrAt u W .ebp (S + 24 + 4 * N) ∧ u.mem = p.mem ∧
        Keeps [.eax, .ebx, .ebp] p u := by
  unfold ptrs
  simp only [offW]
  refine wp_movS (P.read pS (by decide)) fun s1 u1 _ => wp_addS rfl fun s2 u2 _ =>
    wp_movS (((P.of_upd u1).of_upd u2).read pN4 (by decide)) fun s3 u3 _ => wp_addS rfl fun s4 u4 _ =>
    wp_movS rfl fun s5 u5 _ => WP.block_nil ?_
  obtain bp : PtrAt s4 W .ebp (S + 24 + 4 * N) := by
    rw [PtrAt, u4.gpr, u3.gpr, u3.other .ebp (by decide), u2.gpr, u1.gpr, BitVec.toNat_add, BitVec.toNat_add,
      PV.s, PV.n4, BitVec.toNat_ofNat]
    omega_using []
  refine ⟨?_, ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem],
    ((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen u5.keeps⟩
  · rw [PtrAt, u5.gpr]; exact bp
  · rw [PtrAt, u5.other _ (by decide)]; exact bp

/-- The body of `subM`'s loop. -/
def subBodyR : List Instr :=
  [.alu .sub .ebp (.imm 4), .mov .eax (.mem (at_ .ebp 0))] ++ Rt.restore ++
    [.alu .sbb .eax (.mem (at_ .esi 0)), .store (at_ .ebx 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .esi (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .edi (.imm 4)]

/-- One word: `[tmp + 4j] = T_j - [mo + 4j] - c`, and the borrow. -/
theorem subStepR_ok {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S mo tmp j N : Nat} {c : Bool}
    (hebp : PtrAt t W .ebp (S + 24 + 4 * (N - j))) (hesi : PtrAt t W .esi (mo + 4 * j))
    (hebx : PtrAt t W .ebx (tmp + 4 * j))
    (hedi : (t.gpr .edi).toNat = 4 * (N - j)) (hj : j < N) (hc : t.gpr .ecx = cmask c)
    (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 * j + 4 ≤ L) (ht : tmp + 4 * j + 4 ≤ L) :
    WP isa (.block subBodyR) t fun u =>
      u.mem = t.mem.writeW (off W (tmp + 4 * j)) (t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32 -
        t.mem.readW (off W (mo + 4 * j)) 32 - (BitVec.ofBool c).setWidth 32) ∧
      u.gpr .ecx = cmask (decide (w32 t.mem W (S + 24 + 4 * (N - 1 - j)) < w32 t.mem W (mo + 4 * j) + c.toNat)) ∧
      PtrAt u W .ebp (S + 24 + 4 * (N - (j + 1))) ∧ PtrAt u W .esi (mo + 4 * (j + 1)) ∧
      PtrAt u W .ebx (tmp + 4 * (j + 1)) ∧ (u.gpr .edi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧ Keeps clob7 t u := by
  have hn := hw.nowrap
  simp only [subBodyR, List.cons_append, List.nil_append, restore_eq]
  refine wp_subZ rfl fun s₀ u₀ _ => ?_
  obtain hw₀ := hw.of_keeps u₀.keeps
  obtain b₀ : PtrAt s₀ W .ebp (S + 24 + 4 * (N - 1 - j)) := by
    rw [PtrAt, u₀.gpr, ptr_sub hebp _ (by rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hj])]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; congr 2; omega_using [hj]
  refine wp_movS (readSrc_ptr hw₀ b₀ (d := 0) (by omega_using [hs, hj])) fun s₁ u₁ _ => ?_
  refine wp_restore (by rw [u₁.other _ (by decide), u₀.other _ (by decide), hc]) fun s₂ u₂ c₂ => ?_
  obtain K₂ : Keeps [.eax, .edx, .ebp] t s₂ := ((u₀.keeps.mono (by decide)).widen u₁.keeps).widen u₂.keeps
  obtain hw₂ := hw.of_keeps K₂
  obtain esi₂ : PtrAt s₂ W .esi (mo + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact hesi
  refine wp_sbbS (readSrc_ptr hw₂ esi₂ (d := 0) (by omega_arith)) c₂ fun s₃ u₃ c₃ => ?_
  obtain hw₃ := hw₂.of_keeps u₃.keeps
  obtain ebx₃ : PtrAt s₃ W .ebx (tmp + 4 * j) := by rw [PtrAt, u₃.other _ (by decide), K₂.1 _ (by decide)]; exact hebx
  refine wp_storeS (ea_ptr hw₃ ebx₃ (d := 0) (by omega_arith))
    (ws_write hw₃ (y := tmp + 4 * j + 0) (n := 4) (by omega_arith))
    fun s₄ m₄ => wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_subZ rfl fun s₈ u₈ z₈ => WP.block_nil ?_
  obtain m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem, u₀.mem]
  obtain eax₂ : s₂.gpr .eax = t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32 := by
    rw [u₂.other _ (by decide), u₁.gpr, u₀.mem, Nat.add_zero]
  obtain K₅ : Keeps [.eax, .ecx, .edx, .ebp] t s₅ :=
    ((K₂.mono (by decide)).widen u₃.keeps |>.widen (m₄.keeps [])).widen u₅.keeps
  obtain r₅ : ∀ r, r = .esi ∨ r = .ebx ∨ r = .edi → s₅.gpr r = t.gpr r := by
    intro r hr; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  obtain bp₅ : s₅.gpr .ebp = s₀.gpr .ebp := by
    rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain ⟨c₁, c₂'⟩ := count_zf hedi hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.gpr, eax₂, u₃.mem, m₂]; simp only [Nat.add_zero]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, eax₂, m₂]
    simp only [Nat.add_zero]
  · rw [PtrAt, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), bp₅, b₀]
    congr 2; omega_using [hj]
  · rw [PtrAt, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, r₅ _ (.inl rfl), ptr_add hesi]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_arith
  · rw [PtrAt, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), r₅ _ (.inr (.inl rfl)), ptr_add hebx]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_arith
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (.inr (.inr rfl))]; exact c₁
  · rw [z₈, u₇.other _ (by decide), u₆.other _ (by decide), r₅ _ (.inr (.inr rfl)), c₂']
  · exact (((K₅.mono (by decide)).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps

/-- The loop: `[tmp] = T - [mo]`, `N` words, and the borrow. -/
theorem subLoopR_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {S mo tmp N : Nat} (hN : 0 < N)
    (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 * N ≤ L) (ht : tmp + 4 * N ≤ L)
    (hts : tmp + 4 * N ≤ S + 24 ∨ S + 24 + 4 * N ≤ tmp) (htm : tmp + 4 * N ≤ mo ∨ mo + 4 * N ≤ tmp)
    (hebp : PtrAt t₀ W .ebp (S + 24 + 4 * N)) (hesi : PtrAt t₀ W .esi mo) (hebx : PtrAt t₀ W .ebx tmp)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hc : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block subBodyR) .ne) t₀ fun u =>
      Outside W tmp (4 * N) t₀.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem W tmp N + val32 t₀.mem W mo N = rvalT t₀.mem W N S N + 2 ^ (32 * N) * c.toNat) ∧
      Keeps clob7 t₀ u := by
  have hn := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps clob7 t₀ t ∧ PtrAt t W .ebp (S + 24 + 4 * (N - j)) ∧ PtrAt t W .esi (mo + 4 * j) ∧
    PtrAt t W .ebx (tmp + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧ Outside W tmp (4 * j) t₀.mem t.mem ∧
    ∃ c : Bool, t.gpr .ecx = cmask c ∧
      val32 t.mem W tmp j + val32 t₀.mem W mo j = rvalT t₀.mem W N S j + 2 ^ (32 * j) * c.toNat
  obtain I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, by simpa using hebx,
    by simpa using hedi, Outside.refl _ _ _ _, false, hc, by simp [val32, rvalT]⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega_arith, hN, I₀⟩) fun u ⟨K, _, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, esi, ebx, edi, O, c, ec, V⟩
  obtain ht' := hw.of_keeps K
  refine WP.mono (subStepR_ok ht' ebp esi ebx edi hj ec hs (by omega_using [hm, hj]) (by omega_using [ht, hj]))
    fun u ⟨mu, eu, pu, su, bu, du, zu, Ku⟩ => ?_
  obtain ea : w32 t.mem W (S + 24 + 4 * (N - 1 - j)) = w32 t₀.mem W (S + 24 + 4 * (N - 1 - j)) :=
    O.w32 (by omega_using [hts, hj]) (by omega_using [hs, hj, hn])
  obtain eb : w32 t.mem W (mo + 4 * j) = w32 t₀.mem W (mo + 4 * j) :=
    O.w32 (by omega_using [htm, hj]) (by omega_using [hm, hj, hn])
  obtain I' : I (j + 1) u := by
    refine ⟨K.trans Ku, pu, su, bu, du, ?_, _, eu, ?_⟩
    · rw [mu]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [ht, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [mu, val32_store hn (by omega_using [ht, hj]), val32_succ t₀.mem W mo, rvalT, pow32_succ]
      obtain h := sbb_rel (t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32) (t.mem.readW (off W (mo + 4 * j)) 32) c
      have ea' : (t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32).toNat =
        w32 t₀.mem W (S + 24 + 4 * (N - 1 - j)) := ea
      have eb' : (t.mem.readW (off W (mo + 4 * j)) 32).toNat = w32 t₀.mem W (mo + 4 * j) := eb
      rw [ea', eb'] at h
      rw [ea, eb]
      exact chain_sub_step V h
  by_cases hjN : j + 1 = N
  · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
      N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjN], I'⟩

/-- The mask, from `T`'s top word, the last carry's low word at `S + 16`, and
the borrow `c`. -/
theorem maskS_ok {p : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hw : Ws p W L) (P : Params p W L V 0)
    {c : Bool} (hc : p.gpr .ecx = cmask c) :
    WP isa (.block mask) p fun u =>
      u.gpr .ecx = (if !(decide (w32 p.mem W (S + 16) < c.toNat)) then BitVec.allOnes 32 else 0) ∧
      u.mem = p.mem ∧ Keeps [.eax, .ecx, .edx] p u := by
  have hn := hw.nowrap
  have hs := Ly.s_le
  simp only [mask, offC, List.cons_append, List.nil_append, restore_eq]
  refine wp_movS (P.read pS (by decide)) fun s₁ u₁ _ => ?_
  obtain hw₁ := hw.of_keeps u₁.keeps
  refine wp_movS (readSrc_ptr hw₁ (ptr_of_param u₁.gpr PV.s) (d := 16) (by omega_using [hs])) fun s₂ u₂ _ => ?_
  refine wp_restore (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc]) fun s₃ u₃ c₃ => ?_
  refine wp_sbbS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_sbbS rfl c₄ fun s₅ u₅ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  refine wp_movS rfl fun s₇ u₇ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mask := u₆.gpr
    simp only [reduceCtorEq, ite_false] at mask
    rw [u₅.gpr, mask_val] at mask
    rw [u₇.gpr, mask]
    have z : (0 : BitVec 32).toNat = 0 := rfl
    obtain eax₃ : (s₃.gpr .eax).toNat = w32 p.mem W (S + 16) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
    rw [eax₃, z, Nat.zero_add]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · exact (((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps).widen
      u₆.keeps).widen u₇.keeps

/-- The body of `select`'s loop. -/
def selBodyR : List Instr :=
  [.alu .sub .ebp (.imm 4), .mov .eax (.mem (at_ .ebp 0)), .mov .edx (.mem (at_ .ebx 0)),
   .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
   .store (at_ .esi 0) .eax, .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4),
   .alu .sub .edi (.imm 4)]

/-- One word of the selection. -/
theorem selStepR_ok {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S tmp o j N : Nat} (k : Bool)
    (hebp : PtrAt t W .ebp (S + 24 + 4 * (N - j))) (hebx : PtrAt t W .ebx (tmp + 4 * j))
    (hesi : PtrAt t W .esi (o + 4 * j))
    (hedi : (t.gpr .edi).toNat = 4 * (N - j)) (hj : j < N)
    (hm : t.gpr .ecx = if k then BitVec.allOnes 32 else 0)
    (hs : S + 24 + 4 * N ≤ L) (ht : tmp + 4 * j + 4 ≤ L) (ho : o + 4 * j + 4 ≤ L) :
    WP isa (.block selBodyR) t fun u =>
      u.mem = t.mem.writeW (off W (o + 4 * j))
        (if k then t.mem.readW (off W (tmp + 4 * j)) 32 else t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32) ∧
      PtrAt u W .ebp (S + 24 + 4 * (N - (j + 1))) ∧ PtrAt u W .ebx (tmp + 4 * (j + 1)) ∧
      PtrAt u W .esi (o + 4 * (j + 1)) ∧ (u.gpr .edi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t u := by
  have hn := hw.nowrap
  simp only [selBodyR]
  refine wp_subZ rfl fun s₀ u₀ _ => ?_
  obtain hw₀ := hw.of_keeps u₀.keeps
  obtain b₀ : PtrAt s₀ W .ebp (S + 24 + 4 * (N - 1 - j)) := by
    rw [PtrAt, u₀.gpr, ptr_sub hebp _ (by rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hj])]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; congr 2; omega_using [hj]
  refine wp_movS (readSrc_ptr hw₀ b₀ (d := 0) (by omega_using [hs, hj])) fun s₂ u₂ _ => ?_
  obtain hw₂ := hw₀.of_keeps u₂.keeps
  obtain ebx₂ : PtrAt s₂ W .ebx (tmp + 4 * j) := by rw [PtrAt, u₂.other _ (by decide), u₀.other _ (by decide)]; exact hebx
  refine wp_movS (readSrc_ptr hw₂ ebx₂ (d := 0) (by omega_using [ht])) fun s₃ u₃ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  obtain k₆ : Keeps [.eax, .edx, .ebp] t s₆ := ((((u₀.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen
    u₄.keeps |>.widen u₅.keeps).widen u₆.keeps
  obtain hw₆ := hw.of_keeps k₆
  obtain esi₆ : PtrAt s₆ W .esi (o + 4 * j) := by rw [PtrAt, k₆.1 _ (by decide)]; exact hesi
  refine wp_storeS (ea_ptr hw₆ esi₆ (d := 0) (by omega_using [ho]))
    (ws_write hw₆ (y := o + 4 * j + 0) (n := 4) (by omega_using [ho])) fun s₇ m₇ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  refine wp_subZ rfl fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  obtain r₇ : ∀ r, r = .esi ∨ r = .ebx ∨ r = .edi → s₇.gpr r = t.gpr r := by
    intro r hr; rw [m₇.gpr]; apply k₆.1; rcases hr with rfl | rfl | rfl <;> decide
  obtain bp₇ : s₇.gpr .ebp = s₀.gpr .ebp := by
    rw [m₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]
  obtain ⟨c₁, c₂⟩ := count_zf hedi hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₀.mem]
    obtain ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₀.other _ (by decide)]
    obtain eax₆ : s₆.gpr .eax = t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32 ^^^
        ((t.mem.readW (off W (tmp + 4 * j)) 32 ^^^ t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₄, hm,
        u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₂.mem, u₀.mem]
      simp only [Nat.add_zero]
      rfl
    rw [select_val] at eax₆
    rw [u₁₀.mem, u₉.mem, u₈.mem, m₇.mem, mem₆, eax₆, Nat.add_zero]
  · rw [PtrAt, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), bp₇, b₀]
    congr 2; omega_using [hj]
  · rw [PtrAt, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, r₇ _ (.inr (.inl rfl)), ptr_add hebx]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
  · rw [PtrAt, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), r₇ _ (.inl rfl), ptr_add hesi]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), r₇ _ (.inr (.inr rfl))]; exact c₁
  · rw [z₁₀, u₉.other _ (by decide), u₈.other _ (by decide), r₇ _ (.inr (.inr rfl)), c₂]
  · exact ((((k₆.mono (by decide)).widen (m₇.keeps [])).widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps

/-- The selection: `[o] = [tmp]` if `k`, else `T`, `N` words. -/
theorem selLoopR_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {S tmp o N : Nat} (k : Bool) (hN : 0 < N)
    (hs : S + 24 + 4 * N ≤ L) (ht : tmp + 4 * N ≤ L) (ho : o + 4 * N ≤ L)
    (hos : o + 4 * N ≤ S + 24 ∨ S + 24 + 4 * N ≤ o) (hot : o + 4 * N ≤ tmp ∨ tmp + 4 * N ≤ o)
    (hebp : PtrAt t₀ W .ebp (S + 24 + 4 * N)) (hebx : PtrAt t₀ W .ebx tmp) (hesi : PtrAt t₀ W .esi o)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hm : t₀.gpr .ecx = if k then BitVec.allOnes 32 else 0) :
    WP isa (.loop (.block selBodyR) .ne) t₀ fun u =>
      Outside W o (4 * N) t₀.mem u.mem ∧
      val32 u.mem W o N = (if k then val32 t₀.mem W tmp N else rvalT t₀.mem W N S N) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t₀ u := by
  have hn := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t₀ t ∧ PtrAt t W .ebp (S + 24 + 4 * (N - j)) ∧
    PtrAt t W .ebx (tmp + 4 * j) ∧ PtrAt t W .esi (o + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧
    Outside W o (4 * j) t₀.mem t.mem ∧
    val32 t.mem W o j = (if k then val32 t₀.mem W tmp j else rvalT t₀.mem W N S j)
  obtain I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hesi,
    by simpa using hedi, Outside.refl _ _ _ _, by cases k <;> rfl⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega_using [hN], hN, I₀⟩) fun u ⟨K, _, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, ebx, esi, edi, O, V⟩
  obtain ht' := hw.of_keeps K
  obtain hm' : t.gpr .ecx = if k then BitVec.allOnes 32 else 0 := by rw [K.1 _ (by decide)]; exact hm
  refine WP.mono (selStepR_ok ht' k ebp ebx esi edi hj hm' hs (by omega_using [ht, hj])
    (by omega_using [ho, hj])) fun u ⟨mu, pu, bu, su, du, zu, Ku⟩ => ?_
  obtain I' : I (j + 1) u := by
    refine ⟨K.trans Ku, pu, bu, su, du, ?_, ?_⟩
    · rw [mu]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [ho, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [mu, val32_store hn (by omega_using [ho, hj]), V]
      cases k
      · simp only [Bool.false_eq_true, ↓reduceIte, rvalT]
        exact congrArg (_ + 2 ^ (32 * j) * ·) (O.w32 (d := S + 24 + 4 * (N - 1 - j)) (by omega_using [hos, hj])
          (by omega_using [hs, hj, hn]))
      · simp only [↓reduceIte, val32_succ]
        exact congrArg (_ + 2 ^ (32 * j) * ·) (O.w32 (d := tmp + 4 * j) (by omega_using [hot, hj])
          (by omega_using [ht, hj, hn]))
  by_cases hjN : j + 1 = N
  · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
      N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjN], I'⟩

/-- The reduction: `O = T mod M`, for `T` below `2 M`. -/
theorem reduction_ok {p : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hw : Ws p W L) (P : Params p W L V 0)
    (hT : rvalT p.mem W N S N + 2 ^ (32 * N) * w32 p.mem W (S + 16) < 2 * val32 p.mem W mo N) :
    WP isa (seqs [subM, .block mask, select]) p fun v =>
      val32 v.mem W o N = (rvalT p.mem W N S N + 2 ^ (32 * N) * w32 p.mem W (S + 16)) % val32 p.mem W mo N ∧
      Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] p.mem v.mem ∧ Keeps clob7 p v := by
  have hn := hw.nowrap
  have hs := Ly.s_le
  have hN := Ly.hN
  have hmo := Ly.mo_le
  have ho := Ly.o_le
  have hsmo : mo + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ mo := Ly.smo
  have hso : o + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ o := Ly.so
  simp only [seqs]
  -- The subtraction.
  unfold subM
  refine WP.seq (WP.seq (WP.block_append (WP.mono (ptrs_ok PV P) fun u1 ⟨bx1, bp1, m1, K1⟩ => ?_)))
  obtain P1 := P.of_keeps K1 (by rw [m1]; exact Outs.refl _ _ _)
  refine wp_movS (P1.read pM (by decide)) fun u2 v2 _ => wp_movS ((P1.of_upd v2).read pN4 (by decide))
    fun u3 v3 _ => wp_movS rfl fun u4 v4 _ => WP.block_nil ?_
  obtain K4 : Keeps clob7 p u4 := (((K1.mono (by decide)).widen v2.keeps).widen v3.keeps).widen v4.keeps
  obtain m4 : u4.mem = p.mem := by rw [v4.mem, v3.mem, v2.mem, m1]
  refine WP.mono (subLoopR_ok (hw.of_keeps K4) hN (S := S) (mo := mo) (tmp := S + 24 + 4 * N)
    (by omega_using [hs]) hmo (by omega_using [hs]) (.inr (Nat.le_refl _)) (by omega_using [hsmo])
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact bp1)
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.gpr]; exact PV.mo)
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact bx1)
    (by rw [v4.other _ (by decide), v3.gpr, PV.n4]) v4.gpr) fun u5 ⟨O5, ⟨c, ec5, V5⟩, K5⟩ => ?_
  obtain K5p : Keeps clob7 p u5 := K4.trans K5
  obtain hw5 := hw.of_keeps K5p
  obtain O5' : Outs W [(0, L)] p.mem u5.mem := by
    rw [← m4]; exact Outs.of_outside (O5.mono (o' := 0) (n' := L) (by omega_using []) (by omega_using [hs])) (by simp)
  obtain P5 := P.of_keeps K5p O5'
  obtain top5 : w32 u5.mem W (S + 16) = w32 p.mem W (S + 16) := by
    rw [← m4]; exact O5.w32 (by omega_using []) (by omega_using [hs, hn])
  -- The mask.
  refine WP.seq (WP.mono (maskS_ok Ly PV hw5 P5 ec5) fun u6 ⟨mk, m6, K6⟩ => ?_)
  rw [top5] at mk
  generalize hk : (!(decide (w32 p.mem W (S + 16) < c.toNat))) = k at mk
  obtain P6 := P5.of_keeps K6 (by rw [m6]; exact Outs.refl _ _ _)
  obtain hw6 := hw5.of_keeps K6
  -- The selection.
  unfold select
  refine WP.seq (WP.block_append (WP.mono (ptrs_ok PV P6) fun u7 ⟨bx7, bp7, m7, K7⟩ => ?_))
  obtain P7 := P6.of_keeps K7 (by rw [m7]; exact Outs.refl _ _ _)
  refine wp_movS (P7.read pO (by decide)) fun u8 v8 _ => wp_movS ((P7.of_upd v8).read pN4 (by decide))
    fun u9 v9 _ => WP.block_nil ?_
  obtain K9 : Keeps [.eax, .ebx, .ebp, .esi, .edi] u6 u9 := ((K7.mono (by decide)).widen v8.keeps).widen v9.keeps
  obtain m9 : u9.mem = u5.mem := by rw [v9.mem, v8.mem, m7, m6]
  refine WP.mono (selLoopR_ok (hw6.of_keeps K9) k hN (S := S) (tmp := S + 24 + 4 * N) (o := o)
    (by omega_using [hs]) (by omega_using [hs]) ho (by omega_using [hso]) (by omega_using [hso])
    (by rw [PtrAt, v9.other _ (by decide), v8.other _ (by decide)]; exact bp7)
    (by rw [PtrAt, v9.other _ (by decide), v8.other _ (by decide)]; exact bx7)
    (by rw [PtrAt, v9.other _ (by decide), v8.gpr]; exact PV.o)
    (by rw [v9.gpr, PV.n4])
    (by rw [v9.other _ (by decide), v8.other _ (by decide), K7.1 _ (by decide)]; exact mk))
    fun v ⟨Ov, Vv, Kv⟩ => ⟨?_, ?_, ?_⟩
  · -- The value.
    obtain T5 : rvalT u5.mem W N S N = rvalT p.mem W N S N := by
      rw [← m4]
      exact rvalT_congr fun j hj => O5.w32 (by omega_using [hj]) (by omega_using [hs, hj, hn])
    rw [m4] at V5
    rw [m9, T5] at Vv
    obtain hM : val32 p.mem W mo N < 2 ^ (32 * N) := val32_lt _ _ _ _
    obtain sel := csub_arith hM (val32_lt u5.mem W (S + 24 + 4 * N) N) hT V5 (b := c)
      (top := w32 p.mem W (S + 16))
    rw [Vv, ← hk, ← sel]
    by_cases h : w32 p.mem W (S + 16) < c.toNat <;> simp [h]
  · have e2 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] p.mem u5.mem := by
      rw [← m4]; exact Outs.of_outside (O5.mono (o' := S + 24) (n' := 8 * N + 4) (by omega_using []) (by omega_using []))
        (by simp)
    obtain e3 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] u5.mem v.mem := by
      rw [← m9]; exact Outs.of_outside Ov (by simp)
    exact e2.trans e3
  · exact ((K5p.trans (K6.mono (by decide))).trans (K9.mono (by decide))).trans (Kv.mono (by decide))

end VG.Proof.Mont.X86.Sse2

end

end


/-! # The kernel

The columns in an MCDT frame, whose two words lie below the parameters and
apart from the working space, then the reduction (`kernel_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar)

/-- The parameters read the same in a state `t` whose reads of them are the
same bytes, holding the same values, with the same permissions. -/
theorem Params.transport {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d d' : Nat}
    (P : Params s W L V d) (hea : ∀ i < 7, t.ea (prm d' i) = s.ea (prm d i))
    (hmem : ∀ i < 7, ∀ j < 4, t.mem (s.ea (prm d i) + BitVec.ofNat 64 j) = s.mem (s.ea (prm d i) + BitVec.ofNat 64 j))
    (hrw : ∀ a, InRegions (s.rd ++ s.wr) a 4 → InRegions (t.rd ++ t.wr) a 4) : Params t W L V d' := by
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · have h := P.read i hi
    show t.load32 (t.ea (prm d' i)) = _
    change s.load32 (s.ea (prm d i)) = _ at h
    rw [hea i hi]
    simp only [State.load32] at h ⊢
    split at h
    · rename_i hr
      rw [ite_eq_left (hrw _ hr), ← h, Mem.readW_congr fun j hj => hmem i hi j hj]
    · cases h
  · rw [hea i hi]; exact P.far i hi j hj

/-- The offset of a byte of the parameters from the MCDT frame's bottom. -/
theorem ofs_param {sp : BitVec 32} (hlo : 12 ≤ sp.toNat) (hhi : sp.toNat + 28 ≤ 2 ^ 32) {i j : Nat} (hi : i < 7)
    (hj : j < 4) :
    ofs ((sp - 12).setWidth 64) ((sp + BitVec.ofNat 32 (0 + 4 * i)).setWidth 64 + BitVec.ofNat 64 j) =
      12 + 4 * i + j := by
  simp only [ofs, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (12 : BitVec 32).toNat = 12 from rfl]
  omega_arith

/-- The MCDT frame's push writes no byte of the parameters. -/
theorem pushed_param (s : State) (hlo : 12 ≤ (s.gpr .esp).toNat) (hhi : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    {i j : Nat} (hi : i < 7) (hj : j < 4) :
    (mcdtPushed .eax s).mem (s.ea (prm 0 i) + BitVec.ofNat 64 j) = s.mem (s.ea (prm 0 i) + BitVec.ofNat 64 j) := by
  obtain b0 : ((s.gpr .esp - 12).setWidth 64 : Addr) = off ((s.gpr .esp - 12).setWidth 64) 0 := by
    simp only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  obtain b4 : ((s.gpr .esp - 8).setWidth 64 : Addr) = off ((s.gpr .esp - 12).setWidth 64) 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (8 : BitVec 32).toNat = 8 from rfl]
    omega_arith
  obtain o := ofs_param hlo hhi hi hj
  simp only [mcdtPushed]
  rw [b0, b4]
  rw [writeW32_outside _ _ _ (by decide) _ (by simp only [State.ea, prm, at_] at o ⊢; omega_arith),
    writeW32_outside _ _ _ (by decide) _ (by simp only [State.ea, prm, at_] at o ⊢; omega_arith)]

/-- The MCDT frame's push writes only its 8 bytes. -/
theorem pushed_other (s : State) (hlo : 12 ≤ (s.gpr .esp).toNat) {x : Addr}
    (hx : ∀ j < 8, x ≠ (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j) :
    (mcdtPushed .eax s).mem x = s.mem x := by
  obtain b4 : ((s.gpr .esp - 8).setWidth 64 : Addr) = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (8 : BitVec 32).toNat = 8 from rfl]
    omega_arith
  simp only [mcdtPushed, Mem.writeW]
  rw [Mem.write_apply (fun h => hx ((x - (s.gpr .esp - 12).setWidth 64).toNat) (by omega_arith)
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])),
    Mem.write_apply (fun h => hx ((x - (s.gpr .esp - 12).setWidth 64).toNat) (by
      rw [b4] at h
      have := (Offset.lt_iff x ((s.gpr .esp - 12).setWidth 64) (d := 4) (n := 4) (by decide)).mp h
      omega_arith) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]))]

/-- The MCDT frame's push writes no byte of the working space. -/
theorem pushed_ws (s : State) {W : Addr} {L : Nat}
    (hfar : ∀ j < 8, L ≤ ofs W ((s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j))
    (hlo : 12 ≤ (s.gpr .esp).toNat) : Outs W [(L, 2 ^ 64)] s.mem (mcdtPushed .eax s).mem := by
  intro x hx
  obtain hx' : ofs W x < L := by
    have := hx _ (List.mem_singleton_self _)
    have : ofs W x < 2 ^ 64 := (x - W).isLt
    simp only at *; omega_arith
  exact pushed_other s hlo fun j hj h => by have := hfar j hj; rw [← h] at this; omega_arith

theorem value_digits (m : Mem) (W : Addr) (x n : Nat) :
    Column.value (2 ^ 32) (digits m W x) n = val32 m W x n := VG.Proof.Mont.X86.Square.value_val32 m W x n

theorem columns_noSp' : NoSp columns := NoSp.of_all (by decide +kernel)

/-- What the kernel takes of its entry state: the layout, the parameters `V`
in its frame at `esp`, and the 40 bytes from 12 below `esp` (the MCDT
frame's and the parameters') past the working space. -/
structure KReady (s : State) (W : Addr) (L N S mo inv o a b : Nat) (V : Nat → BitVec 32) : Prop where
  ly : Lay L N S mo inv o a b
  pv : PVals V W N S mo inv o a b
  ws : Ws s W L
  prm : Params s W L V 0
  lo : 12 ≤ (s.gpr .esp).toNat
  hi : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  far : ∀ j < 40, L ≤ ofs W ((s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j)
  inv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0
  bLt : val32 s.mem W b N < val32 s.mem W mo N

section
variable {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}

/-- The columns' entry, inside the MCDT frame: the working space as it was,
the parameters 12 bytes above `esp`. -/
theorem pushed_ready (K : KReady s W L N S mo inv o a b V) :
    Ws (mcdtPushed .eax s) W L ∧ Params (mcdtPushed .eax s) W L V 12 ∧
    (w32 (mcdtPushed .eax s).mem W mo * w32 (mcdtPushed .eax s).mem W inv + 1) % 2 ^ 32 = 0 ∧
    ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (mcdtPushed .eax s).mem W d k = val32 s.mem W d k := by
  have hn := K.ws.nowrap
  have Ly := K.ly
  obtain esp0 : (mcdtPushed .eax s).gpr .esp = s.gpr .esp - 12 := mcdtPushed_esp _ _ (by decide)
  obtain O0 := pushed_ws s (fun j hj => K.far j (by omega_arith)) K.lo
  obtain ws0 : ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (mcdtPushed .eax s).mem W d k = val32 s.mem W d k := fun hd =>
    O0.val32 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  refine ⟨⟨List.mem_cons_of_mem _ K.ws.wr, hn⟩, K.prm.transport
    (fun i _ => by
      simp only [State.ea, prm, at_, esp0]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [show (12 : BitVec 32).toNat = 12 from rfl]
      omega_arith)
    (fun i hi j hj => pushed_param s K.lo K.hi hi hj)
    (fun a ⟨r, hr, hc⟩ => ⟨r, by
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h), hc⟩), ?_, ws0⟩
  obtain e1 := ws0 (d := mo) (k := 1) (by have := Ly.mo_le; have := Ly.hN; omega_arith)
  obtain e2 := ws0 (d := inv) (k := 1) (by have := Ly.inv_le; omega_arith)
  simp only [val32, Nat.mul_zero, Nat.add_zero] at e1 e2
  rw [e1, e2]; exact K.inv

/-- The value of `N` digits below `2³²`. -/
theorem value_lt_pow {q : Nat → Nat} (hq : ∀ i, q i ≤ 2 ^ 32 - 1) :
    ∀ N, Column.value (2 ^ 32) q N < 2 ^ (32 * N)
  | 0 => by simp [Column.value]
  | N + 1 => by
    obtain ih := value_lt_pow hq N
    obtain hN := hq N
    simp only [Column.value, NatSum.succ] at ih ⊢
    rw [← Nat.pow_mul, pow32_succ]
    generalize hX : 2 ^ (32 * N) = X at ih ⊢
    have := Nat.mul_le_mul_right X hN
    rw [Nat.sub_mul, Nat.one_mul] at this
    omega_arith

/-- After the MCDT frame: `R (T + R c) = A B + Q M` for some `Q` (the
quotient digits'), with `T + R c < 2 M`, `T`'s words in reverse at `S + 24`;
the memory as it was but the scratch and the MCDT frame's 8 bytes; `esp` and
the permissions as they were. -/
structure Mid (s : State) (W : Addr) (L N S mo inv o a b : Nat) (V : Nat → BitVec 32) (v : State) : Prop where
  ws : Ws v W L
  prm : Params v W L V 0
  esp : v.gpr .esp = s.gpr .esp
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  modulus : val32 v.mem W mo N = val32 s.mem W mo N
  bound : rvalT v.mem W N S N + 2 ^ (32 * N) * w32 v.mem W (S + 16) < 2 * val32 s.mem W mo N
  eqn : ∃ Q, 2 ^ (32 * N) * (rvalT v.mem W N S N + 2 ^ (32 * N) * w32 v.mem W (S + 16)) =
    val32 s.mem W a N * val32 s.mem W b N + Q * val32 s.mem W mo N
  out : ∀ x, (∀ j < 8, x ≠ (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j) →
    (ofs W x < S ∨ S + (8 * N + 28) ≤ ofs W x) → v.mem x = s.mem x

/-- The columns in their MCDT frame. -/
theorem frame_ok (K : KReady s W L N S mo inv o a b V) :
    WP isa (.frame (.mcdtEnter .eax) columns .mcdtLeave) s (Mid s W L N S mo inv o a b V) := by
  have Ly := K.ly
  have hn := K.ws.nowrap
  have hs := Ly.s_le
  have hN := Ly.hN
  have hlo := K.lo
  have hhi := K.hi
  let s0 := mcdtPushed .eax s
  obtain esp0 : s0.gpr .esp = s.gpr .esp - 12 := mcdtPushed_esp _ _ (by decide)
  obtain ⟨hw0, P0, hinv0, ws0⟩ := pushed_ready K
  refine WP.mcdtFrame (by decide) hlo columns_noSp'
    (WP.mono (columns_ok Ly K.pv hinv0 (by rw [mcdtPushed_mcdt]; omega_arith) hw0 P0) fun u ⟨c, q, I⟩ => ?_)
  have Ku := I.keep
  obtain espu : u.gpr .esp = s0.gpr .esp := Ku.1 _ (by decide)
  -- Memory past the working space, as the push left it.
  obtain far : ∀ x, L ≤ ofs W x → u.mem x = s0.mem x := fun x hx =>
    I.out x (by simp only [List.mem_singleton, forall_eq]; omega_arith)
  refine ⟨by rw [I.mcdt, mcdtPushed_mcdt], ?_, ?_⟩
  · rw [espu, ← mcdtPushed_saved .eax s (by decide) hlo]
    refine Mem.readW_congr fun j hj => far _ ?_
    obtain e : (s0.gpr .esp + 4).setWidth 64 + BitVec.ofNat 64 j =
        (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 (4 + j) := by
      rw [esp0]
      apply BitVec.eq_of_toNat_eq
      have := (s.gpr .esp).isLt
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [show (12 : BitVec 32).toNat = 12 from rfl, show (4 : BitVec 32).toNat = 4 from rfl]
      omega_arith
    rw [e]; exact K.far _ (by omega_arith)
  -- After the frame.
  obtain hpe : (mcdtPopped u).gpr .esp = s.gpr .esp := by
    rw [mcdtPopped_esp, espu, esp0, BitVec.sub_add_cancel]
  obtain hpw : (mcdtPopped u).wr = s.wr := by rw [mcdtPopped_wr, Ku.2.2]; rfl
  obtain hpr : (mcdtPopped u).rd = s.rd := by rw [mcdtPopped_rd, Ku.2.1]; rfl
  -- The columns' equation, at the end.
  have eq := I.eq
  rw [show 2 * N - N = N by omega_arith] at eq
  rw [Column.partSum_done _ _ _ (Nat.le_refl _), Column.partSum_congr_left _ _ N (2 * N)
    (b := q) (fun i hi => by simp only [Column.prefixDigits]; rw [ite_eq_left (by omega_arith)]),
    Column.partSum_done _ _ _ (Nat.le_refl _)] at eq
  simp only [value_digits] at eq
  obtain ea := ws0 (d := a) (k := N) Ly.a_le
  obtain eb := ws0 (d := b) (k := N) Ly.b_le
  obtain em := ws0 (d := mo) (k := N) Ly.mo_le
  rw [ea, eb, em, VG.Proof.Mont.X86.Square.pow32, VG.Proof.Mont.X86.Square.pow32, show (2 : Nat) ^ (32 * (2 * N)) = 2 ^ (32 * N) * 2 ^ (32 * N) by
    rw [← Nat.pow_add]; congr 1; omega_arith] at eq
  obtain eq' : 2 ^ (32 * N) * (rvalT u.mem W N S N + 2 ^ (32 * N) * c) =
      val32 s.mem W a N * val32 s.mem W b N + Column.value (2 ^ 32) q N * val32 s.mem W mo N := by
    rw [← eq]; grind
  obtain ⟨hT, hc2⟩ := final_bound (val32_lt _ _ _ _) K.bLt (Nat.le_of_lt (val32_lt _ _ _ _))
    (value_lt_pow I.qlt N) eq'
  obtain hc0 : w32 u.mem W (S + 16) = c := by
    have := I.carry
    have := Nat.zero_le (w32 u.mem W (S + 20))
    have : w32 u.mem W (S + 20) = 0 := by
      rcases Nat.eq_zero_or_pos (w32 u.mem W (S + 20)) with h | h
      · exact h
      · have : 2 ^ 32 ≤ 2 ^ 32 * w32 u.mem W (S + 20) := Nat.le_mul_of_pos_right _ h
        omega_arith
    omega_arith
  obtain mou : val32 u.mem W mo N = val32 s.mem W mo N := by
    rw [← em]; exact I.out.val32 (by have := Ly.smo; simp only [List.mem_singleton, forall_eq]; omega_arith)
      (by have := Ly.mo_le; omega_arith)
  refine ⟨⟨by rw [hpw]; exact K.ws.wr, hn⟩, K.prm.transport
    (fun i _ => by simp only [State.ea, prm, at_, hpe])
    (fun i hi j hj => by
      rw [mcdtPopped_mem, far _ (K.prm.far i hi j hj)]; exact pushed_param s hlo hhi hi hj)
    (fun a h => by rw [hpr, hpw]; exact h), hpe, hpr, hpw, by rw [mcdtPopped_mem, mou],
    by rw [mcdtPopped_mem, hc0]; exact hT, ⟨_, by rw [mcdtPopped_mem, hc0]; exact eq'⟩, fun x hx hr => ?_⟩
  rw [mcdtPopped_mem, I.out x (fun r h => by simp only [List.mem_singleton] at h; subst h; exact hr),
    pushed_other s hlo hx]

/-- The kernel: `O = A B R⁻¹ mod M`; only the scratch, `O` and memory past
the working space (the MCDT frame's bytes) change, and every register but
`esp` may. -/
theorem kernel_ok (K : KReady s W L N S mo inv o a b V) :
    WP isa kernel s fun v =>
      val32 v.mem W o N < val32 s.mem W mo N ∧
      val32 v.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W b N % val32 s.mem W mo N ∧
      (∀ x, (∀ j < 8, x ≠ (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j) →
        (∀ r ∈ [(S, 8 * N + 28), (o, 4 * N)], ofs W x < r.1 ∨ r.1 + r.2 ≤ ofs W x) → v.mem x = s.mem x) ∧
      Keeps clob7 s v := by
  have Ly := K.ly
  have hs := Ly.s_le
  have hN := Ly.hN
  have hn := K.ws.nowrap
  simp only [kernel, seqs]
  refine WP.seq (WP.mono (frame_ok K) fun p M => WP.mono
    (reduction_ok Ly K.pv M.ws M.prm (by rw [M.modulus]; exact M.bound)) fun v ⟨Vv, Ov, Kv⟩ => ?_)
  obtain hM : 0 < val32 s.mem W mo N := by have := K.bLt; omega_arith
  rw [M.modulus] at Vv
  obtain ⟨Q, eqn⟩ := M.eqn
  refine ⟨by rw [Vv]; exact Nat.mod_lt _ hM, by rw [Vv]; exact final_mod eqn, ?_, ?_⟩
  · intro x hx hr
    obtain h1 : v.mem x = p.mem x :=
      Ov x fun r h => by
        obtain h0 := hr _ (List.mem_cons_self ..)
        obtain h2 := hr _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h h0 h2
        rcases h with rfl | rfl
        · simp only; omega_using [h0]
        · simp only; omega_using [h2]
    rw [h1, M.out x hx (hr _ (List.mem_cons_self ..))]
  · refine ⟨fun r hr => ?_, by rw [Kv.2.1, M.rd], by rw [Kv.2.2, M.wr]⟩
    cases r <;> simp only [clob7, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true, not_true_eq_false]
      at hr
    rw [Kv.1 _ (by decide), M.esp]

end

end VG.Proof.Mont.X86.Sse2

end

end


/-! # A function around the kernel

`body params`: the callee-saved registers pushed, `params` setting the
kernel's parameters in registers, which a frame of 28 bytes pushes, the
kernel, then the registers back (`body_ok`). Its frames and the kernel's MCDT
frame use the 56 bytes below `esp`, apart from the working space (`Entry`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar ofs_far)

/-- The stack on entry: `esp`, its 56 bytes below apart from the working space. -/
structure Entry (s : State) (W : Addr) (L : Nat) : Prop where
  lo : 56 ≤ (s.gpr .esp).toNat
  hi : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  ws : Ws s W L
  far : ∀ j < 60, L ≤ ofs W ((s.gpr .esp).setWidth 64 - 56 + BitVec.ofNat 64 j)

/-- A stack address `c` bytes below `esp` plus `k`, from the bottom of the 56 bytes. -/
theorem stack_addr {sp : BitVec 32} (hlo : 56 ≤ sp.toNat) (hhi : sp.toNat + 24 ≤ 2 ^ 32) {c k : Nat}
    (hc : c ≤ 56) (hk : k < c + 24) :
    (sp - BitVec.ofNat 32 c + BitVec.ofNat 32 k).setWidth 64 = sp.setWidth 64 - 56 + BitVec.ofNat 64 (56 - c + k) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (56 : BitVec 64).toNat = 56 from rfl]
  omega_arith

/-- The values the kernel's frame of parameters holds, from the registers. -/
def vals (t : State) (i : Nat) : BitVec 32 := t.gpr (([.ebp, .edi, .esi, .edx, .ecx, .ebx, .eax] : List Reg).getD i .eax)

/-- The registers the frame of parameters pushes, last pushed first. -/
abbrev rs7 : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

theorem vals_eq (t : State) {i : Nat} (hi : i < 7) : vals t i = t.gpr rs7[rs7.length - 1 - i] := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

theorem add_ofNat64 (a : Addr) (d j : Nat) : a + BitVec.ofNat 64 d + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (d + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The frame of parameters, 44 bytes below the entry's `esp`. -/
theorem params_pushed {t : State} {W : Addr} {L : Nat} {sp : BitVec 32} (hlo : 56 ≤ sp.toNat)
    (hhi : sp.toNat + 24 ≤ 2 ^ 32) (hesp : t.gpr .esp = sp - 16)
    (far : ∀ j < 60, L ≤ ofs W (sp.setWidth 64 - 56 + BitVec.ofNat 64 j)) :
    Params (pushed rs7 t) W L (vals t) 0 := by
  obtain e7 : (pushed rs7 t).gpr .esp = sp - 16 - 28 := by rw [pushed_esp, hesp]; rfl
  obtain ea : ∀ i < 7, (pushed rs7 t).ea (prm 0 i) = sp.setWidth 64 - 56 + BitVec.ofNat 64 (12 + 4 * i) := by
    intro i hi
    simp only [State.ea, prm, at_, e7, Nat.zero_add]
    rw [show sp - 16 - 28 = sp - BitVec.ofNat 32 44 by rw [BitVec.sub_sub]; rfl, stack_addr hlo hhi (by decide) (by omega_arith)]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · show (pushed rs7 t).load32 ((pushed rs7 t).ea (prm 0 i)) = _
    obtain hs16 : (sp - 16).toNat = sp.toNat - 16 := by
      rw [BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl]; omega_arith
    obtain hn7 : 4 * rs7.length ≤ (t.gpr .esp).toNat := by rw [hesp, hs16]; simp only [List.length_cons, List.length_nil]; omega_arith
    obtain w := pushed_word (rs := rs7) (s := t) (by decide) hn7 (i := i) (by simpa using hi)
    rw [State.load32, ite_eq_left_iff.mpr fun h => absurd ?_ h, vals_eq t hi]
    · simp only [State.ea, prm, at_, Nat.zero_add]; rw [w]
    · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      rw [ea i hi]
      simp only [Region.Contains, hesp, List.length_cons, List.length_nil]
      have := sp.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [show (56 : BitVec 64).toNat = 56 from rfl, show (16 : BitVec 32).toNat = 16 from rfl]
      omega_arith
  · rw [ea i hi, add_ofNat64]; exact far _ (by omega_arith)

/-- The address `n` bytes below `e - c`, as a number: `(e - c - n).toNat` for 32-bit `e`, as
`BitVec.toNat_sub` states it. (`omega` takes long over the nest of remainders where it is one of
several in a goal.) -/
theorem below_base_toNat {e c n : Nat} (he : e < 2 ^ 32) (hlo : 56 ≤ e) (hc : c + n ≤ 56) :
    (2 ^ 32 - n % 2 ^ 32 + (2 ^ 32 - c % 2 ^ 32 + e) % 2 ^ 32) % 2 ^ 32 = e - c - n := by
  omega_using [he, hlo, hc]

/-- A byte of a frame within the 56 bytes below the entry's `esp` lies past the working space. -/
theorem below_far {s : State} {W : Addr} {L : Nat} (E : Entry s W L) {c n : Nat} (hc : c + n ≤ 56) (hn : 0 < n)
    {x : Addr} (hx : (below (s.gpr .esp - BitVec.ofNat 32 c) n).Contains x 1) : L ≤ ofs W x := by
  have hlo := E.lo
  have hhi := E.hi
  obtain e : x = (s.gpr .esp).setWidth 64 - 56 + BitVec.ofNat 64 (56 - c - n + (x - (s.gpr .esp - BitVec.ofNat 32 c -
      BitVec.ofNat 32 n).setWidth 64).toNat) := by
    obtain he := (s.gpr .esp).isLt
    simp only [Region.Contains] at hx
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hx ⊢
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    rw [below_base_toNat he hlo hc] at hx ⊢
    have := x.isLt
    omega_arith
  rw [e]
  simp only [Region.Contains] at hx
  exact E.far _ (by omega_arith)

/-- The working space's bytes past the frames' pushes. -/
theorem frame_ws {s : State} {W : Addr} {L : Nat} (E : Entry s W L) {c n : Nat} (hc : c + n ≤ 56) (hn : 0 < n)
    {m m' : Mem} (F : Frame [below (s.gpr .esp - BitVec.ofNat 32 c) n] m m') : Outs W [(L, 2 ^ 64)] m m' :=
  fun x hx => F x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    intro h
    have := below_far E hc hn h
    have := hx _ (List.mem_singleton_self _)
    have : ofs W x < 2 ^ 64 := (x - W).isLt
    simp only at *; omega_arith

theorem kernel_noSp : NoSp kernel := NoSp.of_all (by decide +kernel)

abbrev rs4 : List Reg := [.ebx, .esi, .edi, .ebp]

/-- The byte `d` of the stack from 56 bytes below `sp`. -/
abbrev stk (sp : BitVec 32) (d : Nat) : Addr := sp.setWidth 64 - 56 + BitVec.ofNat 64 d

theorem below_contains {sp base : BitVec 32} (hlo : 56 ≤ sp.toNat) (hhi : sp.toNat + 24 ≤ 2 ^ 32) {c n d : Nat}
    (hb : base = sp - BitVec.ofNat 32 c) (hc : c + n ≤ 56) (hd : d < 60) :
    (below base n).Contains (stk sp d) 1 ↔ (56 - c - n ≤ d ∧ d < 56 - c) := by
  subst hb
  have he := sp.isLt
  simp only [Region.Contains, stk, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [show (56 : BitVec 64).toNat = 56 from rfl, below_base_toNat he hlo hc]
  omega_arith

theorem stk_inj {sp : BitVec 32} {d e : Nat} (hd : d < 60) (he : e < 60)
    (h : stk sp d = stk sp e) : d = e := by
  obtain h' : (sp.setWidth 64 - 56 + BitVec.ofNat 64 d).toNat = (sp.setWidth 64 - 56 + BitVec.ofNat 64 e).toNat := by
    rw [show sp.setWidth 64 - 56 + BitVec.ofNat 64 d = stk sp d from rfl, h]
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
  rw [show (56 : BitVec 64).toNat = 56 from rfl] at h'
  omega_arith

/-- A byte of a frame below `sp - c` is among the 56 bytes below `sp`. -/
theorem below_sub {sp base : BitVec 32} (hlo : 56 ≤ sp.toNat) {c n : Nat} (hb : base = sp - BitVec.ofNat 32 c)
    (hc : c + n ≤ 56) {x : Addr} (h : (below base n).Contains x 1) : (below sp 56).Contains x 1 := by
  subst hb
  have he := sp.isLt
  have := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h ⊢
  rw [below_base_toNat he hlo hc] at h
  omega_arith

/-- `pop r` `k + 1` times leaves in `r` the frame's last word. -/
theorem popReg_last (s : State) {d : Reg} (hd : d ≠ .esp) (k : Nat) :
    (popReg s d (k + 1)).gpr d = s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 := by
  induction k generalizing s with
  | zero => simp [popReg, State.setReg, hd]
  | succ k ih =>
    rw [popReg, ih]
    simp only [State.setReg, ite_true, Ne.symm hd, ite_false, BitVec.add_assoc]
    congr 3
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]; congr 1; omega_arith

/-- What `params` leaves, from the state `s` before the callee-saved
registers' push: the kernel's parameters in registers. -/
def ParamsPost (s : State) (W : Addr) (N S mo inv o a b : Nat) (t : State) : Prop :=
  PVals (vals t) W N S mo inv o a b ∧ t.gpr .esp = s.gpr .esp - 16 ∧ t.mem = (pushed rs4 s).mem ∧
    t.rd = s.rd ∧ t.wr = (pushed rs4 s).wr

/-- The kernel's entry, after the frame of parameters' push. -/
theorem kernel_ready {s t1 : State} {W : Addr} {L N S mo inv o a b : Nat}
    (E : Entry s W L) (Ly : Lay L N S mo inv o a b)
    (hinv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) (H : ParamsPost s W N S mo inv o a b t1) :
    KReady (pushed rs7 t1) W L N S mo inv o a b (vals t1) := by
  obtain ⟨PV, esp1, m1, -, wr1⟩ := H
  have hlo := E.lo
  have hhi := E.hi
  have hn := E.ws.nowrap
  obtain hs16 : (s.gpr .esp - 16).toNat = (s.gpr .esp).toNat - 16 := by
    rw [BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl]; omega_arith
  obtain hn7 : 4 * rs7.length ≤ (t1.gpr .esp).toNat := by
    rw [esp1, hs16]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  obtain F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl, ← m1] at F1
  obtain F2 := pushed_frame (rs := rs7) (s := t1) (by decide) hn7
  rw [show 4 * rs7.length = 28 from rfl] at F2
  obtain esp2 : (pushed rs7 t1).gpr .esp = s.gpr .esp - 44 := by
    rw [pushed_esp, esp1, BitVec.sub_sub]; rfl
  obtain O2 : Outs W [(L, 2 ^ 64)] s.mem (pushed rs7 t1).mem := by
    refine (frame_ws E (c := 0) (n := 16) (by decide) (by decide) (by simpa using F1)).trans
      (frame_ws E (c := 16) (n := 28) (by decide) (by decide) (by rw [esp1] at F2; exact F2))
  obtain ws2 : ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (pushed rs7 t1).mem W d k = val32 s.mem W d k := fun hd =>
    O2.val32 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  obtain w2 : ∀ {d : Nat}, d + 4 ≤ L → w32 (pushed rs7 t1).mem W d = w32 s.mem W d := fun {d} hd => by
    have := ws2 (d := d) (k := 1) (by omega_arith)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  obtain hs44 : (s.gpr .esp - 44).toNat = (s.gpr .esp).toNat - 44 := by
    rw [BitVec.toNat_sub, show (44 : BitVec 32).toNat = 44 from rfl]; omega_arith
  obtain hm2 : (pushed rs7 t1).gpr .esp - 12 = s.gpr .esp - BitVec.ofNat 32 56 + BitVec.ofNat 32 0 := by
    rw [esp2, BitVec.sub_sub, BitVec.add_zero]; rfl
  refine ⟨Ly, PV, ⟨by rw [pushed_wr, wr1, pushed_wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ E.ws.wr), hn⟩,
    params_pushed hlo hhi esp1 E.far, by rw [esp2, hs44]; omega_arith, by rw [esp2, hs44]; omega_arith, fun j hj => ?_,
    by rw [w2 (by have := Ly.mo_le; have := Ly.hN; omega_arith), w2 Ly.inv_le]; exact hinv,
    by rw [ws2 Ly.b_le, ws2 Ly.mo_le]; exact hB⟩
  rw [hm2, stack_addr hlo hhi (c := 56) (k := 0) (by decide) (by omega_arith), add_ofNat64]
  exact E.far _ (by omega_arith)

/-- What `body params` leaves, for `params` setting the parameters from the
state after the callee-saved registers' push. -/
theorem body_ok {s : State} {params : List Instr} {W : Addr} {L N S mo inv o a b : Nat}
    (E : Entry s W L) (Ly : Lay L N S mo inv o a b)
    (hns : NoSp (seqs [.block params, withParams, .block restoreRegs]))
    (hp : WP isa (.block params) (pushed rs4 s) fun t =>
      PVals (vals t) W N S mo inv o a b ∧ t.gpr .esp = s.gpr .esp - 16 ∧ t.mem = (pushed rs4 s).mem ∧
        t.rd = s.rd ∧ t.wr = (pushed rs4 s).wr)
    (hinv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) :
    WP isa (body params) s fun u =>
      val32 u.mem W o N < val32 s.mem W mo N ∧
      val32 u.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W b N % val32 s.mem W mo N ∧
      (∀ x, (∀ r ∈ [(S, 8 * N + 28), (o, 4 * N)], ofs W x < r.1 ∨ r.1 + r.2 ≤ ofs W x) →
        ¬ (below (s.gpr .esp) 56).Contains x 1 → u.mem x = s.mem x) ∧
      (∀ r ∈ calleeSaved, u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hlo := E.lo
  have hhi := E.hi
  have hn := E.ws.nowrap
  obtain hs16 : (s.gpr .esp - 16).toNat = (s.gpr .esp).toNat - 16 := by
    rw [BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl]; omega_arith
  unfold body
  refine WP.frameKept (rs := rs4) (r := .ebx) (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega_arith) hns ?_
  simp only [seqs]
  refine WP.seq (WP.mono hp fun t1 ⟨PV, esp1, m1, rd1, wr1⟩ => ?_)
  obtain hn7 : 4 * rs7.length ≤ (t1.gpr .esp).toNat := by
    rw [esp1, hs16]; simp only [List.length_cons, List.length_nil]; omega_arith
  refine WP.seq (WP.frameKept (rs := rs7) (r := .eax) (by decide) (by decide) (by decide) hn7 kernel_noSp ?_)
  obtain h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  obtain F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl, ← m1] at F1
  obtain F2 := pushed_frame (rs := rs7) (s := t1) (by decide) hn7
  rw [show 4 * rs7.length = 28 from rfl] at F2
  obtain esp2 : (pushed rs7 t1).gpr .esp = s.gpr .esp - 44 := by
    rw [pushed_esp, esp1, BitVec.sub_sub]; rfl
  -- The working space's bytes, as on entry.
  obtain O2 : Outs W [(L, 2 ^ 64)] s.mem (pushed rs7 t1).mem := by
    refine (frame_ws E (c := 0) (n := 16) (by decide) (by decide) (by simpa using F1)).trans
      (frame_ws E (c := 16) (n := 28) (by decide) (by decide) (by rw [esp1] at F2; exact F2))
  obtain ws2 : ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (pushed rs7 t1).mem W d k = val32 s.mem W d k := fun hd =>
    O2.val32 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  obtain w2 : ∀ {d : Nat}, d + 4 ≤ L → w32 (pushed rs7 t1).mem W d = w32 s.mem W d := fun {d} hd => by
    have := ws2 (d := d) (k := 1) (by omega_arith)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  obtain hw2 : Ws (pushed rs7 t1) W L :=
    ⟨by rw [pushed_wr, wr1, pushed_wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ E.ws.wr), hn⟩
  obtain hs44 : (s.gpr .esp - 44).toNat = (s.gpr .esp).toNat - 44 := by
    rw [BitVec.toNat_sub, show (44 : BitVec 32).toNat = 44 from rfl]; omega_arith
  obtain hm2 : ∀ j < 8, (pushed rs7 t1).gpr .esp - 12 = s.gpr .esp - BitVec.ofNat 32 56 + BitVec.ofNat 32 0 := by
    intro _ _; rw [esp2, BitVec.sub_sub, BitVec.add_zero]; rfl
  refine WP.mono (kernel_ok (kernel_ready E Ly hinv hB ⟨PV, esp1, m1, rd1, wr1⟩))
    fun v ⟨lt, cong, mv, Kv⟩ => ?_
  rw [show rs7.length = 7 from rfl]
  -- After the kernel's frame: the saved registers.
  obtain espv : v.gpr .esp = s.gpr .esp - 44 := by rw [Kv.1 _ (by decide), esp2]
  obtain espw : (popped .eax 7 v).gpr .esp = s.gpr .esp - 16 := by
    rw [popped_esp, espv, BitVec.sub_add_comm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (44 : BitVec 32).toNat = 44 from rfl, show (16 : BitVec 32).toNat = 16 from rfl]
    have := (s.gpr .esp).isLt
    omega_arith
  obtain wrw : (popped .eax 7 v).wr = below (s.gpr .esp) 16 :: s.wr := by
    rw [popped_wr, Kv.2.2, pushed_wr, wr1, pushed_wr]; rfl
  obtain rdw : (popped .eax 7 v).rd = s.rd := by rw [popped_rd, Kv.2.1, pushed_rd, rd1]
  -- A stack byte above the kernel's frames is as the first push left it.
  obtain mw : ∀ d, 40 ≤ d → d < 60 → (popped .eax 7 v).mem (stk (s.gpr .esp) d) = (pushed rs4 s).mem (stk (s.gpr .esp) d) := by
    intro d hd1 hd2
    rw [popped_mem, mv _ (fun j hj h => by
        rw [hm2 j hj, stack_addr hlo hhi (c := 56) (k := 0) (by decide) (by omega_arith), add_ofNat64] at h
        have := stk_inj (sp := s.gpr .esp) (by omega_arith) (by omega_arith) h
        omega_arith)
      (fun r hr => by
        obtain hf : L ≤ ofs W (stk (s.gpr .esp) d) := E.far d hd2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have := Ly.s_le
        have := Ly.o_le
        rcases hr with rfl | rfl <;> simp only <;> omega_arith),
      F2 _ (fun r hr h => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [below_contains hlo hhi (c := 16) (n := 28) esp1 (by decide) (by omega_arith)] at h
        omega_arith), m1]
  obtain saved : ∀ i < 4, readSrc (popped .eax 7 v) (.mem (at_ .esp (4 * i))) = some (s.gpr (rs4[rs4.length - 1 - i]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)))) := by
    intro i hi
    obtain ea : (popped .eax 7 v).ea (at_ .esp (4 * i)) = stk (s.gpr .esp) (40 + 4 * i) := by
      simp only [State.ea, at_, espw]
      rw [show s.gpr .esp - 16 = s.gpr .esp - BitVec.ofNat 32 16 from rfl, stack_addr hlo hhi (by decide) (by omega_arith)]
    show (popped .eax 7 v).load32 _ = _
    rw [ea, State.load32, ite_eq_left_iff.mpr fun h => absurd ?_ h]
    · have w := pushed_word (rs := rs4) (s := s) (by decide) h16 (i := i) hi
      rw [pushed_esp, show 4 * rs4.length = 16 from rfl] at w
      rw [show ((s.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)).setWidth 64 : Addr) =
        stk (s.gpr .esp) (40 + 4 * i) from stack_addr hlo hhi (by decide) (by omega_arith)] at w
      rw [← w, Mem.readW_congr fun j hj => ?_]
      rw [show stk (s.gpr .esp) (40 + 4 * i) + BitVec.ofNat 64 j = stk (s.gpr .esp) (40 + 4 * i + j) from
        add_ofNat64 _ _ _]
      exact mw _ (by omega_arith) (by omega_arith)
    · rw [rdw, wrw]
      refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      have := (s.gpr .esp).isLt
      simp only [Region.Contains, stk, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat]
      rw [show (56 : BitVec 64).toNat = 56 from rfl]
      omega_arith
  -- The callee-saved registers back.
  unfold restoreRegs
  refine wp_movS (saved 0 (by decide)) fun z1 y1 _ =>
    wp_movS ((Dynamic.readSrc_upd y1 (by decide)).trans (saved 1 (by decide))) fun z2 y2 _ =>
    wp_movS (((Dynamic.readSrc_upd y2 (by decide)).trans (Dynamic.readSrc_upd y1 (by decide))).trans
      (saved 2 (by decide))) fun z3 y3 _ => WP.block_nil ?_
  rw [show rs4.length = 4 from rfl]
  obtain g3 : ∀ r, r ≠ .ebp → r ≠ .edi → r ≠ .esi → z3.gpr r = (popped .eax 7 v).gpr r := fun r h1 h2 h3 => by
    rw [y3.other _ h3, y2.other _ h2, y1.other _ h1]
  obtain mem3 : z3.mem = (popped .eax 7 v).mem := by rw [y3.mem, y2.mem, y1.mem]
  obtain esp3 : z3.gpr .esp = s.gpr .esp - 16 := by rw [g3 _ (by decide) (by decide) (by decide), espw]
  obtain ebx3 : (popped .ebx 4 z3).gpr .ebx = s.gpr .ebx := by
    obtain h := saved 3 (by decide)
    simp only [readSrc, State.load32] at h
    split at h
    · simp only [Option.some.injEq] at h
      show (popReg z3 .ebx (3 + 1)).gpr .ebx = _
      rw [popReg_last _ (by decide), esp3, mem3, show s.gpr .ebx = s.gpr rs4[rs4.length - 1 - 3] from rfl, ← h]
      simp only [State.ea, at_, espw]
    · cases h
  obtain mu : (popped .ebx 4 z3).mem = v.mem := by rw [popped_mem, mem3, popped_mem]
  have hw0 : val32 v.mem W o N = val32 v.mem W o N := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mu, ← ws2 Ly.mo_le]; exact lt
  · rw [mu, ← ws2 Ly.mo_le, ← ws2 Ly.a_le, ← ws2 Ly.b_le]; exact cong
  · intro x hr hb
    rw [mu, mv x (fun j hj h => hb (by
        rw [h, hm2 j hj, stack_addr hlo hhi (c := 56) (k := 0) (by decide) (by omega_arith), add_ofNat64]
        rw [below_contains hlo hhi (c := 0) (n := 56) (by simp) (by decide) (by omega_arith)]
        omega_arith)) hr,
      F2 x (fun r h h' => by
        simp only [List.mem_singleton] at h; subst h
        exact hb (below_sub hlo (c := 16) (n := 28) esp1 (by decide) h')),
      F1 x (fun r h h' => by
        simp only [List.mem_singleton] at h; subst h
        exact hb (below_sub hlo (c := 0) (n := 16) (by simp) (by decide) h'))]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ebx3
    · rw [popped_gpr _ _ _ (by decide) (by decide), y3.gpr]; rfl
    · rw [popped_gpr _ _ _ (by decide) (by decide), y3.other _ (by decide), y2.gpr]; rfl
    · rw [popped_gpr _ _ _ (by decide) (by decide), y3.other _ (by decide), y2.other _ (by decide), y1.gpr]; rfl
    · rw [popped_esp, esp3, show BitVec.ofNat 32 (4 * 4) = 16 from rfl, BitVec.sub_add_cancel]
  · rw [popped_rd, y3.rd, y2.rd, y1.rd, rdw]
  · rw [popped_wr, y3.wr, y2.wr, y1.wr, wrw]; rfl

end VG.Proof.Mont.X86.Sse2
