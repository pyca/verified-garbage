module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Csub
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Column
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

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
  have bp : PtrAt s4 W .ebp (S + 24 + 4 * N) := by
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
  have hw₀ := hw.of_keeps u₀.keeps
  have b₀ : PtrAt s₀ W .ebp (S + 24 + 4 * (N - 1 - j)) := by
    rw [PtrAt, u₀.gpr, ptr_sub hebp _ (by rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hj])]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; congr 2; omega_using [hj]
  refine wp_movS (readSrc_ptr hw₀ b₀ (d := 0) (by omega_using [hs, hj])) fun s₁ u₁ _ => ?_
  refine wp_restore (by rw [u₁.other _ (by decide), u₀.other _ (by decide), hc]) fun s₂ u₂ c₂ => ?_
  have K₂ : Keeps [.eax, .edx, .ebp] t s₂ := ((u₀.keeps.mono (by decide)).widen u₁.keeps).widen u₂.keeps
  have hw₂ := hw.of_keeps K₂
  have esi₂ : PtrAt s₂ W .esi (mo + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact hesi
  refine wp_sbbS (readSrc_ptr hw₂ esi₂ (d := 0) (by omega_arith)) c₂ fun s₃ u₃ c₃ => ?_
  have hw₃ := hw₂.of_keeps u₃.keeps
  have ebx₃ : PtrAt s₃ W .ebx (tmp + 4 * j) := by rw [PtrAt, u₃.other _ (by decide), K₂.1 _ (by decide)]; exact hebx
  refine wp_storeS (ea_ptr hw₃ ebx₃ (d := 0) (by omega_arith))
    (ws_write hw₃ (y := tmp + 4 * j + 0) (n := 4) (by omega_arith))
    fun s₄ m₄ => wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_subZ rfl fun s₈ u₈ z₈ => WP.block_nil ?_
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem, u₀.mem]
  have eax₂ : s₂.gpr .eax = t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32 := by
    rw [u₂.other _ (by decide), u₁.gpr, u₀.mem, Nat.add_zero]
  have K₅ : Keeps [.eax, .ecx, .edx, .ebp] t s₅ :=
    ((K₂.mono (by decide)).widen u₃.keeps |>.widen (m₄.keeps [])).widen u₅.keeps
  have r₅ : ∀ r, r = .esi ∨ r = .ebx ∨ r = .edi → s₅.gpr r = t.gpr r := by
    intro r hr; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  have bp₅ : s₅.gpr .ebp = s₀.gpr .ebp := by
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
  have I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, by simpa using hebx,
    by simpa using hedi, Outside.refl _ _ _ _, false, hc, by simp [val32, rvalT]⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega, hN, I₀⟩) fun u ⟨K, _, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, esi, ebx, edi, O, c, ec, V⟩
  have ht' := hw.of_keeps K
  refine WP.mono (subStepR_ok ht' ebp esi ebx edi hj ec hs (by omega_using [hm, hj]) (by omega_using [ht, hj]))
    fun u ⟨mu, eu, pu, su, bu, du, zu, Ku⟩ => ?_
  have ea : w32 t.mem W (S + 24 + 4 * (N - 1 - j)) = w32 t₀.mem W (S + 24 + 4 * (N - 1 - j)) :=
    O.w32 (by omega_using [hts, hj]) (by omega_using [hs, hj, hn])
  have eb : w32 t.mem W (mo + 4 * j) = w32 t₀.mem W (mo + 4 * j) :=
    O.w32 (by omega_using [htm, hj]) (by omega_using [hm, hj, hn])
  have I' : I (j + 1) u := by
    refine ⟨K.trans Ku, pu, su, bu, du, ?_, _, eu, ?_⟩
    · rw [mu]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [ht, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [mu, val32_store hn (by omega_using [ht, hj]), val32_succ t₀.mem W mo, rvalT, pow32_succ]
      have h := sbb_rel (t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32) (t.mem.readW (off W (mo + 4 * j)) 32) c
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
  have hw₁ := hw.of_keeps u₁.keeps
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
    have eax₃ : (s₃.gpr .eax).toNat = w32 p.mem W (S + 16) := by
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
  have hw₀ := hw.of_keeps u₀.keeps
  have b₀ : PtrAt s₀ W .ebp (S + 24 + 4 * (N - 1 - j)) := by
    rw [PtrAt, u₀.gpr, ptr_sub hebp _ (by rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hj])]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; congr 2; omega_using [hj]
  refine wp_movS (readSrc_ptr hw₀ b₀ (d := 0) (by omega_using [hs, hj])) fun s₂ u₂ _ => ?_
  have hw₂ := hw₀.of_keeps u₂.keeps
  have ebx₂ : PtrAt s₂ W .ebx (tmp + 4 * j) := by rw [PtrAt, u₂.other _ (by decide), u₀.other _ (by decide)]; exact hebx
  refine wp_movS (readSrc_ptr hw₂ ebx₂ (d := 0) (by omega_using [ht])) fun s₃ u₃ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  have k₆ : Keeps [.eax, .edx, .ebp] t s₆ := ((((u₀.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen
    u₄.keeps |>.widen u₅.keeps).widen u₆.keeps
  have hw₆ := hw.of_keeps k₆
  have esi₆ : PtrAt s₆ W .esi (o + 4 * j) := by rw [PtrAt, k₆.1 _ (by decide)]; exact hesi
  refine wp_storeS (ea_ptr hw₆ esi₆ (d := 0) (by omega_using [ho]))
    (ws_write hw₆ (y := o + 4 * j + 0) (n := 4) (by omega_using [ho])) fun s₇ m₇ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  refine wp_subZ rfl fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have r₇ : ∀ r, r = .esi ∨ r = .ebx ∨ r = .edi → s₇.gpr r = t.gpr r := by
    intro r hr; rw [m₇.gpr]; apply k₆.1; rcases hr with rfl | rfl | rfl <;> decide
  have bp₇ : s₇.gpr .ebp = s₀.gpr .ebp := by
    rw [m₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]
  obtain ⟨c₁, c₂⟩ := count_zf hedi hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₀.mem]
    have ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₀.other _ (by decide)]
    have eax₆ : s₆.gpr .eax = t.mem.readW (off W (S + 24 + 4 * (N - 1 - j))) 32 ^^^
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
  have I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hesi,
    by simpa using hedi, Outside.refl _ _ _ _, by cases k <;> rfl⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega_using [hN], hN, I₀⟩) fun u ⟨K, _, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, ebx, esi, edi, O, V⟩
  have ht' := hw.of_keeps K
  have hm' : t.gpr .ecx = if k then BitVec.allOnes 32 else 0 := by rw [K.1 _ (by decide)]; exact hm
  refine WP.mono (selStepR_ok ht' k ebp ebx esi edi hj hm' hs (by omega_using [ht, hj])
    (by omega_using [ho, hj])) fun u ⟨mu, pu, bu, su, du, zu, Ku⟩ => ?_
  have I' : I (j + 1) u := by
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
  have P1 := P.of_keeps K1 (by rw [m1]; exact Outs.refl _ _ _)
  refine wp_movS (P1.read pM (by decide)) fun u2 v2 _ => wp_movS ((P1.of_upd v2).read pN4 (by decide))
    fun u3 v3 _ => wp_movS rfl fun u4 v4 _ => WP.block_nil ?_
  have K4 : Keeps clob7 p u4 := (((K1.mono (by decide)).widen v2.keeps).widen v3.keeps).widen v4.keeps
  have m4 : u4.mem = p.mem := by rw [v4.mem, v3.mem, v2.mem, m1]
  refine WP.mono (subLoopR_ok (hw.of_keeps K4) hN (S := S) (mo := mo) (tmp := S + 24 + 4 * N)
    (by omega_using [hs]) hmo (by omega_using [hs]) (.inr (Nat.le_refl _)) (by omega_using [hsmo])
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact bp1)
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.gpr]; exact PV.mo)
    (by rw [PtrAt, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact bx1)
    (by rw [v4.other _ (by decide), v3.gpr, PV.n4]) v4.gpr) fun u5 ⟨O5, ⟨c, ec5, V5⟩, K5⟩ => ?_
  have K5p : Keeps clob7 p u5 := K4.trans K5
  have hw5 := hw.of_keeps K5p
  have O5' : Outs W [(0, L)] p.mem u5.mem := by
    rw [← m4]; exact Outs.of_outside (O5.mono (o' := 0) (n' := L) (by omega_using []) (by omega_using [hs])) (by simp)
  have P5 := P.of_keeps K5p O5'
  have top5 : w32 u5.mem W (S + 16) = w32 p.mem W (S + 16) := by
    rw [← m4]; exact O5.w32 (by omega_using []) (by omega_using [hs, hn])
  -- The mask.
  refine WP.seq (WP.mono (maskS_ok Ly PV hw5 P5 ec5) fun u6 ⟨mk, m6, K6⟩ => ?_)
  rw [top5] at mk
  generalize hk : (!(decide (w32 p.mem W (S + 16) < c.toNat))) = k at mk
  have P6 := P5.of_keeps K6 (by rw [m6]; exact Outs.refl _ _ _)
  have hw6 := hw5.of_keeps K6
  -- The selection.
  unfold select
  refine WP.seq (WP.block_append (WP.mono (ptrs_ok PV P6) fun u7 ⟨bx7, bp7, m7, K7⟩ => ?_))
  have P7 := P6.of_keeps K7 (by rw [m7]; exact Outs.refl _ _ _)
  refine wp_movS (P7.read pO (by decide)) fun u8 v8 _ => wp_movS ((P7.of_upd v8).read pN4 (by decide))
    fun u9 v9 _ => WP.block_nil ?_
  have K9 : Keeps [.eax, .ebx, .ebp, .esi, .edi] u6 u9 := ((K7.mono (by decide)).widen v8.keeps).widen v9.keeps
  have m9 : u9.mem = u5.mem := by rw [v9.mem, v8.mem, m7, m6]
  refine WP.mono (selLoopR_ok (hw6.of_keeps K9) k hN (S := S) (tmp := S + 24 + 4 * N) (o := o)
    (by omega_using [hs]) (by omega_using [hs]) ho (by omega_using [hso]) (by omega_using [hso])
    (by rw [PtrAt, v9.other _ (by decide), v8.other _ (by decide)]; exact bp7)
    (by rw [PtrAt, v9.other _ (by decide), v8.other _ (by decide)]; exact bx7)
    (by rw [PtrAt, v9.other _ (by decide), v8.gpr]; exact PV.o)
    (by rw [v9.gpr, PV.n4])
    (by rw [v9.other _ (by decide), v8.other _ (by decide), K7.1 _ (by decide)]; exact mk))
    fun v ⟨Ov, Vv, Kv⟩ => ⟨?_, ?_, ?_⟩
  · -- The value.
    have T5 : rvalT u5.mem W N S N = rvalT p.mem W N S N := by
      rw [← m4]
      exact rvalT_congr fun j hj => O5.w32 (by omega_using [hj]) (by omega_using [hs, hj, hn])
    rw [m4] at V5
    rw [m9, T5] at Vv
    have hM : val32 p.mem W mo N < 2 ^ (32 * N) := val32_lt _ _ _ _
    have sel := csub_arith hM (val32_lt u5.mem W (S + 24 + 4 * N) N) hT V5 (b := c)
      (top := w32 p.mem W (S + 16))
    rw [Vv, ← hk, ← sel]
    by_cases h : w32 p.mem W (S + 16) < c.toNat <;> simp [h]
  · have e2 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] p.mem u5.mem := by
      rw [← m4]; exact Outs.of_outside (O5.mono (o' := S + 24) (n' := 8 * N + 4) (by omega_using []) (by omega_using []))
        (by simp)
    have e3 : Outs W [(S + 24, 8 * N + 4), (o, 4 * N)] u5.mem v.mem := by
      rw [← m9]; exact Outs.of_outside Ov (by simp)
    exact e2.trans e3
  · exact ((K5p.trans (K6.mono (by decide))).trans (K9.mono (by decide))).trans (Kv.mono (by decide))

end VG.Proof.Mont.X86.Sse2
