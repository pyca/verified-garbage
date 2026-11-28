module

-- separate module: a tree's parts, which `ForsMain` does not rebuild when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, a tree

`topHeights`: the heights of tree `t` above its subtrees (for `s < a`,
`levels` over the subtree roots copied to `oN`), its root to lane 0 of the
lanes `B` (`top_ok`); `treeBody`: the tree's index, its signature zeroed,
the subtrees and the heights above them, the next tree (`tree_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)

/-- The block before the call of `levels` above the subtrees: `capBase = 0`,
`adrsBase = V4`, `FORS_TREE`, `kp`; the `2^(a-s)` subtree roots at `oN`
from height `s`, the path at `AU + n + s·n`. -/
theorem topB_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha : p.a ≤ 14) {S AU : Addr} {V4 : Nat}
    {u : State} (hbx : u.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr)
    (h1 : u.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h4 : u.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4) :
    WP isa (.block (([.mov .r10 (.mem (var 1)),
        .alu .add .r10 (.imm (BitVec.ofNat 32 ((⟨p.n, p.len⟩ : Layout).n + s p.a * (⟨p.n, p.len⟩ : Layout).n)))] :
          List Instr) ++
        Impl.SlhDsa.X86_64.Tree.setParams (.imm 0) (.mem (var 4)) (.imm 3) (.reg .r12) ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
          .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ (p.a - s p.a)))), .mov32 .rcx (.imm (BitVec.ofNat 32 (s p.a))),
          .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)] : List Instr))) u
      fun u' => LB p.n S u u' (2 ^ (p.a - s p.a)) (s p.a) (AU + BitVec.ofNat 64 (p.n + s p.a * p.n))
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 V4) (BitVec.ofNat 64 3) (u.gpr .r12) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have has := a_s ha
  have hsn : s p.a * p.n ≤ 9 * 32 := Nat.mul_le_mul hs9 hn32
  have h32 : 2 ^ (p.a - s p.a) ≤ 32 := by
    calc 2 ^ (p.a - s p.a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) has
      _ = 32 := rfl
  have hin : ∀ (t : State), t.rd = u.rd → t.wr = u.wr → ∀ f i, f < 5 → i < 9 →
      InRegions (t.rd ++ t.wr) (at' S (Layout.oVar f i)) 8 := fun t hr hw' f i hf hi => by
    rw [hr, hw']; exact Levels.in_scr' hw (by simp only [Layout.oVar, Layout.oFrame, Layout.oVars]; omega_using [hf, hi])
  refine WP.mono_mx (by simp [Code.allInstrs_eq, instrs, Impl.SlhDsa.X86_64.Tree.setParams, loadsMxcsr])
    (Q := fun u' => u'.mxcsr = u.mxcsr → LB p.n S u u' (2 ^ (p.a - s p.a)) (s p.a)
      (AU + BitVec.ofNat 64 (p.n + s p.a * p.n)) (BitVec.ofNat 64 0) (BitVec.ofNat 64 V4) (BitVec.ofNat 64 3)
      (u.gpr .r12)) ?_ fun _ h hm => h hm
  simp only [Impl.SlhDsa.X86_64.Tree.setParams, Impl.SlhDsa.X86_64.Tree.var, List.cons_append, List.nil_append]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (hin u rfl rfl 2 1 (by decide) (by decide)) fun u₁ e₁ => ?_
  refine Proof.Sha3.X86_64.wp_addi fun u₂ e₂ => ?_
  have hb₂ : u₂.gpr .rbx = S := by rw [e₂.other _ (by decide), e₁.other _ (by decide), hbx]
  have hm₂ : u₂.mem = u.mem := by rw [e₂.mem, e₁.mem]
  have h10 : u₂.gpr .r10 = AU + BitVec.ofNat 64 (p.n + s p.a * p.n) := by
    rw [e₂.gpr, e₁.gpr, h1, Levels.sx_ofNat (by omega_using [hsn, hn32])]
  -- the parameters
  refine wp_movi fun u₅ e₅ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 5)) (by rw [Proof.Sha3.X86_64.ea_at, e₅.other _ (by decide), hb₂])
    (by rw [e₅.wr, e₂.wr, e₁.wr]; exact Levels.in_scr hw (by rw [oVar4]; omega_using [])) fun u₆ g₆ m₆ r₆ w₆ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 4))
    (by rw [var, Proof.Sha3.X86_64.ea_at, g₆, e₅.other _ (by decide), hb₂])
    (hin u₆ (by rw [r₆, e₅.rd, e₂.rd, e₁.rd]) (by rw [w₆, e₅.wr, e₂.wr, e₁.wr]) 2 4 (by decide) (by decide)) fun u₇ e₇ => ?_
  have hv4 : u₆.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4 := by
    rw [m₆, Mem.readW_writeW_sep (Offset.sep S (by rw [oVar4, oVar2]; omega_using []) (by rw [oVar2]; omega_using [])
      (by rw [oVar4]; omega_using [])) (by decide), e₅.mem, hm₂, h4]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 6))
    (by rw [Proof.Sha3.X86_64.ea_at, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hb₂])
    (by rw [e₇.wr, w₆, e₅.wr, e₂.wr, e₁.wr]; exact Levels.in_scr hw (by rw [oVar4]; omega_using [])) fun u₈ g₈ m₈ r₈ w₈ => ?_
  refine wp_movi fun u₉ e₉ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 7))
    (by rw [Proof.Sha3.X86_64.ea_at, e₉.other _ (by decide), g₈, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hb₂])
    (by rw [e₉.wr, w₈, e₇.wr, w₆, e₅.wr, e₂.wr, e₁.wr]; exact Levels.in_scr hw (by rw [oVar4]; omega_using []))
    fun u₁₀ g₁₀ m₁₀ r₁₀ w₁₀ => ?_
  refine Proof.Sha3.X86_64.wp_mov fun u₁₁ e₁₁ => ?_
  have hb₁₁ : u₁₁.gpr .rbx = S := by
    rw [e₁₁.other _ (by decide), g₁₀, e₉.other _ (by decide), g₈, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hb₂]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 8)) (by rw [Proof.Sha3.X86_64.ea_at, hb₁₁])
    (by rw [e₁₁.wr, w₁₀, e₉.wr, w₈, e₇.wr, w₆, e₅.wr, e₂.wr, e₁.wr]; exact Levels.in_scr hw (by rw [oVar4]; omega_using []))
    fun u₁₂ g₁₂ m₁₂ r₁₂ w₁₂ => ?_
  refine Proof.Sha3.X86_64.wp_mov fun u₁₃ e₁₃ => Proof.Sha3.X86_64.wp_mov fun u₁₄ e₁₄ =>
    Proof.Sha3.X86_64.wp_addi fun u₁₅ e₁₅ => Proof.Sha3.X86_64.wp_mov32i fun u₁₆ e₁₆ =>
    Proof.Sha3.X86_64.wp_mov32i fun u₁₇ e₁₇ => Proof.Sha3.X86_64.wp_mov fun u₁₈ e₁₈ =>
    Proof.Sha3.X86_64.wp_mov fun u₁₉ e₁₉ => WP.block_nil fun hmx => ?_
  have G : ∀ g, g ≠ .rax → g ≠ .r10 → u₁₂.gpr g = u.gpr g := fun g h₀ h₇ => by
    rw [g₁₂, e₁₁.other _ h₀, g₁₀, e₉.other _ h₀, g₈, e₇.other _ h₀, g₆, e₅.other _ h₀, e₂.other _ h₇, e₁.other _ h₇]
  have hm₁₂ : u₁₂.mem = (((u.mem.writeW (at' S (Layout.oVar 4 5)) (BitVec.ofNat 64 0)).writeW (at' S (Layout.oVar 4 6))
      (BitVec.ofNat 64 V4)).writeW (at' S (Layout.oVar 4 7)) (BitVec.ofNat 64 3)).writeW
      (at' S (Layout.oVar 4 8)) (u.gpr .r12) := by
    rw [m₁₂, e₁₁.mem, m₁₀, e₉.mem, m₈, e₇.mem, m₆, e₅.mem, hm₂, e₁₁.gpr, g₁₀, e₉.other .r12 (by decide), g₈,
      e₇.other .r12 (by decide), g₆, e₅.other .r12 (by decide), e₂.other .r12 (by decide), e₁.other .r12 (by decide),
      e₉.gpr, show BitVec.signExtend 64 (3 : BitVec 32) = BitVec.ofNat 64 3 by decide, e₇.gpr, hv4, e₅.gpr,
      show BitVec.signExtend 64 (0 : BitVec 32) = BitVec.ofNat 64 0 by decide]
  obtain ⟨s5, s6, s7, s8, sf⟩ := stores_val (m := u.mem) (S := S) (BitVec.ofNat 64 0) (BitVec.ofNat 64 V4)
    (BitVec.ofNat 64 3) (u.gpr .r12)
  have hm₁₉ : u₁₉.mem = u₁₂.mem := by rw [e₁₉.mem, e₁₈.mem, e₁₇.mem, e₁₆.mem, e₁₅.mem, e₁₄.mem, e₁₃.mem]
  refine ⟨fun g h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmx, by rw [hm₁₉, hm₁₂]; exact s5,
    by rw [hm₁₉, hm₁₂]; exact s6, by rw [hm₁₉, hm₁₂]; exact s7, by rw [hm₁₉, hm₁₂]; exact s8, by rw [hm₁₉, hm₁₂]; exact sf⟩
  · rw [e₁₉.other _ h₆, e₁₈.other _ h₅, e₁₇.other _ h₁, e₁₆.other _ h₂, e₁₅.other _ h₃, e₁₄.other _ h₃, e₁₃.other _ h₄,
      G g h₀ h₇]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide),
      e₁₅.other _ (by decide), e₁₄.other _ (by decide), e₁₃.gpr, g₁₂, hb₁₁]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide),
      e₁₅.gpr, e₁₄.gpr, e₁₃.other _ (by decide), g₁₂, hb₁₁, Levels.sx_ofNat (by decide)]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.gpr,
      setW _ (by omega_using [h32])]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.gpr, setW _ (by omega_using [hs9])]
  · rw [e₁₉.other _ (by decide), e₁₈.gpr, e₁₇.other _ (by decide), e₁₆.other _ (by decide), e₁₅.other _ (by decide),
      e₁₄.other _ (by decide), e₁₃.other _ (by decide), g₁₂, e₁₁.other _ (by decide), g₁₀, e₉.other _ (by decide), g₈,
      e₇.other _ (by decide), g₆, e₅.other _ (by decide), h10]
  · rw [e₁₉.gpr, e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide), e₁₅.other _ (by decide),
      e₁₄.other _ (by decide), e₁₃.other _ (by decide), G _ (by decide) (by decide)]
  · rw [e₁₉.rd, e₁₈.rd, e₁₇.rd, e₁₆.rd, e₁₅.rd, e₁₄.rd, e₁₃.rd, r₁₂, e₁₁.rd, r₁₀, e₉.rd, r₈, e₇.rd, r₆, e₅.rd, e₂.rd, e₁.rd]
  · rw [e₁₉.wr, e₁₈.wr, e₁₇.wr, e₁₆.wr, e₁₅.wr, e₁₄.wr, e₁₃.wr, w₁₂, e₁₁.wr, w₁₀, e₉.wr, w₈, e₇.wr, w₆, e₅.wr, e₂.wr, e₁.wr]

theorem rootB_nm (L : Layout) (R : Nat) : (([.mov .rdx (.mem (var 0))] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN L.n .rdx .rcx ++
    ([.alu .add .rdx (.reg .rbx)] : List Instr) ++ copyWords .rdx (Layout.laneB 0 + L.msgOff) .rbx R (L.n / 8) : List Instr).all
    (fun i => !loadsMxcsr i) = true := by
  simp only [List.all_append, mulN_nm, copyWords_nm]
  simp [loadsMxcsr]

/-- The tree's root, the `n` bytes at `S + R`, to string `tt` of lane 0 of the lanes `B`'s message. -/
theorem rootB_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {tt R : Nat} {u : State}
    (hbx : u.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr)
    (h0 : u.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) (htk : (tt + 1) * p.n ≤ 1120)
    (hR : R + p.n ≤ 31648) (hRB : R + p.n ≤ 3808 ∨ 3808 + p.n + 32 + 1120 ≤ R) :
    WP isa (.block (([.mov .rdx (.mem (var 0))] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Layout).n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).msgOff) .rbx R ((⟨p.n, p.len⟩ : Layout).n / 8))) u fun u' =>
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      bytesAt u'.mem (at' S (Layout.laneB 0 + p.n + 32 + tt * p.n)) p.n = bytesAt u.mem (at' S R) p.n ∧
      Frame [⟨at' S (Layout.laneB 0 + p.n + 32 + tt * p.n), p.n⟩] u.mem u'.mem := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have eB : Layout.laneB 0 = 3808 := rfl
  have htn : tt * p.n + p.n ≤ 1120 := by rw [← Nat.succ_mul]; exact htk
  refine WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using rootB_nm ⟨p.n, p.len⟩ R)
    (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_ fun _ h hm => h hm
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 0)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (Levels.in_scr' hw (by rw [oVar2]; omega_using [])) fun u₁ e₁ => ?_
  refine Levels.mulN_ok hn (by decide) fun u₃ h₃ g₃ m₃ r₃ w₃ => ?_
  refine Levels.wp_add fun u₄ e₄ => ?_
  have hdx : u₄.gpr .rdx = at' S (tt * p.n) := by
    rw [e₄.gpr, h₃, e₁.gpr, h0, BitVec.ofNat_mul_ofNat, g₃ _ (by decide) (by decide), e₁.other _ (by decide), hbx,
      BitVec.add_comm]
  have hb₄ : u₄.gpr .rbx = S := by rw [e₄.other _ (by decide), g₃ _ (by decide) (by decide), e₁.other _ (by decide), hbx]
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, m₃, e₁.mem]
  have hw₄ : u₄.wr = u.wr := by rw [e₄.wr, w₃, e₁.wr]
  refine WP.mono (Levels.copy_ok (S := S) (a := tt * p.n) (b := 0) (d₁ := R) (d₂ := Layout.laneB 0 + (p.n + 32))
    (by decide) (by decide) (p.n / 8) u₄ hdx (by rw [hb₄]; exact Levels.scr0 S) (by rw [hw₄]; exact hw)
    (by omega_using [e8, hR]) (by rw [eB]; omega_using [e8, htn, hn32]) (by rw [eB]; omega_using [e8, htn, hn32, hRB]))
    fun u' ⟨g', r', w', c', f'⟩ hmx => ?_
  rw [e8] at c' f'
  refine ⟨fun g h₀ h₁ h₂ => by rw [g' _ h₀, e₄.other _ h₂, g₃ _ h₂ h₁, e₁.other _ h₂], by rw [r', e₄.rd, r₃, e₁.rd],
    by rw [w', hw₄], hmx, ?_, ?_⟩
  · rw [← hm₄]
    refine bytesAt_ext fun i hi => ?_
    rw [Levels.add_add, Levels.add_add, show Layout.laneB 0 + p.n + 32 + tt * p.n + i =
      tt * p.n + (Layout.laneB 0 + (p.n + 32)) + i by omega_using [], c' i hi, Nat.zero_add]
  · rw [hm₄, show tt * p.n + (Layout.laneB 0 + (p.n + 32)) = Layout.laneB 0 + p.n + 32 + tt * p.n by omega_using []] at f'
    exact f'

/-- What a tree's heights above its subtrees leave. -/
structure TopP (p : Params) (stack : Nat) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp tt idx : Nat)
    (t₀ t t' : State) : Prop where
  fix : Fix t₀ t'
  env : Env p t'.mem S pkSeed a16
  sk : SkAt p t'.mem S skSeed
  vars : ∀ i, i < 9 → i ≠ 2 → i ≠ 3 →
    t'.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64
  skp : ∀ j < p.n, t'.mem (AU + BitVec.ofNat 64 j) = skv p pkSeed a16 skSeed kp (tt * 2 ^ p.a + idx) j
  auth : ∀ r < p.a, bytesAt t'.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    node p skSeed pkSeed a16 kp (tt * 2 ^ (p.a - r) + sib idx r) r
  root : bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + tt * p.n)) p.n = node p skSeed pkSeed a16 kp tt p.a
  frame : Frame (subW p S AU (t₀.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32 + tt * p.n), p.n⟩])
    t₀.mem t'.mem

theorem top_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) (htk : (tt + 1) * p.n ≤ 1120) {t : State}
    (hI : ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t)
    (h0 : t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) :
    WP isa (topHeights ⟨p.n, p.len⟩ p.a name ln T.code) t
      (TopP p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ t) := by
  have hn := C.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs6 := s_ge C.a6
  have hsa := s_le p.a
  have has := a_s C.a14
  have han : (p.a + 1) * p.n = p.n + p.a * p.n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hAN : (p.a + 1) * p.n ≤ 15 * 32 := Nat.mul_le_mul (by omega_using [C.a14]) hn32
  have hdAn : dA + (p.a + 1) * p.n ≤ L := C.dA
  have htn : tt * p.n + p.n ≤ 1120 := by rw [← Nat.succ_mul]; exact htk
  have hbx : t.gpr .rbx = S := by rw [hI.fix.cs _ (by simp [calleeSaved]), C.bx]
  have hsp : t.gpr .rsp = t₀.gpr .rsp := hI.fix.cs _ (by simp [calleeSaved])
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [hI.fix.wr]; exact C.w
  have h16 : a16.length = 16 := by rw [← hI.env.adrsA 0 (by decide)]; simp [bytesAt]
  have dXs : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n → ∀ {R : Region}, Region.Sub R ⟨S, Layout.oSigTmp⟩ →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ R := fun {o l} h {R} hR =>
    (C.Gd.sub_left (sigSub C.AU (by omega_using [h, hdAn]))).sub_right hR
  have sS : ∀ {o l : Nat}, o + l ≤ 31648 → Region.Sub ⟨at' S o, l⟩ ⟨S, Layout.oSigTmp⟩ := fun h =>
    Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; exact h)
  have eB : Layout.laneB 0 = 3808 := rfl
  have bk : ∀ {rs : List Region} {m m' : Mem} (x : Addr), Frame rs m m' → (∀ r ∈ rs, Region.Disjoint ⟨x, 1⟩ r) →
      m' x = m x := fun x f h => by simpa using f.bytes (R := ⟨x, 1⟩) h (show 1 ≤ 2 ^ 64 by decide) (show 0 < 1 by decide)
  -- the last block, from a state `v` with the tree's root at `S + R`
  have fin : ∀ (R : Nat) (v : State), R + p.n ≤ 31648 → (R + p.n ≤ 3808 ∨ 3808 + p.n + 32 + 1120 ≤ R) →
      Fix t₀ v → Env p v.mem S pkSeed a16 → SkAt p v.mem S skSeed →
      (∀ i, i < 9 → i ≠ 2 → i ≠ 3 → v.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64) →
      (∀ j < p.n, v.mem (AU + BitVec.ofNat 64 j) = skv p pkSeed a16 skSeed (t₀.gpr .r12).toNat (tt * 2 ^ p.a + idx) j) →
      (∀ r < p.a, bytesAt v.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
        node p skSeed pkSeed a16 (t₀.gpr .r12).toNat (tt * 2 ^ (p.a - r) + sib idx r) r) →
      bytesAt v.mem (at' S R) p.n = node p skSeed pkSeed a16 (t₀.gpr .r12).toNat tt p.a →
      Frame (subW p S AU (t₀.gpr .rsp) stack) t₀.mem v.mem →
      WP isa (.block ([.mov .rdx (.mem (var 0))] ++ Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Layout).n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).msgOff) .rbx R ((⟨p.n, p.len⟩ : Layout).n / 8))) v
        (TopP p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ t) := by
    intro R v hR hRB fx ev sv vv skv' av rv fv
    refine WP.mono (rootB_ok (S := S) hn (by rw [fx.cs _ (by simp [calleeSaved]), C.bx]) (by rw [fx.wr]; exact C.w)
      (by rw [vv 0 (by decide) (by decide) (by decide), h0]) htk hR hRB) fun v' ⟨g', r', w', mx', c', f'⟩ => ?_
    have dch : ∀ q, q < 31648 → (q < 3808 + p.n + 32 + tt * p.n ∨ 3808 + p.n + 32 + tt * p.n + p.n ≤ q) →
        v'.mem (at' S q) = v.mem (at' S q) := fun q hq h => keepS f' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [eB]; omega_using [h]) (by omega_using [hq]) (by rw [eB]; omega_using [htn, hn32])
    have dsig : ∀ o l, o + l ≤ (p.a + 1) * p.n → ∀ r ∈ [(⟨at' S (Layout.laneB 0 + p.n + 32 + tt * p.n), p.n⟩ : Region)],
        Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun o l h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dXs h (sS (by rw [eB]; omega_using [htn, hn32]))
    refine ⟨fx.trans ⟨fun r hr => g' r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), r', w', by rw [mx']⟩,
      env_bytes hn32 ev fun q hq => dch q (by simp only [EnvB] at hq; omega_using [hq]) (by
        simp only [EnvB] at hq; omega_using [hq, hn32, htn]),
      sk_bytes sv fun q h₁ h₂ => dch q (by omega_using [h₂, hn32]) (.inl (by omega_using [h₂, hn32])),
      fun i hi h2 h3 => by
        rw [← vv i hi h2 h3]
        exact Mem.readW_congr fun j hj => by
          rw [Levels.add_add, oVar2]; exact dch _ (by omega_using [hi, hj]) (.inl (by omega_using [hi, hj])),
      fun j hj => by rw [bk _ f' (dsig j 1 (by omega_using [hj, han]))]; exact skv' j hj,
      fun r hr => ?_, by rw [c', rv], ?_⟩
    · have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
        have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [hr]); rw [Nat.succ_mul] at this
        omega_using [this, han]
      rw [Levels.add_add, bytesAt_frame f' (dsig _ _ hrn) (by omega_using [hn32]), ← Levels.add_add]; exact av r hr
    · refine (fv.mono fun r hr => List.mem_append_left _ hr).trans (f'.mono fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr; simp
  have hall : ∀ r < s p.a, bytesAt t.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
      node p skSeed pkSeed a16 (t₀.gpr .r12).toNat (tt * 2 ^ (p.a - r) + sib idx r) r := fun r hr => by
    rw [hI.auth r hr]; exact acc_all p skSeed pkSeed a16 _ C.idx hsa hr
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have hskp : ∀ j < p.n, t.mem (AU + BitVec.ofNat 64 j) = skv p pkSeed a16 skSeed (t₀.gpr .r12).toNat (tt * 2 ^ p.a + idx) j :=
    fun j hj => by rw [hI.skp j hj, hUs, ite_eq_left C.idx]
  unfold topHeights
  by_cases hc : s p.a < p.a
  · rw [ite_eq_left hc, show rootOff p.a = Layout.oN from ite_eq_left hc]
    have h2U : 2 ^ (p.a - s p.a) ≤ 32 := by
      calc 2 ^ (p.a - s p.a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) has
        _ = 32 := rfl
    have hUn : 2 ^ (p.a - s p.a) * p.n ≤ 1024 := by have := Nat.mul_le_mul h2U hn32; omega_using [this]
    have h8 : 8 ∣ p.n := by omega_using [hn]
    have e8 : 8 * (2 ^ (p.a - s p.a) * p.n / 8) = 2 ^ (p.a - s p.a) * p.n :=
      Nat.mul_div_cancel' (Nat.dvd_mul_left_of_dvd h8 _)
    have eN : Layout.oN = 12640 := rfl
    have eR : Layout.oRoots = 29280 := rfl
    refine WP.seq (WP.seq (WP.block_append (WP.block_append (WP.block_append
      (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using
          (copyWords_nm .rbx Layout.oN .rbx Layout.oRoots (2 ^ (p.a - s p.a) * p.n / 8)))
        (Levels.copy_ok (S := S) (a := 0) (b := 0) (d₁ := Layout.oRoots) (d₂ := Layout.oN) (by decide) (by decide)
          (2 ^ (p.a - s p.a) * p.n / 8) t (by rw [hbx]; exact Levels.scr0 S) (by rw [hbx]; exact Levels.scr0 S) hw
          (by rw [e8, eR]; omega_using [hUn]) (by rw [e8, eN]; omega_using [hUn]) (by rw [e8, eN, eR]; omega_using [hUn]))
        fun u₁ ⟨g₁, r₁, w₁, c₁, f₁⟩ mx₁ => ?_)))))
    rw [e8, Nat.zero_add, Nat.zero_add] at c₁
    rw [e8, Nat.zero_add] at f₁
    have kc : ∀ q, q < 2 ^ 16 → (q < Layout.oN ∨ Layout.oN + 2 ^ (p.a - s p.a) * p.n ≤ q) →
        u₁.mem (at' S q) = t.mem (at' S q) := fun q hq h => keepS f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by omega_using [h]) (by omega_using [hq]) (by rw [eN]; omega_using [hUn])
    have kcw : ∀ i, i < 9 → u₁.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
      fun i hi => Mem.readW_congr fun j hj => by
        rw [Levels.add_add, oVar2]; exact kc _ (by omega_using [hi, hj]) (.inl (by rw [eN]; omega_using [hi, hj]))
    have hbx₁ : u₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbx]
    have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ u₁.wr := by rw [w₁]; exact hw
    refine WP.block_append_iff.mp (WP.block_append_iff.mp (WP.mono (topB_ok hn C.a14 (V4 := tt * 2 ^ p.a) (AU := AU)
      hbx₁ hw₁ (by rw [kcw 1 (by decide), hI.v1]) (by rw [kcw 4 (by decide), hI.v4])) fun u₂ B => ?_))
    have nr := fun g => B.gpr g
    have hsp₂ : u₂.gpr .rsp = t₀.gpr .rsp := by
      rw [B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), hsp]
    have kB : ∀ q, q < 2 ^ 16 → (q < 3000 ∨ 3032 ≤ q) → u₂.mem (at' S q) = u₁.mem (at' S q) := fun q hq h =>
      keepS B.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dS S (by rw [oVar4]; omega_using [h]) (by omega_using [hq]) (by rw [oVar4]; omega_using [])
    have hE₂ : Env p u₂.mem S pkSeed a16 := env_bytes hn32 (env_bytes hn32 hI.env fun q hq => kc q
      (by simp only [EnvB] at hq; omega_using [hq]) (.inl (by simp only [EnvB] at hq; rw [eN]; omega_using [hq])))
      fun q hq => kB q (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
    have hsn : s p.a * p.n ≤ p.a * p.n := Nat.mul_le_mul_right _ hsa
    have has1 : (p.a - s p.a) * p.n + s p.a * p.n = p.a * p.n := by rw [← Nat.add_mul, Nat.sub_add_cancel hsa]
    have hAU' : AU + BitVec.ofNat 64 (p.n + s p.a * p.n) = SG + BitVec.ofNat 64 (dA + (p.n + s p.a * p.n)) := by
      rw [C.AU, Levels.add_add]
    have hsubA : Region.Sub ⟨AU + BitVec.ofNat 64 (p.n + s p.a * p.n), (p.a - s p.a) * p.n⟩ ⟨SG, L⟩ := by
      rw [hAU']; exact Offset.sub_base SG (by omega_using [hdAn, han, has1])
    have ht : ∀ (x : Nat), x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hx])
    have hV4 : tt * 2 ^ p.a < 2 ^ 32 := by have := C.tt; rw [Nat.succ_mul] at this; omega_using [this]
    have hva : ∀ i, varAt u₂.mem S 4 i = u₂.mem.readW (at' S (Layout.oVar 4 i)) 64 := fun _ => rfl
    have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
    have hpos : 1 ≤ (p.a - s p.a) * p.n := Nat.mul_pos (by omega_using [hc]) (by omega_using [hn])
    refine lcall_ok T name ln hn C.hf hst hs63 (h := p.a - s p.a) (z₀ := s p.a) (L := L) (d := dA + (p.n + s p.a * p.n))
      (pkSeed := pkSeed) (a16 := a16) B.rdi B.rsi B.rdx B.rcx B.r8
      (by rw [B.r9, g₁ _ (by decide), hI.fix.cs _ (by simp [calleeSaved]), C.r13, ht idx (by omega_using [C.idx, h2a])]
          omega_using [C.idx, h2a]) (by omega_using [hc]) (by omega_using [hsa, C.a14])
      (by rw [show Layout.nodeSlots = 520 from rfl]; have := Nat.mul_le_mul (show 2 ^ (p.a - s p.a) + 8 ≤ 40 by omega_using [h2U]) hn32
          omega_using [this])
      (by rw [B.wr, w₁, hI.fix.wr]; exact C.w) (by rw [B.wr, w₁, hI.fix.wr]; exact C.wG) hAU'
      (by omega_using [hdAn, han, has1]) C.fit (by rw [hsp₂]; exact C.stk)
      (by rw [hAU', Levels.toNat_at (by have := C.Gf; omega_using [this, hdAn, han, has1, hpos])]
          have := C.Gf; omega_using [this, hdAn, han, has1])
      (C.Gd.sub_left hsubA) (by rw [hsp₂]; exact C.Gs.sub_left hsubA) hE₂ (fun i h₁ h₂ => by
        rw [hva]
        rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [h₁, h₂]) with rfl | rfl | rfl | rfl
        · rw [B.v5]; decide
        · rw [B.v6, ht _ hV4]; exact hV4
        · rw [B.v7]; decide
        · rw [B.v8, g₁ _ (by decide), hI.fix.cs _ (by simp [calleeSaved])]; exact C.kp)
      fun v' fx ev rt au fr => ?_
    have hcnt : Layout.oN + (2 ^ (p.a - s p.a) + 8) * p.n ≤ 31648 := by
      have := Nat.mul_le_mul (show 2 ^ (p.a - s p.a) + 8 ≤ 40 by omega_using [h2U]) hn32; rw [eN]; omega_using [this]
    have kL : ∀ q, q < 31648 → 1600 ≤ q → (q < 2368 ∨ 2400 ≤ q) → (q < 2912 ∨ 3040 ≤ q) →
        (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 16 + (16 + 2 * p.n) ≤ q) →
        (q < Layout.oN ∨ Layout.oN + (2 ^ (p.a - s p.a) + 8) * p.n ≤ q) → v'.mem (at' S q) = u₂.mem (at' S q) :=
      fun q hq h₀ h₁ h₂ h₃ h₄ => keepS fr fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
          · exact dS S (h₃ k hk |>.imp (by omega_using []) id) (by omega_using [hq])
              (by rw [laneA_eq]; omega_using [hk, hn32])
          · exact Offset.disjoint_base S h₀ (by omega_using [hq])
          · exact dS S (by omega_using [h₁]) (by omega_using [hq]) (by decide)
          · exact dS S (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [h₂]) (by omega_using [hq]) (by decide)
          · exact dS S (by omega_using [h₄]) (by omega_using [hq]) (by omega_using [hcnt])
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ((C.Gd.sub_left hsubA).sub_right (sS (by omega_using [hq]))).symm
          · rw [hsp₂]; exact (C.stk.sub_right (Levels.sub_scr S (by omega_using [hq]))).symm
    -- `scratch` from `t` to `v'`, outside what the block and the call change
    have kT : ∀ q, q < 31648 → 1600 ≤ q → (q < 2368 ∨ 2400 ≤ q) → (q < 2912 ∨ 3040 ≤ q) →
        (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 16 + (16 + 2 * p.n) ≤ q) →
        (q < Layout.oN ∨ Layout.oN + (2 ^ (p.a - s p.a) + 8) * p.n ≤ q) → v'.mem (at' S q) = t.mem (at' S q) :=
      fun q hq h₀ h₁ h₂ h₃ h₄ => by
        rw [kL q hq h₀ h₁ h₂ h₃ h₄, kB q (by omega_using [hq]) (by omega_using [h₂]),
          kc q (by omega_using [hq]) (by
            have := Nat.mul_le_mul_right p.n (show 2 ^ (p.a - s p.a) ≤ 2 ^ (p.a - s p.a) + 8 by omega_using [])
            omega_using [h₄, this])]
    -- the signature, from `t` to `v'`
    have dsig : ∀ o l, o + l ≤ (p.a + 1) * p.n → (o + l ≤ p.n + s p.a * p.n ∨ p.n + p.a * p.n ≤ o) →
        bytesAt v'.mem (AU + BitVec.ofNat 64 o) l = bytesAt t.mem (AU + BitVec.ofNat 64 o) l := fun o l h₀ h => by
      have hl : l ≤ 2 ^ 64 := by omega_using [h₀, hAN]
      rw [bytesAt_frame fr (fun r hr => ?_) hl, bytesAt_frame B.frame (fun r hr => ?_) hl,
        bytesAt_frame f₁ (fun r hr => ?_) hl]
      · simp only [List.mem_singleton] at hr; subst hr; exact dXs h₀ (sS (by rw [eN]; omega_using [hUn]))
      · simp only [List.mem_singleton] at hr; subst hr; exact dXs h₀ (sS (by rw [oVar4]; omega_using []))
      · rcases List.mem_append.mp hr with hr | hr
        · exact dXs h₀ (Levels.levelsChanges_low hn32 S (by rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hcnt])
            r hr)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sigD AU (by omega_using [h, has1]) (by omega_using [h₀, hAN]) (by omega_using [han, has1, hAN])
          · rw [hsp₂]; exact C.Gs.sub_left (sigSub C.AU (by omega_using [h₀, hdAn]))
    have hkp₂ : u₁.gpr .r12 = t₀.gpr .r12 := by rw [g₁ _ (by decide), hI.fix.cs _ (by simp [calleeSaved])]
    have hidx₂ : (u₂.gpr .r9).toNat = idx := by
      rw [B.r9, g₁ _ (by decide), hI.fix.cs _ (by simp [calleeSaved]), C.r13, ht idx (by omega_using [C.idx, h2a])]
    rw [hva, hva, hva, B.v6, B.v7, B.v8, hkp₂, ht 3 (by decide), ht _ hV4] at rt
    rw [hva, hva, hva, hva, B.v5, B.v6, B.v7, B.v8, hkp₂, ht 3 (by decide), ht _ hV4, ht 0 (by decide), hidx₂] at au
    -- the subtree roots the heights started from
    have hdv : 2 ^ (s p.a + (p.a - s p.a)) ∣ tt * 2 ^ p.a := by
      rw [Nat.add_sub_cancel' hsa]; exact Nat.dvd_mul_left _ _
    have hL0 : ∀ j < 2 ^ (p.a - s p.a), (nodesAt p u₂.mem (at' S Layout.oN) (2 ^ (p.a - s p.a))).getD j [] =
        node p skSeed pkSeed a16 (t₀.gpr .r12).toNat (tt * 2 ^ p.a / 2 ^ s p.a + j) (s p.a) := fun j hj => by
      have hjn : j * p.n + p.n ≤ 2 ^ (p.a - s p.a) * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
      rw [Levels.getD_nodesAt _ _ hj, Levels.add_add, mul_pow_div tt hsa, ← hI.roots j hj]
      refine bytesAt_ext fun i hi => ?_
      rw [Levels.add_add, Levels.add_add, kB _ (by rw [eN]; omega_using [hjn, hi, hUn]) (.inr (by rw [eN]; omega_using [])),
        show Layout.oN + j * p.n + i = Layout.oN + (j * p.n + i) by omega_using [], c₁ _ (by omega_using [hjn, hi]),
        show Layout.oRoots + (j * p.n + i) = Layout.oRoots + j * p.n + i by omega_using []]
    have hup := up_node p skSeed pkSeed a16 (t₀.gpr .r12).toNat (L := nodesAt p u₂.mem (at' S Layout.oN) (2 ^ (p.a - s p.a)))
      (Levels.length_nodesAt _ _ _) hdv hL0
    simp only [FORS_TREE] at hup
    have hsa' : s p.a + (p.a - s p.a) = p.a := Nat.add_sub_cancel' hsa
    refine fin Layout.oN v' (by rw [eN]; omega_using [hn32]) (.inr (by rw [eN]; omega_using [hn32])) ?_ ev ?_ ?_ ?_ ?_ ?_ ?_
    · have F₁ : Fix t u₁ := ⟨fun r hr => g₁ r (by
          simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), r₁, w₁, by rw [mx₁]⟩
      have F₂ : Fix u₁ u₂ := ⟨fun r hr => by
          simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          B.rd, B.wr, by rw [B.mx]⟩
      exact ((hI.fix.trans F₁).trans F₂).trans fx
    · exact sk_bytes hI.sk fun q h₁ h₂ => kT q (by omega_using [h₂, hn32]) (by omega_using [h₁]) (.inr (by omega_using [h₁]))
        (.inr (by omega_using [h₁])) (fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂, hn32]))
        (.inl (by rw [eN]; omega_using [h₂, hn32]))
    · intro i hi h2 h3
      exact Mem.readW_congr fun j hj => by
        rw [Levels.add_add, oVar2]
        exact kT _ (by omega_using [hi, hj]) (by omega_using []) (.inr (by omega_using [])) (.inl (by omega_using [hi, hj]))
          (fun k hk => .inl (by rw [laneA_eq]; omega_using [hi, hj])) (.inl (by rw [eN]; omega_using [hi, hj]))
    · intro j hj
      have e := dsig j 1 (by omega_using [hj, han]) (.inl (by omega_using [hj]))
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, List.cons.injEq, and_true] at e
      rw [e]; exact hskp j hj
    · intro r hr
      by_cases hrs : r < s p.a
      · have hrn : p.n + r * p.n + p.n ≤ p.n + s p.a * p.n := by
          have := Nat.mul_le_mul_right p.n (show r + 1 ≤ s p.a by omega_using [hrs]); rw [Nat.succ_mul] at this
          omega_using [this]
        rw [Levels.add_add, dsig _ _ (by omega_using [hrn, han, hsn]) (.inl hrn), ← Levels.add_add]
        exact hall r hrs
      · have hr' : r - s p.a < p.a - s p.a := by omega_using [hr, hrs]
        have e₁ : AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n) =
            AU + BitVec.ofNat 64 (p.n + s p.a * p.n) + BitVec.ofNat 64 ((r - s p.a) * p.n) := by
          have hsr : s p.a * p.n ≤ r * p.n := Nat.mul_le_mul_right _ (by omega_using [hrs])
          have hsub : (r - s p.a) * p.n = r * p.n - s p.a * p.n := Nat.sub_mul _ _ _
          rw [Levels.add_add, Levels.add_add, show p.n + s p.a * p.n + (r - s p.a) * p.n = p.n + r * p.n by
            omega_using [hsr, hsub]]
        rw [e₁, au _ hr']
        obtain ⟨hlen, hget⟩ := hup (r - s p.a) (Nat.le_of_lt hr')
        rw [show s p.a + (r - s p.a) = r by omega_using [hrs]] at hget ⊢
        rw [Nat.zero_div, pick_eq hlen (fun x => node p skSeed pkSeed a16 (t₀.gpr .r12).toNat (tt * 2 ^ (p.a - r) + x) r)
          (fun j hj => by rw [hget j hj, mul_pow_div tt (by omega_using [hr]), Nat.zero_add]),
          ite_eq_left ⟨Nat.zero_le _, by
            rw [Nat.zero_add, show p.a - s p.a - (r - s p.a) = p.a - r by omega_using [hrs, hsa]]
            exact sib_lt C.idx hr⟩]
        have hz : bytesAt u₂.mem (AU + BitVec.ofNat 64 (p.n + s p.a * p.n) + BitVec.ofNat 64 ((r - s p.a) * p.n)) p.n =
            toByte 0 p.n := by
          rw [← e₁, ← hI.high r (by omega_using [hrs]) hr]
          have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
            have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [hr]); rw [Nat.succ_mul] at this
            omega_using [this, han]
          have hl : p.n ≤ 2 ^ 64 := by omega_using [hn32]
          rw [Levels.add_add, bytesAt_frame B.frame (fun x hx => by
              simp only [List.mem_singleton] at hx; subst hx; exact dXs hrn (sS (by rw [oVar4]; omega_using []))) hl,
            bytesAt_frame f₁ (fun x hx => by
              simp only [List.mem_singleton] at hx; subst hx; exact dXs hrn (sS (by rw [eN]; omega_using [hUn]))) hl]
        rw [hz, xorB_zero_left (forsNode_length hn32 _ _ _ _ _)]
    · rw [rt]
      have e := (hup (p.a - s p.a) (Nat.le_refl _)).2 0 (by simp)
      rw [hsa', Nat.add_zero, Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at e
      exact e
    · refine hI.frame.trans ((f₁.sub fun x hx => ?_).trans ((B.frame.sub fun x hx => ?_).trans (fr.sub fun x hx => ?_)))
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Offset.sub S (by omega_using [])
          (by rw [show Layout.nodeSlots = 520 from rfl]; omega_using [hUn])⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨⟨at' S (Layout.oFrame 4), 128⟩, by simp, Offset.sub S (by decide) (by decide)⟩
      · rcases List.mem_append.mp hx with hx | hx
        · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
            or_false] at hx
          rcases hx with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
          · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), fun _ h => h⟩
          · exact ⟨_, by simp, fun _ h => h⟩
          · exact ⟨_, by simp, fun _ h => h⟩
          · exact ⟨_, by simp, fun _ h => h⟩
          · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Offset.sub S (by omega_using [])
              (by
                have := Nat.mul_le_mul (show 2 ^ (p.a - s p.a) + 8 ≤ 40 by omega_using [h2U]) hn32
                rw [show Layout.nodeSlots = 520 from rfl]; omega_using [this])⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ⟨⟨AU, (p.a + 1) * p.n⟩, by simp, Offset.sub_base AU (by omega_using [han, has1])⟩
          · rw [hsp₂]; exact ⟨_, by simp, fun _ h => h⟩
  · have e : s p.a = p.a := by omega_using [hc, hsa]
    rw [ite_eq_right hc, show rootOff p.a = Layout.oRoots from ite_eq_right hc]
    refine WP.seq (WP.block_nil ?_)
    have hr0 := hI.roots 0 (Nat.two_pow_pos _)
    rw [e, Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_mul, Nat.add_zero] at hr0
    exact fin Layout.oRoots t (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [hn32])
      (.inr (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [hn32])) hI.fix hI.env hI.sk (fun _ _ _ _ => rfl)
      hskp (fun r hr => hall r (by omega_using [hr, e])) hr0 hI.frame

/-! ## A tree -/

theorem ea_fidx (s : State) {S : Addr} {tt : Nat} (hbx : s.gpr .rbx = S) (hax : s.gpr .rax = BitVec.ofNat 64 tt) :
    s.ea fidx = at' S (Layout.oFidx + 8 * tt) := by
  simp only [State.ea, fidx, fidxR, hbx, hax, ofInt_nat]
  rw [BitVec.ofNat_mul_ofNat, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega_using []

/-- The first block of a tree: its index to `r13`, its signature at `AU` zeroed, variable 2 zeroed. -/
theorem treeA_ok {p : Params} {S AU SG : Addr} {L dA tt idx : Nat} {u : State} (hbx : u.gpr .rbx = S)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) (hwG : (⟨SG, L⟩ : Region) ∈ u.wr) (hAU : AU = SG + BitVec.ofNat 64 dA)
    (hdA : dA + (p.a + 1) * p.n ≤ L) (hGf : SG.toNat + L ≤ 2 ^ 64) (hn8 : p.n % 8 = 0)
    (h0 : u.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) (htt : tt < 40)
    (h1 : u.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (hf : u.mem.readW (at' S (Layout.oFidx + 8 * tt)) 64 = BitVec.ofNat 64 idx)
    (hGd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩) :
    WP isa (.block (([.mov .rax (.mem (var 0)), .mov .r13 (.mem fidx), .mov .rsi (.mem (var 1)), .mov32 .rax (.imm 0)] :
        List Instr) ++ (List.range ((p.a + 1) * (⟨p.n, p.len⟩ : Layout).n / 8)).map
          (fun w => .store (Impl.Sha3.X86_64.at_ .rsi (8 * w)) .rax) ++ ([.store (var 2) .rax] : List Instr))) u fun u' =>
      (∀ g, g ≠ .rax → g ≠ .r13 → g ≠ .rsi → u'.gpr g = u.gpr g) ∧ u'.gpr .r13 = BitVec.ofNat 64 idx ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      (∀ i < (p.a + 1) * p.n, u'.mem (AU + BitVec.ofNat 64 i) = 0) ∧
      u'.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 0 ∧
      Frame [⟨AU, (p.a + 1) * p.n⟩, ⟨at' S (Layout.oVar 2 2), 8⟩] u.mem u'.mem := by
  have e8 : 8 * ((p.a + 1) * p.n / 8) = (p.a + 1) * p.n :=
    Nat.mul_div_cancel' (Nat.dvd_mul_left_of_dvd (by omega_using [hn8]) _)
  refine WP.mono_mx (by simp [Code.allInstrs_eq, instrs, loadsMxcsr]) (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_
    fun _ h hm => h hm
  simp only [List.cons_append, List.nil_append]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 0)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (Levels.in_scr' hw (by rw [oVar2]; omega_using [])) fun u₁ e₁ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oFidx + 8 * tt))
    (ea_fidx u₁ (by rw [e₁.other _ (by decide), hbx]) (by rw [e₁.gpr, h0]))
    (by rw [e₁.rd, e₁.wr]; exact Levels.in_scr' hw (by rw [show Layout.oFidx = 31328 from rfl]; omega_using [htt]))
    fun u₂ e₂ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 1))
    (by rw [var, Proof.Sha3.X86_64.ea_at, e₂.other _ (by decide), e₁.other _ (by decide), hbx])
    (by rw [e₂.rd, e₂.wr, e₁.rd, e₁.wr]; exact Levels.in_scr' hw (by rw [oVar2]; omega_using [])) fun u₃ e₃ => ?_
  refine Proof.Sha3.X86_64.wp_mov32i fun u₄ e₄ => ?_
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have hsi : u₄.gpr .rsi = AU := by rw [e₄.other _ (by decide), e₃.gpr, e₂.mem, e₁.mem, h1]
  have hax : u₄.gpr .rax = 0 := by rw [e₄.gpr]; rfl
  let P : Nat → State → Prop := fun j v => v.gpr = u₄.gpr ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
    (∀ i < 8 * j, v.mem (AU + BitVec.ofNat 64 i) = 0) ∧ Frame [⟨AU, (p.a + 1) * p.n⟩] u.mem v.mem
  refine WP.block_append (WP.mono (Levels.wp_rangeMap (P := P) ((p.a + 1) * p.n / 8)
    ⟨rfl, by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd], by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr], fun _ h => absurd h (by omega_using []),
      hm₄ ▸ Frame.refl _ _⟩ fun j hj v ⟨g, r, w, z, f⟩ => ?_) fun v ⟨g, r, w, z, f⟩ => ?_)
  · have hj8 : 8 * j + 8 ≤ (p.a + 1) * p.n := by omega_using [hj, e8]
    have hc : (⟨SG, L⟩ : Region).Contains (AU + BitVec.ofNat 64 (8 * j)) 8 := by
      rw [hAU, Levels.add_add]
      exact Offset.contains_base SG (by omega_using [hdA, hj8]) (by omega_using [hdA, hj8, hGf])
    refine Proof.Sha3.X86_64.wp_store (a := AU + BitVec.ofNat 64 (8 * j)) (by rw [Proof.Sha3.X86_64.ea_at, g, hsi])
      (by rw [w]; exact ⟨_, hwG, hc⟩) fun v' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rw [m', Levels.byte_write8' _ _ (by omega_using [hj8, hdA, hGf]) (by omega_using [hi, hj8, hdA, hGf])]
      split
      · rw [g, hax]; simp
      · rename_i h; exact z i (by omega_using [hi, h])
    · rw [m']
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base AU (by omega_using [hj8])
        (by omega_using [hj8, hdA, hGf]))
  · rw [e8] at z
    refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 2)) (by rw [var, Proof.Sha3.X86_64.ea_at, g,
        e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hbx])
      (by rw [w]; exact Levels.in_scr hw (by rw [oVar2]; omega_using [])) fun v' g' m' r' w' => WP.block_nil fun hmx => ?_
    have hd : Region.Disjoint ⟨AU, (p.a + 1) * p.n⟩ ⟨at' S (Layout.oVar 2 2), 8⟩ :=
      (hGd.sub_left (by rw [hAU]; exact Offset.sub_base SG hdA)).sub_right
        (Offset.sub_base S (by rw [oVar2, show Layout.oSigTmp = 31648 from rfl]; omega_using []))
    refine ⟨fun g'' h₀ h₁ h₂ => by rw [g', g, e₄.other _ h₀, e₃.other _ h₂, e₂.other _ h₁, e₁.other _ h₀], by
        rw [g', g, e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.mem, hf],
      by rw [r', r], by rw [w', w], hmx, fun i hi => ?_, by rw [m', Mem.readW_writeW_self64, g, hax]; rfl, ?_⟩
    · have fs : Frame [⟨at' S (Layout.oVar 2 2), 8⟩] v.mem v'.mem := by
        rw [m']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      rw [fs.bytes (R := ⟨AU, (p.a + 1) * p.n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
        (show (p.a + 1) * p.n ≤ 2 ^ 64 by omega_using [hdA, hGf]) hi]
      exact z i hi
    · rw [m']
      exact (f.mono fun r hr => by simp at hr; simp [hr]).writeW (r := ⟨at' S (Layout.oVar 2 2), 8⟩) (by simp) _
        (Region.contains_self _ _)

/-- The last block of a tree: the next tree's signature, first leaf and number. -/
theorem treeEnd_ok {S AU : Addr} {D A K V4 tt : Nat} {u : State} (hbx : u.gpr .rbx = S)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) (hD : D < 2 ^ 31) (hA : A < 2 ^ 31) (hK : K < 2 ^ 31)
    (h0 : u.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt)
    (h1 : u.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h4 : u.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4) (htt : tt < 2 ^ 32) :
    WP isa (.block [.mov .rax (.mem (var 1)), .alu .add .rax (.imm (BitVec.ofNat 32 D)), .store (var 1) .rax,
        .mov .rax (.mem (var 4)), .alu .add .rax (.imm (BitVec.ofNat 32 A)), .store (var 4) .rax,
        .mov .rax (.mem (var 0)), .alu .add .rax (.imm 1), .store (var 0) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 K))]) u fun u' =>
      (∀ g, g ≠ .rax → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      u'.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 (tt + 1) ∧
      u'.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU + BitVec.ofNat 64 D ∧
      u'.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 (V4 + A) ∧
      u'.zf = some (decide (tt + 1 = K)) ∧
      Frame [⟨at' S (Layout.oVar 2 0), 16⟩, ⟨at' S (Layout.oVar 2 4), 8⟩] u.mem u'.mem := by
  refine WP.mono_mx (by rfl) (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_ fun _ h hm => h hm
  have sp : ∀ i j, i ≠ j → i < 9 → j < 9 → Mem.Sep (at' S (Layout.oVar 2 i)) (64 / 8) (at' S (Layout.oVar 2 j)) (64 / 8) :=
    fun i j h hi hj => Offset.sep S (by rw [oVar2, oVar2]; omega_using [h]) (by rw [oVar2]; omega_using [hi])
      (by rw [oVar2]; omega_using [hj])
  have inS : ∀ (v : State), v.rd = u.rd → v.wr = u.wr → ∀ i, i < 9 → InRegions (v.rd ++ v.wr) (at' S (Layout.oVar 2 i)) 8 :=
    fun v hr hw' i hi => by rw [hr, hw']; exact Levels.in_scr' hw (by rw [oVar2]; omega_using [hi])
  have inW : ∀ (v : State), v.wr = u.wr → ∀ i, i < 9 → InRegions v.wr (at' S (Layout.oVar 2 i)) 8 :=
    fun v hw' i hi => by rw [hw']; exact Levels.in_scr hw (by rw [oVar2]; omega_using [hi])
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (inS u rfl rfl 1 (by decide)) fun u₁ e₁ => Proof.Sha3.X86_64.wp_addi fun u₂ e₂ => ?_
  have hb₂ : u₂.gpr .rbx = S := by rw [e₂.other _ (by decide), e₁.other _ (by decide), hbx]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, hb₂])
    (inW _ (by rw [e₂.wr, e₁.wr]) 1 (by decide)) fun u₃ g₃ m₃ r₃ w₃ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 4)) (by rw [var, Proof.Sha3.X86_64.ea_at, g₃, hb₂])
    (inS _ (by rw [r₃, e₂.rd, e₁.rd]) (by rw [w₃, e₂.wr, e₁.wr]) 4 (by decide)) fun u₄ e₄ =>
    Proof.Sha3.X86_64.wp_addi fun u₅ e₅ => ?_
  have hb₅ : u₅.gpr .rbx = S := by rw [e₅.other _ (by decide), e₄.other _ (by decide), g₃, hb₂]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 4)) (by rw [var, Proof.Sha3.X86_64.ea_at, hb₅])
    (inW _ (by rw [e₅.wr, e₄.wr, w₃, e₂.wr, e₁.wr]) 4 (by decide)) fun u₆ g₆ m₆ r₆ w₆ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 0)) (by rw [var, Proof.Sha3.X86_64.ea_at, g₆, hb₅])
    (inS _ (by rw [r₆, e₅.rd, e₄.rd, r₃, e₂.rd, e₁.rd]) (by rw [w₆, e₅.wr, e₄.wr, w₃, e₂.wr, e₁.wr]) 0 (by decide))
    fun u₇ e₇ => Proof.Sha3.X86_64.wp_addi fun u₈ e₈ => ?_
  have hb₈ : u₈.gpr .rbx = S := by rw [e₈.other _ (by decide), e₇.other _ (by decide), g₆, hb₅]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 0)) (by rw [var, Proof.Sha3.X86_64.ea_at, hb₈])
    (inW _ (by rw [e₈.wr, e₇.wr, w₆, e₅.wr, e₄.wr, w₃, e₂.wr, e₁.wr]) 0 (by decide)) fun u₉ g₉ m₉ r₉ w₉ => ?_
  refine Levels.wp_cmpi fun u' g' m' r' w' z' => WP.block_nil fun hmx => ?_
  have a1 : u₂.gpr .rax = AU + BitVec.ofNat 64 D := by rw [e₂.gpr, e₁.gpr, h1, Levels.sx_ofNat hD]
  have a4 : u₅.gpr .rax = BitVec.ofNat 64 (V4 + A) := by
    rw [e₅.gpr, e₄.gpr, m₃, Mem.readW_writeW_sep (sp 4 1 (by decide) (by decide) (by decide)) (by decide), e₂.mem, e₁.mem,
      h4, Levels.sx_ofNat hA, BitVec.ofNat_add_ofNat]
  have a0 : u₈.gpr .rax = BitVec.ofNat 64 (tt + 1) := by
    rw [e₈.gpr, e₇.gpr, m₆, Mem.readW_writeW_sep (sp 0 4 (by decide) (by decide) (by decide)) (by decide), e₅.mem, e₄.mem, m₃,
      Mem.readW_writeW_sep (sp 0 1 (by decide) (by decide) (by decide)) (by decide), e₂.mem, e₁.mem, h0,
      show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add_ofNat]
  refine ⟨fun g h => by rw [g', g₉, e₈.other _ h, e₇.other _ h, g₆, e₅.other _ h, e₄.other _ h, g₃, e₂.other _ h, e₁.other _ h],
    by rw [r', r₉, e₈.rd, e₇.rd, r₆, e₅.rd, e₄.rd, r₃, e₂.rd, e₁.rd],
    by rw [w', w₉, e₈.wr, e₇.wr, w₆, e₅.wr, e₄.wr, w₃, e₂.wr, e₁.wr], hmx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m', m₉, Mem.readW_writeW_self64, a0]
  · rw [m', m₉, Mem.readW_writeW_sep (sp 1 0 (by decide) (by decide) (by decide)) (by decide), e₈.mem, e₇.mem, m₆,
      Mem.readW_writeW_sep (sp 1 4 (by decide) (by decide) (by decide)) (by decide), e₅.mem, e₄.mem, m₃,
      Mem.readW_writeW_self64, a1]
  · rw [m', m₉, Mem.readW_writeW_sep (sp 4 0 (by decide) (by decide) (by decide)) (by decide), e₈.mem, e₇.mem, m₆,
      Mem.readW_writeW_self64, a4]
  · rw [z', g₉, a0, Levels.sx_ofNat hK, Fors.zf_eq (by omega_using [htt]) (by omega_using [hK])]
  · have c : ∀ i, i < 2 → (⟨at' S (Layout.oVar 2 0), 16⟩ : Region).Contains (at' S (Layout.oVar 2 i)) (64 / 8) := fun i hi => by
      rw [show at' S (Layout.oVar 2 i) = at' S (Layout.oVar 2 0) + BitVec.ofNat 64 (8 * i) by
        rw [Levels.add_add, oVar2, oVar2]]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    rw [m', m₉, e₈.mem, e₇.mem, m₆, e₅.mem, e₄.mem, m₃, e₂.mem, e₁.mem]
    exact (((Frame.refl [⟨at' S (Layout.oVar 2 0), 16⟩, ⟨at' S (Layout.oVar 2 4), 8⟩] u.mem).writeW
      (List.mem_cons_self ..) _ (c 1 (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _
      (c 0 (by decide))

end VG.Proof.SlhDsa.X86_64.Fors
