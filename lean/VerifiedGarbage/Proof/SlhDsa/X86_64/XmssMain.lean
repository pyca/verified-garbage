module

-- separate module: the correctness of `xmssTree`, rebuilt without its constant-time proof's taint checks

public import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssLeaves
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect

/-!
# SLH-DSA (SHAKE) on x86-64: `xmssTree`, the whole function

After the leaves (`XmssLeaves.lean`): the authentication path zeroed and
`levels`'s parameters set (`hblock_ok`), the call of `levels` on the
`2^h′` leaves (`heights_ok`), the root copied to `oMsg` and the
callee-saved registers restored (`xmss_wp`), and so `xmssContract`'s
postcondition (`xmss_correct`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.XmssTree

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add in_scr in_scr' at_add wp_cmpi)

variable {p : Params}

/-- `mov r64, imm32`, which sign-extends. -/
theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem setWidth_ofNat32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).setWidth 64 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- The stores of zeros from `r10 = AU`, `w` words of the buffer `⟨sig, X⟩`. -/
theorem zero_ok {sig AU : Addr} {X d w : Nat} {t₀ : State} (hAU : AU = sig + BitVec.ofNat 64 d)
    (h10 : t₀.gpr .r10 = AU) (hax : t₀.gpr .rax = 0) (hw : (⟨sig, X⟩ : Region) ∈ t₀.wr) (hX : d + 8 * w ≤ X)
    (hf : sig.toNat + X ≤ 2 ^ 64) :
    WP isa (.block ((List.range w).map fun i => Instr.store (Impl.Sha3.X86_64.at_ .r10 (8 * i)) .rax)) t₀
      fun t => t.gpr = t₀.gpr ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr ∧ (∀ i < 8 * w, t.mem (AU + BitVec.ofNat 64 i) = 0) ∧
        Frame [⟨AU, 8 * w⟩] t₀.mem t.mem := by
  refine WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = t₀.gpr ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr ∧
      (∀ i < 8 * j, t.mem (AU + BitVec.ofNat 64 i) = 0) ∧ Frame [⟨AU, 8 * w⟩] t₀.mem t.mem) w
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, wr, z, f⟩ => ?_) fun _ h => h
  have hX' : (8 * j + 8) ≤ 8 * w := by omega
  refine wp_store (a := AU + BitVec.ofNat 64 (8 * j)) (by rw [ea_at, g, h10]) (by
      rw [wr]
      refine ⟨_, hw, ?_⟩
      rw [hAU, add_add]
      exact Offset.contains_base sig (by omega) (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
  refine ⟨by rw [g', g], by rw [r', r], by rw [w', wr], fun i hi => ?_, ?_⟩
  · rw [m', Levels.byte_write8' _ _ (by omega) (by omega)]
    split
    · rw [g, hax]; simp
    · exact z i (by omega)
  · rw [m']
    exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base AU (by omega) (by omega))

/-- `levels`'s precondition at a call from `v`: the `2^h′` leaves at `oN`,
the authentication path at `AU`. -/
theorem levels_pre (hn : Levels.Ns p.n) (hhp : 1 ≤ p.hp) (hhp9 : p.hp ≤ 9) {stack stk : Nat}
    (hst : stk + 8 ≤ stack) (hs : stack < 2 ^ 63) {σ v : State} {S sig AU : Addr} {X d : Nat}
    (hR : Regions stack σ S [] ⟨sig, X⟩) (hAU : AU = sig + BitVec.ofNat 64 d) (hX : d + p.hp * p.n ≤ X)
    (h1 : v.gpr .rdi = S) (h2 : v.gpr .rsi = at' S Layout.oN) (h3 : v.gpr .rdx = BitVec.ofNat 64 (2 ^ p.hp))
    (h4 : v.gpr .rcx = 0) (h5 : v.gpr .r8 = AU) (h6 : (v.gpr .r9).toNat < 2 ^ 32)
    (hsp : v.gpr .rsp = σ.gpr .rsp) (hwr : v.wr = σ.wr) {pk a : List Byte} (he : Env p v.mem S pk a)
    (hv : ∀ i, 5 ≤ i → i ≤ 8 → (varAt v.mem S 4 i).toNat < 2 ^ 32) :
    (levelsContract p stk).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) ∧
      Covers ([] ++ [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) (v.rd ++ v.wr) ∧
      Covers [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩] v.wr := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hg : ∀ r, r ≠ .rsp → (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr r = v.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have h8 : (below (v.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hsp]; exact hR.stk_scr.sub_left (below_sub (by omega) (by omega))
  have h512 : 2 ^ p.hp ≤ 512 := by
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have h2h : (BitVec.ofNat 64 (2 ^ p.hp)).toNat = 2 ^ p.hp := by rw [BitVec.toNat_ofNat]; omega
  have hlog : heightsOf (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) = p.hp := by
    simp only [heightsOf]; rw [hg _ (by decide), h3, h2h, Nat.log2_two_pow]
  have hsub : Region.Sub ⟨AU, p.hp * p.n⟩ ⟨sig, X⟩ := by rw [hAU]; exact Offset.sub_base sig hX
  have hcov : Covers [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩] v.wr := Covers.of_sub fun r hr => by
    rw [hwr, hR.wr_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., 0, Levels.scr0 S, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), d, hAU, hX⟩
  have hvm : ∀ i, i < 8 * 9 → varAt (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).mem
      ((v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]).gpr .rdi) 4 i = varAt v.mem S 4 i := by
    intro i hi
    simp only [varAt]
    rw [hg _ (by decide), h1, State.withRegions_mem]
    refine Thash4Avx.readW_frame (frame_callEntry v) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (h8.sub_right (Levels.sub_scr S (by rw [show Layout.oVar 4 i = 2960 + 8 * i from rfl]; omega))).symm
  refine ⟨⟨?_, ⟨pk, a, ?_⟩, .inl (by rw [hg _ (by decide), hg _ (by decide), h1, h2]), by rw [hlog]; exact hhp,
    by rw [hlog, hg _ (by decide), h4]; simp; omega, by rw [hlog, hg _ (by decide), h3, h2h],
    fun _ => by rw [hg _ (by decide), h3, h2h, show Layout.nodeSlots = 520 from rfl]
                have := Nat.mul_le_mul (show 2 ^ p.hp + 8 ≤ 520 by omega) hn32; omega,
    fun e => ?_, by rw [hg _ (by decide)]; exact h6, by rw [hvm 5 (by decide)]; exact hv 5 (by decide) (by decide),
    by rw [hvm 6 (by decide)]; exact hv 6 (by decide) (by decide), by rw [hvm 7 (by decide)]; exact hv 7 (by decide) (by decide),
    by rw [hvm 8 (by decide)]; exact hv 8 (by decide) (by decide)⟩,
    by rw [List.nil_append]; exact Covers.right hcov, hcov⟩
  · rw [hg _ (by decide), hg _ (by decide), h1, h5, hlog]
    exact regions_call hR hsub (by
      have := hR.out_fit
      have h16 : 1 ≤ p.hp * p.n := Nat.mul_pos hhp (by omega_using [hn])
      simp only at this ⊢
      rw [hAU]; show (at' sig d).toNat + _ ≤ _; rw [Levels.toNat_at (by omega)]; omega) hsp hst (by omega)
  · rw [hg _ (by decide), h1, State.withRegions_mem]
    exact Env.of_frame hn32 he ((frame_callEntry v).mono fun r hr => List.mem_append_right _ hr) h8
  · rw [hg _ (by decide), hg _ (by decide), h1, h2] at e
    exact absurd e (Offset.add_ofNat_ne S (by decide) (by decide) (by decide))

/-- The heights block, as `heights` has it. -/
abbrev hbCode (L : Layout) (hp : Nat) : List Instr :=
  [.mov .r10 (.reg .r13), .alu .add .r10 (.imm (BitVec.ofNat 32 (L.len * L.n))), .mov32 .rax (.imm 0)] ++
    (List.range (hp * L.n / 8)).map (fun w => .store (Impl.Sha3.X86_64.at_ .r10 (8 * w)) .rax) ++
    Impl.SlhDsa.X86_64.Tree.setParams (.imm 0) (.imm 0) (.imm 2) (.imm 0) ++
    [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ hp))), .mov32 .rcx (.imm 0), .mov .r8 (.reg .r10),
      .mov .r9 (.reg .r12)]

theorem heights_nm (L : Layout) (hp : Nat) :
    (Code.block (hbCode L hp) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp [hbCode, Code.allInstrs_eq, instrs, Impl.SlhDsa.X86_64.Tree.setParams, loadsMxcsr]

/-- After the heights block, before the call of `levels`. -/
structure HB (p : Params) (u v : State) (S AU : Addr) : Prop where
  rdi : v.gpr .rdi = S
  rsi : v.gpr .rsi = at' S Layout.oN
  rdx : v.gpr .rdx = BitVec.ofNat 64 (2 ^ p.hp)
  rcx : v.gpr .rcx = 0
  r8 : v.gpr .r8 = AU
  r9 : v.gpr .r9 = u.gpr .r12
  other : ∀ g, g ≠ .rax → g ≠ .r10 → g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → g ≠ .r9 →
    v.gpr g = u.gpr g
  rd : v.rd = u.rd
  wr : v.wr = u.wr
  mx : v.mxcsr = u.mxcsr
  zero : ∀ i < p.hp * p.n, v.mem (AU + BitVec.ofNat 64 i) = 0
  vars : ∀ i, 5 ≤ i → i ≤ 8 → varAt v.mem S 4 i = if i = 7 then 2 else 0
  frame : Frame [⟨AU, p.hp * p.n⟩, ⟨at' S (Layout.oVar 4 5), 32⟩] u.mem v.mem

/-- The heights block: the authentication path zeroed, `levels`'s parameters
and arguments. -/
theorem hblock_ok (hz : Wots4.Sz p) (hhp9 : p.hp ≤ 9) {u : State} {S sig : Addr}
    (hbx : u.gpr .rbx = S) (h13 : u.gpr .r13 = sig) (hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr)
    (hws : (⟨sig, p.xmssSigLen⟩ : Region) ∈ u.wr) (hf : sig.toNat + p.xmssSigLen ≤ 2 ^ 64)
    (hAd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩) {Q : State → Prop}
    (k : ∀ v, HB p u v S (sig + BitVec.ofNat 64 (p.len * p.n)) → Q v) :
    WP isa (.block (hbCode (Wots4.L p) p.hp)) u Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hl := hz.len
  have hln : p.len * p.n ≤ 2144 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have h512 : 2 ^ p.hp ≤ 512 := by
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hw8 : 8 * (p.hp * p.n / 8) = p.hp * p.n := by
    have : p.hp * p.n % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.mul_zero]
    omega
  have eV : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  refine WP.mono_mx (heights_nm (Wots4.L p) p.hp) (Q := fun v => v.mxcsr = u.mxcsr → Q v) ?_ fun _ h hm => h hm
  simp only [hbCode, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun t₁ e₁ => wp_addi fun t₂ e₂ => wp_mov32i fun t₃ e₃ => ?_
  have h10 : t₃.gpr .r10 = sig + BitVec.ofNat 64 (p.len * p.n) := by
    rw [e₃.other _ (by decide), e₂.gpr, e₁.gpr, h13, sx_ofNat (by omega)]
  have hax : t₃.gpr .rax = 0 := by rw [e₃.gpr]; decide
  have hm₃ : t₃.mem = u.mem := by rw [e₃.mem, e₂.mem, e₁.mem]
  have hw₃ : t₃.wr = u.wr := by rw [e₃.wr, e₂.wr, e₁.wr]
  have hd₃ : t₃.rd = u.rd := by rw [e₃.rd, e₂.rd, e₁.rd]
  have hg₃ : ∀ g, g ≠ .rax → g ≠ .r10 → t₃.gpr g = u.gpr g := fun g h₁ h₂ => by
    rw [e₃.other _ h₁, e₂.other _ h₂, e₁.other _ h₂]
  have hX : p.len * p.n + 8 * (p.hp * p.n / 8) ≤ p.xmssSigLen := by
    rw [hw8]; simp only [Params.xmssSigLen, Nat.add_mul]; omega
  refine WP.block_append (WP.mono (zero_ok rfl h10 hax (by rw [hw₃]; exact hws) hX hf)
    fun t₄ ⟨g₄, r₄, w₄, z₄, f₄⟩ => ?_)
  rw [hw8] at z₄ f₄
  have hbx₄ : t₄.gpr .rbx = S := by rw [g₄, hg₃ _ (by decide) (by decide), hbx]
  have hwS₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₄.wr := by rw [w₄, hw₃]; exact hwS
  simp only [Impl.SlhDsa.X86_64.Tree.setParams, List.cons_append, List.nil_append]
  refine wp_movi fun t₅ e₅ => wp_store (a := at' S (Layout.oVar 4 5))
    (by rw [Impl.SlhDsa.X86_64.Tree.var, ea_at, e₅.other _ (by decide), hbx₄]) (by
      rw [e₅.wr]; exact in_scr hwS₄ (by rw [eV]; omega)) fun t₆ g₆ m₆ r₆ w₆ => ?_
  refine wp_movi fun t₇ e₇ => wp_store (a := at' S (Layout.oVar 4 6))
    (by rw [Impl.SlhDsa.X86_64.Tree.var, ea_at, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hbx₄]) (by
      rw [e₇.wr, w₆, e₅.wr]; exact in_scr hwS₄ (by rw [eV]; omega)) fun t₈ g₈ m₈ r₈ w₈ => ?_
  refine wp_movi fun t₉ e₉ => wp_store (a := at' S (Layout.oVar 4 7))
    (by rw [Impl.SlhDsa.X86_64.Tree.var, ea_at, e₉.other _ (by decide), g₈, e₇.other _ (by decide), g₆,
      e₅.other _ (by decide), hbx₄]) (by
      rw [e₉.wr, w₈, e₇.wr, w₆, e₅.wr]; exact in_scr hwS₄ (by rw [eV]; omega)) fun t₁₀ g₁₀ m₁₀ r₁₀ w₁₀ => ?_
  refine wp_movi fun t₁₁ e₁₁ => wp_store (a := at' S (Layout.oVar 4 8))
    (by rw [Impl.SlhDsa.X86_64.Tree.var, ea_at, e₁₁.other _ (by decide), g₁₀, e₉.other _ (by decide), g₈,
      e₇.other _ (by decide), g₆, e₅.other _ (by decide), hbx₄]) (by
      rw [e₁₁.wr, w₁₀, e₉.wr, w₈, e₇.wr, w₆, e₅.wr]; exact in_scr hwS₄ (by rw [eV]; omega))
    fun t₁₂ g₁₂ m₁₂ r₁₂ w₁₂ => ?_
  -- the registers and memory after `setParams`
  have hg₁₂ : ∀ g, g ≠ .rax → t₁₂.gpr g = t₄.gpr g := fun g h => by
    rw [g₁₂, e₁₁.other _ h, g₁₀, e₉.other _ h, g₈, e₇.other _ h, g₆, e₅.other _ h]
  have hm₁₂ : t₁₂.mem = (((t₄.mem.writeW (at' S (Layout.oVar 4 5)) (0 : BitVec 64)).writeW
      (at' S (Layout.oVar 4 6)) (0 : BitVec 64)).writeW (at' S (Layout.oVar 4 7)) (2 : BitVec 64)).writeW
      (at' S (Layout.oVar 4 8)) (0 : BitVec 64) := by
    rw [m₁₂, e₁₁.gpr, e₁₁.mem, m₁₀, e₉.gpr, e₉.mem, m₈, e₇.gpr, e₇.mem, m₆, e₅.gpr, e₅.mem]; rfl
  have hc : ∀ i, 5 ≤ i → i ≤ 8 → (⟨at' S (Layout.oVar 4 5), 32⟩ : Region).Contains (at' S (Layout.oVar 4 i)) (64 / 8) :=
    fun i h₁ h₂ => Offset.contains S (by rw [eV, eV]; omega) (by rw [eV, eV]; omega) (by rw [eV]; omega)
  have hfp : Frame [⟨at' S (Layout.oVar 4 5), 32⟩] t₄.mem t₁₂.mem := by
    rw [hm₁₂]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 5 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 6 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (hc 7 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (hc 8 (by decide) (by decide))
  have hsep : ∀ i j, 5 ≤ i → i ≤ 8 → 5 ≤ j → j ≤ 8 → i ≠ j →
      Mem.Sep (at' S (Layout.oVar 4 i)) (64 / 8) (at' S (Layout.oVar 4 j)) (64 / 8) := fun i j h₁ h₂ h₃ h₄ h₅ =>
    Offset.sep S (by rw [eV, eV]; omega) (by rw [eV]; omega) (by rw [eV]; omega)
  refine wp_mov fun t₁₃ e₁₃ => wp_mov fun t₁₄ e₁₄ => wp_addi fun t₁₅ e₁₅ => wp_mov32i fun t₁₆ e₁₆ =>
    wp_mov32i fun t₁₇ e₁₇ => wp_mov fun t₁₈ e₁₈ => wp_mov fun t₁₉ e₁₉ => WP.block_nil fun hmx => k t₁₉ ?_
  have hm₁₉ : t₁₉.mem = t₁₂.mem := by rw [e₁₉.mem, e₁₈.mem, e₁₇.mem, e₁₆.mem, e₁₅.mem, e₁₄.mem, e₁₃.mem]
  have hS₁₂ : t₁₂.gpr .rbx = S := by rw [hg₁₂ _ (by decide), hbx₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun g h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => ?_, ?_, ?_, hmx, fun i hi => ?_, fun i h₁ h₂ => ?_, ?_⟩
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide),
      e₁₅.other _ (by decide), e₁₄.other _ (by decide), e₁₃.gpr, hS₁₂]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide),
      e₁₅.gpr, e₁₄.gpr, e₁₃.other _ (by decide), hS₁₂, sx_ofNat (by decide)]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.gpr,
      setWidth_ofNat32 (by omega)]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.gpr]; decide
  · rw [e₁₉.other _ (by decide), e₁₈.gpr, e₁₇.other _ (by decide), e₁₆.other _ (by decide), e₁₅.other _ (by decide),
      e₁₄.other _ (by decide), e₁₃.other _ (by decide), hg₁₂ _ (by decide), g₄, h10]
  · rw [e₁₉.gpr, e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide), e₁₅.other _ (by decide),
      e₁₄.other _ (by decide), e₁₃.other _ (by decide), hg₁₂ _ (by decide), g₄, hg₃ _ (by decide) (by decide)]
  · rw [e₁₉.other _ h₈, e₁₈.other _ h₇, e₁₇.other _ h₆, e₁₆.other _ h₅, e₁₅.other _ h₄, e₁₄.other _ h₄,
      e₁₃.other _ h₃, hg₁₂ _ h₁, g₄, hg₃ _ h₁ h₂]
  · rw [e₁₉.rd, e₁₈.rd, e₁₇.rd, e₁₆.rd, e₁₅.rd, e₁₄.rd, e₁₃.rd, r₁₂, e₁₁.rd, r₁₀, e₉.rd, r₈, e₇.rd, r₆, e₅.rd, r₄, hd₃]
  · rw [e₁₉.wr, e₁₈.wr, e₁₇.wr, e₁₆.wr, e₁₅.wr, e₁₄.wr, e₁₃.wr, w₁₂, e₁₁.wr, w₁₀, e₉.wr, w₈, e₇.wr, w₆, e₅.wr, w₄, hw₃]
  · rw [hm₁₉, hfp _ fun r hr => ?_]
    · exact z₄ i hi
    simp only [List.mem_singleton] at hr; subst hr
    refine fun hcon => ?_
    have hA : (⟨sig, p.xmssSigLen⟩ : Region).Contains (sig + BitVec.ofNat 64 (p.len * p.n) + BitVec.ofNat 64 i) 1 := by
      rw [add_add]; exact Offset.contains_base sig (by simp only [Params.xmssSigLen, Nat.add_mul]; omega) (by omega)
    exact hAd _ hA (Offset.sub_base S (by rw [eV, show Layout.oSigTmp = 31648 from rfl]; omega) _ hcon)
  · simp only [varAt]
    rw [hm₁₉, hm₁₂]
    rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega) with rfl | rfl | rfl | rfl
    · rw [Mem.readW_writeW_sep (hsep 5 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (hsep 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (hsep 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_sep (hsep 6 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (hsep 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_sep (hsep 7 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_self64]; rfl
  · rw [hm₁₉, ← hm₃]
    exact (f₄.mono fun r hr => by simp at hr ⊢; simp [hr]).trans (hfp.mono fun r hr => by simp at hr ⊢; simp [hr])

/-- `Env` across a frame whose regions keep the round constants and the
lanes' `PK.seed` and `a16`. -/
theorem env_frame (hn32 : p.n ≤ 32) {m m' : Mem} {S : Addr} {pk a : List Byte} {rs : List Region}
    (he : Env p m S pk a) (hf : Frame rs m m')
    (hd : ∀ {o l : Nat}, ((1600 ≤ o ∧ o + l ≤ 2368) ∨ (3296 ≤ o ∧ o + l ≤ 12640)) →
      ∀ r ∈ rs, Region.Disjoint ⟨at' S o, l⟩ r) : Env p m' S pk a := by
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have hA : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt m' (at' S (Layout.laneA k + o)) l = bytesAt m (at' S (Layout.laneA k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (hd (.inr ⟨by rw [hLA]; omega, by rw [hLA]; omega⟩)) (by omega)
  have hB : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt m' (at' S (Layout.laneB k + o)) l = bytesAt m (at' S (Layout.laneB k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (hd (.inr ⟨by rw [hLB]; omega, by rw [hLB]; omega⟩)) (by omega)
  refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [← he.rc r hr k hk]
    exact Thash4Avx.readW_frame hf (hd (.inl ⟨by omega, by omega⟩))
  · rw [← he.seedA k hk, ← Nat.add_zero (Layout.laneA k), hA k hk 0 p.n (by omega)]
  · rw [← he.seedB k hk, ← Nat.add_zero (Layout.laneB k), hB k hk 0 p.n (by omega)]
  · rw [← he.adrsA k hk, hA k hk p.n 16 (by omega)]
  · rw [← he.adrsB k hk, hB k hk p.n 16 (by omega)]

/-- The saved registers of frame 1, which the heights keep. -/
theorem hu_disj (hn32 : p.n ≤ 32) {S sig sp AU : Addr} {o l c stk X d : Nat}
    (hsig : Region.Disjoint ⟨sig, X⟩ ⟨S, Layout.oSigTmp⟩) (hAU : AU = sig + BitVec.ofNat 64 d)
    (hAX : d + p.hp * p.n ≤ X) (hstk : (below sp stk).Disjoint ⟨S, 2 ^ 16⟩)
    (hc : Layout.oN + (c + 8) * p.n ≤ 2 ^ 16) (ho : 2528 ≤ o ∧ o + l ≤ 2912) :
    ∀ r ∈ levelsChanges p S (at' S Layout.oN) c ++ [⟨AU, p.hp * p.n⟩, below sp stk, ⟨at' S (Layout.oVar 4 5), 32⟩],
      Region.Disjoint ⟨at' S o, l⟩ r := by
  have eN : Layout.oN = 12640 := rfl
  intro r hr
  simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with (⟨k, hk, rfl⟩ | (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl)
  · exact Levels.disj_scr S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · have h : Region.Disjoint ⟨at' S o, l⟩ ⟨S + BitVec.ofNat 64 0, 1600⟩ :=
      Levels.disj_scr S (o' := 0) (by omega) (by omega) (by omega)
    rwa [← Levels.scr0 S] at h
  · exact Levels.disj_scr S (by omega) (by omega) (by omega)
  · exact Levels.disj_scr S (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega) (by omega)
      (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega)
  · exact Levels.disj_scr S (by omega) (by omega) hc
  · rw [hAU]
    exact ((hsig.sub_left (Offset.sub_base sig hAX)).sub_right
      (Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; omega))).symm
  · exact (hstk.sub_right (Offset.sub_base S (by omega))).symm
  · exact Levels.disj_scr S (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega) (by omega)
      (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega)

/-- After the heights. -/
structure HPost (p : Params) (stack : Nat) (σ : State) (S sig : Addr) (pk a sk M : List Byte) (w : State) : Prop where
  bx : w.gpr .rbx = S
  r15 : w.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg
  sp : w.gpr .rsp = σ.gpr .rsp
  rd : w.rd = σ.rd
  wr : w.wr = σ.wr
  mx : w.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10
  env : Env p w.mem S pk a
  saved : ∀ i < 6, w.mem.readW (at' S (Layout.oSave 1 i)) 64 = σ.gpr (savedRegs.getD i .rbx)
  root : bytesAt w.mem (at' S Layout.oN) p.n = xmssNode p sk 0 p.hp pk (treeAdrs a)
  xsig : (σ.gpr .rsi).toNat < 2 ^ p.hp →
    bytesAt w.mem sig p.xmssSigLen = xmssSign p M sk (σ.gpr .rsi).toNat pk (treeAdrs a)
  frame : Frame (changes p S ++ [⟨sig, p.xmssSigLen⟩, below (σ.gpr .rsp) stack]) σ.mem w.mem

/-- The heights: the call of `levels` on the leaves. -/
theorem heights_ok (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9)
    {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions stack σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .rsi).toNat < 2 ^ 32)
    {u : State} (hI : LInv p stack σ S sig pk a sk M (2 ^ (p.hp - 2)) u) :
    WP isa (Impl.SlhDsa.X86_64.Xmss.heights (Wots4.L p) p.hp t4name ln T.code) u
      (HPost p stack σ S sig pk a sk M) := by
  have hn32 := hz.n32
  have hl := hz.len
  have hln : p.len * p.n ≤ 2144 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have h512 : 2 ^ p.hp ≤ 512 := by
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have h4 : 4 * 2 ^ (p.hp - 2) = 2 ^ p.hp := by
    rw [show p.hp = p.hp - 2 + 2 by omega, Nat.pow_add, Nat.add_sub_cancel]; omega
  have ha : a.length = 16 := by rw [← hI.env.adrsA 0 (by decide)]; simp [bytesAt]
  have eN : Layout.oN = 12640 := rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have eSv : ∀ i, Layout.oSave 1 i = 2528 + 8 * i := fun _ => rfl
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have hws : (⟨sig, p.xmssSigLen⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp
  have hsigd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  have hstk : ∀ k ≤ stack, (below (σ.gpr .rsp) k).Disjoint ⟨S, 2 ^ 16⟩ := fun k hk =>
    hR.stk_scr.sub_left (below_sub hk (by omega))
  have hSL : p.xmssSigLen = p.len * p.n + p.hp * p.n := by simp only [Params.xmssSigLen, Nat.add_mul]
  have hcap : (2 ^ p.hp + 8) * p.n ≤ 16640 := by have := Nat.mul_le_mul (show 2 ^ p.hp + 8 ≤ 520 by omega) hn32; omega
  have hpn : p.hp * p.n ≤ 288 := Nat.mul_le_mul hhp9 hn32
  obtain ⟨AU, hAU⟩ : ∃ AU, AU = sig + BitVec.ofNat 64 (p.len * p.n) := ⟨_, rfl⟩
  unfold Impl.SlhDsa.X86_64.Xmss.heights
  refine WP.seq (hblock_ok hz hhp9 hI.bx hI.r13 (by rw [hI.wr]; exact hwS) (by rw [hI.wr]; exact hws) hR.out_fit
    hsigd fun v hv => ?_)
  rw [← hAU] at hv
  have hsp : v.gpr .rsp = σ.gpr .rsp := by
    rw [hv.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hI.sp]
  have hvenv : Env p v.mem S pk a := env_frame hn32 hI.env hv.frame fun {o l} ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hAU]
      exact ((hsigd.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S (by omega))).symm
    · exact Levels.disj_scr S (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega) (by omega)
        (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega)
  obtain ⟨hpre, hc, hw⟩ := levels_pre hz.nv (by omega) hhp9 (stk := T.stack + 16) (by omega) hs63 hR hAU
    (by rw [hSL]) hv.rdi hv.rsi hv.rdx hv.rcx hv.r8 (by rw [hv.r9, hI.r12]; exact hidx) hsp
    (by rw [hv.wr, hI.wr]) hvenv fun i h₁ h₂ => by rw [hv.vars i h₁ h₂]; split <;> decide
  refine Levels.levelscall_ok T t4name ln hz.nv hz.shake (Nat.le_refl _) (by omega) hpre hc hw
    fun s' h₁ h₂ h₃ h₄ ⟨s₂, hm₂, _, hpost⟩ h₆ => ?_
  generalize hE : v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩] = E at hpost
  have hEg : ∀ r, r ≠ .rsp → E.gpr r = v.gpr r := fun r h => by
    rw [← hE, State.withRegions_gpr, State.callEntry_gpr _ h]
  have hEm : E.mem = v.callEntry.mem := by rw [← hE]; rfl
  have hEsp : E.gpr .rsp = σ.gpr .rsp - 8 := by rw [← hE, State.withRegions_gpr, State.callEntry_rsp, hsp]
  have h8 : (below (v.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by rw [hsp]; exact hstk 8 (by omega)
  have hcm : Frame [below (σ.gpr .rsp) 8] v.mem E.mem := by rw [hEm, ← hsp]; exact frame_callEntry v
  have hEnv : Env p E.mem S pk a := by
    rw [hEm]; exact Env.of_frame hn32 hvenv ((frame_callEntry v).mono fun r hr => List.mem_append_right _ hr) h8
  have h2h : (BitVec.ofNat 64 (2 ^ p.hp)).toNat = 2 ^ p.hp := by rw [BitVec.toNat_ofNat]; omega
  have hlog : heightsOf E = p.hp := by
    simp only [heightsOf]; rw [hEg _ (by decide), hv.rdx, h2h, Nat.log2_two_pow]
  have hvarE : ∀ i, 5 ≤ i → i ≤ 8 → varAt E.mem S 4 i = if i = 7 then 2 else 0 := fun i h₁ h₂ => by
    rw [← hv.vars i h₁ h₂]
    simp only [varAt]
    refine Thash4Avx.readW_frame hcm fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hstk 8 (by omega)).sub_right (Levels.sub_scr S (by rw [show Layout.oVar 4 i = 2960 + 8 * i from rfl]; omega))).symm
  simp only [levelsContract] at hpost
  have hE1 : E.gpr .rdi = S := by rw [hEg _ (by decide), hv.rdi]
  have hE2 : E.gpr .rsi = at' S Layout.oN := by rw [hEg _ (by decide), hv.rsi]
  have hE3 : (E.gpr .rdx).toNat = 2 ^ p.hp := by rw [hEg _ (by decide), hv.rdx, h2h]
  have hE4 : (E.gpr .rcx).toNat = 0 := by rw [hEg _ (by decide), hv.rcx]; rfl
  have hE5 : E.gpr .r8 = AU := by rw [hEg _ (by decide), hv.r8]
  have hE6 : E.gpr .r9 = σ.gpr .rsi := by rw [hEg _ (by decide), hv.r9, hI.r12]
  have hv5 : (varAt E.mem S 4 5).toNat = 0 := by rw [hvarE 5 (by decide) (by decide)]; rfl
  have hv6 : (varAt E.mem S 4 6).toNat = 0 := by rw [hvarE 6 (by decide) (by decide)]; rfl
  have hv7 : (varAt E.mem S 4 7).toNat = TREE := by rw [hvarE 7 (by decide) (by decide)]; rfl
  have hv8 : (varAt E.mem S 4 8).toNat = 0 := by rw [hvarE 8 (by decide) (by decide)]; rfl
  rw [hE1, hE2, hE3, hE4, hE5, hE6, hEsp, hlog, hv5, hv6, hv7, hv8] at hpost
  obtain ⟨env₂, root₂, auth₂, fr₂⟩ := hpost pk a hEnv
  rw [hm₂] at env₂ root₂ auth₂ fr₂
  -- the regions, and what each frame keeps
  have hAUs : Region.Sub ⟨AU, p.hp * p.n⟩ ⟨sig, p.xmssSigLen⟩ := by rw [hAU]; exact Offset.sub_base sig (by omega)
  have hW0 : Region.Sub ⟨sig, p.len * p.n⟩ ⟨sig, p.xmssSigLen⟩ := Region.sub_prefix (by omega)
  have hWA : Region.Disjoint ⟨sig, p.len * p.n⟩ ⟨AU, p.hp * p.n⟩ := by
    have h := Offset.disjoint sig (d := 0) (n := p.len * p.n) (e := p.len * p.n) (k := p.hp * p.n) (.inl (by omega))
      (by have := hR.out_fit; simp only at this; omega) (by have := hR.out_fit; simp only at this; omega)
    rwa [← Levels.scr0 sig, ← hAU] at h
  have hcapN : Layout.oN + (2 ^ p.hp + 8) * p.n ≤ Layout.oSigTmp := by omega
  have hbel : Region.Sub (below (σ.gpr .rsp - 8) (T.stack + 16)) (below (σ.gpr .rsp) (T.stack + 24)) :=
    fun x hx => below_sub (sp := σ.gpr .rsp) (a := T.stack + 16 + 8) (by omega) (by omega) x (below_callee _ _ x hx)
  have FU : Frame (levelsChanges p S (at' S Layout.oN) (2 ^ p.hp) ++ [⟨AU, p.hp * p.n⟩,
      below (σ.gpr .rsp) (T.stack + 24), ⟨at' S (Layout.oVar 4 5), 32⟩]) u.mem s'.mem := by
    refine (hv.frame.sub fun r hr => ?_).trans ((hcm.sub fun r hr => ?_).trans (fr₂.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (σ.gpr .rsp) (T.stack + 24), by simp, below_sub (by omega) (by omega)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨below (σ.gpr .rsp) (T.stack + 24), by simp, hbel⟩
  -- the wots signature, outside what the heights change
  have hsigK : bytesAt s'.mem sig (p.len * p.n) = bytesAt u.mem sig (p.len * p.n) := by
    rw [bytesAt_frame FU (fun r hr => ?_) (by omega)]
    rcases List.mem_append.mp hr with hr | hr
    · exact (hsigd.sub_left hW0).sub_right (Levels.levelsChanges_low hn32 S hcapN r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hWA
      · exact (hR.stk_out.sub_left (below_sub (by omega) (by omega))).symm.sub_left hW0
      · exact (hsigd.sub_left hW0).sub_right (Offset.sub_base S (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega))
  -- the leaves, as `levels` read them
  have hL : nodesAt p E.mem (at' S Layout.oN) (2 ^ p.hp) =
      (List.range (2 ^ p.hp)).map fun j => xmssNode p sk j 0 pk (treeAdrs a) := by
    simp only [nodesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hin : (i + 1) * p.n ≤ 16384 := by have := Nat.mul_le_mul (show i + 1 ≤ 512 by omega) hn32; omega
    rw [Levels.at_add, bytesAt_frame hcm (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hstk 8 (by omega)).sub_right (Levels.sub_scr S (by rw [Nat.add_mul, Nat.one_mul] at hin; omega))).symm)
      (by omega),
      bytesAt_frame hv.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hAU]
          exact ((hsigd.sub_left (Offset.sub_base sig (by omega))).sub_right
            (Offset.sub_base S (by rw [Nat.add_mul, Nat.one_mul] at hin; omega))).symm
        · exact Levels.disj_scr S (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega)
            (by rw [Nat.add_mul, Nat.one_mul] at hin; omega) (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega))
      (by omega)]
    exact hI.nodes i (by omega)
  -- the nodes of height `r`
  have hup : ∀ r ≤ p.hp, upNodes p pk a TREE 0 0 0 (nodesAt p E.mem (at' S Layout.oN) (2 ^ p.hp)) r =
      (List.range (2 ^ (p.hp - r))).map fun j => xmssNode p sk j (0 + r) pk (treeAdrs a) := fun r hr => by
    rw [hL, show (List.range (2 ^ p.hp)).map (fun j => xmssNode p sk j 0 pk (treeAdrs a)) =
      (List.range (2 ^ (p.hp - r + r))).map (fun j => xmssNode p sk j 0 pk (treeAdrs a)) by
        rw [Nat.sub_add_cancel hr], upNodes_xmss ha sk pk r 0 (p.hp - r)]
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → s'.gpr r = u.gpr r := fun r hr hne => by
    rw [h₃ r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact absurd rfl hne
      | exact hv.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsub : ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ p.hp) ++ [⟨AU, p.hp * p.n⟩,
      below (σ.gpr .rsp) (T.stack + 24), ⟨at' S (Layout.oVar 4 5), 32⟩],
      ∃ R ∈ changes p S ++ [⟨sig, p.xmssSigLen⟩, below (σ.gpr .rsp) stack], Region.Sub r R := by
    intro r hr
    simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (⟨k, hk, rfl⟩ | (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl)
    · refine ⟨⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩, ?_, Region.sub_prefix (by
        simp only [Layout.strideA]; omega)⟩
      simp only [changes, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
      exact .inl (.inl (.inr ⟨k, hk, .inl rfl⟩))
    · exact ⟨_, by simp [changes], fun _ h => h⟩
    · exact ⟨_, by simp [changes], fun _ h => h⟩
    · exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Offset.sub S (by decide) (by decide)⟩
    · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp [changes], Region.sub_prefix (by
        rw [show Layout.nodeSlots = 520 from rfl]; omega)⟩
    · exact ⟨⟨sig, p.xmssSigLen⟩, by simp, hAUs⟩
    · exact ⟨below (σ.gpr .rsp) stack, by simp, below_sub (by omega) (by omega)⟩
    · exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Offset.sub S (by decide) (by decide)⟩
  refine ⟨by rw [hcs _ (by simp [calleeSaved]) (by decide), hI.bx],
    by rw [hcs _ (by simp [calleeSaved]) (by decide), hI.r15], by rw [h₃ _ (by simp [calleeSaved]), hsp],
    by rw [h₁, hv.rd, hI.rd], by rw [h₂, hv.wr, hI.wr], by rw [h₆, hv.mx, hI.mx], env₂,
    fun i hi => ?_, ?_, fun hidx' => ?_, hI.frame.trans (FU.sub hsub)⟩
  · rw [Thash4Avx.readW_frame FU (hu_disj hn32 hsigd hAU (by omega) (hstk _ (by omega)) (by omega)
      ⟨by rw [eSv]; omega, by rw [eSv]; omega⟩)]
    exact hI.saved i hi
  · rw [root₂, hup p.hp (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, List.range_one, List.map_cons, List.map_nil,
      List.getD_cons_zero, Nat.zero_add]
  · rw [hSL, bytesAt_add', ← hAU, bytesAt_chunks s'.mem AU p.n p.hp, xmssSign_eq, hsigK, hI.wsig (by omega)]
    refine congrArg _ (flatMap_range_congr fun r hr => ?_)
    have hz0 : bytesAt E.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n = List.replicate p.n 0 := by
      refine Levels.bytesAt_eq (by simp) fun i hi => ?_
      have hrn : r * p.n + i < p.hp * p.n := by
        have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.hp by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega
      rw [add_add, hcm _ fun r' hr' => ?_, hv.zero _ hrn]
      · simp [hi]
      simp only [List.mem_singleton] at hr'; subst hr'
      refine fun hc => (hR.stk_out.sub_left (below_sub (by omega) (by omega))) _ hc ?_
      rw [hAU, add_add]
      exact Offset.contains_base sig (by rw [hSL]; omega) (by omega)
    rw [auth₂ r hr, hz0, hup r (by omega), pick_xmss hr hidx', xorB_zero (xmssNode_length hn32 _ _ _ _ _),
      Nat.zero_add]

theorem tail_nm (n : Nat) :
    (Code.block (Impl.SlhDsa.X86_64.copyWords .r15 0 .rbx Layout.oN (n / 8) ++ restoreRegs 1) : Prog isa).allInstrs
      (fun i => !loadsMxcsr i) = true := by
  simp only [Code.allInstrs_eq, instrs, List.all_append, Levels.copyWords_nm, Bool.true_and]; rfl

/-- `xmssTree`, from its precondition: its postcondition and the calling convention. -/
theorem xmss_wp (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {s : State}
    (hpre : (xmssContract p stack).pre s) :
    WP isa (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln T.code) s fun s' =>
      abiPreserved s s' ∧ (xmssContract p stack).post s s' := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eN : Layout.oN = 12640 := rfl
  have eM : Layout.oMsg = 30496 := rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  obtain ⟨hR, ⟨pk, a, hE⟩, hidx⟩ := hpre
  generalize hS : s.gpr .rdi = S at hR hE
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have hsk : SkAt p s.mem S (bytesAt s.mem (at' S Layout.oSkSeed) p.n) := rfl
  unfold Impl.SlhDsa.X86_64.Xmss.xmssTree
  refine WP.seq (entry_ok hz hS hR hE hsk fun u hu => ?_)
  refine WP.seq (WP.mono (leaves_ok hz T t4name wn hst hs63 hhp hhp9 hR hidx hu) fun u' hu' => ?_)
  refine WP.seq (WP.mono (heights_ok hz T t4name ln hst hs63 hhp hhp9 hR hidx hu') fun w hw => ?_)
  refine WP.mono_mx (tail_nm p.n) (Q := fun v => v.mxcsr = w.mxcsr → _) ?_ fun _ h hm => h hm
  have hw8 : 8 * (p.n / 8) = p.n := by omega
  have hwS' : (⟨S, 2 ^ 16⟩ : Region) ∈ w.wr := by rw [hw.wr]; exact hwS
  refine WP.block_append (WP.mono (Levels.copy_ok (S := S) (t := .r15) (sr := .rbx) (by decide) (by decide)
    (a := Layout.oMsg) (b := 0) (d₁ := Layout.oN) (d₂ := 0) (p.n / 8) w hw.r15 (by rw [hw.bx]; exact Levels.scr0 S)
    hwS' (by omega) (by omega) (by omega)) fun w₁ ⟨g₁, r₁, wr₁, c₁, f₁⟩ => ?_)
  rw [hw8] at c₁ f₁
  have hbx₁ : w₁.gpr .rbx = S := by rw [g₁ _ (by decide), hw.bx]
  have hsv₁ : ∀ i < 6, w₁.mem.readW (at' S (Layout.oSave 1 i)) 64 = s.gpr (savedRegs.getD i .rbx) := fun i hi => by
    rw [Thash4Avx.readW_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Levels.disj_scr S (by rw [show Layout.oSave 1 i = 2528 + 8 * i from rfl]; omega)
        (by rw [show Layout.oSave 1 i = 2528 + 8 * i from rfl]; omega) (by omega)]
    exact hw.saved i hi
  refine restore1_ok (σ := s) (S := S) hbx₁ (by rw [wr₁]; exact hwS') hsv₁ (by rw [g₁ _ (by decide), hw.sp])
    fun t' hm hrd hwr hcs => fun hmx => ?_
  -- what the copy changes
  have hcp : ∀ r ∈ [(⟨S + BitVec.ofNat 64 (Layout.oMsg + 0), p.n⟩ : Region)],
      ∃ R ∈ changes p S ++ [⟨s.gpr .rdx, p.xmssSigLen⟩, below (s.gpr .rsp) stack], Region.Sub r R := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨at' S Layout.oMsg, 64⟩, by simp [changes], Region.sub_prefix (by omega)⟩
  have hF : Frame (changes p S ++ [⟨s.gpr .rdx, p.xmssSigLen⟩, below (s.gpr .rsp) stack]) s.mem t'.mem := by
    rw [hm]; exact hw.frame.trans (f₁.sub hcp)
  refine ⟨⟨fun r hr => hcs r hr, hF.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide),
    by rw [hmx, hw.mx]⟩, fun pk' a' sk' hE' hsk' => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · have hsc : Region.Sub ⟨S, Layout.oSigTmp⟩ ⟨S, scratchLen⟩ := by
        have hs := Offset.sub_base S (d := 0) (n := Layout.oSigTmp) (k := scratchLen) (by rw [eT]; decide)
        rwa [← Levels.scr0 S] at hs
      exact hR.ret_scr.sub_right fun x h' => hsc x (Levels.changes_low hn32 S r hr x h')
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.ret_out
      · exact Offset.base_disjoint_below _ (by omega)
  -- the postcondition
  rw [hS] at hE' hsk' ⊢
  obtain ⟨rfl, rfl⟩ := Env.unique hE hE'
  have e₃ : sk' = bytesAt s.mem (at' S Layout.oSkSeed) p.n := hsk'.symm
  subst e₃
  refine ⟨?_, ?_, fun hi => ?_, hF⟩
  · rw [hm]
    exact Env.of_frame hn32 hw.env (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨at' S Layout.oMsg, 64⟩, by simp [changes], Region.sub_prefix (by omega)⟩) (hR.stk_scr.sub_left
        (below_sub (Nat.zero_le _) (by omega)))
  · rw [hm, ← hw.root]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [Levels.at_add, Levels.at_add, show Layout.oMsg + i = Layout.oMsg + 0 + i by omega,
      show Layout.oN + i = 0 + Layout.oN + i by omega]
    exact c₁ i hi'
  · rw [hm, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.out_scr.sub_right (Offset.sub_base S (by omega))) (by have := hR.out_fit; simp only at this; omega)]
    exact hw.xsig hi

/-- The first part of `Verified`. -/
theorem xmss_correct (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) :
    ∀ s, (xmssContract p stack).pre s → ∃ t s',
      Exec isa (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln T.code) s t s' ∧
      abiPreserved s s' ∧ (xmssContract p stack).post s s' := fun s h => by
  obtain ⟨t, s', e, abi, post⟩ := xmss_wp hz T t4name wn ln hst hs63 hhp hhp9 h
  exact ⟨t, s', e, abi, post⟩

end VG.Proof.SlhDsa.X86_64.XmssTree
