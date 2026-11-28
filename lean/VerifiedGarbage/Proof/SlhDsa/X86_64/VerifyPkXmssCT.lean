module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssCTBase
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# SLH-DSA (SHAKE) on x86-64: `xmssPk` is constant time

Two runs of `xmssPk` from states of its precondition that agree on its
public data leak the same trace (`xmssPk_ct`). Its parts between calls
pass the taint analysis (`VerifyPkXmssCTBase.lean`) from registers and
variables that each run holds, by its correctness, at the same values: the
chain, step and height of the loop both runs are in, which their invariants
index (`Levels.relLoop`), and the digits of the message, which both runs have.
Each call of `thash4` has the same arguments in both runs (`t4ctG`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.XmssCT

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add toNat_at relSeq relLoop wpLoop in_scr in_scr')

/-! ## A call of `thash4` -/

/-- `thashArgs` for the lanes at `o`, `st` bytes apart, messages of `len` bytes. -/
theorem argsG_ok {p : Params} (hn : p.n ≤ 32) {S : Addr} {o st len : Nat} (ho : o < 2 ^ 31) (hst : st < 2 ^ 31)
    (hlen : len ≤ st) {t : State} (hbx : t.gpr .rbx = S) {Q : State → Prop}
    (k : ∀ u, u.gpr .rdi = at' S o → (u.gpr .rsi).toNat = st → (u.gpr .rdx).toNat = len →
      u.gpr .rcx = at' S o + BitVec.ofNat 64 (p.n + 32) → u.gpr .r8 = S →
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) →
      u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len)) t Q := by
  simp only [Impl.SlhDsa.X86_64.thashArgs, Impl.SlhDsa.X86_64.Layout.msgOff]
  refine Proof.Sha3.X86_64.wp_mov fun u₁ v₁ => Proof.Sha3.X86_64.wp_addi fun u₂ v₂ =>
    Proof.Sha3.X86_64.wp_mov32i fun u₃ v₃ => Proof.Sha3.X86_64.wp_mov32i fun u₄ v₄ =>
    Proof.Sha3.X86_64.wp_mov fun u₅ v₅ => Proof.Sha3.X86_64.wp_addi fun u₆ v₆ =>
    Proof.Sha3.X86_64.wp_mov fun u v => WP.block_nil ?_
  have hdi2 : u₂.gpr .rdi = at' S o := by rw [v₂.gpr, v₁.gpr, hbx, sx_ofNat ho]
  refine k u ?_ ?_ ?_ ?_ ?_ (fun g h1 h2 h3 h4 h5 => ?_) ?_ ?_ ?_
  · rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), hdi2]
  · rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hst]
  · rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hst, hlen]
  · rw [v.other _ (by decide), v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), hdi2,
      sx_ofNat (by omega_using [hn])]
  · rw [v.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hbx]
  · rw [v.other _ h5, v₆.other _ h4, v₅.other _ h4, v₄.other _ h3, v₃.other _ h2, v₂.other _ h1, v₁.other _ h1]
  · rw [v.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- A call of `thash4` on the lanes `A` or `B` from states with `rbx` =
`scratch` and the same stack pointer, each with its table of constants:
both runs pass it the same arguments. -/
theorem t4ctG {p : Params} (T : Thash4Impl p.n) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (name : String)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {o st len : Nat}
    (hl : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    {S sp : Addr} (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
    {A : State → Prop}
    (hA : ∀ a, A a → a.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ a.wr ∧ a.gpr .rsp = sp ∧ RcTable a.mem S)
    (hct : RelCT isa (fun a b => A a ∧ A b) (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len))
      fun _ _ => True) :
    RelCT isa (fun a b => A a ∧ A b) (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code o st len)
      fun _ _ => True := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hoS : o + 4 * st ≤ 12640 ∧ o < 2 ^ 31 ∧ st < 2 ^ 31 ∧ 3296 ≤ o ∧ 2 * p.n + 32 ≤ st := by
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Layout.oA, Layout.oB, Layout.strideA, Layout.strideB] <;>
      omega_using [hn32]
  obtain ⟨hoS, ho, hst', ho3, hout⟩ := hoS
  let F : State → Prop := fun u => ∃ t, A t ∧ u.gpr .rdi = at' S o ∧ (u.gpr .rsi).toNat = st ∧
    (u.gpr .rdx).toNat = len ∧ u.gpr .rcx = at' S o + BitVec.ofNat 64 (p.n + 32) ∧ u.gpr .r8 = S ∧
    (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) ∧
    u.mem = t.mem ∧ u.wr = t.wr
  have hw : ∀ a, A a → WP isa (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len)) a F := fun a ha =>
    argsG_ok hn32 ho hst' hll (hA a ha).1 fun u e1 e2 e3 e4 e5 eg em _ ew => ⟨a, ha, e1, e2, e3, e4, e5, eg, em, ew⟩
  unfold Impl.SlhDsa.X86_64.thashCall
  refine relSeq (B₁ := F) (B₂ := F) hct (fun a h => hw a h) (fun b h => hw b h) ?_
  have hLs : Region.Sub ⟨at' S o, 4 * st⟩ ⟨S, 2 ^ 16⟩ := Offset.sub_base S (by omega_using [hoS])
  have hWs : Region.Sub ⟨S, workLen⟩ ⟨S, 2 ^ 16⟩ := Region.sub_prefix (by simp [workLen])
  have hb8 : Region.Sub (below sp (T.stack + 8)) (below sp stack) :=
    below_sub (by omega_using [hst, T.stack_le]) (by omega_using [hs63])
  have entry : ∀ u, F u → (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]) ∧
      Covers ([] ++ [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩] u.wr ∧ u.gpr .rsp = sp := by
    intro u ⟨t, ht, e1, e2, e3, e4, e5, eg, em, ew⟩
    obtain ⟨_, htw, hts, hrc⟩ := hA t ht
    have hsp : u.gpr .rsp = sp := by rw [eg _ (by decide) (by decide) (by decide) (by decide) (by decide), hts]
    have hw' : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [ew]; exact htw
    have hcov : Covers [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩] u.wr := Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hw', o, rfl, by show o + 4 * st ≤ 2 ^ 16; omega_using [hoS]⟩
      · exact ⟨_, hw', 0, Levels.scr0 S, by simp [workLen]⟩
    refine ⟨thash4_entry T e1 e2 e3 e4 e5 hlp hlm hll (by omega_using [hout])
      (by rw [toNat_at (by omega_using [hS, hoS])]; omega_using [hS, hoS]) (by simp only [workLen]; omega_using [hS])
      (Offset.disjoint_base S (by simp only [workLen]; omega_using [ho3]) (by omega_using [hoS]))
      (by rw [hsp]; exact (hstk.sub_left hb8).sub_right hLs) (by rw [hsp]; exact (hstk.sub_left hb8).sub_right hWs)
      (by rw [em]; exact hrc), by rw [List.nil_append]; exact Covers.right hcov, hcov, hsp⟩
  refine RelCT.call T.verified.1 T.verified.2.1 [] [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩] fun a b ⟨ha, hb⟩ => ?_
  obtain ⟨p₁, c₁, w₁, s₁⟩ := entry a ha
  obtain ⟨p₂, c₂, w₂, s₂⟩ := entry b hb
  obtain ⟨_, _, a1, a2, a3, a4, a5, -⟩ := ha
  obtain ⟨_, _, b1, b2, b3, b4, b5, -⟩ := hb
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, by rw [s₁, s₂]⟩ <;>
    simp only [State.withRegions_gpr, State.callEntry_rsp]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a1, b1]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide)]
    exact BitVec.eq_of_toNat_eq (by rw [a2, b2])
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide)]
    exact BitVec.eq_of_toNat_eq (by rw [a3, b3])
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a4, b4]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a5, b5]
  · rw [s₁, s₂]

/-! ## What each run holds -/

/-- A run of `xmssPk` after its prologue: `scratch` at `S` in `rbx`, `idx`,
the signature `sig`, `oMsg`, the stack pointer `sp`, its regions, the digits
`dg` of the message, and an environment. -/
structure XS (p : Params) (S sig sp : Addr) (idx : Nat) (dg : Nat → Byte) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = BitVec.ofNat 64 idx
  r13 : t.gpr .r13 = sig
  r14 : t.gpr .r14 = S + BitVec.ofNat 64 Layout.oMsg
  sp : t.gpr .rsp = sp
  rd : t.rd = [⟨sig, p.xmssSigLen⟩]
  wr : t.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]
  dig : ∀ c < p.len, t.mem (at' S (Layout.oDigits + c)) = dg c
  env : ∃ pkSeed a16, Env p t.mem S pkSeed a16

section
variable {p : Params} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte} {t : State}

theorem XS.hw (h : XS p S sig sp idx dg t) : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by
  rw [h.wr]; exact List.mem_cons_self ..

theorem XS.hsr (h : XS p S sig sp idx dg t) : (⟨sig, p.xmssSigLen⟩ : Region) ∈ t.rd := by
  rw [h.rd]; exact List.mem_singleton_self _

theorem XS.rc (h : XS p S sig sp idx dg t) : RcTable t.mem S := by
  obtain ⟨_, _, e⟩ := h.env; exact e.rc

/-- What a step that keeps the callee-saved registers and the regions, and
changes only regions of `changes` and the stack (`hFe`), outside the digits
(`hFd`), keeps. -/
theorem XS.of_frame (h : XS p S sig sp idx dg t) (hn : p.n ≤ 32) (hl : p.len ≤ 128) {stack : Nat}
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) {t' : State}
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp], t'.gpr r = t.gpr r) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hFe : Frame (changes p S ++ [below sp stack]) t.mem t'.mem) {R : List Region} (hFd : Frame R t.mem t'.mem)
    (hdis : ∀ r ∈ R, Region.Disjoint ⟨at' S Layout.oDigits, 128⟩ r) : XS p S sig sp idx dg t' := by
  obtain ⟨pk, a, e⟩ := h.env
  refine ⟨by rw [hg _ (by simp), h.bx], by rw [hg _ (by simp), h.r12], by rw [hg _ (by simp), h.r13],
    by rw [hg _ (by simp), h.r14], by rw [hg _ (by simp), h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr],
    fun c hc => ?_, pk, a, Env.of_frame hn e hFe hstk⟩
  have : c < 128 := by omega
  rw [← h.dig c hc]
  exact frame_at hFd fun r hr => (hdis r hr).sub_left
    (Offset.sub S (d := Layout.oDigits + c) (e := Layout.oDigits) (by omega) (by omega))

end

/-- A variable outside a frame's regions keeps its value. -/
theorem var_keep {R : List Region} {m m' : Mem} (hF : Frame R m m') {S : Addr} {o : Nat}
    (hd : ∀ r ∈ R, Region.Disjoint ⟨at' S o, 8⟩ r) : m'.readW (at' S o) 64 = m.readW (at' S o) 64 :=
  hF.readW (Region.contains_self _ _) hd (by decide)

theorem hsl1 (o : Nat) (h : o + 8 ≤ 65536) : ∀ x ∈ [o], x + 8 ≤ 65536 := fun x hx => by
  rw [List.mem_singleton] at hx; subst hx; exact h

/-! ## The restores of a step -/

/-- A run in the step `j` of the group from `c₀`. -/
structure RP (p : Params) (S sig sp : Addr) (idx : Nat) (dg : Nat → Byte) (c₀ j : Nat) (t : State) : Prop where
  xs : XS p S sig sp idx dg t
  v0 : t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀
  v1 : t.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j

/-- The first block of a lane's restore: its chain `c` in `r10`, ZF and CF
its digit's comparison with the step. -/
theorem rhead_ok {p : Params} (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128) {k' c₀ j : Nat} (hk' : k' < 4)
    (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 2 ^ 32) {t : State} {S : Addr} (hbx : t.gpr .rbx = S)
    (hv0 : t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hv1 : t.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) {Q : State → Prop}
    (k : ∀ u, (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → g ≠ .r11 → u.gpr g = t.gpr g) →
      u.mem = t.mem → u.rd = t.rd → u.wr = t.wr →
      u.gpr .r10 = BitVec.ofNat 64 (min (c₀ + k') (p.len - 1)) →
      u.zf = some (decide ((t.mem (at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)))).toNat = j)) →
      u.cf = some (decide ((t.mem (at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)))).toNat < j)) → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainOf p k' ++ ([.alu .cmp .r11 (.mem (Impl.SlhDsa.X86_64.Verify.xv 1))] : List Instr)))
      t Q := by
  refine chainOf_ok hlen1 hlen (by omega) hbx hv0 hw fun s₁ g₁ m₁ r₁ w₁ h10₁ h11₁ => ?_
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  refine wp_cmpm (a := at' S (Layout.oVar 1 1))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hb₁])
    (by rw [r₁, w₁, oVar11]; exact in_scr' hw (by omega)) fun s₂ g₂ m₂ r₂ w₂ z₂ c₂ => WP.block_nil ?_
  obtain ⟨d, hd⟩ : ∃ d, d = (t.mem (at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)))).toNat := ⟨_, rfl⟩
  rw [← hd] at h11₁ k
  have hd256 : d < 256 := by rw [hd]; exact (t.mem _).isLt
  rw [m₁, hv1, h11₁] at z₂ c₂
  have hd' : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hj' : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hd', hj'] at c₂
  rw [cmp_eq (by omega) (by omega)] at z₂
  exact k s₂ (fun g h1 h2 h3 h4 h5 => by rw [g₂, g₁ _ h1 h2 h3 h4 h5]) (by rw [m₂, m₁]) (by rw [r₂, r₁])
    (by rw [w₂, w₁]) (by rw [g₂, h10₁]) z₂ c₂

section
variable {p : Params} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) {stack : Nat}
  (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64)
  (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ p.xmssSigLen)

include hn hl hstk hsfit hss hsL in
/-- A lane's restore, in one run. -/
theorem rp_restore {k' c₀ j : Nat} (hk' : k' < 4) (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 2 ^ 32)
    {t : State} (ht : RP p S sig sp idx dg c₀ j t) :
    WP isa (Impl.SlhDsa.X86_64.Verify.restoreLane p k') t (RP p S sig sp idx dg c₀ j) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  refine restore_ok hn (by omega) hlen hk' hc₀ hj ht.xs.bx ht.xs.r13 ht.v0 ht.v1 ht.xs.hw ht.xs.hsr hsfit hss hsL
    fun s' g' r' w' _ F' => ?_
  have hd : ∀ {o : Nat}, o + 8 ≤ 3296 →
      ∀ r ∈ [(⟨at' S (Layout.laneA k' + p.n + 32), p.n⟩ : Region)], Region.Disjoint ⟨at' S o, 8⟩ r := fun ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [eA]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  refine ⟨ht.xs.of_frame hn32 hlen hstk (fun r hr => ?_) r' w' (F'.sub fun r hr => ?_) F' (fun r hr => ?_), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact sub_changes hn32 S _ (Or.inl ⟨k', hk', by omega, by rw [eA]; omega⟩)
  · simp only [List.mem_singleton] at hr; subst hr
    rw [eA]; exact Offset.disjoint S (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega) (by omega)
  · rw [var_keep F' (hd (by rw [oVar10]; omega)), ht.v0]
  · rw [var_keep F' (hd (by rw [oVar11]; omega)), ht.v1]

include hn hl in
/-- Two runs of a lane's restore, in the same step of the same group. -/
theorem rl_ct {k' c₀ j : Nat} (hk' : k' < 4) (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 2 ^ 32) :
    RelCT isa (fun a b => RP p S sig sp idx dg c₀ j a ∧ RP p S sig sp idx dg c₀ j b)
      (Impl.SlhDsa.X86_64.Verify.restoreLane p k') fun _ _ => True := by
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  obtain ⟨c, hc⟩ : ∃ c, c = min (c₀ + k') (p.len - 1) := ⟨_, rfl⟩
  have hcl : c < p.len := by omega
  let H : State → Prop := fun u => u.gpr .rbx = S ∧ u.gpr .r13 = sig ∧ u.gpr .r10 = BitVec.ofNat 64 c ∧
    u.zf = some (decide ((dg c).toNat = j)) ∧ u.cf = some (decide ((dg c).toNat < j))
  have hH : ∀ a, RP p S sig sp idx dg c₀ j a → WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainOf p k' ++
      [.alu .cmp .r11 (.mem (Impl.SlhDsa.X86_64.Verify.xv 1))])) a H := fun a ha =>
    rhead_ok (by omega) hlen hk' hc₀ hj ha.xs.bx ha.v0 ha.v1 ha.xs.hw fun u g _ _ _ h10 hz hc' => by
      rw [← hc, ha.xs.dig c hcl] at hz hc'
      rw [← hc] at h10
      exact ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), ha.xs.bx],
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), ha.xs.r13], h10, hz, hc'⟩
  unfold Impl.SlhDsa.X86_64.Verify.restoreLane
  refine relSeq (B₁ := H) (B₂ := H) (ct_rhead hn hl hk' fun a b ⟨ha, hb⟩ =>
    xT_agree ha.xs.wr hb.xs.wr ha.xs.bx hb.xs.bx (by simp) (hsl1 _ (by rw [oVar10]; omega)) fun o ho => by
      rw [List.mem_singleton] at ho; subst ho; rw [ha.v0, hb.v0]) hH hH ?_
  refine RelCT.ite (fun a b ⟨ha, hb⟩ => by show a.zf = b.zf; rw [ha.2.2.2.1, hb.2.2.2.1])
    (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine RelCT.ite (fun a b ⟨⟨ha, hb⟩, _⟩ => by show a.cf = b.cf; rw [ha.2.2.2.2, hb.2.2.2.2])
    (RelCT.block_nil fun _ _ _ => trivial) ?_
  exact ct_rsig hn hl hk' fun a b ⟨⟨⟨ha, hb⟩, _⟩, _⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ha.1, hb.1]
    · rw [ha.2.2.1, hb.2.2.1]
    · rw [ha.2.1, hb.2.1]

end

theorem cs_sub : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp], r ∈ calleeSaved := by decide

theorem eV (i : Nat) : Layout.oVar 1 i = 2576 + 8 * i := rfl

/-- What a call of `thash4` changes, but the stack, is outside the
variables and the digits. -/
theorem lw_disj {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack o st : Nat}
    (hl : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) {d l : Nat}
    (hd : (2400 ≤ d ∧ d + l ≤ 3296) ∨ (12640 ≤ d ∧ d + l ≤ 2 ^ 16)) :
    ∀ r ∈ lanesOut p S o st ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp stack], Region.Disjoint ⟨at' S d, l⟩ r := by
  have hb : d + l ≤ 2 ^ 16 := by omega
  intro r hr
  simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Layout.oA, Layout.oB, Layout.strideA, Layout.strideB] <;>
      exact Offset.disjoint S (by omega) (by omega) (by omega)
  · exact Offset.disjoint_base S (by omega) (by omega)
  · exact Offset.disjoint S (by omega) (by omega) (by omega)
  · exact (hstk.sub_right (Offset.sub_base S hb)).symm

section
variable {p : Params} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)

include hn hl hstk hS in
/-- A call of `thash4` in one run: it keeps the run's registers, the
variables and the digits. -/
theorem xs_call (T : Thash4Impl p.n) (name : String) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {o st len : Nat} (hl' : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st) {t : State} (h : XS p S sig sp idx dg t) :
    WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code o st len) t (fun t' => XS p S sig sp idx dg t' ∧
      ∀ i < 4, t'.mem.readW (at' S (Layout.oVar 1 i)) 64 = t.mem.readW (at' S (Layout.oVar 1 i)) 64) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  refine lanes_ok T name hn hst hs63 hl' hlp hlm hll h.bx h.hw hS (by rw [h.sp]; exact hstk) h.rc
    fun t' r' w' g' _ F1 F2 => ?_
  rw [h.sp] at F1 F2
  exact ⟨h.of_frame hn32 hlen hstk (fun r hr => g' r (cs_sub r hr)) r' w' F1 F2
      (lw_disj hn32 hl' hstk (Or.inr ⟨by rw [oDigits_eq]; omega, by rw [oDigits_eq]; omega⟩)),
    fun i hi => var_keep F2 (lw_disj hn32 hl' hstk (Or.inl ⟨by rw [eV]; omega, by rw [eV]; omega⟩))⟩

end

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsL : p.len * p.n ≤ p.xmssSigLen)

include hn hl hstk in
/-- The first block of a step, in one run. -/
theorem rp_h28 {c₀ j : Nat} (hj : j < 2 ^ 32) {t : State} (ht : RP p S sig sp idx dg c₀ j t) :
    WP isa (.block (.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 1)) :: (List.range 4).flatMap fun k' =>
      Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r10))
      t (RP p S sig sp idx dg c₀ j) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  refine hash28_ok hn hj ht.xs.bx ht.v1 ht.xs.hw fun s' g' r' w' _ F' => ?_
  have hd : ∀ {o l : Nat}, (o + l ≤ 3296 ∨ (12640 ≤ o ∧ o + l ≤ 2 ^ 16)) →
      ∀ r ∈ (List.range 4).map (fun k' => (⟨at' S (Layout.laneA k' + p.n + 28), 4⟩ : Region)),
        Region.Disjoint ⟨at' S o, l⟩ r := fun ho r hr => by
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    rw [eA]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  refine ⟨ht.xs.of_frame hn32 hlen hstk (fun r hr => ?_) r' w' (F'.sub fun r hr => ?_) F'
    (hd (Or.inr ⟨by rw [oDigits_eq]; omega, by rw [oDigits_eq]; omega⟩)), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g' _ (by decide) (by decide)
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact sub_changes hn32 S _ (Or.inl ⟨c, hc, by omega, by rw [eA]; omega⟩)
  · rw [var_keep F' (hd (Or.inl (by rw [oVar10]; omega))), ht.v0]
  · rw [var_keep F' (hd (Or.inl (by rw [oVar11]; omega))), ht.v1]

include hn hl hS hstk hsfit hss hsL in
/-- Two runs of a step, in the same step of the same group. -/
theorem sb_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {c₀ j : Nat} (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 15) :
    RelCT isa (fun a b => RP p S sig sp idx dg c₀ j a ∧ RP p S sig sp idx dg c₀ j b)
      (Impl.SlhDsa.X86_64.Verify.stepBody p f) fun _ _ => True := by
  have hj' : j < 2 ^ 32 := by omega
  have hR : ∀ {k'}, k' < 4 → ∀ a, RP p S sig sp idx dg c₀ j a →
      WP isa (Impl.SlhDsa.X86_64.Verify.restoreLane p k') a (RP p S sig sp idx dg c₀ j) := fun hk a ha =>
    rp_restore hn hl hstk hsfit hss hsL hk hc₀ hj' ha
  have hrbx : ∀ a b, RP p S sig sp idx dg c₀ j a ∧ RP p S sig sp idx dg c₀ j b → ∀ r ∈ [Reg.rbx], a.gpr r = b.gpr r :=
    fun a b ⟨ha, hb⟩ r hr => by rw [List.mem_singleton] at hr; subst hr; rw [ha.xs.bx, hb.xs.bx]
  unfold Impl.SlhDsa.X86_64.Verify.stepBody
  refine relSeq (ct_h28 hn hl hrbx) (fun a h => rp_h28 hn hl hstk hj' h) (fun a h => rp_h28 hn hl hstk hj' h) ?_
  rw [ht]
  have hcall : ∀ a, RP p S sig sp idx dg c₀ j a → WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ f.t4name T.code
      Layout.oA Layout.strideA (2 * p.n + 32)) a (RP p S sig sp idx dg c₀ j) := fun a ha =>
    WP.mono (xs_call hn hl hS hstk T f.t4name hst hs63 (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega_using [hn])
      (by simp only [Layout.strideA]; omega_using [hn]) ha.xs) fun t' ⟨hx, hv⟩ =>
      ⟨hx, by rw [hv 0 (by decide), ha.v0], by rw [hv 1 (by decide), ha.v1]⟩
  refine relSeq (t4ctG T hn f.t4name hst hs63 (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega_using [hn])
      (by simp only [Layout.strideA]; omega_using [hn]) hS hstk
      (fun a ha => ⟨ha.xs.bx, ha.xs.hw, ha.xs.sp, ha.xs.rc⟩) (ct_args hn hl (Or.inl ⟨rfl, rfl⟩) _ hrbx))
    hcall hcall ?_
  refine relSeq (rl_ct hn hl (by decide) hc₀ hj') (hR (by decide)) (hR (by decide)) ?_
  refine relSeq (rl_ct hn hl (by decide) hc₀ hj') (hR (by decide)) (hR (by decide)) ?_
  refine relSeq (rl_ct hn hl (by decide) hc₀ hj') (hR (by decide)) (hR (by decide)) ?_
  refine relSeq (rl_ct hn hl (by decide) hc₀ hj') (hR (by decide)) (hR (by decide)) ?_
  exact ct_sfin hrbx

end

/-! ## The steps of a group -/

/-- The lanes' fields of a group from `c₀`. -/
def Fld (p : Params) (S : Addr) (idx c₀ : Nat) (t : State) : Prop :=
  ∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
    toByte 0 4 ++ toByte idx 4 ++ toByte (min (c₀ + k) (p.len - 1)) 4

/-- The invariant of a group's steps, at the measure `m = 15 - j`. -/
def SInv (p : Params) (S sig sp : Addr) (idx : Nat) (dg : Nat → Byte) (c₀ m : Nat) (t : State) : Prop :=
  ∃ j, m = 15 - j ∧ j < 15 ∧ RP p S sig sp idx dg c₀ j t ∧ Fld p S idx c₀ t

/-- Whether the steps go on after the one at the measure `m`. -/
def sCont (m : Nat) : Bool := !decide (15 - m + 1 = 15)

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hfam : p.family = .shake) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsL : p.len * p.n ≤ p.xmssSigLen) (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below sp stack))

include hn hl hfam hS hstk hsfit hss hsL hsb in
/-- A step, in one run. -/
theorem s_step (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {c₀ : Nat} (hc₀ : c₀ + 4 < 2 ^ 31) (m : Nat) (s : State) (hs : SInv p S sig sp idx dg c₀ m s) :
    WP isa (Impl.SlhDsa.X86_64.Verify.stepBody p f) s fun s' => isa.eval .ne s' = some (sCont m) ∧
      (sCont m = false → XS p S sig sp idx dg s' ∧
        s'.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀) ∧
      (sCont m = true → m - 1 < m ∧ SInv p S sig sp idx dg c₀ (m - 1) s') := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  obtain ⟨j, rfl, hj, hr, hf⟩ := hs
  obtain ⟨pk, a, henv⟩ := hr.xs.env
  refine stepBody_ok T ht hn hfam (by omega) hlen hst hs63 (idx := idx) hc₀ hj hr.xs.bx hr.xs.r13 hr.v0 hr.v1
    hr.xs.hw hS (by rw [hr.xs.sp]; exact hstk) henv hf hr.xs.hsr hsfit hss hsL (by rw [hr.xs.sp]; exact hsb)
    fun t' g' r' w' v0' v1' z' f' _ F' => ?_
  rw [hr.xs.sp] at F'
  have hx : XS p S sig sp idx dg t' := hr.xs.of_frame hn32 hlen hstk (fun r h => g' r (cs_sub r h)) r' w'
    (F'.sub (chFrame_sub p S sp stack)) F'
    (chFrame_disj hn32 hstk (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega))
  have e : sCont (15 - j) = !decide (j + 1 = 15) := by simp only [sCont, show 15 - (15 - j) = j by omega]
  refine ⟨by show t'.zf.map (!·) = _; rw [z', e]; rfl, fun hc => ⟨hx, v0'⟩, fun hc => ⟨by omega, j + 1, by omega,
    ?_, ⟨hx, v0', v1'⟩, fun k hk => by rw [f' k hk, hf k hk]⟩⟩
  rw [e] at hc
  have : ¬ j + 1 = 15 := fun h => by simp [h] at hc
  omega

include hn hl hfam hS hstk hsfit hss hsL hsb in
/-- Two runs of a group's steps, from the same step `t₀`. -/
theorem sl_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {c₀ : Nat} (hc₀ : c₀ + 4 < 2 ^ 31) (m : Nat) :
    RelCT isa (fun a b => SInv p S sig sp idx dg c₀ m a ∧ SInv p S sig sp idx dg c₀ m b)
      (.loop (Impl.SlhDsa.X86_64.Verify.stepBody p f) .ne) fun _ _ => True := by
  refine RelCT.mono (relLoop sCont (fun m => m - 1) (fun m => ?_)
    (s_step hn hl hfam hS hstk hsfit hss hsL hsb T ht hst hs63 hc₀)
    (s_step hn hl hfam hS hstk hsfit hss hsL hsb T ht hst hs63 hc₀) m) (fun _ _ h => h) fun _ _ _ => trivial
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨j₁, e₁, hj₁, r₁, _⟩, ⟨j₂, e₂, _, r₂, _⟩⟩ x₁ x₂
  obtain rfl : j₂ = j₁ := by omega
  exact sb_ct hn hl hS hstk hsfit hss hsL T ht hst hs63 hc₀ hj₁ _ _ _ _ _ _ ⟨r₁, r₂⟩ x₁ x₂

end

/-! ## A group -/

/-- The block between a group's lanes and its steps: variable 1 the least
digit `v`, CF set if below 15. -/
theorem mid_ok {u : State} {S : Addr} {v : Nat} (hv : v ≤ 15) (hbx : u.gpr .rbx = S)
    (hv2 : u.mem.readW (at' S (Layout.oVar 1 2)) 64 = BitVec.ofNat 64 v) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr)
    {Q : State → Prop}
    (k : ∀ s₃, (∀ g, g ≠ .rax → s₃.gpr g = u.gpr g) → s₃.rd = u.rd → s₃.wr = u.wr →
      s₃.mem = u.mem.writeW (at' S (Layout.oVar 1 1)) (BitVec.ofNat 64 v) → s₃.cf = some (decide (v < 15)) →
      Q s₃) :
    WP isa (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .store (Impl.SlhDsa.X86_64.Verify.xv 1) .rax,
      .alu .cmp .rax (.imm 15)]) u Q := by
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 1 2))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hbx])
    (by rw [oVar12]; exact in_scr' hw (by omega)) fun s₁ u₁ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 1 1))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.wr, oVar11]; exact in_scr hw (by omega)) fun s₂ g₂ m₂ r₂ w₂ => ?_
  refine wp_cmpi_cf fun s₃ g₃ m₃ r₃ w₃ _ c₃ => WP.block_nil ?_
  have hrax : s₂.gpr .rax = BitVec.ofNat 64 v := by rw [g₂, u₁.gpr, hv2]
  rw [g₂, ← g₂, hrax, show BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 15 by decide] at c₃
  simp only [BitVec.toNat_ofNat] at c₃
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at c₃
  exact k s₃ (fun g h => by rw [g₃, g₂, u₁.other _ h]) (by rw [r₃, r₂, u₁.rd]) (by rw [w₃, w₂, u₁.wr])
    (by rw [m₃, m₂, u₁.gpr, hv2, u₁.mem]) c₃

/-- The least of 15 and the digits of a group's first `K` lanes. -/
def dminG (p : Params) (dg : Nat → Byte) (c₀ : Nat) : Nat → Nat
  | 0 => 15
  | K + 1 => min (dminG p dg c₀ K) (dg (min (c₀ + K) (p.len - 1))).toNat

theorem dmin_eq {p : Params} {m : Mem} {S : Addr} {dg : Nat → Byte} (hl : 1 ≤ p.len)
    (h : ∀ c < p.len, m (at' S (Layout.oDigits + c)) = dg c) (c₀ : Nat) :
    ∀ K, dmin p m S c₀ K = dminG p dg c₀ K
  | 0 => rfl
  | K + 1 => by
    simp only [dmin, dminG, dmin_eq hl h c₀ K]
    rw [h (min (c₀ + K) (p.len - 1)) (by omega)]

theorem dminG_le (p : Params) (dg : Nat → Byte) (c₀ : Nat) : ∀ K, dminG p dg c₀ K ≤ 15
  | 0 => Nat.le_refl _
  | K + 1 => Nat.le_trans (Nat.min_le_left _ _) (dminG_le p dg c₀ K)

/-- A run at the group from `c₀`. -/
def GI (p : Params) (S sig sp : Addr) (idx : Nat) (dg : Nat → Byte) (c₀ : Nat) (t : State) : Prop :=
  XS p S sig sp idx dg t ∧ t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hfam : p.family = .shake) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsL : p.len * p.n ≤ p.xmssSigLen) (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below sp stack))
  (hidx : idx < 2 ^ 32)

/-- A run after a lane's end. -/
def EP (S : Addr) (c₀ : Nat) (u : State) : Prop :=
  u.gpr .rbx = S ∧ u.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩] ∧ u.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀

include hn hl in
theorem ep_end {k' c₀ : Nat} (hk' : k' < 4) (hc₀ : c₀ < p.len) {u : State} (hu : EP S c₀ u) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainOf p k' ++ ([.mov .rdx (.reg .r10)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      Impl.SlhDsa.X86_64.copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
        (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8))) u (EP S c₀) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB := by
    rw [hl, show Layout.strideB = 2208 from rfl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hu.2.1]; exact List.mem_cons_self ..
  have h := endLane_ok hn (by omega) hlen hlB hk' (by omega) hu.1 hu.2.2 hw (is := []) (Q := EP S c₀)
    fun s' g' r' w' _ F' => WP.block_nil ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide), hu.1],
      by rw [w', hu.2.1], by
        rw [var_keep F' fun r hr => ?_, hu.2.2]
        simp only [List.mem_singleton] at hr; subst hr
        have hc : min (c₀ + k') (p.len - 1) * p.n + p.n ≤ 128 * 32 :=
          Nat.le_trans (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul hlen hn32)
        rw [oVar10, show Layout.laneB 0 = 3808 from rfl]
        exact Offset.disjoint S (by omega) (by omega) (by omega)⟩
  rwa [List.append_nil] at h

include hn hl hfam hS hstk hsfit hss hsL hsb hidx in
/-- Two runs of a group, from the same chain `c₀`. -/
theorem gc_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {c₀ : Nat} (hc₀ : c₀ < p.len) :
    RelCT isa (fun a b => GI p S sig sp idx dg c₀ a ∧ GI p S sig sp idx dg c₀ b)
      (Impl.SlhDsa.X86_64.Verify.chainGroup p f) fun _ _ => True := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have hc₀' : c₀ + 4 < 2 ^ 31 := by omega
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = dminG p dg c₀ 4 := ⟨_, rfl⟩
  have ht₀15 : t₀ ≤ 15 := by rw [ht₀]; exact dminG_le _ _ _ _
  let LB : State → Prop := fun u => ∃ t, GI p S sig sp idx dg c₀ t ∧ LInv p S sig idx c₀ t 4 u
  let MB : State → Prop := fun u => RP p S sig sp idx dg c₀ t₀ u ∧ Fld p S idx c₀ u ∧
    u.cf = some (decide (t₀ < 15))
  have hLB : ∀ a, GI p S sig sp idx dg c₀ a → WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainLanes p)) a LB :=
    fun a ha => chainLanes_ok hn (by omega) hlen hc₀' hidx ha.1.bx ha.1.r12 ha.1.r13 ha.2 ha.1.hw ha.1.hsr hsfit hss
      hsL fun u hu => ⟨a, ha, hu⟩
  have hMB : ∀ a, LB a → WP isa (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)),
      .store (Impl.SlhDsa.X86_64.Verify.xv 1) .rax, .alu .cmp .rax (.imm 15)]) a MB := by
    intro u ⟨t, ht, hu⟩
    have hv2 := hu.v2
    rw [dmin_eq (by omega) ht.1.dig, ← ht₀] at hv2
    refine mid_ok ht₀15 hu.bx hv2 (by rw [hu.wr]; exact ht.1.hw) fun s₃ g₃ r₃ w₃ m₃ c₃ => ?_
    have F₃ : Frame [⟨at' S (Layout.oVar 1 1), 8⟩] u.mem s₃.mem := by rw [m₃]; exact frame_writeW (w := 64) _ _ _
    have D₁ : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 2584 ∨ 2592 ≤ o) →
        ∀ r ∈ [(⟨at' S (Layout.oVar 1 1), 8⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar11]; exact Offset.disjoint S (by omega) (by omega) (by omega)
    have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r10 → r ≠ .r11 → s₃.gpr r = t.gpr r :=
      fun r h1 h2 h3 h4 h5 h6 => by rw [g₃ _ h1, hu.gpr _ h1 h2 h3 h4 h5 h6]
    let R : List Region := initR p S ++ [⟨at' S (Layout.oVar 1 1), 8⟩]
    have FR : Frame R t.mem s₃.mem :=
      (hu.frame.mono fun r hr => List.mem_append_left _ hr).trans (F₃.mono fun r hr => List.mem_append_right _ hr)
    have hRd : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
        ((∀ c < 4, o + l ≤ Layout.laneA c + p.n + 16 ∨ Layout.laneA c + 2 * p.n + 32 ≤ o) ∧
          (o + l ≤ 2592 ∨ 2600 ≤ o)) → (o + l ≤ 2584 ∨ 2592 ≤ o) →
        ∀ r ∈ R, Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ h₃ r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact initR_disj hn32 S h₁ h₂ r hr
      · exact D₁ h₁ h₃ r hr
    refine ⟨⟨ht.1.of_frame hn32 hlen hstk (fun r hr => ?_) (by rw [r₃, hu.rd]) (by rw [w₃, hu.wr])
      (FR.sub fun r hr => ?_) FR (hRd (by rw [oDigits_eq]; omega) ⟨fun c hc => by rw [oDigits_eq, eA]; omega,
        by rw [oDigits_eq]; omega⟩ (by rw [oDigits_eq]; omega)), ?_, ?_⟩, fun k hk => ?_, c₃⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [initR, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
        rcases hr with ⟨c, hc, rfl⟩ | rfl
        · exact sub_changes hn32 S _ (Or.inl ⟨c, hc, by omega, by rw [eA]; omega⟩)
        · exact sub_changes hn32 S _ (Or.inr (Or.inr (Or.inr ⟨by rw [oVar12]; omega, by rw [oVar12]; omega⟩)))
      · simp only [List.mem_singleton] at hr; subst hr
        exact sub_changes hn32 S _ (Or.inr (Or.inr (Or.inr ⟨by rw [oVar11]; omega, by rw [oVar11]; omega⟩)))
    · rw [var_keep FR (hRd (by rw [oVar10]; omega) ⟨fun c hc => by rw [oVar10, eA]; omega,
        by rw [oVar10]; omega⟩ (by rw [oVar10]; omega)), ht.2]
    · rw [m₃]; exact Mem.readW_writeW_self64 _ _ _
    · rw [bytesAt_frame F₃ (D₁ (by rw [eA]; omega) (by rw [eA]; omega)) (by omega)]
      exact (hu.done k hk).fields
  have hsl : ∀ a, MB a → t₀ < 15 → WP isa (.loop (Impl.SlhDsa.X86_64.Verify.stepBody p f) .ne) a
      (GI p S sig sp idx dg c₀) := fun a ⟨hr, hf, _⟩ h15 =>
    wpLoop (Q := fun s' => XS p S sig sp idx dg s' ∧ s'.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
      sCont (fun m => m - 1) (s_step hn hl hfam hS hstk hsfit hss hsL hsb T ht hst hs63 hc₀') (15 - t₀)
      ⟨t₀, rfl, h15, hr, hf⟩
  have hite : ∀ a, MB a → WP isa (.ite .b (.loop (Impl.SlhDsa.X86_64.Verify.stepBody p f) .ne) (.block [])) a
      (GI p S sig sp idx dg c₀) := fun a ha =>
    WP.ite (decide (t₀ < 15)) ha.2.2 (fun h => hsl a ha (of_decide_eq_true h))
      (fun _ => WP.block_nil ⟨ha.1.xs, ha.1.v0⟩)
  have hrbx : ∀ a b, EP S c₀ a ∧ EP S c₀ b → ∀ r ∈ [Reg.rbx], a.gpr r = b.gpr r :=
    fun a b ⟨ha, hb⟩ r hr => by rw [List.mem_singleton] at hr; subst hr; rw [ha.1, hb.1]
  have hEa : ∀ a b, EP S c₀ a ∧ EP S c₀ b → X86_64.Taint.Agree (xT [] [Layout.oVar 1 0]) a b :=
    fun a b ⟨ha, hb⟩ => xT_agree ha.2.1 hb.2.1 ha.1 hb.1 (by simp) (hsl1 _ (by rw [oVar10]; omega)) fun o ho => by
      rw [List.mem_singleton] at ho; subst ho; rw [ha.2.2, hb.2.2]
  have hE : ∀ {k'}, k' < 4 → ∀ a, EP S c₀ a → _ := fun hk a ha => ep_end hn hl hk hc₀ ha
  unfold Impl.SlhDsa.X86_64.Verify.chainGroup
  refine relSeq (B₁ := LB) (B₂ := LB) (ct_lanes hn hl fun a b ⟨ha, hb⟩ =>
    xT_agree ha.1.wr hb.1.wr ha.1.bx hb.1.bx (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [ha.1.r13, hb.1.r13]) (hsl1 _ (by rw [oVar10]; omega))
      fun o ho => by rw [List.mem_singleton] at ho; subst ho; rw [ha.2, hb.2]) hLB hLB ?_
  refine relSeq (B₁ := MB) (B₂ := MB) (ct_mid fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [ha.bx, hb.bx]) hMB hMB ?_
  refine relSeq (B₁ := GI p S sig sp idx dg c₀) (B₂ := GI p S sig sp idx dg c₀) ?_ hite hite ?_
  · refine RelCT.ite (fun a b ⟨ha, hb⟩ => by show a.cf = b.cf; rw [ha.2.2, hb.2.2])
      (RelCT.mono (sl_ct (idx := idx) (dg := dg) hn hl hfam hS hstk hsfit hss hsL hsb T ht hst hs63 hc₀' (15 - t₀))
        (fun a b ⟨⟨ha, hb⟩, he⟩ => ?_) fun _ _ _ => trivial) (RelCT.block_nil fun _ _ _ => trivial)
    have h15 : t₀ < 15 := by
      have e : a.cf = some true := he
      rw [ha.2.2, Option.some.injEq] at e
      exact of_decide_eq_true e
    exact ⟨⟨t₀, rfl, h15, ha.1, ha.2.1⟩, ⟨t₀, rfl, h15, hb.1, hb.2.1⟩⟩
  -- the ends, lane by lane
  rw [List.range_succ, List.range_succ, List.range_succ, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton,
    List.flatMap_singleton, List.flatMap_singleton, List.append_assoc, List.append_assoc, List.append_assoc]
  have hGE : ∀ a, GI p S sig sp idx dg c₀ a → EP S c₀ a := fun a ha => ⟨ha.1.bx, ha.1.wr, ha.2⟩
  refine RelCT.mono (P := fun a b => EP S c₀ a ∧ EP S c₀ b) ?_ (fun a b ⟨ha, hb⟩ => ⟨hGE a ha, hGE b hb⟩)
    fun _ _ h => h
  refine RelCT.block_append (relSeq (ct_end hn hl (by decide) hEa) (hE (by decide)) (hE (by decide)) ?_)
  refine RelCT.block_append (relSeq (ct_end hn hl (by decide) hEa) (hE (by decide)) (hE (by decide)) ?_)
  refine RelCT.block_append (relSeq (ct_end hn hl (by decide) hEa) (hE (by decide)) (hE (by decide)) ?_)
  refine RelCT.block_append (relSeq (ct_end hn hl (by decide) hEa) (hE (by decide)) (hE (by decide)) ?_)
  exact ct_endfin _ hrbx

end

/-! ## The groups -/

/-- The invariant of the groups, at the measure `m = len - c₀`. -/
def GInv (p : Params) (S sig sp : Addr) (idx : Nat) (dg : Nat → Byte) (m : Nat) (t : State) : Prop :=
  ∃ c₀, m = p.len - c₀ ∧ c₀ < p.len ∧ GI p S sig sp idx dg c₀ t

/-- Whether the groups go on after the one at the measure `m`. -/
def gCont (p : Params) (m : Nat) : Bool := decide (p.len - m + 4 < p.len)

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hfam : p.family = .shake) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsL : p.len * p.n ≤ p.xmssSigLen) (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below sp stack))
  (hidx : idx < 2 ^ 32) (hD : ∀ c < p.len, (dg c).toNat ≤ 15)

include hn hl hfam hS hstk hsfit hss hsL hsb hidx hD in
/-- A group, in one run. -/
theorem g_step (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (m : Nat) (s : State) (hs : GInv p S sig sp idx dg m s) :
    WP isa (Impl.SlhDsa.X86_64.Verify.chainGroup p f) s fun s' => isa.eval .b s' = some (gCont p m) ∧
      (gCont p m = false → XS p S sig sp idx dg s') ∧
      (gCont p m = true → m - 4 < m ∧ GInv p S sig sp idx dg (m - 4) s') := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB := by
    rw [hl, show Layout.strideB = 2208 from rfl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have eB : Layout.laneB 0 = 3808 := rfl
  obtain ⟨c₀, rfl, hc₀, hx, hv0⟩ := hs
  obtain ⟨pk, a, henv⟩ := hx.env
  refine chainGroup_ok T ht hn hfam (by omega) hlen hlB hst hs63 hc₀ hidx hx.bx hx.r12 hx.r13 hv0 hx.hw hS
    (by rw [hx.sp]; exact hstk) henv hx.hsr hsfit hss hsL (by rw [hx.sp]; exact hsb)
    (fun c hc => by rw [hx.dig c hc]; exact hD c hc) fun t' g' r' w' v0' c' _ F' => ?_
  rw [hx.sp] at F'
  have hln : p.len * p.n ≤ 128 * 32 := Nat.mul_le_mul hlen hn32
  have hX : XS p S sig sp idx dg t' := hx.of_frame hn32 hlen hstk (fun r h => g' r (cs_sub r h)) r' w'
    (F'.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact chFrame_sub p S _ stack r hr
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
          Offset.sub S (e := Layout.laneB 0 + p.n + 16) (k := Layout.strideB - p.n - 16) (by omega) (by omega)⟩)
    F' fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact chFrame_disj hn32 hstk (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega) r hr
      · rw [List.mem_singleton] at hr; subst hr
        rw [oDigits_eq, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have e : gCont p (p.len - c₀) = decide (c₀ + 4 < p.len) := by
    simp only [gCont, show p.len - (p.len - c₀) = c₀ by omega]
  refine ⟨by show t'.cf = _; rw [c', e], fun _ => hX, fun hc => ⟨by omega, c₀ + 4, by omega, ?_, hX, v0'⟩⟩
  rw [e] at hc; exact of_decide_eq_true hc

include hn hl hfam hS hstk hsfit hss hsL hsb hidx hD in
/-- Two runs of the groups. -/
theorem gl_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (m : Nat) :
    RelCT isa (fun a b => GInv p S sig sp idx dg m a ∧ GInv p S sig sp idx dg m b)
      (.loop (Impl.SlhDsa.X86_64.Verify.chainGroup p f) .b)
      fun a b => XS p S sig sp idx dg a ∧ XS p S sig sp idx dg b := by
  refine relLoop (gCont p) (fun m => m - 4) (fun m => ?_)
    (g_step hn hl hfam hS hstk hsfit hss hsL hsb hidx hD T ht hst hs63)
    (g_step hn hl hfam hS hstk hsfit hss hsL hsb hidx hD T ht hst hs63) m
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨c₁, e₁, hc₁, r₁⟩, ⟨c₂, e₂, _, r₂⟩⟩ x₁ x₂
  obtain rfl : c₂ = c₁ := by omega
  exact gc_ct hn hl hfam hS hstk hsfit hss hsL hsb hidx T ht hst hs63 hc₁ _ _ _ _ _ _ ⟨r₁, r₂⟩ x₁ x₂

end

/-! ## The WOTS⁺ public key and the path -/

/-- The invariant of the path's heights, at the measure `m = h′ - z`. -/
def PInv (p : Params) (S sig sp : Addr) (idx : Nat) (dg : Nat → Byte) (m : Nat) (t : State) : Prop :=
  ∃ z, m = p.hp - z ∧ z < p.hp ∧ XS p S sig sp idx dg t ∧
    t.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z

/-- Whether the heights go on after the one at the measure `m`. -/
def pCont (p : Params) (m : Nat) : Bool := !decide (p.hp - m + 1 = p.hp)

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hfam : p.family = .shake) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below sp stack))
  (hidx : idx < 2 ^ 32) (hhp : p.hp ≤ 32)

include hn hl hfam hS hstk hidx in
/-- `wotsPk`, in one run. -/
theorem xs_wpk (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {t : State} (h : XS p S sig sp idx dg t) :
    WP isa (Impl.SlhDsa.X86_64.Verify.wotsPk p f) t (XS p S sig sp idx dg) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB := by
    rw [hl, show Layout.strideB = 2208 from rfl]; rcases hn with h | h | h <;> rw [h] <;> decide
  obtain ⟨pk, a, henv⟩ := h.env
  refine wotsPk_ok T ht hn hfam hlB hst hs63 hidx h.bx h.r12 h.hw hS (by rw [h.sp]; exact hstk) henv
    fun s' g' r' w' _ F' => ?_
  rw [h.sp] at F'
  exact h.of_frame hn32 hlen hstk (fun r h => g' r (cs_sub r h)) r' w' (F'.sub (xFrame_sub p S sp stack)) F'
    (xFrame_disj hn32 hstk (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega))

include hn hl hS hstk hidx in
/-- Two runs of `wotsPk`. -/
theorem w_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    RelCT isa (fun a b => XS p S sig sp idx dg a ∧ XS p S sig sp idx dg b)
      (Impl.SlhDsa.X86_64.Verify.wotsPk p f) fun _ _ => True := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB := by
    rw [hl, show Layout.strideB = 2208 from rfl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have hm8 : (p.n + 32 + p.len * p.n) % 8 = 0 := by rw [hl]; rcases hn with h | h | h <;> rw [h]
  have eB : Layout.laneB 0 = 3808 := rfl
  have hrbx : ∀ a b, XS p S sig sp idx dg a ∧ XS p S sig sp idx dg b → ∀ r ∈ [Reg.rbx], a.gpr r = b.gpr r :=
    fun a b ⟨ha, hb⟩ r hr => by rw [List.mem_singleton] at hr; subst hr; rw [ha.bx, hb.bx]
  have hwf : ∀ a, XS p S sig sp idx dg a → WP isa (.block
      (Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 1 ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
        Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0))
      a (XS p S sig sp idx dg) := fun a ha =>
    wfields_ok' hn hidx ha.bx ha.r12 ha.hw fun s' g' r' w' _ F' =>
      ha.of_frame hn32 hlen hstk (fun r hr => g' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) r' w'
        (F'.sub fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
            Offset.sub S (e := Layout.laneB 0 + p.n + 16) (k := Layout.strideB - p.n - 16) (by omega)
              (by simp only [Layout.strideB]; omega)⟩) F' fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          rw [oDigits_eq, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  unfold Impl.SlhDsa.X86_64.Verify.wotsPk
  refine relSeq (ct_wf hn hl hrbx) hwf hwf ?_
  rw [ht]
  have hcall : ∀ a, XS p S sig sp idx dg a → WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ f.t4name T.code
      Layout.oB Layout.strideB (p.n + 32 + p.len * p.n)) a (XS p S sig sp idx dg) := fun a ha =>
    WP.mono (xs_call hn hl hS hstk T f.t4name hst hs63 (Or.inr ⟨rfl, rfl⟩) (by omega) hm8 hlB ha)
      fun _ h => h.1
  refine relSeq (t4ctG T hn f.t4name hst hs63 (Or.inr ⟨rfl, rfl⟩) (by omega) hm8 hlB hS hstk
      (fun a ha => ⟨ha.bx, ha.hw, ha.sp, ha.rc⟩) (ct_args hn hl (Or.inr ⟨rfl, rfl⟩) _ hrbx)) hcall hcall ?_
  exact ct_wcp hn hl hrbx

include hn hl hstk in
/-- Variable 3 ← 0, in one run. -/
theorem xs_b4 (hh : 0 < p.hp) {t : State} (h : XS p S sig sp idx dg t) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Verify.xv 3) .rax]) t
      (PInv p S sig sp idx dg (p.hp - 0)) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  refine Proof.Sha3.X86_64.wp_mov32i fun s₅ u₅ => Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 1 3))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, u₅.other _ (by decide), h.bx])
    (by rw [u₅.wr, oVar13]; exact in_scr h.hw (by omega)) fun s₆ g₆ m₆ r₆ w₆ => WP.block_nil ?_
  have hm₆ : s₆.mem = t.mem.writeW (at' S (Layout.oVar 1 3)) (BitVec.ofNat 64 0) := by
    rw [m₆, u₅.gpr, u₅.mem]; rfl
  have F : Frame [⟨at' S (Layout.oVar 1 3), 8⟩] t.mem s₆.mem := by rw [hm₆]; exact frame_writeW (w := 64) _ _ _
  have hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp], s₆.gpr r = t.gpr r := by
    intro r hr
    rw [g₆]; apply u₅.other
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨0, rfl, hh, h.of_frame hn32 hlen hstk hg (by rw [r₆, u₅.rd]) (by rw [w₆, u₅.wr])
    (F.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact sub_changes hn32 S _ (Or.inr (Or.inr (Or.inr ⟨by rw [oVar13]; omega, by rw [oVar13]; omega⟩)))) F
    (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [oDigits_eq, oVar13]; exact Offset.disjoint S (by omega) (by omega) (by omega)), ?_⟩
  rw [hm₆]; exact Mem.readW_writeW_self64 _ _ _

end

/-- What a call of `thash4` needs of a run. -/
def PP (S sp : Addr) (u : State) : Prop :=
  u.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr ∧ u.gpr .rsp = sp ∧ RcTable u.mem S

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {dg : Nat → Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hfam : p.family = .shake) {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below sp stack))
  (hidx : idx < 2 ^ 32) (hhp : p.hp ≤ 32)

include hn hl hstk hsfit hss hidx hhp in
/-- A height of the path up to its call, in one run. -/
theorem pp_ok {z : Nat} (hz : z < p.hp) {t : State} (h : XS p S sig sp idx dg t)
    (hv3 : t.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z) :
    WP isa (.seq (.seq (.block (([.mov .rcx (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .mov .rax (.reg .r12),
        .shiftCl .shr .rax, .mov .rsi (.reg .rcx)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rsi .rdx ++
        ([.alu .add .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (p.len * p.n))), .alu .and .rax (.imm 1)] : List Instr)))
      (.ite .e
        (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n)
          .rsi 0 (p.n / 8)))
        (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rbx
            (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8) ++
          Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)))))
      (.block (Impl.SlhDsa.X86_64.setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 2 ++
        Impl.SlhDsa.X86_64.setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) 0 ++
        ([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .alu .add .r10 (.imm 1)] : List Instr) ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .mov .r11 (.reg .r12), .shiftCl .shr .r11] : List Instr) ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11)))
      t (PP S sp) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen31 : p.len * p.n < 2 ^ 31 := by rw [hl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have hxs : p.xmssSigLen = (p.len + p.hp) * p.n := rfl
  have hzn : p.len * p.n + z * p.n + p.n ≤ p.xmssSigLen := by
    rw [hxs, Nat.add_mul, Nat.add_assoc, ← Nat.succ_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hz) _
  have ha0 : Layout.laneA 0 = 3296 := rfl
  obtain ⟨pk, a, henv⟩ := h.env
  refine WP.seq (order_ok hn hlen31 hidx (by omega) h.bx h.r12 h.r13 hv3 h.hw
    (fun j hj => ⟨_, List.mem_append_left _ h.hsr, by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base sig (by omega_using [hzn, hj, hn]) (by omega_using [hzn, hsfit, hj, hn])⟩)
    (hss.sub_left (Offset.sub_base sig hzn)) fun s₂ g₂ r₂ w₂ _ fr₂ => ?_)
  have hb₂ : s₂.gpr .rbx = S := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.bx]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 idx := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.r12]
  have hv3₂ : s₂.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z := by
    rw [var_keep fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [oVar13]
      exact Offset.disjoint S (by omega) (by omega) (by omega), hv3]
  refine adrs_ok' hn hidx (by omega) hb₂ h12₂ hv3₂ (by rw [w₂]; exact h.hw) fun s₃ g₃ r₃ w₃ _ fr₃ => ?_
  have F : Frame (changes p S ++ [below sp stack]) t.mem s₃.mem :=
    (fr₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_changes hn32 S _ (Or.inl ⟨0, by decide, by omega, by omega⟩)).trans
      (fr₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_changes hn32 S _ (Or.inl ⟨0, by decide, by omega, by omega⟩))
  refine ⟨by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hb₂], by rw [w₃, w₂]; exact h.hw,
    by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide),
      h.sp], (Env.of_frame hn32 henv F hstk).rc⟩

include hn hl hfam hS hstk hsfit hss hidx hhp in
/-- A height of the path, in one run. -/
theorem p_step (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (m : Nat) (s : State) (hs : PInv p S sig sp idx dg m s) :
    WP isa (Impl.SlhDsa.X86_64.Verify.pathBody p f) s fun s' => isa.eval .ne s' = some (pCont p m) ∧
      (pCont p m = false → XS p S sig sp idx dg s') ∧
      (pCont p m = true → m - 1 < m ∧ PInv p S sig sp idx dg (m - 1) s') := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlen : p.len ≤ 128 := by omega_using [hn, hl]
  have hlen31 : p.len * p.n < 2 ^ 31 := by rw [hl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have hxs : p.xmssSigLen = (p.len + p.hp) * p.n := rfl
  obtain ⟨z, rfl, hz, hx, hv3⟩ := hs
  have hzn : p.len * p.n + z * p.n + p.n ≤ p.xmssSigLen := by
    rw [hxs, Nat.add_mul, Nat.add_assoc, ← Nat.succ_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hz) _
  obtain ⟨pk, a, henv⟩ := hx.env
  refine pathBody_ok T ht hn hfam hlen31 (by omega) hst hs63 hidx hz hx.bx hx.r12 hx.r13 hv3 hx.hw hS
    (by rw [hx.sp]; exact hstk) henv
    (fun j hj => ⟨_, List.mem_append_left _ hx.hsr, by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base sig (by omega_using [hzn, hj, hn]) (by omega_using [hzn, hsfit, hj, hn])⟩)
    (hss.sub_left (Offset.sub_base sig hzn)) fun s' g' r' w' v3' z' _ F' => ?_
  rw [hx.sp] at F'
  have hX : XS p S sig sp idx dg s' := hx.of_frame hn32 hlen hstk (fun r h => g' r (cs_sub r h)) r' w'
    (F'.sub (chFrame_sub p S sp stack)) F'
    (chFrame_disj hn32 hstk (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega))
  have e : pCont p (p.hp - z) = !decide (z + 1 = p.hp) := by
    simp only [pCont, show p.hp - (p.hp - z) = z by omega]
  refine ⟨by show s'.zf.map (!·) = _; rw [z', e]; rfl, fun _ => hX, fun hc => ⟨by omega, z + 1, by omega, ?_, hX, v3'⟩⟩
  rw [e] at hc
  have : ¬ z + 1 = p.hp := fun h => by simp [h] at hc
  omega

include hn hl hS hstk hsfit hss hidx hhp in
/-- Two runs of a height of the path. -/
theorem pb_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {z : Nat} (hz : z < p.hp) :
    RelCT isa (fun a b => (XS p S sig sp idx dg a ∧ a.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z) ∧
        (XS p S sig sp idx dg b ∧ b.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z))
      (Impl.SlhDsa.X86_64.Verify.pathBody p f) fun _ _ => True := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hm8 : (3 * p.n + 32) % 8 = 0 := by omega_using [hn]
  have hPP : ∀ a, XS p S sig sp idx dg a ∧ a.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z →
      WP isa _ a (PP S sp) := fun a ha => pp_ok hn hl hstk hsfit hss hidx hhp hz ha.1 ha.2
  have hrbx : ∀ a b, PP S sp a ∧ PP S sp b → ∀ r ∈ [Reg.rbx], a.gpr r = b.gpr r :=
    fun a b ⟨ha, hb⟩ r hr => by rw [List.mem_singleton] at hr; subst hr; rw [ha.1, hb.1]
  have hcall : ∀ a, PP S sp a → WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ f.t4name T.code
      Layout.oA Layout.strideA (3 * p.n + 32)) a (fun u => u.gpr .rbx = S) := fun a ha =>
    lanes_ok T f.t4name hn hst hs63 (Or.inl ⟨rfl, rfl⟩) (by omega) hm8 (by simp only [Layout.strideA]; omega) ha.1
      ha.2.1 hS (by rw [ha.2.2.1]; exact hstk) ha.2.2.2 fun t' _ _ g' _ _ _ => by rw [g' _ (by decide), ha.1]
  unfold Impl.SlhDsa.X86_64.Verify.pathBody
  refine RelCT.assoc (RelCT.assoc ?_)
  refine relSeq (B₁ := PP S sp) (B₂ := PP S sp) (ct_ppre hn hl fun a b ⟨ha, hb⟩ =>
    xT_agree ha.1.wr hb.1.wr ha.1.bx hb.1.bx (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [ha.1.r12, hb.1.r12]
      · rw [ha.1.r13, hb.1.r13]) (hsl1 _ (by rw [oVar13]; omega))
      fun o ho => by rw [List.mem_singleton] at ho; subst ho; rw [ha.2, hb.2]) hPP hPP ?_
  rw [ht]
  refine relSeq (B₁ := fun u => u.gpr .rbx = S) (B₂ := fun u => u.gpr .rbx = S)
    (t4ctG T hn f.t4name hst hs63 (Or.inl ⟨rfl, rfl⟩) (by omega) hm8 (by simp only [Layout.strideA]; omega) hS hstk
      (fun a ha => ha) (ct_args hn hl (Or.inl ⟨rfl, rfl⟩) _ hrbx)) hcall hcall ?_
  exact ct_pfin p.hp fun a b ⟨ha, hb⟩ r hr => by rw [List.mem_singleton] at hr; subst hr; rw [ha, hb]

include hn hl hfam hS hstk hsfit hss hidx hhp in
/-- Two runs of the path. -/
theorem pl_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (m : Nat) :
    RelCT isa (fun a b => PInv p S sig sp idx dg m a ∧ PInv p S sig sp idx dg m b)
      (.loop (Impl.SlhDsa.X86_64.Verify.pathBody p f) .ne)
      fun a b => XS p S sig sp idx dg a ∧ XS p S sig sp idx dg b := by
  refine relLoop (pCont p) (fun m => m - 1) (fun m => ?_)
    (p_step hn hl hfam hS hstk hsfit hss hidx hhp T ht hst hs63)
    (p_step hn hl hfam hS hstk hsfit hss hidx hhp T ht hst hs63) m
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨z₁, e₁, hz₁, x₁, v₁⟩, ⟨z₂, e₂, _, x₂, v₂⟩⟩ c₁ c₂
  obtain rfl : z₂ = z₁ := by omega
  exact pb_ct hn hl hS hstk hsfit hss hidx hhp T ht hst hs63 hz₁ _ _ _ _ _ _ ⟨⟨x₁, v₁⟩, ⟨x₂, v₂⟩⟩ c₁ c₂

end

/-! ## `xmssPk` -/

/-- The digits of `M`, as bytes. -/
def dgOf (p : Params) (M : List Byte) (c : Nat) : Byte := BitVec.ofNat 8 ((wotsDigits p M).getD c 0)

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hw4 : p.lgw = 4) {stack : Nat}

include hn hl hw4 in
/-- The prologue, in one run: the run after it, at group 0. -/
theorem xs_pro {s : State} (hpre : (xmssPkContract p stack).pre s) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.xpro ++
      Impl.SlhDsa.X86_64.Xmss.digits (Impl.SlhDsa.X86_64.Shake.layout p) ++
      ([.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Verify.xv 0) .rax] : List Instr))) s
      (GInv p (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsp) (s.gpr .rsi).toNat
        (dgOf p (bytesAt s.mem (at' (s.gpr .rdi) Layout.oMsg) p.n)) (p.len - 0)) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eD : Layout.oDigits = 30368 := rfl
  obtain ⟨R, ⟨pk, a, henv⟩, _⟩ := hpre
  have hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [R.wr_eq]; exact List.mem_cons_self ..
  refine WP.mono (xpre_ok hn hw4 hw) fun u h₂ => ⟨0, rfl, by omega, ⟨h₂.bx, ?_, h₂.r13, h₂.r14, ?_, ?_, ?_, ?_, ?_⟩,
    h₂.v0⟩
  · rw [h₂.r12, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact h₂.cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [h₂.rd, R.rd_eq]
  · rw [h₂.wr, R.wr_eq]
  · intro c hc
    have h16 := wotsDigits_lt p hw4 hn (bytesAt s.mem (at' (s.gpr .rdi) Layout.oMsg) p.n) c
    apply BitVec.eq_of_toNat_eq
    rw [h₂.digits c hc, dgOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · refine ⟨pk, a, Env.of_frame hn32 henv (h₂.frame.sub fun r hr => ?_) R.stk_scr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub _ (by rw [oSave1]; simp only [Layout.oVars]; omega) (by rw [oSave1]; simp only [Layout.oVars]; omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub _ (by rw [oVar10]; simp only [Layout.oVars]; omega) (by rw [oVar10]; simp only [Layout.oVars]; omega)⟩

end

section
variable {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} {S sig sp : Addr} {idx : Nat} {M : List Byte}
  (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3) (hfam : p.family = .shake) (hw4 : p.lgw = 4)
  {stack : Nat}
  (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
  (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
  (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below sp stack))
  (hidx : idx < 2 ^ 32) (hhp : 0 < p.hp) (hhp' : p.hp ≤ 32)

/-- A run of `xmssPk` from its precondition, with the arguments `S`, `idx`,
`sig`, the stack pointer `sp` and the message `M` at `oMsg`. -/
def Init (p : Params) (stack : Nat) (S sig sp : Addr) (idx : Nat) (M : List Byte) (s : State) : Prop :=
  (xmssPkContract p stack).pre s ∧ s.gpr .rdi = S ∧ s.gpr .rdx = sig ∧ s.gpr .rsp = sp ∧
    (s.gpr .rsi).toNat = idx ∧ bytesAt s.mem (at' S Layout.oMsg) p.n = M

include hn hl hfam hw4 hS hstk hsfit hss hsb hidx hhp hhp' in
/-- Two runs of `xmssPk` with the same arguments. -/
theorem xr_ct (T : Thash4Impl p.n) (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    RelCT isa (fun a b => Init p stack S sig sp idx M a ∧ Init p stack S sig sp idx M b)
      (Impl.SlhDsa.X86_64.Verify.xmssPk p f) fun _ _ => True := by
  have hxs : p.xmssSigLen = (p.len + p.hp) * p.n := rfl
  have hsL : p.len * p.n ≤ p.xmssSigLen := by rw [hxs, Nat.add_mul]; omega
  have hD : ∀ c < p.len, (dgOf p M c).toNat ≤ 15 := fun c _ => by
    have := wotsDigits_lt p hw4 hn M c
    rw [dgOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hpro : ∀ a, Init p stack S sig sp idx M a → WP isa _ a (GInv p S sig sp idx (dgOf p M) (p.len - 0)) :=
    fun a ⟨hp, e1, e2, e3, e4, e5⟩ => by
      have h := xs_pro hn hl hw4 hp
      rw [e1, e2, e3, e4, e5] at h; exact h
  have hgl : ∀ a, GInv p S sig sp idx (dgOf p M) (p.len - 0) a →
      WP isa (.loop (Impl.SlhDsa.X86_64.Verify.chainGroup p f) .b) a (XS p S sig sp idx (dgOf p M)) := fun a ha =>
    wpLoop (gCont p) (fun m => m - 4) (g_step hn hl hfam hS hstk hsfit hss hsL hsb hidx hD T ht hst hs63) _ ha
  have hpl : ∀ a, PInv p S sig sp idx (dgOf p M) (p.hp - 0) a →
      WP isa (.loop (Impl.SlhDsa.X86_64.Verify.pathBody p f) .ne) a (XS p S sig sp idx (dgOf p M)) := fun a ha =>
    wpLoop (pCont p) (fun m => m - 1) (p_step hn hl hfam hS hstk hsfit hss hidx hhp' T ht hst hs63) _ ha
  have hwk : ∀ a, XS p S sig sp idx (dgOf p M) a → WP isa (Impl.SlhDsa.X86_64.Verify.wotsPk p f) a
      (XS p S sig sp idx (dgOf p M)) := fun a ha => xs_wpk hn hl hfam hS hstk hidx T ht hst hs63 ha
  have hb4 : ∀ a, XS p S sig sp idx (dgOf p M) a → WP isa _ a (PInv p S sig sp idx (dgOf p M) (p.hp - 0)) :=
    fun a ha => xs_b4 hn hl hstk hhp ha
  have hrbx : ∀ a b, XS p S sig sp idx (dgOf p M) a ∧ XS p S sig sp idx (dgOf p M) b →
      ∀ r ∈ [Reg.rbx], a.gpr r = b.gpr r :=
    fun a b ⟨ha, hb⟩ r hr => by rw [List.mem_singleton] at hr; subst hr; rw [ha.bx, hb.bx]
  unfold Impl.SlhDsa.X86_64.Verify.xmssPk
  refine relSeq (ct_pro hn hl fun a b ⟨ha, hb⟩ r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [ha.2.1, hb.2.1]) hpro hpro ?_
  refine relSeq (RelCT.mono (gl_ct hn hl hfam hS hstk hsfit hss hsL hsb hidx hD T ht hst hs63 _) (fun _ _ h => h)
    fun _ _ _ => trivial) hgl hgl ?_
  refine relSeq (w_ct hn hl hS hstk hidx T ht hst hs63) hwk hwk ?_
  refine relSeq (ct_b4 hrbx) hb4 hb4 ?_
  refine relSeq (RelCT.mono (pl_ct hn hl hfam hS hstk hsfit hss hidx hhp' T ht hst hs63 _) (fun _ _ h => h)
    fun _ _ _ => trivial) hpl hpl ?_
  exact ct_epi hn hl fun a b ⟨ha, hb⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [ha.bx, hb.bx]
    · rw [ha.r14, hb.r14]

end

/-- `xmssPk` is constant time: two runs from states of its precondition
that agree on its public data leak the same trace. -/
theorem xmssPk_ct {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hw4 : p.lgw = 4)
    (hhp : 0 < p.hp) (hhp' : p.hp ≤ 32) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    ConstantTime isa (xmssPkContract p stack).pre (xmssPkContract p stack).pub
      (Impl.SlhDsa.X86_64.Verify.xmssPk p f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, e1, e2, e3, e4, _, e6⟩ x₁ x₂
  have R := h₁.1
  have hidx : (s₁.gpr .rsi).toNat < 2 ^ 32 :=
    Nat.lt_of_lt_of_le h₁.2.2 (Nat.pow_le_pow_right (by decide) hhp')
  have hsr : (⟨s₁.gpr .rdx, p.xmssSigLen⟩ : Region) ∈ s₁.rd := by rw [R.rd_eq]; exact List.mem_singleton_self _
  have e6' : bytesAt s₂.mem (at' (s₁.gpr .rdi) Layout.oMsg) p.n = bytesAt s₁.mem (at' (s₁.gpr .rdi) Layout.oMsg) p.n := by
    rw [e6, e1]
  exact xr_ct hn (len_eq p hw4 hn) hfam hw4 R.scr_fit R.stk_scr (R.rd_fit _ (by rw [← R.rd_eq]; exact hsr))
    (R.rd_scr _ (by rw [← R.rd_eq]; exact hsr)) (R.stk_rd _ (by rw [← R.rd_eq]; exact hsr)).symm hidx hhp hhp'
    (M := bytesAt s₁.mem (at' (s₁.gpr .rdi) Layout.oMsg) p.n) T ht hst hs63 s₁ s₂ t₁ t₂ s₁' s₂'
    ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, e1.symm, e3.symm, e4.symm, by rw [e2], e6'⟩⟩ x₁ x₂

/-- No instruction of `xmssPk` loads MXCSR, if none of `thash4`'s does. -/
theorem xmssPk_nm' {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (hT : f.t4.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Impl.SlhDsa.X86_64.Verify.xmssPk p f).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq] at hT ⊢
  simp only [Impl.SlhDsa.X86_64.Verify.xmssPk, Impl.SlhDsa.X86_64.Verify.chainGroup,
    Impl.SlhDsa.X86_64.Verify.stepBody, Impl.SlhDsa.X86_64.Verify.restoreLane, Impl.SlhDsa.X86_64.Verify.wotsPk,
    Impl.SlhDsa.X86_64.Verify.pathBody, Impl.SlhDsa.X86_64.thashCall, Impl.SlhDsa.X86_64.thashArgs,
    Impl.SlhDsa.X86_64.Verify.chainLanes, Impl.SlhDsa.X86_64.Verify.chainOf, Impl.SlhDsa.X86_64.Verify.chainSig,
    Impl.SlhDsa.X86_64.Verify.xpro, Impl.SlhDsa.X86_64.Xmss.digits,
    Impl.SlhDsa.X86_64.saveRegs, Impl.SlhDsa.X86_64.restoreRegs, Impl.SlhDsa.X86_64.setField,
    Impl.SlhDsa.X86_64.setFieldR, instrs, hT, List.all_append, List.all_flatMap, List.all_map,
    Levels.mulN_nm, Levels.copyWords_nm, Bool.and_true, Bool.true_and]
  simp [loadsMxcsr, Impl.SlhDsa.X86_64.Xmss.digitByte]

/-- `xmssPk` meets its contract. -/
theorem xmssPk_verified {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hw4 : p.lgw = 4)
    (hhp : 0 < p.hp) (hhp' : p.hp ≤ 32) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (hT : T.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Verify.xmssPk p f) (xmssPkContract p stack) :=
  ⟨xmssPk_correct T ht hn hfam hw4 hhp hhp' hst hs63 (xmssPk_nm' (by rw [ht]; exact hT)),
    xmssPk_ct T ht hn hfam hw4 hhp hhp' hst hs63,
    ⟨xsat p, xsat_pre (by omega_using [hn]) (by rw [len_eq p hw4 hn]; omega_using [hn]) hhp' hs63⟩⟩

@[simp] theorem cp_hp (n hp : Nat) : (cp n hp).hp = hp := rfl

/-- `xmssPk`'s code depends on `p` only through `n`, `len` and `h′`. -/
theorem xcode {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hl : p.len = 2 * p.n + 3)
    (g : Impl.SlhDsa.X86_64.Shake.Fns) :
    Impl.SlhDsa.X86_64.Verify.xmssPk p g = Impl.SlhDsa.X86_64.Verify.xmssPk (cp p.n p.hp) g := by
  simp only [Impl.SlhDsa.X86_64.Verify.xmssPk, Impl.SlhDsa.X86_64.Verify.chainGroup,
    Impl.SlhDsa.X86_64.Verify.stepBody, Impl.SlhDsa.X86_64.Verify.restoreLane, Impl.SlhDsa.X86_64.Verify.wotsPk,
    Impl.SlhDsa.X86_64.Verify.pathBody, Impl.SlhDsa.X86_64.Verify.chainLanes, Impl.SlhDsa.X86_64.Verify.chainOf,
    Impl.SlhDsa.X86_64.Verify.chainSig, Impl.SlhDsa.X86_64.Shake.layout, hl, cp_n, cp_hp, cp_len hn]

/-- No block of `xmssPk` writes `rsp`. -/
theorem xmssPk_own_nosp {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hl : p.len = 2 * p.n + 3) :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.xmssPk p { f with t4 := .block [] }), (!Taint.clobbers i .rsp) = true := by
  rw [xcode hn hl]
  apply List.all_eq_true.mp
  rcases hn with h | h | h <;> rw [h] <;> kernel_rfl

/-- A call of `xmssPk`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem xmssPkcall_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hw4 : p.lgw = 4)
    (hhp : 0 < p.hp) (hhp' : p.hp ≤ 32) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (hT : T.code.allInstrs (fun i => !loadsMxcsr i) = true) (name : String) {s : State}
    {rd wr : List Region} (hpre : (xmssPkContract p stack).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (T.code.depth + 2))]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (xmssPkContract p stack).post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call name (Impl.SlhDsa.X86_64.Verify.xmssPk p f)) s Q := by
  have hd := T.depth_le
  have hdep := xmssPk_depth p f
  rw [ht] at hdep
  exact WP.call_mx (xmssPk_verified T ht hn hfam hw4 hhp hhp' hst hs63 hT).1
    (xmssPk_nosp (by rw [ht]; exact T.nosp) (xmssPk_own_nosp hn (len_eq p hw4 hn)))
    (by rw [hdep]; omega_using [hd]) hpre hc hw fun s' h₁ h₂ h₃ h₄ _ h₆ h₇ =>
      hQ s' h₁ h₂ h₃ (by rw [hdep] at h₄; exact h₄) h₆ h₇

end VG.Proof.SlhDsa.X86_64.XmssCT
