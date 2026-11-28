module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsPk` is constant time

Two runs of `forsPk` from states of its precondition that agree on its public
data leak the same trace (`forsPk_ct`). Each run keeps the facts of its own
correctness; the registers and the variables of frame 2 the taint analysis
needs public hold the same values in both (`FC`), and so do the conditions of
the branches and loops, functions of those values and of the public FORS
indices (`I`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.ForsCT

open VG VG.X86_64
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs restoreRegs setField setFieldR copyWords thashArgs)
open VG.Proof.SlhDsa.X86_64.Levels (relSeq relLoop sx_ofNat add_add in_scr in_scr' wp_add)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)

theorem eval_ne' (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_b' (s : State) : isa.eval .b s = s.cf := rfl
theorem eval_e' (s : State) : isa.eval .e s = s.zf := rfl

/-! ## A call of `thash4` -/

/-- The arguments of a call on the lanes at `o`, `st` apart. -/
theorem fargs_ok {p : Params} (hn : p.n ≤ 32) {S : Addr} {o st len : Nat} (ho : o < 2 ^ 31) (hst : st < 2 ^ 31)
    (hlen : len < 2 ^ 31) {t : State} (hbx : t.gpr .rbx = S) {Q : State → Prop}
    (k : ∀ u, u.gpr .rdi = at' S o → u.gpr .rsi = BitVec.ofNat 64 st →
      u.gpr .rdx = BitVec.ofNat 64 len → u.gpr .rcx = at' S o + BitVec.ofNat 64 (p.n + 32) → u.gpr .r8 = S →
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) →
      u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → Q u) :
    WP isa (.block (thashArgs ⟨p.n, p.len⟩ o st len)) t Q := by
  simp only [thashArgs, Impl.SlhDsa.X86_64.Layout.msgOff]
  refine wp_mov fun u₁ v₁ => wp_addi fun u₂ v₂ => wp_mov32i fun u₃ v₃ => wp_mov32i fun u₄ v₄ =>
    wp_mov fun u₅ v₅ => wp_addi fun u₆ v₆ => wp_mov fun u v => WP.block_nil ?_
  have hdi2 : u₂.gpr .rdi = at' S o := by rw [v₂.gpr, v₁.gpr, hbx, sx_ofNat ho]
  refine k u ?_ ?_ ?_ ?_ ?_ (fun g h1 h2 h3 h4 h5 => ?_) (by rw [v.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem])
    (by rw [v.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]) (by rw [v.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr])
  · rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), hdi2]
  · rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      setw_ofNat32 (by omega)]
  · rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, setw_ofNat32 (by omega)]
  · rw [v.other _ (by decide), v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), hdi2,
      sx_ofNat (by omega)]
  · rw [v.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hbx]
  · rw [v.other _ h5, v₆.other _ h4, v₅.other _ h4, v₄.other _ h3, v₃.other _ h2, v₂.other _ h1, v₁.other _ h1]

/-- What a call of `thash4` needs of each run. -/
structure CB (S sp : Addr) (stack : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  rsp : t.gpr .rsp = sp
  wr : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  rc : RcTable t.mem S

/-- A call of `thash4` on the lanes `A` or `B`, in two runs each with `CB`. -/
theorem fcall_rel {p : Params} (hp : P6 p) (T : Thash4Impl p.n) (name : String) {stack : Nat}
    (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {S sp : Addr} {o st len : Nat}
    (hl : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    {A₁ A₂ : State → Prop} (h₁ : ∀ a, A₁ a → CB S sp stack a) (h₂ : ∀ b, A₂ b → CB S sp stack b) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code o st len)
      fun _ _ => True := by
  have hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32 := by
    rcases hp with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hoS : o + 4 * st ≤ 12640 ∧ o < 2 ^ 31 ∧ st < 2 ^ 31 ∧ 3296 ≤ o ∧ 2 * p.n + 32 ≤ st := by
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Layout.oA, Layout.oB, Layout.strideA, Layout.strideB] <;>
      omega_using [hn32]
  obtain ⟨hoS, ho, hst', ho3, hout⟩ := hoS
  let F : State → Prop := fun u => ∃ t, CB S sp stack t ∧ u.gpr .rdi = at' S o ∧
    u.gpr .rsi = BitVec.ofNat 64 st ∧ u.gpr .rdx = BitVec.ofNat 64 len ∧
    u.gpr .rcx = at' S o + BitVec.ofNat 64 (p.n + 32) ∧ u.gpr .r8 = S ∧
    (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) ∧
    u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr
  have hw : ∀ a, CB S sp stack a → WP isa (.block (thashArgs ⟨p.n, p.len⟩ o st len)) a F := fun a ha =>
    fargs_ok hn32 ho hst' (by omega) ha.bx fun u e1 e2 e3 e4 e5 eg em er ew => ⟨a, ha, e1, e2, e3, e4, e5, eg, em, er, ew⟩
  unfold Impl.SlhDsa.X86_64.thashCall
  refine relSeq (B₁ := F) (B₂ := F) (ct_fargs hp hl len fun a b h => ?_) (fun a h => hw a (h₁ a h))
    (fun b h => hw b (h₂ b h)) ?_
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [(h₁ a h.1).bx, (h₂ b h.2).bx]
  have pre : ∀ u, F u → (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]) ∧
      Covers ([] ++ [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩] u.wr ∧ u.gpr .rsp = sp := by
    intro u ⟨t, ht, e1, e2, e3, e4, e5, eg, em, er, ew⟩
    have hsp : u.gpr .rsp = sp := by rw [eg _ (by decide) (by decide) (by decide) (by decide) (by decide), ht.rsp]
    have hb8 : Region.Sub (below (u.gpr .rsp) (T.stack + 8)) (below sp stack) := by
      rw [hsp]; exact below_sub (by omega_using [hst]) (by omega_using [hs63])
    have hLs : Region.Sub ⟨at' S o, 4 * st⟩ ⟨S, 2 ^ 16⟩ := Offset.sub_base S (by omega_using [hoS])
    have hWs : Region.Sub ⟨S, workLen⟩ ⟨S, 2 ^ 16⟩ := Region.sub_prefix (by simp [workLen])
    have hw' : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [ew]; exact ht.wr
    have hcov : Covers [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩] u.wr := Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hw', o, rfl, by show o + 4 * st ≤ 2 ^ 16; omega_using [hoS]⟩
      · exact ⟨_, hw', 0, Levels.scr0 S, by simp [workLen]⟩
    refine ⟨thash4_entry T e1 (by rw [e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      (by rw [e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) e4 e5 hlp hlm hll (by omega_using [hout])
      (by rw [Levels.toNat_at (by omega_using [ht.fit, hoS])]; omega_using [ht.fit, hoS])
      (by simp only [workLen]; omega_using [ht.fit])
      (Offset.disjoint_base S (by simp only [workLen]; omega_using [ho3]) (by omega_using [hoS]))
      ((ht.stk.sub_left hb8).sub_right hLs) ((ht.stk.sub_left hb8).sub_right hWs) (by rw [em]; exact ht.rc),
      by rw [List.nil_append]; exact Covers.right hcov, hcov, hsp⟩
  refine RelCT.call T.verified.1 T.verified.2.1 [] [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩] fun a b ⟨ha, hb⟩ => ?_
  obtain ⟨p₁, c₁, w₁, s₁⟩ := pre a ha
  obtain ⟨p₂, c₂, w₂, s₂⟩ := pre b hb
  obtain ⟨_, _, a1, a2, a3, a4, a5, _⟩ := ha
  obtain ⟨_, _, b1, b2, b3, b4, b5, _⟩ := hb
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, by rw [s₁, s₂]⟩ <;>
    simp only [State.withRegions_gpr, State.callEntry_rsp]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a1, b1]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a2, b2]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a3, b3]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a4, b4]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a5, b5]
  · rw [s₁, s₂]

/-! ## A lane of a height -/

/-- What a lane of a height needs of each run, at height `z` of the group from `t₀`. -/
structure LP (p : Params) (S sig : Addr) (t₀ z : Nat) (I : Nat → Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r14 : t.gpr .r14 = sig
  wr : t.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]
  rd : (⟨sig, p.forsSigLen⟩ : Region) ∈ t.rd
  sfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64
  sss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩
  v0 : t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z
  fidx : ∀ i < p.k, t.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (I i)
  ia : ∀ i < p.k, I i < 2 ^ p.a
  z : z < p.a
  t₀ : t₀ + 4 < 2 ^ 31

theorem LP.hw {p : Params} {S sig : Addr} {t₀ z : Nat} {I : Nat → Nat} {t : State} (h : LP p S sig t₀ z I t) :
    (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..

/-- The path's node `z` of lane `k`'s tree. -/
abbrev auOf (p : Params) (sig : Addr) (t₀ k' z : Nat) : Addr :=
  sig + BitVec.ofNat 64 (p.n * (min (t₀ + k') (p.k - 1) * (p.a + 1) + 1) + z * p.n)

/-- After the first block of a lane's height. -/
structure MP (p : Params) (S sig : Addr) (t₀ z k' : Nat) (I : Nat → Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  si : t.gpr .rsi = auOf p sig t₀ k' z
  zf : t.zf = some (decide (lOf p I t₀ k' / 2 ^ z % 2 = 0))
  wr : t.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]
  rd : (⟨sig, p.forsSigLen⟩ : Region) ∈ t.rd
  sfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64
  sss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z
  au : p.n * (min (t₀ + k') (p.k - 1) * (p.a + 1) + 1) + z * p.n + p.n ≤ p.forsSigLen

/-- The first block of a lane's height, in one run. -/
theorem uhead_ok {p : Params} (hp : FPar p) {S sig : Addr} {t₀ z k' : Nat} {I : Nat → Nat} (hk' : k' < 4)
    {s : State} (h : LP p S sig t₀ z I s) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.treeOf p k' ++ ([.mov .rcx (.mem (Impl.SlhDsa.X86_64.Fors.var 1)),
      .mov .rax (.reg .r11), .shiftCl .shr .rax, .mov .rdx (.mem (Impl.SlhDsa.X86_64.Fors.var 1))] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rsi (.reg .rdx),
      .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)), .alu .and .rax (.imm 1)] : List Instr))) s (MP p S sig t₀ z k' I) := by
  have hn := hp.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  obtain ⟨t, ht⟩ : ∃ t, t = min (t₀ + k') (p.k - 1) := ⟨_, rfl⟩
  have htk : t < p.k := by have := hp.k1; omega
  have hIt := h.ia t htk
  have hL32 : t * 2 ^ p.a + I t < 2 ^ 32 := by
    have : (t + 1) * 2 ^ p.a ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by have := hp.k; omega) (Nat.pow_le_pow_right (by decide) hp.a)
    rw [Nat.succ_mul] at this; omega
  have hsl := forsSig_le htk (j := z + 1) (by have := h.z; omega)
  have e1 : p.n * (t * (p.a + 1) + 1) = p.n * (t * (p.a + 1)) + p.n := Nat.mul_succ _ _
  have e2 : p.n * (z + 1) = p.n * z + p.n := Nat.mul_succ _ _
  have e3 : z * p.n = p.n * z := Nat.mul_comm _ _
  have hz := h.z
  have ha14 := hp.a
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine treeOf_ok hn hp.a1 hp.a hp.k1 hp.k (by have := h.t₀; omega) h.bx h.r14 h.v0 h.fidx h.ia h.hw
    fun s₁ g₁ m₁ r₁ w₁ h10₁ h11₁ hsi₁ => ?_
  rw [← ht] at h10₁ h11₁ hsi₁
  have hb₁ : s₁.gpr .rbx = S := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.bx]
  refine wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, hb₁])
    (by rw [r₁, w₁, oVar21]; exact in_scr' h.hw (by omega)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => Levels.wp_shrcl fun s₄ u₄ => ?_
  refine wp_movm (a := at' S (Layout.oVar 2 1))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hb₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, r₁, w₁, oVar21]; exact in_scr' h.hw (by omega)) fun s₅ u₅ => ?_
  refine Levels.mulN_ok hn (r := .rdx) (tmp := .rcx) (by decide) fun s₆ h₆ g₆ m₆ r₆ w₆ => ?_
  refine wp_add fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_andi_zf fun s₉ u₉ z₉ => WP.block_nil ?_
  have hm₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hmz : s₄.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z := by
    rw [u₄.mem, u₃.mem, u₂.mem, m₁, h.v1]
  have hrax : s₉.gpr .rax = BitVec.ofNat 64 (lOf p I t₀ k' / 2 ^ z % 2) := by
    rw [u₉.gpr, u₈.other .rax (by decide), u₇.other .rax (by decide), g₆ .rax (by decide) (by decide),
      u₅.other .rax (by decide), u₄.gpr, u₃.gpr, u₃.other .rcx (by decide), u₂.gpr, u₂.other .r11 (by decide), h11₁, m₁,
      h.v1, shr_nat _ _ (by omega) (by omega), sx1', and1_nat _ (by
        have := Nat.div_le_self (t * 2 ^ p.a + I t) (2 ^ z); omega), lOf, tOf, ← ht]
  refine ⟨?_, ?_, ?_, by rw [u₉.wr, u₈.wr, u₇.wr, w₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, w₁, h.wr],
    by rw [u₉.rd, u₈.rd, u₇.rd, r₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, r₁]; exact h.rd, h.sfit, h.sss,
    by rw [hm₉]; exact h.v1, by subst ht; omega⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hb₁]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, g₆ _ (by decide) (by decide), h₆, u₅.gpr, hmz,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hsi₁,
      sx_ofNat (by omega), auOf, ← ht, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat]
    congr 2
    omega
  · rw [z₉, ← u₉.gpr, hrax, beq_bit]

/-- What the copies of a lane's height leave of each run. -/
structure MP2 (S : Addr) (z : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  wr : t.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z

/-- The copies of a lane's height, in one run. -/
theorem ucopy_ok {p : Params} (hp : FPar p) {S sig : Addr} {t₀ z k' : Nat} {I : Nat → Nat} (hk' : k' < 4)
    {s : State} (h : MP p S sig t₀ z k' I s) :
    WP isa (.ite .e
        (.block (copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rsi 0 (p.n / 8)))
        (.block (copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rbx
            (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8) ++
          copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)))) s
      (MP2 S z) := by
  have hn := hp.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  have hla : Layout.laneA k' + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hla' : 3296 ≤ Layout.laneA k' := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have hdis : Region.Disjoint ⟨auOf p sig t₀ k' z, p.n⟩ ⟨S, 2 ^ 16⟩ := h.sss.sub_left (Offset.sub_base sig h.au)
  have hsig : ∀ j < p.n / 8, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (0 + 8 * j)) 8 := fun j hj =>
    ⟨_, List.mem_append_left _ h.rd, by
      rw [h.si, Nat.zero_add, auOf, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base sig (by have := h.au; omega) (by have := h.au; have := h.sfit; omega)⟩
  have hv1 : ∀ {m : Mem} {o l : Nat}, Frame [⟨S + BitVec.ofNat 64 o, l⟩] s.mem m → Layout.laneA k' ≤ o →
      o + l ≤ Layout.laneA k' + 128 → m.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z := fun hf h₁ h₂ => by
    rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar21]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), h.v1]
  rw [hmsg]
  refine WP.ite (decide (lOf p I t₀ k' / 2 ^ z % 2 = 0)) (by show s.zf = _; exact h.zf) (fun _ => ?_) (fun _ => ?_)
  · refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
      (fun j hj => by rw [h.bx]; exact in_scr hw (by omega)) hsig
      (by rw [h.bx, h.si, BitVec.add_zero, e8]; exact (hdis.sub_right (Offset.sub_base S (by omega))).symm)
      (by omega) (by omega)) fun s' c => ⟨by rw [c.gpr _ (by decide), h.bx], by rw [c.wr, h.wr], ?_⟩
    rw [h.bx, e8] at c
    exact hv1 c.frame (by omega) (by omega)
  · refine WP.block_append (WP.mono (copyWords_ok (by decide) (by decide)
      (fun j hj => by rw [h.bx]; exact in_scr hw (by omega))
      (fun j hj => by rw [h.bx]; exact in_scr' hw (by omega))
      (by rw [h.bx, e8]; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by omega) (by omega)) fun s₁ c₁ => ?_)
    rw [h.bx, e8] at c₁
    have hb₁ : s₁.gpr .rbx = S := by rw [c₁.gpr _ (by decide), h.bx]
    have hsi₁ : s₁.gpr .rsi = auOf p sig t₀ k' z := by rw [c₁.gpr _ (by decide), h.si]
    have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₁.wr := by rw [c₁.wr]; exact hw
    refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
      (fun j hj => by rw [hb₁]; exact in_scr hw₁ (by omega))
      (fun j hj => ⟨_, List.mem_append_left _ (by rw [c₁.rd]; exact h.rd), by
        rw [hsi₁, Nat.zero_add, auOf, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact Offset.contains_base sig (by have := h.au; omega) (by have := h.au; have := h.sfit; omega)⟩)
      (by rw [hb₁, hsi₁, BitVec.add_zero, e8]; exact (hdis.sub_right (Offset.sub_base S (by omega))).symm)
      (by omega) (by omega)) fun s' c => ⟨by rw [c.gpr _ (by decide), hb₁], by rw [c.wr, c₁.wr, h.wr], ?_⟩
    rw [hb₁, e8] at c
    have := hv1 c₁.frame (by omega) (by omega)
    rw [c.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar21]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), this]

theorem P6.fpar {p : Params} (hp : P6 p) (hfam : p.family = .shake) : FPar p := by
  have hmd : p.mdLen = (p.k * p.a + 7) / 8 := rfl
  rcases hp with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    exact ⟨by omega, hfam, by omega, by omega, by omega, by omega, by rw [hmd, ha, hk]; decide⟩

theorem slot_agree {S : Addr} {sl : List Nat} {s₁ s₂ : State} {vs : Nat → Nat}
    (h₁ : ∀ o ∈ sl, s₁.mem.readW (at' S o) 64 = BitVec.ofNat 64 (vs o))
    (h₂ : ∀ o ∈ sl, s₂.mem.readW (at' S o) 64 = BitVec.ofNat 64 (vs o)) :
    ∀ o ∈ sl, s₁.mem.readW (at' S o) 64 = s₂.mem.readW (at' S o) 64 := fun o ho => by rw [h₁ o ho, h₂ o ho]

/-- A lane of a height, in two runs at the same height of the same group. -/
theorem lane_rel {p : Params} (hp : P6 p) (hfam : p.family = .shake) {S sig : Addr} {t₀ z k' : Nat}
    {I : Nat → Nat} (hk' : k' < 4) :
    RelCT isa (fun a b => LP p S sig t₀ z I a ∧ LP p S sig t₀ z I b) (Impl.SlhDsa.X86_64.Verify.forsUpLane p k')
      fun _ _ => True := by
  have hF := hp.fpar hfam
  unfold Impl.SlhDsa.X86_64.Verify.forsUpLane
  refine relSeq (B₁ := MP p S sig t₀ z k' I) (B₂ := MP p S sig t₀ z k' I)
    (ct_uhead hp hk' fun a b ⟨ha, hb⟩ => fT_agree ha.wr hb.wr ha.bx hb.bx (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.r14, hb.r14])
      (fun o ho => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; rcases ho with rfl | rfl <;> decide)
      (fun o ho => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · rw [ha.v0, hb.v0]
        · rw [ha.v1, hb.v1]))
    (fun a h => uhead_ok hF hk' h) (fun b h => uhead_ok hF hk' h) ?_
  refine relSeq (B₁ := MP2 S z) (B₂ := MP2 S z)
    (RelCT.ite (fun a b ⟨ha, hb⟩ => by rw [eval_e', eval_e', ha.zf, hb.zf])
      (ct_ucopy0 hp hk' fun a b ⟨⟨ha, hb⟩, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.bx, hb.bx]
        · rw [ha.si, hb.si])
      (ct_ucopy1 hp hk' fun a b ⟨⟨ha, hb⟩, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.bx, hb.bx]
        · rw [ha.si, hb.si]))
    (fun a h => ucopy_ok hF hk' h) (fun b h => ucopy_ok hF hk' h) ?_
  exact ct_ufields hp hk' fun a b ⟨ha, hb⟩ => fT_agree ha.wr hb.wr ha.bx hb.bx (fun _ h => absurd h List.not_mem_nil)
    (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; decide)
    (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; rw [ha.v1, hb.v1])

/-! ## The facts each run keeps -/

/-- What each run keeps in a group from `t₀`. -/
structure GB (p : Params) (S sig sp : Addr) (kp stack t₀ : Nat) (I : Nat → Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = BitVec.ofNat 64 kp
  r14 : t.gpr .r14 = sig
  r15 : t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg
  rsp : t.gpr .rsp = sp
  wr : t.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]
  rd : (⟨sig, p.forsSigLen⟩ : Region) ∈ t.rd
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  env : ∃ pk a, Env p t.mem S pk a
  fidx : ∀ i < p.k, t.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (I i)
  ia : ∀ i < p.k, I i < 2 ^ p.a
  sfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64
  sss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩
  ssb : Region.Disjoint ⟨sig, p.forsSigLen⟩ (below sp stack)
  v0 : t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀
  t₀k : t₀ < p.k
  kp : kp < 2 ^ 32
  t₀b : t₀ + 4 < 2 ^ 31

theorem GB.hw {p : Params} {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {t : State}
    (h : GB p S sig sp kp stack t₀ I t) : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..

/-- `GB` after code that keeps the callee-saved registers, the regions, and
changes only what `rs` lists, outside variable 0 and the indices. -/
theorem GB.after {p : Params} (hn : p.n ≤ 32) {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {t t' : State}
    (h : GB p S sig sp kp stack t₀ I t) {rs : List Region} (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hf : Frame rs t.mem t'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r')
    (hv : ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.oVar 2 0), 8⟩ r)
    (hi : ∀ i < p.k, ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.oFidx + 8 * i), 8⟩ r) :
    GB p S sig sp kp stack t₀ I t' := by
  obtain ⟨pk, a, he⟩ := h.env
  refine ⟨by rw [hcs _ (by decide), h.bx], by rw [hcs _ (by decide), h.r12], by rw [hcs _ (by decide), h.r14],
    by rw [hcs _ (by decide), h.r15], by rw [hcs _ (by decide), h.rsp], by rw [hwr, h.wr], by rw [hrd]; exact h.rd,
    h.fit, h.stk, ⟨pk, a, Env.of_frame hn he (hf.sub hsub) h.stk⟩, fun i hi' => ?_, h.ia, h.sfit, h.sss, h.ssb, ?_,
    h.t₀k, h.kp, h.t₀b⟩
  · rw [hf.readW (Region.contains_self _ _) (hi i hi') (by decide), h.fidx i hi']
  · rw [hf.readW (Region.contains_self _ _) hv (by decide), h.v0]

/-- At height `z`. -/
def GZ (p : Params) (S sig sp : Addr) (kp stack t₀ z : Nat) (I : Nat → Nat) (t : State) : Prop :=
  GB p S sig sp kp stack t₀ I t ∧ t.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z ∧ z < p.a

theorem GZ.lp {p : Params} {S sig sp : Addr} {kp stack t₀ z : Nat} {I : Nat → Nat} {t : State}
    (h : GZ p S sig sp kp stack t₀ z I t) : LP p S sig t₀ z I t :=
  ⟨h.1.bx, h.1.r14, h.1.wr, h.1.rd, h.1.sfit, h.1.sss, h.1.v0, h.2.1, h.1.fidx, h.1.ia, h.2.2, h.1.t₀b⟩

theorem GB.cb {p : Params} {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {t : State}
    (h : GB p S sig sp kp stack t₀ I t) : CB S sp stack t :=
  ⟨h.bx, h.rsp, h.hw, h.fit, h.stk, by obtain ⟨_, _, e⟩ := h.env; exact e.rc⟩

/-- A lane of a height keeps `GZ`. -/
theorem gz_lane {p : Params} (hp : FPar p) {S sig sp : Addr} {kp stack t₀ z k' : Nat} {I : Nat → Nat}
    (hk' : k' < 4) {t : State} (h : GZ p S sig sp kp stack t₀ z I t) :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsUpLane p k') t (GZ p S sig sp kp stack t₀ z I) := by
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  have eA : Layout.laneA k' = 3296 + 128 * k' := rfl
  have hl := h.lp
  refine upLane_ok hp.n hp.a1 hp.a hp.k1 hp.k hk' hl.t₀ hl.z hl.bx hl.r14 hl.v0 hl.v1 hl.fidx hl.ia hl.hw hl.rd hl.sfit
    hl.sss fun t' g' r' w' _ _ F' => ?_
  have hd : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → (o + 8 ≤ 3296 ∨ 3808 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.laneA k' + p.n + 24), 8⟩ : Region), ⟨at' S (Layout.laneA k' + p.n + 32), 2 * p.n⟩],
        Region.Disjoint ⟨at' S o, 8⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [eA]; exact Offset.disjoint S (by omega) (by omega) (by omega))
  refine ⟨h.1.after hn32 (fun r hr => ?_) r' w' F' (fun r hr => ?_) (hd (by rw [oVar20]; omega) (by rw [oVar20]; omega))
    (fun i hi => hd (by rw [oFidx_eq]; have := hp.k; omega) (by rw [oFidx_eq]; omega)), ?_, h.2.2⟩
  · have hne : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g' r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hsA : ∀ {o l : Nat}, Layout.laneA k' + p.n + 16 ≤ o → o + l ≤ Layout.laneA k' + 128 →
        ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub ⟨at' S o, l⟩ r' := fun h₁ h₂ =>
      ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨k', List.mem_range.mpr hk', List.mem_cons_self ..⟩))),
        Offset.sub S h₁ (by simp only [Layout.strideA]; omega)⟩
    rcases hr with rfl | rfl
    · exact hsA (by omega) (by omega)
    · exact hsA (by omega) (by omega)
  · rw [F'.readW (Region.contains_self _ _) (hd (by rw [oVar21]; omega) (by rw [oVar21]; omega)) (by decide), h.2.1]

/-- `GB` after a frame of `gFrame`. -/
theorem GB.after_g {p : Params} (hp : FPar p) {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {t t' : State}
    (h : GB p S sig sp kp stack t₀ I t) (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hf : Frame (gFrame p S sp stack) t.mem t'.mem) :
    GB p S sig sp kp stack t₀ I t' := by
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  have hk := hp.k
  exact h.after hn32 hcs hrd hwr hf (gFrame_sub p S sp stack)
    (gFrame_disj hn32 h.stk (by rw [oVar20] <;> omega)
      (Or.inr (Or.inl ⟨by rw [oVar20] <;> omega, by rw [oVar20] <;> omega⟩)))
    fun i hi => gFrame_disj hn32 h.stk (by rw [oFidx_eq] <;> omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (by rw [oFidx_eq] <;> omega)))))

/-- A height of a group, in two runs at the same height. -/
theorem up_rel {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sig sp : Addr} {kp t₀ z : Nat} {I : Nat → Nat} :
    RelCT isa (fun a b => GZ p S sig sp kp stack t₀ z I a ∧ GZ p S sig sp kp stack t₀ z I b)
      (Impl.SlhDsa.X86_64.Verify.forsUp p f) fun _ _ => True := by
  have hF := hp.fpar hfam
  have hn := hF.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hL : ∀ k' < 4, RelCT isa (fun a b => GZ p S sig sp kp stack t₀ z I a ∧ GZ p S sig sp kp stack t₀ z I b)
      (Impl.SlhDsa.X86_64.Verify.forsUpLane p k') fun _ _ => True := fun k' hk' =>
    RelCT.mono (lane_rel hp hfam hk') (fun a b h => ⟨h.1.lp, h.2.lp⟩) fun _ _ h => h
  have hW : ∀ k' < 4, ∀ t, GZ p S sig sp kp stack t₀ z I t →
      WP isa (Impl.SlhDsa.X86_64.Verify.forsUpLane p k') t (GZ p S sig sp kp stack t₀ z I) :=
    fun k' hk' t h => gz_lane hF hk' h
  unfold Impl.SlhDsa.X86_64.Verify.forsUp
  refine relSeq (hL 0 (by decide)) (hW 0 (by decide)) (hW 0 (by decide)) ?_
  refine relSeq (hL 1 (by decide)) (hW 1 (by decide)) (hW 1 (by decide)) ?_
  refine relSeq (hL 2 (by decide)) (hW 2 (by decide)) (hW 2 (by decide)) ?_
  refine relSeq (hL 3 (by decide)) (hW 3 (by decide)) (hW 3 (by decide)) ?_
  have hC : ∀ t, GZ p S sig sp kp stack t₀ z I t →
      WP isa (Impl.SlhDsa.X86_64.thashCall (Impl.SlhDsa.X86_64.Shake.layout p) f.t4name f.t4 Layout.oA Layout.strideA
        (3 * p.n + 32)) t fun t' => t'.gpr .rbx = S := fun t h => by
    obtain ⟨_, _, he⟩ := h.1.env
    rw [ht]
    exact lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 3 * p.n + 32)
      (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by simp only [Layout.strideA]; omega) h.1.bx h.1.hw h.1.fit
      (by rw [h.1.rsp]; exact h.1.stk) he.rc fun t' _ _ g' _ _ _ => by rw [g' _ (by decide), h.1.bx]
  refine relSeq (B₁ := fun t => t.gpr .rbx = S) (B₂ := fun t => t.gpr .rbx = S) ?_ hC hC
    (ct_ufin p.a fun a b ⟨ha, hb⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [ha, hb])
  rw [ht]
  exact fcall_rel hp T f.t4name hst hs63 (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega)
    (by simp only [Layout.strideA]; omega) (fun a h => h.1.cb) (fun b h => h.1.cb)

/-- At height `z`, with the lanes' nodes. -/
def GL (p : Params) (S sig sp : Addr) (kp stack t₀ z : Nat) (I : Nat → Nat) (t : State) : Prop :=
  GZ p S sig sp kp stack t₀ z I t ∧
    ∃ V : Nat → List Byte, ∀ j < 4, FLane p S j kp z (lOf p I t₀ j / 2 ^ z) (V j) t.mem

/-- The heights of a group, in two runs of the same group. -/
theorem heights_rel {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sig sp : Addr} {kp t₀ : Nat} {I : Nat → Nat} :
    RelCT isa (fun a b => GL p S sig sp kp stack t₀ 0 I a ∧ GL p S sig sp kp stack t₀ 0 I b)
      (.loop (Impl.SlhDsa.X86_64.Verify.forsUp p f) .ne)
      fun a b => GB p S sig sp kp stack t₀ I a ∧ GB p S sig sp kp stack t₀ I b := by
  have hF := hp.fpar hfam
  let J : Nat → State → Prop := fun m t => 1 ≤ m ∧ m ≤ p.a ∧ GL p S sig sp kp stack t₀ (p.a - m) I t
  have step : ∀ m t, J m t → WP isa (Impl.SlhDsa.X86_64.Verify.forsUp p f) t fun t' =>
      isa.eval .ne t' = some (!decide (p.a - m + 1 = p.a)) ∧
      ((!decide (p.a - m + 1 = p.a)) = false → GB p S sig sp kp stack t₀ I t') ∧
      ((!decide (p.a - m + 1 = p.a)) = true → m - 1 < m ∧ J (m - 1) t') := by
    intro m t ⟨h1, h2, ⟨hb, hv1, hz⟩, V, hl⟩
    obtain ⟨pk, a16, he⟩ := hb.env
    refine forsUp_ok T ht hF.n hF.fam hF.a1 hF.a hF.k1 hF.k hst hs63 hb.t₀b hz hb.bx hb.r14 hb.v0 hv1 hb.fidx hb.ia
      hb.hw hb.fit (by rw [hb.rsp]; exact hb.stk) he hb.rd hb.sfit hb.sss hl fun t' g' r' w' v' z' l' F' => ?_
    rw [hb.rsp] at F'
    have hb' := hb.after_g hF g' r' w' F'
    refine ⟨by rw [eval_ne', z']; rfl, fun _ => hb', fun hc => ?_⟩
    have : ¬ (p.a - m + 1 = p.a) := by simpa using hc
    refine ⟨by omega, by omega, by omega, ?_⟩
    rw [show p.a - (m - 1) = p.a - m + 1 by omega]
    exact ⟨⟨hb', v', by omega⟩, _, l'⟩
  refine RelCT.mono (relLoop (I₁ := J) (I₂ := J) (fun m => !decide (p.a - m + 1 = p.a)) (fun m => m - 1)
    (fun m => ?_) step step p.a) (fun a b ⟨ha, hb⟩ => ⟨⟨hF.a1, Nat.le_refl _, by rw [Nat.sub_self]; exact ha⟩,
      ⟨hF.a1, Nat.le_refl _, by rw [Nat.sub_self]; exact hb⟩⟩) fun _ _ h => h
  exact RelCT.mono (up_rel hp hfam T ht hst hs63 (z := p.a - m)) (fun a b ⟨ha, hb⟩ => ⟨ha.2.2.1, hb.2.2.1⟩)
    fun _ _ h => h

/-! ## A group -/

/-- After the leaves' block or call: `GB` and the lanes' fields at height 0. -/
def LB (p : Params) (S sig sp : Addr) (kp stack t₀ : Nat) (I : Nat → Nat) (t : State) : Prop :=
  GB p S sig sp kp stack t₀ I t ∧
    ∃ V : Nat → List Byte, ∀ j < 4, FLane p S j kp 0 (lOf p I t₀ j) (V j) t.mem

theorem laneR_ch {p : Params} (hn : p.n ≤ 32) (S sp : Addr) (stack : Nat) :
    ∀ r ∈ laneR p S, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r' := by
  intro r hr
  simp only [laneR, List.mem_map, List.mem_range] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  have eA : Layout.laneA c = 3296 + 128 * c := rfl
  exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, List.mem_cons_self ..⟩))),
    Offset.sub S (by omega) (by simp only [Layout.strideA]; rw [eA]; omega)⟩

/-- The leaves' block, in one run. -/
theorem lblock_ok {p : Params} (hp : FPar p) {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {s : State}
    (h : GB p S sig sp kp stack t₀ I s) :
    WP isa (.block ((List.range 4).flatMap fun k' => Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
      setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 3 ++
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11 ++
      copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8))) s
      (LB p S sig sp kp stack t₀ I) := by
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  have hk := hp.k
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h₀ : LvInv p S sig kp t₀ I s 0 s := ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have L := fun {K : Nat} {u : State} (hK : K < 4) (hu : LvInv p S sig kp t₀ I s K u) {is : List Instr}
      {Q : State → Prop} (k : ∀ u', LvInv p S sig kp t₀ I s (K + 1) u' → WP isa (.block is) u' Q) =>
    lvstep hp.n hp.a1 hp.a hp.k1 hp.k hK h.t₀b h.kp h.bx h.r12 h.r14 h.v0 h.fidx h.ia h.hw h.rd h.sfit h.sss hu k
  refine L (by decide) h₀ fun u₁ hu₁ => L (by decide) hu₁ fun u₂ hu₂ => L (by decide) hu₂ fun u₃ hu₃ => ?_
  have hh := L (by decide) hu₃ (is := []) (Q := LB p S sig sp kp stack t₀ I) fun u hu => WP.block_nil ?_
  · rwa [List.append_nil] at hh
  have hR : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → (o + 8 ≤ 3296 ∨ 3808 ≤ o) →
      ∀ r ∈ laneR p S, Region.Disjoint ⟨at' S o, 8⟩ r :=
    fun h₁ h₂ => laneR_disj hn32 S h₁ fun c hc => by rw [eA]; omega
  refine ⟨h.after hn32 (fun r hr => ?_) hu.rd hu.wr hu.frame (laneR_ch hn32 S sp stack)
    (hR (by rw [oVar20]; omega) (by rw [oVar20]; omega)) fun i hi => hR (by rw [oFidx_eq]; omega)
      (by rw [oFidx_eq]; omega), _, hu.done⟩
  have hne : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hu.gpr r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2

/-- A call of `thash4` keeps `GB` and the fields of the lanes `A`. -/
theorem lcall_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : FPar p) (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sig sp : Addr} {kp t₀ : Nat} {I : Nat → Nat} {s : State} (h : LB p S sig sp kp stack t₀ I s) :
    WP isa (Impl.SlhDsa.X86_64.thashCall (Impl.SlhDsa.X86_64.Shake.layout p) f.t4name f.t4 Layout.oA Layout.strideA
      (2 * p.n + 32)) s (LB p S sig sp kp stack t₀ I) := by
  have hn := hp.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hk := hp.k
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  obtain ⟨hb, V, hl⟩ := h
  obtain ⟨_, _, he⟩ := hb.env
  rw [ht]
  refine lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 2 * p.n + 32)
    (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by simp only [Layout.strideA]; omega) hb.bx hb.hw hb.fit
    (by rw [hb.rsp]; exact hb.stk) he.rc fun t' r' w' g' o' _ F' => ?_
  rw [hb.rsp] at F'
  have hsub : ∀ r ∈ lanesOut p S Layout.oA Layout.strideA ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp stack],
      ∃ r' ∈ gFrame p S sp stack, Region.Sub r r' := fun r hr => by
    simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
        Offset.sub S (by simp only [Layout.laneA]; omega) (by simp only [Layout.laneA, Layout.strideA, Layout.oA]; omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
  refine ⟨hb.after_g hp g' r' w' (F'.sub hsub), fun j => bytesAt t'.mem (at' S (Layout.laneA j + p.n + 32)) p.n,
    fun j hj => ⟨?_, rfl⟩⟩
  rw [bytesAt_frame F' (fun r hr => by
    simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
    · have e : Layout.oA + Layout.strideA * c + p.n + 32 = Layout.laneA c + p.n + 32 := rfl
      rw [e, eA, eA]
      rcases Nat.lt_or_ge c j with h' | h'
      · exact Offset.disjoint S (by omega) (by omega) (by omega)
      · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · rw [eA]; exact Offset.disjoint_base S (by omega) (by omega)
    · rw [eA]; exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hb.stk.sub_right (Offset.sub_base S (by rw [eA]; omega))).symm) (by decide)]
  exact (hl j hj).fields

/-- Variable 1 ← 0, in one run. -/
theorem v1z_ok {p : Params} (hp : FPar p) {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {s : State}
    (h : LB p S sig sp kp stack t₀ I s) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Fors.var 1) .rax]) s
      (GL p S sig sp kp stack t₀ 0 I) := by
  obtain ⟨hb, V, hl⟩ := h
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  have hk := hp.k
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  refine wp_mov32i fun s₂ u₂ => wp_store (a := at' S (Layout.oVar 2 1))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, u₂.other _ (by decide), hb.bx])
    (by rw [u₂.wr, oVar21]; exact in_scr hb.hw (by omega)) fun s₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
  have hm₃ : s₃.mem = s.mem.writeW (at' S (Layout.oVar 2 1)) (BitVec.ofNat 64 0) := by
    rw [m₃, u₂.gpr, u₂.mem, mov32_zero]; rfl
  have F₃ : Frame [⟨at' S (Layout.oVar 2 1), 8⟩] s.mem s₃.mem := by
    rw [hm₃]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have hd : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 2712 ∨ 2720 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.oVar 2 1), 8⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [oVar21]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  refine ⟨⟨hb.after hn32 (fun r hr => ?_) (by rw [r₃, u₂.rd]) (by rw [w₃, u₂.wr]) F₃ (fun r hr => ?_)
    (hd (by rw [oVar20]; omega) (by rw [oVar20]; omega)) (fun i hi => hd (by rw [oFidx_eq]; omega)
      (by rw [oFidx_eq]; omega)), by rw [hm₃]; exact Mem.readW_writeW_self64 _ _ _, hp.a1⟩, V, fun j hj => ?_⟩
  · have h' : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃, u₂.other _ h']
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
      Offset.sub S (by rw [oVar21]; simp only [Layout.oVars]; omega) (by rw [oVar21]; simp only [Layout.oVars]; omega)⟩
  · rw [Nat.pow_zero, Nat.div_one]
    exact ⟨by rw [bytesAt_frame F₃ (hd (by rw [eA]; omega) (by rw [eA]; omega)) (by omega)]; exact (hl j hj).fields,
      by rw [bytesAt_frame F₃ (hd (by rw [eA]; omega) (by rw [eA]; omega)) (by omega)]; exact (hl j hj).value⟩

/-- A lane's root, in one run. -/
theorem rootW {p : Params} (hp : FPar p) {S sig sp : Addr} {kp stack t₀ k' : Nat} {I : Nat → Nat} (hk' : k' < 4)
    {s : State} (h : GB p S sig sp kp stack t₀ I s) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
        ([.mov .rdx (.reg .r10)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
          (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8))) s
      (GB p S sig sp kp stack t₀ I) := by
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  have hk := hp.k
  have eB : Layout.laneB 0 = 3808 := rfl
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have hh := rootLane_ok hp.n hp.a1 hp.a hp.k1 hp.k hk' h.t₀b (is := []) (Q := GB p S sig sp kp stack t₀ I) h.bx h.r14
    h.v0 h.fidx h.ia h.hw fun s' g' r' w' _ F' => WP.block_nil ?_
  · rwa [List.append_nil] at hh
  have htk : tOf p t₀ k' < p.k := by simp only [tOf]; have := hp.k1; omega
  have hcn : tOf p t₀ k' * p.n + p.n ≤ p.k * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ htk
  have hd : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → (o + 8 ≤ 3808 ∨ 3808 + p.n + 32 + p.k * p.n ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.laneB 0 + p.n + 32 + tOf p t₀ k' * p.n), p.n⟩ : Region)], Region.Disjoint ⟨at' S o, 8⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  refine h.after hn32 (fun r hr => ?_) r' w' F' (fun r hr => ?_) (hd (by rw [oVar20]; omega) (by rw [oVar20]; omega))
    fun i hi => hd (by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega)
  · have hne : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g' r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
      Offset.sub S (e := Layout.laneB 0 + p.n + 16) (k := Layout.strideB - p.n - 16) (by omega)
        (by simp only [Layout.strideB]; rw [eB]; omega)⟩

theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e : List Instr}
    (h : RelCT isa P (.block (a ++ (b ++ (c ++ (d ++ e))))) Q) : RelCT isa P (.block ((a ++ (b ++ (c ++ d))) ++ e)) Q := by
  simpa only [List.append_assoc] using h

/-- The roots of a group, in two runs of the same group. -/
theorem roots_rel {p : Params} (hp : P6 p) (hfam : p.family = .shake) {S sig sp : Addr} {kp stack t₀ : Nat}
    {I : Nat → Nat} :
    RelCT isa (fun a b => GB p S sig sp kp stack t₀ I a ∧ GB p S sig sp kp stack t₀ I b)
      (.block ((List.range 4).flatMap (fun k' => Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
        ([.mov .rdx (.reg .r10)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
          (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++
      ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Fors.var 0)), .alu .add .rax (.imm 4),
        .store (Impl.SlhDsa.X86_64.Fors.var 0) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.k))] : List Instr))) fun _ _ => True := by
  have hF := hp.fpar hfam
  have hA : ∀ a b, GB p S sig sp kp stack t₀ I a ∧ GB p S sig sp kp stack t₀ I b →
      X86_64.Taint.Agree (fT [] [Layout.oVar 2 0]) a b := fun a b ⟨ha, hb⟩ =>
    fT_agree ha.wr hb.wr ha.bx hb.bx (fun _ h => absurd h List.not_mem_nil)
      (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; decide)
      (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; rw [ha.v0, hb.v0])
  have hR : ∀ k' < 4, RelCT isa (fun a b => GB p S sig sp kp stack t₀ I a ∧ GB p S sig sp kp stack t₀ I b)
      (.block (Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
        ([.mov .rdx (.reg .r10)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
          (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8))) fun _ _ => True :=
    fun k' hk' => ct_root hp hk' hA
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine rel_assoc5 ?_
  refine RelCT.block_append (relSeq (hR 0 (by decide)) (fun a h => rootW hF (by decide) h)
    (fun b h => rootW hF (by decide) h) ?_)
  refine RelCT.block_append (relSeq (hR 1 (by decide)) (fun a h => rootW hF (by decide) h)
    (fun b h => rootW hF (by decide) h) ?_)
  refine RelCT.block_append (relSeq (hR 2 (by decide)) (fun a h => rootW hF (by decide) h)
    (fun b h => rootW hF (by decide) h) ?_)
  refine RelCT.block_append (relSeq (hR 3 (by decide)) (fun a h => rootW hF (by decide) h)
    (fun b h => rootW hF (by decide) h) ?_)
  exact ct_rfin p.k fun a b ⟨ha, hb⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [ha.bx, hb.bx]

/-- A group, in two runs of the same group. -/
theorem group_rel {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sig sp : Addr} {kp t₀ : Nat} {I : Nat → Nat} :
    RelCT isa (fun a b => GB p S sig sp kp stack t₀ I a ∧ GB p S sig sp kp stack t₀ I b)
      (Impl.SlhDsa.X86_64.Verify.forsGroup p f) fun _ _ => True := by
  have hF := hp.fpar hfam
  have hn := hF.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hlv : ∀ t, GB p S sig sp kp stack t₀ I t →
      WP isa (Impl.SlhDsa.X86_64.Verify.forsLeaves p f) t (LB p S sig sp kp stack t₀ I) := fun t h =>
    WP.seq (WP.mono (lblock_ok hF h) fun u hu => lcall_ok hF T ht hst hs63 hu)
  have hhw : ∀ t, GL p S sig sp kp stack t₀ 0 I t →
      WP isa (.loop (Impl.SlhDsa.X86_64.Verify.forsUp p f) .ne) t (GB p S sig sp kp stack t₀ I) := by
    intro t ⟨⟨hb, hv1, _⟩, V, hl⟩
    obtain ⟨pk, a16, he⟩ := hb.env
    exact upLoop_ok T ht hF.n hF.fam hF.a1 hF.a hF.k1 hF.k hst hs63 hb.t₀b hb.bx hb.r14 hb.v0 hv1 hb.fidx hb.ia
      hb.hw hb.fit (by rw [hb.rsp]; exact hb.stk) he hb.rd hb.sfit hb.sss (by rw [hb.rsp]; exact hb.ssb)
      (fun j hj => by have := hl j hj; rwa [Nat.pow_zero, Nat.div_one] at this)
      fun s' g' r' w' _ F' => hb.after_g hF g' r' w' (by rw [hb.rsp] at F'; exact F')
  unfold Impl.SlhDsa.X86_64.Verify.forsGroup
  refine relSeq (B₁ := LB p S sig sp kp stack t₀ I) (B₂ := LB p S sig sp kp stack t₀ I) ?_ hlv hlv ?_
  · unfold Impl.SlhDsa.X86_64.Verify.forsLeaves
    refine relSeq (B₁ := LB p S sig sp kp stack t₀ I) (B₂ := LB p S sig sp kp stack t₀ I)
      (ct_leaves hp fun a b ⟨ha, hb⟩ => fT_agree ha.wr hb.wr ha.bx hb.bx (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [ha.r14, hb.r14])
        (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; decide)
        (fun o ho => by simp only [List.mem_singleton] at ho; subst ho; rw [ha.v0, hb.v0]))
      (fun a h => lblock_ok hF h) (fun b h => lblock_ok hF h) ?_
    rw [ht]
    exact fcall_rel hp T f.t4name hst hs63 (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega)
      (by simp only [Layout.strideA]; omega) (fun a h => h.1.cb) (fun b h => h.1.cb)
  refine relSeq (B₁ := GL p S sig sp kp stack t₀ 0 I) (B₂ := GL p S sig sp kp stack t₀ 0 I)
    (ct_v1z fun a b ⟨ha, hb⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [ha.1.bx, hb.1.bx])
    (fun a h => v1z_ok hF h) (fun b h => v1z_ok hF h) ?_
  exact relSeq (RelCT.mono (heights_rel hp hfam T ht hst hs63) (fun _ _ h => h) fun _ _ _ => trivial) hhw hhw
    (roots_rel hp hfam)

/-- What each run keeps after the groups. -/
structure EB (p : Params) (S sp : Addr) (kp stack : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = BitVec.ofNat 64 kp
  r15 : t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg
  rsp : t.gpr .rsp = sp
  wr : t.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  env : ∃ pk a, Env p t.mem S pk a
  kp : kp < 2 ^ 32

theorem EB.hw {p : Params} {S sp : Addr} {kp stack : Nat} {t : State} (h : EB p S sp kp stack t) :
    (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..

theorem EB.cb {p : Params} {S sp : Addr} {kp stack : Nat} {t : State} (h : EB p S sp kp stack t) : CB S sp stack t :=
  ⟨h.bx, h.rsp, h.hw, h.fit, h.stk, by obtain ⟨_, _, e⟩ := h.env; exact e.rc⟩

theorem EB.after {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {kp stack : Nat} {t t' : State}
    (h : EB p S sp kp stack t) {rs : List Region} (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hwr : t'.wr = t.wr) (hf : Frame rs t.mem t'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r') : EB p S sp kp stack t' := by
  obtain ⟨pk, a, he⟩ := h.env
  exact ⟨by rw [hcs _ (by decide), h.bx], by rw [hcs _ (by decide), h.r12], by rw [hcs _ (by decide), h.r15],
    by rw [hcs _ (by decide), h.rsp], by rw [hwr, h.wr], h.fit, h.stk, ⟨pk, a, Env.of_frame hn he (hf.sub hsub) h.stk⟩,
    h.kp⟩

theorem GB.eb {p : Params} {S sig sp : Addr} {kp stack t₀ : Nat} {I : Nat → Nat} {t : State}
    (h : GB p S sig sp kp stack t₀ I t) : EB p S sp kp stack t :=
  ⟨h.bx, h.r12, h.r15, h.rsp, h.wr, h.fit, h.stk, h.env, h.kp⟩

/-- The groups, in two runs. -/
theorem groups_rel {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sig sp : Addr} {kp : Nat} {I : Nat → Nat} :
    RelCT isa (fun a b => GB p S sig sp kp stack 0 I a ∧ GB p S sig sp kp stack 0 I b)
      (.loop (Impl.SlhDsa.X86_64.Verify.forsGroup p f) .b) fun a b => EB p S sp kp stack a ∧ EB p S sp kp stack b := by
  have hF := hp.fpar hfam
  have hn32 : p.n ≤ 32 := by omega_using [hF.n]
  have hk := hF.k
  have eB : Layout.laneB 0 = 3808 := rfl
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  let J : Nat → State → Prop := fun m t => 1 ≤ m ∧ m ≤ p.k ∧ GB p S sig sp kp stack (p.k - m) I t
  have step : ∀ m t, J m t → WP isa (Impl.SlhDsa.X86_64.Verify.forsGroup p f) t fun t' =>
      isa.eval .b t' = some (decide (p.k - m + 4 < p.k)) ∧
      (decide (p.k - m + 4 < p.k) = false → EB p S sp kp stack t') ∧
      (decide (p.k - m + 4 < p.k) = true → m - 4 < m ∧ J (m - 4) t') := by
    intro m t ⟨h1, h2, hb⟩
    obtain ⟨pk, a16, he⟩ := hb.env
    refine forsGroup_ok T ht hF.n hF.fam hF.a1 hF.a hF.k1 hF.k hst hs63 hb.t₀k hb.kp hb.bx hb.r12 hb.r14 hb.v0 hb.fidx
      hb.ia hb.hw hb.fit (by rw [hb.rsp]; exact hb.stk) he hb.rd hb.sfit hb.sss (by rw [hb.rsp]; exact hb.ssb)
      fun t' g' r' w' v' c' _ F' => ?_
    rw [hb.rsp] at F'
    have hsub := grFrame_sub hk hn32 S sp stack
    refine ⟨by rw [eval_b', c'], fun _ => hb.eb.after hn32 g' w' F' hsub, fun hc => ?_⟩
    have hc' : p.k - m + 4 < p.k := of_decide_eq_true hc
    refine ⟨by omega, by omega, by omega, ?_⟩
    rw [show p.k - (m - 4) = p.k - m + 4 by omega]
    obtain ⟨pk', a', he'⟩ := hb.env
    have hgr : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → 3808 + p.n + 32 + p.k * p.n ≤ o →
        ∀ r ∈ grFrame p S sp stack, Region.Disjoint ⟨at' S o, 8⟩ r := fun h₁ h₂ r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact gFrame_disj hn32 hb.stk h₁ (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))) r hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
        · rw [oVar20]; exact Offset.disjoint S (by omega) (by omega) (by omega)
    exact ⟨by rw [g' _ (by decide), hb.bx], by rw [g' _ (by decide), hb.r12], by rw [g' _ (by decide), hb.r14],
      by rw [g' _ (by decide), hb.r15], by rw [g' _ (by decide), hb.rsp], by rw [w', hb.wr], by rw [r']; exact hb.rd,
      hb.fit, hb.stk, ⟨pk', a', Env.of_frame hn32 he' (F'.sub hsub) hb.stk⟩, fun i hi => by
        rw [F'.readW (Region.contains_self _ _) (hgr (by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega)) (by decide),
          hb.fidx i hi], hb.ia, hb.sfit, hb.sss, hb.ssb, v', hc', hb.kp, by omega⟩
  refine RelCT.mono (relLoop (I₁ := J) (I₂ := J) (fun m => decide (p.k - m + 4 < p.k)) (fun m => m - 4)
    (fun m => ?_) step step p.k) (fun a b ⟨ha, hb⟩ => ⟨⟨hF.k1, Nat.le_refl _, by rw [Nat.sub_self]; exact ha⟩,
      ⟨hF.k1, Nat.le_refl _, by rw [Nat.sub_self]; exact hb⟩⟩) fun _ _ h => h
  exact RelCT.mono (group_rel hp hfam T ht hst hs63 (t₀ := p.k - m)) (fun a b ⟨ha, hb⟩ => ⟨ha.2.2, hb.2.2⟩)
    fun _ _ h => h

/-! ## `pkFors` and `forsPk` -/

/-- `pkFors`'s fields, in one run. -/
theorem pkf_ok {p : Params} (hp : FPar p) {S sp : Addr} {kp stack : Nat} {s : State} (h : EB p S sp kp stack s) :
    WP isa (.block (setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 4 ++
        setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0)) s (EB p S sp kp stack) := by
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  refine ffields_ok hp.n h.kp h.bx h.r12 h.hw fun s' g' r' w' _ f' => h.after hn32 (fun r hr => ?_) w' f' fun r hr => ?_
  · have h' : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g' r h'
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
      Offset.sub S (by omega) (by simp only [Layout.strideB]; omega)⟩

/-- `pkFors`'s call, in one run. -/
theorem pkc_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : FPar p) (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sp : Addr} {kp : Nat} {s : State} (h : EB p S sp kp stack s) :
    WP isa (Impl.SlhDsa.X86_64.thashCall (Impl.SlhDsa.X86_64.Shake.layout p) f.t4name f.t4 Layout.oB Layout.strideB
      ((Impl.SlhDsa.X86_64.Shake.layout p).n + 32 + p.k * (Impl.SlhDsa.X86_64.Shake.layout p).n)) s
      fun t => t.gpr .rbx = S ∧ t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg ∧ t.wr = s.wr := by
  have hn := hp.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hk := hp.k
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  obtain ⟨_, _, he⟩ := h.env
  rw [ht]
  exact lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oB) (st := Layout.strideB) (len := p.n + 32 + p.k * p.n)
    (Or.inr ⟨rfl, rfl⟩) (by omega) (by rw [Nat.add_mod, Nat.add_mod p.n, hn8, Nat.mul_mod, hn8]; simp)
    (by simp only [Layout.strideB]; omega) h.bx h.hw h.fit (by rw [h.rsp]; exact h.stk) he.rc
    fun t' _ w' g' _ _ _ => ⟨by rw [g' _ (by decide), h.bx], by rw [g' _ (by decide), h.r15], w'⟩

/-- `pkFors`, in two runs. -/
theorem pk_rel {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S sp : Addr} {kp : Nat} :
    RelCT isa (fun a b => EB p S sp kp stack a ∧ EB p S sp kp stack b)
      (Impl.SlhDsa.X86_64.Fors.pkFors (Impl.SlhDsa.X86_64.Shake.layout p) p.k f.t4name f.t4) fun _ _ => True := by
  have hF := hp.fpar hfam
  have hn := hF.n
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hk := hF.k
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  unfold Impl.SlhDsa.X86_64.Fors.pkFors
  refine relSeq (B₁ := EB p S sp kp stack) (B₂ := EB p S sp kp stack)
    (ct_pkf hp fun a b ⟨ha, hb⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [ha.bx, hb.bx])
    (fun a h => pkf_ok hF h) (fun b h => pkf_ok hF h) ?_
  refine relSeq (B₁ := fun t => t.gpr .rbx = S ∧ t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg)
    (B₂ := fun t => t.gpr .rbx = S ∧ t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg) ?_
    (fun a h => WP.mono (pkc_ok hF T ht hst hs63 h) fun _ h' => ⟨h'.1, h'.2.1⟩)
    (fun b h => WP.mono (pkc_ok hF T ht hst hs63 h) fun _ h' => ⟨h'.1, h'.2.1⟩)
    (ct_pkc hp fun a b ⟨ha, hb⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2, hb.2])
  rw [ht]
  exact fcall_rel hp T f.t4name hst hs63 (Or.inr ⟨rfl, rfl⟩) (by omega)
    (by show (p.n + 32 + p.k * p.n) % 8 = 0; rw [Nat.add_mod, Nat.add_mod p.n, hn8, Nat.mul_mod, hn8]; simp)
    (by show p.n + 32 + p.k * p.n ≤ Layout.strideB; simp only [Layout.strideB]; omega) (fun a h => h.cb) (fun b h => h.cb)

/-- `forsPk`'s public data, from the first run. -/
def Top (p : Params) (stack : Nat) (S sig sp : Addr) (kp : Nat) (md : List Byte) (s : State) : Prop :=
  (forsPkContract p stack).pre s ∧ s.gpr .rdi = S ∧ s.gpr .rsi = sig ∧ (s.gpr .rdx).toNat = kp ∧ s.gpr .rsp = sp ∧
    mdAt p s.mem S = md

/-- `forsPk`'s prologue, in one run. -/
theorem top_pro {p : Params} (hp : FPar p) {stack : Nat} {S sig sp : Addr} {kp : Nat} {md : List Byte} {s : State}
    (h : Top p stack S sig sp kp md s) :
    WP isa (.block (Impl.SlhDsa.X86_64.Fors.pro ++ Impl.SlhDsa.X86_64.Fors.indices p.a p.k)) s
      (GB p S sig sp kp stack 0 (fun t => (base2b md p.a p.k).getD t 0)) := by
  obtain ⟨⟨R, ⟨pk, a16, henv⟩, hkp⟩, e1, e2, e3, e4, e5⟩ := h
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  rw [e1] at R henv; rw [e2] at R
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [R.wr_eq]; exact List.mem_cons_self ..
  have hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd := by rw [R.rd_eq]; exact List.mem_singleton_self _
  refine WP.mono (fpre_ok hp.a1 hp.a hp.k hp.md (by rw [e1]; exact hw)) fun s₂ h₂ => ?_
  rw [e1] at h₂
  have F₂c : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oSave2]; simp only [Layout.oVars]; omega) (by rw [oSave2]; simp only [Layout.oVars]; omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (by simp)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oVar20]; simp only [Layout.oVars]; omega) (by rw [oVar20]; simp only [Layout.oVars]; omega)⟩
  rw [e4] at F₂c
  have hstk : (below sp stack).Disjoint ⟨S, scratchLen⟩ := by have := R.stk_scr; rwa [e4] at this
  have hsb : Region.Disjoint ⟨sig, p.forsSigLen⟩ (below sp stack) := by
    have := (R.stk_rd _ (by rw [← R.rd_eq]; exact hsr)).symm; rwa [e4] at this
  exact ⟨h₂.bx, by rw [h₂.r12, ← e3, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [h₂.r14, e2], h₂.r15,
    by rw [h₂.sp, e4], by rw [h₂.wr, R.wr_eq], by rw [h₂.rd]; exact hsr, R.scr_fit, hstk,
    ⟨pk, a16, Env.of_frame hn32 henv F₂c hstk⟩, fun i hi => by rw [h₂.fidx i hi, e5],
    fun i _ => base2b_getD_lt _ _ _ _, R.rd_fit _ (by rw [← R.rd_eq]; exact hsr),
    R.rd_scr _ (by rw [← R.rd_eq]; exact hsr), hsb, h₂.v0, hp.k1,
    by rw [← e3]; exact hkp, by omega⟩

theorem forsPk_ct {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    ConstantTime isa (forsPkContract p stack).pre (forsPkContract p stack).pub (Impl.SlhDsa.X86_64.Verify.forsPk p f) := by
  have hF := hp.fpar hfam
  have hn32 : p.n ≤ 32 := by omega_using [hF.n]
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp1, hp2, hp3, hp4, _, hp6⟩ := hpub
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .rdi = S := ⟨_, rfl⟩
  obtain ⟨md, emd⟩ : ∃ md, mdAt p s₁.mem S = md := ⟨_, rfl⟩
  have hmd₂ : mdAt p s₂.mem S = md := by
    rw [← emd, mdAt, mdAt, ← bytesAt_take _ _ (Nat.le_add_right p.mdLen 2), ← bytesAt_take _ _ (Nat.le_add_right p.mdLen 2)]
    rw [← eS] at ⊢
    rw [hp6, hp1]
  let I : Nat → Nat := fun t => (base2b md p.a p.k).getD t 0
  have hA : ∀ s, Top p stack S (s₁.gpr .rsi) (s₁.gpr .rsp) (s₁.gpr .rdx).toNat md s →
      WP isa (.block (Impl.SlhDsa.X86_64.Fors.pro ++ Impl.SlhDsa.X86_64.Fors.indices p.a p.k)) s
        (GB p S (s₁.gpr .rsi) (s₁.gpr .rsp) (s₁.gpr .rdx).toNat stack 0 I) := fun s h => top_pro hF h
  have hG : ∀ t, GB p S (s₁.gpr .rsi) (s₁.gpr .rsp) (s₁.gpr .rdx).toNat stack 0 I t →
      WP isa (.loop (Impl.SlhDsa.X86_64.Verify.forsGroup p f) .b) t
        (EB p S (s₁.gpr .rsp) (s₁.gpr .rdx).toNat stack) := fun t hb => by
    obtain ⟨pk, a16, he⟩ := hb.env
    exact forsGroups_ok T ht hF.n hF.fam hF.a1 hF.a hF.k1 hF.k hst hs63 hb.kp hb.bx hb.r12 hb.r14 hb.v0 hb.fidx hb.ia
      hb.hw hb.fit (by rw [hb.rsp]; exact hb.stk) he hb.rd hb.sfit hb.sss (by rw [hb.rsp]; exact hb.ssb)
      fun t' g' _ w' _ F' => hb.eb.after hn32 g' w' (by rw [hb.rsp] at F'; exact F') (grFrame_sub hF.k hn32 S _ stack)
  have hP : ∀ t, EB p S (s₁.gpr .rsp) (s₁.gpr .rdx).toNat stack t →
      WP isa (Impl.SlhDsa.X86_64.Fors.pkFors (Impl.SlhDsa.X86_64.Shake.layout p) p.k f.t4name f.t4) t
        fun t' => t'.gpr .rbx = S := fun t h => by
    unfold Impl.SlhDsa.X86_64.Fors.pkFors
    refine WP.seq (WP.mono (pkf_ok hF h) fun u hu => WP.seq (WP.mono (pkc_ok hF T ht hst hs63 hu) fun v hv => ?_))
    have e8 : 8 * (p.n / 8) = p.n := by omega_using [hF.n]
    have eM : Layout.oMsg = 30496 := rfl
    have eB : Layout.laneB 0 = 3808 := rfl
    obtain ⟨_, _, he⟩ := h.env
    exact WP.mono (Levels.copy_ok (S := S) (t := .r15) (sr := .rbx) (by decide) (by decide)
      (a := Layout.oMsg) (b := 0) (d₁ := Layout.laneB 0 + (p.n + 32)) (d₂ := 0) (p.n / 8) v hv.2.1
      (by rw [hv.1]; exact Levels.scr0 S) (by rw [hv.2.2]; exact hu.hw) (by rw [eB, e8]; omega) (by rw [eM, e8]; omega)
      (by rw [eM, eB, e8]; omega)) fun w ⟨g, _⟩ => by rw [g _ (by decide), hv.1]
  have hct : RelCT isa (fun a b => Top p stack S (s₁.gpr .rsi) (s₁.gpr .rsp) (s₁.gpr .rdx).toNat md a ∧
      Top p stack S (s₁.gpr .rsi) (s₁.gpr .rsp) (s₁.gpr .rdx).toNat md b) (Impl.SlhDsa.X86_64.Verify.forsPk p f)
      fun _ _ => True := by
    unfold Impl.SlhDsa.X86_64.Verify.forsPk
    refine relSeq (ct_fpro hp fun a b ⟨⟨_, a1, _⟩, ⟨_, b1, _⟩⟩ r hr => ?_) hA hA
      (relSeq (RelCT.mono (groups_rel hp hfam T ht hst hs63) (fun _ _ h => h) fun _ _ _ => trivial) hG hG
        (relSeq (pk_rel hp hfam T ht hst hs63) hP hP (ct_rest fun a b ⟨a1, b1⟩ r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; rw [a1, b1]
    · simp only [List.mem_singleton] at hr; subst hr; rw [a1, b1]
  exact (hct _ _ _ _ _ _ ⟨⟨h₁, eS, rfl, rfl, rfl, emd⟩, ⟨h₂, by rw [← hp1, eS], hp2.symm, by rw [hp3], by rw [hp4],
    hmd₂⟩⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- `forsPk` meets `forsPkContract`, for the six SHAKE parameter sets and every
implementation of `thash4` that loads no MXCSR. -/
theorem forsPk_verified {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hp : P6 p) (hfam : p.family = .shake)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Verify.forsPk p f) (forsPkContract p stack) := by
  have hF := hp.fpar hfam
  exact ⟨forsPk_correct T ht hF hst hs63 hmx, forsPk_ct hp hfam T ht hst hs63,
    ⟨fsat p, fsat_pre (by omega_using [hF.n]) hF.a hF.k hs63⟩⟩

end VG.Proof.SlhDsa.X86_64.ForsCT
