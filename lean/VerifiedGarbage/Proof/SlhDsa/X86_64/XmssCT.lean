module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssMain
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssMain
public meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# SLH-DSA (SHAKE) on x86-64: `xmssTree` is constant time, and `Verified`
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.XmssTree

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs)

open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add in_scr in_scr' at_add)

/-! ## The blocks, by the taint analysis -/

section
variable {P : State → State → Prop}

/-- The sizes of `h′`: those of the SHAKE parameter sets. -/
abbrev Hps (hp : Nat) : Prop := hp = 3 ∨ hp = 4 ∨ hp = 8 ∨ hp = 9

theorem ct_b1 {L : Layout} (hL : Wots4.Lays L) (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rdi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Xmss.pro ++ Impl.SlhDsa.X86_64.Xmss.digits L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact Levels.taintR _ hr (by taint_decide)

theorem ct_leaf1 (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rdi (.reg .rbx), .mov .rsi (.mem (Impl.SlhDsa.X86_64.Xmss.var 0)),
      .mov .rdx (.reg .r12), .mov .rcx (.reg .r13)]) fun _ _ => True :=
  Levels.taintR _ hr (by taint_decide)

theorem ct_leaf3 {hp : Nat} (hh : Hps hp) (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Xmss.var 0)), .alu .add .rax (.imm 4),
      .store (Impl.SlhDsa.X86_64.Xmss.var 0) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ hp)))]) fun _ _ => True := by
  rcases hh with rfl | rfl | rfl | rfl <;> exact Levels.taintR _ hr (by taint_decide)

theorem ct_hb {L : Layout} (hL : Wots4.Lays L) {hp : Nat} (hh : Hps hp)
    (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r13], x.gpr r = y.gpr r) :
    RelCT isa P (.block (hbCode L hp)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
    exact Levels.taintR _ hr (by taint_decide)

theorem ct_tail {L : Layout} (hL : Wots4.Lays L) (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r15], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.copyWords .r15 0 .rbx Layout.oN (L.n / 8) ++ restoreRegs 1))
      fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact Levels.taintR _ hr (by taint_decide)

end

/-! ## The calls, in one run -/

variable {p : Params}

/-- What a call of `wotsLeaves4` needs, after the arguments' block. -/
structure Call1 (p : Params) (T : Thash4Impl p.n) (σ : State) (S sig : Addr) (j : Nat) (v : State) : Prop where
  rdi : v.gpr .rdi = S
  rsi : v.gpr .rsi = BitVec.ofNat 64 (4 * j)
  rcx : v.gpr .rcx = sig
  sp : v.gpr .rsp = σ.gpr .rsp
  bx : v.gpr .rbx = S
  pre : (wots4Contract p (8 + T.stack)).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩])
  c₁ : Covers ([] ++ [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩]) (v.rd ++ v.wr)
  c₂ : Covers [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] v.wr

theorem b1_ok (hz : Wots4.Sz p) (T : Thash4Impl p.n) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp9 : p.hp ≤ 9)
    {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions stack σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .rsi).toNat < 2 ^ 32)
    {j : Nat} (hj : 4 * (j + 1) ≤ 2 ^ p.hp) {u : State} (hI : LInv p stack σ S sig pk a sk M j u) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.mem (Impl.SlhDsa.X86_64.Xmss.var 0)),
      .mov .rdx (.reg .r12), .mov .rcx (.reg .r13)]) u (Call1 p T σ S sig j) := by
  have h512 : 2 ^ p.hp ≤ 512 := by
    calc 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp9
      _ = 512 := rfl
  have hX : p.len * p.n ≤ p.xmssSigLen := by simp only [Params.xmssSigLen, Nat.add_mul]; omega
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun _ => rfl
  refine wp_mov fun u₁ e₁ => wp_movm (a := at' S (Layout.oVar 1 0))
    (by rw [Impl.SlhDsa.X86_64.Xmss.var, ea_at, e₁.other _ (by decide), hI.bx])
    (by rw [e₁.rd, e₁.wr, hI.wr]; exact in_scr' hwS (by rw [eV]; omega)) fun u₂ e₂ =>
      wp_mov fun u₃ e₃ => wp_mov fun u₄ e₄ => WP.block_nil ?_
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have a1 : u₄.gpr .rdi = S := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, hI.bx]
  have a2 : u₄.gpr .rsi = BitVec.ofNat 64 (4 * j) := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.mem, hI.v0]
  have a3 : u₄.gpr .rdx = σ.gpr .rsi := by
    rw [e₄.other _ (by decide), e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hI.r12]
  have a4 : u₄.gpr .rcx = sig := by
    rw [e₄.gpr, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hI.r13]
  have asp : u₄.gpr .rsp = σ.gpr .rsp := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hI.sp]
  have abx : u₄.gpr .rbx = S := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hI.bx]
  have awr : u₄.wr = σ.wr := by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr, hI.wr]
  have hdig : ∀ i < p.len, digitAt u₄.mem S i < 16 := fun i hi => by
    rw [hm₄, hI.dig i hi]; exact wotsDigits_lt p hz.lgw hz.nv M i
  obtain ⟨hpre, hc, hw⟩ := wots_pre hz (stk := 8 + T.stack) (by omega) hs63 hR hX (by omega) a1 a2
    (by rw [a3]; exact hidx) a4 asp awr (by rw [hm₄]; exact hI.env) hdig
  exact ⟨a1, a2, a4, asp, abx, hpre, hc, hw⟩

/-- What a call of `levels` needs, after the heights block. -/
structure Call2 (p : Params) (T : Thash4Impl p.n) (σ : State) (S AU : Addr) (v : State) : Prop where
  rdi : v.gpr .rdi = S
  rsi : v.gpr .rsi = at' S Layout.oN
  rdx : v.gpr .rdx = BitVec.ofNat 64 (2 ^ p.hp)
  rcx : v.gpr .rcx = 0
  r8 : v.gpr .r8 = AU
  sp : v.gpr .rsp = σ.gpr .rsp
  pre : (levelsContract p (T.stack + 16)).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩])
  c₁ : Covers ([] ++ [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩]) (v.rd ++ v.wr)
  c₂ : Covers [⟨S, scratchLen⟩, ⟨AU, p.hp * p.n⟩] v.wr

theorem hb1_ok (hz : Wots4.Sz p) (T : Thash4Impl p.n) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9)
    {σ : State} {S sig : Addr} {pk a sk M : List Byte}
    (hR : Regions stack σ S [] ⟨sig, p.xmssSigLen⟩) (hidx : (σ.gpr .rsi).toNat < 2 ^ 32)
    {u : State} (hI : LInv p stack σ S sig pk a sk M (2 ^ (p.hp - 2)) u) :
    WP isa (.block (hbCode (Wots4.L p) p.hp)) u (Call2 p T σ S (sig + BitVec.ofNat 64 (p.len * p.n))) := by
  have hn32 := hz.n32
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have hws : (⟨sig, p.xmssSigLen⟩ : Region) ∈ σ.wr := by rw [hR.wr_eq]; simp
  have hsigd : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  have hSL : p.xmssSigLen = p.len * p.n + p.hp * p.n := by simp only [Params.xmssSigLen, Nat.add_mul]
  refine hblock_ok hz hhp9 hI.bx hI.r13 (by rw [hI.wr]; exact hwS) (by rw [hI.wr]; exact hws) hR.out_fit
    hsigd fun v hv => ?_
  have hsp : v.gpr .rsp = σ.gpr .rsp := by
    rw [hv.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hI.sp]
  have hvenv : Env p v.mem S pk a := env_frame hn32 hI.env hv.frame fun {o l} ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hsigd.sub_left (Offset.sub_base sig (by omega))).sub_right
        (Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; omega))).symm
    · exact Levels.disj_scr S (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega) (by omega)
        (by rw [show Layout.oVar 4 5 = 3000 from rfl]; omega)
  obtain ⟨hpre, hc, hw⟩ := levels_pre hz.nv (by omega) hhp9 (stk := T.stack + 16) (by omega) hs63 hR rfl
    (by rw [hSL]) hv.rdi hv.rsi hv.rdx hv.rcx hv.r8 (by rw [hv.r9, hI.r12]; exact hidx) hsp
    (by rw [hv.wr, hI.wr]) hvenv fun i h₁ h₂ => by rw [hv.vars i h₁ h₂]; split <;> decide
  exact ⟨hv.rdi, hv.rsi, hv.rdx, hv.rcx, hv.r8, hsp, hpre, hc, hw⟩

/-! ## Two runs -/

theorem wots_pub {v₁ v₂ : State} {T : Thash4Impl p.n} {σ₁ σ₂ : State} {S sig : Addr} {j : Nat}
    (h₁ : Call1 p T σ₁ S sig j v₁) (h₂ : Call1 p T σ₂ S sig j v₂) (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) {W : List Region} :
    (wots4Contract p (8 + T.stack)).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [wots4Contract, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_rsp, State.callEntry_rsp, h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rcx, h₂.rcx, h₁.sp, h₂.sp, hsp]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A pass of the leaves' loop, in two runs at the same point. -/
theorem body_ct (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hh : Hps p.hp)
    {σ₁ σ₂ : State} {S sig : Addr} {pk₁ a₁ sk₁ M₁ pk₂ a₂ sk₂ M₂ : List Byte}
    (hR₁ : Regions stack σ₁ S [] ⟨sig, p.xmssSigLen⟩) (hR₂ : Regions stack σ₂ S [] ⟨sig, p.xmssSigLen⟩)
    (hidx₁ : (σ₁.gpr .rsi).toNat < 2 ^ 32) (hidx₂ : (σ₂.gpr .rsi).toNat < 2 ^ 32)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (m : Nat) :
    RelCT isa (fun a b => LI p stack σ₁ S sig pk₁ a₁ sk₁ M₁ m a ∧ LI p stack σ₂ S sig pk₂ a₂ sk₂ M₂ m b)
      (Impl.SlhDsa.X86_64.Xmss.leafBody (Wots4.L p) p.hp t4name wn T.code) fun _ _ => True := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  have h4 : 2 ^ p.hp = 4 * 2 ^ (p.hp - 2) := by
    rw [show p.hp = p.hp - 2 + 2 by omega, Nat.pow_add, Nat.add_sub_cancel]; omega
  by_cases hm : 1 ≤ m ∧ m ≤ 2 ^ (p.hp - 2)
  · have key : ∀ {σ : State} {pk a sk M : List Byte} {u : State}, LI p stack σ S sig pk a sk M m u →
        LInv p stack σ S sig pk a sk M (2 ^ (p.hp - 2) - m) u := by
      rintro σ pk a sk M u ⟨j, rfl, hj, h⟩; rwa [show 2 ^ (p.hp - 2) - (2 ^ (p.hp - 2) - j) = j by omega]
    have hj : 4 * (2 ^ (p.hp - 2) - m + 1) ≤ 2 ^ p.hp := by omega
    unfold Impl.SlhDsa.X86_64.Xmss.leafBody
    refine Levels.relSeq (ct_leaf1 fun x y ⟨hx, hy⟩ r hr => ?_)
      (fun x hx => b1_ok hz T hst hs63 hhp9 hR₁ hidx₁ hj (key hx))
      (fun y hy => b1_ok hz T hst hs63 hhp9 hR₂ hidx₂ hj (key hy)) ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [(key hx).bx, (key hy).bx]
    refine Levels.relSeq (B₁ := fun w => w.gpr .rbx = S) (B₂ := fun w => w.gpr .rbx = S)
      (RelCT.call (Wots4.wots4_correct hz T t4name) (Wots4.wots4_ct hz T t4name) []
        [⟨S, scratchLen⟩, ⟨sig, p.len * p.n⟩] fun x y ⟨hx, hy⟩ =>
          ⟨hx.pre, hy.pre, wots_pub hx hy hsp, hx.c₁, hx.c₂, hy.c₁, hy.c₂, by rw [hx.sp, hy.sp, hsp]⟩)
      (fun x hx => Wots4.wots4call_ok hz T t4name wn hx.pre hx.c₁ hx.c₂ fun s' _ _ h₃ _ _ _ => by
        rw [h₃ .rbx (by simp [calleeSaved]), hx.bx])
      (fun y hy => Wots4.wots4call_ok hz T t4name wn hy.pre hy.c₁ hy.c₂ fun s' _ _ h₃ _ _ _ => by
        rw [h₃ .rbx (by simp [calleeSaved]), hy.bx])
      (ct_leaf3 hh fun x y ⟨hx, hy⟩ r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy]
  · refine RelCT.of_false fun x y ⟨⟨j, hj₁, hj₂, _⟩, _⟩ => hm ⟨by omega, by omega⟩

theorem levels_pub {v₁ v₂ : State} {T : Thash4Impl p.n} {σ₁ σ₂ : State} {S AU : Addr}
    (h₁ : Call2 p T σ₁ S AU v₁) (h₂ : Call2 p T σ₂ S AU v₂) (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) {W : List Region} :
    (levelsContract p (T.stack + 16)).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [levelsContract, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_rsp, State.callEntry_rsp, h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi,
    h₁.rdx, h₂.rdx, h₁.rcx, h₂.rcx, h₁.r8, h₂.r8, h₁.sp, h₂.sp, hsp]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The heights, in two runs. -/
theorem heights_ct (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hh : Hps p.hp)
    {σ₁ σ₂ : State} {S sig : Addr} {pk₁ a₁ sk₁ M₁ pk₂ a₂ sk₂ M₂ : List Byte}
    (hR₁ : Regions stack σ₁ S [] ⟨sig, p.xmssSigLen⟩) (hR₂ : Regions stack σ₂ S [] ⟨sig, p.xmssSigLen⟩)
    (hidx₁ : (σ₁.gpr .rsi).toNat < 2 ^ 32) (hidx₂ : (σ₂.gpr .rsi).toNat < 2 ^ 32)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) :
    RelCT isa (fun a b => LInv p stack σ₁ S sig pk₁ a₁ sk₁ M₁ (2 ^ (p.hp - 2)) a ∧
        LInv p stack σ₂ S sig pk₂ a₂ sk₂ M₂ (2 ^ (p.hp - 2)) b)
      (Impl.SlhDsa.X86_64.Xmss.heights (Wots4.L p) p.hp t4name ln T.code) fun _ _ => True := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  have hs : T.stack + 16 < 2 ^ 63 := by omega
  unfold Impl.SlhDsa.X86_64.Xmss.heights
  refine Levels.relSeq (ct_hb hz.lays hh fun x y ⟨hx, hy⟩ r hr => ?_)
    (fun x hx => hb1_ok hz T hst hs63 hhp hhp9 hR₁ hidx₁ hx)
    (fun y hy => hb1_ok hz T hst hs63 hhp hhp9 hR₂ hidx₂ hy)
    (RelCT.call (Levels.levels_correct T t4name hz.nv hz.shake (Nat.le_refl _) hs)
      (Levels.levels_ct T t4name hz.nv hz.shake (Nat.le_refl _) hs) []
      [⟨S, scratchLen⟩, ⟨sig + BitVec.ofNat 64 (p.len * p.n), p.hp * p.n⟩] fun x y ⟨hx, hy⟩ =>
        ⟨hx.pre, hy.pre, levels_pub hx hy hsp, hx.c₁, hx.c₂, hy.c₁, hy.c₂, by rw [hx.sp, hy.sp, hsp]⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx.bx, hy.bx]
  · rw [hx.r13, hy.r13]

/-- A state of the precondition with the given public data. -/
abbrev XPub (p : Params) (stack : Nat) (S SIG SP : Addr) (s : State) : Prop :=
  (xmssContract p stack).pre s ∧ s.gpr .rdi = S ∧ s.gpr .rdx = SIG ∧ s.gpr .rsp = SP

theorem xmss_ct (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hh : Hps p.hp) :
    ConstantTime isa (xmssContract p stack).pre (xmssContract p stack).pub
      (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln T.code) := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp1, hp2, hp3⟩ := hpub
  obtain ⟨hR₁, ⟨pk₁, a₁, hE₁⟩, hidx₁⟩ := h₁
  obtain ⟨hR₂, ⟨pk₂, a₂, hE₂⟩, hidx₂⟩ := h₂
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .rdi = S := ⟨_, rfl⟩
  have eS₂ : s₂.gpr .rdi = S := by rw [← hp1, eS]
  rw [eS] at hR₁ hE₁
  rw [eS₂] at hR₂ hE₂
  have hR₂' : Regions stack s₂ S [] ⟨s₁.gpr .rdx, p.xmssSigLen⟩ := by rw [hp2]; exact hR₂
  -- the runs, each with its own invariants
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂)
      (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln T.code) fun _ _ => True := by
    unfold Impl.SlhDsa.X86_64.Xmss.xmssTree
    refine Levels.relSeq (ct_b1 hz.lays fun x y ⟨hx, hy⟩ r hr => ?_)
      (fun x hx => by rw [hx]; exact entry_ok hz eS hR₁ hE₁ rfl fun u hu => (⟨0, by omega, Nat.one_le_two_pow, hu⟩ :
        LI p stack s₁ S (s₁.gpr .rdx) pk₁ a₁ _ _ (2 ^ (p.hp - 2)) u))
      (fun y hy => by
        rw [hy]; exact entry_ok hz eS₂ hR₂ hE₂ rfl fun u hu => (⟨0, by omega, Nat.one_le_two_pow, by rw [← hp2] at hu; exact hu⟩ :
          LI p stack s₂ S (s₁.gpr .rdx) pk₂ a₂ _ _ (2 ^ (p.hp - 2)) u)) ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy, hp1]
    refine Levels.relSeq (RelCT.mono (Levels.relLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
        (body_ct hz T t4name wn hst hs63 hh hR₁ hR₂' hidx₁ hidx₂ hp3)
        (leaves_step hz T t4name wn hst hs63 hhp hhp9 hR₁ hidx₁)
        (leaves_step hz T t4name wn hst hs63 hhp hhp9 hR₂' hidx₂) (2 ^ (p.hp - 2))) (fun _ _ h => h)
          fun _ _ _ => trivial)
      (fun x hx => Levels.wpLoop _ _ (leaves_step hz T t4name wn hst hs63 hhp hhp9 hR₁ hidx₁) _ hx)
      (fun y hy => Levels.wpLoop _ _ (leaves_step hz T t4name wn hst hs63 hhp hhp9 hR₂' hidx₂) _ hy) ?_
    refine Levels.relSeq (heights_ct hz T t4name ln hst hs63 hh hR₁ hR₂' hidx₁ hidx₂ hp3)
      (fun x hx => heights_ok hz T t4name ln hst hs63 hhp hhp9 hR₁ hidx₁ hx)
      (fun y hy => heights_ok hz T t4name ln hst hs63 hhp hhp9 hR₂' hidx₂ hy)
      (ct_tail hz.lays fun x y ⟨hx, hy⟩ r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.bx, hy.bx]
    · rw [hx.r15, hy.r15]
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The stack pointer, the depth of calls, and calls of `xmssTree` -/

/-- `xmssTree` never writes `rsp` itself. -/
theorem xmss_nosp (hz : Wots4.Sz p) (t4name wn ln : String) {t4 : Prog isa} (hT : NoSp t4) :
    NoSp (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln t4) := by
  unfold Impl.SlhDsa.X86_64.Xmss.xmssTree Impl.SlhDsa.X86_64.Xmss.leafBody Impl.SlhDsa.X86_64.Xmss.heights
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (fun i hi => Levels.nosp_seq
    (Levels.nosp_block (by kernel_rfl)) (Levels.nosp_seq (fun i hi => Wots4.wots4_nosp hz.lays t4name hT i hi)
      (Levels.nosp_block (by kernel_rfl))) i hi)
    (Levels.nosp_seq (Levels.nosp_seq (Levels.nosp_block ?_) (fun i hi => Levels.levels_nosp hz.nv t4name hT i hi))
      (Levels.nosp_block ?_)))
  · simp [Impl.SlhDsa.X86_64.Xmss.pro, Impl.SlhDsa.X86_64.Xmss.digits, Impl.SlhDsa.X86_64.Xmss.digitByte, saveRegs,
      List.all_flatMap, Taint.clobbers, Taint.dstOf]
  · simp [Impl.SlhDsa.X86_64.Tree.setParams, Taint.clobbers, Taint.dstOf]
  · simp [Impl.SlhDsa.X86_64.copyWords, restoreRegs, List.all_flatMap, Taint.clobbers, Taint.dstOf]; decide

theorem xmss_depth (L : Layout) (hp : Nat) (t4name wn ln : String) (t4 : Prog isa) :
    (Impl.SlhDsa.X86_64.Xmss.xmssTree L hp t4name wn ln t4).depth = t4.depth + 2 := by
  have h₁ := Wots4.wots4_depth L t4name t4
  have h₂ := Levels.levels_depth L t4name t4
  simp only [Impl.SlhDsa.X86_64.Xmss.xmssTree, Impl.SlhDsa.X86_64.Xmss.leafBody, Impl.SlhDsa.X86_64.Xmss.heights,
    Code.depth, h₁, h₂, Nat.zero_max, Nat.max_zero, Nat.max_self]

/-- A call of `xmssTree`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem xmsscall_ok (hz : Wots4.Sz p) (T : Thash4Impl p.n) (t4name wn ln xn : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) (hhp : 2 ≤ p.hp) (hhp9 : p.hp ≤ 9) {s : State}
    {rd wr : List Region} (hpre : (xmssContract p stack).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (T.code.depth + 3))]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (xmssContract p stack).post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call xn (Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp t4name wn ln T.code)) s Q := by
  have hd := T.depth_le
  exact WP.call_mx (xmss_correct hz T t4name wn ln hst hs63 hhp hhp9) (xmss_nosp hz t4name wn ln T.nosp)
    (by rw [xmss_depth]; omega_using [hd]) hpre hc hw fun s' h₁ h₂ h₃ h₄ _ h₆ h₇ =>
      hQ s' h₁ h₂ h₃ (by rw [xmss_depth] at h₄; exact h₄) h₆ h₇

/-! ## A state satisfying the precondition -/

/-- `levels`'s witness with the signature at `lAU`, for the key pair 0. -/
def xsat (p : Params) : State where
  gpr r := match r with
    | .rdi => Levels.lS | .rdx => Levels.lAU | .rsp => Levels.lsp | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := Levels.lmem
  rd := []
  wr := [⟨Levels.lS, scratchLen⟩, ⟨Levels.lAU, p.xmssSigLen⟩]

theorem xsat_pre (hz : Wots4.Sz p) (hhp9 : p.hp ≤ 9) {stack : Nat} (hs63 : stack < 2 ^ 63) :
    (xmssContract p stack).pre (xsat p) := by
  have hn32 := hz.n32
  have hl := hz.len
  have hln : p.len * p.n ≤ 2144 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have hSL : p.xmssSigLen ≤ 2432 := by
    simp only [Params.xmssSigLen, Nat.add_mul]; have := Nat.mul_le_mul hhp9 hn32; omega
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have hAs : Region.Disjoint ⟨Levels.lAU, p.xmssSigLen⟩ ⟨Levels.lS, Layout.oSigTmp⟩ :=
    Offset.disjoint Levels.lsp (.inr (by rw [eT]; omega)) (by omega) (by rw [eT]; omega)
  refine ⟨⟨rfl, rfl, by show Levels.lS.toNat + scratchLen ≤ 2 ^ 64; rw [Levels.lS_toNat]; decide, ?_, hAs,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
    fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, Levels.lsat_rc, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
      fun k hk => ?_⟩, by show (0 : BitVec 64).toNat < 2 ^ 32; decide⟩
  · show (Levels.lsp + BitVec.ofNat 64 0x200000).toNat + p.xmssSigLen ≤ 2 ^ 64
    have : (Levels.lsp + BitVec.ofNat 64 0x200000).toNat = 2 ^ 63 + 0x200000 := by decide
    omega
  · exact (Offset.disjoint_base Levels.lsp (k := 8) (by omega) (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · exact (Offset.disjoint_base Levels.lsp (k := 8) (by omega) (by omega)).symm
  · exact (Offset.disjoint_below Levels.lsp (n := stack) (d := 0x100000) (k := scratchLen)
      (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · exact (Offset.disjoint_below Levels.lsp (n := stack) (d := 0x200000) (k := p.xmssSigLen) (by omega)).symm
  · exact (Levels.lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (Levels.lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))
  · exact (Levels.lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (Levels.lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))

/-! ## `Verified` -/

/-- `xmssTree` for the SHAKE parameter sets, with any `thash4`. -/
theorem xmss_verified (hz : Wots4.Sz p) (hh : Hps p.hp) (T : Thash4Impl p.n) (t4name wn ln : String) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Xmss.xmssTree ⟨p.n, p.len⟩ p.hp t4name wn ln T.code)
      (xmssContract p (T.stack + 24)) := by
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  have hs : T.stack + 24 < 2 ^ 63 := by have := T.stack_le; omega
  exact ⟨xmss_correct hz T t4name wn ln (Nat.le_refl _) hs hhp hhp9, xmss_ct hz T t4name wn ln (Nat.le_refl _) hs hh,
    ⟨xsat p, xsat_pre hz hhp9 hs⟩⟩

end VG.Proof.SlhDsa.X86_64.XmssTree
