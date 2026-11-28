module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsCT
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsMain
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA on AArch64: `levels`, verified

As on x86-64 (`Proof/SlhDsa/X86_64/LevelsCT.lean`): two runs of `levels`
from states of its precondition that agree on its public data (`scratch`,
`nodes`, `count`, `z₀`, `auth` and `sp`; not `idx` nor frame 3's parameters)
leak the same trace (`levels_ct`). Each run's state satisfies, at every
point of the code, the invariants its correctness proof uses, at the same
height `r` and group `j`, so two runs agree on the registers that address
memory and that the loops test; the code between the calls of `thash4`
is constant time by the taint analysis from those registers, for each of
the three sizes (the prologue and the alignment, the scan of a height, the
halving, the lanes, the arguments, the outputs, the next height, the
epilogue); the calls of `thash4` by its contract (`RelCT.call`). Then the
code has no frames and no depth, a state satisfies the precondition,
`Verified`, and a call of it (`levelscall_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Levels

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks
open VG.Proof.SlhDsa.AArch64.Wots4 (relSeq taintR Lays lays_of VK t4pre t4cov t4wr ce_gpr thashArgs_eq movz_ofNat add0
  laneA_eq eval_nz)
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64

/-! ## The blocks, by the taint analysis -/

section
variable {L : Layout} (hL : Lays L) {P : State → State → Prop}
include hL

theorem ct_pa (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], x.gpr r = y.gpr r) :
    RelCT isa P (.seq (.block Tree.pro) Tree.align) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_scan (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x20, .x21, .x23], x.gpr r = y.gpr r) :
    RelCT isa P (.seq (.block Tree.scanInit) (.loop (.block (Tree.scanBody L)) (.nonzero .x .x9))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_lanes (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x24], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Tree.levelLanes L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_args (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19], x.gpr r = y.gpr r) :
    RelCT isa P (.block (thashArgs L Layout.oA Layout.strideA (3 * L.n + 32))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_out (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x23, .x24], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Tree.levelOut L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_next (hr : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block (Tree.nextHeight L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;>
    exact taintR [] (fun x y h => ⟨hr x y h, fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide)

end

theorem ct_halve {P : State → State → Prop} (hr : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block Tree.halve) fun _ _ => True :=
  taintR [] (fun x y h => ⟨hr x y h, fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide)

theorem ct_restore {P : State → State → Prop} (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19], x.gpr r = y.gpr r) :
    RelCT isa P (.block (restoreRegs 3 Tree.saved)) fun _ _ => True :=
  taintR _ hr (by taint_decide)

/-- A relation proved for each pair of related states. -/
theorem relct_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ a b, P a b → RelCT isa (fun x y => x = a ∧ y = b) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-! ## The arguments of a call of `thash4`, and the call in two runs -/

section
variable {p : Params} {σ : State} {S AU : Addr} {idx c h z₀ : Nat} {pkSeed a16 : List Byte}

/-- What the arguments of a call of `thash4` on `A` leave. -/
structure LArgs (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (u : State) : Prop where
  base : Base hE u
  x0 : u.gpr .x0 = at' S 3136
  x1 : u.gpr .x1 = BitVec.ofNat 64 128
  x2 : u.gpr .x2 = BitVec.ofNat 64 (3 * p.n + 32)
  x3 : u.gpr .x3 = at' S (3136 + p.n + 32)
  x4 : u.gpr .x4 = S

theorem largs_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {t : State} (hb : Base hE t) :
    WP isa (.block (thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA (3 * p.n + 32))) t (LArgs hE) := by
  have hn := hz.n32
  rw [thashArgs_eq _ (show Layout.oA < 4096 by decide)]
  refine wp_addImm (by decide) fun t₁ u₁ => wp_movz fun t₂ u₂ => wp_movz fun t₃ u₃ =>
    wp_addImm (by simp only [Layout.msgOff]; omega_using [hn]) fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
  have hm : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h0 : t₁.gpr .x0 = at' S 3136 := by rw [u₁.gpr, hb.x19]; rfl
  refine ⟨hb.regs hm (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun g hg => by
      rcases lr_mem hg with rfl | rfl | rfl <;>
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h0]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, movz_ofNat (by decide)]; rfl
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, movz_ofNat (by omega_using [hn])]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h0]
    simp only [Layout.msgOff]; rw [ofNat_add', Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hb.x19, add0]

theorem largs_pre (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {u : State} (ha : LArgs hE u) :
    (thash4Contract p.n).pre (u.callEntry.withRegions [] (t4wr S 3136 128)) ∧
      Covers ([] ++ t4wr S 3136 128) (u.rd ++ u.wr) ∧ Covers (t4wr S 3136 128) u.wr := by
  have hn := hz.n32
  have h8 := hz.n8
  exact ⟨t4pre hE.scr_fit (by decide) (by decide) ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 (by omega_using [])
      (by omega_using [h8]) (by omega_using [hn]) (by omega_using [hn]),
    t4cov (hE.scr_mem ha.base.wr) (by decide)⟩

end

section
variable {p : Params} {σ₁ σ₂ : State} {S AU : Addr} {idx₁ idx₂ c h z₀ : Nat} {pk₁ a₁ pk₂ a₂ : List Byte}

/-- A call of `thash4` on the lanes `A`, in two runs each with `Base`. -/
theorem lcall_rel (hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {P : State → State → Prop} (hP : ∀ a b, P a b → Base hE₁ a ∧ Base hE₂ b) :
    RelCT isa P (thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (3 * p.n + 32)) fun _ _ => True := by
  refine RelCT.seq (RelCT.mono (RelCT.wp (F₁ := LArgs hE₁) (F₂ := LArgs hE₂)
      (ct_args (lays_of hz) fun a b hab => ⟨by rw [(hP a b hab).1.sp, (hP a b hab).2.sp, hsp], fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [(hP a b hab).1.x19, (hP a b hab).2.x19]⟩)
      fun a b hab => ⟨largs_ok hE₁ hz (hP a b hab).1, largs_ok hE₂ hz (hP a b hab).2⟩) (fun _ _ h => h)
      fun _ _ h => h.2) ?_
  refine RelCT.call T.verified.1 T.verified.2.1 [] (t4wr S 3136 128) fun a b ⟨u₁, u₂⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := largs_pre hE₁ hz u₁
  obtain ⟨p₂, c₂, w₂⟩ := largs_pre hE₂ hz u₂
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x0, u₂.x0]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x1, u₂.x1]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x2, u₂.x2]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x3, u₂.x3]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x4, u₂.x4]
  · simp only [State.withRegions_sp, State.callEntry_sp]; rw [u₁.base.sp, u₂.base.sp, hsp]

/-! ## The groups in two runs -/

/-- `Base`, and the group's and the height's counters. -/
def GB (hE : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (j P : Nat) (t : State) : Prop :=
  Base hE t ∧ t.gpr .x24 = BitVec.ofNat 64 j ∧ t.gpr .x23 = BitVec.ofNat 64 P

theorem gb_eq {hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁} {hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂}
    (hsp : σ₁.sp = σ₂.sp) {j P : Nat} {a b : State} (ha : GB hE₁ j P a) (hb : GB hE₂ j P b) :
    a.sp = b.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x23, .x24], a.gpr r = b.gpr r := by
  refine ⟨by rw [ha.1.sp, hb.1.sp, hsp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.1.x19, hb.1.x19]
  · rw [ha.1.x20, hb.1.x20]
  · rw [ha.2.2, hb.2.2]
  · rw [ha.2.1, hb.2.1]

/-- The lanes of a group, from `LvI`, to `GB`. -/
theorem lanes_gb (hE : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hz : Sz p) {z P : Nat} {L : List (List Byte)}
    {t₀ : State} (hs : LvStart hE t₀ L z P) {g : Nat} (hjP : 4 * g < P) {u : State}
    (hI : LvI hE t₀ L z P (4 * g) u) :
    WP isa (.block (Tree.levelLanes ⟨p.n, p.len⟩)) u (GB hE (4 * g) P) := by
  have hc13 := hE.c_le hz
  have hbase : baseA σ₁ S < 2 ^ 32 := hE.v1
  have hB : baseA σ₁ S / 2 ^ (z + 1) ≤ baseA σ₁ S / 2 := by
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]; exact Nat.div_le_self _ _
  have hPc := hs.Pc
  have hroom : Layout.oN + 2 * (4 * g) * p.n + 8 * p.n ≤ 65536 := by
    have := node_fit hE (i := 2 * (4 * g) + 7) (by omega_using [hjP, hPc])
    rw [show (2 * (4 * g) + 7) * p.n = 2 * (4 * g) * p.n + 7 * p.n by rw [Nat.add_mul]] at this; omega_using [this]
  refine WP.mono (lanes_ok hE hz (B := baseA σ₁ S / 2 ^ (z + 1)) hI.base (by rw [hI.keep _ (by decide), hs.x22]) hs.z14
    (by rw [hI.keep _ (by decide), hs.x27]) hI.x24 (by omega_using [hB, hbase, hjP, hc13, hPc]) hroom)
    fun t ⟨hb, hg, _, _⟩ => ⟨hb, by rw [hg _ (by decide), hI.x24], by rw [hg _ (by decide), hI.keep _ (by decide), hs.x23]⟩

theorem group_rel (hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) {z P : Nat} {L₁ L₂ : List (List Byte)}
    {t₁ t₂ : State} (hs₁ : LvStart hE₁ t₁ L₁ z P) (hs₂ : LvStart hE₂ t₂ L₂ z P) {g : Nat} (hjP : 4 * g < P) :
    RelCT isa (fun a b => LvI hE₁ t₁ L₁ z P (4 * g) a ∧ LvI hE₂ t₂ L₂ z P (4 * g) b)
      (Tree.levelBody ⟨p.n, p.len⟩ name T.code) fun _ _ => True :=
  relSeq (B₁ := GB hE₁ (4 * g) P) (B₂ := GB hE₂ (4 * g) P)
    (ct_lanes (lays_of hz) fun a b ⟨ha, hb⟩ => ⟨by rw [ha.base.sp, hb.base.sp, hsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [ha.base.x19, hb.base.x19]
      · rw [ha.base.x20, hb.base.x20]
      · rw [ha.x24, hb.x24]⟩)
    (fun _ h => lanes_gb hE₁ hz hs₁ hjP h) (fun _ h => lanes_gb hE₂ hz hs₂ hjP h)
  (relSeq (B₁ := GB hE₁ (4 * g) P) (B₂ := GB hE₂ (4 * g) P) (lcall_rel hE₁ hE₂ hsp hz T name fun a b h => ⟨h.1.1, h.2.1⟩)
    (fun _ h => lcall_ok hE₁ hz T name h.1 fun t' hb hg _ _ _ => ⟨hb, by rw [hg _ (by decide) (by decide), h.2.1],
      by rw [hg _ (by decide) (by decide), h.2.2]⟩)
    (fun _ h => lcall_ok hE₂ hz T name h.1 fun t' hb hg _ _ _ => ⟨hb, by rw [hg _ (by decide) (by decide), h.2.1],
      by rw [hg _ (by decide) (by decide), h.2.2]⟩)
    (ct_out (lays_of hz) fun a b ⟨ha, hb⟩ => gb_eq hsp ha hb))

/-- The groups of a height, in two runs. -/
theorem level_rel (hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) {z P : Nat} {L₁ L₂ : List (List Byte)}
    {t₁ t₂ : State} (hs₁ : LvStart hE₁ t₁ L₁ z P) (hs₂ : LvStart hE₂ t₂ L₂ z P) :
    RelCT isa (fun a b => a = t₁ ∧ b = t₂) (.loop (Tree.levelBody ⟨p.n, p.len⟩ name T.code) (.nonzero .x .x9))
      fun _ _ => True := by
  have hc13 := hE₁.c_le hz
  have hPc := hs₁.Pc
  let G := (P + 3) / 4
  refine RelCT.mono (RelCT.loop (fun n a b => ∃ g, n = G - g ∧ g < G ∧ LvI hE₁ t₁ L₁ z P (4 * g) a ∧
      LvI hE₂ t₂ L₂ z P (4 * g) b) (fun n => ?_) G)
    (fun a b ⟨e₁, e₂⟩ => ⟨0, by omega_using [], by have := hs₁.P1; omega_using [this], by rw [e₁]; exact hs₁.lvi0,
      by rw [e₂]; exact hs₂.lvi0⟩) fun _ _ h => h
  refine RelCT.exists_ fun g => ?_
  by_cases hg : g < G
  swap
  · exact RelCT.of_false fun _ _ h => hg h.2.1
  by_cases hn : n = G - g
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have hjP : 4 * g < P := by omega_using [hg]
  let X := fun (u : State) => u.gpr .x9 = (BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 P) >>> 63
  refine RelCT.mono (RelCT.wp (F₁ := fun u => LvI hE₁ t₁ L₁ z P (4 * (g + 1)) u ∧ X u)
      (F₂ := fun u => LvI hE₂ t₂ L₂ z P (4 * (g + 1)) u ∧ X u)
      (group_rel hE₁ hE₂ hsp hz T name hs₁ hs₂ hjP)
      fun a b ⟨ha, hb⟩ => ⟨levelStep_ok hE₁ hz T name hs₁ hjP ha, levelStep_ok hE₂ hz T name hs₂ hjP hb⟩)
    (fun a b ⟨e, _, ha, hb⟩ => ⟨ha, hb⟩) fun a b ⟨_, ⟨ha, za⟩, ⟨hb, zb⟩⟩ => ?_
  have ea := eval_lt za (by omega_using [hjP, hc13, hPc]) (by omega_using [hjP, hc13, hPc])
  have eb := eval_lt zb (by omega_using [hjP, hc13, hPc]) (by omega_using [hjP, hc13, hPc])
  refine ⟨by rw [ea, eb], fun _ => trivial, fun ht => ?_⟩
  by_cases hc' : 4 * g + 4 < P
  · exact ⟨G - (g + 1), by omega_using [hg, hc'], g + 1, rfl, by omega_using [hc'], ha, hb⟩
  · rw [ea, decide_eq_false hc'] at ht; cases ht

/-! ## The heights in two runs -/

theorem height_rel (hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) {r : Nat} (hr : r < h) :
    RelCT isa (fun a b => HI hE₁ r a ∧ HI hE₂ r b) (Tree.heightBody ⟨p.n, p.len⟩ name T.code) fun _ _ => True := by
  unfold Tree.heightBody
  refine RelCT.assoc (relSeq (B₁ := fun t => ∃ u, HI hE₁ r u ∧ ScanQ0 hE₁ r u t)
    (B₂ := fun t => ∃ u, HI hE₂ r u ∧ ScanQ0 hE₂ r u t)
    (ct_scan (lays_of hz) fun a b ⟨ha, hb⟩ => ⟨by rw [ha.base.sp, hb.base.sp, hsp], fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · rw [ha.base.x20, hb.base.x20]
      · rw [ha.x21, hb.x21]
      · rw [ha.x23, hb.x23]⟩)
    (fun a ha => WP.mono (scan_part hE₁ hz hr ha) fun t ht => ⟨a, ha, ht.1⟩)
    (fun b hb => WP.mono (scan_part hE₂ hz hr hb) fun t ht => ⟨b, hb, ht.1⟩) ?_)
  refine relSeq (B₁ := fun t => LvStart hE₁ t (up p σ₁ S c z₀ pk₁ a₁ r) (z₀ + r) (2 ^ (h - (r + 1))))
    (B₂ := fun t => LvStart hE₂ t (up p σ₂ S c z₀ pk₂ a₂ r) (z₀ + r) (2 ^ (h - (r + 1))))
    (ct_halve fun a b ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩⟩ => by rw [ha.1.sp, hb.1.sp, hsp])
    (fun _ ⟨u, hu, hq⟩ => halve_ok hE₁ hz hr hu hq) (fun _ ⟨u, hu, hq⟩ => halve_ok hE₂ hz hr hu hq) ?_
  refine relSeq (B₁ := Base hE₁) (B₂ := Base hE₂)
    (relct_pt fun a b ⟨ha, hb⟩ => level_rel hE₁ hE₂ hsp hz T name ha hb)
    (fun _ h => WP.mono (level_ok hE₁ hz T name h) fun _ ⟨_, _, hl⟩ => hl.base)
    (fun _ h => WP.mono (level_ok hE₂ hz T name h) fun _ ⟨_, _, hl⟩ => hl.base)
    (ct_next (lays_of hz) fun a b ⟨ha, hb⟩ => by rw [ha.sp, hb.sp, hsp])

theorem heights_rel (hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    RelCT isa (fun a b => HI hE₁ 0 a ∧ HI hE₂ 0 b) (.loop (Tree.heightBody ⟨p.n, p.len⟩ name T.code) (.nonzero .x .x9))
      (fun a b => HI hE₁ h a ∧ HI hE₂ h b) := by
  have hh := hE₁.h_le
  have h1 := hE₁.h_pos
  refine RelCT.mono (RelCT.loop (fun n a b => ∃ r, n = h - r ∧ r < h ∧ HI hE₁ r a ∧ HI hE₂ r b) (fun n => ?_) h)
    (fun a b ⟨ha, hb⟩ => ⟨0, by omega_using [], by omega_using [h1], ha, hb⟩) fun _ _ h => h
  refine RelCT.exists_ fun r => ?_
  by_cases hr : r < h
  swap
  · exact RelCT.of_false fun _ _ h => hr h.2.1
  by_cases hn : n = h - r
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  let X := fun (u : State) => u.gpr .x9 = BitVec.ofNat 64 (2 ^ (h - (r + 1))) - BitVec.ofNat 64 1
  refine RelCT.mono (RelCT.wp (F₁ := fun u => HI hE₁ (r + 1) u ∧ X u) (F₂ := fun u => HI hE₂ (r + 1) u ∧ X u)
      (height_rel hE₁ hE₂ hsp hz T name hr)
      fun a b ⟨ha, hb⟩ => ⟨height_ok hE₁ hz T name hr ha, height_ok hE₂ hz T name hr hb⟩)
    (fun a b ⟨_, _, ha, hb⟩ => ⟨ha, hb⟩) fun a b ⟨_, ⟨ha, za⟩, ⟨hb, zb⟩⟩ => ?_
  have hp : 2 ^ (h - (r + 1)) < 2 ^ 64 := by
    have := pow_lt (h := h) (r := r + 1) (by omega_using [hh]); omega_using [this]
  have ea := eval_nz za hp (by decide)
  have eb := eval_nz zb hp (by decide)
  refine ⟨by rw [ea, eb], fun hf => ?_, fun ht => ?_⟩
  · by_cases e : r + 1 = h
    · rw [e] at ha hb; exact ⟨ha, hb⟩
    · rw [ea, decide_eq_false (fun h' => e (by have := pow_eq_one.mp h'; omega_using [this, hr]))] at hf; cases hf
  · by_cases e : r + 1 = h
    · rw [ea, decide_eq_true (pow_eq_one.mpr (by omega_using [e]))] at ht; cases ht
    · exact ⟨h - (r + 1), by omega_using [hr, e], r + 1, rfl, by omega_using [hr, e], ha, hb⟩

theorem levels_rel (hE₁ : Entry p σ₁ S AU idx₁ c h z₀ pk₁ a₁) (hE₂ : Entry p σ₂ S AU idx₂ c h z₀ pk₂ a₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (Tree.levels ⟨p.n, p.len⟩ name T.code) fun _ _ => True := by
  unfold Tree.levels
  refine RelCT.assoc (relSeq (B₁ := SH hE₁ z₀) (B₂ := SH hE₂ z₀)
    (ct_pa (lays_of hz) fun a b ⟨e₁, e₂⟩ => by
      rw [e₁, e₂]
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hE₁.x0, hE₂.x0]
      · rw [hE₁.x1, hE₂.x1]
      · rw [hE₁.x2, hE₂.x2]
      · rw [hE₁.x3, hE₂.x3]
      · rw [hE₁.x4, hE₂.x4])
    (fun _ e => by rw [e]; exact WP.seq (WP.mono (pro_ok hE₁) fun _ h => align_ok hE₁ h))
    (fun _ e => by rw [e]; exact WP.seq (WP.mono (pro_ok hE₂) fun _ h => align_ok hE₂ h)) ?_)
  exact RelCT.seq (RelCT.mono (heights_rel hE₁ hE₂ hsp hz T name) (fun a b ⟨ha, hb⟩ => ⟨hi0 hE₁ hz ha, hi0 hE₂ hz hb⟩)
    fun _ _ h => h)
    (ct_restore fun a b ⟨ha, hb⟩ => ⟨by rw [ha.base.sp, hb.base.sp, hsp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.base.x19, hb.base.x19]⟩)

end

/-- `levels` is constant time. -/
theorem levels_ct {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    ConstantTime isa (levelsContract p).pre (levelsContract p).pub (Tree.levels ⟨p.n, p.len⟩ name T.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨_, _, hE₁⟩ := entry_of h₁
  obtain ⟨_, _, hE₂⟩ := entry_of h₂
  obtain ⟨p0, p1, p2, p3, p4, psp⟩ := hp
  simp only [heightsOf] at hE₁ hE₂
  rw [← p0, ← p2, ← p3, ← p4] at hE₂
  exact (levels_rel hE₁ hE₂ psp hz T name _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Frames, depth, and calls of `levels` -/

/-- `levels` has no frames (and so never writes `sp`). -/
theorem levels_noFrames (L : Layout) (name : String) {t4 : Prog isa} (h : t4.noFrames = true) :
    (Tree.levels L name t4).noFrames = true := by
  simp [Tree.levels, Tree.align, Tree.heightBody, Tree.levelBody, thashCall, Code.noFrames, h]

theorem levels_depth (L : Layout) (name : String) {t4 : Prog isa} (h : t4.aarch64Depth = 0) :
    (Tree.levels L name t4).aarch64Depth = 0 := by
  simp [Tree.levels, Tree.align, Tree.heightBody, Tree.levelBody, thashCall, Code.aarch64Depth, h]

/-- A call of `levels`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem levelscall_ok {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name wn : String) {s : State}
    {rd wr : List Region} (hpre : (levelsContract p).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (levelsContract p).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call wn (Tree.levels ⟨p.n, p.len⟩ name T.code)) s Q :=
  WP.callV (levels_correct hz T name) hpre hc hw (fun s' h₁ h₂ h₃ h₄ h₅ _ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₇ h₈)
    (levels_noFrames _ name T.noFrames)

/-! ## A state satisfying the precondition -/

/-- `scratch` and the path in the witness. -/
abbrev satS : Addr := BitVec.ofNat 64 0x100000
abbrev satAU : Addr := BitVec.ofNat 64 0x10000

/-- The witness: zeros everywhere; two nodes, one height from 0, `idx` 0. -/
def lsat (p : Params) : State where
  gpr r := match r with
    | .x0 => satS | .x1 => at' satS Layout.oN | .x2 => 2 | .x4 => satAU | _ => 0
  sp := BitVec.ofNat 64 0x200000
  mem := fun _ => 0
  rd := []
  wr := [⟨satS, scratchLen⟩, ⟨satAU, 1 * p.n⟩]

theorem lsat_pre {p : Params} (hz : Sz p) : (levelsContract p).pre (lsat p) := by
  have hn := hz.n32
  have hS : satS.toNat = 0x100000 := rfl
  have hG : satAU.toNat = 0x10000 := rfl
  have hh : heightsOf (lsat p) = 1 := by
    show ((2 : BitVec 64).toNat).log2 = 1
    rw [show (2 : BitVec 64).toNat = 2 ^ 1 from rfl, Nat.log2_two_pow]
  have hv : ∀ i, varAt (lsat p).mem satS 3 i = 0 := fun i => by
    simp only [varAt, lsat, Mem.readW]
    rw [Mem.read_eq_of_bytes (v := 0) fun j _ => (BitVec.eq_of_toNat_eq (by simp)).symm]
    rfl
  refine ⟨?_, ⟨List.replicate p.n 0, List.replicate 16 0, fun k _ => Wots4.bytesAt_zero _ _,
      fun k _ => Wots4.bytesAt_zero _ _, fun k _ => Wots4.bytesAt_zero _ _, fun k _ => Wots4.bytesAt_zero _ _⟩,
    rfl, by rw [hh], ?_, ?_, ?_, by show (0 : BitVec 64).toNat < 2 ^ 32; decide, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    exact ⟨rfl, rfl, by show satS.toNat + scratchLen ≤ _; rw [hS]; decide,
      by show satAU.toNat + 1 * p.n ≤ _; rw [hG]; omega_using [hn],
      Offset.disjoint_of_le (by show satAU.toNat + 1 * p.n ≤ satS.toNat; rw [hG, hS]; omega_using [hn])
        (by show satS.toNat + Layout.oSigTmp ≤ _; rw [hS]; decide),
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  · rw [hh]; show (0 : BitVec 64).toNat + 1 ≤ 14; decide
  · rw [hh]; rfl
  · show ((2 : BitVec 64).toNat + 8) * p.n ≤ 32 * Layout.nodeSlots; rw [Wots4.nodeSlots_eq]
    show (2 + 8) * p.n ≤ 32 * 520; omega_using [hn]
  all_goals (show (varAt (lsat p).mem satS 3 _).toNat < 2 ^ 32; rw [hv]; decide)

/-! ## `Verified` -/

/-- `levels` meets `levelsContract`, for every implementation of `thash4`. -/
theorem levels_verified {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    Verified AArch64.target (Tree.levels ⟨p.n, p.len⟩ name T.code) (levelsContract p) :=
  ⟨levels_correct hz T name, levels_ct hz T name, ⟨lsat p, lsat_pre hz⟩⟩

end VG.Proof.SlhDsa.AArch64.Levels
