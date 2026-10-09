import VerifiedGarbage.Proof.Ed25519.X86.FieldCT
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport

/-!
# Code with calls on x86 (32-bit): two runs, with what the taint analysis knows

Code that calls `vg_gf25519_r32_mul` and keeps public data in the working
space (a counter, the tables' address) or in `esi` across the calls is
related run by run with what the taint analysis knows public (`AR x τ`:
`τ`'s public data agree, each run's working space at `x`, and `esp` the
same). A block keeps it if the analysis from `τ` ends with at least what
`σ` says public (`block_ar`: the analysis is sound, and a block never
changes the permissions nor, if it never writes `esp`, `esp`; `edi` stays
the working space's base, as `τ` says). A call keeps it for a taint that
says public only what the call keeps (`CallSafe`: `esi`, `edi` and `esp`,
and bytes of the working space outside the slots and the function's own
working space, bytes 64 to 1023), by its correctness (`mulCall_ar`). A loop
keeps a relation its body keeps, if the condition agrees (`loop_inv`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519.X86.Field32 (RF mulCall_tr mulCall_ok)
open VG.Impl.X25519.X86.Field32 (mulCall opA)

/-- Two runs that agree on what `τ` says public, each with the working space
at `x`, and `esp` the same. -/
def AR (x : BitVec 32) (τ : VG.X86.Taint.T) (s t : State) : Prop :=
  VG.X86.Taint.Agree τ s t ∧ PointCTCtx x s ∧ PointCTCtx x t ∧ s.gpr .esp = t.gpr .esp

theorem AR.rf {x : BitVec 32} {τ : VG.X86.Taint.T} {s t : State} (h : AR x τ s t) : RF x s t :=
  ⟨h.2.1.ctx, h.2.2.1.ctx, h.2.2.2⟩

/-- A run's state after code that keeps `edi` the working space's base,
the permissions and `esp`. -/
theorem PointCTCtx.after {x : BitVec 32} {s t : State} (h : PointCTCtx x s) (hw : t.wr = s.wr)
    (hsp : t.gpr .esp = s.gpr .esp)
    (he : VG.X86.addr (t.gpr .edi) 0 = (VG.X86.Taint.region t 1).base) : PointCTCtx x t := by
  have hr : VG.X86.Taint.region t 1 = scR 8192 x := by
    rw [show VG.X86.Taint.region t 1 = VG.X86.Taint.region s 1 from congrArg (fun wr => wr.getD 1 ⟨0, 0⟩) hw]
    exact h.region
  have edi : t.gpr .edi = s.gpr .edi := by
    rw [hr] at he
    have e : (t.gpr .edi).setWidth 64 = x.setWidth 64 := by
      rw [← addr_zero]; exact he
    exact (BitVec.setWidth_32_64_inj.mp e).trans h.ctx.edi.symm
  exact h.keep edi hw hsp

/-- A block keeps `AR`, from `τ` to what `σ` says public, if the analysis
from `τ` ends with at least what `σ` says, and it never writes `esp`. -/
theorem block_ar (x : BitVec 32) {τ σ τ' : VG.X86.Taint.T} {is : List Instr} {h : VG.Taint.Hint VG.X86.Taint.T}
    (hc : taint.check τ (.block is) h = some τ') (hle : taint.le σ τ' = true)
    (hb : (.edi, 1, 0) ∈ σ.bases) (hsp : NoSp (.block is)) :
    RelCT isa (AR x τ) (.block is) (AR x σ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨ha, c₁, c₂, e⟩ e₁ e₂
  obtain ⟨ht, ha'⟩ := Taint.check_sound (A := taint) hc ha e₁ e₂
  have a : VG.X86.Taint.Agree σ s₁' s₂' := taint.le_sound hle ha'
  have p₁ := Exec.gpr hsp e₁
  have p₂ := Exec.gpr hsp e₂
  exact ⟨ht, a, c₁.after (Exec.rdwr e₁).2 p₁ (a.wf₁.bases _ hb), c₂.after (Exec.rdwr e₂).2 p₂ (a.wf₂.bases _ hb),
    by rw [p₁, p₂, e]⟩

/-- A block that ends with the flags public, before a loop's or a branch's condition. -/
theorem block_ar_cond (x : BitVec 32) {τ σ τ' : VG.X86.Taint.T} {is : List Instr}
    {h : VG.Taint.Hint VG.X86.Taint.T} (c : Cond)
    (hc : taint.check τ (.block is) h = some τ') (hle : taint.le σ τ' = true) (hf : τ'.flags = true)
    (hb : (.edi, 1, 0) ∈ σ.bases) (hsp : NoSp (.block is)) :
    RelCT isa (AR x τ) (.block is) fun s t => isa.eval c s = isa.eval c t ∧ AR x σ s t := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := block_ar x hc hle hb hsp _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨-, ha'⟩ := Taint.check_sound (A := taint) hc hp.1 e₁ e₂
  exact ⟨ht, taint.cond_sound ha' hf, hq⟩

/-- A loop keeps a relation that its body keeps, with the condition agreeing. -/
theorem loop_inv {I : State → State → Prop} {body : Prog isa} {c : Cond}
    (h : RelCT isa I body fun s t => isa.eval c s = isa.eval c t ∧ I s t) :
    RelCT isa I (.loop body c) I := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  generalize hc₁ : (Code.loop body c : Prog isa) = p at e₁
  induction e₁ generalizing s₂ t₂ s₂' with
  | loopExit b₁ c₁ =>
    cases hc₁
    cases e₂ with
    | loopExit b₂ c₂ =>
      obtain ⟨rfl, -, hq⟩ := h _ _ _ _ _ _ hp b₁ b₂
      exact ⟨rfl, hq⟩
    | loopNext b₂ c₂ _ =>
      obtain ⟨-, hc, -⟩ := h _ _ _ _ _ _ hp b₁ b₂
      rw [c₁, c₂] at hc; cases hc
  | loopNext b₁ c₁ r₁ _ ih =>
    cases hc₁
    cases e₂ with
    | loopExit b₂ c₂ =>
      obtain ⟨-, hc, -⟩ := h _ _ _ _ _ _ hp b₁ b₂
      rw [c₁, c₂] at hc; cases hc
    | loopNext b₂ c₂ r₂ =>
      obtain ⟨rfl, -, hi⟩ := h _ _ _ _ _ _ hp b₁ b₂
      obtain ⟨rfl, hq⟩ := ih _ _ _ hi r₂ rfl
      exact ⟨rfl, hq⟩
  | _ => cases hc₁

/-! ## Calls -/

/-- A taint whose public data a call of `vg_gf25519_r32_mul` keeps: `esi`,
`edi` and `esp`, the flags not, the working space (region 1, at most 8192
bytes) based at `edi`, and bytes of it outside bytes 64 to 1023. -/
def CallSafe (τ : VG.X86.Taint.T) : Bool :=
  !τ.flags && τ.regs.subset (.ofList [.esi, .edi, .esp]) &&
    τ.bases.all (· == (.edi, 1, 0)) && τ.wbases.isEmpty && τ.argLen == 0 && τ.argBases.isEmpty &&
    τ.stk.isEmpty && τ.room == 0 && τ.lens.getD 1 0 ≤ 8192 &&
    τ.slots.all fun sl => sl.1 == 1 && (sl.2.1 + sl.2.2 ≤ 64 || 1024 ≤ sl.2.1)

/-- What `CallSafe` says. -/
structure CallSafe.Props (τ : VG.X86.Taint.T) : Prop where
  flags : τ.flags = false
  regs : ∀ r ∈ τ.regs, r = .esi ∨ r = .edi ∨ r = .esp
  bases : ∀ p ∈ τ.bases, p = (.edi, 1, 0)
  wbases : τ.wbases = []
  argLen : τ.argLen = 0
  argBases : τ.argBases = []
  stk : τ.stk = []
  room : τ.room = 0
  lens : τ.lens.getD 1 0 ≤ 8192
  slots : ∀ sl ∈ τ.slots, sl.1 = 1 ∧ (sl.2.1 + sl.2.2 ≤ 64 ∨ 1024 ≤ sl.2.1)

theorem CallSafe.props {τ : VG.X86.Taint.T} (h : CallSafe τ = true) : CallSafe.Props τ := by
  simp only [CallSafe, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff,
    List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hr⟩, hb⟩, hw⟩, ha⟩, hab⟩, hs⟩, hro⟩, hl⟩, hsl⟩ := h
  refine ⟨hf, fun r hr' => ?_, hb, hw, ha, hab, hs, hro, hl, hsl⟩
  have := RegSet.mem_ofList.mp (RegSet.mem_of_subset hr hr')
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using this

/-- What `τ` says of a state on its own survives a call, which keeps `esi`,
`edi`, `esp` and the permissions. -/
theorem wf_after {τ : VG.X86.Taint.T} (hτ : CallSafe.Props τ) {s t : State} (w : VG.X86.Taint.Wf τ s)
    (k : Keep s t) : VG.X86.Taint.Wf τ t where
  lens hne := by rw [k.wr]; exact w.lens hne
  bases p hp := by
    have e := hτ.bases p hp
    rw [e]
    have hb := w.bases _ hp
    rw [e] at hb
    rw [k.edi, show VG.X86.Taint.region t 1 = VG.X86.Taint.region s 1 from
      congrArg (fun wr => wr.getD 1 ⟨0, 0⟩) k.wr]
    exact hb
  wbases p hp := by rw [hτ.wbases] at hp; cases hp
  args h := absurd h (by rw [hτ.argLen]; decide)
  argBases p hp := by rw [hτ.argBases] at hp; cases hp
  stk := by rw [k.esp]; exact w.stk
  frames p hp := by rw [hτ.stk] at hp; cases hp
  room h := absurd h (by rw [hτ.room]; decide)

/-- Agreement on what `τ` says survives a call in both runs, which keeps
`esi`, `edi`, `esp`, the permissions and the bytes of the working space
outside bytes 64 to 1023. -/
theorem agree_after {x : BitVec 32} {τ : VG.X86.Taint.T} (hτ : CallSafe.Props τ) {s₁ s₂ t₁ t₂ : State}
    (ha : VG.X86.Taint.Agree τ s₁ s₂) (c₁ : PointCTCtx x s₁) (c₂ : PointCTCtx x s₂)
    (k₁ : Keep s₁ t₁) (k₂ : Keep s₂ t₂)
    (m₁ : ∀ k, (k + 1 ≤ 64 ∨ 1024 ≤ k) → k < 8192 → t₁.mem (VG.X86.addr x k) = s₁.mem (VG.X86.addr x k))
    (m₂ : ∀ k, (k + 1 ≤ 64 ∨ 1024 ≤ k) → k < 8192 → t₂.mem (VG.X86.addr x k) = s₂.mem (VG.X86.addr x k)) :
    VG.X86.Taint.Agree τ t₁ t₂ := by
  have hx := c₁.ctx.fit
  have ba : ∀ (s t : State), PointCTCtx x s → t.wr = s.wr → ∀ k, k < 8192 →
      VG.X86.Taint.byteAddr t 1 k = VG.X86.addr x k := fun s t c hw k hk => by
    rw [VG.X86.Taint.byteAddr, show VG.X86.Taint.region t 1 = VG.X86.Taint.region s 1 from
      congrArg (fun wr => wr.getD 1 ⟨0, 0⟩) hw, c.region, addr_eq (by omega)]
  refine ⟨⟨fun r hr => ?_, fun hf => absurd hf (by rw [hτ.flags]; decide)⟩,
    fun h => k₁.wr.trans ((ha.wr h).trans k₂.wr.symm), wf_after hτ ha.wf₁ k₁, wf_after hτ ha.wf₂ k₂,
    ha.ok, fun sl hsl k hlo hhi => ?_, fun h => absurd h (by rw [hτ.argLen]; decide),
    fun k _ hk => absurd hk (by rw [hτ.argLen]; omega)⟩
  · rcases hτ.regs r hr with rfl | rfl | rfl
    · rw [k₁.esi, k₂.esi]; exact ha.rf.1 _ hr
    · rw [k₁.edi, k₂.edi]; exact ha.rf.1 _ hr
    · rw [k₁.esp, k₂.esp]; exact ha.rf.1 _ hr
  · obtain ⟨h1, hout⟩ := hτ.slots sl hsl
    have hk8 : k < 8192 := by
      have := ha.ok sl hsl
      rw [h1] at this
      have := hτ.lens
      omega
    have hk' : k + 1 ≤ 64 ∨ 1024 ≤ k := by omega
    have e := ha.slots sl hsl k hlo hhi
    rw [h1] at e ⊢
    rw [ba _ _ c₁ k₁.wr k hk8, ba _ _ c₂ k₂.wr k hk8, m₁ k hk' hk8, m₂ k hk' hk8]
    rwa [ba _ _ c₁ rfl k hk8, ba _ _ c₂ rfl k hk8] at e

/-- A call of `vg_gf25519_r32_mul` keeps `AR` for a taint `CallSafe` accepts. -/
theorem mulCall_ar (x : BitVec 32) {τ : VG.X86.Taint.T} (hτ : CallSafe τ = true) {o a b : Nat}
    (ho' : 64 ≤ o) (ho : o + 32 ≤ 768) (ha : a + 32 ≤ 768) (hb : b + 32 ≤ 768) :
    RelCT isa (AR x τ) (mulCall o a b) (AR x τ) := by
  have hp := CallSafe.props hτ
  refine (((mulCall_tr x ho ha hb).mono (fun _ _ h => AR.rf h) fun _ _ h => h).wpDep
    (F := fun (s t : State) => Keep s t ∧
      Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x opA 256, callStk s] s.mem t.mem)
    fun s₁ s₂ h => ⟨WP.mono (mulCall_ok h.2.1.ctx ho ha hb) fun _ h => ⟨h.1, h.2.1⟩,
      WP.mono (mulCall_ok h.2.2.1.ctx ho ha hb) fun _ h => ⟨h.1, h.2.1⟩⟩).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, ⟨ha', c₁, c₂, e⟩, ⟨k₁, f₁⟩, ⟨k₂, f₂⟩⟩
  have mem : ∀ {s t : State}, PointCTCtx x s →
      Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x opA 256, callStk s] s.mem t.mem →
      ∀ k, (k + 1 ≤ 64 ∨ 1024 ≤ k) → k < 8192 → t.mem (VG.X86.addr x k) = s.mem (VG.X86.addr x k) := by
    intro s t c f k hk hk8
    have hx := c.ctx.fit
    apply f
    intro r hr
    have hc : (VG.Proof.X25519.X86.sub x k 1).Contains (VG.X86.addr x k) 1 := Region.contains_self _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (sub_disj (by omega) (by omega) (by omega)) _ hc
    · exact (sub_disj (by omega) (by simp only [opA]; omega) (by simp only [opA]; omega)) _ hc
    · exact stk_apart c.ctx (d := k) (n := 1) (by omega) (by decide) _ hc
  exact ⟨agree_after hp ha' c₁ c₂ k₁ k₂ (mem c₁ f₁) (mem c₂ f₂), c₁.keep k₁.edi k₁.wr k₁.esp,
    c₂.keep k₂.edi k₂.wr k₂.esp, by rw [k₁.esp, k₂.esp, e]⟩

/-! ## Field programs -/

/-- The analysis of a block from `τ` keeps at least what `τ` says public, and
the block never writes `esp`. -/
def BlockOk (τ : VG.X86.Taint.T) (is : List Instr) : Bool :=
  ((taint.check τ (.block is) (.block [] 256)).map fun τ' => taint.le τ τ').getD false &&
    is.all fun i => !VG.X86.Taint.clobbers i .esp

theorem block_ar_ok (x : BitVec 32) {τ : VG.X86.Taint.T} {is : List Instr} (h : BlockOk τ is = true)
    (hb : (.edi, 1, 0) ∈ τ.bases) : RelCT isa (AR x τ) (.block is) (AR x τ) := by
  simp only [BlockOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases hc : taint.check τ (.block is) (.block [] 256) with
  | none => rw [hc] at h₁; cases h₁
  | some τ' =>
    rw [hc] at h₁
    exact block_ar x hc h₁ hb fun i hi => by simpa using h₂ i hi

/-- A field operation's block, if it is not a product, keeps `AR x τ`. -/
def FieldOpOk (τ : VG.X86.Taint.T) : FieldOp → Bool
  | .mul _ _ _ => true
  | op => BlockOk τ op.code

theorem fieldOp_ar (x : BitVec 32) {τ : VG.X86.Taint.T} (hτ : CallSafe τ = true) (hb : (.edi, 1, 0) ∈ τ.bases)
    (op : FieldOp) (h : FieldOpOk τ op = true) : RelCT isa (AR x τ) op.prog (AR x τ) := by
  cases op with
  | mul o a b =>
    exact mulCall_ar x hτ (by simp only [offset]; omega) (offset_bound o) (offset_bound a) (offset_bound b)
  | copy o a => exact block_ar_ok x h hb
  | const o v => exact block_ar_ok x h hb
  | add o a b => exact block_ar_ok x h hb
  | sub o a b => exact block_ar_ok x h hb

theorem fieldProg_ar (x : BitVec 32) {τ : VG.X86.Taint.T} (hτ : CallSafe τ = true) (hb : (.edi, 1, 0) ∈ τ.bases)
    (ops : List FieldOp) (h : ops.all (FieldOpOk τ) = true) :
    RelCT isa (AR x τ) (fieldProg ops) (AR x τ) := by
  induction ops with
  | nil => exact RelCT.nil fun _ _ h => h
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact RelCT.seq (fieldOp_ar x hτ hb op h.1) (ih h.2)

/-! ## Taints of the working space -/

/-- The registers `rs` and the words at the offsets `os` of the working space
public, the working space (region 1, 8192 bytes) at `edi`. -/
def ptR (rs : List Reg) (os : List Nat) : VG.X86.Taint.T :=
  { regs := .ofList rs, flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)],
    slots := os.map fun o => (1, o, 4) }

theorem ptR_base (rs : List Reg) (os : List Nat) : (.edi, 1, 0) ∈ (ptR rs os).bases :=
  List.mem_singleton_self _

theorem ptR_wf {x : BitVec 32} {s : State} (h : PointCTCtx x s) (rs : List Reg) (os : List Nat) :
    VG.X86.Taint.Wf (ptR rs os) s := by
  apply VG.X86.Taint.Wf.entry rfl rfl
  refine ⟨fun _ => ⟨h.lengths, h.separate, h.fits⟩, ?_, fun _ hh => (by cases hh),
    fun hh => (by cases hh), fun _ hh => (by cases hh)⟩
  intro p hp
  simp only [ptR, List.mem_singleton] at hp
  subst p
  rw [h.ctx.edi, addr_zero, h.region]

/-- Two runs agree on what `ptR rs os` says public. -/
theorem ptR_agree {x : BitVec 32} {s t : State} {rs : List Reg} {os : List Nat}
    (hs : PointCTCtx x s) (ht : PointCTCtx x t) (hw : s.wr = t.wr)
    (hr : ∀ r ∈ rs, s.gpr r = t.gpr r) (ho : ∀ o ∈ os, o + 4 ≤ 8192 ∧ wd s.mem x o = wd t.mem x o) :
    VG.X86.Taint.Agree (ptR rs os) s t := by
  refine ⟨⟨fun r h => hr r (RegSet.mem_ofList.mp h), fun h => (by cases h)⟩, fun _ => hw, ptR_wf hs rs os,
    ptR_wf ht rs os, ?_, ?_, fun h => (by cases h), fun n _ h => (Nat.not_lt_zero n h).elim⟩
  · intro sl hsl
    simp only [ptR, List.mem_map] at hsl
    obtain ⟨o, hmo, rfl⟩ := hsl
    exact (ho o hmo).1
  · intro sl hsl k hlo hhi
    simp only [ptR, List.mem_map] at hsl
    obtain ⟨o, hmo, rfl⟩ := hsl
    obtain ⟨hb, hv⟩ := ho o hmo
    change o ≤ k at hlo
    change k < o + 4 at hhi
    obtain ⟨j, hj, rfl⟩ : ∃ j < 4, k = o + j := ⟨k - o, by omega, by omega⟩
    simp only [VG.X86.Taint.byteAddr, hs.region, ht.region]
    have hx := hs.ctx.fit
    rw [← addr_eq (by omega : x.toNat + (o + j) < 2 ^ 32),
      addr_offset (x := x) (o := o) (d := j) (by omega),
      Mem.readW_byte s.mem _ hj, Mem.readW_byte t.mem _ hj]
    exact congrArg (BitVec.extractLsb' (8 * j) 8) hv

/-- `AR` with less public. -/
theorem AR.weaken {x : BitVec 32} {τ σ : VG.X86.Taint.T} (hle : taint.le σ τ = true) {s t : State}
    (h : AR x τ s t) : AR x σ s t :=
  ⟨taint.le_sound hle h.1, h.2⟩

/-- The analysis of a block from `τ` ends with at least what `σ` says public,
and the block never writes `esp`. -/
def BlockTo (τ : VG.X86.Taint.T) (is : List Instr) (σ : VG.X86.Taint.T) : Bool :=
  ((taint.check τ (.block is) (.block [] 256)).map fun τ' => taint.le σ τ').getD false &&
    is.all fun i => !VG.X86.Taint.clobbers i .esp

/-- `BlockTo`, with the flags public at the end. -/
def BlockCond (τ : VG.X86.Taint.T) (is : List Instr) (σ : VG.X86.Taint.T) : Bool :=
  ((taint.check τ (.block is) (.block [] 256)).map fun τ' => taint.le σ τ' && τ'.flags).getD false &&
    is.all fun i => !VG.X86.Taint.clobbers i .esp

theorem block_to (x : BitVec 32) {τ σ : VG.X86.Taint.T} {is : List Instr} (h : BlockTo τ is σ = true)
    (hb : (.edi, 1, 0) ∈ σ.bases) : RelCT isa (AR x τ) (.block is) (AR x σ) := by
  simp only [BlockTo, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases hc : taint.check τ (.block is) (.block [] 256) with
  | none => rw [hc] at h₁; cases h₁
  | some τ' =>
    rw [hc] at h₁
    exact block_ar x hc h₁ hb fun i hi => by simpa using h₂ i hi

theorem block_cond (x : BitVec 32) {τ σ : VG.X86.Taint.T} {is : List Instr} (c : Cond)
    (h : BlockCond τ is σ = true) (hb : (.edi, 1, 0) ∈ σ.bases) :
    RelCT isa (AR x τ) (.block is) fun s t => isa.eval c s = isa.eval c t ∧ AR x σ s t := by
  simp only [BlockCond, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases hc : taint.check τ (.block is) (.block [] 256) with
  | none => rw [hc] at h₁; cases h₁
  | some τ' =>
    rw [hc] at h₁
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true] at h₁
    exact block_ar_cond x c hc h₁.1 h₁.2 hb fun i hi => by simpa using h₂ i hi

end VG.Proof.Ed25519.X86
