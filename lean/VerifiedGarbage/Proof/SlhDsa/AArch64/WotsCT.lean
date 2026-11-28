module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsMain
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsMain
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block

/-!
# SLH-DSA on AArch64: `wotsLeaves4`, verified

As on x86-64 (`Proof/SlhDsa/X86_64/WotsCT.lean`): two runs of `wotsLeaves4`
from states of its precondition that agree on its public data (`scratch`,
`kp`, `sig` and `sp`; not `idx`, the seeds or the digits) leak the same
trace (`wots4_ct`). Each run's state satisfies, at every point of the code,
the invariants its correctness proof uses, at the same chain `i` and step
`j`, so two runs agree on the registers that address memory (`baseR`, and
`x21` in the chains); the blocks are constant time by the taint analysis
from those registers, for each of the three sizes; the calls of `thash4` by
its contract (`RelCT.call`), whose precondition `Base` gives in each run
(`tcall_rel`); and the loops' conditions agree since each run's counter is
the same. Then the code has no frames and no depth, a state satisfies the
precondition, `Verified`, and a call of it (`wots4call_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Wots4

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64
open VG.Spec.Sha3 (bytesAt)

/-! ## Two runs, each with its own invariants -/

theorem relSeq {A₁ A₂ B₁ B₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (hct : RelCT isa (fun a b => A₁ a ∧ A₂ b) c₁ fun _ _ => True)
    (h₁ : ∀ a, A₁ a → WP isa c₁ a B₁) (h₂ : ∀ b, A₂ b → WP isa c₁ b B₂)
    (hr : RelCT isa (fun a b => B₁ a ∧ B₂ b) c₂ Q) : RelCT isa (fun a b => A₁ a ∧ A₂ b) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.mono (RelCT.wp hct fun a b h => ⟨h₁ a h.1, h₂ b h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) hr

/-- Code the taint analysis proves constant time from the registers `rs`
and the stack pointer. -/
theorem taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint AArch64.Taint.T}
    (h : (taint.check (AArch64.Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (AArch64.Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h => (hr x y hp).2 r (AArch64.Taint.mem_ofRegs.mp h)⟩) h

theorem wp_skip {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨_, _, e, q⟩ := h
  cases e with
  | block h =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]; exact q

/-! ## The blocks, by the taint analysis -/

/-- The three layouts. -/
def Lays (L : Layout) : Prop := L = ⟨16, 35⟩ ∨ L = ⟨24, 51⟩ ∨ L = ⟨32, 67⟩

theorem lays_of {p : Params} (hz : Sz p) : Lays (L p) := by
  have hl := hz.len
  rcases hz.nv with e | e | e <;> simp [Lays, L, hl, e]

/-- The registers that hold `scratch`, `kp` and `sig`, which `Base` fixes. -/
abbrev baseR : List Reg := [.x19, .x20, .x24]

/-- And `i`, in the chains. -/
abbrev chainR : List Reg := [.x19, .x20, .x21, .x24]

section
variable {L : Layout} (hL : Lays L) {P : State → State → Prop}
include hL

theorem ct_start (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x0, .x1, .x3], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.pro ++ Wots.setup L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_prf (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ chainR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.prfLanes L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_argsA (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (thashArgs L Layout.oA Layout.strideA (2 * L.n + 32))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_argsB (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (thashArgs L Layout.oB Layout.strideB (L.n + 32 + L.len * L.n))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_hashType (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.hashType L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_step1 (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ chainR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.capture L ++ Wots.hashAdrs L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_end (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ chainR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.capture L ++ Wots.toB L ++
      ([.addImm .x .x21 .x21 1, .subImm .x .x9 .x21 L.len] : List Instr))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_leaf (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.leafPtr L ++ (List.range 4).flatMap fun k =>
      copyWords .x10 (Layout.oN + L.n * k) .x19 (Layout.laneB k + L.msgOff) (L.n / 8))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

end

theorem ct_step2 {P : State → State → Prop} (hr : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block [.addImm .x .x22 .x22 1, .subImm .x .x9 .x22 15]) fun _ _ => True :=
  taintR [] (fun x y h => ⟨hr x y h, fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide)

theorem ct_restore {P : State → State → Prop} (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (restoreRegs 0 Wots.saved)) fun _ _ => True :=
  taintR _ hr (by taint_decide)

/-! ## Two runs of the same `kp`, `scratch` and `sig` -/

section
variable {p : Params} {σ₁ σ₂ : State} {S sig : Addr} {kp idx₁ idx₂ : Nat}
  {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}

theorem base_eq {hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁} {hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂}
    (hsp : σ₁.sp = σ₂.sp) {a b : State} (ha : Base hE₁ a) (hb : Base hE₂ b) :
    a.sp = b.sp ∧ ∀ r ∈ baseR, a.gpr r = b.gpr r := by
  refine ⟨by rw [ha.sp, hb.sp, hsp], fun r hr => ?_⟩
  simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ha.x19, hb.x19]
  · rw [ha.x20, hb.x20]
  · rw [ha.x24, hb.x24]

theorem chain_eq {hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁} {hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂}
    (hsp : σ₁.sp = σ₂.sp) {a b : State} (ha : Base hE₁ a) (hb : Base hE₂ b) {i : Nat}
    (h₁ : a.gpr .x21 = BitVec.ofNat 64 i) (h₂ : b.gpr .x21 = BitVec.ofNat 64 i) :
    a.sp = b.sp ∧ ∀ r ∈ chainR, a.gpr r = b.gpr r := by
  refine ⟨by rw [ha.sp, hb.sp, hsp], fun r hr => ?_⟩
  simp only [chainR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.x19, hb.x19]
  · rw [ha.x20, hb.x20]
  · rw [h₁, h₂]
  · rw [ha.x24, hb.x24]

/-- `thash4`'s precondition, at the entry of its call after its arguments. -/
theorem args_pre {hE : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁} (hz : Sz p)
    {o st len : Nat} (hl : Lanes o st) (hlp : 0 < len) (hlm : len % 8 = 0)
    (hll : len ≤ st) {t u : State} (h : ArgsPost hE t u o st len) :
    (thash4Contract p.n).pre (u.callEntry.withRegions [] (t4wr S o st)) ∧
      Covers ([] ++ t4wr S o st) (u.rd ++ u.wr) ∧ Covers (t4wr S o st) u.wr := by
  have hn := hz.n32
  have hol : o + 4 * st ≤ 65536 := by rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  exact ⟨t4pre hE.scr_fit (by rcases hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide) hol h.x0 h.x1 h.x2 h.x3 h.x4
      hlp hlm hll (by rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega_using [hn]),
    t4cov (hE.scr_mem h.base.wr) hol⟩

/-- A call of `thash4` on the lanes at `o`, in two runs each with `Base`. -/
theorem tcall_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {o st len : Nat} (hl : Lanes o st) (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    (hct : ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ baseR, x.gpr r = y.gpr r) →
      RelCT isa P (.block (thashArgs (L p) o st len)) fun _ _ => True)
    {P : State → State → Prop} (hP : ∀ a b, P a b → Base hE₁ a ∧ Base hE₂ b) :
    RelCT isa P (thashCall (L p) name T.code o st len) fun _ _ => True := by
  refine RelCT.seq (RelCT.mono (RelCT.wp (F₁ := fun u => ∃ t, ArgsPost hE₁ t u o st len)
      (F₂ := fun u => ∃ t, ArgsPost hE₂ t u o st len)
      (hct fun a b h => base_eq hsp (hP a b h).1 (hP a b h).2) fun a b h =>
        ⟨WP.mono (targs_ok hE₁ hz hl hll (hP a b h).1) fun u h' => ⟨a, h'⟩,
          WP.mono (targs_ok hE₂ hz hl hll (hP a b h).2) fun u h' => ⟨b, h'⟩⟩) (fun _ _ h => h)
      fun _ _ h => h.2) ?_
  refine RelCT.call T.verified.1 T.verified.2.1 [] (t4wr S o st) fun a b ⟨⟨_, u₁⟩, ⟨_, u₂⟩⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := args_pre hz hl hlp hlm hll u₁
  obtain ⟨p₂, c₂, w₂⟩ := args_pre (hE := hE₂) hz hl hlp hlm hll u₂
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x0, u₂.x0]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x1, u₂.x1]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x2, u₂.x2]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x3, u₂.x3]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.x4, u₂.x4]
  · simp only [State.withRegions_sp, State.callEntry_sp]; rw [u₁.base.sp, u₂.base.sp, hsp]

/-! ## The steps -/

theorem tcallA_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {P : State → State → Prop} (hP : ∀ a b, P a b → Base hE₁ a ∧ Base hE₂ b) :
    RelCT isa P (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32)) fun _ _ => True := by
  have hn := hz.n32
  exact tcall_rel hE₁ hE₂ hsp hz T name (o := 3136) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) (fun hr => ct_argsA (lays_of hz) hr) hP

/-- A call of `thash4` on `A`, from `Base` to `Base`. -/
theorem tcallA_base (hE : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {t : State} (hb : Base hE t) :
    WP isa (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32)) t (Base hE) := by
  have hn := hz.n32
  exact tcall_ok hE hz T name (o := 3136) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb fun _ hb' _ _ _ _ => hb'

theorem step_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {i j : Nat} (hi : i < p.len) (hj : j < 15) :
    RelCT isa (fun a b => (∃ m, StepInv hE₁ m i j a) ∧ ∃ m, StepInv hE₂ m i j b)
      (Wots.stepBody (L p) name T.code) fun _ _ => True :=
  relSeq (B₁ := Base hE₁) (B₂ := Base hE₂)
    (ct_step1 (lays_of hz) fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => chain_eq hsp h₁.base h₂.base h₁.x21 h₂.x21)
    (fun _ ⟨_, h⟩ => WP.mono (stepPre_ok hE₁ hz hi hj h) fun _ ⟨_, _, hb, _⟩ => hb.1)
    (fun _ ⟨_, h⟩ => WP.mono (stepPre_ok hE₂ hz hi hj h) fun _ ⟨_, _, hb, _⟩ => hb.1)
    (relSeq (B₁ := Base hE₁) (B₂ := Base hE₂) (tcallA_rel hE₁ hE₂ hsp hz T name fun _ _ h => h)
      (fun _ h => tcallA_base hE₁ hz T name h) (fun _ h => tcallA_base hE₂ hz T name h)
      (ct_step2 fun x y ⟨hx, hy⟩ => by rw [hx.sp, hy.sp, hsp]))

/-- The 15 steps of chain `i`. -/
theorem steps_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {i : Nat} (hi : i < p.len) :
    RelCT isa (fun a b => (∃ m, StepInv hE₁ m i 0 a) ∧ ∃ m, StepInv hE₂ m i 0 b)
      (.loop (Wots.stepBody (L p) name T.code) (.nonzero .x .x9))
      (fun a b => (∃ m, StepInv hE₁ m i 15 a) ∧ ∃ m, StepInv hE₂ m i 15 b) := by
  refine RelCT.mono (RelCT.loop (fun n a b => 1 ≤ n ∧ n ≤ 15 ∧ (∃ m, StepInv hE₁ m i (15 - n) a) ∧
      ∃ m, StepInv hE₂ m i (15 - n) b) (fun n => ?_) 15) (fun _ _ h => ⟨by decide, by decide, h⟩) fun _ _ h => h
  by_cases h₁ : 1 ≤ n
  swap
  · exact RelCT.of_false fun _ _ h => h₁ h.1
  by_cases h₂ : n ≤ 15
  swap
  · exact RelCT.of_false fun _ _ h => h₂ h.2.1
  let X := fun (u : State) => u.gpr .x9 = BitVec.ofNat 64 (15 - n + 1) - BitVec.ofNat 64 15
  refine RelCT.mono (RelCT.wp (F₁ := fun (u : State) => (∃ m, StepInv hE₁ m i (15 - n + 1) u) ∧ X u)
      (F₂ := fun (u : State) => (∃ m, StepInv hE₂ m i (15 - n + 1) u) ∧ X u)
      (step_rel hE₁ hE₂ hsp hz T name (j := 15 - n) hi (by omega_using [h₁]))
      fun a b ⟨⟨m, ha⟩, ⟨m', hb⟩⟩ =>
        ⟨WP.mono (step_ok hE₁ hz T name hi (by omega_using [h₁]) ha) fun u ⟨hu, hz'⟩ => ⟨⟨m, hu⟩, hz'⟩,
          WP.mono (step_ok hE₂ hz T name hi (by omega_using [h₁]) hb) fun u ⟨hu, hz'⟩ => ⟨⟨m', hu⟩, hz'⟩⟩)
    (fun _ _ ⟨_, _, h⟩ => h) fun a b ⟨_, ⟨ha, za⟩, ⟨hb, zb⟩⟩ => ?_
  have ea := eval_nz za (by omega_using [h₂]) (by decide)
  have eb := eval_nz zb (by omega_using [h₂]) (by decide)
  refine ⟨by rw [ea, eb], fun hf => ?_, fun ht => ?_⟩
  · by_cases e : 15 - n + 1 = 15
    · rw [e] at ha hb; exact ⟨ha, hb⟩
    · rw [ea, decide_eq_false e] at hf; cases hf
  · by_cases e : 15 - n + 1 = 15
    · rw [ea, decide_eq_true e] at ht; cases ht
    · rw [show 15 - n + 1 = 15 - (n - 1) by omega_using [h₁, h₂, e]] at ha hb
      exact ⟨n - 1, by omega_using [h₁], by omega_using [h₁, h₂, e], by omega_using [h₂], ha, hb⟩

/-! ## The chains -/

/-- The rest of the head of chain `i`, after the private key values'
addresses: `PRF`, the type `WOTS_HASH`. -/
abbrev headRest (p : Params) (name : String) (T : Thash4Impl p.n) : Prog isa :=
  .seq (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32))
    (.seq (.block (Wots.hashType (L p))) (.block []))

/-- After the private key values' addresses. -/
def H1 (hE : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (name : String) (T : Thash4Impl p.n) (i : Nat)
    (t : State) : Prop :=
  Base hE t ∧ t.gpr .x21 = BitVec.ofNat 64 i ∧ ∃ m, WP isa (headRest p name T) t (StepInv hE m i 0)

/-- After `PRF`. -/
def H2 (hE : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (i : Nat) (t : State) : Prop :=
  Base hE t ∧ t.gpr .x21 = BitVec.ofNat 64 i ∧
    ∃ m, WP isa (.seq (.block (Wots.hashType (L p))) (.block [])) t (StepInv hE m i 0)

theorem h1_ok (hE : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {i : Nat} (hi : i < p.len) {t : State} (h : ChainInv hE i t) :
    WP isa (.block (Wots.prfLanes (L p))) t (H1 hE name T i) := by
  have W := chainHead_ok hE hz T name hi h.base h.vk h.x21 (fun k hk => (h.lanes k hk).a20)
    (X := .block []) (Q := StepInv hE t.mem i 0) fun u hu => WP.block_nil hu
  exact WP.mono (WP.and (prfs_ok hE hz hi h.base h.x21 fun k hk => (h.lanes k hk).a20) (WP.seq_iff.mp W))
    fun u ⟨⟨⟨hb, hg, _⟩, _⟩, hw⟩ => ⟨hb, by rw [hg _ (by decide), h.x21], t.mem, hw⟩

theorem h2_ok (hE : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {i : Nat} {t : State} (h : H1 hE name T i t) :
    WP isa (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32)) t (H2 hE i) := by
  have hn := hz.n32
  obtain ⟨hb, hr, m, hw⟩ := h
  exact WP.mono (WP.and (tcall_ok hE hz T name (o := 3136) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
      (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb
      (Q := fun t' => Base hE t' ∧ t'.gpr .x21 = t.gpr .x21) fun t' hb' hcs _ _ _ =>
        ⟨hb', hcs _ (by decide) (by decide)⟩) (WP.seq_iff.mp hw))
    fun u ⟨⟨hb', hcs⟩, hw'⟩ => ⟨hb', by rw [hcs, hr], m, hw'⟩

/-- Chain `i` of the four lanes. -/
theorem chain_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {i : Nat} (hi : i < p.len) :
    RelCT isa (fun a b => ChainInv hE₁ i a ∧ ChainInv hE₂ i b) (Wots.chainBody (L p) name T.code)
      fun _ _ => True :=
  relSeq (B₁ := H1 hE₁ name T i) (B₂ := H1 hE₂ name T i)
    (ct_prf (lays_of hz) fun _ _ h => chain_eq hsp h.1.base h.2.base h.1.x21 h.2.x21)
    (fun _ h => h1_ok hE₁ hz T name hi h) (fun _ h => h1_ok hE₂ hz T name hi h)
  (relSeq (B₁ := H2 hE₁ i) (B₂ := H2 hE₂ i) (tcallA_rel hE₁ hE₂ hsp hz T name fun _ _ h => ⟨h.1.1, h.2.1⟩)
    (fun _ h => h2_ok hE₁ hz T name h) (fun _ h => h2_ok hE₂ hz T name h)
  (relSeq (B₁ := fun t => ∃ m, StepInv hE₁ m i 0 t) (B₂ := fun t => ∃ m, StepInv hE₂ m i 0 t)
    (ct_hashType (lays_of hz) fun _ _ h => base_eq hsp h.1.1 h.2.1)
    (fun _ ⟨_, _, m, hw⟩ => WP.mono (WP.seq_iff.mp hw) fun _ hv => ⟨m, wp_skip hv⟩)
    (fun _ ⟨_, _, m, hw⟩ => WP.mono (WP.seq_iff.mp hw) fun _ hv => ⟨m, wp_skip hv⟩)
  (RelCT.seq (steps_rel hE₁ hE₂ hsp hz T name hi)
    (ct_end (lays_of hz) fun _ _ ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ => chain_eq hsp ha.base hb.base ha.x21 hb.x21))))

/-- The `len` chains. -/
theorem chains_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    RelCT isa (fun a b => ChainInv hE₁ 0 a ∧ ChainInv hE₂ 0 b) (.loop (Wots.chainBody (L p) name T.code) (.nonzero .x .x9))
      (fun a b => ChainInv hE₁ p.len a ∧ ChainInv hE₂ p.len b) := by
  have hl : 1 ≤ p.len := by have := hz.len; omega_using [this]
  have hl64 : p.len < 2 ^ 63 := by have h1 := hz.len; have h2 := hz.n32; omega_using [h1, h2]
  refine RelCT.mono (RelCT.loop (fun n a b => 1 ≤ n ∧ n ≤ p.len ∧ ChainInv hE₁ (p.len - n) a ∧
      ChainInv hE₂ (p.len - n) b) (fun n => ?_) p.len)
    (fun _ _ h => ⟨hl, Nat.le_refl _, by rw [Nat.sub_self]; exact h.1, by rw [Nat.sub_self]; exact h.2⟩) fun _ _ h => h
  by_cases h₁ : 1 ≤ n
  swap
  · exact RelCT.of_false fun _ _ h => h₁ h.1
  by_cases h₂ : n ≤ p.len
  swap
  · exact RelCT.of_false fun _ _ h => h₂ h.2.1
  have hi : p.len - n < p.len := by omega_using [h₁, h₂]
  let X := fun (u : State) => u.gpr .x9 = BitVec.ofNat 64 (p.len - n + 1) - BitVec.ofNat 64 p.len
  refine RelCT.mono (RelCT.wp (F₁ := fun (u : State) => ChainInv hE₁ (p.len - n + 1) u ∧ X u)
      (F₂ := fun (u : State) => ChainInv hE₂ (p.len - n + 1) u ∧ X u)
      (chain_rel hE₁ hE₂ hsp hz T name hi)
      fun a b ⟨ha, hb⟩ => ⟨chainBody_ok hE₁ hz T name hi ha, chainBody_ok hE₂ hz T name hi hb⟩)
    (fun _ _ ⟨_, _, h⟩ => h) fun a b ⟨_, ⟨ha, za⟩, ⟨hb, zb⟩⟩ => ?_
  have ea := eval_nz za (by omega_using [h₂, hl64]) (by omega_using [hl64])
  have eb := eval_nz zb (by omega_using [h₂, hl64]) (by omega_using [hl64])
  refine ⟨by rw [ea, eb], fun hf => ?_, fun ht => ?_⟩
  · by_cases e : p.len - n + 1 = p.len
    · rw [e] at ha hb; exact ⟨ha, hb⟩
    · rw [ea, decide_eq_false e] at hf; cases hf
  · by_cases e : p.len - n + 1 = p.len
    · rw [ea, decide_eq_true e] at ht; cases ht
    · rw [show p.len - n + 1 = p.len - (n - 1) by omega_using [h₁, h₂, e]] at ha hb
      exact ⟨n - 1, by omega_using [h₁], by omega_using [h₁, h₂, e], by omega_using [h₂], ha, hb⟩

/-! ## The public keys, and the whole function -/

theorem leaves_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    RelCT isa (fun a b => ChainInv hE₁ p.len a ∧ ChainInv hE₂ p.len b) (Wots.leaves (L p) name T.code)
      fun _ _ => True := by
  have hl := hz.len
  have hlm : (p.n + 32 + p.len * p.n) % 8 = 0 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e]
  have hll : p.n + 32 + p.len * p.n ≤ 2208 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have hc : ∀ {σ : State} {idx : Nat} {pk a sk : List Byte} (E : Entry p σ S sig kp idx pk a sk) {t : State},
      ChainInv E p.len t →
      WP isa (thashCall (L p) name T.code Layout.oB Layout.strideB ((L p).n + 32 + (L p).len * (L p).n)) t (Base E) := by
    intro _ _ _ _ _ E _ h
    exact tcall_ok E hz T name (o := 3648) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
      (by omega_using []) hlm hll h.base fun _ hb _ _ _ _ => hb
  exact relSeq (B₁ := Base hE₁) (B₂ := Base hE₂)
    (tcall_rel hE₁ hE₂ hsp hz T name (o := 3648) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
      (by omega_using []) hlm hll (fun hr => ct_argsB (lays_of hz) hr) fun _ _ h => ⟨h.1.base, h.2.base⟩)
    (fun _ h => hc hE₁ h) (fun _ h => hc hE₂ h)
    (ct_leaf (lays_of hz) fun _ _ h => base_eq hsp h.1 h.2)

theorem wots_rel (hE₁ : Entry p σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.sp = σ₂.sp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (Wots.wotsLeaves4 (L p) name T.code) fun _ _ => True :=
  relSeq (B₁ := ChainInv hE₁ 0) (B₂ := ChainInv hE₂ 0)
    (ct_start (lays_of hz) fun _ _ ⟨e₁, e₂⟩ => by
      rw [e₁, e₂]
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hE₁.x0, hE₂.x0]
      · rw [hE₁.x1, hE₂.x1]
      · rw [hE₁.x3, hE₂.x3])
    (fun _ e => by rw [e]; exact start_ok hE₁ hz) (fun _ e => by rw [e]; exact start_ok hE₂ hz)
  (RelCT.seq (chains_rel hE₁ hE₂ hsp hz T name)
  (relSeq (B₁ := Base hE₁) (B₂ := Base hE₂) (leaves_rel hE₁ hE₂ hsp hz T name)
    (fun _ h => WP.mono (leaves_ok hE₁ hz T name h) fun _ h' => h'.1)
    (fun _ h => WP.mono (leaves_ok hE₂ hz T name h) fun _ h' => h'.1)
    (ct_restore fun _ _ h => base_eq hsp h.1 h.2)))

end

/-- The entry facts of a state of the precondition, with its `scratch`,
`sig` and `kp` given. -/
theorem entry_of {p : Params} {s : State} (h : (wots4Contract p).pre s) {S sig : Addr} {kp : Nat}
    (hS : s.gpr .x0 = S) (hsig : s.gpr .x3 = sig) (hkp : (s.gpr .x1).toNat = kp) :
    ∃ pkSeed a16, Entry p s S sig kp (s.gpr .x2).toNat pkSeed a16 (bytesAt s.mem (at' S Layout.oSkSeed) p.n) := by
  subst hS hsig hkp
  obtain ⟨hreg, ⟨pkSeed, a16, henv⟩, hkp4, hkpN, hidx, hdig⟩ := h
  exact ⟨pkSeed, a16, rfl, by simp, by simp, rfl, hreg, henv, rfl, hkp4, hkpN, hidx, hdig⟩

/-- `wotsLeaves4` is constant time. -/
theorem wots4_ct {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    ConstantTime isa (wots4Contract p).pre (wots4Contract p).pub (Wots.wotsLeaves4 (L p) name T.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨_, _, hE₁⟩ := entry_of h₁ rfl rfl rfl
  obtain ⟨_, _, hE₂⟩ := entry_of h₂ hp.1.symm hp.2.2.1.symm (congrArg BitVec.toNat hp.2.1.symm)
  exact (wots_rel hE₁ hE₂ hp.2.2.2 hz T name _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Frames, depth, and calls of `wotsLeaves4` -/

/-- `wotsLeaves4` has no frames (and so never writes `sp`). -/
theorem wots4_noFrames (L : Layout) (name : String) {t4 : Prog isa} (h : t4.noFrames = true) :
    (Wots.wotsLeaves4 L name t4).noFrames = true := by
  simp [Wots.wotsLeaves4, Wots.chainBody, Wots.stepBody, Wots.leaves, thashCall, Code.noFrames, h]

theorem wots4_depth (L : Layout) (name : String) {t4 : Prog isa} (h : t4.aarch64Depth = 0) :
    (Wots.wotsLeaves4 L name t4).aarch64Depth = 0 := by
  simp [Wots.wotsLeaves4, Wots.chainBody, Wots.stepBody, Wots.leaves, thashCall, Code.aarch64Depth, h]

/-- A call of `wotsLeaves4`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem wots4call_ok {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name wn : String) {s : State}
    {rd wr : List Region} (hpre : (wots4Contract p).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (wots4Contract p).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call wn (Wots.wotsLeaves4 ⟨p.n, p.len⟩ name T.code)) s Q :=
  WP.callV (wots4_correct hz T name) hpre hc hw (fun s' h₁ h₂ h₃ h₄ h₅ _ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₇ h₈)
    (wots4_noFrames _ name T.noFrames)

/-! ## A state satisfying the precondition -/

/-- `scratch` and `sig` in the witness. -/
abbrev satS : Addr := BitVec.ofNat 64 0x100000
abbrev satSig : Addr := BitVec.ofNat 64 0x10000

/-- The witness: zeros everywhere; `kp` and `idx` 0. -/
def wsat (p : Params) : State where
  gpr r := match r with
    | .x0 => satS | .x3 => satSig | _ => 0
  sp := BitVec.ofNat 64 0x200000
  mem := fun _ => 0
  rd := []
  wr := [⟨satS, scratchLen⟩, ⟨satSig, p.len * p.n⟩]

theorem bytesAt_zero (a : Addr) (l : Nat) : bytesAt (fun _ => 0) a l = List.replicate l 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp [bytesAt], fun b hb => ?_⟩
  simp only [bytesAt, List.mem_map, List.mem_range] at hb
  obtain ⟨i, _, rfl⟩ := hb
  rfl

theorem wsat_pre {p : Params} (hz : Sz p) : (wots4Contract p).pre (wsat p) := by
  have hn := hz.n32
  have hl := hz.len
  have hln : p.len * p.n ≤ 2144 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have hS : satS.toNat = 0x100000 := rfl
  have hG : satSig.toNat = 0x10000 := rfl
  refine ⟨⟨rfl, rfl, by show satS.toNat + scratchLen ≤ _; rw [hS]; decide,
    by show satSig.toNat + p.len * p.n ≤ _; rw [hG]; omega_using [hln],
    Offset.disjoint_of_le (by show satSig.toNat + p.len * p.n ≤ satS.toNat; rw [hG, hS]; omega_using [hln])
      (by show satS.toNat + Layout.oSigTmp ≤ _; rw [hS]; decide),
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0,
      fun k _ => bytesAt_zero _ _, fun k _ => bytesAt_zero _ _, fun k _ => bytesAt_zero _ _,
      fun k _ => bytesAt_zero _ _⟩,
    rfl, by show (0 + 4) * p.n ≤ 32 * Layout.nodeSlots; rw [nodeSlots_eq]; omega_using [hn],
    by show (0 : BitVec 64).toNat < 2 ^ 32; decide, fun i _ => by show (0 : BitVec 8).toNat < 16; decide⟩

/-! ## `Verified` -/

/-- `wotsLeaves4` meets `wots4Contract`, for every implementation of `thash4`. -/
theorem wots4_verified {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    Verified AArch64.target (Wots.wotsLeaves4 ⟨p.n, p.len⟩ name T.code) (wots4Contract p) :=
  ⟨wots4_correct hz T name, wots4_ct hz T name, ⟨wsat p, wsat_pre hz⟩⟩

end VG.Proof.SlhDsa.AArch64.Wots4
