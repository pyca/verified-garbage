module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsMain
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Avx
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsMain
public meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Avx
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# SLH-DSA on x86-64: `wotsLeaves4`, verified

Two runs of `wotsLeaves4` from states of its precondition that agree on its
public data (`scratch`, `kp`, `sig` and `rsp`; not `idx`, the seeds or the
digits) leak the same trace (`wots4_ct`). Each run's state satisfies, at
every point of the code, the invariants its correctness proof uses, at the
same chain `i` and step `j` (the loops' counters depend on nothing secret),
so two runs agree on the registers that address memory (`baseR`, and `r13`
in the chains); the blocks are constant time by the taint analysis from
those registers, for each of the three sizes; the calls of `thash4` by its
contract (`RelCT.call`), whose precondition `Base` gives in each run
(`tcall_rel`); and the loops' conditions agree since each run's counter is
the same.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Wots4

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64
open VG.Spec.Sha3 (bytesAt)

/-! ## Two runs, each with its own invariants -/

/-- `c₁` then `c₂`, from states each satisfying a predicate of its own: `c₁`
leaks the same in both runs, and takes each to a state of its own
predicate. -/
theorem relSeq {A₁ A₂ B₁ B₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (hct : RelCT isa (fun a b => A₁ a ∧ A₂ b) c₁ fun _ _ => True)
    (h₁ : ∀ a, A₁ a → WP isa c₁ a B₁) (h₂ : ∀ b, A₂ b → WP isa c₁ b B₂)
    (hr : RelCT isa (fun a b => B₁ a ∧ B₂ b) c₂ Q) : RelCT isa (fun a b => A₁ a ∧ A₂ b) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.mono (RelCT.wp hct fun a b h => ⟨h₁ a h.1, h₂ b h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) hr

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun x y hp => Taint.agree_ofRegs (hr x y hp)) h

theorem wp_skip {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨_, _, e, q⟩ := h
  cases e with
  | block h =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]; exact q

/-! ## The blocks, by the taint analysis -/

/-- The three layouts. -/
def Lays (L : Layout) : Prop := L = ⟨16, 35⟩ ∨ L = ⟨24, 51⟩ ∨ L = ⟨32, 67⟩

theorem Sz.lays {p : Params} (hz : Sz p) : Lays (L p) := by
  have hl := hz.len
  rcases hz.nv with e | e | e <;> simp [Lays, L, hl, e]

/-- The registers that hold `scratch`, `kp`, `sig` and `rsp`, which `Base`
fixes. -/
abbrev baseR : List Reg := [.rbx, .r12, .r15, .rsp]

/-- And `i`, in the chains. -/
abbrev chainR : List Reg := [.rbx, .r12, .r13, .r15, .rsp]

section
variable {L : Layout} (hL : Lays L) {P : State → State → Prop}
include hL

theorem ct_start (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rdi, .rsi, .rcx, .rsp], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.pro ++ Wots.setup L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_prf (hr : ∀ x y, P x y → ∀ r ∈ chainR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.prfLanes L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_argsA (hr : ∀ x y, P x y → ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (thashArgs L Layout.oA Layout.strideA (2 * L.n + 32))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_argsB (hr : ∀ x y, P x y → ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (thashArgs L Layout.oB Layout.strideB (L.n + 32 + L.len * L.n))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_hashType (hr : ∀ x y, P x y → ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.hashType L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_step1 (hr : ∀ x y, P x y → ∀ r ∈ chainR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.capture L ++ Wots.hashAdrs L)) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_end (hr : ∀ x y, P x y → ∀ r ∈ chainR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.capture L ++ Wots.toB L ++
      ([.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 L.len))] : List Instr))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_leaf (hr : ∀ x y, P x y → ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (Wots.leafPtr L ++ (List.range 4).flatMap fun k =>
      copyWords .rdx (L.n * k) .rbx (Layout.laneB k + L.msgOff) (L.n / 8))) fun _ _ => True := by
  rcases hL with rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

end

theorem ct_step2 {P : State → State → Prop} :
    RelCT isa P (.block [.alu .add .rbp (.imm 1), .alu .cmp .rbp (.imm 15)]) fun _ _ => True :=
  taintR [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

theorem ct_restore {P : State → State → Prop} (hr : ∀ x y, P x y → ∀ r ∈ baseR, x.gpr r = y.gpr r) :
    RelCT isa P (.block (restoreRegs 0)) fun _ _ => True :=
  taintR _ hr (by taint_decide)

/-! ## Two runs of the same `kp`, `scratch` and `sig` -/

section
variable {p : Params} {stk : Nat} {σ₁ σ₂ : State} {S sig : Addr} {kp idx₁ idx₂ : Nat}
  {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}

theorem base_eq {hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁} {hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) {a b : State} (ha : Base hE₁ a) (hb : Base hE₂ b) :
    ∀ r ∈ baseR, a.gpr r = b.gpr r := by
  intro r hr
  simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.rbx, hb.rbx]
  · rw [ha.r12, hb.r12]
  · rw [ha.r15, hb.r15]
  · rw [ha.rsp, hb.rsp, hsp]

theorem chain_eq {hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁} {hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) {a b : State} (ha : Base hE₁ a) (hb : Base hE₂ b) {i : Nat}
    (h₁ : a.gpr .r13 = BitVec.ofNat 64 i) (h₂ : b.gpr .r13 = BitVec.ofNat 64 i) :
    ∀ r ∈ chainR, a.gpr r = b.gpr r := by
  intro r hr
  simp only [chainR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [ha.rbx, hb.rbx]
  · rw [ha.r12, hb.r12]
  · rw [h₁, h₂]
  · rw [ha.r15, hb.r15]
  · rw [ha.rsp, hb.rsp, hsp]

/-- `thash4`'s precondition, at the entry of its call after its arguments. -/
theorem args_pre {hE : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁} (hz : Sz p) (T : Thash4Impl p.n)
    (hs : stk = 8 + T.stack) {o st len : Nat} (hl : Lanes o st) (hlp : 0 < len) (hlm : len % 8 = 0)
    (hll : len ≤ st) {t u : State} (h : ArgsPost hE t u o st len) :
    (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] (t4wr S o st)) ∧
      Covers ([] ++ t4wr S o st) (u.rd ++ u.wr) ∧ Covers (t4wr S o st) u.wr := by
  have hn := hz.n32
  have hol : o + 4 * st ≤ 65536 := by rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  exact ⟨t4pre T hE.scr_fit (by rcases hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide) hol h.rdi h.rsi h.rdx h.rcx h.r8
      (by rw [h.base.rsp]; have := hE.reg.stk_scr; rw [hs] at this; exact this) (h.base.env hz).rc hlp hlm hll
      (by rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega_using [hn]),
    t4cov (by rw [h.base.wr, hE.reg.wr_eq]; exact List.mem_cons_self ..) hol⟩

/-- A call of `thash4` on the lanes at `o`, in two runs each with `Base`. -/
theorem tcall_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack)
    {o st len : Nat} (hl : Lanes o st) (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    (hct : ∀ {P : State → State → Prop}, (∀ x y, P x y → ∀ r ∈ baseR, x.gpr r = y.gpr r) →
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
  obtain ⟨p₁, c₁, w₁⟩ := args_pre hz T hs hl hlp hlm hll u₁
  obtain ⟨p₂, c₂, w₂⟩ := args_pre (hE := hE₂) hz T hs hl hlp hlm hll u₂
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, by rw [u₁.base.rsp, u₂.base.rsp, hsp]⟩
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.rdi, u₂.rdi]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.rsi, u₂.rsi]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.rdx, u₂.rdx]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.rcx, u₂.rcx]
  · rw [ce_gpr _ _ (by decide), ce_gpr _ _ (by decide), u₁.r8, u₂.r8]
  · rw [ce_rsp, ce_rsp, u₁.base.rsp, u₂.base.rsp, hsp]

/-! ## The steps -/

theorem tcallA_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack)
    {P : State → State → Prop} (hP : ∀ a b, P a b → Base hE₁ a ∧ Base hE₂ b) :
    RelCT isa P (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32)) fun _ _ => True := by
  have hn := hz.n32
  exact tcall_rel hE₁ hE₂ hsp hz T name hs (o := 3296) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) (fun hr => ct_argsA hz.lays hr) hP

theorem step_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack)
    {i j : Nat} (hi : i < p.len) (hj : j < 15) :
    RelCT isa (fun a b => (∃ m, StepInv hE₁ m i j a) ∧ ∃ m, StepInv hE₂ m i j b)
      (Wots.stepBody (L p) name T.code) fun _ _ => True :=
  relSeq (B₁ := Base hE₁) (B₂ := Base hE₂)
    (ct_step1 hz.lays fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => chain_eq hsp h₁.base h₂.base h₁.r13 h₂.r13)
    (fun _ ⟨_, h⟩ => WP.mono (stepPre_ok hE₁ hz hi hj h) fun _ ⟨_, _, hb, _⟩ => hb.1)
    (fun _ ⟨_, h⟩ => WP.mono (stepPre_ok hE₂ hz hi hj h) fun _ ⟨_, _, hb, _⟩ => hb.1)
    (RelCT.seq (tcallA_rel hE₁ hE₂ hsp hz T name hs fun _ _ h => h) ct_step2)

/-- The 15 steps of chain `i`. -/
theorem steps_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack)
    {i : Nat} (hi : i < p.len) :
    RelCT isa (fun a b => (∃ m, StepInv hE₁ m i 0 a) ∧ ∃ m, StepInv hE₂ m i 0 b)
      (.loop (Wots.stepBody (L p) name T.code) .ne)
      (fun a b => (∃ m, StepInv hE₁ m i 15 a) ∧ ∃ m, StepInv hE₂ m i 15 b) := by
  refine RelCT.mono (RelCT.loop (fun n a b => 1 ≤ n ∧ n ≤ 15 ∧ (∃ m, StepInv hE₁ m i (15 - n) a) ∧
      ∃ m, StepInv hE₂ m i (15 - n) b) (fun n => ?_) 15) (fun _ _ h => ⟨by decide, by decide, h⟩) fun _ _ h => h
  by_cases h₁ : 1 ≤ n
  swap
  · exact RelCT.of_false fun _ _ h => h₁ h.1
  by_cases h₂ : n ≤ 15
  swap
  · exact RelCT.of_false fun _ _ h => h₂ h.2.1
  refine RelCT.mono (RelCT.wp (F₁ := fun (u : State) => (∃ m, StepInv hE₁ m i (15 - n + 1) u) ∧ u.zf = some (decide (15 - n + 1 = 15)))
      (F₂ := fun (u : State) => (∃ m, StepInv hE₂ m i (15 - n + 1) u) ∧ u.zf = some (decide (15 - n + 1 = 15)))
      (step_rel hE₁ hE₂ hsp hz T name hs (j := 15 - n) hi (by omega_using [h₁]))
      fun a b ⟨⟨m, ha⟩, ⟨m', hb⟩⟩ =>
        ⟨WP.mono (step_ok hE₁ hz T name hs hi (by omega_using [h₁]) ha) fun u ⟨hu, hz'⟩ => ⟨⟨m, hu⟩, hz'⟩,
          WP.mono (step_ok hE₂ hz T name hs hi (by omega_using [h₁]) hb) fun u ⟨hu, hz'⟩ => ⟨⟨m', hu⟩, hz'⟩⟩)
    (fun _ _ ⟨_, _, h⟩ => h) fun a b ⟨_, ⟨ha, za⟩, ⟨hb, zb⟩⟩ => ?_
  refine ⟨by rw [eval_ne za, eval_ne zb], fun hf => ?_, fun ht => ?_⟩
  · by_cases e : 15 - n + 1 = 15
    · rw [e] at ha hb; exact ⟨ha, hb⟩
    · rw [eval_ne za, decide_eq_false e] at hf; cases hf
  · by_cases e : 15 - n + 1 = 15
    · rw [eval_ne za, decide_eq_true e] at ht; cases ht
    · rw [show 15 - n + 1 = 15 - (n - 1) by omega_using [h₁, h₂, e]] at ha hb
      exact ⟨n - 1, by omega_using [h₁], by omega_using [h₁, h₂, e], by omega_using [h₂], ha, hb⟩

/-! ## The chains -/

/-- The rest of the head of chain `i`, after the private key values'
addresses: `PRF`, the type `WOTS_HASH`. -/
abbrev headRest (p : Params) (name : String) (T : Thash4Impl p.n) : Prog isa :=
  .seq (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32))
    (.seq (.block (Wots.hashType (L p))) (.block []))

/-- After the private key values' addresses: `Base`, `i`, and what the rest
of the head leads to. -/
def H1 (hE : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (name : String) (T : Thash4Impl p.n) (i : Nat)
    (t : State) : Prop :=
  Base hE t ∧ t.gpr .r13 = BitVec.ofNat 64 i ∧ ∃ m, WP isa (headRest p name T) t (StepInv hE m i 0)

/-- After `PRF`. -/
def H2 (hE : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (i : Nat) (t : State) : Prop :=
  Base hE t ∧ t.gpr .r13 = BitVec.ofNat 64 i ∧
    ∃ m, WP isa (.seq (.block (Wots.hashType (L p))) (.block [])) t (StepInv hE m i 0)

theorem h1_ok (hE : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    (hs : stk = 8 + T.stack) {i : Nat} (hi : i < p.len) {t : State} (h : ChainInv hE i t) :
    WP isa (.block (Wots.prfLanes (L p))) t (H1 hE name T i) := by
  have W := chainHead_ok hE hz T name hs hi h.base h.mx h.r13 (fun k hk => (h.lanes k hk).a20)
    (X := .block []) (Q := StepInv hE t.mem i 0) fun u hu => WP.block_nil hu
  exact WP.mono (WP.and (prfs_ok hE hz hi h.base h.r13 fun k hk => (h.lanes k hk).a20) (WP.seq_iff.mp W))
    fun u ⟨⟨⟨hb, hg, _⟩, _⟩, hw⟩ => ⟨hb, by rw [hg _ (by decide), h.r13], t.mem, hw⟩

theorem h2_ok (hE : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    (hs : stk = 8 + T.stack) {i : Nat} {t : State} (h : H1 hE name T i t) :
    WP isa (thashCall (L p) name T.code Layout.oA Layout.strideA (2 * (L p).n + 32)) t (H2 hE i) := by
  have hn := hz.n32
  obtain ⟨hb, hr, m, hw⟩ := h
  exact WP.mono (WP.and (tcall_ok hE hz T name hs (o := 3296) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
      (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb
      (Q := fun t' => Base hE t' ∧ ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) fun t' hb' hcs _ _ _ => ⟨hb', hcs⟩) (WP.seq_iff.mp hw))
    fun u ⟨⟨hb', hcs⟩, hw'⟩ => ⟨hb', by rw [hcs _ (by simp [calleeSaved]), hr], m, hw'⟩

/-- Chain `i` of the four lanes. -/
theorem chain_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack)
    {i : Nat} (hi : i < p.len) :
    RelCT isa (fun a b => ChainInv hE₁ i a ∧ ChainInv hE₂ i b) (Wots.chainBody (L p) name T.code)
      fun _ _ => True :=
  relSeq (B₁ := H1 hE₁ name T i) (B₂ := H1 hE₂ name T i)
    (ct_prf hz.lays fun _ _ h => chain_eq hsp h.1.base h.2.base h.1.r13 h.2.r13)
    (fun _ h => h1_ok hE₁ hz T name hs hi h) (fun _ h => h1_ok hE₂ hz T name hs hi h)
  (relSeq (B₁ := H2 hE₁ i) (B₂ := H2 hE₂ i) (tcallA_rel hE₁ hE₂ hsp hz T name hs fun _ _ h => ⟨h.1.1, h.2.1⟩)
    (fun _ h => h2_ok hE₁ hz T name hs h) (fun _ h => h2_ok hE₂ hz T name hs h)
  (relSeq (B₁ := fun t => ∃ m, StepInv hE₁ m i 0 t) (B₂ := fun t => ∃ m, StepInv hE₂ m i 0 t)
    (ct_hashType hz.lays fun _ _ h => base_eq hsp h.1.1 h.2.1)
    (fun _ ⟨_, _, m, hw⟩ => WP.mono (WP.seq_iff.mp hw) fun _ hv => ⟨m, wp_skip hv⟩)
    (fun _ ⟨_, _, m, hw⟩ => WP.mono (WP.seq_iff.mp hw) fun _ hv => ⟨m, wp_skip hv⟩)
  (RelCT.seq (steps_rel hE₁ hE₂ hsp hz T name hs hi)
    (ct_end hz.lays fun _ _ ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ => chain_eq hsp ha.base hb.base ha.r13 hb.r13))))

/-- The `len` chains. -/
theorem chains_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack) :
    RelCT isa (fun a b => ChainInv hE₁ 0 a ∧ ChainInv hE₂ 0 b) (.loop (Wots.chainBody (L p) name T.code) .ne)
      (fun a b => ChainInv hE₁ p.len a ∧ ChainInv hE₂ p.len b) := by
  have hl : 1 ≤ p.len := by have := hz.len; omega_using [this]
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
  refine RelCT.mono (RelCT.wp (F₁ := fun (u : State) => ChainInv hE₁ (p.len - n + 1) u ∧
        u.zf = some (decide (p.len - n + 1 = p.len)))
      (F₂ := fun (u : State) => ChainInv hE₂ (p.len - n + 1) u ∧ u.zf = some (decide (p.len - n + 1 = p.len)))
      (chain_rel hE₁ hE₂ hsp hz T name hs hi)
      fun a b ⟨ha, hb⟩ => ⟨chainBody_ok hE₁ hz T name hs hi ha, chainBody_ok hE₂ hz T name hs hi hb⟩)
    (fun _ _ ⟨_, _, h⟩ => h) fun a b ⟨_, ⟨ha, za⟩, ⟨hb, zb⟩⟩ => ?_
  refine ⟨by rw [eval_ne za, eval_ne zb], fun hf => ?_, fun ht => ?_⟩
  · by_cases e : p.len - n + 1 = p.len
    · rw [e] at ha hb; exact ⟨ha, hb⟩
    · rw [eval_ne za, decide_eq_false e] at hf; cases hf
  · by_cases e : p.len - n + 1 = p.len
    · rw [eval_ne za, decide_eq_true e] at ht; cases ht
    · rw [show p.len - n + 1 = p.len - (n - 1) by omega_using [h₁, h₂, e]] at ha hb
      exact ⟨n - 1, by omega_using [h₁], by omega_using [h₁, h₂, e], by omega_using [h₂], ha, hb⟩

/-! ## The public keys, and the whole function -/

theorem leaves_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack) :
    RelCT isa (fun a b => ChainInv hE₁ p.len a ∧ ChainInv hE₂ p.len b) (Wots.leaves (L p) name T.code)
      fun _ _ => True := by
  have hl := hz.len
  have hlm : (p.n + 32 + p.len * p.n) % 8 = 0 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e]
  have hll : p.n + 32 + p.len * p.n ≤ 2208 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have hc : ∀ {E : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁} {t : State}, ChainInv E p.len t →
      WP isa (thashCall (L p) name T.code Layout.oB Layout.strideB ((L p).n + 32 + (L p).len * (L p).n)) t (Base E) :=
    fun h => tcall_ok _ hz T name hs (o := 3808) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
      (by omega_using []) hlm hll h.base fun _ hb _ _ _ _ => hb
  exact relSeq (B₁ := Base hE₁) (B₂ := Base hE₂)
    (tcall_rel hE₁ hE₂ hsp hz T name hs (o := 3808) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
      (by omega_using []) hlm hll (fun hr => ct_argsB hz.lays hr) fun _ _ h => ⟨h.1.base, h.2.base⟩)
    (fun _ h => hc h)
    (fun _ h => tcall_ok hE₂ hz T name hs (o := 3808) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
      (by omega_using []) hlm hll h.base fun _ hb _ _ _ _ => hb)
    (ct_leaf hz.lays fun _ _ h => base_eq hsp h.1 h.2)

theorem wots_rel (hE₁ : Entry p stk σ₁ S sig kp idx₁ pk₁ a₁ sk₁) (hE₂ : Entry p stk σ₂ S sig kp idx₂ pk₂ a₂ sk₂)
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hz : Sz p) (T : Thash4Impl p.n) (name : String) (hs : stk = 8 + T.stack) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (Wots.wotsLeaves4 (L p) name T.code) fun _ _ => True :=
  relSeq (B₁ := ChainInv hE₁ 0) (B₂ := ChainInv hE₂ 0)
    (ct_start hz.lays fun _ _ ⟨e₁, e₂⟩ r hr => by
      rw [e₁, e₂]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hE₁.rdi, hE₂.rdi]
      · rw [hE₁.rsi, hE₂.rsi]
      · rw [hE₁.rcx, hE₂.rcx]
      · exact hsp)
    (fun _ e => by rw [e]; exact start_ok hE₁ hz) (fun _ e => by rw [e]; exact start_ok hE₂ hz)
  (RelCT.seq (chains_rel hE₁ hE₂ hsp hz T name hs)
  (relSeq (B₁ := Base hE₁) (B₂ := Base hE₂) (leaves_rel hE₁ hE₂ hsp hz T name hs)
    (fun _ h => WP.mono (leaves_ok hE₁ hz T name hs h) fun _ h' => h'.1)
    (fun _ h => WP.mono (leaves_ok hE₂ hz T name hs h) fun _ h' => h'.1)
    (ct_restore fun _ _ h => base_eq hsp h.1 h.2)))

end

/-- The entry facts of a state of the precondition, with its `scratch`,
`sig` and `kp` given. -/
theorem entry_of {p : Params} {stk : Nat} {s : State} (h : (wots4Contract p stk).pre s) {S sig : Addr} {kp : Nat}
    (hS : s.gpr .rdi = S) (hsig : s.gpr .rcx = sig) (hkp : (s.gpr .rsi).toNat = kp) :
    ∃ pkSeed a16, Entry p stk s S sig kp (s.gpr .rdx).toNat pkSeed a16 (bytesAt s.mem (at' S Layout.oSkSeed) p.n) := by
  subst hS hsig hkp
  obtain ⟨hreg, ⟨pkSeed, a16, henv⟩, hkp4, hkpN, hidx, hdig⟩ := h
  exact ⟨pkSeed, a16, rfl, by simp, by simp, rfl, hreg, henv, rfl, hkp4, hkpN, hidx, hdig⟩

/-- `wotsLeaves4` is constant time. -/
theorem wots4_ct {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    ConstantTime isa (wots4Contract p (8 + T.stack)).pre (wots4Contract p (8 + T.stack)).pub
      (Wots.wotsLeaves4 (L p) name T.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨_, _, hE₁⟩ := entry_of h₁ rfl rfl rfl
  obtain ⟨_, _, hE₂⟩ := entry_of h₂ hp.1.symm hp.2.2.1.symm (congrArg BitVec.toNat hp.2.1.symm)
  exact (wots_rel hE₁ hE₂ hp.2.2.2 hz T name rfl _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The stack pointer, the depth of calls, and calls of `wotsLeaves4` -/

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) :=
  fun i hi => (List.mem_append.mp hi).elim (ha i) (hb i)

theorem nosp_block {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .rsp) = true) : NoSp (.block is) :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

/-- `wotsLeaves4` never writes `rsp` itself, for each layout. -/
theorem wots4_nosp {L : Layout} (hL : Lays L) (name : String) {t4 : Prog isa} (hT : NoSp t4) :
    NoSp (Wots.wotsLeaves4 L name t4) := by
  rcases hL with rfl | rfl | rfl <;>
  exact nosp_seq (nosp_block (by kernel_rfl))
    (nosp_seq (fun i hi => nosp_seq (nosp_block (by kernel_rfl))
        (nosp_seq (nosp_seq (nosp_block (by kernel_rfl)) (fun i hi => hT i hi))
          (nosp_seq (nosp_block (by kernel_rfl))
            (nosp_seq (fun i hi => nosp_seq (nosp_block (by kernel_rfl))
                (nosp_seq (nosp_seq (nosp_block (by kernel_rfl)) (fun i hi => hT i hi)) (nosp_block (by kernel_rfl))) i hi)
              (nosp_block (by kernel_rfl))))) i hi)
      (nosp_seq (nosp_seq (nosp_seq (nosp_block (by kernel_rfl)) (fun i hi => hT i hi)) (nosp_block (by kernel_rfl)))
        (nosp_block (by kernel_rfl))))

theorem wots4_depth (L : Layout) (name : String) (t4 : Prog isa) :
    (Wots.wotsLeaves4 L name t4).depth = t4.depth + 1 := by
  simp [Wots.wotsLeaves4, Wots.chainBody, Wots.stepBody, Wots.leaves, thashCall, Code.depth]

/-- A call of `wotsLeaves4`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem wots4call_ok {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name wn : String) {s : State}
    {rd wr : List Region} (hpre : (wots4Contract p (8 + T.stack)).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (T.code.depth + 2))]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (wots4Contract p (8 + T.stack)).post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call wn (Wots.wotsLeaves4 (L p) name T.code)) s Q := by
  have hd := T.depth_le
  exact WP.call_mx (wots4_correct hz T name) (wots4_nosp hz.lays name T.nosp)
    (by rw [wots4_depth]; omega_using [hd]) hpre hc hw fun s' h₁ h₂ h₃ h₄ _ h₆ h₇ =>
      hQ s' h₁ h₂ h₃ (by rw [wots4_depth] at h₄; exact h₄) h₆ h₇

/-! ## A state satisfying the precondition -/

/-- `scratch` and `sig` in the witness. -/
abbrev satS : Addr := BitVec.ofNat 64 0x100000
abbrev satSig : Addr := BitVec.ofNat 64 0x10000

/-- The witness: the round constants in `work` (`Thash4Avx.satMem`, whose
table is at `satS + 1600`), zeros elsewhere; `kp` and `idx` 0. -/
def wsat (p : Params) : State where
  gpr r := match r with
    | .rdi => satS | .rcx => satSig | .rsp => BitVec.ofNat 64 0x200000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := Thash4Avx.satMem
  rd := []
  wr := [⟨satS, scratchLen⟩, ⟨satSig, p.len * p.n⟩]

theorem sat_byte {o : Nat} (h₁ : 2368 ≤ o) (h₂ : o < 65536) : Thash4Avx.satMem (at' satS o) = 0 := by
  have ha : (at' satS o).toNat = 0x100000 + o := by
    simp only [at', BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h₂]
  simp only [Thash4Avx.satMem, Thash4Avx.satW, ha]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h₁]))]

theorem sat_zero {o l : Nat} (h₁ : 2368 ≤ o) (h₂ : o + l ≤ 65536) :
    bytesAt Thash4Avx.satMem (at' satS o) l = List.replicate l 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp [bytesAt], fun b hb => ?_⟩
  simp only [bytesAt, List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  rw [at', BitVec.add_assoc, ← BitVec.ofNat_add]
  exact sat_byte (by omega_using [h₁]) (by omega_using [h₂, hi])

theorem wsat_pre {p : Params} (hz : Sz p) {stk : Nat} (hstk : stk ≤ 24) : (wots4Contract p stk).pre (wsat p) := by
  have hn := hz.n32
  have hl := hz.len
  have hln : p.len * p.n ≤ 2144 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  have hsp : (BitVec.ofNat 64 0x200000 - BitVec.ofNat 64 stk).toNat = 0x200000 - stk := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hstk]
  have hS : satS.toNat = 0x100000 := rfl
  have hG : satSig.toNat = 0x10000 := rfl
  have hR : (BitVec.ofNat 64 0x200000 : Addr).toNat = 0x200000 := rfl
  have hB : (below (BitVec.ofNat 64 0x200000) stk).base.toNat + (below (BitVec.ofNat 64 0x200000) stk).len ≤ 2 ^ 64 := by
    dsimp only [below]; rw [hsp]; omega_using [hstk]
  have d₁ : (below (BitVec.ofNat 64 0x200000) stk).Disjoint ⟨satS, scratchLen⟩ := by
    refine (Offset.disjoint_of_le (r₁ := ⟨satS, scratchLen⟩) ?_ hB).symm
    dsimp only [below]; rw [hS, hsp]; simp only [scratchLen]; omega_using [hstk]
  have d₂ : (below (BitVec.ofNat 64 0x200000) stk).Disjoint ⟨satSig, p.len * p.n⟩ := by
    refine (Offset.disjoint_of_le (r₁ := ⟨satSig, p.len * p.n⟩) ?_ hB).symm
    dsimp only [below]; rw [hG, hsp]; omega_using [hstk, hln]
  refine ⟨⟨rfl, rfl, by show satS.toNat + scratchLen ≤ _; rw [hS]; decide,
    by show satSig.toNat + p.len * p.n ≤ _; rw [hG]; omega_using [hln],
    Offset.disjoint_of_le (by show satSig.toNat + p.len * p.n ≤ satS.toNat; rw [hG, hS]; omega_using [hln])
      (by show satS.toNat + Layout.oSigTmp ≤ _; rw [hS]; decide),
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    (Offset.disjoint_of_le (by show satS.toNat + scratchLen ≤ (BitVec.ofNat 64 0x200000 : Addr).toNat; rw [hS, hR]; decide)
      (by show (BitVec.ofNat 64 0x200000 : Addr).toNat + 8 ≤ _; rw [hR]; decide)).symm,
    (Offset.disjoint_of_le (by show satSig.toNat + p.len * p.n ≤ (BitVec.ofNat 64 0x200000 : Addr).toNat; rw [hG, hR]; omega_using [hln])
      (by show (BitVec.ofNat 64 0x200000 : Addr).toNat + 8 ≤ _; rw [hR]; decide)).symm,
    fun _ h => absurd h List.not_mem_nil,
    d₁, d₂,
    fun _ h => absurd h List.not_mem_nil⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, Thash4Avx.sat_rc 16,
      fun k hk => sat_zero (by rw [laneA_eq]; omega_using []) (by rw [laneA_eq]; omega_using [hk, hn]),
      fun k hk => sat_zero (by rw [laneB_eq]; omega_using []) (by rw [laneB_eq]; omega_using [hk, hn]),
      fun k hk => sat_zero (by rw [laneA_eq]; omega_using []) (by rw [laneA_eq]; omega_using [hk, hn]),
      fun k hk => sat_zero (by rw [laneB_eq]; omega_using []) (by rw [laneB_eq]; omega_using [hk, hn])⟩,
    rfl, by show (0 + 4) * p.n ≤ 32 * Layout.nodeSlots; rw [nodeSlots_eq]; omega_using [hn],
    by show (0 : BitVec 64).toNat < 2 ^ 32; decide, fun i hi => ?_⟩
  show (Thash4Avx.satMem (at' satS (Layout.oDigits + i))).toNat < 16
  rw [sat_byte (by rw [oDigits_eq]; omega_using []) (by rw [oDigits_eq]; omega_using [hi, hl, hn])]
  decide

/-! ## `Verified` -/

/-- `wotsLeaves4` meets `wots4Contract`, for every implementation of `thash4`. -/
theorem wots4_verified {p : Params} (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    Verified X86_64.target (Wots.wotsLeaves4 ⟨p.n, p.len⟩ name T.code) (wots4Contract p (8 + T.stack)) :=
  ⟨wots4_correct hz T name, wots4_ct hz T name, ⟨wsat p, wsat_pre hz (by have := T.stack_le; omega_using [this])⟩⟩

end VG.Proof.SlhDsa.X86_64.Wots4
