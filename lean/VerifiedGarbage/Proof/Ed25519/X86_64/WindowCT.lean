import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport

/-! Merged from `Proof.Ed25519.X86_64.PointEqualCT`. -/
section
/-! Point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def EqualCTPre (base : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Scratch s base ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
      Keep base s t ∧
      t.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs pointEqualOps) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (hs.of_keep ka) 8 9) fun t ⟨tz, kt, te⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    RelCT isa (fun _ _ => True) (.block [.mov32 .rax (.imm (if b then 1 else 0))]) (fun _ _ => True) := by
  cases b
  · apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  · apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)

theorem equalSecond_ct (base : Addr) (u v : Spec.X25519.Fe) :
    RelCT isa (fun s t => (Scratch s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scratch t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (.block (fieldEqual fld 10 11)) (.ite .e (.block [.mov32 .rax (.imm 1)]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (Scratch s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scratch t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.block (fieldEqual fld 10 11)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : Scratch s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (.block (fieldEqual fld 10 11)) s fun t => t.zf = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun _ k => ?_
    rw [k.1, h.2.1, h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : Addr) (p q : Spec.Ed25519.Point) :
    RelCT isa (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (Impl.Ed25519.X86_64.pointEqual fld) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : EqualCTPre base p q s) :
      WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
        Scratch t base ∧ t.zf = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨h.1.of_keep kt, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.X86_64.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the public inputs are the same in both runs). The digits are
read through pointers and a counter in the scratch, the same in both runs by
correctness; everything else is public by the taint analysis. The final
comparison branches on whether two points of the group are equal, which only
depends on the points represented.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps)
open VG.Impl.X25519.X86_64 (sc)

variable {fld : Arith} [EdArith fld]

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : RelCT isa (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  VG.RelCT.seq ((VG.RelCT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) h₂

/-- Code the taint analysis proves constant time with `rdi` alone public. -/
theorem rdi_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .rdi = base)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree_rdi {x y : State} (h : x.gpr .rdi = y.gpr .rdi) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-! ## Digits -/

/-- The digit's address: the pointer at byte `ptr` plus `add`, and the counter. -/
def digitPrefix (ptr add : Nat) : List Instr :=
  [.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (sc 56))]

theorem digitPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {ptr add : Nat}
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P C : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P) (hc : s.mem.readW (off base 56) 64 = C) :
    WP isa (.block (digitPrefix ptr add)) s fun t =>
      t.gpr .rdi = base ∧ t.gpr .rsi = off P add ∧ t.gpr .rax = C := by
  rw [digitPrefix, show ([.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)),
      .mov .rax (.mem (sc 56))] : List Instr) =
    [.mov .rsi (.mem (sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      [.mov .rax (.mem (sc 56))]) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  have hb := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (loadPointer_ok hb .rax 56 (by decide)) fun c ⟨cp, kc⟩ => ?_
  refine ⟨(hb.of_keeps kc (by decide)).rdi, ?_, ?_⟩
  · rw [kc.1 _ (by decide), bp, ap, hp]
  · rw [cp, kb.2.1, ka.2.1, hc]

theorem agree_rsi_rax {x y : State} (h : x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rsi, .rax]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

theorem prefixK_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (digitPrefix 7952 0))
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

/-! ## Windows -/

theorem addDigitA_ct (tb : Bool) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.seq (.block [.alu .sub .rbx (.imm 1)]) (.seq (.block (tableAddr 5376 ++ pointFromTableQ))
      (Point64.addFn fld tb)))
    (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by cases tb <;> fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem baseAddrPart_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAddr)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem baseAddPart_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax)
    (.seq (.block pointFromTableQ) (Point64.addFn fld false)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rax]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem baseAddAffPart_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax)
    (.seq (.block pointFromTableQ) (addAffIn fld)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rax]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

/-- Before `S`'s digit's byte `v` is added, in one run: the static's address `T` at byte 7960. -/
structure BasePre (base T : Addr) (v : Nat) (x : State) : Prop where
  scratch : Scratch x base
  header : x.mem.readW (off base 7960) 64 = T
  rbx : x.gpr .rbx = BitVec.ofNat 64 v
  zf : x.zf = some (decide (v = 0))
  bound : v ≤ 128

/-- The addition of `S`'s digit: the branch is on its byte, its entry's address `T + 128 (v - 1)`
the same in both runs. -/
theorem addBase_ct {add : Prog isa}
    (hadd : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rax = y.gpr .rax)
      (.seq (.block pointFromTableQ) add) (fun _ _ => True)) {base T : Addr} {v : Nat} :
    RelCT isa (fun x y => BasePre base T v x ∧ BasePre base T v y) (addBase add)
      (fun _ _ => True) := by
  rw [addBase]
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.zf, h.2.zf]) ?_
    (VG.RelCT.block_nil fun _ _ _ => trivial)
  have hw (x : State) (h : BasePre base T v x) (hv : v ≠ 0) :
      WP isa (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAddr)) x fun u =>
        u.gpr .rdi = base ∧ u.gpr .rax = off T (128 * (v - 1)) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [WP.block_append_iff]
    refine WP.mono (accumulateDec_ok x n h.rbx) fun b ⟨bc, kb⟩ => ?_
    refine WP.mono (baseAddr_ok (T := T) (h.scratch.of_keeps kb (by decide)) (by rw [kb.2.1]; exact h.header) n
      (by have := h.bound; omega) bc) fun u ⟨ua, ku⟩ => ?_
    exact ⟨(ku.1 _ (by decide)).trans ((kb.1 _ (by decide)).trans h.scratch.rdi), ua⟩
  refine reassoc_ct ?_
  have hv (x : State) (h : BasePre base T v x) (he : isa.eval .ne x = some true) : v ≠ 0 := by
    intro h0
    simp only [eval, h.zf, h0, decide_true, Option.map_some, Bool.not_true, Option.some.injEq,
      Bool.false_eq_true] at he
  refine VG.RelCT.seq ((VG.RelCT.wp (baseAddrPart_ct.mono (fun x y h =>
    ⟨h.1.1.scratch.rdi.trans h.1.2.scratch.rdi.symm, h.1.1.rbx.trans h.1.2.rbx.symm⟩) (fun _ _ h => h))
    fun x y h => ⟨hw x h.1.1 (hv x h.1.1 h.2), hw y h.1.2 (hv x h.1.1 h.2)⟩).mono (fun _ _ h => h) ?_)
    hadd
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

/-! ## Bytes -/

theorem batchBegin_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block batchBegin)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem batchTest_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block batchTest)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem counterCmp_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi)
    (.block [.mov .rbx (.mem (sc 56)), .alu .cmp .rbx (.imm 32)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

/-! ## Skipping the leading zero bytes of `k` -/

/-- A run of the skipping's result: from a state satisfying `R₀`, with `c` bytes left. -/
def SkipLoopRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipLoop s₀ base kp sp T A K S c x

/-- A run of the skipping: from a state satisfying `R₀`, with `32 + n` bytes left. -/
def SkipRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (K S n : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipInv s₀ base kp sp T A K S n x

theorem skipPrefix_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi)
    (.block (batchBegin ++ digitPrefix 7952 0)) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem skipRest_ct : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rsi, index := some .rax }, .alu .test .rbx (.reg .rbx)])
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rsi, .rax]) (fun _ _ h => agree_rsi_rax h) (by fld_taint_decide)

theorem skipStop_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block skipStop)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem skipPrefix_ok {s : State} {base kp : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7952) 64 = kp) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block (batchBegin ++ digitPrefix 7952 0)) s fun t =>
      t.gpr .rsi = off kp 0 ∧ t.gpr .rax = BitVec.ofNat 64 j := by
  rw [WP.block_append_iff]
  refine WP.mono (batchBegin_ok hs j hc) fun a ⟨_, ac, ag, _, aw, am⟩ => ?_
  have ha : Scratch a base := ⟨(ag _ (by decide)).trans hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
  exact WP.mono (digitPrefix_ok ha (by decide) (by decide)
    ((am.word (Or.inr (by decide)) (by decide)).trans hp) ac) fun _ ⟨_, ts, ta⟩ => ⟨ts, ta⟩

theorem skipBody_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S j : Nat} :
    RelCT isa (fun x y => SkipRun R₀ base kp sp T A K S (j + 1) x ∧ SkipRun R₀ base kp sp T A K S (j + 1) y)
      skipBody (fun _ _ => True) := by
  let P := SkipRun R₀ base kp sp T A K S (j + 1)
  have hrdi (x : State) (h : P x) : x.gpr .rdi = base := by
    obtain ⟨_, _, h, _⟩ := h; exact h.ctx.scratch.rdi
  have hpre (x : State) (h : P x) : WP isa (.block (batchBegin ++ digitPrefix 7952 0)) x fun t =>
      t.gpr .rsi = off kp 0 ∧ t.gpr .rax = BitVec.ofNat 64 (32 + j) := by
    obtain ⟨_, _, h, _⟩ := h
    exact skipPrefix_ok h.ctx.scratch h.ctx.kHeader (32 + j) (by rw [h.counter]; rfl)
  have hload : RelCT isa (fun x y => P x ∧ P y) (.block skipLoad) (fun _ _ => True) := by
    rw [show skipLoad = (batchBegin ++ digitPrefix 7952 0) ++
      [.movzx8 .rbx { base := .rsi, index := some .rax }, .alu .test .rbx (.reg .rbx)] from rfl]
    refine blockAppend_ct ((VG.RelCT.wp (rdi_ct hrdi skipPrefix_ct) fun x y h =>
      ⟨hpre x h.1, hpre y h.2⟩).mono (fun _ _ h => h) ?_) skipRest_ct
    intro x y ⟨_, hx, hy⟩
    exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩
  have hw (x : State) (h : P x) : WP isa (.block skipLoad) x fun u => u.gpr .rdi = base ∧
      u.zf = some (decide (K / 256 ^ (32 + j) % 256 = 0)) := by
    obtain ⟨_, _, hl, _, _, hn⟩ := h
    refine WP.mono (skipLoad_ok hl.ctx (32 + j) (by omega) (by rw [hl.counter]; rfl))
      fun u ⟨uz, _, ku⟩ => ⟨(ku.byte.scratch hl.ctx.scratch).rdi, ?_⟩
    rw [uz, scalar_byte (n := 64) (by omega), hl.kVal]
  have hcmp : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block counterCmp) (fun _ _ => True) := by
    rw [counterCmp]; exact counterCmp_ct
  rw [skipBody]
  refine VG.RelCT.seq ((VG.RelCT.wp hload fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine VG.RelCT.ite (fun x y h => by simp only [eval, h.1.2, h.2.2]) ?_ ?_
  · exact skipStop_ct.mono (fun _ _ h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)
  · exact hcmp.mono (fun _ _ h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

theorem skipZero_ct {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat} :
    RelCT isa (fun x y => SkipRun R₀ base kp sp T A K S 32 x ∧ SkipRun R₀ base kp sp T A K S 32 y) skipZero
      (fun x y => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ K / 256 ^ c = 0 ∧ SkipLoopRun R₀ base kp sp T A K S c x ∧
        SkipLoopRun R₀ base kp sp T A K S c y) := by
  rw [skipZero]
  refine VG.RelCT.loop (M := isa)
    (fun n x y => SkipRun R₀ base kp sp T A K S n x ∧ SkipRun R₀ base kp sp T A K S n y) ?_ 32
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => by obtain ⟨_, _, _, _, h, _⟩ := h.1; exact Nat.lt_irrefl 0 h
  by_cases hj : j < 32
  · have hw (x : State) (h : SkipRun R₀ base kp sp T A K S (j + 1) x) : WP isa skipBody x fun u =>
        isa.eval .ne u = some (skipOn K j) ∧
        (skipOn K j = false → SkipLoopRun R₀ base kp sp T A K S (skipEnd K j) u ∧
          K / 256 ^ skipEnd K j = 0) ∧
        (skipOn K j = true → SkipRun R₀ base kp sp T A K S j u) := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (skipBody_ok h) fun u ⟨uz, uf, ut⟩ =>
        ⟨uz, fun hf => ⟨⟨s₀, r₀, (uf hf).1⟩, (uf hf).2⟩, fun ht => ⟨s₀, r₀, ut ht⟩⟩
    refine (VG.RelCT.wp skipBody_ct fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have hs : skipOn K j = false := Option.some.inj (xz.symm.trans he)
      exact ⟨skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2, (xf hs).2, (xf hs).1,
        (yf hs).1⟩
    · have hs : skipOn K j = true := Option.some.inj (xz.symm.trans he)
      exact ⟨j, by omega, xt hs, yt hs⟩
  · exact VG.RelCT.of_false fun _ _ h => by obtain ⟨_, _, _, _, _, h⟩ := h.1; exact hj (by omega)

/-! ## The comparison -/

/-- Two points representing `P` and `Q` (`X : Y : Z`) in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scratch s base ∧ RepP (point (env s.mem base) 0 1 2 3) P ∧ RepP (point (env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (Impl.Ed25519.X86_64.pointEqual fld) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
        Scratch t base ∧ t.zf = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨h.1.of_keep kt, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact repP_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : RelCT isa (fun s t => (Scratch s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scratch t base ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual fld 10 11)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw2 (s : State) (h : Scratch s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual fld 10 11)) s fun t => t.zf = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun _ k => by
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := VG.RelCT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.X86_64.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine VG.RelCT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
    · exact fun _ _ h => by simp only [eval, h.2.1, h.2.2]
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
