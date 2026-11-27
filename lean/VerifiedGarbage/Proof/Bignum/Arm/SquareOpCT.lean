module

import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.Row
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
meta import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Bignum.Arm.SquareState
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.Square
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareState
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Bignum.Arm.SquareRedCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.SquareCrossCT`, which only this module used -/

section

/-! ### `Bignum.Arm.SquareCTBase`, which only this module used -/

section

/-! # Two runs of a square leak the same trace: the pieces

The square's addresses and counts come from its metadata and the header,
which correctness shows hold the same public values in both runs. Each
piece between such loads is checked by the taint analysis from the
registers correctness pins down (`seg`), or by an existing constant-time
proof (`segCT`); the loads from the stack (`segStack`) have the same
address in both runs. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

/-- A piece the taint analysis checks with the registers `rs` public. -/
abbrev SqCert (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs rs) c hc).isSome = true

theorem seg {P Q : State → Prop} {c : Prog isa} {rs : List Reg} (hc : SqCert rs c)
    (pin : ∀ s t, P s → P t → ∀ r ∈ rs, s.gpr r = t.gpr r) (wp : ∀ s, P s → WP isa c s Q) :
    RelCT isa (fun s t => P s ∧ P t) c (fun s t => Q s ∧ Q t) := by
  obtain ⟨h, hh⟩ := hc
  exact pair_posts (RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun s t hst => Taint.agree_ofRegs (pin s t hst.1 hst.2)) hh) wp

/-- The last piece: its trace alone. -/
theorem segEnd {P : State → Prop} {c : Prog isa} {rs : List Reg} (hc : SqCert rs c)
    (pin : ∀ s t, P s → P t → ∀ r ∈ rs, s.gpr r = t.gpr r) :
    RelCT isa (fun s t => P s ∧ P t) c (fun _ _ => True) := by
  obtain ⟨h, hh⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s t hst => Taint.agree_ofRegs (pin s t hst.1 hst.2)) hh

theorem segStack {P Q : State → Prop} {r : Reg} {d : Nat} (sp : ∀ s t, P s → P t → s.sp = t.sp)
    (wp : ∀ s, P s → WP isa (.block [.ldrSp r d]) s Q) :
    RelCT isa (fun s t => P s ∧ P t) (.block [.ldrSp r d]) (fun s t => Q s ∧ Q t) :=
  pair_posts ((loadStack_ct r d).mono (fun s t h => sp s t h.1 h.2) (fun _ _ _ => trivial)) wp

theorem segCT {P Q : State → Prop} {c : Prog isa} {Pub : State → State → Prop}
    (ct : ConstantTime isa (fun _ => True) Pub c) (pub : ∀ s t, P s → P t → Pub s t)
    (wp : ∀ s, P s → WP isa c s Q) :
    RelCT isa (fun s t => P s ∧ P t) c (fun s t => Q s ∧ Q t) :=
  pair_posts (fun s t tr1 tr2 u v h e1 e2 =>
    ⟨ct s t tr1 tr2 u v trivial trivial (pub s t h.1 h.2) e1 e2, trivial⟩) wp

theorem anchorLoad_cert : SqCert [.r0] (.block [.ldr .r0 .r0 80]) := ⟨_, by taint_decide⟩

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

/-- What every point of a square keeps: the stack pointer and the environment. -/
def SqHold (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (s : State) : Prop :=
  s.sp = sp0 ∧ ∃ m0 inv, SqEnv m0 base size out a mod M n inv s

theorem sqAnchor_ct {P : State → Prop} (hold : ∀ s, P s → SqHold base size out a mod M n sp0 s)
    (stable : ∀ s t, P s → t.mem = s.mem → Rest [.r0] s t → P t) :
    RelCT isa (fun s t => P s ∧ P t) sqAnchor fun s t =>
      (P s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M) ∧ (P t ∧ t.gpr .r0 = base + BitVec.ofNat 32 M) := by
  unfold sqAnchor
  have first := segStack (P := P) (Q := fun s => P s ∧ s.gpr .r0 = base) (r := .r0) (d := 0)
    (fun s t hs ht => (hold s hs).1.trans (hold t ht).1.symm) (fun s hs => by
      obtain ⟨_, m0, inv, env⟩ := hold s hs
      exact WP.mono (sqBase_ok s env .r0) fun t ⟨p, mem, rest⟩ => ⟨stable s t hs mem rest, p⟩)
  refine first.seq (seg anchorLoad_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_))
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
  · obtain ⟨_, m0, inv, env⟩ := hold s hs.1
    have nowrap := env.nowrap
    have := env.header; have := env.fits
    refine wp_ldr (a := off (State.addr base) 80) (by decide) (sq_ea0 nowrap hs.2 (by omega_arith))
      (env.read (by omega_arith)) fun t ut => WP.block_nil ?_
    exact ⟨stable s t hs.1 ut.mem (ut.rest (by simp)), ut.gpr.trans env.metaNow⟩

end

end VG.Proof.Bignum.Arm

end

end

/-! # The square's setup and rows of cross products leak only the width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem sqInit_cert : SqCert [.r6, .r7] sqInit := ⟨_, by taint_decide⟩
theorem crossArgs_cert : SqCert [.r0] (.block crossArgs) := ⟨_, by taint_decide⟩
theorem crossScalar_cert : SqCert [.r2] (.block crossScalar) := ⟨_, by taint_decide⟩
theorem crossCarry_cert : SqCert [.r0] (.block crossCarry) := ⟨_, by taint_decide⟩
theorem sqCount_cert : SqCert [.r0] (.block sqCount) := ⟨_, by taint_decide⟩

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

/-- The square's entry, from `MontFn.bases`' registers. -/
def SqStart (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (s : State) : Prop :=
  s.sp = sp0 ∧ (∃ inv, SqEnv s.mem base size out a mod M n inv s) ∧
    s.gpr .r6 = base + BitVec.ofNat 32 M ∧ s.gpr .r7 = BitVec.ofNat 32 n ∧
    s.gpr .r8 = base + BitVec.ofNat 32 a ∧ s.gpr .r10 = base + BitVec.ofNat 32 out

/-- After `k` rows of cross products. -/
def CrossReady (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (k : Nat) (s : State) : Prop :=
  s.sp = sp0 ∧ ∃ m0 inv, CrossInv m0 base size out a mod M n inv k s

theorem CrossInv.of_mem {m0 : Mem} {inv : BitVec 32} {k : Nat} {s t : State} {rs : List Reg}
    (h : CrossInv m0 base size out a mod M n inv k s) (mem : t.mem = s.mem) (rest : Rest rs s t) :
    CrossInv m0 base size out a mod M n inv k t := by
  refine ⟨h.env.of_mem mem rest, h.index, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mem]
  exacts [h.md, h.next, h.cnt, h.tptr, h.value, h.top]

theorem sqInit_ct :
    RelCT isa (fun s t => SqStart base size out a mod M n sp0 s ∧ SqStart base size out a mod M n sp0 t) sqInit
      (fun s t => CrossReady base size out a mod M n sp0 0 s ∧ CrossReady base size out a mod M n sp0 0 t) := by
  refine seg sqInit_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.2.1.trans ht.2.2.1.symm
    · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
  · obtain ⟨sp, ⟨inv, env⟩, p6, p7, p8, p10⟩ := hs
    exact WP.mono (sqInit_ok s env p6 p7 p8 p10) fun t ⟨ht, rt⟩ => ⟨rt.sp.trans sp, _, _, ht⟩

theorem crossRound_ct {k : Nat} (hk : k + 2 ≤ n) :
    RelCT isa (fun s t => CrossReady base size out a mod M n sp0 k s ∧ CrossReady base size out a mod M n sp0 k t)
      crossRound (fun _ _ => True) := by
  -- The points between the pieces.
  let o := M + 28 + 8 * k
  let len := n - 1 - k
  let P1 := fun s : State => CrossReady base size out a mod M n sp0 k s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M
  let P2 := fun s : State => SqHold base size out a mod M n sp0 s ∧ s.gpr .r2 = base + BitVec.ofNat 32 (a + 4 * k) ∧
    s.gpr .r12 = base + BitVec.ofNat 32 (a + 4 * k + 4) ∧ s.gpr .lr = BitVec.ofNat 32 len ∧
    s.gpr .r0 = base + BitVec.ofNat 32 o
  let P3 := fun s : State => SqHold base size out a mod M n sp0 s ∧
    s.gpr .r12 = base + BitVec.ofNat 32 (a + 4 * k + 4) ∧ s.gpr .lr = BitVec.ofNat 32 len ∧
    s.gpr .r0 = base + BitVec.ofNat 32 o
  let P4 := fun s : State => SqHold base size out a mod M n sp0 s ∧ s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * len)
  let P5 := SqHold base size out a mod M n sp0
  have holdStable : ∀ s t : State, P5 s → t.mem = s.mem → Rest [.r0] s t → P5 t :=
    fun s t ⟨sp, m0, inv, env⟩ mem rest => ⟨rest.sp.trans sp, m0, inv, env.of_mem mem rest⟩
  have A := sqAnchor_ct (P := CrossReady base size out a mod M n sp0 k)
    (fun s ⟨sp, m0, inv, h⟩ => ⟨sp, m0, inv, h.env⟩)
    (fun s t ⟨sp, m0, inv, h⟩ mem rest => ⟨rest.sp.trans sp, m0, inv, h.of_mem mem rest⟩)
  have B : RelCT isa (fun s t => P1 s ∧ P1 t) (.block crossArgs) (fun s t => P2 s ∧ P2 t) := by
    refine seg crossArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨sp, m0, inv, h⟩, p0⟩ := hs
      have env := h.env
      have nowrap := env.nowrap
      have := env.fits; have := env.count
      refine WP.mono (crossArgs_ok s (A := a + 4 * k) (C := len) (P := o) env.workspace (by omega_arith) p0 h.next
        h.cnt h.tptr) ?_
      rintro t ⟨g2, g12, glr, g0, _, mt, rt⟩
      have o1 := writeW32_outside s.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 8)) (by omega_arith)
      have o2 := writeW32_outside (s.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (o + 8)))
        (State.addr base) (d := M + 12) (base + BitVec.ofNat 32 (a + 4 * k + 4)) (by omega_arith)
      rw [← mt] at o2
      have O : Outside (State.addr base) M (4 * (2 * n + 8)) s.mem t.mem :=
        (o1.mono (by omega_using []) (by omega_using [])).trans (o2.mono (by omega_using []) (by omega_using []))
      exact ⟨⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside O (by simp)) rt⟩, g2, g12, glr, g0⟩
  have C : RelCT isa (fun s t => P2 s ∧ P2 t) (.block crossScalar) (fun s t => P3 s ∧ P3 t) := by
    refine seg crossScalar_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.1.trans ht.2.1.symm
    · obtain ⟨⟨sp, m0, inv, env⟩, g2, g12, glr, g0⟩ := hs
      have := env.aFits; have := env.count
      refine WP.mono (crossScalar_ok s env.workspace (by omega_arith) g2) ?_
      rintro t ⟨_, mt, rt⟩
      exact ⟨⟨rt.sp.trans sp, m0, inv, env.of_mem mt rt⟩, by rw [rt.gpr .r12 (by simp)]; exact g12,
        by rw [rt.gpr .lr (by simp)]; exact glr, by rw [rt.gpr .r0 (by simp)]; exact g0⟩
  have D : RelCT isa (fun s t => P3 s ∧ P3 t) row (fun s t => P4 s ∧ P4 t) := by
    refine segCT row_ct (fun s t hs ht => ⟨hs.2.2.2.trans ht.2.2.2.symm, hs.2.1.trans ht.2.1.symm,
      hs.2.2.1.trans ht.2.2.1.symm⟩) (fun s hs => ?_)
    obtain ⟨⟨sp, m0, inv, env⟩, g12, glr, g0⟩ := hs
    have := env.aFits; have := env.count; have := env.fits; have := env.sepA
    have ctx : RowCtx s base size o (a + 4 * (k + 1)) len :=
      ⟨env.nowrap, by omega_arith, by omega_arith, by omega_using [this], env.workspace.writable⟩
    refine WP.mono (row_ok s ctx (by omega) g0 (by rw [g12, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_using []]) glr) ?_
    intro t ri
    exact ⟨⟨ri.rest.sp.trans sp, m0, inv, env.next (Outs.of_outside (ri.outside.mono (o' := M)
      (n' := 4 * (2 * n + 8)) (by omega_using []) (by omega_using [hk])) (by simp)) ri.rest⟩, ri.outPtr⟩
  have E : RelCT isa (fun s t => P4 s ∧ P4 t) (.block crossCarry) (fun s t => P5 s ∧ P5 t) := by
    refine seg crossCarry_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨sp, m0, inv, env⟩, g0⟩ := hs
      have := env.count; have := env.fits; have := env.nowrap
      refine WP.mono (crossCarry_ok s env.workspace (by omega_arith) g0) ?_
      rintro t ⟨mt, rt⟩
      have O := writeW32_outside s.mem (State.addr base) (d := o + 4 * len) (s.gpr .r11) (by omega)
      rw [← mt] at O
      exact ⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside (O.mono (o' := M) (n' := 4 * (2 * n + 8))
        (by omega_using []) (by omega_using [hk])) (by simp)) rt⟩
  have F := sqAnchor_ct (P := P5) (fun _ h => h) holdStable
  have G : RelCT isa (fun s t => (P5 s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M) ∧
      (P5 t ∧ t.gpr .r0 = base + BitVec.ofNat 32 M)) (.block sqCount) (fun _ _ => True) :=
    segEnd sqCount_cert fun s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
  unfold crossRound
  exact A.seq (B.seq (C.seq (D.seq (E.seq (F.seq G)))))

theorem crossRows_ct :
    RelCT isa (fun s t => CrossReady base size out a mod M n sp0 0 s ∧ CrossReady base size out a mod M n sp0 0 t)
      crossRows (fun s t => CrossReady base size out a mod M n sp0 (n - 1) s ∧
        CrossReady base size out a mod M n sp0 (n - 1) t) := by
  let I := fun k s t => ∃ i, i + k = n - 1 ∧ 0 < k ∧
    CrossReady base size out a mod M n sp0 i s ∧ CrossReady base size out a mod M n sp0 i t
  have step : ∀ k, RelCT isa (I k) crossRound fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → CrossReady base size out a mod M n sp0 (n - 1) s ∧
        CrossReady base size out a mod M n sp0 (n - 1) t) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k
    apply RelCT.exists_
    intro i
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨hik, hk, hs, ht⟩ := h
    have hn : i + 2 ≤ n := by
      obtain ⟨_, _, _, hi⟩ := hs
      have := hi.index
      omega_using [hik, hk]
    have ready (x : State) (hx : CrossReady base size out a mod M n sp0 i x) :
        WP isa crossRound x fun y => CrossReady base size out a mod M n sp0 (i + 1) y ∧ y.z = decide (i + 2 = n) := by
      obtain ⟨sp, m0, inv, hx⟩ := hx
      exact WP.mono (crossRound_ok x hx hn) fun y ⟨hy, z, r⟩ => ⟨⟨r.sp.trans sp, m0, inv, hy⟩, z⟩
    obtain ⟨trace, _, ⟨hu, zu⟩, ⟨hv, zv⟩⟩ :=
      (crossRound_ct hn).wp (fun x y h => ⟨ready x h.1, ready y h.2⟩) s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    refine ⟨trace, ?_, fun branch => ?_, fun branch => ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · have : i + 2 = n := by
        change some (!u.z) = some false at branch
        by_contra ne
        simp only [zu, ne, decide_false, Bool.not_false] at branch
        cases branch
      rw [show n - 1 = i + 1 by omega_using [this]]
      exact ⟨hu, hv⟩
    · have ne : i + 2 ≠ n := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, ne], hu, hv⟩
  apply (RelCT.loop I step (n - 1)).mono _ (fun _ _ h => h)
  intro s t h
  obtain ⟨_, m0, inv, hi⟩ := h.1
  have := hi.env.count
  exact ⟨0, by omega_using [], by omega_using [this], h⟩

end

end VG.Proof.Bignum.Arm

end

end

/-! # The square's doubling, squares of words and reduction leak only the width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem sqDoubleArgs_cert : SqCert [.r0] (.block sqDoubleArgs) := ⟨_, by taint_decide⟩
theorem sqDiagArgs_cert : SqCert [.r0] (.block sqDiagArgs) := ⟨_, by taint_decide⟩
theorem diagLoop_cert : SqCert [.r0, .r12, .lr] diagLoop := ⟨_, by taint_decide⟩
theorem redInit_cert : SqCert [.r0] (.block redInit) := ⟨_, by taint_decide⟩
theorem redHeader_cert : SqCert [.r0] (.block redHeader) := ⟨_, by taint_decide⟩
theorem redArgs_cert : SqCert [.r0] (.block redArgs) := ⟨_, by taint_decide⟩
theorem redScalar_cert : SqCert [.r0] (.block redScalar) := ⟨_, by taint_decide⟩
theorem redLoad_cert : SqCert [.r2] (.block [.ldr .r2 .r2 80]) := ⟨_, by taint_decide⟩
theorem redCarry_cert : SqCert [.r0, .r2] (.block redCarry) := ⟨_, by taint_decide⟩

/-- The trace of code constant time for a relation on its entry states. -/
theorem segCTEnd {P : State → Prop} {c : Prog isa} {Pub : State → State → Prop}
    (ct : ConstantTime isa (fun _ => True) Pub c) (pub : ∀ s t, P s → P t → Pub s t) :
    RelCT isa (fun s t => P s ∧ P t) c (fun _ _ => True) :=
  fun s t tr1 tr2 u v h e1 e2 => ⟨ct s t tr1 tr2 u v trivial trivial (pub s t h.1 h.2) e1 e2, trivial⟩

/-- A phase's trace, and its states after by correctness. -/
theorem phase {P Q : State → Prop} {c : Prog isa} (ct : RelCT isa (fun s t => P s ∧ P t) c (fun _ _ => True))
    (wp : ∀ s, P s → WP isa c s Q) : RelCT isa (fun s t => P s ∧ P t) c (fun s t => Q s ∧ Q t) :=
  pair_posts ct wp

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

def DblReady (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (s : State) : Prop :=
  s.sp = sp0 ∧ ∃ m0 inv, DblInv m0 base size out a mod M n inv s

def ProdReady (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (s : State) : Prop :=
  s.sp = sp0 ∧ ∃ m0 inv, ProdInv m0 base size out a mod M n inv s

def RedReady (base : BitVec 32) (size out a mod M n : Nat) (sp0 : BitVec 32) (k : Nat) (s : State) : Prop :=
  s.sp = sp0 ∧ ∃ m0 inv, RedInv m0 base size out a mod M n inv k s

theorem sqDouble_ct :
    RelCT isa (fun s t => CrossReady base size out a mod M n sp0 (n - 1) s ∧
      CrossReady base size out a mod M n sp0 (n - 1) t) sqDouble
      (fun s t => DblReady base size out a mod M n sp0 s ∧ DblReady base size out a mod M n sp0 t) := by
  refine phase ?_ fun s ⟨sp, m0, inv, h⟩ =>
    WP.mono (sqDouble_ok s h) fun t ⟨ht, rt⟩ => ⟨rt.sp.trans sp, m0, inv, ht⟩
  let P2 := fun s : State => s.gpr .lr = BitVec.ofNat 32 (2 * n) ∧ s.gpr .r0 = base + BitVec.ofNat 32 (M + 24)
  have A := sqAnchor_ct (P := CrossReady base size out a mod M n sp0 (n - 1))
    (fun s ⟨sp, m0, inv, h⟩ => ⟨sp, m0, inv, h.env⟩)
    (fun s t ⟨sp, m0, inv, h⟩ mem rest => ⟨rest.sp.trans sp, m0, inv, h.of_mem mem rest⟩)
  have B : RelCT isa (fun s t => (CrossReady base size out a mod M n sp0 (n - 1) s ∧
      s.gpr .r0 = base + BitVec.ofNat 32 M) ∧ (CrossReady base size out a mod M n sp0 (n - 1) t ∧
      t.gpr .r0 = base + BitVec.ofNat 32 M)) (.block sqDoubleArgs) (fun s t => P2 s ∧ P2 t) := by
    refine seg sqDoubleArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨_, m0, inv, h⟩, p0⟩ := hs
      have := h.env.fits; have := h.env.nowrap
      exact WP.mono (sqDoubleArgs_ok s (M := M) (n := n) h.env.workspace (by omega_arith) (by omega_arith) p0 h.md.count)
        fun t ⟨plr, p0, _⟩ => ⟨plr, p0⟩
  have C : RelCT isa (fun s t => P2 s ∧ P2 t) shiftLeft (fun _ _ => True) :=
    segCTEnd shiftLeft_ct fun s t hs ht => ⟨hs.2.trans ht.2.symm, hs.1.trans ht.1.symm⟩
  unfold sqDouble
  exact A.seq (B.seq C)

theorem sqDiag_ct :
    RelCT isa (fun s t => DblReady base size out a mod M n sp0 s ∧ DblReady base size out a mod M n sp0 t) sqDiag
      (fun s t => ProdReady base size out a mod M n sp0 s ∧ ProdReady base size out a mod M n sp0 t) := by
  refine phase ?_ fun s ⟨sp, m0, inv, h⟩ =>
    WP.mono (sqDiagPhase_ok s h) fun t ⟨ht, rt⟩ => ⟨rt.sp.trans sp, m0, inv, ht⟩
  let P2 := fun s : State => s.gpr .r12 = base + BitVec.ofNat 32 a ∧ s.gpr .lr = BitVec.ofNat 32 n ∧
    s.gpr .r0 = base + BitVec.ofNat 32 (M + 24)
  have A := sqAnchor_ct (P := DblReady base size out a mod M n sp0)
    (fun s ⟨sp, m0, inv, h⟩ => ⟨sp, m0, inv, h.env⟩)
    (fun s t ⟨sp, m0, inv, h⟩ mem rest => ⟨rest.sp.trans sp, m0, inv,
      ⟨h.env.of_mem mem rest, by rw [mem]; exact h.md, by rw [mem]; exact h.value, by rw [mem]; exact h.top⟩⟩)
  have B : RelCT isa (fun s t => (DblReady base size out a mod M n sp0 s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M) ∧
      (DblReady base size out a mod M n sp0 t ∧ t.gpr .r0 = base + BitVec.ofNat 32 M)) (.block sqDiagArgs)
      (fun s t => P2 s ∧ P2 t) := by
    refine seg sqDiagArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨_, m0, inv, h⟩, p0⟩ := hs
      have := h.env.fits
      exact WP.mono (sqDiagArgs_ok s (M := M) (n := n) (a := a) h.env.workspace (by omega_using [this]) p0 h.md.count
        h.md.aPtr) fun t ⟨p12, plr, p0, _⟩ => ⟨p12, plr, p0⟩
  have C : RelCT isa (fun s t => P2 s ∧ P2 t) diagLoop (fun _ _ => True) :=
    segEnd diagLoop_cert fun s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.2.2.trans ht.2.2.symm
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
  unfold sqDiag
  exact A.seq (B.seq C)

theorem RedInv.of_mem {m0 : Mem} {inv : BitVec 32} {k : Nat} {s t : State} {rs : List Reg}
    (h : RedInv m0 base size out a mod M n inv k s) (mem : t.mem = s.mem) (rest : Rest rs s t) :
    RedInv m0 base size out a mod M n inv k t := by
  refine ⟨h.env.of_mem mem rest, ?_, h.index, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mem]
  exacts [h.md, h.cnt, h.tptr, h.value, h.low, h.top]

theorem sqReduce_ct :
    RelCT isa (fun s t => ProdReady base size out a mod M n sp0 s ∧ ProdReady base size out a mod M n sp0 t)
      sqReduce
      (fun s t => RedReady base size out a mod M n sp0 n s ∧ RedReady base size out a mod M n sp0 n t) := by
  -- The setup.
  have init : RelCT isa (fun s t => ProdReady base size out a mod M n sp0 s ∧ ProdReady base size out a mod M n sp0 t)
      (.seq sqAnchor (.block redInit))
      (fun s t => RedReady base size out a mod M n sp0 0 s ∧ RedReady base size out a mod M n sp0 0 t) := by
    refine phase ?_ fun s ⟨sp, m0, inv, h⟩ =>
      WP.mono (sqReduceInit_ok s h) fun t ⟨ht, rt⟩ => ⟨rt.sp.trans sp, m0, inv, ht⟩
    have A := sqAnchor_ct (P := ProdReady base size out a mod M n sp0)
      (fun s ⟨sp, m0, inv, h⟩ => ⟨sp, m0, inv, h.env⟩)
      (fun s t ⟨sp, m0, inv, h⟩ mem rest => ⟨rest.sp.trans sp, m0, inv,
        ⟨h.env.of_mem mem rest, by rw [mem]; exact h.md, by rw [mem]; exact h.value, by rw [mem]; exact h.top⟩⟩)
    exact A.seq (segEnd redInit_cert fun s t hs ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm)
  -- A round.
  have round (k : Nat) (hk : k < n) : RelCT isa (fun s t => RedReady base size out a mod M n sp0 k s ∧
      RedReady base size out a mod M n sp0 k t) redRound (fun _ _ => True) := by
    let o := M + 24 + 4 * k
    let H := SqHold base size out a mod M n sp0
    let R := RedReady base size out a mod M n sp0 k
    have rStable : ∀ s t : State, R s → t.mem = s.mem → ∀ {rs : List Reg}, Rest rs s t → R t :=
      fun s t ⟨sp, m0, inv, h⟩ mem _ rest => ⟨rest.sp.trans sp, m0, inv, h.of_mem mem rest⟩
    have rHold : ∀ s, R s → H s := fun s ⟨sp, m0, inv, h⟩ => ⟨sp, m0, inv, h.env⟩
    let P1 := fun s : State => R s ∧ s.gpr .r0 = base
    let P2 := fun s : State => R s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M ∧ s.gpr .r12 = base + BitVec.ofNat 32 mod
    let P3 := fun s : State => H s ∧ s.gpr .lr = BitVec.ofNat 32 n ∧ s.gpr .r0 = base + BitVec.ofNat 32 o ∧
      s.gpr .r12 = base + BitVec.ofNat 32 mod
    let P5 := fun s : State => H s ∧ s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * n)
    let P6 := fun s : State => P5 s ∧ s.gpr .r2 = base
    let P7 := fun s : State => P5 s ∧ s.gpr .r2 = base + BitVec.ofNat 32 M
    let P8 := fun s : State => H s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M
    have S1 : RelCT isa (fun s t => R s ∧ R t) (.block [.ldrSp .r0 0]) (fun s t => P1 s ∧ P1 t) :=
      segStack (fun s t hs ht => hs.1.trans ht.1.symm) fun s hs => by
        have hs' := hs
        obtain ⟨_, m0, inv, h⟩ := hs'
        exact WP.mono (sqBase_ok s h.env .r0) fun t ⟨p, mem, rest⟩ => ⟨rStable s t hs mem rest, p⟩
    have S2 : RelCT isa (fun s t => P1 s ∧ P1 t) (.block redHeader) (fun s t => P2 s ∧ P2 t) := by
      refine seg redHeader_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
      · obtain ⟨⟨sp, m0, inv, h⟩, p0⟩ := hs
        have := h.env.fits; have := h.env.header
        exact WP.mono (redHeader_ok s h.env.workspace (by omega_arith) p0 h.env.modNow h.env.invNow h.env.metaNow)
          fun t ⟨q12, _, q0, mem, rest⟩ => ⟨rStable s t ⟨sp, m0, inv, h⟩ mem rest, q0, q12⟩
    have S3 : RelCT isa (fun s t => P2 s ∧ P2 t) (.block redArgs) (fun s t => P3 s ∧ P3 t) := by
      refine seg redArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.1.trans ht.2.1.symm
      · obtain ⟨⟨sp, m0, inv, h⟩, p0, p12⟩ := hs
        have env := h.env
        have := env.fits; have := env.nowrap
        refine WP.mono (redArgs_ok s (P := o) env.workspace (by omega_arith) p0 h.md.count h.tptr) ?_
        rintro t ⟨glr, g0, mt, rt⟩
        have O := writeW32_outside s.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 4)) (by omega_arith)
        rw [← mt] at O
        exact ⟨⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside (O.mono (o' := M) (n' := 4 * (2 * n + 8))
          (by omega_arith) (by omega_arith)) (by simp)) rt⟩, glr, g0, by rw [rt.gpr .r12 (by simp)]; exact p12⟩
    have S4 : RelCT isa (fun s t => P3 s ∧ P3 t) (.block redScalar) (fun s t => P3 s ∧ P3 t) := by
      refine seg redScalar_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.2.1.trans ht.2.2.1.symm
      · obtain ⟨⟨sp, m0, inv, env⟩, glr, g0, g12⟩ := hs
        have := env.fits; have := env.count
        refine WP.mono (redScalar_ok s env.workspace (D := o) (by omega_arith) g0) ?_
        rintro t ⟨_, _, q0, mt, rt⟩
        exact ⟨⟨rt.sp.trans sp, m0, inv, env.of_mem mt rt⟩, by rw [rt.gpr .lr (by simp)]; exact glr,
          q0.trans g0, by rw [rt.gpr .r12 (by simp)]; exact g12⟩
    have S5 : RelCT isa (fun s t => P3 s ∧ P3 t) row (fun s t => P5 s ∧ P5 t) := by
      refine segCT row_ct (fun s t hs ht => ⟨hs.2.2.1.trans ht.2.2.1.symm, hs.2.2.2.trans ht.2.2.2.symm,
        hs.2.1.trans ht.2.1.symm⟩) (fun s hs => ?_)
      obtain ⟨⟨sp, m0, inv, env⟩, glr, g0, g12⟩ := hs
      have := env.fits; have := env.count; have := env.sepM; have := env.mFits
      have ctx : RowCtx s base size o mod n := ⟨env.nowrap, by omega_arith, by omega_arith, by omega_arith, env.workspace.writable⟩
      refine WP.mono (row_ok s ctx (by omega_arith) g0 g12 glr) fun t ri => ?_
      exact ⟨⟨ri.rest.sp.trans sp, m0, inv, env.next (Outs.of_outside (ri.outside.mono (o' := M)
        (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)) (by simp)) ri.rest⟩, ri.outPtr⟩
    have S6 : RelCT isa (fun s t => P5 s ∧ P5 t) (.block [.ldrSp .r2 0]) (fun s t => P6 s ∧ P6 t) :=
      segStack (fun s t hs ht => hs.1.1.trans ht.1.1.symm) fun s hs => by
        obtain ⟨⟨sp, m0, inv, env⟩, g0⟩ := hs
        refine WP.mono (sqBase_ok s env .r2) fun t ⟨p, mem, rest⟩ => ?_
        exact ⟨⟨⟨rest.sp.trans sp, m0, inv, env.of_mem mem rest⟩, by rw [rest.gpr .r0 (by simp)]; exact g0⟩, p⟩
    have S7 : RelCT isa (fun s t => P6 s ∧ P6 t) (.block [.ldr .r2 .r2 80]) (fun s t => P7 s ∧ P7 t) := by
      refine seg redLoad_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
      · obtain ⟨⟨⟨sp, m0, inv, env⟩, g0⟩, p2⟩ := hs
        have := env.fits; have := env.header
        refine wp_ldr (a := off (State.addr base) 80) (by decide) (sq_ea0 env.nowrap p2 (by omega_arith))
          (env.read (by omega_arith)) fun t ut => WP.block_nil ?_
        exact ⟨⟨⟨ut.sp.trans sp, m0, inv, env.of_mem ut.mem (ut.rest (ws := [.r2]) (by simp))⟩,
          by rw [ut.other .r0 (by decide)]; exact g0⟩, ut.gpr.trans env.metaNow⟩
    have S8 : RelCT isa (fun s t => P7 s ∧ P7 t) (.block redCarry) (fun s t => P8 s ∧ P8 t) := by
      refine seg redCarry_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.1.2.trans ht.1.2.symm
        · exact hs.2.trans ht.2.symm
      · obtain ⟨⟨⟨sp, m0, inv, env⟩, g0⟩, p2⟩ := hs
        have := env.fits; have := env.count; have := env.nowrap
        refine WP.mono (redCarry_ok s env.workspace (D := o + 4 * n) (M := M) (by omega_arith) (by omega_arith) g0 p2) ?_
        rintro t ⟨lo, hi, _, mt, q0, rt⟩
        have o1 := writeW32_outside s.mem (State.addr base) (d := o + 4 * n) lo (by omega_arith)
        have o2 := writeW32_outside (s.mem.writeW (off (State.addr base) (o + 4 * n)) lo) (State.addr base)
          (d := M + 12) hi (by omega_arith)
        rw [← mt] at o2
        exact ⟨⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside ((o1.mono (o' := M) (n' := 4 * (2 * n + 8))
          (by omega_arith) (by omega_arith)).trans (o2.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)))
          (by simp)) rt⟩, q0⟩
    have S9 : RelCT isa (fun s t => P8 s ∧ P8 t) (.block sqCount) (fun _ _ => True) :=
      segEnd sqCount_cert fun s t hs ht r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    unfold redRound
    exact S1.seq (S2.seq (S3.seq (S4.seq (S5.seq (S6.seq (S7.seq (S8.seq S9)))))))
  -- The rounds.
  let I := fun k s t => ∃ i, i + k = n ∧ 0 < k ∧
    RedReady base size out a mod M n sp0 i s ∧ RedReady base size out a mod M n sp0 i t
  have step : ∀ k, RelCT isa (I k) redRound fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → RedReady base size out a mod M n sp0 n s ∧
        RedReady base size out a mod M n sp0 n t) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k
    apply RelCT.exists_
    intro i
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨hik, hk, hs, ht⟩ := h
    have hi : i < n := by omega_arith
    have ready (x : State) (hx : RedReady base size out a mod M n sp0 i x) :
        WP isa redRound x fun y => RedReady base size out a mod M n sp0 (i + 1) y ∧ y.z = decide (i + 1 = n) := by
      obtain ⟨sp, m0, inv, hx⟩ := hx
      exact WP.mono (redRound_ok x hx hi) fun y ⟨hy, z, r⟩ => ⟨⟨r.sp.trans sp, m0, inv, hy⟩, z⟩
    obtain ⟨trace, _, ⟨hu, zu⟩, ⟨hv, zv⟩⟩ :=
      (round i hi).wp (fun x y h => ⟨ready x h.1, ready y h.2⟩) s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    refine ⟨trace, ?_, fun branch => ?_, fun branch => ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · have : i + 1 = n := by
        change some (!u.z) = some false at branch
        by_contra ne
        simp only [zu, ne, decide_false, Bool.not_false] at branch
        cases branch
      rw [this] at hu hv
      exact ⟨hu, hv⟩
    · have ne : i + 1 ≠ n := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, hu, hv⟩
  have rounds : RelCT isa (fun s t => RedReady base size out a mod M n sp0 0 s ∧
      RedReady base size out a mod M n sp0 0 t) redRounds
      (fun s t => RedReady base size out a mod M n sp0 n s ∧ RedReady base size out a mod M n sp0 n t) := by
    apply (RelCT.loop I step n).mono _ (fun _ _ h => h)
    intro s t h
    obtain ⟨_, m0, inv, hi⟩ := h.1
    have := hi.env.count
    exact ⟨0, by omega_arith, by omega_arith, h⟩
  unfold sqReduce
  exact init.seq rounds

end

end VG.Proof.Bignum.Arm

end

end

/-! # The whole Montgomery square leaks only the width, as `montOp` does -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sqFinishHeader_cert : SqCert [.r0] (.block sqFinishHeader) := ⟨_, by taint_decide⟩
theorem sqFinishLoad_cert : SqCert [.r0] (.block sqFinishLoad) := ⟨_, by taint_decide⟩
theorem sqFinishArgs_cert : SqCert [.r0, .r7] (.block sqFinishArgs) := ⟨_, by taint_decide⟩

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

theorem sqFinish_ct :
    RelCT isa (fun s t => RedReady base size out a mod M n sp0 n s ∧ RedReady base size out a mod M n sp0 n t)
      sqFinish (fun _ _ => True) := by
  let R := RedReady base size out a mod M n sp0 n
  have rStable : ∀ s t : State, R s → t.mem = s.mem → ∀ {rs : List Reg}, Rest rs s t → R t :=
    fun s t ⟨sp, m0, inv, h⟩ mem _ rest => ⟨rest.sp.trans sp, m0, inv, h.of_mem mem rest⟩
  let P1 := fun s : State => R s ∧ s.gpr .r0 = base
  let P2 := fun s : State => R s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M ∧ s.gpr .r12 = base + BitVec.ofNat 32 mod
  let P3 := fun s : State => R s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M ∧
    s.gpr .r12 = base + BitVec.ofNat 32 mod ∧ s.gpr .r7 = BitVec.ofNat 32 n ∧ s.gpr .r9 = base + BitVec.ofNat 32 out
  let P4 := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 M ∧
    s.gpr .r12 = base + BitVec.ofNat 32 mod ∧ s.gpr .r7 = BitVec.ofNat 32 n ∧
    s.gpr .r9 = base + BitVec.ofNat 32 out ∧ s.gpr .r10 = base + BitVec.ofNat 32 (M + 24 + 4 * n) ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have S1 : RelCT isa (fun s t => R s ∧ R t) (.block [.ldrSp .r0 0]) (fun s t => P1 s ∧ P1 t) :=
    segStack (fun s t hs ht => hs.1.trans ht.1.symm) fun s hs => by
      have hs' := hs
      obtain ⟨_, m0, inv, h⟩ := hs'
      exact WP.mono (sqBase_ok s h.env .r0) fun t ⟨p, mem, rest⟩ => ⟨rStable s t hs mem rest, p⟩
  have S2 : RelCT isa (fun s t => P1 s ∧ P1 t) (.block sqFinishHeader) (fun s t => P2 s ∧ P2 t) := by
    refine seg sqFinishHeader_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨sp, m0, inv, h⟩, p0⟩ := hs
      have := h.env.fits; have := h.env.header
      exact WP.mono (sqFinishHeader_ok s h.env.workspace (by omega_arith) p0 h.env.modNow h.env.metaNow)
        fun t ⟨q12, q0, mem, rest⟩ => ⟨rStable s t ⟨sp, m0, inv, h⟩ mem rest, q0, q12⟩
  have S3 : RelCT isa (fun s t => P2 s ∧ P2 t) (.block sqFinishLoad) (fun s t => P3 s ∧ P3 t) := by
    refine seg sqFinishLoad_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.1.trans ht.2.1.symm
    · obtain ⟨⟨sp, m0, inv, h⟩, p0, p12⟩ := hs
      have := h.env.fits
      exact WP.mono (sqFinishLoad_ok s (n := n) (out := out) h.env.workspace (by omega_using [this]) p0 h.md.count h.md.outPtr)
        fun t ⟨g7, g9, _, g0, mem, rest⟩ => ⟨rStable s t ⟨sp, m0, inv, h⟩ mem rest, g0.trans p0,
          by rw [rest.gpr .r12 (by simp)]; exact p12, g7, g9⟩
  have S4 : RelCT isa (fun s t => P3 s ∧ P3 t) (.block sqFinishArgs) (fun s t => P4 s ∧ P4 t) := by
    refine seg sqFinishArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
    · obtain ⟨⟨_, m0, inv, h⟩, p0, p12, p7, p9⟩ := hs
      have := h.env.fits
      exact WP.mono (sqFinishArgs_ok s h.env.workspace (by omega_using [this]) p0 p7)
        fun t ⟨_, g10, glr, _, rest⟩ => ⟨by rw [rest.gpr .r0 (by simp)]; exact p0,
          by rw [rest.gpr .r12 (by simp)]; exact p12, by rw [rest.gpr .r7 (by simp)]; exact p7,
          by rw [rest.gpr .r9 (by simp)]; exact p9, g10, glr⟩
  have S5 : RelCT isa (fun s t => P4 s ∧ P4 t) csub (fun _ _ => True) :=
    segCTEnd csub_ct fun s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
      · exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.2.2.2.trans ht.2.2.2.2.2.symm
  unfold sqFinish
  exact S1.seq (S2.seq (S3.seq (S4.seq S5)))

theorem sqBody_ct :
    RelCT isa (fun s t => SqStart base size out a mod M n sp0 s ∧ SqStart base size out a mod M n sp0 t)
      sqBody (fun _ _ => True) := by
  unfold sqBody
  exact sqInit_ct.seq (crossRows_ct.seq (sqDouble_ct.seq (sqDiag_ct.seq (sqReduce_ct.seq sqFinish_ct))))

end

/-- `squareBody`'s entry: `montFnBody`'s, with the workspace pointer at `sp`. -/
structure SqFnReady (base : BitVec 32) (len w o a : Nat) (s : State) : Prop where
  body : FnBodyReady base len w o a a s
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem squareBases_ready {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a)
    (s : State) (h : SqFnReady base len w o a s) :
    WP isa (.block MontFn.bases) s
      (SqStart base (8 * len) (arrAt w o) (arrAt w a) (arrAt w 0) (arrAt w 2) (2 * w) s.sp) := by
  obtain ⟨hb, stackRead, stackSep, saved⟩ := h
  obtain ⟨ws, layout, width, ptr, po, pa, pb, inverse, operand⟩ := hb
  subst width
  have hw : 2 ≤ wOf s.mem (State.addr base) := layout.1
  have fits : arrAt (wOf s.mem (State.addr base)) 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega_using [fits]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 ha.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  have env := sqEnv_of_layout s u ws layout ho ha header
    (native_inverse s.mem (State.addr base) (by omega_using [hw]) inverse) operand stackRead stackSep saved mem keep
  exact ⟨keep.sp, ⟨_, env⟩, regs.accPtr, regs.count, regs.aPtr, regs.outPtr⟩

theorem squareBody_ct {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a) :
    RelCT isa (fun s t => s.sp = t.sp ∧ SqFnReady base len w o a s ∧ SqFnReady base len w o a t)
      squareBody (fun _ _ => True) := by
  have family : ∀ sp0 : BitVec 32, RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
      (SqFnReady base len w o a t ∧ t.sp = sp0)) squareBody (fun _ _ => True) := by
    intro sp0
    have ct : RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
        (SqFnReady base len w o a t ∧ t.sp = sp0)) (.block MontFn.bases) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
      intro s t h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.1.1.body.ptr.trans h.2.1.body.ptr.symm
      · exact h.1.1.body.outIndex.trans h.2.1.body.outIndex.symm
      · exact h.1.1.body.aIndex.trans h.2.1.body.aIndex.symm
      · exact h.1.1.body.bIndex.trans h.2.1.body.bIndex.symm
    have wp (s : State) (h : SqFnReady base len w o a s ∧ s.sp = sp0) :
        WP isa (.block MontFn.bases) s
          (SqStart base (8 * len) (arrAt w o) (arrAt w a) (arrAt w 0) (arrAt w 2) (2 * w) sp0) :=
      h.2 ▸ squareBases_ready ho ha s h.1
    unfold squareBody
    exact (pair_posts ct wp).seq sqBody_ct
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v ⟨⟨h.2.1, rfl⟩, h.2.2, h.1.symm⟩ e1 e2

theorem squareArgs_ready (s : State) {base : BitVec 32} {len w o a : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a)
    (operand : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) :
    WP isa (.block (montOpArgs o a a)) s (SqFnReady base len w o a) := by
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 ha.1) ?_
  rintro t ⟨po, pa, pb, mem, rest⟩
  refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr, po, pa, pb, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [mem]; exact h.inverse
  · rw [mem]; exact operand
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [rest.sp, mem]; exact h.saved

theorem squareOp_ct {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w a < numAt t.mem (State.addr base) w 0) ∧
        s.sp = t.sp)
      (squareOp o a) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w a < numAt t.mem (State.addr base) w 0) ∧
      s.sp = t.sp
  have args : RelCT isa P (.block (montOpArgs o a a)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨squareArgs_ready s h.1.1 ho ha h.1.2, squareArgs_ready t h.2.1.1 ho ha h.2.1.2⟩)
  have body := relCT_keep_sp (squareBody_ct (base := base) (len := len) (w := w) ho ha) (fun _ _ h => h.1)
  exact (ready.seq (body.seq (loadStack_ct .r0 0))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
