module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareCTBase
public import VerifiedGarbage.Proof.Bignum.Arm.SquareInit
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Square
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowBody
import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

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
      refine WP.mono (crossArgs_ok s (A := a + 4 * k) (C := len) (P := o) env.workspace (by omega) p0 h.next
        h.cnt h.tptr) ?_
      rintro t ⟨g2, g12, glr, g0, _, mt, rt⟩
      have o1 := writeW32_outside s.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 8)) (by omega)
      have o2 := writeW32_outside (s.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (o + 8)))
        (State.addr base) (d := M + 12) (base + BitVec.ofNat 32 (a + 4 * k + 4)) (by omega)
      rw [← mt] at o2
      have O : Outside (State.addr base) M (4 * (2 * n + 8)) s.mem t.mem :=
        (o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))
      exact ⟨⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside O (by simp)) rt⟩, g2, g12, glr, g0⟩
  have C : RelCT isa (fun s t => P2 s ∧ P2 t) (.block crossScalar) (fun s t => P3 s ∧ P3 t) := by
    refine seg crossScalar_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.1.trans ht.2.1.symm
    · obtain ⟨⟨sp, m0, inv, env⟩, g2, g12, glr, g0⟩ := hs
      have := env.aFits; have := env.count
      refine WP.mono (crossScalar_ok s env.workspace (by omega) g2) ?_
      rintro t ⟨_, mt, rt⟩
      exact ⟨⟨rt.sp.trans sp, m0, inv, env.of_mem mt rt⟩, by rw [rt.gpr .r12 (by simp)]; exact g12,
        by rw [rt.gpr .lr (by simp)]; exact glr, by rw [rt.gpr .r0 (by simp)]; exact g0⟩
  have D : RelCT isa (fun s t => P3 s ∧ P3 t) row (fun s t => P4 s ∧ P4 t) := by
    refine segCT row_ct (fun s t hs ht => ⟨hs.2.2.2.trans ht.2.2.2.symm, hs.2.1.trans ht.2.1.symm,
      hs.2.2.1.trans ht.2.2.1.symm⟩) (fun s hs => ?_)
    obtain ⟨⟨sp, m0, inv, env⟩, g12, glr, g0⟩ := hs
    have := env.aFits; have := env.count; have := env.fits; have := env.sepA
    have ctx : RowCtx s base size o (a + 4 * (k + 1)) len :=
      ⟨env.nowrap, by omega, by omega, by omega, env.workspace.writable⟩
    refine WP.mono (row_ok s ctx (by omega) g0 (by rw [g12, show a + 4 * k + 4 = a + 4 * (k + 1) by omega]) glr) ?_
    intro t ri
    exact ⟨⟨ri.rest.sp.trans sp, m0, inv, env.next (Outs.of_outside (ri.outside.mono (o' := M)
      (n' := 4 * (2 * n + 8)) (by omega) (by omega)) (by simp)) ri.rest⟩, ri.outPtr⟩
  have E : RelCT isa (fun s t => P4 s ∧ P4 t) (.block crossCarry) (fun s t => P5 s ∧ P5 t) := by
    refine seg crossCarry_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨sp, m0, inv, env⟩, g0⟩ := hs
      have := env.count; have := env.fits; have := env.nowrap
      refine WP.mono (crossCarry_ok s env.workspace (by omega) g0) ?_
      rintro t ⟨mt, rt⟩
      have O := writeW32_outside s.mem (State.addr base) (d := o + 4 * len) (s.gpr .r11) (by omega)
      rw [← mt] at O
      exact ⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside (O.mono (o' := M) (n' := 4 * (2 * n + 8))
        (by omega) (by omega)) (by simp)) rt⟩
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
      omega
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
      rw [show n - 1 = i + 1 by omega]
      exact ⟨hu, hv⟩
    · have ne : i + 2 ≠ n := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega, i + 1, by omega, by omega, hu, hv⟩
  apply (RelCT.loop I step (n - 1)).mono _ (fun _ _ h => h)
  intro s t h
  obtain ⟨_, m0, inv, hi⟩ := h.1
  have := hi.env.count
  exact ⟨0, by omega, by omega, h⟩

end

end VG.Proof.Bignum.Arm
