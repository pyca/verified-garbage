module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareCrossCT
public import VerifiedGarbage.Proof.Bignum.Arm.SquareReduce
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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

theorem holdStable : ∀ s t : State, SqHold base size out a mod M n sp0 s → t.mem = s.mem →
    Rest [.r0] s t → SqHold base size out a mod M n sp0 t :=
  fun _ _ ⟨sp, m0, inv, env⟩ mem rest => ⟨rest.sp.trans sp, m0, inv, env.of_mem mem rest⟩

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
      exact WP.mono (sqDoubleArgs_ok s (M := M) (n := n) h.env.workspace (by omega) (by omega) p0 h.md.count)
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
      exact WP.mono (sqDiagArgs_ok s (M := M) (n := n) (a := a) h.env.workspace (by omega) p0 h.md.count
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
        exact WP.mono (redHeader_ok s h.env.workspace (by omega) p0 h.env.modNow h.env.invNow h.env.metaNow)
          fun t ⟨q12, _, q0, mem, rest⟩ => ⟨rStable s t ⟨sp, m0, inv, h⟩ mem rest, q0, q12⟩
    have S3 : RelCT isa (fun s t => P2 s ∧ P2 t) (.block redArgs) (fun s t => P3 s ∧ P3 t) := by
      refine seg redArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.1.trans ht.2.1.symm
      · obtain ⟨⟨sp, m0, inv, h⟩, p0, p12⟩ := hs
        have env := h.env
        have := env.fits; have := env.nowrap
        refine WP.mono (redArgs_ok s (P := o) env.workspace (by omega) p0 h.md.count h.tptr) ?_
        rintro t ⟨glr, g0, mt, rt⟩
        have O := writeW32_outside s.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 4)) (by omega)
        rw [← mt] at O
        exact ⟨⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside (O.mono (o' := M) (n' := 4 * (2 * n + 8))
          (by omega) (by omega)) (by simp)) rt⟩, glr, g0, by rw [rt.gpr .r12 (by simp)]; exact p12⟩
    have S4 : RelCT isa (fun s t => P3 s ∧ P3 t) (.block redScalar) (fun s t => P3 s ∧ P3 t) := by
      refine seg redScalar_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.2.1.trans ht.2.2.1.symm
      · obtain ⟨⟨sp, m0, inv, env⟩, glr, g0, g12⟩ := hs
        have := env.fits; have := env.count
        refine WP.mono (redScalar_ok s env.workspace (D := o) (by omega) g0) ?_
        rintro t ⟨_, _, q0, mt, rt⟩
        exact ⟨⟨rt.sp.trans sp, m0, inv, env.of_mem mt rt⟩, by rw [rt.gpr .lr (by simp)]; exact glr,
          q0.trans g0, by rw [rt.gpr .r12 (by simp)]; exact g12⟩
    have S5 : RelCT isa (fun s t => P3 s ∧ P3 t) row (fun s t => P5 s ∧ P5 t) := by
      refine segCT row_ct (fun s t hs ht => ⟨hs.2.2.1.trans ht.2.2.1.symm, hs.2.2.2.trans ht.2.2.2.symm,
        hs.2.1.trans ht.2.1.symm⟩) (fun s hs => ?_)
      obtain ⟨⟨sp, m0, inv, env⟩, glr, g0, g12⟩ := hs
      have := env.fits; have := env.count; have := env.sepM; have := env.mFits
      have ctx : RowCtx s base size o mod n := ⟨env.nowrap, by omega, by omega, by omega, env.workspace.writable⟩
      refine WP.mono (row_ok s ctx (by omega) g0 g12 glr) fun t ri => ?_
      exact ⟨⟨ri.rest.sp.trans sp, m0, inv, env.next (Outs.of_outside (ri.outside.mono (o' := M)
        (n' := 4 * (2 * n + 8)) (by omega) (by omega)) (by simp)) ri.rest⟩, ri.outPtr⟩
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
        refine wp_ldr (a := off (State.addr base) 80) (by decide) (sq_ea0 env.nowrap p2 (by omega))
          (env.read (by omega)) fun t ut => WP.block_nil ?_
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
        refine WP.mono (redCarry_ok s env.workspace (D := o + 4 * n) (M := M) (by omega) (by omega) g0 p2) ?_
        rintro t ⟨lo, hi, _, mt, q0, rt⟩
        have o1 := writeW32_outside s.mem (State.addr base) (d := o + 4 * n) lo (by omega)
        have o2 := writeW32_outside (s.mem.writeW (off (State.addr base) (o + 4 * n)) lo) (State.addr base)
          (d := M + 12) hi (by omega)
        rw [← mt] at o2
        exact ⟨⟨rt.sp.trans sp, m0, inv, env.next (Outs.of_outside ((o1.mono (o' := M) (n' := 4 * (2 * n + 8))
          (by omega) (by omega)).trans (o2.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega)))
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
    have hi : i < n := by omega
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
      exact ⟨k - 1, by omega, i + 1, by omega, by omega, hu, hv⟩
  have rounds : RelCT isa (fun s t => RedReady base size out a mod M n sp0 0 s ∧
      RedReady base size out a mod M n sp0 0 t) redRounds
      (fun s t => RedReady base size out a mod M n sp0 n s ∧ RedReady base size out a mod M n sp0 n t) := by
    apply (RelCT.loop I step n).mono _ (fun _ _ h => h)
    intro s t h
    obtain ⟨_, m0, inv, hi⟩ := h.1
    have := hi.env.count
    exact ⟨0, by omega, by omega, h⟩
  unfold sqReduce
  exact init.seq rounds

end

end VG.Proof.Bignum.Arm
