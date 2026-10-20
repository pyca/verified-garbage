module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Correct
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Correct
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeSized
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeSized
import VerifiedGarbage.Proof.Framework.Omega

/-! # The trace of precomputed public RSA at a run-time width, from the values to the result

The copies and checks, the failure, `applyPrefix` and the output are checked
by the taint analysis (`τA`), the exponentiation related by
`exponentiate_relCT` from the same exponent, on runs narrowed to the output and the working space
(`sized_relCT`); the checks' outcome agrees as the values of `pre` do. The
runs from the states themselves leak the same traces (`sizedNarrow_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What `sized`'s narrowed runs need of a run. -/
def SIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  RtIn base bytes len args s ∧ PreIn base bytes len args s ∧ Room base bytes args s ∧ ArgsOk s ∧ s.gpr .esp = sp

/-- The modulus `pre` holds. -/
abbrev preM (len : Nat) (args : Nat → BitVec 32) (s : State) : Nat := val32 s.mem (byteAddr (args 2)) 0 (nw len)

/-- The `R² mod M` `pre` holds. -/
abbrev preT (len : Nat) (args : Nat → BitVec 32) (s : State) : Nat :=
  val32 s.mem (byteAddr (args 2)) (wb len) (nw len)

theorem SIn.agree {sp : BitVec 32} {s t : State} (S₁ : SIn base bytes len args sp s)
    (S₂ : SIn base bytes len args sp t) : VG.X86.Taint.Agree τA s t :=
  agreeA S₁.1 S₂.1 S₁.2.2.2.1 S₂.2.2.2.1 (S₁.2.2.2.2.trans S₂.2.2.2.2.symm)

theorem SIn.keep {sp : BitVec 32} {s t : State} (S : SIn base bytes len args sp s) {rs : List Reg}
    (K : Keeps rs s t) (di : .edi ∉ rs) (sp' : .esp ∉ rs) (O : Outside base 0 bytes s.mem t.mem) :
    SIn base bytes len args sp t :=
  ⟨S.1.keep K di sp' O, S.2.1.keep K, S.2.2.1.keep K sp', S.2.2.2.1.keep K sp', (K.1 _ sp').trans S.2.2.2.2⟩

/-- After the copies and the checks, from `σ`. -/
def KeyOut (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (σ s : State) : Prop :=
  SIn base bytes len args sp s ∧ s.zf = some (!Accepted (preM len args σ) (preT len args σ)) ∧
    val32 s.mem base (numAt len 0) (nw len) = preM len args σ ∧
    val32 s.mem base (numAt len 4) (nw len) = preT len args σ ∧ val32 s.mem base (numAt len 3) (nw len) = 1 ∧
    val32 s.mem base 128 2 = val32 σ.mem base 128 2

theorem keyChecks_ok {sp : BitVec 32} {σ : State} (S : SIn base bytes len args sp σ) :
    WP isa (.seq importKey checks) σ (KeyOut base bytes len args sp σ) := by
  have h := S.1
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f7 := h.fits (j := 7) (by decide)
  have wl := wb_ge h.lower
  refine WP.seq (WP.mono (importKey_ok h S.2.1) fun u ⟨V0, V4, V3, O₁, K₁⟩ => ?_)
  have O₁' : Outside base 0 bytes σ.mem u.mem := O₁.mono (by simp only [numOff]; omega) (by
    have := (h.fits (j := 5) (by decide)).2; simp only [numAt, numOff] at this ⊢; omega)
  have Su := S.keep K₁ (by decide) (by decide) O₁'
  refine WP.mono (checks_ok Su.1 V3) fun v ⟨Z, O₂, K₂⟩ => ?_
  simp only [checkOffset] at O₂
  have O₂' : Outside base 0 bytes u.mem v.mem := O₂.mono (by omega) (by
    have := (h.fits (j := 0) (by decide)).1; simp only [numAt, numOff] at this; omega)
  have uv : ∀ j, j ≤ 4 → val32 v.mem base (numAt len j) (nw len) = val32 u.mem base (numAt len j) (nw len) :=
    fun j hj => O₂.val32 (.inr (by simp only [numAt, numOff]; omega)) (by
      have := (h.fits (j := j) (by omega)).1; simp only [nw, wb] at *; omega)
  exact ⟨Su.keep K₂ (by decide) (by decide) O₂', by rw [Z, V0, V4], by rw [uv 0 (by decide), V0],
    by rw [uv 4 (by decide), V4], by rw [uv 3 (by decide), V3],
    by rw [O₂.val32 (.inl (by decide)) (by decide), O₁.val32 (.inl (by simp only [numOff]; omega)) (by decide)]⟩

theorem sized_relCT (hbytes : bytes = (args 9).toNat * 8) (sp : BitVec 32) :
    RelCT isa (fun s t => SIn base bytes len args sp s ∧ SIn base bytes len args sp t ∧
      preM len args s = preM len args t ∧ preT len args s = preT len args t ∧
      val32 s.mem base 128 2 = val32 t.mem base 128 2) PrecomputedRt.sized
      fun _ _ => True := by
  unfold PrecomputedRt.sized
  apply VG.RelCT.assoc
  refine VG.RelCT.seq ((RelCT.taint (A := taint) τA (fun _ _ ⟨S₁, S₂, _⟩ => S₁.agree S₂)
    (hc := VG.Taint.hintOf taint τA (.seq importKey checks)) (by taint_decide)).wpDep
    (F := KeyOut base bytes len args sp) fun _ _ ⟨S₁, S₂, _⟩ => ⟨keyChecks_ok S₁, keyChecks_ok S₂⟩) ?_
  refine VG.RelCT.ite (fun s t ⟨_, σ₁, σ₂, ⟨_, _, eM, eT, _⟩, F₁, F₂⟩ => by
    show s.zf = t.zf; rw [F₁.2.1, F₂.2.1, eM, eT]) ?_ ?_
  · exact RelCT.taint (A := taint) τA (fun _ _ ⟨⟨_, _, _, _, F₁, F₂⟩, _⟩ => F₁.1.agree F₂.1)
      (hc := VG.Taint.hintOf taint τA PublicFn.failure) (by taint_decide)
  · unfold applyInput
    have pre : ∀ k s, (∃ σ, KeyOut base bytes len args sp σ s ∧ Accepted (preM len args σ) (preT len args σ) = true) ∧
        val32 s.mem base 128 2 = k → WP isa applyPrefix s fun u => ∃ M, ExpIn base bytes len args sp M k u := by
      rintro k s ⟨⟨σ, ⟨⟨h, _, X, A, sp₀⟩, _, N, T, O, _⟩, acc⟩, W⟩
      simp only [Accepted, Bool.and_eq_true, decide_eq_true_eq] at acc
      obtain ⟨⟨hM1, hTM⟩, odd⟩ := acc
      refine WP.mono (applyPrefix_ok h X.room X.top N odd W rfl) fun u ⟨E, _, T₄, One₄, _, W₄, _, K⟩ =>
        ⟨_, E, A.keep K (by decide), (K.1 _ (by decide)).trans sp₀, by rw [One₄, O]; exact hM1,
          by rw [T₄, T]; exact hTM, W₄⟩
    have core : ∀ k, RelCT isa (Both fun s => (∃ σ, KeyOut base bytes len args sp σ s ∧
        Accepted (preM len args σ) (preT len args σ) = true) ∧ val32 s.mem base 128 2 = k)
        (.seq applyPrefix (.seq exponentiate (.seq maskOut write))) fun _ _ => True := fun k =>
      VG.RelCT.seq (taint_both (fun _ _ ⟨⟨_, K₁, _⟩, _⟩ ⟨⟨_, K₂, _⟩, _⟩ => K₁.1.agree K₂.1)
        (VG.Taint.hintOf taint τA applyPrefix) (by taint_decide) (pre k))
        (VG.RelCT.seq (exponentiate_relCT hbytes sp k)
          (RelCT.taint (A := taint) τA (fun _ _ ⟨⟨_, E₁, A₁, sp₁⟩, ⟨_, E₂, A₂, sp₂⟩⟩ =>
            agreeA E₁.pi E₂.pi A₁ A₂ (sp₁.trans sp₂.symm)) (hc := VG.Taint.hintOf taint τA (.seq maskOut write))
            (by taint_decide)))
    rintro s t tr ur sf tf ⟨⟨_, σ₁, σ₂, ⟨_, _, eM, eT, eE⟩, F₁, F₂⟩, ev⟩ E F
    have z : s.zf = some false := ev
    rw [F₁.2.1] at z
    have acc : Accepted (preM len args σ₁) (preT len args σ₁) = true := by simpa using z
    exact core (val32 s.mem base 128 2) _ _ _ _ _ _ ⟨⟨⟨σ₁, F₁, acc⟩, rfl⟩,
      ⟨⟨σ₂, F₂, by rw [← eM, ← eT]; exact acc⟩, by rw [F₂.2.2.2.2.2, F₁.2.2.2.2.2, eE]⟩⟩ E F

/-- The permissions of `sized`'s narrowed runs: everything readable, the output and the working space
writable. -/
abbrev narrowW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : List Region :=
  [⟨byteAddr (args 0), len⟩, ⟨base, bytes⟩]

/-- The exponent saved at 128 and valid. -/
def ExpAt (base : Addr) (args : Nat → BitVec 32) (s : State) : Prop :=
  val32 s.mem base 128 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat) ∧
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true

/-- What the runs of `sized` from the states themselves need: what the narrowed runs need, the arguments
apart from the output and the working space. -/
def SAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PrecomputedInputs base bytes len args s ∧ Room base bytes args s ∧ s.gpr .esp = sp ∧ ExpAt base args s ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨base, bytes⟩

theorem narrow_inputs {sp : BitVec 32} {s : State} (S : SAt base bytes len args sp s) :
    PrecomputedInputs base bytes len args (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  obtain ⟨h, -, -, -, -, -⟩ := S
  refine ⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper, h.space,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.preLen, h.inLen,
    h.ePositive, h.eBound, h.outFit, h.preFit, h.eFit, h.inFit,
    ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, ?_, ?_, ?_, h.outApart, h.preApart, h.eApart,
    h.inApart⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.preRead; exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.eRead; exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inRead; exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem narrow_in {sp : BitVec 32} {s : State} (S : SAt base bytes len args sp s) :
    SIn base bytes len args sp (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  have h := narrow_inputs S
  obtain ⟨-, X, sp₀, -, Do, Ds⟩ := S
  refine ⟨h.rt, h.pre, ⟨X.hbase, X.hbytes, X.room, X.top⟩, ⟨X.top, ?_⟩, sp₀⟩
  intro r hr
  simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Do
  · exact Ds

theorem sizedNarrow_relCT (hbytes : bytes = (args 9).toNat * 8)
    (sp : BitVec 32) : RelCT isa (fun s t => SAt base bytes len args sp s ∧ SAt base bytes len args sp t ∧
      preM len args s = preM len args t ∧ preT len args s = preT len args t ∧
      val32 s.mem base 128 2 = val32 t.mem base 128 2) PrecomputedRt.sized
      fun _ _ => True := by
  refine relCT_narrow (fun s => s.rd ++ s.wr) (fun _ => narrowW base bytes len args)
    (fun s₁ s₂ ⟨S₁, S₂, eM, eT, eE⟩ => ?_) (sized_relCT (base := base) (len := len) hbytes sp)
  have cov : ∀ {s : State}, SAt base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, SAt base bytes len args sp s →
      ∃ F, WP isa PrecomputedRt.sized (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F := by
    intro s S
    have h := narrow_inputs S
    obtain ⟨-, X, -, ⟨E, V⟩, -⟩ := S
    exact ⟨_, sized_ok h ⟨X.hbase, X.hbytes, X.room, X.top⟩ E V⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    narrow_in S₁, narrow_in S₂, eM, eT, eE⟩

end

end VG.Proof.Bignum.X86.PrecomputedRt
