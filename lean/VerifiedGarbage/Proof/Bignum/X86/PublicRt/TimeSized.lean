module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
public import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega

/-! # The trace of public RSA at a run-time width, from the inputs to the result

`prepare` and the result's masking and output are checked by the taint
analysis (`τA`), the exponentiation related by `exponentiate_relCT`, from
what each run's correctness gives (`prepare_ok`), on states whose
permissions are narrowed to the output and the working space
(`sized_relCT`); the runs from the states themselves leak the same traces
(`sizedNarrow_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What the exponentiation needs of a run: `Env`, the arguments apart, `esp`, one and `R² mod M` below `M`. -/
def ExpIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (M : Nat) (s : State) : Prop :=
  Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp ∧
    val32 s.mem base (numAt len 3) (nw len) < M ∧ val32 s.mem base (numAt len 4) (nw len) < M

/-- After `R mod M`: the base below `M` instead of `R mod M`. -/
def ExpIn₁ (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (M : Nat) (s : State) : Prop :=
  Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp ∧
    val32 s.mem base (numAt len 1) (nw len) < M ∧ val32 s.mem base (numAt len 3) (nw len) < M

/-- After the exponentiation. -/
def ExpOut (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  ∃ M, Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp

theorem exponentiate_relCT (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (sp : BitVec 32) :
    RelCT isa (Both fun s => ∃ M, ExpIn base bytes len args sp M s) exponentiate
      (Both (ExpOut base bytes len args sp)) := by
  unfold exponentiate
  refine VG.RelCT.seq (relCT_both (F := fun s => ∃ M, ExpIn base bytes len args sp M s)
    ((mul_relCT hbytes sp (o := 2) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, X₁⟩, ⟨_, X₂⟩⟩ =>
        ⟨X₁.2.2.1, X₂.2.2.1, ⟨⟨_, X₁.1, X₁.2.2.2.1⟩, X₁.2.1⟩, ⟨⟨_, X₂.1, X₂.2.2.2.1⟩, X₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, E, A, sp₀, O, T⟩ => WP.mono (mulKeep_ok E A hbytes (o := 2) (a := 4) (b := 3) (by decide)
      (by decide) (by decide) (by decide) O) fun _ ⟨Eu, Au, K, _, V, _⟩ => ⟨M, Eu, Au, (K.1 _ (by decide)).trans sp₀,
        by rw [V 3 (by decide) (by decide)]; exact O, by rw [V 4 (by decide) (by decide)]; exact T⟩) ?_
  refine VG.RelCT.seq (relCT_both (F := fun s => ∃ M, ExpIn₁ base bytes len args sp M s)
    ((mul_relCT hbytes sp (o := 1) (a := 1) (b := 4) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, X₁⟩, ⟨_, X₂⟩⟩ =>
        ⟨X₁.2.2.1, X₂.2.2.1, ⟨⟨_, X₁.1, X₁.2.2.2.2⟩, X₁.2.1⟩, ⟨⟨_, X₂.1, X₂.2.2.2.2⟩, X₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, E, A, sp₀, O, T⟩ => WP.mono (mulKeep_ok E A hbytes (o := 1) (a := 1) (b := 4) (by decide)
      (by decide) (by decide) (by decide) T) fun _ ⟨Eu, Au, K, L, V, _⟩ => ⟨M, Eu, Au, (K.1 _ (by decide)).trans sp₀,
        L, by rw [V 3 (by decide) (by decide)]; exact O⟩) ?_
  refine VG.RelCT.seq (taint_both (F := fun s => ∃ M, St base bytes len args sp M 64 s)
    (fun _ _ ⟨_, E₁, A₁, sp₁, _⟩ ⟨_, E₂, A₂, sp₂, _⟩ => agreeA E₁.pi E₂.pi A₁ A₂ (sp₁.trans sp₂.symm)) (.block [])
    (by taint_decide) fun _ ⟨M, E, A, sp₀, X, O⟩ => wp_movS rfl fun u e _ => WP.block_nil
      ⟨M, E.keep e.keeps (by decide) (by decide) (by rw [e.mem]; exact Frame.refl _ _), A.keep e.keeps (by decide),
        (e.other _ (by decide)).trans sp₀, by rw [e.mem]; exact X, by rw [e.mem]; exact O, e.gpr⟩) ?_
  refine VG.RelCT.seq (expLoop_relCT sp hbase hbytes 64 (by decide) (by decide)) ?_
  exact relCT_both ((mul_relCT hbytes sp (o := 2) (a := 2) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, S₁⟩, ⟨_, S₂⟩⟩ =>
        ⟨S₁.2.2.1, S₂.2.2.1, ⟨⟨_, S₁.1, S₁.2.2.2.2.1⟩, S₁.2.1⟩, ⟨⟨_, S₂.1, S₂.2.2.2.2.1⟩, S₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, E, A, sp₀, _, O, _⟩ => WP.mono (mulKeep_ok E A hbytes (o := 2) (a := 2) (b := 3) (by decide)
      (by decide) (by decide) (by decide) O) fun _ ⟨Eu, Au, K, _⟩ => ⟨M, Eu, Au, (K.1 _ (by decide)).trans sp₀⟩

/-- What `sized` needs of a run. -/
def SizedIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PublicInputs base bytes len args s ∧ Room base bytes args s ∧ ArgsOk s ∧ s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true

theorem sized_relCT (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8) (sp : BitVec 32) :
    RelCT isa (Both (SizedIn base bytes len args sp)) sized fun _ _ => True := by
  unfold sized
  refine VG.RelCT.seq (taint_both (F := fun s => ∃ M, ExpIn base bytes len args sp M s)
    (fun _ _ ⟨h₁, _, A₁, sp₁, _⟩ ⟨h₂, _, A₂, sp₂, _⟩ => agreeA h₁ h₂ A₁ A₂ (sp₁.trans sp₂.symm))
    (VG.Taint.hintOf taint τA prepare) (by taint_decide) fun _ ⟨h, X, A, sp₀, V⟩ => ?_) ?_
  · have facts := valid_facts V h.lower
    refine WP.mono (prepare_ok h X.hbase X.room X.top V rfl rfl rfl) fun u ⟨E, hT, hO, _, _, _, _, K⟩ =>
      ⟨_, E, A.keep K (by decide), (K.1 _ (by decide)).trans sp₀, by rw [hO]; exact facts.2.1,
        by rw [hT]; exact Nat.mod_lt _ (by omega)⟩
  refine VG.RelCT.seq (exponentiate_relCT hbase hbytes sp) ?_
  exact RelCT.taint (A := taint) τA (fun _ _ ⟨⟨_, E₁, A₁, sp₁⟩, ⟨_, E₂, A₂, sp₂⟩⟩ =>
    agreeA E₁.pi E₂.pi A₁ A₂ (sp₁.trans sp₂.symm)) (hc := VG.Taint.hintOf taint τA (.seq maskOut write))
    (by taint_decide)

/-- The permissions of `sized`'s narrowed runs: everything readable, the output and the working space
writable. -/
abbrev narrowW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : List Region :=
  [⟨byteAddr (args 0), len⟩, ⟨base, bytes⟩]

/-- What the runs of `sized` from the states themselves need: what the narrowed runs need, the arguments
apart from the output and the working space. -/
def SizedAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PublicInputs base bytes len args s ∧ Room base bytes args s ∧ s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨base, bytes⟩

theorem narrow_in {sp : BitVec 32} {s : State} (S : SizedAt base bytes len args sp s) :
    SizedIn base bytes len args sp (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  obtain ⟨h, X, sp₀, V, Do, Ds⟩ := S
  refine ⟨⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper, h.space,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.nLen, h.inLen, h.ePositive,
    h.eBound, h.outFit, h.nFit, h.eFit, h.inFit, ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, ?_, ?_, ?_,
    h.outApart, h.nApart, h.eApart, h.inApart⟩, ⟨X.hbase, X.hbytes, X.room, X.top⟩, ⟨X.top, ?_⟩, sp₀, V⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.nRead; exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.eRead; exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inRead; exact ⟨r, List.mem_append_left _ hr, hc⟩
  · intro r hr
    simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Do
    · exact Ds

theorem sizedNarrow_relCT (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (sp : BitVec 32) : RelCT isa (Both (SizedAt base bytes len args sp)) sized fun _ _ => True := by
  refine relCT_narrow (Pn := Both (SizedIn base bytes len args sp)) (fun s => s.rd ++ s.wr) (fun _ => narrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_)
    (sized_relCT hbase hbytes sp)
  have cov : ∀ {s : State}, SizedAt base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, SizedAt base bytes len args sp s →
      ∃ F, WP isa sized (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F := by
    intro s S
    obtain ⟨h, X, _, _, V⟩ := narrow_in S
    exact ⟨_, sized_ok h X.hbase X.hbytes X.room X.top V rfl⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    narrow_in S₁, narrow_in S₂⟩

end

end VG.Proof.Bignum.X86.PublicRt
