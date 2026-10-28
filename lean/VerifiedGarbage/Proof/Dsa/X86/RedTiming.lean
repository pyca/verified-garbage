module

public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.RedBody
public import VerifiedGarbage.Proof.Dsa.X86.PowABI
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Traces of the IA-32 DSA reduction

Two runs with the same stack pointer and arguments leak the same trace: the
saves and the loads of the arguments are at public addresses, the context's
setup is checked by taint, and the stream runs from the same public address
and length (`reduceStream_relCT`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith VG.Proof.Mont.X86.Dynamic
open VG.Proof.Dsa.X86.Pow (ws bytes)

/-- What the body needs of a run on entry, at the places its arguments give,
with a working space of `size` bytes. -/
structure BodyIn (n size : Nat) (s : State) : Prop where
  input : In n s (ws s) size (arg s 2) (arg s 3).toNat
  size : contextBytes n ≤ size
  large : 255 < wordsVal s.mem (ws s) (slot n 0) n
  odd : wordsVal s.mem (ws s) (slot n 0) n % 2 = 1

/-- Two runs of the body: the same stack pointer and arguments. -/
def Pair (n size : Nat) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ i < 4, arg s i = arg t i) ∧
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) ∧ readSrc t (.mem (at_ .esp 4)) = some (arg t 0) ∧
    BodyIn n size s ∧ BodyIn n size t

theorem contextStart_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (contextStart n) (.seq (workspaceTaint false) (.block []) (oneHint false)) =
      some (zerosTaint false) :=
  exponent_check_seq taint (a := .block (setupInverse (slot n 0) 0)) (ha := .block [])
    (setupInverse_taint false (slot n 0) 0) (by rfl) (one_check false n (slot n 3))

theorem edi_eq {s t : State} {base : Addr} {size size' : Nat} (S : Scr s base size) (T : Scr t base size') :
    s.gpr .edi = t.gpr .edi :=
  BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)

theorem prefix_relCT (n size : Nat) : RelCT isa (Pair n size) (reducePrefix n) (fun _ _ => True) := by
  unfold reducePrefix
  have saveCT : RelCT isa (Pair n size) (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold VG.Impl.Dsa.X86.Pow.save
    rw [List.append_assoc]
    exact (RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
      (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))).mono
      (fun _ _ ⟨SP, A, R₁, R₂, _⟩ => ⟨SP, A 0 (by decide), R₁, R₂⟩) (fun _ _ h => h)
  have saved := saveCT.wpDep (F := fun (σ u : State) => Scr u (ws σ) size ∧ u.gpr .esp = σ.gpr .esp)
    fun s t ⟨_, _, _, _, B₁, B₂⟩ => by
      have go : ∀ σ, BodyIn n size σ → WP isa (.block VG.Impl.Dsa.X86.Pow.save) σ fun u =>
          Scr u (ws σ) size ∧ u.gpr .esp = σ.gpr .esp := by
        intro σ B
        have hz24 : 24 ≤ size := by have := B.size; simp only [contextBytes, slot, stride] at this; omega
        exact WP.mono (Pow.save_ok B.input.entry hz24) fun u ⟨Su, _, _, Ku⟩ => ⟨Su, Ku.1 _ (by decide)⟩
      exact ⟨go s B₁, go t B₂⟩
  have toAgree : ∀ u₁ u₂ : State, (VG.X86.Taint.Agree (workspaceTaint false) u₁ u₂ ∧ ∃ σ₁ σ₂, Pair n size σ₁ σ₂ ∧
      (Scr u₁ (ws σ₁) size ∧ u₁.gpr .esp = σ₁.gpr .esp) ∧
      (Scr u₂ (ws σ₂) size ∧ u₂.gpr .esp = σ₂.gpr .esp)) →
      VG.X86.Taint.Agree (τr [.edi, .esp]) u₁ u₂ := by
    rintro u₁ u₂ ⟨_, σ₁, σ₂, ⟨SP, A, _⟩, ⟨S₁, E₁⟩, ⟨S₂, E₂⟩⟩
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [show ws σ₂ = ws σ₁ by simp only [ws, A 0 (by decide)]] at S₂
      exact edi_eq S₁ S₂
    · rw [E₁, E₂, SP]
  refine RelCT.seq (saved.mono (fun _ _ h => h) toAgree) ?_
  refine RelCT.seq (checkedProgramChange (τ := τr [.edi, .esp]) (σ := workspaceTaint false) (hint := .block []) rfl rfl) ?_
  refine RelCT.seq (checkedProgramChange (σ := workspaceTaint false) (contextStart_check n) (by rfl)) ?_
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_relCT (n size : Nat) (hn : 0 < n) : RelCT isa (Pair n size) (reduceBody n) (fun _ _ => True) := by
  unfold reduceBody
  have P := (prefix_relCT n size).wpDep (F := fun (σ x : State) => Ready n (wordsVal σ.mem (ws σ) (slot n 0) n) σ x
      (ws σ) size (arg σ 2) (arg σ 3).toNat) fun s t ⟨_, _, _, _, B₁, B₂⟩ =>
    ⟨prefix_ok B₁.input B₁.size hn rfl B₁.large B₁.odd, prefix_ok B₂.input B₂.size hn rfl B₂.large B₂.odd⟩
  refine RelCT.seq (R := fun x₁ x₂ => ∃ q : Addr × Nat × Nat, contextBytes n ≤ q.2.1 ∧
      VG.Proof.Dsa.X86.StreamPair n q.2.1 q.2.2 q.1 (.mem (sc lenAt)) x₁ x₂)
    (P.mono (fun _ _ h => h) ?_) ?_
  · rintro x₁ x₂ ⟨_, σ₁, σ₂, ⟨_, A, _, _, B₁, _⟩, R₁, R₂⟩
    have e0 : ws σ₂ = ws σ₁ := by simp only [ws, A 0 (by decide)]
    have e2 : arg σ₂ 2 = arg σ₁ 2 := (A 2 (by decide)).symm
    have e3 : (arg σ₂ 3).toNat = (arg σ₁ 3).toNat := by rw [A 3 (by decide)]
    rw [e0, e2, e3] at R₂
    refine ⟨(ws σ₁, size, (arg σ₁ 3).toNat), B₁.size, ?_, R₁.ctx.scr, R₂.ctx.scr, R₁.lenSrc, R₂.lenSrc⟩
    apply agree_regs (rs := [.edi, .esi])
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact edi_eq R₁.ctx.scr R₂.ctx.scr
    · rw [R₁.esi, R₂.esi]
  refine RelCT.exists_ fun q => ?_
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · intro s t tr ur sf tf ⟨hz, H⟩ E F
    exact VG.Proof.Dsa.X86.reduceStream_relCT (by exact .inr ⟨_, rfl⟩) hn hz s t tr ur sf tf H E F
  · exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
      (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
      (fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Red
