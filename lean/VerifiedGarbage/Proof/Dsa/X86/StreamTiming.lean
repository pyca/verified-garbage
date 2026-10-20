module

public import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
public import VerifiedGarbage.Proof.Dsa.X86.StreamStep
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# Secret-independent byte reduction

The stream's source pointer (`esi`) and its end (`ebx`) are public: `esi`
comes in public, and the length is a word both runs agree on (an immediate,
or a saved public length), so its load is related directly (`lenLoad_relCT`)
rather than by the taint analysis, which knows nothing about the workspace's
words. The rest is the analysis of its code without its offsets.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

/-- A length operand: an immediate, or a word of the workspace. -/
def LenForm (src : Src) : Prop := (∃ v, src = .imm v) ∨ ∃ d, src = .mem (sc d)

/-- Both runs about to stream: public workspace and source pointers, and
the same length. -/
structure StreamPair (n size len : Nat) (base : Addr) (src : Src) (s t : State) : Prop where
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t
  scr₁ : Scr s base size
  scr₂ : Scr t base size
  len₁ : LenSrc base size n s src len
  len₂ : LenSrc base size n t src len

theorem zeros_pair {n size len j : Nat} {base : Addr} {src : Src} (hj : j = 6 ∨ j = 7)
    (hn : 0 < n) (hz : contextBytes n ≤ size) :
    RelCT isa (StreamPair n size len base src) (zerosW (slot n j) (2 * n)) (StreamPair n size len base src) := by
  have b := slot_bound (n := n) (i := 7) (by decide)
  have b6 := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have hb : slot n 9 ≤ size := hz
  have b9 := slot_le (n := n) (i := 7) (j := 9) (by decide)
  simp only [stride] at b b6 b9
  have hsz : slot n j + 4 * (2 * n) ≤ size := by rcases hj with rfl | rfl <;> omega
  have T : RelCT isa (VG.X86.Taint.Agree (workspaceTaint true)) (zerosW (slot n j) (2 * n))
      (VG.X86.Taint.Agree (workspaceTaint true)) :=
    erased_relCT _ (zerosW 0 1) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (zerosW 0 1)))
      rfl rfl rfl rfl
  have T' : RelCT isa (StreamPair n size len base src) (zerosW (slot n j) (2 * n))
      (VG.X86.Taint.Agree (workspaceTaint true)) := T.mono (fun _ _ P => P.agree) (fun _ _ h => h)
  refine (T'.wpDep
    (F := fun (s s' : State) => Outside base (slot n j) (4 * (2 * n)) s.mem s'.mem ∧ Keeps [.eax, .ebp, .edx] s s')
    fun s t (P : StreamPair n size len base src s t) => ⟨WP.mono (zerosW_ok P.scr₁ (by omega) hsz) fun _ ⟨O, _, K⟩ => ⟨O, K⟩,
      WP.mono (zerosW_ok P.scr₂ (by omega) hsz) fun _ ⟨O, _, K⟩ => ⟨O, K⟩⟩).mono (fun _ _ h => h) ?_
  rintro s' t' ⟨A, σ₁, σ₂, P, ⟨O₁, K₁⟩, ⟨O₂, K₂⟩⟩
  have r : ∀ {σ σ' : State}, Outside base (slot n j) (4 * (2 * n)) σ.mem σ'.mem →
      Outs base (streamRanges n) σ.mem σ'.mem := fun O =>
    Outs.of_outside (o := slot n j) (n := 4 * (2 * n)) O (by
      rw [show 4 * (2 * n) = 8 * n by omega]
      rcases hj with rfl | rfl <;> simp [streamRanges])
  exact ⟨A, P.scr₁.of_keeps K₁ (by decide), P.scr₂.of_keeps K₂ (by decide),
    P.len₁.trans K₁.2.1 K₁.2.2 (r O₁), P.len₂.trans K₂.2.1 K₂.2.2 (r O₂)⟩

/-- The length, loaded into `ebx`: the same in both runs. -/
theorem lenLoad_relCT {n size len : Nat} {base : Addr} {src : Src} (hf : LenForm src) :
    RelCT isa (StreamPair n size len base src) (.block [.mov .ebx src]) (VG.X86.Taint.Agree cursorTaint) := by
  intro s t tr ur s' t' P E F
  change StreamPair n size len base src s t at P
  obtain ⟨τ, H⟩ : ∃ τ, taint.checkBlock (workspaceTaint true) [.mov .ebx src] = some τ := by
    rcases hf with ⟨v, rfl⟩ | ⟨d, rfl⟩
    · exact ⟨_, rfl⟩
    · refine ⟨workspaceTaint true, ?_⟩
      rw [← VG.X86.Taint.checkBlock_erase _ _ rfl]
      change taint.checkBlock (workspaceTaint true) [.mov .ebx (.mem (sc 0))] = _
      rfl
  have C : VG.Taint.check taint (workspaceTaint true) (.block [.mov .ebx src]) (.block []) = some τ := H
  refine ⟨(VG.Taint.check_sound C P.agree E F).1, ?_⟩
  have W₁ : WP isa (.block [.mov .ebx src]) s fun u => u.gpr .ebx = BitVec.ofNat 32 len ∧ Keeps [.ebx] s u :=
    wp_movS (P.len₁ s P.scr₁ rfl rfl (Outs.refl _ _ _)) fun u U _ => WP.block_nil ⟨U.gpr, U.keeps⟩
  have W₂ : WP isa (.block [.mov .ebx src]) t fun u => u.gpr .ebx = BitVec.ofNat 32 len ∧ Keeps [.ebx] t u :=
    wp_movS (P.len₂ t P.scr₂ rfl rfl (Outs.refl _ _ _)) fun u U _ => WP.block_nil ⟨U.gpr, U.keeps⟩
  have L₁ := wp_result W₁ E
  have L₂ := wp_result W₂ F
  apply agree_regs (rs := [.edi, .esi, .ebx])
  intro reg hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [L₁.2.1 _ (by decide), L₂.2.1 _ (by decide)]
    exact P.agree.rf.1 _ (by simp [workspaceTaint, RegSet.mem_ofList])
  · rw [L₁.2.1 _ (by decide), L₂.2.1 _ (by decide)]
    exact P.agree.rf.1 _ (by simp [workspaceTaint, RegSet.mem_ofList])
  · exact L₁.1.trans L₂.1.symm

/-- The comparison and the loop, from public source and end pointers. -/
theorem streamLoop_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree cursorTaint)
      (.seq (.block [.alu .add .ebx (.reg .esi), .alu .cmp .esi (.reg .ebx)])
        (.ite .e (.block []) (.loop (streamStep n) .ne)))
      (VG.X86.Taint.Agree (workspaceTaint true)) :=
  erased_relCT _ (.seq (.block [.alu .add .ebx (.reg .esi), .alu .cmp .esi (.reg .ebx)])
      (.ite .e (.block []) (.loop (streamStep 1) .ne)))
    (VG.Taint.hintOf taint cursorTaint (Code.erase (.seq (.block [.alu .add .ebx (.reg .esi), .alu .cmp .esi (.reg .ebx)])
      (.ite .e (.block []) (.loop (streamStep 1) .ne)))))
    rfl rfl rfl rfl

theorem reduceStream_relCT {n size len : Nat} {base : Addr} {src : Src} (hf : LenForm src)
    (hn : 0 < n) (hz : contextBytes n ≤ size) :
    RelCT isa (StreamPair n size len base src) (reduceStream n src) (VG.X86.Taint.Agree (workspaceTaint true)) :=
  RelCT.seq (zeros_pair (.inl rfl) hn hz) (RelCT.seq (zeros_pair (.inr rfl) hn hz)
    (RelCT.seq (lenLoad_relCT hf) (streamLoop_relCT n)))

end VG.Proof.Dsa.X86
