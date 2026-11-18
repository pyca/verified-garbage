module

public import VerifiedGarbage.Proof.Rsa.X86.PrivContext
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument

/-! ### `Rsa.X86.PrivArguments`, which the modules that import this one used -/

section

/-! # Installing successive cdecl arguments preserves every earlier word -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def Arguments (g : PrivGeometry) (values : Nat → BitVec 32) (n : Nat) (s : State) : Prop :=
  ∀ j < n, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = values j

theorem Arguments.append {g : PrivGeometry} {values : Nat → BitVec 32} {n : Nat} {s t : State}
    (h : Arguments g values n s) (hn : n < 18)
    (M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n))
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem) :
    Arguments g values (n + 1) t := by
  intro j hj
  by_cases same : j = n
  · subst j; rw [M, Mem.readW_writeW_self32]
  · rw [outgoing_word_preserved (by omega_using [hn, hj]) hn same F]
    exact h j (by omega_using [hj, same])

theorem slotFrame_outgoing {g : PrivGeometry} {s t : State} {j : Nat} (hj : j < 18)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem) :
    Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [hj])⟩)

theorem prepareArgument_ok {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    {values : Nat → BitVec 32} {n : Nat} {code : List Instr}
    (a : Arguments g values n s) (hn : n < 18)
    (w : WP isa (.block code) s fun t => PrivContext g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t) :
    WP isa (.block code) s fun t => PrivContext g bs t ∧ Arguments g values (n + 1) t ∧
      Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono w ?_
  rintro t ⟨h, M, F, K⟩
  exact ⟨h, a.append hn M F, slotFrame_outgoing hn F, K⟩

end VG.Proof.Rsa.X86.PrivChecked

end

end

/-! # Retaining a call result above the outgoing argument area -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem saveStatus_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) {d : Nat} (hd : d + 4 ≤ 88) :
    WP isa (.block [.store (stackAt d) .eax]) s fun t => PrivContext g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 d) (s.gpr .eax) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem ∧ Keeps [] s t := by
  unfold stackAt
  refine wp_stm (B := s.gpr .esp) rfl
    (by rw [h.address (d := d) (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [hd])]
        exact h.inner.write (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [hd]))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 d) (s.gpr .eax) := by
    rw [T.mem, h.address (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [hd])]
  have K := T.keeps []
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [hd])⟩

theorem status_preserved {g : PrivGeometry} {m m' : Mem} {d : Nat} (hd : 72 ≤ d) (hf : d + 4 ≤ 88)
    (F : Frame [⟨byteAddr g.stack, 72⟩] m m') :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 =
      m.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 := by
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint_base _ hd (by omega_using [hf])

end VG.Proof.Rsa.X86.PrivChecked
