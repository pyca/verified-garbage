module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # DSA parameter generation on ARMv7: frame words in pieces

The taint analysis does not follow the frame's words, which the search
keeps its state in: a load of one (`ld`) and a store into one (`st`, through
`r12`) leak only addresses from `sp`, the same in two runs of the search
(`ld_vp`, `st_vp`), and the code between them is analysed with the registers
the loads set public (`VP.taint`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd)
open VG.Proof.Rsa.Arm.Recover (VP Two)

/-- A store into the frame leaks its address, from `sp`. -/
theorem st_ct (r : Reg) (o : Nat) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (st r o)) (fun s t => s.sp = t.sp) := by
  intro s t tr1 tr2 u v h e1 e2
  rw [Exec.block_iff] at e1 e2
  simp only [st, execBlock] at e1 e2
  split at e1
  · cases e1
  · rename_i a ha
    split at e2
    · cases e2
    · rename_i b hb
      simp only [exec, show (0 : Nat) < 256 from by decide, ↓reduceIte, Option.some.injEq] at ha hb
      subst ha hb
      split at e1
      · cases e1
      · rename_i a' ha'
        split at e2
        · cases e2
        · rename_i b' hb'
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at e1 e2
          obtain ⟨rfl, rfl⟩ := e1
          obtain ⟨rfl, rfl⟩ := e2
          refine ⟨by simp only [addrs, State.setReg, h, ite_true, List.map_nil, List.nil_append], ?_⟩
          show a'.sp = b'.sp
          rw [exec_sp ha', exec_sp hb']
          simp only [State.setReg, h]

/-- The stage's states have the frame's `sp`. -/
abbrev SpOk (G : VG.Proof.Dsa.Arm.Gen.GP) (F : State → State → Prop) : Prop := ∀ σ s, F σ s → s.sp = G.sp

theorem VP.ld {G : GP} {F Q : State → State → Prop} (hs : SpOk G F) {r : Reg} {o : Nat}
    (wp : ∀ σ s, F σ s → WP isa (.block [ld r o]) s (Q σ)) : VP F (.block [ld r o]) Q :=
  VP.ldrSp (c := [(r, o)]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [hs _ _ h₁, hs _ _ h₂]) wp

theorem VP.st {G : GP} {F Q : State → State → Prop} (hs : SpOk G F) {r : Reg} {o : Nat}
    (wp : ∀ σ s, F σ s → WP isa (.block (st r o)) s (Q σ)) : VP F (.block (st r o)) Q :=
  VP.of_ct (fun σ₁ σ₂ => ((st_ct r o).mono (fun s₁ s₂ h => by rw [hs _ _ h.1, hs _ _ h.2])
    fun _ _ _ => trivial)) wp

theorem SS.spOk {G : GP} {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G σ (c σ) s) :
    SpOk G F := fun σ s h => (hF σ s h).gi.sp

end VG.Proof.Dsa.Arm.Gen
