module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sized
public import VerifiedGarbage.Spec.Dsa.GenerationSized
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SizedContract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendVerified
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInnerCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInitial
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnSpecialized
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86_64.Target

/-! # Width-specific generation retains the original executed trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.Sized
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)


variable {checkName : String}

theorem dispatch_iff (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    {p : GenerationContext} {W : Nat → BitVec 64} {s t : State} {tr : List Leak}
    (h : GenerationMemory p W s) :
    Exec isa (VG.Impl.Dsa.X86_64.Generation.Sized.dispatch (checkName := checkName) p.geo.pLen G1 G256 sq mul round) s tr t ↔
      Exec isa (VG.Impl.Dsa.X86_64.Generation.dispatch (checkName := checkName) G1 G256 sq mul round) s tr t := by
  obtain ⟨V, R⟩ := h.rep
  have h17 := (h.slots 17 (by simp [generationSlots])).trans p.pLenSlot
  have first := lengthTest_ok h.layout R
  unfold VG.Impl.Dsa.X86_64.Generation.Sized.dispatch VG.Impl.Dsa.X86_64.Generation.dispatch
  constructor <;> intro e <;> cases e with
  | seq ec ei =>
    obtain ⟨ha, hz, hm, ku⟩ := Specialized.result first ec
    rw [h17] at ha hz
    rcases p.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · simp only [hp, ↓reduceIte] at ei ⊢
      rcases Exec.ite_inv ei with ⟨_, rfl, hb, et⟩ | ⟨_, rfl, hb, _⟩
      · exact .seq ec (.iteT hb et)
      · simp [eval, hz, hp] at hb
    · simp only [hp, ↓reduceIte] at ei ⊢
      rcases Exec.ite_inv ei with ⟨_, rfl, hb, _⟩ | ⟨_, rfl, hb, er⟩
      · simp [eval, hz, hp] at hb
      · obtain ⟨_, _, u, ec2, ei2, rfl⟩ := Exec.seq_inv er
        obtain ⟨hz2, _, _⟩ := Specialized.result lengthTest256_ok ec2
        rcases Exec.ite_inv ei2 with ⟨_, rfl, hc, et⟩ | ⟨_, rfl, hc, _⟩
        · exact .seq ec (.iteF hb (.seq ec2 (.iteT hc et)))
        · simp [eval, hz2, ha, hp] at hc
    · simp only [hp, ↓reduceIte] at ei ⊢
      rcases Exec.ite_inv ei with ⟨_, rfl, hb, _⟩ | ⟨_, rfl, hb, er⟩
      · simp [eval, hz, hp] at hb
      · obtain ⟨_, _, u, ec2, ei2, rfl⟩ := Exec.seq_inv er
        obtain ⟨hz2, _, _⟩ := Specialized.result lengthTest256_ok ec2
        rcases Exec.ite_inv ei2 with ⟨_, rfl, hc, _⟩ | ⟨_, rfl, hc, et⟩
        · simp [eval, hz2, ha, hp] at hc
        · exact .seq ec (.iteF hb (.seq ec2 (.iteF hc et)))

theorem entryBody_iff (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    {p : GenerationContext} {s t : State} {tr : List Leak} (h : EntryState p s) :
    Exec isa (VG.Impl.Dsa.X86_64.Generation.Sized.entryBody (checkName := checkName) p.geo.pLen G1 G256 sq mul round) s tr t ↔
      Exec isa (VG.Impl.Dsa.X86_64.Generation.entryBody (checkName := checkName) G1 G256 sq mul round) s tr t := by
  constructor <;> intro e <;> cases e with
  | seq ec ed =>
    obtain ⟨W, mu, _⟩ := Specialized.result (entryReady_ok h) ec
    first | exact .seq ec ((dispatch_iff (checkName := checkName) G1 G256 sq mul round mu).mp ed)
          | exact .seq ec ((dispatch_iff (checkName := checkName) G1 G256 sq mul round mu).mpr ed)

theorem code_iff (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    {s t : State} {tr : List Leak} (h : GenerationABI s) :
    Exec isa (VG.Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) (s.gpr .rdx).toNat G1 G256 sq mul round) s tr t ↔
      Exec isa (VG.Impl.Dsa.X86_64.Generation.code (checkName := checkName) G1 G256 sq mul round) s tr t := by
  unfold VG.Impl.Dsa.X86_64.Generation.Sized.code VG.Impl.Dsa.X86_64.Generation.code
  constructor <;> intro e <;> cases e with
  | frame pa body po =>
    have lower : 48 ≤ (s.gpr .rsp).toNat := by have := h.stackLower; omega
    rw [generation_alloc (by decide) lower, Option.some.injEq] at pa
    subst pa
    cases body with
    | seq save rest =>
      obtain ⟨hg, hr, hw, _, hf⟩ := Specialized.result
        (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) save
      cases rest with
      | seq inner restore =>
        cases inner with
        | frame pia ibody pio =>
          have lowerInner := outer_stack_room h hg
          rw [generation_alloc (by decide) lowerInner, Option.some.injEq] at pia
          subst pia
          have init := entryInitial h hg hr hw hf
          first
          | exact .frame (generation_alloc (by decide) lower)
              (.seq save (.seq (.frame (generation_alloc (by decide) lowerInner)
                ((entryBody_iff (checkName := checkName) G1 G256 sq mul round init).mp ibody) pio) restore)) po
          | exact .frame (generation_alloc (by decide) lower)
              (.seq save (.seq (.frame (generation_alloc (by decide) lowerInner)
                ((entryBody_iff (checkName := checkName) G1 G256 sq mul round init).mpr ibody) pio) restore)) po

theorem code_all (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) (pBytes : Nat) (f : Instr → Bool)
    (h : (VG.Impl.Dsa.X86_64.Generation.code (checkName := checkName) G1 G256 sq mul round).all f = true) :
    (VG.Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) pBytes G1 G256 sq mul round).all f = true := by
  unfold VG.Impl.Dsa.X86_64.Generation.code VG.Impl.Dsa.X86_64.Generation.entryBody
    VG.Impl.Dsa.X86_64.Generation.dispatch at h
  unfold VG.Impl.Dsa.X86_64.Generation.Sized.code VG.Impl.Dsa.X86_64.Generation.Sized.entryBody
    VG.Impl.Dsa.X86_64.Generation.Sized.dispatch
  simp only [Code.all, Bool.and_eq_true] at h ⊢
  split <;> split <;> split <;> simp_all [Code.all]

theorem verified (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hv : Verified target (VG.Impl.Dsa.X86_64.Generation.code (checkName := checkName) G1 G256 sq mul round)
      (Spec.Dsa.generateParametersContract abi 472))
    (pBytes : Nat) (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) :
    Verified target (VG.Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) pBytes G1 G256 sq mul round)
      (Spec.Dsa.GenerationSized.contract pBytes abi 472) := by
  refine ⟨?_, ?_, sized_satisfiable pBytes hp⟩
  · intro s hs
    have old := pre_of_sized hs
    obtain ⟨tr, t, he, ha, result⟩ := hv.1 s old
    have hw := width_of_sized hs
    rw [← hw]
    exact ⟨tr, t, (code_iff (checkName := checkName) G1 G256 sq mul round (generationABI_of old)).mpr he, ha, result⟩
  · intro s t tr₁ tr₂ u v hs ht hpub es et
    have olds := pre_of_sized hs
    have oldt := pre_of_sized ht
    have ws := width_of_sized hs
    have wt := width_of_sized ht
    rw [← ws] at es
    rw [← wt] at et
    exact hv.2.1 s t tr₁ tr₂ u v olds oldt hpub
      ((code_iff (checkName := checkName) G1 G256 sq mul round (generationABI_of olds)).mp es)
      ((code_iff (checkName := checkName) G1 G256 sq mul round (generationABI_of oldt)).mp et)

theorem single128 (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) :
    VG.Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) 128 G1 sq mul round =
      VG.Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) 128 G1 G256 sq mul round := by rfl

theorem single256 (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) :
    VG.Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) 256 G256 sq mul round =
      VG.Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) 256 G1 G256 sq mul round := by rfl

theorem single384 (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) :
    VG.Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) 384 G256 sq mul round =
      VG.Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) 384 G1 G256 sq mul round := by rfl

end VG.Proof.Dsa.X86_64.Generation.Sized
