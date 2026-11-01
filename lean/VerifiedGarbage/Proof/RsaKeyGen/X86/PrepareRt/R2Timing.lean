module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.SeedTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Timing
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.DoubleTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # R² at the run-time width reads the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86 (seg withRuns)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

section
variable {g : Geometry} {capacity : Nat} {p : BitVec 32}

theorem held_pair {s t : State} (S : Held g capacity p s) (T : Held g capacity p t) : Pair g [.edi] s t := by
  obtain ⟨_, S⟩ := S
  obtain ⟨_, T⟩ := T
  refine ⟨S.context, T.context, agree_regs fun r mem => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.caller.sp.trans T.caller.sp.symm
  · exact (edi_at S.context).trans (edi_at T.context).symm

/-- In the doublings' frame. -/
def Framed (g : Geometry) (capacity : Nat) (p : BitVec 32) (a : State) : Prop :=
  ∃ s, Held g capacity p s ∧ a = allocFrame 20 s

theorem doubles_trace (v : g.Valid) :
    RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) doubles (fun _ _ => True) := by
  unfold doubles
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  intro a b tr ur u z H E G
  obtain ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩ := H
  have apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨(p - 20#32).setWidth 64, 20⟩ := by
    obtain ⟨_, S⟩ := S₁
    exact S.caller.stackFar.sub_right (below_sub (a := 20) (by decide) S.caller.low)
  have setup := seg (X := Framed g capacity p) (Y := In g (p - 20#32) g.w) (c := .block doublesArgs) [.esp, .edi]
    (fun r => if r = .esp then p - 20#32 else BitVec.ofNat 32 g.W.toNat) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.caller.sp]; rfl
      · rw [allocFrame_gpr (q := .edi) _ _ (by decide)]; exact edi_at S.context)
    (VG.Proof.RsaKeyGen.X86.rawBlock (by decide +kernel)) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      have sp := S.caller.sp
      have St : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) (allocFrame 20 s) := by
        rw [← sp]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; have := S.caller.low; omega)
      have C := S.context
      have Ci : Context g (allocFrame 20 s) :=
        ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
          C.width, C.stride, C.pointers⟩
      exact WP.mono (doublesArgs_ok v Ci St apart) fun b ⟨Cb, _, _, Sb, saved, count, _⟩ =>
        ⟨Cb, Sb, saved, count, by have := v.maxWidth; omega⟩)
  exact ⟨(RelCT.seq setup (doublings_trace v apart g.w) _ _ _ _ _ _ ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩ E G).1, trivial⟩


/-- Seeded: `2^(64 w − 1)` in array 6. -/
def Seeded (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ 2 ^ (64 * g.w - 1) ≤ c ∧
    val32 s.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w - 1)

theorem r2_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56) (v : g.Valid) (length : g.L = 8 * capacity) :
    RelCT isa (fun s t => PreparedR2.Input g capacity p s ∧ PreparedR2.Input g capacity p t) (r2 name mont)
      (fun u z => Constants.Input g capacity p u ∧ Constants.Input g capacity p z) := by
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S, odd, top⟩ =>
    WP.mono (r2_ok verified noSp stack v length S odd top) fun _ ⟨T, value, _⟩ => ⟨c, T, odd, by omega, value⟩
  unfold r2
  have seedT : RelCT isa (fun s t => PreparedR2.Input g capacity p s ∧ PreparedR2.Input g capacity p t) seed
      (fun u z => Seeded g capacity p u ∧ Seeded g capacity p z) :=
    withRuns ((seed_trace v).mono (fun _ _ ⟨⟨c, S, _⟩, ⟨d, T, _⟩⟩ => ⟨⟨c, S⟩, ⟨d, T⟩⟩) (fun _ _ H => H))
      fun s ⟨c, S, odd, top⟩ => WP.mono (seed_ok v S) fun _ ⟨T, value, _⟩ => ⟨c, T, odd, top, value⟩
  have doublesT : RelCT isa (fun s t => Seeded g capacity p s ∧ Seeded g capacity p t) doubles
      (fun u z => PreparedR2.SquareInput g capacity p u ∧ PreparedR2.SquareInput g capacity p z) :=
    withRuns ((doubles_trace v).mono (fun _ _ ⟨⟨c, S, _⟩, ⟨d, T, _⟩⟩ => ⟨⟨c, S⟩, ⟨d, T⟩⟩) (fun _ _ H => H))
      fun s ⟨c, S, odd, top, value⟩ => WP.mono (doubles_ok v S odd top value) fun _ ⟨T, V, _⟩ =>
        ⟨c, T, odd, by rw [V]; exact Nat.mod_lt _ (by omega)⟩
  refine RelCT.seq (RelCT.seq seedT (RelCT.seq doublesT ((PreparedR2.squares_pair verified noSp stack v length 5).mono
    (fun s t ⟨S, T⟩ => ⟨held_pair (let ⟨c, S, _⟩ := S; ⟨c, S⟩) (let ⟨c, T, _⟩ := T; ⟨c, T⟩), S, T⟩)
    (fun _ _ H => H.1)))) ?_
  exact (copy_relCT v 4 6 (by decide) (by decide)).mono (fun _ _ H => H) (fun _ _ _ => trivial)

end

end VG.Proof.RsaKeyGen.X86.PrepareRt
