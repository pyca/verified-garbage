module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.SeedTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.DoubleTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Montgomery one and minus one at the run-time width read the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86 (seg withRuns rawBlock ptr_value)
open VG.Proof.RsaKeyGen.X86.Sieve (StackContext)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- About to subtract: `ebp` at the candidate, `ebx` at array 9, `edi` at array 10, `edx` their octets. -/
structure Subtracting (g : Geometry) (q : BitVec 32) (s : State) : Prop where
  ws : Ws s g.W g.L
  stack : StackContext q s
  ebp : PtrAt s g.W .ebp (g.array 0)
  ebx : PtrAt s g.W .ebx (g.array 9)
  edi : PtrAt s g.W .edi (g.array 10)
  edx : (s.gpr .edx).toNat = 4 * g.words
  ecx : s.gpr .ecx = cmask false

theorem subtractArgs_ok {g : Geometry} (v : g.Valid) {a : State} {q : BitVec 32} (C : Context g a)
    (St : StackContext q a) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    WP isa (.block subtractArgs) a (Subtracting g q) := by
  obtain ⟨-, -, -, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  unfold subtractArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (St.store 0 (by decide) .edi) fun e ⟨_, Oe, Ke, Se⟩ => ?_)
  obtain ⟨_, We⟩ := frame_workspace C.ws.nowrap apart (by decide) Oe
  have Ce := Context.keepWork v C Ke (by decide) We fun _ mem => nomatch mem
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v Ce 0 (by decide) .ebp) fun f1 ⟨Q1, N1, L1⟩ => ?_)
  have Cf1 := Ce.keepMem L1 (by decide) N1
  refine WP.block_append (WP.mono (Cf1.ptr v 9 (by decide) .ebx (by decide) (by decide)) fun f2 ⟨Q2, N2, L2⟩ => ?_)
  have Cf2 := Cf1.keepMem L2 (by decide) N2
  refine WP.block_append (WP.mono (Cf2.ptr v 10 (by decide) .eax (by decide) (by decide)) fun f3 ⟨Q3, N3, L3⟩ => ?_)
  have Cf3 := Cf2.keepMem L3 (by decide) N3
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v Cf3) fun f4 ⟨D4, N4, L4⟩ => ?_)
  refine wp_movS rfl fun f5 F5 _ => wp_movS rfl fun f F _ => WP.block_nil ?_
  have Lf : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e f :=
    (((((L1.mono (by decide)).widen L2).widen L3).widen L4).widen F5.keeps).widen F.keeps
  refine ⟨Ce.ws.of_keeps Lf, Se.keep Lf (by decide), ?_, ?_, ?_, ?_, F.gpr⟩
  · rw [PtrAt, F.other .ebp (by decide), F5.other .ebp (by decide), L4.1 .ebp (by decide), L3.1 .ebp (by decide),
      L2.1 .ebp (by decide)]; exact Q1
  · rw [PtrAt, F.other .ebx (by decide), F5.other .ebx (by decide), L4.1 .ebx (by decide), L3.1 .ebx (by decide)]
    exact Q2
  · rw [PtrAt, F.other .edi (by decide), F5.gpr, L4.1 .eax (by decide)]; exact Q3
  · rw [F.other .edx (by decide), F5.other .edx (by decide), D4, BitVec.toNat_ofNat]; omega

section
variable {g : Geometry} {capacity : Nat} {p : BitVec 32}

theorem subtract_trace (v : g.Valid) :
    RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) subtract (fun _ _ => True) := by
  obtain ⟨-, -, many, -⟩ := WitnessRt.fits v
  have fit0 := v.arrayFit (j := 0) (by decide)
  have fit9 := v.arrayFit (j := 9) (by decide)
  have fit10 := v.arrayFit (j := 10) (by decide)
  unfold subtract
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  intro a b tr ur u z H E G
  obtain ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩ := H
  have apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨(p - 20#32).setWidth 64, 20⟩ := by
    obtain ⟨_, S⟩ := S₁
    exact S.caller.stackFar.sub_right (below_sub (a := 20) (by decide) S.caller.low)
  have setup := seg (X := Framed g capacity p) (Y := Subtracting g (p - 20#32)) (c := .block subtractArgs)
    [.esp, .edi] (fun r => if r = .esp then p - 20#32 else BitVec.ofNat 32 g.W.toNat) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.caller.sp]; rfl
      · rw [allocFrame_gpr (q := .edi) _ _ (by decide)]; exact edi_at S.context)
    (rawBlock (by decide +kernel)) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      have sp := S.caller.sp
      have St : StackContext (p - 20#32) (allocFrame 20 s) := by
        rw [← sp]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; have := S.caller.low; omega)
      have C := S.context
      have Ci : Context g (allocFrame 20 s) :=
        ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
          C.width, C.stride, C.pointers⟩
      exact subtractArgs_ok v Ci St apart)
  have loop := seg (X := Subtracting g (p - 20#32)) (Y := StackContext (p - 20#32)) [.ebp, .ebx, .edi, .edx]
    (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 0)
      else if r = .ebx then BitVec.ofNat 32 (g.W.toNat + g.array 9)
      else if r = .edi then BitVec.ofNat 32 (g.W.toNat + g.array 10) else BitVec.ofNat 32 (4 * g.words))
    (fun s S r mem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl
      · exact ptr_value S.ebp
      · exact ptr_value S.ebx
      · exact ptr_value S.edi
      · exact nat_at S.edx) reduceLoop_raw (fun s S =>
      WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok S.ws (a := g.array 0) (m := g.array 9) (d := g.array 10)
        (N := g.words) (by omega) fit0 fit9 fit10 (Or.inr (g.arrayBefore (by decide)))
        (Or.inr (g.arrayBefore (by decide))) S.ebp S.ebx S.edi S.edx S.ecx) fun _ ⟨_, _, _, K⟩ =>
        S.stack.keep K (by decide))
  have restore := seg (X := StackContext (p - 20#32)) (Y := fun _ => True) (c := .block [.mov .edi (.mem (VG.Impl.Mont.X86.at_ .esp 0))])
    [.esp] (fun _ => p - 20#32) (fun a A r mem => by obtain rfl := List.mem_singleton.mp mem; exact A.sp)
    (rawBlock (by decide +kernel)) (fun a A => wp_movS (A.read 0 (by decide)) fun _ _ _ => WP.block_nil trivial)
  exact ⟨(RelCT.seq setup (RelCT.seq loop restore) _ _ _ _ _ _ ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩ E G).1, trivial⟩

/-- About to multiply one by R² (array 4). -/
def OneSet (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ val32 s.mem g.W (g.array 4) g.words < c

theorem constants_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56) (v : g.Valid) (length : g.L = 8 * capacity) :
    RelCT isa (fun s t => Constants.Input g capacity p s ∧ Constants.Input g capacity p t) (constants name mont)
      (fun _ _ => True) := by
  have fit4 := v.arrayFit (j := 4) (by decide)
  unfold constants
  have oneT : RelCT isa (fun s t => Constants.Input g capacity p s ∧ Constants.Input g capacity p t) one
      (fun u z => OneSet g capacity p u ∧ OneSet g capacity p z) :=
    withRuns ((one_trace v).mono (fun _ _ ⟨⟨c, S, _⟩, ⟨d, T, _⟩⟩ => ⟨⟨c, S⟩, ⟨d, T⟩⟩) (fun _ _ H => H))
      fun s ⟨c, S, odd, positive, r2⟩ => WP.mono (one_ok v S) fun _ ⟨T, _, O, _⟩ =>
        ⟨c, T, odd, by
          rw [O.val32 (Or.inl (g.arrayBefore (by decide))) (by have := S.scratch.nowrap; omega), r2]
          exact Nat.mod_lt _ positive⟩
  have mulT : RelCT isa (fun s t => OneSet g capacity p s ∧ OneSet g capacity p t) (VG.Impl.MillerRabin.X86.mulY name mont 4)
      (fun u z => Held g capacity p u ∧ Held g capacity p z) :=
    withRuns ((mulY_relCT (p := p) (b := 4) verified noSp stack v length (by unfold Proof.Rsa.Mont.Operand; decide)).mono
      (fun s t ⟨⟨c, S, odd, lt⟩, ⟨d, T, odd', lt'⟩⟩ => ⟨held_pair ⟨c, S⟩ ⟨d, T⟩,
        ⟨S.context, ⟨c, S.modulus, odd, lt⟩, S.caller⟩, ⟨T.context, ⟨d, T.modulus, odd', lt'⟩, T.caller⟩⟩)
      (fun _ _ H => H))
      fun s ⟨c, S, odd, lt⟩ => WP.mono (mulY_ok verified noSp stack v S.context length S.modulus
        (by unfold Proof.Rsa.Mont.Operand; decide) odd lt S.caller.readLen (by rw [S.caller.sp]; exact S.caller.low)
        (by rw [S.caller.sp]; exact S.caller.stackFar)) fun b ⟨_, _, Kb, Cb, Mb, Fb⟩ => by
          rw [S.caller.sp] at Fb
          exact ⟨c, Cb, Mb, S.caller.keepFrame Kb (by decide) Fb, S.scratch.of_keeps Kb (by decide)⟩
  have copyT : RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) (VG.Impl.MillerRabin.X86.copy 9 6)
      (fun u z => Held g capacity p u ∧ Held g capacity p z) :=
    withRuns ((copy_relCT v 9 6 (by decide) (by decide)).mono (fun s t ⟨S, T⟩ => held_pair S T) (fun _ _ H => H))
      fun s ⟨c, S⟩ => WP.mono (Prepared.copy_ready v S 9 6 (by decide) (by decide) (by decide))
        fun _ ⟨T, _⟩ => ⟨c, T⟩
  exact RelCT.seq oneT (RelCT.seq mulT (RelCT.seq copyT (subtract_trace v)))

end

end VG.Proof.RsaKeyGen.X86.PrepareRt
