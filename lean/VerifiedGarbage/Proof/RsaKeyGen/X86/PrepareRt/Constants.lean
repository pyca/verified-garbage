module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Montgomery one and minus one at the run-time width, with `Constants.code_ok`'s post-state -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86.Sieve (StackContext)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- `c − one` in array 10, in a frame keeping the workspace pointer. -/
theorem subtract_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity one : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (oneVal : val32 s.mem g.W (g.array 9) g.words = one) (oneLt : one < c) :
    WP isa subtract s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 9) g.words = one ∧
      val32 t.mem g.W (g.array 10) g.words = c - one ∧
      WorkspaceFrame g [(g.array 10, 4 * g.words)] s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have sp := S.caller.sp
  have low := S.caller.low
  have C := S.context
  have nowrap := C.ws.nowrap
  obtain ⟨-, -, many, words⟩ := WitnessRt.fits v
  have fit0 := v.arrayFit (j := 0) (by decide)
  have fit9 := v.arrayFit (j := 9) (by decide)
  have fit10 := v.arrayFit (j := 10) (by decide)
  have a09 : g.array 0 + 4 * g.words ≤ g.array 10 := g.arrayBefore (by decide)
  have a910 : g.array 9 + 4 * g.words ≤ g.array 10 := g.arrayBefore (by decide)
  unfold subtract
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [sp]; omega) (NoSp.of_all (by rfl)) ?_
  have St : StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; omega)
  have Ci : Context g (allocFrame 20 s) :=
    ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
      C.width, C.stride, C.pointers⟩
  have apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ := by
    have A := S.caller.stackFar.sub_right (below_sub (a := 20) (by decide) low)
    rw [← sp] at A
    exact A
  unfold subtractArgs
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (St.store 0 (by decide) .edi) fun e ⟨Me, Oe, Ke, Se⟩ => ?_))
  obtain ⟨Fe, We⟩ := frame_workspace nowrap apart (by decide) Oe
  have Ce := Context.keepWork v Ci Ke (by decide) We fun _ mem => nomatch mem
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
  have Mf : f.mem = e.mem := by rw [F.mem, F5.mem, N4, N3, N2, N1]
  have ebpF : PtrAt f g.W .ebp (g.array 0) := by
    rw [PtrAt, F.other .ebp (by decide), F5.other .ebp (by decide), L4.1 .ebp (by decide), L3.1 .ebp (by decide),
      L2.1 .ebp (by decide)]; exact Q1
  have ebxF : PtrAt f g.W .ebx (g.array 9) := by
    rw [PtrAt, F.other .ebx (by decide), F5.other .ebx (by decide), L4.1 .ebx (by decide), L3.1 .ebx (by decide)]
    exact Q2
  have ediF : PtrAt f g.W .edi (g.array 10) := by
    rw [PtrAt, F.other .edi (by decide), F5.gpr, L4.1 .eax (by decide)]; exact Q3
  have edxF : (f.gpr .edx).toNat = 4 * g.words := by
    rw [F.other .edx (by decide), F5.other .edx (by decide), D4, BitVec.toNat_ofNat]; have := v.maxWidth; omega
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok (Ce.ws.of_keeps Lf) (a := g.array 0)
    (m := g.array 9) (d := g.array 10) (N := g.words) (by omega) fit0 fit9 fit10 (Or.inr a09) (Or.inr a910)
    ebpF ebxF ediF edxF F.gpr) fun h ⟨Oh, _, ⟨borrow, _, equation⟩, Kh⟩ => ?_)
  rw [Mf] at Oh equation
  have Keh : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e h := Lf.trans Kh
  refine wp_movS ((Se.keep Keh (by decide)).read 0 (by decide)) fun u U _ => WP.block_nil ?_
  have Mu : u.mem = h.mem := U.mem
  have restored : u.gpr .edi = (allocFrame 20 s).gpr .edi := by
    rw [U.gpr, stack_read apart fit10 Oh, Me, Mem.readW_writeW_self32]
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] (allocFrame 20 s) u :=
    ((Ke.mono (by decide)).trans Keh).widen U.keeps
  have Kbody : Keeps [.eax, .ebx, .ecx, .edx, .ebp] (allocFrame 20 s) u := by
    refine ⟨fun r mem => ?_, Kall.2⟩
    by_cases same : r = .edi
    · subst r; exact restored
    · exact Kall.1 r (by cases r <;> simp_all)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s (freed 20 u) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps Kbody (by decide)
  have Ws : WorkspaceFrame g [(g.array 10, 4 * g.words)] s.mem (freed 20 u).mem := by
    rw [freed_mem, Mu]
    exact (We.mono fun _ mem => nomatch mem).trans
      (WorkspaceFrame.of_outs nowrap (Outs.of_outside Oh (List.mem_singleton_self _)))
  have Fs : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem (freed 20 u).mem := by
    rw [freed_mem, Mu]
    refine Frame.trans (Fe.sub fun r mem => ?_) ((workspaceGlobalFrame (Outs.of_outside Oh
      (List.mem_singleton_self _)) fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit10).mono
      fun r mem => List.mem_append_left _ mem)
    obtain rfl := List.mem_singleton.mp mem
    refine ⟨below p 80, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [sp]
    exact below_sub (sp := p) (a := 20) (b := 80) (by decide) low
  have Me' : Modulus g c e.mem := S.modulus.keep v We (fun _ mem => nomatch mem) (fun _ mem => nomatch mem)
  have oneE : val32 e.mem g.W (g.array 9) g.words = one := by
    rw [We.val32 fit9 (fun _ mem => nomatch mem), allocFrame_mem, oneVal]
  rw [Me'.candidate, oneE] at equation
  refine ⟨S.keepWorkOf v K (by decide) (by decide) Ws (fun r mem => by
      obtain rfl := List.mem_singleton.mp mem; exact v.arrayHeader _)
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact a09) Fs, ?_, ?_, Ws, Fs, K⟩
  · rw [freed_mem, Mu, Oh.val32 (Or.inl a910) (by omega), oneE]
  · rw [freed_mem, Mu]
    have bound := val32_lt h.mem g.W (g.array 10) g.words
    cases borrow <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      at equation <;> omega

theorem constants_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (odd : c % 2 = 1) (positive : 0 < c)
    (r2 : val32 s.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c) :
    WP isa (constants name mont) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c ∧
      WorkspaceFrame g (Constants.ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps Constants.clob s t := by
  unfold constants
  refine WP.seq (WP.mono (one_ok v S) fun a ⟨A, one, Oa, Ka⟩ => ?_)
  have r2A : val32 a.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c := by
    have fit4 := v.arrayFit (j := 4) (by decide)
    have nowrap := S.scratch.nowrap
    rw [Oa.val32 (Or.inl (g.arrayBefore (by decide))) (by omega)]
    exact r2
  refine WP.seq (WP.mono (mulY_ok verified noSp stack v A.context length A.modulus
    (by unfold Proof.Rsa.Mont.Operand; decide) odd (by rw [r2A]; exact Nat.mod_lt _ positive)
    A.caller.readLen (by rw [A.caller.sp]; exact A.caller.low) (by rw [A.caller.sp]; exact A.caller.stackFar))
    fun b ⟨Vb, Ob, Kb, Cb, Mb, Fb⟩ => ?_)
  rw [A.caller.sp] at Fb
  have B : Ready g c capacity p b := ⟨Cb, Mb, A.caller.keepFrame Kb (by decide) Fb,
    A.scratch.of_keeps Kb (by decide)⟩
  rw [one, r2A, Constants.one_r2 odd] at Vb
  refine WP.seq (WP.mono (Prepared.copy_ready v B 9 6 (by decide) (by decide) (by decide))
    fun d ⟨D, Vd, Od, Kd⟩ => ?_)
  have oneD := Vd.trans Vb
  refine WP.mono (subtract_ok v D oneD (Nat.mod_lt _ positive)) fun t ⟨T, oneT, minusT, Wt, Ft, Kt⟩ => ?_
  have Wa : WorkspaceFrame g (Constants.ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.scratch.nowrap (Outs.of_outside
      (Oa.mono (Nat.le_refl _) (by unfold Geometry.words; omega))
      (show (g.array 6, 8 * (g.w + 2)) ∈ Constants.ranges g from by simp [Constants.ranges, montWrites]))
  have Wb := Ob.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ montWrites g 6, r ∈ Constants.ranges g)
  have Wd : WorkspaceFrame g (Constants.ranges g) b.mem d.mem :=
    WorkspaceFrame.of_outs B.scratch.nowrap (Outs.of_outside Od (by simp [Constants.ranges]))
  have Wt' : WorkspaceFrame g (Constants.ranges g) d.mem t.mem := Wt.mono (by simp [Constants.ranges])
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fd : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) b.mem d.mem :=
    (workspaceGlobalFrame (Outs.of_outside Od (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨T, oneT, minusT, ((Wa.trans Wb).trans Wd).trans Wt', ((Fa.trans Fb).trans Fd).trans Ft, ?_⟩
  have Ksa : Keeps Constants.clob s a := Ka.mono (by unfold Constants.clob; decide)
  exact ((Ksa.widen Kb).widen Kd).widen Kt

end VG.Proof.RsaKeyGen.X86.PrepareRt
