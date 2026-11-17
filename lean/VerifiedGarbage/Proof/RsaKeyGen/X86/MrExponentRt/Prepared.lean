module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Halve32
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2

/-! ### `RsaKeyGen.X86.PrepareRt.Constants`, which this module and modules that import it used -/

section

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
  obtain fit0 := v.arrayFit (j := 0) (by decide)
  obtain fit9 := v.arrayFit (j := 9) (by decide)
  obtain fit10 := v.arrayFit (j := 10) (by decide)
  obtain a09 : g.array 0 + 4 * g.words ≤ g.array 10 := g.arrayBefore (by decide)
  obtain a910 : g.array 9 + 4 * g.words ≤ g.array 10 := g.arrayBefore (by decide)
  unfold subtract
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [sp]; omega_using [low]) (NoSp.of_all (by rfl)) ?_
  obtain St : StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; omega_using [low])
  obtain Ci : Context g (allocFrame 20 s) :=
    ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
      C.width, C.stride, C.pointers⟩
  obtain apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ := by
    obtain A := S.caller.stackFar.sub_right (below_sub (a := 20) (by decide) low)
    rw [← sp] at A
    exact A
  unfold subtractArgs
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (St.store 0 (by decide) .edi) fun e ⟨Me, Oe, Ke, Se⟩ => ?_))
  obtain ⟨Fe, We⟩ := frame_workspace nowrap apart (by decide) Oe
  obtain Ce := Context.keepWork v Ci Ke (by decide) We fun _ mem => nomatch mem
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v Ce 0 (by decide) .ebp) fun f1 ⟨Q1, N1, L1⟩ => ?_)
  obtain Cf1 := Ce.keepMem L1 (by decide) N1
  refine WP.block_append (WP.mono (Cf1.ptr v 9 (by decide) .ebx (by decide) (by decide)) fun f2 ⟨Q2, N2, L2⟩ => ?_)
  obtain Cf2 := Cf1.keepMem L2 (by decide) N2
  refine WP.block_append (WP.mono (Cf2.ptr v 10 (by decide) .eax (by decide) (by decide)) fun f3 ⟨Q3, N3, L3⟩ => ?_)
  obtain Cf3 := Cf2.keepMem L3 (by decide) N3
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v Cf3) fun f4 ⟨D4, N4, L4⟩ => ?_)
  refine wp_movS rfl fun f5 F5 _ => wp_movS rfl fun f F _ => WP.block_nil ?_
  obtain Lf : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e f :=
    (((((L1.mono (by decide)).widen L2).widen L3).widen L4).widen F5.keeps).widen F.keeps
  obtain Mf : f.mem = e.mem := by rw [F.mem, F5.mem, N4, N3, N2, N1]
  obtain ebpF : PtrAt f g.W .ebp (g.array 0) := by
    rw [PtrAt, F.other .ebp (by decide), F5.other .ebp (by decide), L4.1 .ebp (by decide), L3.1 .ebp (by decide),
      L2.1 .ebp (by decide)]; exact Q1
  obtain ebxF : PtrAt f g.W .ebx (g.array 9) := by
    rw [PtrAt, F.other .ebx (by decide), F5.other .ebx (by decide), L4.1 .ebx (by decide), L3.1 .ebx (by decide)]
    exact Q2
  obtain ediF : PtrAt f g.W .edi (g.array 10) := by
    rw [PtrAt, F.other .edi (by decide), F5.gpr, L4.1 .eax (by decide)]; exact Q3
  obtain edxF : (f.gpr .edx).toNat = 4 * g.words := by
    rw [F.other .edx (by decide), F5.other .edx (by decide), D4, BitVec.toNat_ofNat]; have := v.maxWidth; omega_using [words, this]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok (Ce.ws.of_keeps Lf) (a := g.array 0)
    (m := g.array 9) (d := g.array 10) (N := g.words) (by omega_using [many]) fit0 fit9 fit10 (Or.inr a09) (Or.inr a910)
    ebpF ebxF ediF edxF F.gpr) fun h ⟨Oh, _, ⟨borrow, _, equation⟩, Kh⟩ => ?_)
  rw [Mf] at Oh equation
  obtain Keh : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e h := Lf.trans Kh
  refine wp_movS ((Se.keep Keh (by decide)).read 0 (by decide)) fun u U _ => WP.block_nil ?_
  have Mu : u.mem = h.mem := U.mem
  obtain restored : u.gpr .edi = (allocFrame 20 s).gpr .edi := by
    rw [U.gpr, stack_read apart fit10 Oh, Me, Mem.readW_writeW_self32]
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] (allocFrame 20 s) u :=
    ((Ke.mono (by decide)).trans Keh).widen U.keeps
  obtain Kbody : Keeps [.eax, .ebx, .ecx, .edx, .ebp] (allocFrame 20 s) u := by
    refine ⟨fun r mem => ?_, Kall.2⟩
    by_cases same : r = .edi
    · subst r; exact restored
    · exact Kall.1 r (by cases r <;> simp_all)
  obtain K : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s (freed 20 u) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps Kbody (by decide)
  obtain Ws : WorkspaceFrame g [(g.array 10, 4 * g.words)] s.mem (freed 20 u).mem := by
    rw [freed_mem, Mu]
    exact (We.mono fun _ mem => nomatch mem).trans
      (WorkspaceFrame.of_outs nowrap (Outs.of_outside Oh (List.mem_singleton_self _)))
  obtain Fs : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem (freed 20 u).mem := by
    rw [freed_mem, Mu]
    refine Frame.trans (Fe.sub fun r mem => ?_) ((workspaceGlobalFrame (Outs.of_outside Oh
      (List.mem_singleton_self _)) fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit10).mono
      fun r mem => List.mem_append_left _ mem)
    obtain rfl := List.mem_singleton.mp mem
    refine ⟨below p 80, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [sp]
    exact below_sub (sp := p) (a := 20) (b := 80) (by decide) low
  obtain Me' : Modulus g c e.mem := S.modulus.keep v We (fun _ mem => nomatch mem) (fun _ mem => nomatch mem)
  obtain oneE : val32 e.mem g.W (g.array 9) g.words = one := by
    rw [We.val32 fit9 (fun _ mem => nomatch mem), allocFrame_mem, oneVal]
  rw [Me'.candidate, oneE] at equation
  refine ⟨S.keepWorkOf v K (by decide) (by decide) Ws (fun r mem => by
      obtain rfl := List.mem_singleton.mp mem; exact v.arrayHeader _)
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact a09) Fs, ?_, ?_, Ws, Fs, K⟩
  · rw [freed_mem, Mu, Oh.val32 (Or.inl a910) (by omega_using [nowrap, fit9]), oneE]
  · rw [freed_mem, Mu]
    obtain bound := val32_lt h.mem g.W (g.array 10) g.words
    cases borrow <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      at equation <;> omega_arith

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
  obtain r2A : val32 a.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c := by
    obtain fit4 := v.arrayFit (j := 4) (by decide)
    have nowrap := S.scratch.nowrap
    rw [Oa.val32 (Or.inl (g.arrayBefore (by decide))) (by omega_using [fit4, nowrap])]
    exact r2
  refine WP.seq (WP.mono (mulY_ok verified noSp stack v A.context length A.modulus
    (by unfold Proof.Rsa.Mont.Operand; decide) odd (by rw [r2A]; exact Nat.mod_lt _ positive)
    A.caller.readLen (by rw [A.caller.sp]; exact A.caller.low) (by rw [A.caller.sp]; exact A.caller.stackFar))
    fun b ⟨Vb, Ob, Kb, Cb, Mb, Fb⟩ => ?_)
  rw [A.caller.sp] at Fb
  obtain B : Ready g c capacity p b := ⟨Cb, Mb, A.caller.keepFrame Kb (by decide) Fb,
    A.scratch.of_keeps Kb (by decide)⟩
  rw [one, r2A, Constants.one_r2 odd] at Vb
  refine WP.seq (WP.mono (Prepared.copy_ready v B 9 6 (by decide) (by decide) (by decide))
    fun d ⟨D, Vd, Od, Kd⟩ => ?_)
  obtain oneD := Vd.trans Vb
  refine WP.mono (subtract_ok v D oneD (Nat.mod_lt _ positive)) fun t ⟨T, oneT, minusT, Wt, Ft, Kt⟩ => ?_
  obtain Wa : WorkspaceFrame g (Constants.ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.scratch.nowrap (Outs.of_outside
      (Oa.mono (Nat.le_refl _) (by unfold Geometry.words; omega_using []))
      (show (g.array 6, 8 * (g.w + 2)) ∈ Constants.ranges g from by simp [Constants.ranges, montWrites]))
  obtain Wb := Ob.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ montWrites g 6, r ∈ Constants.ranges g)
  obtain Wd : WorkspaceFrame g (Constants.ranges g) b.mem d.mem :=
    WorkspaceFrame.of_outs B.scratch.nowrap (Outs.of_outside Od (by simp [Constants.ranges]))
  obtain Wt' : WorkspaceFrame g (Constants.ranges g) d.mem t.mem := Wt.mono (by simp [Constants.ranges])
  obtain Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  obtain Fd : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) b.mem d.mem :=
    (workspaceGlobalFrame (Outs.of_outside Od (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨T, oneT, minusT, ((Wa.trans Wb).trans Wd).trans Wt', ((Fa.trans Fb).trans Fd).trans Ft, ?_⟩
  obtain Ksa : Keeps Constants.clob s a := Ka.mono (by unfold Constants.clob; decide)
  exact ((Ksa.widen Kb).widen Kd).widen Kt

end VG.Proof.RsaKeyGen.X86.PrepareRt

end

end

/-! ### `RsaKeyGen.X86.MrExponentRt.Code`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MrExponentRt.Scan`, which this module and modules that import it used -/

section

/-! # The first nonzero pair of array 5, scanned at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MrExponentRt
open VG.Proof.RsaKeyGen.X86.LowPair (first select pairAt)

theorem first_succ (m : Mem) (base : Addr) (src : Nat) (before : BitVec 32 × BitVec 32) (start count : Nat) :
    first m base src before start (count + 1) =
      select (first m base src before start count) (pairAt m base (src + 8 * (start + count))) := by
  induction count generalizing before start with
  | zero => rfl
  | succ count ih =>
    change first m base src (select before (pairAt m base (src + 8 * start))) (start + 1) (count + 1) = _
    rw [ih, show start + 1 + count = start + (count + 1) by omega_using []]
    rfl

theorem first_congr {m m' : Mem} {base : Addr} {src : Nat} (before : BitVec 32 × BitVec 32) (start count : Nat)
    (same : ∀ j < start + count, pairAt m base (src + 8 * j) = pairAt m' base (src + 8 * j)) :
    first m base src before start count = first m' base src before start count := by
  induction count generalizing before start with
  | zero => rfl
  | succ count ih =>
    change first m base src (select before (pairAt m base (src + 8 * start))) (start + 1) count =
      first m' base src (select before (pairAt m' base (src + 8 * start))) (start + 1) count
    rw [same start (by omega_using [])]
    exact ih _ _ fun j index => same j (by omega_using [index])

theorem pairStep_ok {t : State} {W : Addr} {L y : Nat} (hw : Ws t W L) (ebp : PtrAt t W .ebp y)
    (fit : y + 8 ≤ L) :
    WP isa (.block pairStep) t fun u =>
      (u.gpr .ebx, u.gpr .esi) = select (t.gpr .ebx, t.gpr .esi) (pairAt t.mem W y) ∧ u.mem = t.mem ∧
      PtrAt u W .ebp (y + 8) ∧ u.gpr .edi = t.gpr .edi - 1 ∧ u.zf = some (t.gpr .edi - 1 == 0) ∧
      Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp, .edi] t u := by
  unfold pairStep
  simp only [List.cons_append]
  refine wp_movS (readSrc_ptr hw ebp (d := 0) (by omega_using [fit])) fun a A _ => ?_
  have ebpA : PtrAt a W .ebp y := by rw [PtrAt, A.other .ebp (by decide)]; exact ebp
  refine wp_movS (readSrc_ptr (hw.of_keeps A.keeps) ebpA (d := 4) (by omega_using [fit])) fun b B _ => ?_
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.LowPair.choose_ok b) fun c ⟨V, Mc, Kc⟩ => ?_)
  refine wp_addS rfl fun d D _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  have Kb : Keeps [.eax, .ecx] t b := (A.keeps.mono (by decide)).widen B.keeps
  have Kd : Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp] t d :=
    ((Kb.mono (by decide)).trans (Kc.mono (by decide))).widen D.keeps
  have mem : u.mem = t.mem := by rw [U.mem, D.mem, Mc, B.mem, A.mem]
  have ediD : d.gpr .edi = t.gpr .edi := Kd.1 .edi (by decide)
  refine ⟨?_, mem, ?_, by rw [U.gpr, ediD], by rw [Z, ediD], (Kd.mono (by decide)).widen U.keeps⟩
  · rw [U.other .ebx (by decide), U.other .esi (by decide), D.other .ebx (by decide), D.other .esi (by decide),
      V, B.other .ebx (by decide), B.other .esi (by decide), A.other .ebx (by decide), A.other .esi (by decide),
      B.other .eax (by decide), A.gpr, B.gpr, A.mem, Nat.add_zero]
    rfl
  · rw [PtrAt, U.other .ebp (by decide), D.gpr, Kc.1 .ebp (by decide), Kb.1 .ebp (by decide), ptr_add ebp]
    rfl

theorem scanLoop_ok {t₀ : State} {W : Addr} {L y N : Nat} (hw : Ws t₀ W L) (positive : 0 < N)
    (fit : y + 8 * N ≤ L) (ebp : PtrAt t₀ W .ebp y) (count : (t₀.gpr .edi).toNat = N) :
    WP isa (.loop (.block pairStep) .ne) t₀ fun u =>
      (u.gpr .ebx, u.gpr .esi) = first t₀.mem W y (t₀.gpr .ebx, t₀.gpr .esi) 0 N ∧ u.mem = t₀.mem ∧
      Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp, .edi] t₀ u := by
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop positive (fun j t =>
      Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp, .edi] t₀ t ∧ t.mem = t₀.mem ∧ PtrAt t W .ebp (y + 8 * j) ∧
      (t.gpr .edi).toNat = N - j ∧ (t.gpr .ebx, t.gpr .esi) = first t₀.mem W y (t₀.gpr .ebx, t₀.gpr .esi) 0 j) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using ebp, by simpa using count, rfl⟩) fun u ⟨K, M, _, _, V⟩ => ⟨V, M, K⟩
  rintro j t index ⟨K, M, bp, edi, V⟩
  refine WP.mono (pairStep_ok (hw.of_keeps K) bp (by omega_using [fit, index])) fun u ⟨Vu, Mu, bpu, ediu, Z, Ku⟩ => ?_
  obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf edi index
  refine ⟨⟨K.trans Ku, Mu.trans M, by rw [show y + 8 * (j + 1) = y + 8 * j + 8 by omega_using []]; exact bpu,
    by rw [ediu]; exact next, ?_⟩, by rw [Z, last]⟩
  rw [Vu, V, M, first_succ, Nat.zero_add]

/-- The scan's frame keeps everything the prepared state says. -/
theorem Ready.keepStack {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s t : State}
    (S : PreparedR2.Ready g c capacity p s) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) (base : .edi ∉ rs)
    (F : Frame [below p 20] s.mem t.mem) : PreparedR2.Ready g c capacity p t ∧ WorkspaceFrame g [] s.mem t.mem := by
  have W : WorkspaceFrame g [] s.mem t.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame F S.scratch.nowrap fun r mem => by
      obtain rfl := List.mem_singleton.mp mem
      exact S.caller.stackFar.sub_right (below_sub (by decide) S.caller.low)
  have head := v.headerFit
  have read {d : Nat} (fit : d + 4 ≤ g.L) : w32 t.mem g.W d = w32 s.mem g.W d :=
    congrArg BitVec.toNat (W.read32 fit fun _ mem => nomatch mem)
  have header := S.context
  refine ⟨⟨⟨header.ws.of_keeps K, ?_, ?_, ?_, ?_⟩, S.modulus.keep v W (fun _ mem => nomatch mem)
    (fun _ mem => nomatch mem), S.caller.keepFrame K sp ?_, S.scratch.of_keeps K base sp⟩, W⟩
  · rw [PtrAt, K.1 .edi base]; exact header.base
  · rw [read (by omega_using [head])]; exact header.width
  · rw [read (by omega_using [head])]; exact header.stride
  · intro j index
    rw [read (by omega_using [head, index])]; exact header.pointers j index
  · refine F.sub fun r mem => ?_
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by decide) S.caller.low⟩

theorem scanSetup_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) {p : BitVec 32}
    (St : VG.Proof.RsaKeyGen.X86.Sieve.StackContext p s) :
    WP isa (.block scanSetup) s fun a =>
      a.mem = s.mem.writeW (off (p.setWidth 64) 0) (s.gpr .edi) ∧ Outside (p.setWidth 64) 0 4 s.mem a.mem ∧
      PtrAt a g.W .ebp (g.array 5) ∧ (a.gpr .edi).toNat = g.w ∧ a.gpr .ebx = 0#32 ∧ a.gpr .esi = 0#32 ∧
      Keeps [.ebx, .esi, .ebp, .edx, .edi] s a := by
  unfold scanSetup
  refine WP.block_append (WP.block_append ?_)
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => WP.block_nil ?_
  have Kb : Keeps [.ebx, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Cb := C.keepMem Kb (by decide) (by rw [B.mem, A.mem])
  refine WP.mono (Cb.ptr v 5 (by decide) .ebp (by decide) (by decide)) fun c ⟨P, Mc, Kc⟩ => ?_
  have Kc' : Keeps [.ebx, .esi, .ebp, .edx] s c := (Kb.mono (by decide)).widen Kc
  have Cc := C.keepMem Kc' (by decide) (by rw [Mc, B.mem, A.mem])
  refine wp_movS (readSrc_ptr Cc.ws Cc.base (d := 48) (by have := v.headerFit; omega_using [this])) fun d D _ => ?_
  have Kd : Keeps [.ebx, .esi, .ebp, .edx] s d := Kc'.widen D.keeps
  have Sd := St.keep Kd (by decide)
  refine wp_storeS (Sd.address 0 (by decide)) (ws_write Sd.ws (y := 0) (n := 4) (by decide)) fun e E => ?_
  refine wp_movS rfl fun u U _ => WP.block_nil ?_
  have memD : d.mem = s.mem := by rw [D.mem, Mc, B.mem, A.mem]
  have ediD : d.gpr .edi = s.gpr .edi := Kd.1 .edi (by decide)
  have mem : u.mem = s.mem.writeW (off (p.setWidth 64) 0) (s.gpr .edi) := by
    rw [U.mem, E.mem, memD, ediD]
  refine ⟨mem, ?_, ?_, ?_, ?_, ?_, ((Kd.mono (by decide)).widen (E.keeps [])).widen U.keeps⟩
  · rw [mem]; exact writeW32_outside _ _ _ (by have := Sd.ws.nowrap; omega_using [])
  · rw [PtrAt, U.other .ebp (by decide), E.gpr, D.other .ebp (by decide)]; exact P
  · rw [U.gpr, E.gpr, D.gpr, Nat.zero_add]
    change w32 c.mem g.W 48 = g.w
    exact Cc.width
  · rw [U.other .ebx (by decide), E.gpr, D.other .ebx (by decide), Kc.1 .ebx (by decide), B.other .ebx (by decide),
      A.gpr]
    rfl
  · rw [U.other .esi (by decide), E.gpr, D.other .esi (by decide), Kc.1 .esi (by decide), B.gpr]
    rfl

theorem scan_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : PreparedR2.Ready g c capacity p s) :
    WP isa scan s fun t =>
      (t.gpr .ebx, t.gpr .esi) = first s.mem g.W (g.array 5) (0#32, 0#32) 0 g.w ∧
      Frame [below p 20] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp] s t := by
  have sp := S.caller.sp
  have low := S.caller.low
  have C := S.context
  unfold scan
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [sp]; omega_using [low]) (NoSp.of_all (by rfl)) ?_
  have St : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; omega_using [low])
  have Ci : Context g (allocFrame 20 s) :=
    ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
      C.width, C.stride, C.pointers⟩
  refine WP.seq (WP.mono (scanSetup_ok v Ci St) fun a ⟨Ma, Oa, P, count, ebx, esi, Ka⟩ => ?_)
  have frameA : Frame [below p 20] s.mem a.mem := by
    rw [← sp]
    simpa only [allocFrame_mem, below, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame (Oa.mono (o' := 0) (n' := 20) (by decide) (by decide)) (by decide)
  have W : WorkspaceFrame g [] s.mem a.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame frameA S.scratch.nowrap fun r mem => by
      obtain rfl := List.mem_singleton.mp mem
      exact S.caller.stackFar.sub_right (below_sub (by decide) low)
  have fit := v.arrayFit (j := 5) (by decide)
  have positive := v.minWidth
  unfold Geometry.words at fit
  refine WP.seq (WP.mono (scanLoop_ok (Ci.ws.of_keeps Ka) (by omega_using [positive]) (by omega_using [fit]) P count)
    fun b ⟨V, Mb, Kb⟩ => ?_)
  have Kab : Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp, .edi] (allocFrame 20 s) b :=
    (Ka.mono (by decide)).trans Kb
  have Sb := St.keep Kab (by decide)
  refine wp_movS (Sb.read 0 (by decide)) fun u U _ => WP.block_nil ?_
  have restored : u.gpr .edi = (allocFrame 20 s).gpr .edi := by
    rw [U.gpr, Mb, Ma, Mem.readW_writeW_self32]
  have Kall : Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp, .edi] (allocFrame 20 s) u :=
    Kab.widen U.keeps
  have Kbody : Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp] (allocFrame 20 s) u := by
    refine ⟨?_, Kall.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact restored
    · exact Kall.1 r (by cases r <;> simp_all)
  refine ⟨?_, ?_, VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps Kbody (by decide)⟩
  · rw [freed_gpr _ _ (by decide), freed_gpr _ _ (by decide), U.other .ebx (by decide), U.other .esi (by decide), V,
      ebx, esi]
    refine (first_congr _ _ _ fun j index => ?_).symm
    have read (d : Nat) (h : d + 4 ≤ g.L) : a.mem.readW (off g.W d) 32 = s.mem.readW (off g.W d) 32 :=
      W.read32 h fun _ mem => nomatch mem
    simp only [pairAt]
    rw [read _ (by omega_using [fit, index]), read _ (by omega_using [fit, index])]
  · rw [freed_mem, U.mem, Mb]
    exact frameA

end VG.Proof.RsaKeyGen.X86.MrExponentRt

end

end

/-! ### `RsaKeyGen.X86.MrExponentRt.Half`, which only this module used -/

section

/-! # Array 27 halved in place at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MrExponentRt

/-- A pointer into the working space, from `edi` at its base. -/
theorem ptr_edi {t : State} {W : Addr} {L x : Nat} (S : Scr t W L) {r : Reg} (P : PtrAt t W r x) (_fit : x < L) :
    t.gpr r = t.gpr .edi + BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have nowrap := S.nowrap
  rw [P, BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
  omega_using []

/-- One word of an in-place pass, at `ebp`, and `esi` down one. -/
theorem halfStep_ok {t : State} {W : Addr} {L x : Nat} (S : Scr t W L) (bp : PtrAt t W .ebp x)
    (aligned : x % 4 = 0) (fit : x + 8 ≤ L) {choice : Bool} (mask : t.gpr .ecx = cmask choice) :
    WP isa (.block halfStep) t fun u =>
      Outside W x 4 t.mem u.mem ∧
      w32 u.mem W x = (if choice then w32 t.mem W x / 2 + 2 ^ 31 * (w32 t.mem W (x + 4) % 2) else w32 t.mem W x) ∧
      PtrAt u W .ebp (x + 4) ∧ u.gpr .esi = t.gpr .esi - 1 ∧ u.zf = some (t.gpr .esi - 1 == 0) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] t u := by
  have index : 0 + 4 * (x / 4) = x := by omega_using [aligned]
  have pointer : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (x / 4)) := by
    rw [ptr_edi S bp (by omega_using [fit])]; congr 2; omega_using [aligned]
  unfold halfStep
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.HalfPass.step_ok (src := 0) (out := 0) S pointer
    (by omega_using [fit]) (by omega_using [fit]) mask) fun a ⟨O, V, K⟩ => ?_)
  refine wp_addS rfl fun b B _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  rw [index] at O V
  have esiB : b.gpr .esi = t.gpr .esi := by rw [B.other .esi (by decide), K.1 .esi (by decide)]
  refine ⟨by rw [U.mem, B.mem]; exact O, by rw [U.mem, B.mem, V],
    ?_, by rw [U.gpr, esiB], by rw [Z, esiB], ((K.mono (by decide)).widen B.keeps).widen U.keeps⟩
  rw [PtrAt, U.other .ebp (by decide), B.gpr, K.1 .ebp (by decide), ptr_add bp]
  rfl

theorem halfLoop_ok {t₀ : State} {W : Addr} {L x N : Nat} (S : Scr t₀ W L) (positive : 0 < N)
    (aligned : x % 4 = 0) (fit : x + 4 * (N + 1) ≤ L) (top : w32 t₀.mem W (x + 4 * N) = 0)
    (bp : PtrAt t₀ W .ebp x) (count : (t₀.gpr .esi).toNat = N) {choice : Bool} (mask : t₀.gpr .ecx = cmask choice) :
    WP isa (.loop (.block halfStep) .ne) t₀ fun u =>
      Outside W x (4 * N) t₀.mem u.mem ∧
      val32 u.mem W x N = (if choice then val32 t₀.mem W x N / 2 else val32 t₀.mem W x N) ∧
      PtrAt u W .ebp (x + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] t₀ u := by
  have nowrap := S.nowrap
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop positive (fun j t =>
      Keeps [.eax, .ebx, .edx, .ebp, .esi] t₀ t ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      (∀ i < j, w32 t.mem W (x + 4 * i) =
        if choice then w32 t₀.mem W (x + 4 * i) / 2 + 2 ^ 31 * (w32 t₀.mem W (x + 4 * i + 4) % 2)
        else w32 t₀.mem W (x + 4 * i)) ∧
      PtrAt t W .ebp (x + 4 * j) ∧ (t.gpr .esi).toNat = N - j) ?_
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), by simpa using bp,
      by simpa using count⟩) ?_
  · rintro j t index ⟨K, O, V, P, esi⟩
    have St := S.of_keeps K (by decide)
    refine WP.mono (halfStep_ok (choice := choice) St P (by omega_using [aligned]) (by omega_using [fit, index]) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Pu, esiU, Z, Ku⟩ => ?_
    obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf esi index
    have sameLo : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) := O.w32 (by omega_using []) (by omega_using [fit, nowrap, index])
    have sameHi : w32 t.mem W (x + 4 * j + 4) = w32 t₀.mem W (x + 4 * j + 4) := O.w32 (by omega_using []) (by omega_using [fit, nowrap, index])
    refine ⟨⟨K.trans Ku, (O.mono (by omega_using []) (by omega_using [])).trans (Ou.mono (by omega_using []) (by omega_using [])), ?_,
      by rw [show x + 4 * (j + 1) = x + 4 * j + 4 by omega_using []]; exact Pu, by rw [esiU]; exact next⟩,
      by rw [Z, last]⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega_using [before]) (by omega_using [fit, nowrap, index, hi])]
      exact V i before
    · rw [value, sameLo, sameHi]
  · rintro u ⟨K, O, V, P, _⟩
    refine ⟨O, ?_, P, K⟩
    cases choice
    · exact val32_congr_at t₀.mem u.mem W N x x V
    · apply val32_halve_at t₀.mem u.mem W N x x
      intro i hi
      rw [V i hi, show x + 4 * i + 4 = x + 4 * (i + 1) by omega_using []]
      by_cases last : i + 1 = N
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

/-- `half`: array 27 halved in place where the mask `ecx` is all ones. -/
theorem half_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) (S : Scr s g.W g.L)
    (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0) {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa half s fun t =>
      Outside g.W (g.array 27) (4 * g.words) s.mem t.mem ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if choice then val32 s.mem g.W (g.array 27) g.words / 2 else val32 s.mem g.W (g.array 27) g.words) ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  have fit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have positive := v.minWidth
  unfold half
  refine WP.seq (WP.block_append (WP.mono (C.ptr v 27 (by decide) .ebp (by decide) (by decide))
    fun a ⟨P, Ma, Ka⟩ => ?_))
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.mono (words_ok v Ca) fun b ⟨count, Mb, Kb⟩ => ?_
  have K : Keeps [.edx, .ebp, .esi] s b := (Ka.mono (by decide)).widen Kb
  have Pb : PtrAt b g.W .ebp (g.array 27) := by rw [PtrAt, Kb.1 .ebp (by decide)]; exact P
  have M : b.mem = s.mem := Mb.trans Ma
  refine WP.mono (halfLoop_ok (choice := choice) (S.of_keeps K (by decide)) (by unfold Geometry.words; omega_using [positive])
    (by simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using [])
    (by unfold Geometry.words; omega_using [fit]) (by rw [M]; exact top) Pb count
    (by rw [K.1 .ecx (by decide)]; exact mask)) fun t ⟨O, V, Pt, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, V, Pt, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MrExponentRt

end

end


/-! # Miller–Rabin's exponent and marker, prepared at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MrExponentRt
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)
open VG.Proof.RsaKeyGen.X86.Exponent (preparedRanges ready_keep)

/-- The marker of `c − 1`: `2 ^ (v₂(c − 1) mod 64)`. -/
abbrev Marker (c : Nat) : BitVec 64 := BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)

theorem outs_prepared {g : Geometry} {d n : Nat} {m m' : Mem} (O : Outside g.W d n m m')
    (inside : ∃ R ∈ preparedRanges g, R.1 ≤ d ∧ d + n ≤ R.1 + R.2) : Outs g.W (preparedRanges g) m m' :=
  Outs.cover (Outs.of_outside O (List.mem_singleton_self _)) fun r mem => by
    obtain rfl := List.mem_singleton.mp mem
    exact inside

/-- A write within array 27, its top word or the marker above it. -/
theorem outs27 {g : Geometry} {d n : Nat} {m m' : Mem} (O : Outside g.W d n m m')
    (lo : g.array 27 ≤ d) (hi : d + n ≤ g.array 27 + 8 * g.w + 8) : Outs g.W (preparedRanges g) m m' := by
  refine outs_prepared O ⟨(g.array 27, 8 * g.w + 8), ?_, lo, by dsimp only; omega_using [hi]⟩
  simp only [preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false, or_true]

/-- The marker from the scanned pair, stored at header byte 136. -/
theorem markerStore_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (large : 1 < c)
    (selected : (s.gpr .esi ++ s.gpr .ebx).toNat =
      (c - 1) / 2 ^ (64 * ((Spec.Rsa.splitTwos (c - 1)).1 / 64)) % 2 ^ 64) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.LowBit.code ++ VG.Impl.RsaKeyGen.X86.Exponent.saveMarker)) s fun t =>
      Ready g c capacity p t ∧ word t.mem g.W 136 = Marker c ∧ Outside g.W 136 8 s.mem t.mem ∧
      Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps Exponent.clob s t := by
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentMarker.lowBit_marker (by omega_using [large]) selected)
    fun a ⟨value, Ma, Ka⟩ => ?_)
  have Ksa : Keeps Exponent.clob s a := Ka.mono (by decide)
  have Sa := S.scratch.of_keeps Ksa (by decide)
  have head := v.headerFit
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Header.storePair_ok Sa (offset := 136) (by omega_using [head]))
    fun t ⟨Mt, Ot, Kt⟩ => ?_
  have O : Outside g.W 136 8 s.mem t.mem := by rw [← Ma]; exact Ot
  have outs : Outs g.W (preparedRanges g) s.mem t.mem :=
    outs_prepared O ⟨(136, 8), by unfold preparedRanges Exponent.ranges; exact List.mem_cons_self,
      Nat.le_refl _, Nat.le_refl _⟩
  have K : Keeps Exponent.clob s t := Ksa.trans (Kt.mono (by decide))
  refine ⟨ready_keep v S outs K, ?_, O, outs, K⟩
  rw [VG.Proof.Mont.word, Mt, Mem.readW_writeW_self64, value]

theorem copyTops_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) :
    WP isa copyTops s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 27) g.words = val32 s.mem g.W (g.array 0) g.words ∧
      w32 t.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ t.gpr .ecx = cmask true ∧
      word t.mem g.W 136 = word s.mem g.W 136 ∧ Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps Exponent.clob s t := by
  have fit0 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 0) (by decide)
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have apart := VG.Proof.RsaKeyGen.X86.Prepared.paddedBefore g (i := 0) (j := 27) (by decide)
  have lo0 := v.arrayHeader 0
  have nowrap := S.scratch.nowrap
  have words : g.words = 2 * g.w := rfl
  unfold copyTops
  refine WP.seq (WP.mono (copy_ends v S.context 27 0 (by decide) (by decide)) fun a ⟨V, O, K, Ca, bp, bx⟩ => ?_)
  refine wp_movS rfl fun b B _ => ?_
  have hwb : Ws b g.W g.L := Ca.ws.of_keeps B.keeps
  have bxb : PtrAt b g.W .ebx (g.array 0 + 4 * g.words) := by rw [PtrAt, B.other .ebx (by decide)]; exact bx
  refine wp_storeS (ea_ptr hwb bxb (d := 0) (by omega_using [fit0, words]))
    (ws_write hwb (y := g.array 0 + 4 * g.words + 0) (n := 4) (by omega_using [fit0, words])) fun d D => ?_
  have hwd : Ws d g.W g.L := hwb.of_keeps (D.keeps [])
  have bpd : PtrAt d g.W .ebp (g.array 27 + 4 * g.words) := by
    rw [PtrAt, D.gpr, B.other .ebp (by decide)]; exact bp
  refine wp_storeS (ea_ptr hwd bpd (d := 0) (by omega_using [fit27, words]))
    (ws_write hwd (y := g.array 27 + 4 * g.words + 0) (n := 4) (by omega_using [fit27, words])) fun e E => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have eaxD : d.gpr .eax = 0#32 := by rw [D.gpr, B.gpr]; rfl
  have O1 : Outside g.W (g.array 0 + 4 * g.words) 4 a.mem d.mem := by
    rw [D.mem, B.mem, ← Nat.add_zero (g.array 0 + 4 * g.words)]
    exact writeW32_outside _ _ _ (by omega_using [fit0, nowrap, words])
  have O2 : Outside g.W (g.array 27 + 4 * g.words) 4 d.mem t.mem := by
    rw [T.mem, E.mem, ← Nat.add_zero (g.array 27 + 4 * g.words)]
    exact writeW32_outside _ _ _ (by omega_using [fit27, nowrap, words])
  have K' : Keeps Exponent.clob s t :=
    (((K.mono (by decide)).widen B.keeps).widen (D.keeps [])).trans ((E.keeps []).mono (by decide)) |>.widen T.keeps
  have Oall : Outs g.W (preparedRanges g) s.mem t.mem :=
    ((outs27 O (Nat.le_refl _) (by omega_using [words])).trans (outs_prepared O1
      ⟨(g.array 0 + 8 * g.w, 4), by
        unfold preparedRanges Exponent.ranges
        exact List.mem_cons_of_mem _ List.mem_cons_self, by omega_using [words], by omega_using [words]⟩)).trans
      (outs27 O2 (by omega_using []) (by omega_using [words]))
  refine ⟨ready_keep v S Oall K', ?_, ?_, by rw [T.gpr]; rfl, ?_, Oall, K'⟩
  · rw [O2.val32 (Or.inl (by omega_using [])) (by omega_using [fit27, nowrap, words]), O1.val32 (Or.inr (by omega_using [apart, words])) (by omega_using [fit27, nowrap, words])]
    exact V
  · rw [T.mem, E.mem, Nat.add_zero, w32_write_self, eaxD]
    rfl
  · rw [O2.word (Or.inl (by omega_using [apart, lo0])) (by omega_using []), O1.word (Or.inl (by omega_using [lo0])) (by omega_using []), O.word (Or.inl (by omega_using [apart, lo0])) (by omega_using [])]

theorem halfStage_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa half s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if choice then val32 s.mem g.W (g.array 27) g.words / 2 else val32 s.mem g.W (g.array 27) g.words) ∧
      w32 t.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ word t.mem g.W 136 = word s.mem g.W 136 ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Outs g.W (preparedRanges g) s.mem t.mem ∧
      Keeps Exponent.clob s t := by
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have lo := v.arrayHeader 27
  have nowrap := S.scratch.nowrap
  have words : g.words = 2 * g.w := rfl
  refine WP.mono (half_ok v S.context S.scratch top mask) fun t ⟨O, V, P, K⟩ => ?_
  have K' : Keeps Exponent.clob s t := K.mono (by decide)
  have outs := outs27 O (Nat.le_refl _) (by omega_using [words])
  refine ⟨ready_keep v S outs K', V, ?_, ?_, P, outs, K'⟩
  · rw [O.w32 (Or.inr (Nat.le_refl _)) (by omega_using [fit27, nowrap, words])]; exact top
  · rw [O.word (Or.inl (by omega_using [lo])) (by omega_using [])]

theorem halfIf_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0) {j k : Nat}
    (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3) (value : word s.mem g.W 136 = BitVec.twoPow 64 k) :
    WP isa (halfIf j) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem g.W (g.array 27) g.words / 2
          else val32 s.mem g.W (g.array 27) g.words) ∧
      w32 t.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ word t.mem g.W 136 = BitVec.twoPow 64 k ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Outs g.W (preparedRanges g) s.mem t.mem ∧
      Keeps Exponent.clob s t := by
  have head := v.headerFit
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.SigMask.code_sig S.scratch
    (by unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [head]) index choice value)
    fun a ⟨mask, M, K⟩ => ?_)
  have Ka : Keeps Exponent.clob s a := K.mono (by decide)
  have Oa : Outs g.W (preparedRanges g) s.mem a.mem := by rw [M]; exact Outs.refl _ _ _
  refine WP.mono (halfStage_ok v (ready_keep v S Oa Ka) (by rw [M]; exact top) mask)
    fun t ⟨T, V, topT, markerT, P, O, Kt⟩ => ?_
  rw [M] at V markerT
  exact ⟨T, by simpa only [decide_eq_true_eq] using V, topT, markerT.trans value, P, Oa.trans O, Ka.trans Kt⟩

theorem finish_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    (bp : PtrAt s g.W .ebp (g.array 27 + 4 * g.words)) :
    WP isa (.block finish) s fun t =>
      word t.mem g.W (g.array 27 + 4 * g.words) = word s.mem g.W 136 ∧
      Outside g.W (g.array 27 + 4 * g.words) 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  have nowrap := S.nowrap
  have words : g.words = 2 * g.w := rfl
  have hw : Ws s g.W g.L := ⟨S.wr, S.nowrap⟩
  unfold finish
  refine wp_movS (readSrc_sc S (d := 136) (by omega_using [head])) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 140) (by omega_using [head])) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have hwb := hw.of_keeps K
  have bpb : PtrAt b g.W .ebp (g.array 27 + 4 * g.words) := by rw [PtrAt, K.1 .ebp (by decide)]; exact bp
  refine wp_storeS (ea_ptr hwb bpb (d := 0) (by omega_using [fit27, words]))
    (ws_write hwb (y := g.array 27 + 4 * g.words + 0) (n := 4) (by omega_using [fit27, words])) fun d D => ?_
  have hwd := hwb.of_keeps (D.keeps [])
  have bpd : PtrAt d g.W .ebp (g.array 27 + 4 * g.words) := by rw [PtrAt, D.gpr]; exact bpb
  refine wp_storeS (ea_ptr hwd bpd (d := 4) (by omega_using [fit27, words]))
    (ws_write hwd (y := g.array 27 + 4 * g.words + 4) (n := 4) (by omega_using [fit27, words])) fun t T => WP.block_nil ?_
  have memory : t.mem = (b.mem.writeW (off g.W (g.array 27 + 4 * g.words)) (b.gpr .eax)).writeW
      (off g.W (g.array 27 + 4 * g.words) + BitVec.ofNat 64 4) (b.gpr .edx) := by
    rw [T.mem, D.mem, D.gpr, Nat.add_zero]
    congr 1
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  have pair : b.gpr .edx ++ b.gpr .eax = word s.mem g.W 136 := by
    rw [B.gpr, B.other .eax (by decide), A.gpr, A.mem,
      VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  refine ⟨?_, ?_, K.widen ((D.keeps []).trans (T.keeps []))⟩
  · rw [VG.Proof.Mont.word, memory, ← VG.Proof.Rc2.Word32.write64_pair, Mem.readW_writeW_self64, pair]
  · rw [T.mem, D.mem, Mb]
    exact ((writeW32_outside _ _ _ (by omega_using [fit27, nowrap, words])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [fit27, nowrap, words])).mono (by omega_using []) (by omega_using []))

theorem prepared_fits {g : Geometry} (v : g.Valid) : ∀ r ∈ preparedRanges g, r.1 + r.2 ≤ g.L := by
  have srcFit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 0) (by decide)
  have outFit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  intro r mem
  simp only [preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith

theorem code_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1)
    (odd : c % 2 = 1) (large : 1 < c) :
    WP isa code s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c ∧
      word t.mem g.W (g.array 27 + 8 * g.w) = Marker c ∧
      WorkspaceFrame g (preparedRanges g) s.mem t.mem ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps Exponent.clob s t := by
  have words : g.words = 2 * g.w := rfl
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have nowrap := S.scratch.nowrap
  unfold code marker
  refine WP.seq (WP.seq (WP.mono (scan_ok v S) fun a ⟨V, F, K⟩ => ?_))
  obtain ⟨Sa, Wa⟩ := Ready.keepStack v S K (by decide) (by decide) F
  have selected : (a.gpr .esi ++ a.gpr .ebx).toNat =
      (c - 1) / 2 ^ (64 * ((Spec.Rsa.splitTwos (c - 1)).1 / 64)) % 2 ^ 64 := by
    have pair := congrArg (fun q : BitVec 32 × BitVec 32 => q.2 ++ q.1) V
    dsimp only at pair
    rw [pair]
    exact VG.Proof.RsaKeyGen.X86.LowPair.first_twos (count := g.w) (by rw [← words]; exact minusOne) (by omega_using [large])
  refine WP.mono (markerStore_ok v Sa large selected) fun b ⟨Sb, markerB, _, Ob, Kb⟩ => ?_
  have candidate : val32 b.mem g.W (g.array 0) g.words = c := Sb.modulus.candidate
  refine WP.seq (WP.mono (copyTops_ok v Sb) fun d ⟨Sd, Vd, topD, maskD, markerD, Od, Kd⟩ => ?_)
  refine WP.seq (WP.mono (halfStage_ok v Sd topD maskD) fun e ⟨Se, Ve, topE, markerE, _, Oe, Ke⟩ => ?_)
  have index : (Spec.Rsa.splitTwos (c - 1)).1 % 64 < 64 := Nat.mod_lt _ (by decide)
  have markerE' : word e.mem g.W 136 = Marker c := by rw [markerE, markerD, markerB]
  refine WP.seq (WP.mono (halfIf_ok v Se topE (j := 1) index (by decide) markerE')
    fun f ⟨Sf, Vf, topF, markerF, _, Of, Kf⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_ok v Sf topF (j := 2) index (by decide) markerF)
    fun h ⟨Sh, Vh, topH, markerH, _, Oh, Kh⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_ok v Sh topH (j := 3) index (by decide) markerH)
    fun i ⟨Si, Vi, _, markerI, Pi, Oi, Ki⟩ => ?_)
  refine WP.mono (finish_ok v Si.scratch Pi) fun t ⟨wordT, Ot, Kt⟩ => ?_
  have Ot' : Outs g.W (preparedRanges g) i.mem t.mem := outs27 Ot (by omega_using []) (by omega_using [words])
  have Kall : Keeps Exponent.clob s t :=
    ((((((((K.mono (by decide)).trans Kb).trans Kd).trans Ke).trans Kf).trans Kh).trans Ki).trans
      (Kt.mono (by decide)))
  have Oall : Outs g.W (preparedRanges g) a.mem t.mem :=
    (((((Ob.trans Od).trans Oe).trans Of).trans Oh).trans Oi).trans Ot'
  have chain : val32 i.mem g.W (g.array 27) g.words =
      (let x := c / 2
       let x1 := if 1 < VG.Proof.RsaKeyGen.sigOf ((Spec.Rsa.splitTwos (c - 1)).1 % 64) then x / 2 else x
       let x2 := if 2 < VG.Proof.RsaKeyGen.sigOf ((Spec.Rsa.splitTwos (c - 1)).1 % 64) then x1 / 2 else x1
       if 3 < VG.Proof.RsaKeyGen.sigOf ((Spec.Rsa.splitTwos (c - 1)).1 % 64) then x2 / 2 else x2) := by
    rw [Vi, Vh, Vf, Ve, Vd, candidate]
    rfl
  rw [VG.Proof.RsaKeyGen.sigOf_mod] at chain
  refine ⟨ready_keep v Si Ot' (Kt.mono (by decide)), ?_, ?_, ?_, ?_, Kall⟩
  · rw [Ot.val32 (Or.inl (by omega_using [])) (by omega_using [words, fit27, nowrap])]
    exact chain.trans (VG.Proof.RsaKeyGen.mrE_halves odd)
  · rw [show g.array 27 + 8 * g.w = g.array 27 + 4 * g.words by omega_using [words], wordT, markerI]
  · exact (Wa.mono fun _ mem => nomatch mem).trans (WorkspaceFrame.of_outs nowrap Oall)
  · have first : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
      F.sub fun r mem => by
        obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by decide) S.caller.low⟩
    exact first.trans ((workspaceGlobalFrame Oall (prepared_fits v)).mono
      fun r mem => List.mem_append_left _ mem)

end VG.Proof.RsaKeyGen.X86.MrExponentRt

end

end

/-! # Preparation with Miller–Rabin's exponent at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- R² and the constants at width `g.w`, after the header (from `s` to `a`):
`Prepare.code_full_okAt` but for the exponent. -/
theorem head_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s a : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (I : Prepare.Input g c capacity p s) (A : Ready g c capacity p a)
    (Oa : Outs g.W PrepareHeader.ranges s.mem a.mem) (Ka : Keeps PrepareHeader.clob s a)
    (strideA : word a.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2))) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead name mont) a fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c ∧
      val32 t.mem g.W (g.array 5) g.words = c - 1 ∧ word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t ∧
      WorkspaceFrame g (PrepareHeader.ranges ++ PreparedR2.ranges g ++ Constants.ranges g) s.mem t.mem := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepareHead
  have minusA : val32 a.mem g.W (g.array 5) g.words = c - 1 := by
    rw [Oa.val32 (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.arrayHeader 5
      rcases mem with (rfl | rfl | rfl) | rfl <;> right <;> omega_using [this])
      (by have := I.scratch.nowrap; have := v.arrayFit (j := 5) (by decide); omega_arith)]
    exact I.minusOne
  refine WP.seq (WP.mono (PrepareRt.r2_ok verified noSp stack v length A I.odd I.top)
    fun b ⟨B, r2B, Fb, Kb, Wb⟩ => ?_)
  have strideB : word b.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change b.mem.readW (off g.W 224) 64 = _
    rw [Wb.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [PreparedR2.ranges, PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
        exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))]
    exact strideA
  have minusB := (PreparedR2.preserve v Wb (j := 5) (Or.inl rfl)).trans minusA
  refine WP.mono (PrepareRt.constants_ok verified noSp stack v length B I.odd (by have := I.large; omega_using [this]) r2B)
    fun d ⟨D, oneD, minusD, Wd, Fd, Kd⟩ => ?_
  have strideD : word d.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change d.mem.readW (off g.W 224) 64 = _
    rw [Wd.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [Constants.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;> exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))]
    exact strideB
  have minusSaved := (Constants.preserve v Wd (j := 5) (Or.inr (Or.inl rfl))).trans minusB
  have r2D := (Constants.preserve v Wd (j := 4) (Or.inl rfl)).trans r2B
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame Oa (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.headerFit
      rcases mem with (rfl | rfl | rfl) | rfl <;> omega_using [this])).mono (fun r mem => List.mem_append_left _ mem)
  have Wa : WorkspaceFrame g PrepareHeader.ranges s.mem a.mem := WorkspaceFrame.of_outs I.scratch.nowrap Oa
  refine ⟨D, r2D, oneD, minusD, minusSaved, strideD, (Fa.trans Fb).trans Fd,
    ((Ka.mono (by unfold Prepare.clob PrepareHeader.clob; decide)).widen Kb).widen Kd, ?_⟩
  exact ((Wa.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ mem))).trans
    (Wb.mono (fun _ mem => List.mem_append_left _ (List.mem_append_right _ mem)))).trans
    (Wd.mono (fun _ mem => List.mem_append_right _ mem))

/-- Preparation at the run-time width, the exponent included:
what `CandidatePrepare.code_ok` gives. -/
theorem prepared_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) {s : State} (I : CandidatePrepare.Input P s)
    (len : s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w)) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) s fun t =>
      CandidatePrepare.Ready P t ∧ WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t := by
  have G := v.geometry
  have Ip : Prepare.Input P.g P.candidate P.capacity P.p s := by
    have := I.prepare
    rw [seed] at this
    exact this
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepared
  refine WP.seq (WP.mono (PrepareHeader.prepareRt_ok G Ip.scratch Ip.caller v.length Ip.candidate Ip.odd len)
    fun h ⟨H, Oh, Kh, strideH⟩ => ?_)
  refine WP.seq (WP.mono (head_ok verified noSp stack G v.length Ip H Oh Kh strideH)
    fun d ⟨D, r2D, oneD, minusD, savedD, strideD, Fd, Kd, Wd⟩ => ?_)
  refine WP.mono (MrExponentRt.code_ok G D savedD Ip.odd (by have := Ip.large; omega_using [this]))
    fun t ⟨T, exponentT, markerT, Wt, Ft, Kt⟩ => ?_
  have preserve {j : Nat} (index : j = 4 ∨ j = 9 ∨ j = 10) :
      val32 t.mem P.g.W (P.g.array j) P.g.words = val32 d.mem P.g.W (P.g.array j) P.g.words := by
    apply Wt.val32 (G.arrayFit (by omega_using [index]))
    intro r mem
    simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl <;> rcases mem with rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_using []
  have strideT : word t.mem P.g.W 224 = BitVec.ofNat 64 (8 * (P.g.w + 2)) := by
    change t.mem.readW (off P.g.W 224) 64 = _
    rw [Wt.read64 (by have := G.headerFit; omega_using [this]) (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · right; decide
      · left; have := G.arrayHeader 0; omega
      · left; have := G.arrayHeader 27; omega)]
    exact strideD
  have W : WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem :=
    (Wd.mono (fun _ mem => List.mem_append_left _ mem)).trans (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem := Fd.trans Ft
  have data : Prepare.Data P.g P.candidate P.capacity P.p t :=
    ⟨T, (preserve (Or.inl rfl)).trans r2D, (preserve (Or.inr (Or.inl rfl))).trans oneD,
      (preserve (Or.inr (Or.inr rfl))).trans minusD, exponentT, markerT, strideT⟩
  refine ⟨⟨data, ?_, ?_, ?_, ?_, ?_⟩, W, F, Kd.trans Kt⟩
  · rw [Kt.2.1, Kt.2.2, Kd.2.1, Kd.2.2]; exact I.readable
  · rw [frame_bytesAt F (by
      intro r mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar.sub_right (below_sub (by decide) v.low)) (by have := v.randLenFit; omega_using [this])]
    exact I.entropy
  · rw [Prepare.metadata32 G W (d := 28) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.randPtr
  · rw [w32, Prepare.metadata32 G W (d := 32) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.randLength
  · rw [w32, Prepare.metadata32 G W (d := 152) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.used

end VG.Proof.RsaKeyGen.X86.MrExponentRt
