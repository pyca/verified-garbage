module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairScan
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPair
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

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
    rw [ih, show start + 1 + count = start + (count + 1) by omega]
    rfl

theorem first_congr {m m' : Mem} {base : Addr} {src : Nat} (before : BitVec 32 × BitVec 32) (start count : Nat)
    (same : ∀ j < start + count, pairAt m base (src + 8 * j) = pairAt m' base (src + 8 * j)) :
    first m base src before start count = first m' base src before start count := by
  induction count generalizing before start with
  | zero => rfl
  | succ count ih =>
    change first m base src (select before (pairAt m base (src + 8 * start))) (start + 1) count =
      first m' base src (select before (pairAt m' base (src + 8 * start))) (start + 1) count
    rw [same start (by omega)]
    exact ih _ _ fun j index => same j (by omega)

theorem pairStep_ok {t : State} {W : Addr} {L y : Nat} (hw : Ws t W L) (ebp : PtrAt t W .ebp y)
    (fit : y + 8 ≤ L) :
    WP isa (.block pairStep) t fun u =>
      (u.gpr .ebx, u.gpr .esi) = select (t.gpr .ebx, t.gpr .esi) (pairAt t.mem W y) ∧ u.mem = t.mem ∧
      PtrAt u W .ebp (y + 8) ∧ u.gpr .edi = t.gpr .edi - 1 ∧ u.zf = some (t.gpr .edi - 1 == 0) ∧
      Keeps [.eax, .ecx, .edx, .ebx, .esi, .ebp, .edi] t u := by
  unfold pairStep
  simp only [List.cons_append]
  refine wp_movS (readSrc_ptr hw ebp (d := 0) (by omega)) fun a A _ => ?_
  have ebpA : PtrAt a W .ebp y := by rw [PtrAt, A.other .ebp (by decide)]; exact ebp
  refine wp_movS (readSrc_ptr (hw.of_keeps A.keeps) ebpA (d := 4) (by omega)) fun b B _ => ?_
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
  refine WP.mono (pairStep_ok (hw.of_keeps K) bp (by omega)) fun u ⟨Vu, Mu, bpu, ediu, Z, Ku⟩ => ?_
  obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf edi index
  refine ⟨⟨K.trans Ku, Mu.trans M, by rw [show y + 8 * (j + 1) = y + 8 * j + 8 by omega]; exact bpu,
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
  · rw [read (by omega)]; exact header.width
  · rw [read (by omega)]; exact header.stride
  · intro j index
    rw [read (by omega)]; exact header.pointers j index
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
  refine wp_movS (readSrc_ptr Cc.ws Cc.base (d := 48) (by have := v.headerFit; omega)) fun d D _ => ?_
  have Kd : Keeps [.ebx, .esi, .ebp, .edx] s d := Kc'.widen D.keeps
  have Sd := St.keep Kd (by decide)
  refine wp_storeS (Sd.address 0 (by decide)) (ws_write Sd.ws (y := 0) (n := 4) (by decide)) fun e E => ?_
  refine wp_movS rfl fun u U _ => WP.block_nil ?_
  have memD : d.mem = s.mem := by rw [D.mem, Mc, B.mem, A.mem]
  have ediD : d.gpr .edi = s.gpr .edi := Kd.1 .edi (by decide)
  have mem : u.mem = s.mem.writeW (off (p.setWidth 64) 0) (s.gpr .edi) := by
    rw [U.mem, E.mem, memD, ediD]
  refine ⟨mem, ?_, ?_, ?_, ?_, ?_, ((Kd.mono (by decide)).widen (E.keeps [])).widen U.keeps⟩
  · rw [mem]; exact writeW32_outside _ _ _ (by have := Sd.ws.nowrap; omega)
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
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [sp]; omega) (NoSp.of_all (by rfl)) ?_
  have St : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; omega)
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
  refine WP.seq (WP.mono (scanLoop_ok (Ci.ws.of_keeps Ka) (by omega) (by omega) P count)
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
    rw [read _ (by omega), read _ (by omega)]
  · rw [freed_mem, U.mem, Mb]
    exact frameA

end VG.Proof.RsaKeyGen.X86.MrExponentRt
