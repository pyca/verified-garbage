module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CachedGeometry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CacheMemory
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract

/-! Region geometry for the controller and its nested key-generation call. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

private theorem reads_legacy (uncached : sampling.cachedContext = false) (s : State) :
    reads sampling s = [inDomain s, inRand s, inArgs sampling s] ++ constRegs (KeyConstants.consts sampling) s := by
  simp [reads, contextReads, uncached]

private theorem argsBytes_legacy (uncached : sampling.cachedContext = false) : argsBytes sampling = 36 := by
  simp [argsBytes, uncached]

private theorem stackUse_legacy (uncached : sampling.cachedContext = false) :
    stackUse sampling = 232 := by
  simp [stackUse, GenerationPolicy.searchStack, GenerationPolicy.argumentBytes, uncached]

private theorem layout_legacy {p : KeyPublic sampling} {s : State} (h : KeyInput p s)
    (uncached : sampling.cachedContext = false) : KeyLayout (sampling := sampling) s := by
  have pre : (GenerationPolicy.legacySearchContract sampling abi (stackUse sampling)).pre
      (stripConsts (KeyConstants.consts sampling) s) := by
    cases sampling with
    | full | vetted => exact h.1
    | cached => simp [GenerationPolicy.cachedContext] at uncached
  have stackEq := stackUse_legacy uncached
  rw [stackEq] at pre
  sig_pre [GenerationPolicy.legacySearchContract, Spec.Ffdh.keySearchSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at pre
  simp only [KeyConstants.stackArg_stripConsts, KeyConstants.stackArgAddr_stripConsts] at pre
  obtain ⟨_, argsFit, rd, wr, xy, xu, xd, xr, xs, xc, xa, yu, yd, yr, ys, yc, ya,
    ud, ur, us, uc, ua, ds, dc, rs, rc, sc, sa, ca,
    stackX, stackY, stackU, stackD, stackR, stackS, stackC, stackA,
    xFit, yFit, uFit, dFit, rFit, sFit, cFit, _⟩ := pre
  have hc := h.2.2
  have rdFull : s.rd = reads sampling s := by
    rw [reads_legacy uncached]
    rw [← List.take_append_drop (s.rd.length - (KeyConstants.consts sampling).length) s.rd, hc.1]
    have typed : List.take (s.rd.length - (KeyConstants.consts sampling).length) s.rd =
        [inDomain s, inRand s, inArgs sampling s] := by
      simpa only [inDomain, inRand, inArgs, argsBytes_legacy uncached, State.addr] using rd
    exact congrArg (· ++ constRegs (KeyConstants.consts sampling) s) typed
  have constantStack (r : Region) (hr : r ∈ constRegs (KeyConstants.consts sampling) s) :
      (⟨State.addr s.sp - BitVec.ofNat 64 (stackUse sampling), (stackUse sampling)⟩ : Region).Disjoint r := by
    apply Region.Disjoint.symm
    apply (hc.2.2 r hr).2.2
    simp only [abi, stackBelow]
    exact List.mem_cons_self
  refine ⟨rdFull, wr, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [writes, reads_legacy uncached, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | ((rfl | rfl | rfl) | constant)
    · exact xFit
    · exact yFit
    · change (stackArg s 0).toNat + 8 ≤ 2 ^ 32; omega
    · exact sFit
    · change (stackArg s 8).toNat + 128 ≤ 2 ^ 32; omega
    · exact dFit
    · exact rFit
    · have addr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
      simp only [inArgs, argsBytes_legacy uncached, addr]
      change (State.addr s.sp).toNat + 36 ≤ 2 ^ 32
      have eq : (State.addr s.sp).toNat = s.sp.toNat := by
        simp only [State.addr, BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt (Nat.lt_trans s.sp.isLt (by decide))
      rw [eq]; omega
    · exact (hc.2.2 r constant).1
  · simp only [writes, List.pairwise_cons, List.Pairwise.nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, and_true]
    exact ⟨⟨xy, xu, xs, xc⟩, ⟨⟨yu, ys, yc⟩, ⟨⟨us, uc⟩, ⟨sc, fun _ => trivial⟩⟩⟩⟩
  · intro w hw r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [reads_legacy uncached, List.mem_append] at hr
    rcases hr with ordinary | constant
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ordinary
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> rcases ordinary with rfl | rfl | rfl
      · exact xd
      · exact xr
      · simpa only [inX, inArgs, argsBytes_legacy uncached, State.addr] using xa
      · exact yd
      · exact yr
      · simpa only [inY, inArgs, argsBytes_legacy uncached, State.addr] using ya
      · exact ud
      · exact ur
      · simpa only [inUsed, inArgs, argsBytes_legacy uncached, State.addr] using ua
      · exact ds.symm
      · exact rs.symm
      · simpa only [inScratch, inArgs, argsBytes_legacy uncached, State.addr] using sa
      · exact dc.symm
      · exact rc.symm
      · simpa only [inControl, inArgs, argsBytes_legacy uncached, State.addr] using ca
    · exact ((hc.2.2 r constant).2.1 w (by rw [wr]; simpa only [writes, inX, inY, inUsed, inScratch, inControl, State.addr, List.mem_cons, List.not_mem_nil, or_false] using hw)).symm
  · intro r hr
    simp only [writes, reads_legacy uncached, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | ((rfl | rfl | rfl) | constant)
    · simpa only [stackEq, inX, State.addr] using stackX
    · simpa only [stackEq, inY, State.addr] using stackY
    · simpa only [stackEq, inUsed, State.addr] using stackU
    · simpa only [stackEq, inScratch, State.addr] using stackS
    · simpa only [stackEq, inControl, State.addr] using stackC
    · simpa only [stackEq, inDomain, State.addr] using stackD
    · simpa only [stackEq, inRand, State.addr] using stackR
    · simpa only [stackEq, inArgs, argsBytes_legacy uncached, State.addr] using stackA
    · exact constantStack r constant

theorem KeyInput.layout {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    KeyLayout (sampling := sampling) s := by
  cases sampling with
  | full | vetted => exact layout_legacy h rfl
  | cached => exact cached_layout h

theorem KeyInput.constant_regions {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    constRegs (KeyConstants.consts sampling) s = KeyConstants.regions sampling p.tablePtr := by
  rw [← h.2.1]
  exact KeyConstants.regions_eq sampling s


theorem KeyInput.output_lengths {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (s.gpr .r1).toNat = p.len ∧ (s.gpr .r3).toNat = p.len := by
  cases sampling <;> (
    have pre := h.1
    cases h.2.1
    change (s.gpr .r1).toNat = (stackArg s 3).toNat ∧ (s.gpr .r3).toNat = (stackArg s 3).toNat
    sig_pre [GenerationPolicy.searchContract, GenerationPolicy.legacySearchContract,
      Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig,
      abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    simp only [KeyConstants.stackArg_stripConsts, KeyConstants.stackArgAddr_stripConsts] at pre
    sig_split pre
    constructor <;> sig_close)

theorem KeyInput.x_eq {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    inX s = ⟨State.addr p.xp, p.len⟩ := by
  have length := h.output_lengths.1
  rw [← h.2.1] at length ⊢
  change (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) = _
  rw [length]
  rfl

theorem KeyInput.y_eq {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    inY s = ⟨State.addr p.yp, p.len⟩ := by
  have length := h.output_lengths.2
  rw [← h.2.1] at length ⊢
  change (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) = _
  rw [length]
  rfl

theorem KeyInput.control_space {p : KeyPublic sampling} {s t : State} (h : KeyInput p s)
    (write : ∀ r ∈ s.wr, r ∈ t.wr) : VG.Proof.Bignum.Arm.Workspace t p.control 128 := by
  refine ⟨h.bounds.controlFit, ?_⟩
  apply write
  rw [h.layout.wr, ← h.2.1]
  simp [writes, inControl, keyOfState]

theorem KeyLive.controller {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : Controller p.control s :=
  ⟨h.input.control_space (fun _ hr => by rw [h.wr]; exact List.mem_cons_of_mem _ hr), h.pointer⟩

theorem KeyDone.controller {p : KeyPublic sampling} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) : Controller p.control s :=
  ⟨h.input.control_space (fun _ hr => by rw [h.wr]; exact List.mem_cons_of_mem _ hr), h.pointer⟩

theorem KeyInput.context_control {p : KeyPublic sampling} {s : State} (h : KeyInput p s)
    (cached : sampling.cachedContext = true) :
    (rContext p).Disjoint ⟨State.addr p.control, 128⟩ := by
  have sep := h.layout.separate (inControl s) (by simp [writes]) (inContext s)
    (by simp [reads, contextReads, cached])
  rw [← h.2.1]
  simpa only [rContext, keyOfState, cached, ite_true, inControl, inContext] using sep.symm

end VG.Proof.Ffdh.Arm.KeySearch
