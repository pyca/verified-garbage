module

public import VerifiedGarbage.Proof.AesGcm.X86.Contiguous.Entry
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Gcm.Contiguous
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.AesGcm.X86.Contiguous.Post
public import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.CtxFrame
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.X86.Scrub
import VerifiedGarbage.Proof.Framework.X86.Rel2
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86.Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.AesGcm.X86.Contiguous
meta import VerifiedGarbage.Proof.AesGcm.X86.Scrub

/-! Bind the direct caller slots to the IA-32 workspace. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Contiguous

abbrev startCode : List Instr :=
  [.mov .eax (.reg .esp), .alu .add .eax (imm 48)] ++ saveAt ++ oPre

theorem start_run (s : State) {W : BitVec 32} (work : s.gpr .esp + 48#32 = W)
    (ww : Covers [⟨w64 W, 2560⟩] s.wr) (fits : W.toNat + 2560 ≤ 2^32) :
    ∃ t, runBlock isa startCode s = some t ∧ t.gpr .ebp = W ∧ t.gpr .esi = stOf W ∧
      t.gpr .esp = s.gpr .esp ∧ SavedAt t.mem W s ∧
      Frame [savedR W] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have ptr : ∃ u, runBlock isa [.mov .eax (.reg .esp), .alu .add .eax (imm 48)] s = some u ∧
      u.gpr .eax = W ∧ (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · regs [← work]
    · intro r h; cases r <;> first | contradiction | rfl
    all_goals rfl
  obtain ⟨u, ptr, eax, regs0, mem0, rd0, wr0⟩ := ptr
  obtain ⟨v, save, ebp, regs1, rd1, wr1, saved, frame⟩ := save_ok u eax (wr0 ▸ ww) fits
  have statePtr : ∃ t, runBlock isa oPre v = some t ∧ t.gpr .esi = stOf W ∧
      (∀ r, r ≠ .esi → t.gpr r = v.gpr r) ∧ t.mem = v.mem ∧ t.rd = v.rd ∧ t.wr = v.wr := by
    refine ⟨_, by xrun [oPre], ?_, ?_, ?_, ?_, ?_⟩
    · regs [stOf, ebp]
    · intro r h; cases r <;> first | contradiction | rfl
    all_goals rfl
  obtain ⟨t, finish, esi, regs2, mem2, rd2, wr2⟩ := statePtr
  refine ⟨t, runBlock_app_of (runBlock_app_of ptr save) finish, (regs2 _ (by decide)).trans ebp, esi,
    (regs2 _ (by decide)).trans ((regs1 _ (by decide)).trans (regs0 _ (by decide))), ?_,
    mem0 ▸ mem2 ▸ frame, rd2.trans (rd1.trans rd0), wr2.trans (wr1.trans wr0)⟩
  rw [mem2]
  obtain ⟨b, i, d, p⟩ := saved
  exact ⟨b.trans (regs0 _ (by decide)), i.trans (regs0 _ (by decide)),
    d.trans (regs0 _ (by decide)), p.trans (regs0 _ (by decide))⟩


/-- Read argument words directly above the allocated frame. The copies share
the existing argument-slot proof with the unframed routines. -/
theorem copyCallerSlots {s : State} {caller W : BitVec 32} (ps : List (Nat × Nat))
    (fields : ∀ p ∈ ps, p.1 < 10 ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0)
    (distinct : (ps.map (·.2)).Nodup)
    (esp : s.gpr .esp = caller - 2608#32) (ebp : s.gpr .ebp = W)
    (wW : Covers [⟨w64 W, 2560⟩] s.wr) (fw : W.toNat + 2560 ≤ 2^32)
    (args : Covers [argsR caller 10] (s.rd ++ s.wr))
    (apart : (argsR caller 10).Disjoint ⟨w64 W, 2560⟩)
    (fa : caller.toNat + 4 + 4 * 10 ≤ 2^32) :
    ∃ t, runBlock isa (ps.flatMap fun p => keep (callerSlot p.1) p.2) s = some t ∧
      (∀ p ∈ ps, slotv t.mem W p.2 = s.mem.readW (argA caller p.1) 32) ∧
      Frame (ps.map (keepR W)) s.mem t.mem ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  simpa only [callerAddress] using keeps_at callerSlot ps fields distinct esp ebp wW fw
    (fun i hi => callerAddress caller i ▸ args _ _ ⟨_, List.mem_singleton_self _, argA_contains hi fa⟩)
    (fun i hi => callerAddress caller i ▸ apart.sub_left (argA_sub hi fa))

/-- The nonce length is read once and written into both slots used by GCM. -/
theorem copyNonceLength {s : State} {W SP : BitVec 32}
    (esp : s.gpr .esp = SP - 2608#32) (ebp : s.gpr .ebp = W)
    (fw : W.toNat + 2560 ≤ 2^32) (hw : Covers [⟨w64 W,2560⟩] s.wr)
    (readable : InRegions (s.rd ++ s.wr) (argA SP 3) 4) :
    ∃ t, runBlock isa (keep (callerSlot 3) nO ++ ([.store (at_ .ebp nlO) .eax] : List Instr)) s = some t ∧
      t.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 nO) (s.mem.readW (argA SP 3) 32)).writeW
        (w64 W + BitVec.ofNat 64 nlO) (s.mem.readW (argA SP 3) 32) ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have ar := callerAddress SP 3
  have wrN := in_off hw (d:=nO) (n:=4) (by decide) (by decide)
  have wrL := in_off hw (d:=nlO) (n:=4) (by decide) (by decide)
  have aN : w64 (W + BitVec.ofNat 32 nO) = w64 W + BitVec.ofNat 64 nO :=
    w64_add (by unfold nO; omega)
  have aL : w64 (W + BitVec.ofNat 32 nlO) = w64 W + BitVec.ofNat 64 nlO :=
    w64_add (by unfold nlO; omega)
  refine ⟨_, by xrun [keep,esp,ebp,ar,aN,aL,wrN,wrL,readable], ?_, ?_, ?_,?_⟩
  · mems []
  · intro r hr; simp only [gpr_setMem, gpr_setReg_of_ne _ _ hr]
  all_goals rfl

/-- Record the ciphertext destination for the shared payload call, then zero
the workspace word used as the length of the trailing piece. -/
theorem finishSlots {s : State} {W SP : BitVec 32}
    (esp : s.gpr .esp = SP - 2608#32) (ebp : s.gpr .ebp = W)
    (fw : W.toNat + 2560 ≤ 2^32) (hw : Covers [⟨w64 W,2560⟩] s.wr)
    (readable : InRegions (s.rd ++ s.wr) (argA SP 7) 4)
    (slot : InRegions s.wr (w64 (SP - 2608#32)) 4) :
    ∃ t, runBlock isa [.mov .eax (argOp (callerSlot 7)), .store (at_ .esp 0) .eax,
      .mov .eax (imm 0), .store (at_ .ebp zO) .eax] s = some t ∧
      t.mem = (s.mem.writeW (w64 (SP - 2608#32)) (s.mem.readW (argA SP 7) 32)).writeW
        (w64 W + BitVec.ofNat 64 zO) (0#32) ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have ar := callerAddress SP 7
  have wrZ := in_off hw (d:=zO) (n:=4) (by decide) (by decide)
  have aZ : w64 (W + BitVec.ofNat 32 zO) = w64 W + BitVec.ofNat 64 zO :=
    w64_add (by unfold zO; omega)
  refine ⟨_, by xrun [esp,ebp,ar,aZ,wrZ,readable,slot,BitVec.add_zero], ?_, ?_,?_,?_⟩
  · mems []
  · intro r hr; simp only [gpr_setMem, gpr_setReg_of_ne _ _ hr]
  all_goals rfl

end VG.Proof.AesGcm.X86.Contiguous

/-! The contiguous seal's IA-32 stack layout and its two permitted payload layouts. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86

abbrev publicContract := Spec.Gcm.sealContiguousContract X86.abi 2640
abbrev caller (s : State) := s.gpr .esp
abbrev sp (s : State) := caller s - 2608#32
abbrev work (s : State) := sp s + 48#32
abbrev keyR (s : State) : Region := ⟨w64 (arg s 0),256⟩
abbrev ivR (s : State) : Region := ⟨w64 (arg s 2),(arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨w64 (arg s 4),(arg s 5).toNat⟩
abbrev srcR (s : State) : Region := ⟨w64 (arg s 6),(arg s 8).toNat⟩
abbrev dstR (s : State) : Region := ⟨w64 (arg s 7),(arg s 8).toNat⟩
abbrev tagR (s : State) : Region := ⟨w64 (arg s 9),16⟩
abbrev stackR (s : State) : Region := ⟨w64 (caller s)-2640#64,2640⟩
abbrev retR (s : State) : Region := ⟨w64 (caller s),4⟩
abbrev incoming (s : State) := argsR (caller s) 10
abbrev external (s : State) := [keyR s, ivR s, aadR s, srcR s, dstR s, tagR s, incoming s]

structure Layout (s : State) : Prop where
  down : 2640 ≤ (caller s).toNat
  up : (caller s).toNat + 44 ≤ 2^32
  readable : ∀ r ∈ [keyR s,ivR s,aadR s,srcR s], r ∈ s.rd ++ s.wr
  writable : ∀ r ∈ [dstR s,tagR s,incoming s], r ∈ s.wr
  sourceLayout : arg s 6 = arg s 7 ∨ (srcR s).Disjoint (dstR s)
  metadata : ∀ r ∈ [keyR s,ivR s,aadR s], r.Disjoint (dstR s)
  tag : (dstR s).Disjoint (tagR s)
  arguments : (dstR s).Disjoint (incoming s)
  stack : ∀ r ∈ external s, (stackR s).Disjoint r
  ret : ∀ r ∈ external s, (retR s).Disjoint r
  fits : ∀ r ∈ external s, r.base.toNat + r.len ≤ 2^32
  rounds : roundsOk s 1

theorem public_layout {s : State} (h : publicContract.pre s) : Layout s := by
  have widen (x y : BitVec 32) : (x.setWidth 64 = y.setWidth 64) ↔ x = y :=
    ⟨fun h => by simpa using congrArg (BitVec.setWidth 32) h, congrArg _⟩
  have small (x : BitVec 32) : x.toNat % 18446744073709551616 = x.toNat :=
    Nat.mod_eq_of_lt (by have := x.isLt; omega)
  by_cases eq : arg s 6 = arg s 7
  all_goals
    sig_pre [publicContract,Spec.Gcm.sealContiguousContract,Spec.Gcm.sealContiguousSig,
      Spec.Gcm.sealPre,X86.abi,argVal,argBytes,sw32,toNat_w64,↓reduceIte,Nat.reduceEqDiff,
      Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul,Sig.bufs,Sig.lists] at h
    simp [small,widen,eq,Sig.pairFacts,Sig.conj,List.filterMap_cons,and_assoc] at h
  case pos =>
    obtain ⟨down, up, rd, wr, kd, _, _, nd, _, _, ad, _, _, dt, dg, _, rk, rn, ra, rdst, rt, rg, sk, sn, sa, sdst, stg, sgarg, fk, fn, fa, fd, ft, rounds⟩ := h
    have sourceLayout : srcR s = dstR s := by simp [srcR,dstR,eq]
    change (caller s).toNat ≤ 4294967252 at up
    have fargs : (incoming s).base.toNat + (incoming s).len ≤ 2^32 := by
      change (w64 (caller s + 4#32)).toNat + 40 ≤ 2^32
      rw [toNat_w64,toNat_add32 (by change (caller s).toNat + 4 < 2^32; omega)]
      change (caller s).toNat + 4 + 40 ≤ 2^32
      omega
    refine ⟨down, by omega, ?_, ?_, .inl eq, ?_, dt, dg, ?_, ?_, ?_, rounds⟩
    · simp [rd, wr, keyR, ivR, aadR, srcR, w64, eq]
    · simp [wr, dstR, tagR, incoming, argsR, w64, argAddr]
    · simp only [List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      exact ⟨kd, nd, ad⟩
    · simp only [external,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true,sourceLayout]
      exact ⟨sk, sn, sa, sdst, sdst, stg, sgarg⟩
    · simp only [external,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true,sourceLayout]
      exact ⟨rk, rn, ra, rdst, rdst, rt, rg⟩
    · simp only [external,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true,sourceLayout]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fargs⟩ <;>
        simp only [toNat_w64] <;> omega
  case neg =>
    obtain ⟨down, up, rd, wr, kd, _, _, nd, _, _, ad, _, _, sd, st, sg, dt, dg, _, rk, rn, ra, rs, rdst, rt, rg, sk, sn, sa, ss, sdst, stg, sgarg, fk, fn, fa, fs, fd, ft, rounds⟩ := h
    change (caller s).toNat ≤ 4294967252 at up
    have fargs : (incoming s).base.toNat + (incoming s).len ≤ 2^32 := by
      change (w64 (caller s + 4#32)).toNat + 40 ≤ 2^32
      rw [toNat_w64,toNat_add32 (by change (caller s).toNat + 4 < 2^32; omega)]
      change (caller s).toNat + 4 + 40 ≤ 2^32
      omega
    refine ⟨down, by omega, ?_, ?_, .inr sd, ?_, dt, dg, ?_, ?_, ?_, rounds⟩
    · simp [rd, wr, keyR, ivR, aadR, srcR, w64]
    · simp [wr, dstR, tagR, incoming, argsR, w64, argAddr]
    · simp only [List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      exact ⟨kd, nd, ad⟩
    · simp only [external,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      exact ⟨sk, sn, sa, ss, sdst, stg, sgarg⟩
    · simp only [external,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      exact ⟨rk, rn, ra, rs, rdst, rt, rg⟩
    · simp only [external,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fargs⟩ <;>
        simp only [toNat_w64] <;> omega

/-- Offsets relative to the lowest address reserved for calls and the allocated frame. -/
abbrev part (s : State) (d n : Nat) : Region := ⟨(stackR s).base + BitVec.ofNat 64 d,n⟩

theorem spNat {s : State} (h : Layout s) : (sp s).toNat = (caller s).toNat - 2608 :=
  by
    have low : 2608 ≤ (caller s).toNat := by omega_using [h.down]
    change ((caller s) - 2608#32).toNat = _
    rw [BitVec.toNat_sub,BitVec.toNat_ofNat]
    have := (caller s).isLt
    omega

theorem workNat {s : State} (h : Layout s) : (work s).toNat = (sp s).toNat + 48 :=
  toNat_add32 (by omega_using [spNat h,h.up,h.down])

theorem spAddr {s : State} (h : Layout s) : w64 (sp s) = (stackR s).base + 32#64 := by
  change (caller s - 2608#32).setWidth 64 = (caller s).setWidth 64 - 2640#64 + 32#64
  rw [Taint.sub_setWidth (by omega_using [h.down] : 2608 ≤ (caller s).toNat)]
  rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem workAddr {s : State} (h : Layout s) : w64 (work s) = (stackR s).base + 80#64 := by
  change w64 (sp s + 48#32) = _
  rw [w64_add (by omega_using [spNat h,h.up,h.down] : (sp s).toNat + 48 < 2^32),spAddr h,BitVec.add_assoc]
  rfl

theorem callZone {s : State} (h : Layout s) : below (sp s) 32 = part s 0 32 := by
  rw [←below_eq (by omega_using [spNat h,h.down] : 32 ≤ (sp s).toNat)]
  change (⟨w64 (sp s) - 32#64,32⟩ : Region) = _
  rw [spAddr h,BitVec.add_sub_cancel]
  change (⟨(stackR s).base,32⟩ : Region) = ⟨(stackR s).base + 0#64,32⟩
  rw [BitVec.add_zero]

theorem partSub (s : State) {d n : Nat} (h : d+n ≤ 2640) : (part s d n).Sub (stackR s) :=
  Offset.sub_base _ h

theorem workSub {s : State} (h : Layout s) : (⟨w64 (work s),2560⟩ : Region).Sub (stackR s) := by
  rw [workAddr h]; exact partSub s (d:=80) (by decide)

theorem callSub {s : State} (h : Layout s) : (below (sp s) 32).Sub (stackR s) := by
  rw [callZone h]; exact partSub s (by decide)

theorem slotSub {s : State} (h : Layout s) : (⟨w64 (sp s),4⟩ : Region).Sub (stackR s) := by
  rw [spAddr h]; exact partSub s (d:=32) (by decide)

theorem slotWork {s : State} (h : Layout s) :
    (⟨w64 (sp s),4⟩ : Region).Disjoint ⟨w64 (work s),2560⟩ := by
  rw [spAddr h,workAddr h]
  exact Offset.disjoint _ (d:=32) (e:=80) (by decide) (by decide) (by decide)

theorem pieceRegions {s : State} (h : Layout s) :
    DirectGather.PieceRegions (arg s 0) (work s) (sp s) (arg s 6) (arg s 7) (arg s 8).toNat := by
  have ss := h.stack _ (by simp [external] : srcR s ∈ external s)
  have sd := h.stack _ (by simp [external] : dstR s ∈ external s)
  refine ⟨(ss.sub_left (workSub h)).symm,(sd.sub_left (workSub h)).symm,h.metadata _ (by simp),
    h.sourceLayout,ss.sub_left (callSub h),sd.sub_left (callSub h),slotWork h,sd.sub_left (slotSub h),
    by omega_using [spNat h,h.down,h.up],?_,?_⟩
  · simpa only [srcR,toNat_w64] using h.fits (srcR s) (by simp [external])
  · simpa only [dstR,toNat_w64] using h.fits (dstR s) (by simp [external])

/-- Map the public argument order to the existing GCM workspace. -/
def params (s : State) (text : BitVec 32) : BitVec 32 × (Nat → BitVec 32) :=
  ⟨sp s, fun i => if i = 6 then text else if i = 7 then arg s 8 else if i = 8 then work s else if i < 6 then arg s i else 0⟩

theorem oldLayout {s : State} (h : Layout s) {text : BitVec 32}
    (member : (⟨w64 text,(arg s 8).toNat⟩ : Region) ∈ external s) : OL (params s text) := by
  let W := work s
  have fw : W.toNat + 2560 ≤ 2^32 := by dsimp [W]; omega_using [workNat h,spNat h,h.up,h.down]
  have sf := stOf_w64 fw
  have sub : (⟨w64 (stOf W),80⟩ : Region).Sub ⟨w64 W,2560⟩ := by
    rw [sf]; exact Lay.wSub (by decide)
  have workAway {r : Region} (mem : r ∈ external s) := ((h.stack _ mem).sub_left (workSub h)).symm
  have callAway {r : Region} (mem : r ∈ external s) := (h.stack _ mem).sub_left (callSub h)
  have slotAway {r : Region} (mem : r ∈ external s) := (h.stack _ mem).sub_left (slotSub h)
  have kw : (below (sp s) 32).Disjoint ⟨w64 W,2560⟩ := by
    rw [callZone h]; change (part s 0 32).Disjoint ⟨w64 (work s),2560⟩
    rw [workAddr h]; exact Offset.disjoint _ (d:=0) (e:=80) (by decide) (by decide) (by decide)
  have mk : keyR s ∈ external s := by simp [external]
  have mn : ivR s ∈ external s := by simp [external]
  have ma : aadR s ∈ external s := by simp [external]
  have fit {x : BitVec 32} {n : Nat} (hh : (⟨w64 x,n⟩ : Region) ∈ external s) : x.toNat + n ≤ 2^32 := by
    simpa only [toNat_w64] using h.fits _ hh
  change OL (params s text)
  refine ⟨⟨fit mk, ?_, fw, by decide, by decide, by change 32 ≤ (sp s).toNat; omega_using [spNat h,h.down],
    (workAway mk).sub_right sub,workAway mk,?_,?_,callAway mk,kw.sub_right sub,kw⟩,
    workAway mn,workAway ma,workAway member,slotAway member,slotWork h,
    callAway mn,callAway ma,callAway member,fit mn,fit ma,fit member,h.rounds⟩
  · change (stOf W).toNat + 80 ≤ _; rw [toNat_add32 (by omega_arith)]; omega_arith
  · change (⟨w64 (stOf W),80⟩ : Region).Disjoint ⟨w64 W,16⟩
    rw [sf]; simpa only [BitVec.add_zero] using
      (Lay.w_w (W:=W) (a:=16) (n:=80) (d:=0) (k:=16) (.inr (by decide)) (by decide) (by decide))
  · change (⟨w64 (stOf W),80⟩ : Region).Disjoint _
    rw [sf]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

end VG.Proof.AesGcm.X86.Contiguous

/-! Compose the IA-32 contiguous record over the public caller's original buffers. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

abbrev srcParams (s : State) := params s (arg s 6)

/-- The straight-line setup leaves the original payload and caller metadata available
while giving the CTR callee its writable output address in the private frame. -/
structure Ready (s ref e : State) : Prop where
  o : OEnt (srcParams s) ref e
  access : DirectGather.PieceAccess e (sp s) (arg s 6) (arg s 7) (arg s 8).toNat
  ptr : e.mem.readW (argA (caller s) 7) 32 = arg s 7
  readable : InRegions (e.rd ++ e.wr) (argA (caller s) 7) 4
  tag : arg ref 8 = arg s 9
  tw : Covers [tagR s] ref.wr
  refFrame : Frame [stackR s] s.mem ref.mem
  entryFrame : Frame [stackR s] s.mem e.mem
  saved : ∀ r ∈ calleeSaved, r ≠ .esp → ref.gpr r = s.gpr r

private theorem destParams_eq (s : State) :
    destParams (srcParams s) (arg s 7) = params s (arg s 7) := by
  refine Prod.ext ?_ ?_
  · rfl
  funext i
  by_cases hi : i=6 <;> simp [destParams,srcParams,params,hi]

private theorem dstLayout {s : State} (l : Layout s) :
    OL (destParams (srcParams s) (arg s 7)) := by
  rw [destParams_eq]
  apply oldLayout l
  exact (show dstR s ∈ external s by simp [external])

private theorem writeLayout {s : State} (l : Layout s) :
    OLD (destParams (srcParams s) (arg s 7)) := by
  refine ⟨?_,?_⟩
  · exact l.metadata (keyR s) (by simp)
  · exact l.metadata (aadR s) (by simp)

private theorem workPart {s : State} (l : Layout s) (d n : Nat) (h : d+n≤2560) :
    (⟨w64 (work s)+BitVec.ofNat 64 d,n⟩ : Region).Sub (stackR s) :=
  fun x hx => workSub l x (Lay.wSub h x hx)

private theorem aadWriteSub {s : State} (l : Layout s) (text : BitVec 32) {r : Region}
    (member : r ∈ oF (params s text)) : r.Sub (stackR s) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact workPart l 16 112 (by decide)
  · exact workPart l auxO 4 (by decide)
  · exact workPart l rO 16 (by decide)
  · exact workPart l 240 2320 (by decide)
  · exact callSub l

private theorem incomingSub {s : State} (l : Layout s) :
    (⟨argA (caller s) 7,4⟩ : Region).Sub (incoming s) :=
  argA_sub (by decide) (by omega_using [l.up])

private theorem physicalArgAway {s : State} (l : Layout s) :
    ∀ r∈cipherFrame (srcParams s) (arg s 7), (⟨argA (caller s) 7,4⟩ : Region).Disjoint r := by
  intro r hr
  let p := params s (arg s 7)
  have G : OL p := oldLayout l (show dstR s ∈ external s by simp [external])
  have ht : r∈crFrame (stOf (work s)) (work s) (sp s) 32 (arg s 7) (arg s 8).toNat := hr
  obtain ⟨q,hq,sub⟩ := crFrame_oF (p:=p) G r ht
  apply Region.Disjoint.sub_right _ sub
  rcases List.mem_cons.mp hq with he|hq
  · subst q; exact l.arguments.symm.sub_left (incomingSub l)
  · have away := (l.stack (incoming s) (by simp [external])).symm
    exact (away.sub_left (incomingSub l)).sub_right (aadWriteSub l (arg s 7) hq)

private theorem aadFrame {s : State} (l : Layout s) {a b : Mem}
    (h : Frame (oF (srcParams s)) a b) : Frame [stackR s] a b :=
  h.sub fun _r hr => ⟨_,List.mem_singleton_self _,aadWriteSub l _ hr⟩

/-- The authenticated prefix leaves the original plaintext, destination pointer
and caller stack arguments available for either contiguous layout. -/
theorem afterAad {s ref e a : State} (l : Layout s) (h : Ready s ref e)
    (y : OAad (srcParams s) ref a) (f : Frame (oF (srcParams s)) e.mem a.mem) :
    PayloadPre (srcParams s) (caller s) (arg s 7) (ref,a) a := by
  have rd := y.o.rd.trans h.o.o.rd.symm
  have wr := y.o.wr.trans h.o.o.wr.symm
  have G := oldLayout l (text:=arg s 6) (show srcR s ∈ external s by simp [external])
  have argSaved := ret_oF G
  refine ⟨y,⟨?_,?_,y.o.dIn,?_⟩,?_,?_,rfl⟩
  · exact (f.readW (r:=⟨w64 (sp s),4⟩) (Region.contains_self _ _)
      (fun r hr => argSaved r (List.mem_cons_of_mem _ hr)) (by decide)).trans h.access.dstArg
  · rw [rd,wr]; exact h.access.argR
  · rw [wr]; exact h.access.wr
  · have aw := (l.stack (incoming s) (by simp [external])).symm.sub_left (incomingSub l)
    exact ((aadFrame l f).readW (r:=⟨argA (caller s) 7,4⟩) (Region.contains_self _ _)
      (fun r hr => List.mem_singleton.mp hr ▸ aw) (by decide)).trans h.ptr
  · rw [rd,wr]; exact h.readable

theorem tailPc (v : GcmImpl) {s : State} (l : Layout s) :
    Pc (fun b a => PayloadPre (srcParams s) (caller s) (arg s 7) b a ∧
        arg b.1 8=arg s 9 ∧ Covers [tagR s] b.1.wr)
      (sealTail v) (fun b a => Sealed (srcParams s) (arg s 7) (arg s 9) b.1 b.2 a) := by
  have tagMem : tagR s ∈ external s := by simp [external]
  have safe := (l.stack (tagR s) tagMem).symm
  exact sealTail_pc v _ _ _ _ rfl (oldLayout l (show srcR s ∈ external s by simp [external]))
    (dstLayout l) (writeLayout l) (pieceRegions l) (physicalArgAway l)
    (by simpa only [tagR,toNat_w64] using l.fits _ tagMem) (safe.sub_right (workSub l))
    l.tag (safe.sub_right (slotSub l)).symm

abbrev Equation (s : State) (m : Mem) :=
  encryptWith (ctxCiph s.mem (w64 (arg s 0)) (arg s 1).toNat) (ctxH s.mem (w64 (arg s 0))) 16
    (bytesAt s.mem (w64 (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (w64 (arg s 6)) (arg s 8).toNat)
    (bytesAt s.mem (w64 (arg s 4)) (arg s 5).toNat) =
    (bytesAt m (w64 (arg s 7)) (arg s 8).toNat, bytesAt m (w64 (arg s 9)) 16)

private theorem outside {s : State} (l : Layout s) {r : Region} (hr : r∈external s) :
    ∀ q ∈ [stackR s], r.Disjoint q := by
  intro q hq
  obtain rfl := List.mem_singleton.mp hq
  exact (l.stack r hr).symm

private theorem sourceEquation {s ref e a z : State} (l : Layout s) (h : Ready s ref e)
    (f : Frame (oF (srcParams s)) e.mem a.mem) (out : Sealed (srcParams s) (arg s 7) (arg s 9) ref a z) :
    Equation s z.mem := by
  have ⟨key,hash⟩ := Proof.AesGcm.ctx_frame h.refFrame (outside l (r:=keyR s) (by simp [external])) l.rounds
  have iv := Proof.Cmac.bytesAt_frame h.refFrame (outside l (r:=ivR s) (by simp [external])) (by omega_using [(arg s 3).isLt])
  have ad := Proof.Cmac.bytesAt_frame h.refFrame (outside l (r:=aadR s) (by simp [external])) (by omega_using [(arg s 5).isLt])
  have pt := Proof.Cmac.bytesAt_frame (h.entryFrame.trans (aadFrame l f)) (outside l (r:=srcR s) (by simp [external]))
    (by omega_using [(arg s 8).isLt])
  have result := out.result
  change encryptWith (ctxCiph ref.mem (w64 (arg s 0)) (arg s 1).toNat) (ctxH ref.mem (w64 (arg s 0))) 16
    (bytesAt ref.mem (w64 (arg s 2)) (arg s 3).toNat) (bytesAt a.mem (w64 (arg s 6)) (arg s 8).toNat)
    (bytesAt ref.mem (w64 (arg s 4)) (arg s 5).toNat) = _ at result
  rw [key,hash,iv,ad,pt] at result
  exact result

theorem publicPost {s z : State} (eqn : Equation s z.mem) : publicContract.post s z := by
  sig_post [publicContract,Spec.Gcm.sealContiguousContract,Spec.Gcm.sealContiguousSig,
    Spec.Gcm.sealContiguousPost,X86.abi,argVal,argBytes,sw32,toNat_w64,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul]
  intro key hk
  obtain ⟨cipher,hash,_⟩ := Proof.AesGcm.keyRounds_ctx hk
  unfold Equation at eqn
  rwa [cipher,hash,←Spec.Gcm.encrypt_eq] at eqn

theorem retOutside (s : State) : (retR s).Disjoint (stackR s) := by
  have pos : w64 (caller s)=(stackR s).base+2640#64 := by
    change _=w64 (caller s)-2640#64+2640#64
    rw [BitVec.sub_add_cancel]
  unfold retR
  rw [pos]
  exact Offset.disjoint_base _ (by decide) (by decide)

private theorem tagWriteSub {s : State} (l : Layout s) {r : Region}
    (hr : r∈oT (params s (arg s 7)) 0) : r.Sub (stackR s) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact workPart l 16 48 (by decide)
  · exact workPart l 96 16 (by decide)
  · exact workPart l 0 16 (by decide)
  · exact workPart l 240 2320 (by decide)
  · exact callSub l

private theorem retSeal {s : State} (l : Layout s) :
    ∀ r∈sealWrites (srcParams s) (arg s 7) (arg s 9), (retR s).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with text|tag
  · rcases List.mem_cons.mp text with h|h
    · subst r; exact (retOutside s).sub_right (workPart l dataO 4 (by decide))
    · let p := params s (arg s 7)
      have G : OL p := oldLayout l (show dstR s ∈ external s by simp [external])
      have hr : r∈crFrame (stOf (work s)) (work s) (sp s) 32 (arg s 7) (arg s 8).toNat := h
      obtain ⟨q,hq,sub⟩ := crFrame_oF (p:=p) G r hr
      apply Region.Disjoint.sub_right _ sub
      rcases List.mem_cons.mp hq with eq|rest
      · subst q; exact l.ret (dstR s) (by simp [external])
      · exact (retOutside s).sub_right (aadWriteSub l (arg s 7) rest)
  · rcases List.mem_cons.mp tag with h|h
    · subst r; exact l.ret (tagR s) (by simp [external])
    · rw [destParams_eq] at h
      exact (retOutside s).sub_right (tagWriteSub l h)

structure Done (s z : State) : Prop where
  saved : ∀ r ∈ calleeSaved, r≠.esp → z.gpr r=s.gpr r
  sp : z.gpr .esp=sp s
  ret : z.mem.readW (w64 (caller s)) 32=s.mem.readW (w64 (caller s)) 32
  eqn : Equation s z.mem

theorem afterSetup_wp (v : GcmImpl) {s ref e : State} (l : Layout s) (h : Ready s ref e) :
    WP isa (.seq (oneAad v.callees) (sealTail v)) e (Done s) := by
  let p := srcParams s
  have G : OL p := oldLayout l (show srcR s ∈ external s by simp [external])
  refine WP.seq (((oneAad_pc (vg:=v) G).wp (ref,e) e ⟨h.o,rfl⟩).mono ?_)
  intro a ha
  have pay := (tailPc v l).wp (ref,a) a ⟨afterAad l h ha.1 ha.2,h.tag,h.tw⟩
  refine pay.mono fun z out => ⟨?_,?_,?_,sourceEquation l h ha.2 out⟩
  · intro r hr ne
    exact ((out.abi.1 r hr).trans (VG.X86.RegUpd.gpr_setReg_of_ne _ _ ne)).trans (h.saved r hr ne)
  · exact (out.abi.1 .esp (by decide)).trans (VG.X86.RegUpd.gpr_setReg_self ..)
  · have q : z.mem.readW (w64 (caller s)) 32=a.mem.readW (w64 (caller s)) 32 := out.frame.readW (r:=retR s) (Region.contains_self _ _) (retSeal l) (by decide)
    have f := h.entryFrame.trans (aadFrame l ha.2)
    exact q.trans (f.readW (r:=retR s) (Region.contains_self _ _)
      (fun _ hr => List.mem_singleton.mp hr ▸ retOutside s) (by decide))

end VG.Proof.AesGcm.X86.Contiguous

/-! The caller's argument slots and the private workspace during the IA-32 prologue. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Contiguous

abbrev allocated (s : State) := allocFrame 2608 s
abbrev workR (s : State) : Region := ⟨w64 (work s),2560⟩
abbrev tempR (s : State) : Region := ⟨w64 (sp s),4⟩
abbrev cell (s : State) (offset : Nat) : Region := ⟨w64 (work s) + BitVec.ofNat 64 offset,4⟩
abbrev firstArgs : List (Nat × Nat) := [(0,ctxO),(1,roundsO),(2,dO)]
abbrev nonceArgs : List (Nat × Nat) := [(3,nO),(3,nlO)]
abbrev otherArgs : List (Nat × Nat) := [(4,aadO),(5,alO),(6,dataO),(8,lenO),(9,tpO)]

structure Bound (s : State) (ps : List (Nat × Nat)) (t : State) : Prop where
  bp : t.gpr .ebp = work s
  si : t.gpr .esi = stOf (work s)
  st : t.gpr .esp = sp s
  rd : t.rd = (allocated s).rd
  wr : t.wr = (allocated s).wr
  saved : SavedAt t.mem (work s) (allocated s)
  slots : ∀ p ∈ ps, slotv t.mem (work s) p.2 = arg s p.1
  frame : Frame [stackR s] s.mem t.mem

theorem allocatedWork {s : State} (l : Layout s) : Covers [workR s] (allocated s).wr := by
  apply Covers.of_sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_,List.mem_cons_self,48,?_,by change 48+2560≤2608; decide⟩
  exact w64_add (by omega_using [spNat l,l.up,l.down])

theorem allocatedSlot {s : State} : Covers [tempR s] (allocated s).wr := by
  apply Covers.of_sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_,List.mem_cons_self,0,(BitVec.add_zero _).symm,by change 0+4≤2608; decide⟩

theorem workFit {s : State} (l : Layout s) : (work s).toNat + 2560 ≤ 2^32 := by
  omega_using [workNat l,spNat l,l.up,l.down]

theorem allocatedArgs {s : State} (l : Layout s) :
    Covers [incoming s] ((allocated s).rd ++ (allocated s).wr) :=
  Covers.of_mem fun _ h => List.mem_singleton.mp h ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (l.writable (incoming s) (by simp)))

theorem Bound.args {s t : State} {ps} (b : Bound s ps t) (l : Layout s) {i : Nat} (hi : i < 10) :
    t.mem.readW (argA (caller s) i) 32 = arg s i := by
  apply b.frame.readW (r:=⟨argA (caller s) i,4⟩) (Region.contains_self _ _)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((l.stack _ (by simp [external] : incoming s ∈ external s)).symm).sub_left
      (argA_sub hi (by omega_using [l.up]))
  · decide

theorem Bound.advance {s t u : State} {ps qs : List (Nat × Nat)} (b : Bound s ps t)
    {regions : List Region} (writes : Frame regions t.mem u.mem)
    (small : ∀ r ∈ regions, r.Sub (stackR s))
    (saved : ∀ r ∈ regions, (savedR (work s)).Disjoint r)
    (apart : ∀ p ∈ ps, ∀ r ∈ regions, (cell s p.2).Disjoint r)
    (slots : ∀ p ∈ qs, slotv u.mem (work s) p.2 = arg s p.1)
    (g : ∀ r, r ≠ .eax → u.gpr r = t.gpr r) (rd : u.rd=t.rd) (wr : u.wr=t.wr) :
    Bound s (qs ++ ps) u := by
  refine ⟨(g _ (by decide)).trans b.bp,(g _ (by decide)).trans b.si,(g _ (by decide)).trans b.st,
    rd.trans b.rd,wr.trans b.wr,b.saved.frame writes saved,?_,
    b.frame.trans (writes.sub fun r hr => ⟨_,List.mem_singleton_self _,small r hr⟩)⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact slots p h
  · exact (slot_frame writes (apart p h)).trans (b.slots p h)

theorem startBound {s : State} (l : Layout s) :
    ∃ t, runBlock isa startCode (allocated s) = some t ∧ Bound s [] t := by
  obtain ⟨t,run,bp,si,st,saved,frame,rd,wr⟩ := start_run (allocated s)
    (W:=work s) (by rw [allocFrame_esp]) (allocatedWork l) (workFit l)
  refine ⟨t,run,bp,si,st.trans (allocFrame_esp ..),rd,wr,saved,by simp,?_⟩
  exact frame.sub fun r hr => ⟨_,List.mem_singleton_self _, List.mem_singleton.mp hr ▸
    (fun a hc => workSub l a (Lay.wSub (by decide : 128+16≤2560) a hc))⟩

theorem Bound.copy {s t : State} {ps} (b : Bound s ps t) (l : Layout s) (qs : List (Nat × Nat))
    (fields : ∀ p ∈ qs, p.1 < 10 ∧ 144 ≤ p.2 ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0)
    (old : ∀ p ∈ ps, p.2+4 ≤ 2560)
    (apart : ∀ p ∈ ps, ∀ q ∈ qs, p.2+4 ≤ q.2 ∨ q.2+4 ≤ p.2)
    (unique : (qs.map (·.2)).Nodup) :
    ∃ u, runBlock isa (qs.flatMap fun p => keep (callerSlot p.1) p.2) t = some u ∧ Bound s (qs ++ ps) u := by
  obtain ⟨u,run,slots,frame,g,rd,wr⟩ := copyCallerSlots qs (fun p hp => ⟨(fields p hp).1,(fields p hp).2.2⟩)
    unique b.st b.bp (b.wr ▸ allocatedWork l) (workFit l) (by rw [b.rd,b.wr]; exact allocatedArgs l)
    (((l.stack _ (by simp [external] : incoming s ∈ external s)).sub_left (workSub l)).symm)
    (by omega_using [l.up])
  refine ⟨u,run,b.advance frame ?_ ?_ ?_ (fun p hp => (slots p hp).trans (b.args l (fields p hp).1)) g rd wr⟩
  · intro r hr; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact fun a hc => workSub l a (Lay.wSub (fields q hq).2.2.1 a hc)
  · intro r hr; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact Lay.w_w (.inl (fields q hq).2.1) (by decide) (fields q hq).2.2.1
  · intro p hp r hr; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact Lay.w_w (apart _ hp _ hq) (old _ hp) (fields q hq).2.2.1

theorem Bound.nonce {s t : State} {ps} (b : Bound s ps t) (l : Layout s)
    (old : ∀ p ∈ ps, p.2+4 ≤ 2560)
    (apart : ∀ p ∈ ps, ∀ q ∈ nonceArgs, p.2+4 ≤ q.2 ∨ q.2+4 ≤ p.2) :
    ∃ u, runBlock isa (keep (callerSlot 3) nO ++ ([.store (at_ .ebp nlO) .eax] : List Instr)) t = some u ∧
      Bound s (nonceArgs ++ ps) u := by
  have read := allocatedArgs l _ _ ⟨_,List.mem_singleton_self _,argA_contains (by decide : 3 < 10)
    (by omega_using [l.up])⟩
  obtain ⟨u,run,mem,g,rd,wr⟩ := copyNonceLength b.st b.bp (workFit l) (b.wr ▸ allocatedWork l)
    (by rw [b.rd,b.wr]; exact read)
  let regions := nonceArgs.map (keepR (work s))
  have fr : Frame regions t.mem u.mem := by
    rw [mem]
    apply Frame.writeW _ (by simp [regions,keepR]) _ (Region.contains_self _ _)
    exact (Frame.refl _ _).writeW (by simp [regions,keepR]) _ (Region.contains_self _ _)
  have fields : ∀ q ∈ nonceArgs, 144 ≤ q.2 ∧ q.2+4 ≤ 2560 := by decide
  refine ⟨u,run,b.advance fr ?_ ?_ ?_ ?_ g rd wr⟩
  · intro r hr; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact fun a hc => workSub l a (Lay.wSub (fields _ hq).2 a hc)
  · intro r hr; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact Lay.w_w (.inl (fields _ hq).1) (by decide) (fields _ hq).2
  · intro p hp r hr; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact Lay.w_w (apart p hp q hq) (old p hp) (fields _ hq).2
  · intro p hp
    simp only [nonceArgs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · rw [slotv_eq,mem,Mem.readW_writeW_sep (Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32]
      exact b.args l (by decide)
    · rw [slotv_eq,mem,Mem.readW_writeW_self32]; exact b.args l (by decide)

abbrev allArgs := otherArgs ++ (nonceArgs ++ (firstArgs ++ []))

abbrev endCode : List Instr :=
  [.mov .eax (argOp (callerSlot 7)), .store (at_ .esp 0) .eax,
   .mov .eax (imm 0), .store (at_ .ebp zO) .eax]

theorem Bound.finish {s t : State} (b : Bound s allArgs t) (l : Layout s) :
    ∃ u, runBlock isa endCode t = some u ∧ Bound s allArgs u ∧
      slotv u.mem (work s) zO = 0 ∧ u.mem.readW (w64 (sp s)) 32 = arg s 7 := by
  have get := allocatedArgs l _ _ ⟨_,List.mem_singleton_self _,argA_contains (by decide : 7 < 10)
    (by omega_using [l.up])⟩
  have slot := allocatedSlot (s:=s) _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩
  obtain ⟨u,run,mem,g,rd,wr⟩ := finishSlots b.st b.bp (workFit l) (b.wr ▸ allocatedWork l)
    (by rw [b.rd,b.wr]; exact get) (b.wr ▸ slot)
  let regions := [tempR s,cell s zO]
  have fr : Frame regions t.mem u.mem := by
    rw [mem]
    apply Frame.writeW _ (by simp [regions,cell]) _ (Region.contains_self _ _)
    exact (Frame.refl _ _).writeW (by simp [regions,tempR,sp]) _ (Region.contains_self _ _)
  have sep := (slotWork l).sub_right (Lay.wSub (by decide : zO+4≤2560))
  refine ⟨u,run,b.advance (qs:=[]) fr ?_ ?_ ?_ (by simp) g rd wr,?_,?_⟩
  · intro r hr; rcases List.mem_cons.mp hr with rfl | hr
    · exact slotSub l
    · obtain rfl := List.mem_singleton.mp hr; exact fun a hc => workSub l a (Lay.wSub (by decide) a hc)
  · intro r hr; rcases List.mem_cons.mp hr with rfl | hr
    · exact (slotWork l).symm.sub_left (Lay.wSub (by decide))
    · obtain rfl := List.mem_singleton.mp hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · have bounds : ∀ p ∈ allArgs, p.2+4≤2560 ∧ (p.2+4≤zO ∨ zO+4≤p.2) := by decide
    intro p hp r hr; rcases List.mem_cons.mp hr with rfl | hr
    · exact (slotWork l).symm.sub_left (Lay.wSub (bounds _ hp).1)
    · obtain rfl := List.mem_singleton.mp hr; exact Lay.w_w (bounds _ hp).2 (bounds _ hp).1 (by decide)
  · rw [slotv_eq,mem,Mem.readW_writeW_self32]; rfl
  · rw [mem,Mem.readW_writeW_sep (sep.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),Mem.readW_writeW_self32]
    exact b.args l (by decide)

theorem setupSlots {s : State} (l : Layout s) :
    ∃ t, runBlock isa setup (allocated s) = some t ∧ Bound s allArgs t ∧
      slotv t.mem (work s) zO = 0 ∧ t.mem.readW (w64 (sp s)) 32 = arg s 7 := by
  obtain ⟨t0,a,h0⟩ := startBound l
  obtain ⟨t1,b,h1⟩ := h0.copy l firstArgs (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t2,c,h2⟩ := h1.nonce l (by decide) (by decide)
  obtain ⟨t3,d,h3⟩ := h2.copy l otherArgs (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t4,e,h4,z,dst⟩ := h3.finish l
  have run := runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of a b) c) d) e
  have code : setup = startCode ++ (firstArgs.flatMap fun p => keep (callerSlot p.1) p.2) ++
      (keep (callerSlot 3) nO ++ ([.store (at_ .ebp nlO) .eax] : List Instr)) ++
      (otherArgs.flatMap fun p => keep (callerSlot p.1) p.2) ++ endCode := by
    simp [setup,startCode,oPre,firstArgs,otherArgs,endCode,List.append_assoc]
  exact ⟨t4,code ▸ run,h4,z,dst⟩

end VG.Proof.AesGcm.X86.Contiguous

/-! Connect the physical prologue to the GCM pieces' private calling convention. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Contiguous

/-- The old GCM pieces number the detached tag at argument 8. Rebase their
reference stack by one word, retaining the post-setup memory and permissions. -/
private def reference (s t : State) : State :=
  { s.setReg .esp (caller s + 4#32) with mem := t.mem, rd := t.rd, wr := t.wr }

private theorem referenceTag {s t : State} (b : Bound s allArgs t) (l : Layout s) :
    arg (reference s t) 8 = arg s 9 := by
  have addr : (caller s + 4#32) + 36#32 = caller s + 40#32 := BitVec.add_assoc _ _ _
  change t.mem.readW (w64 ((caller s + 4#32) + 36#32)) 32 = arg s 9
  exact (congrArg (fun v => t.mem.readW (w64 v) 32) addr).trans (b.args (i:=9) l (by decide))

private theorem referenceSaved {s t : State} (b : Bound s allArgs t) :
    SavedAt t.mem (work s) (reference s t) := by
  obtain ⟨b0,b1,b2,b3⟩ := b.saved
  exact ⟨b0,b1,b2,b3⟩

private theorem Bound.readable {s t : State} {ps} (b : Bound s ps t) {r : Region} (mem : r ∈ s.rd ++ s.wr) : Covers [r] (t.rd ++ t.wr) := by
  rw [b.rd,b.wr]
  apply Covers.of_mem
  intro q hq
  obtain rfl := List.mem_singleton.mp hq
  rcases List.mem_append.mp mem with hm | hm
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)

private theorem Bound.writable {s t : State} {ps} (b : Bound s ps t) {r : Region} (mem : r ∈ s.wr) : Covers [r] t.wr := by
  rw [b.wr]
  exact Covers.of_mem fun q hq => List.mem_singleton.mp hq ▸ List.mem_cons_of_mem _ mem

private theorem readyOfBindings {s t : State} (l : Layout s) (b : Bound s allArgs t)
    (zero : slotv t.mem (work s) zO = 0) (dst : t.mem.readW (w64 (sp s)) 32 = arg s 7) :
    Ready s (reference s t) t := by
  have wk := b.wr ▸ allocatedWork l
  have stmem : Covers [⟨w64 (stOf (work s)),80⟩] t.wr := by
    apply Covers.trans _ wk
    apply Covers.of_sub
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨_,List.mem_singleton_self _,16,stOf_w64 (workFit l),by change 16+80≤2560; decide⟩
  have spmem : Covers [tempR s] t.wr := b.wr ▸ allocatedSlot
  have src := b.readable (l.readable (srcR s) (by simp))
  have iv := b.readable (l.readable (ivR s) (by simp))
  have aad := b.readable (l.readable (aadR s) (by simp))
  have key := b.readable (l.readable (keyR s) (by simp))
  have tag := referenceTag b l
  have sv := referenceSaved b
  have env : Env (arg s 0) (stOf (work s)) (work s) (sp s) t :=
    ⟨b.bp,b.si,b.st,key,stmem,wk,b.slots (0,ctxO) (by decide)⟩
  have rounds : RoundsAt t.mem (work s) (arg s 1).toNat :=
    ⟨(b.slots (1,roundsO) (by decide)).trans (ofNat_toNat32 _).symm,l.rounds⟩
  have o : OEnv (srcParams s) (reference s t) t :=
    ⟨env,rounds,b.slots (4,aadO) (by decide),b.slots (5,alO) (by decide),b.slots (6,dataO) (by decide),
     b.slots (8,lenO) (by decide),zero,b.slots (3,nlO) (by decide),(b.slots (9,tpO) (by decide)).trans tag.symm,
     sv,rfl,rfl,rfl,rfl,rfl,rfl,iv,aad,src⟩
  refine ⟨⟨o,b.slots (2,dO) (by decide),b.slots (3,nO) (by decide),rfl,rfl,Frame.refl _ _⟩,
    ⟨dst,spmem.right,src,b.writable (l.writable (dstR s) (by simp))⟩,b.args (i:=7) l (by decide),?_,tag,
    b.writable (l.writable (tagR s) (by simp)),b.frame,b.frame,?_⟩
  · rw [b.rd,b.wr]
    exact allocatedArgs l _ _ ⟨_,List.mem_singleton_self _,argA_contains (by decide : 7<10) (by omega_using [l.up])⟩
  · intro r _ hr; simp [reference,State.setReg,hr]

theorem setupReady {s : State} (l : Layout s) :
    WP isa (.block setup) (allocated s) fun t => ∃ ref, Ready s ref t := by
  obtain ⟨t,run,b,z,d⟩ := setupSlots l
  exact WP.of_runBlock ⟨t,run,_,readyOfBindings l b z d⟩

end VG.Proof.AesGcm.X86.Contiguous

/-! The contiguous IA-32 public entry, including the allocation and release of its private frame. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86

abbrev SetupOk := ∀ s : State, Layout s →
  WP isa (.block Impl.AesGcm.X86.Contiguous.setup) (Gather.allocated 2608 s) fun e => ∃ ref, Ready s ref e

private theorem srcParams_eq {s t : State} (h : pubN 10 s t) : srcParams t=srcParams s := by
  have sp : Contiguous.sp t=Contiguous.sp s := congrArg (·-2608#32) h.1.symm
  refine Prod.ext sp ?_
  funext i
  by_cases six : i=6
  · subst i; exact (h.2 6 (by decide)).symm
  by_cases seven : i=7
  · subst i; exact (h.2 8 (by decide)).symm
  by_cases eight : i=8
  · subst i; exact congrArg (·+48#32) sp
  by_cases publicWord : i<6
  · simpa only [srcParams,params,six,seven,eight,publicWord,ite_true,ite_false] using (h.2 i (by omega)).symm
  · simp only [srcParams,params,six,seven,eight,publicWord,ite_false]

private theorem fixedCT {P : State → Prop} {c : Prog isa} {s t : State}
    (ct : CT P c) (hs : P s) (ht : P t) : RelCT isa (Eq2 s t) c TT :=
  RelCT.mono ct (fun _ _ ⟨rfl,rfl⟩ => ⟨hs,ht⟩) fun _ _ _ => trivial

theorem afterSetup_rel (v : GcmImpl) {s t ref ref' e e' : State} (l : Layout s) (l' : Layout t)
    (hp : pubN 10 s t) (h : Ready s ref e) (k : Ready t ref' e') :
    RelCT isa (Eq2 e e') (.seq (oneAad v.callees) (sealTail v)) TT := by
  have p := srcParams_eq hp
  have j := oneAad_pc (vg:=v) (oldLayout l (show srcR s∈external s by simp [external]))
  have ko : OEnt (srcParams s) ref' e' := p ▸ k.o
  refine rel_seq (fixedCT j.ct ⟨(ref,e),h.o,rfl⟩ ⟨(ref',e'),ko,rfl⟩)
    (j.wp (ref,e) e ⟨h.o,rfl⟩) (j.wp (ref',e') e' ⟨ko,rfl⟩) ?_
  intro a b ha hb
  change OAad (srcParams s) ref' b ∧ Frame (oF (srcParams s)) e'.mem b.mem at hb
  rw [←p] at hb
  have kb := afterAad l' k hb.1 hb.2
  have tc := tailPc v l
  refine fixedCT tc.ct ⟨(ref,a),afterAad l h ha.1 ha.2,h.tag,h.tw⟩ ⟨(ref',b),?_,?_,?_⟩
  · rw [←p,show caller s=caller t from hp.1,hp.2 7 (by decide)]; exact kb
  · exact k.tag.trans (hp.2 9 (by decide)).symm
  · simpa only [tagR,hp.2 9 (by decide)] using k.tw

theorem publicArgs {s t : State} (hp : publicContract.pub s t) : pubN 10 s t := by
  sig_pub [publicContract,Spec.Gcm.sealContiguousContract,Spec.Gcm.sealContiguousSig,Spec.Gcm.sealPre,
    X86.abi,argVal,↓reduceIte,Nat.reduceEqDiff,argBytes,Nat.reduceDiv,List.sum_cons,List.sum_nil,
    Nat.reduceAdd,Nat.reduceMul,sw32,toNat_w64] at hp
  obtain ⟨sp,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩ := hp
  refine ⟨sp, fun i hi => ?_⟩
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  exacts [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]

theorem constantTime (v : GcmImpl) (setup : SetupOk) :
    ConstantTime isa publicContract.pre publicContract.pub (Impl.AesGcm.X86.Contiguous.sealContiguous v.callees) := by
  apply ct_of
  intro s t hs ht pub
  have hp := publicArgs pub
  have l := public_layout hs
  have l' := public_layout ht
  apply Gather.rel_alloc
  refine rel_seq (setup_rel (congrArg (·-2608#32) hp.1)) (setup s l) (setup t l') ?_
  intro a b ha hb
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  exact afterSetup_rel v l l' hp hx hy

open VG.Impl.AesGcm.X86.Contiguous (body sealContiguous)

/-- The shared body preserves the hardware stack pointer between allocation and release. -/
theorem bodySafe (v : GcmImpl) : (body v.callees).all (fun i => !isa.writesSp i)=true := by
  simp only [body,Open.decTo,Open.wholeTo,Open.ctrToCall,absorb,absorbHead,absorbWhole,ctrCall,flush,
    ghCall,ghash1,j0,j0hash,lens,oneAad,oneTag,tag,tagOut,Code.all,GcmImpl.callees,
    v.ctr.spSafe,v.gh.spSafe,Bool.and_true]
  decide +kernel

theorem coreSafe (v : GcmImpl) : (sealContiguous v.callees).all (fun i => !isa.writesSp i)=true := by
  change ((true && _) && true)=true
  rw [bodySafe]; rfl

private theorem releaseSub {s : State} (l : Layout s) : (below (caller s) 2608).Sub (stackR s) := by
  have st : below (caller s) 2640=stackR s := (below_eq l.down).symm
  rw [←st]
  exact X86.below_sub (by decide) l.down

private theorem releaseEqn {s z : State} (l : Layout s) {m : Mem} (h : Equation s z.mem)
    (f : Frame [below (caller s) 2608] z.mem m) : Equation s m := by
  have away {r : Region} (hr : r∈external s) : ∀ q∈[below (caller s) 2608], r.Disjoint q :=
    fun _ hq => List.mem_singleton.mp hq ▸ (l.stack _ hr).symm.sub_right (releaseSub l)
  exact h.trans (Prod.ext (Proof.Cmac.bytesAt_frame f (away (r:=dstR s) (by simp [external])) (by omega_using [(arg s 8).isLt])).symm
    (Proof.Cmac.bytesAt_frame f (away (r:=tagR s) (by simp [external])) (by decide)).symm)

theorem correct (v : GcmImpl) (setup : SetupOk) (s : State) (hs : publicContract.pre s) :
    WP isa (sealContiguous v.callees) s fun z => abiPreserved s z ∧ publicContract.post s z := by
  have l := public_layout hs
  apply Gather.WP.alloc ⟨by decide,by decide,by decide⟩ (by change 2608≤(caller s).toNat; omega_using [l.down])
    (VG.X86.noSp_of_all (bodySafe v))
  refine WP.seq ((setup s l).mono ?_)
  intro e he
  obtain ⟨ref,h⟩ := he
  refine (afterSetup_wp v l h).mono ?_
  intro out done m u f
  refine ⟨⟨?_,?_⟩,publicPost (releaseEqn l done.eqn f)⟩
  · intro r hr
    by_cases eq : r=.esp
    · subst r
      change out.gpr .esp+2608#32=caller s
      rw [done.sp]; exact BitVec.sub_add_cancel _ _
    · exact (gpr_setReg_of_ne _ _ eq).trans (done.saved r hr eq)
  · change m.readW (w64 (caller s)) 32=_
    refine Eq.trans (f.readW (r:=retR s) (Region.contains_self _ _) ?_ (by decide)) done.ret
    exact fun _ hq => List.mem_singleton.mp hq ▸ (retOutside s).sub_right (releaseSub l)

def witness : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := fun a => if a=0x8005 then 0x10 else if a=0x8008 then 10 else if a=0x8029 then 0x50 else 0
  rd := [⟨0x1000,256⟩,⟨0,0⟩,⟨0,0⟩]
  wr := [⟨0,0⟩,⟨0x5000,16⟩,⟨0x8004,40⟩]

theorem satisfiable : ∃ s, publicContract.pre s := by
  refine ⟨witness,?_⟩
  sig_pre [publicContract,Spec.Gcm.sealContiguousContract,Spec.Gcm.sealContiguousSig,Spec.Gcm.sealPre,
    X86.abi,argVal,argSlots,argBytes,sw32,toNat_w64,↓reduceIte,Nat.reduceEqDiff,Nat.reduceDiv,
    List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul,Sig.bufs,Sig.lists,
    witness,arg,argAddr,Mem.readW,Mem.read]
  simp
  repeat' apply And.intro
  all_goals first | decide | exact Region.disjoint_of_sep (by decide)

theorem verified (v : GcmImpl) (setup : SetupOk) : Verified target (sealContiguous v.callees) publicContract :=
  ⟨correct v setup,constantTime v setup,satisfiable⟩

end VG.Proof.AesGcm.X86.Contiguous

/-! Scrub the private IA-32 frame and caller-scratch registers after sealing. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG VG.X86 VG.X86.Scrub VG.Impl.AesGcm.X86

theorem public_postOut : VG.X86.Scrub.PostOut publicContract 0 := by
  apply VG.X86.Scrub.postOut_of_local (leak := none) VG.X86.Scrub.ScrubAbi.plain
  intro vs _ _ _ _ hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nl, aad, al, src, dst, len, tag], _ =>
    by_cases eq : src = dst
    all_goals
      simp only [Spec.Gcm.sealContiguousSig, Sig.bufs, eq, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      apply (h key hk).trans
      apply Prod.ext
      · first | exact (Scrub.bytesAt_of hb.2.2.2.1 (Scrub.len_le len)).symm | exact (Scrub.bytesAt_of hb.2.2.2.2.1 (Scrub.len_le len)).symm
      · first | exact (Scrub.bytesAt_of hb.2.2.2.2 (Nat.le_refl 16)).symm | exact (Scrub.bytesAt_of hb.2.2.2.2.2 (Nat.le_refl 16)).symm

private theorem stub_side : scrubFSide (Impl.AesGcm.X86.Contiguous.sealContiguous Scrub.stub) [] 2640 = true := by
  lit_decide

theorem scrub_side (v : GcmImpl) : scrubFSide (Impl.AesGcm.X86.Contiguous.sealContiguous v.callees) [] 2640 = true := by
  obtain ⟨hc,hk,hg⟩ := Scrub.holes v
  exact scrubFSide_of_fill (n:=0) (by fill_calls) stub_side

theorem verifiedScrub (v : GcmImpl) :
    VerifiedScrubbed target (Impl.AesGcm.X86.Contiguous.scrubbed v.callees) publicContract 0 :=
  verifiedScrubbedAll (api:=Spec.Gcm.sealContiguousApi)
    {code := Impl.AesGcm.X86.Contiguous.sealContiguous v.callees,
     verified := verified v (fun _ h => setupReady h), spSafe := coreSafe v}
    public_postOut (hs:=scrub_side v)

theorem scrubbedSafe (v : GcmImpl) :
    (Impl.AesGcm.X86.Contiguous.scrubbed v.callees).all (fun i => !isa.writesSp i)=true :=
  scrubAll_spSafe (coreSafe v)

end VG.Proof.AesGcm.X86.Contiguous
