module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The domain check: `vg_dsa_check_parameters` on p||q||g -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The registers the check's call pushes, last argument first. -/
abbrev chkRegs : List Reg := [.ebp, .esi, .ebx, .edx, .ecx, .eax]

/-- The check's contract, as its registration gives it. -/
abbrev chkContract : Contract isa := Proof.Dsa.checkParametersContract abi 108

/-- The regions the check is given: p||q||g, its working space and its
arguments. -/
def chkRd (E : Env) : List Region := [⟨off E.base sPk, E.outLen⟩]

def chkWr (E : Env) (s : State) : List Region :=
  [⟨off E.base sChk, 16 * E.pLen * 8⟩, ⟨(s.gpr .esp - 24#32).setWidth 64, 24⟩]

/-- The state the check starts in. -/
abbrev chkEntry (E : Env) (s : State) : State :=
  (pushed chkRegs s).callEntry.withRegions (chkRd E) (chkWr E s)

/-- The check's arguments in the registers. -/
structure ChkArgs (E : Env) (g : Geo) (s t : State) : Prop where
  eax : t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sPk
  ecx : t.gpr .ecx = BitVec.ofNat 32 (2 * g.pLen + g.qLen)
  edx : t.gpr .edx = BitVec.ofNat 32 g.pLen
  ebx : t.gpr .ebx = BitVec.ofNat 32 g.qLen
  esi : t.gpr .esi = s.gpr .edi + BitVec.ofNat 32 sChk
  ebp : t.gpr .ebp = BitVec.ofNat 32 (16 * g.pLen)
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .esi → r ≠ .ebp → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem chkArgs_ok {E : Env} {g : Geo} {s : State} {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, ChkArgs E g s t → WP isa rest t Q) :
    WP isa (.seq (.block (scr .eax sPk ++ ([.mov .ecx (.imm (BitVec.ofNat 32 (2 * g.pLen + g.qLen))),
      .mov .edx (.imm (BitVec.ofNat 32 g.pLen)), .mov .ebx (.imm (BitVec.ofNat 32 g.qLen))] : List Instr) ++ scr .esi sChk ++
      ([.mov .ebp (.imm (BitVec.ofNat 32 (16 * g.pLen)))] : List Instr))) rest) s Q := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ sy₁ => wp_movi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ =>
    scr_ok fun s₅ e₅ g₅ m₅ rd₅ wr₅ sy₅ => wp_movi fun s₆ u₆ => WP.block_nil (k s₆ ?_))
  have edi₄ : s₄.gpr .edi = s.gpr .edi := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, u₆.gpr, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), e₁]
  · rw [u₆.other _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), g₅ _ (by decide), u₄.gpr]
  · rw [u₆.other _ (by decide), e₅, edi₄]
  · rw [u₆.other r h₆, g₅ r h₅, u₄.other r h₄, u₃.other r h₃, u₂.other r h₂, g₁ r h₁]
  · rw [u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, m₁]
  · rw [u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₆.syms, sy₅, u₄.syms, u₃.syms, u₂.syms, sy₁]

theorem chkEntry_arg {E : Env} {s : State} (fit : 28 ≤ (s.gpr .esp).toNat) :
    arg (chkEntry E s) 0 = s.gpr .eax ∧ arg (chkEntry E s) 1 = s.gpr .ecx ∧
      arg (chkEntry E s) 2 = s.gpr .edx ∧ arg (chkEntry E s) 3 = s.gpr .ebx ∧
      arg (chkEntry E s) 4 = s.gpr .esi ∧ arg (chkEntry E s) 5 = s.gpr .ebp := by
  have fit' : 4 * chkRegs.length + 4 ≤ (s.gpr .esp).toNat := by simpa using fit
  have hrs : Reg.esp ∉ chkRegs := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [chkEntry, arg_withRegions, callEntry_arg fit' hrs (by decide)]; rfl)

theorem chkEntry_mem {E : Env} {s : State} (fit : 28 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 28] s.mem (chkEntry E s).mem :=
  callEntry_frame (rs := chkRegs) (by simpa using fit) (by decide)

theorem check_pre {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s₀ s : State} (B : Base E s₀) (A : ChkArgs E g s₀ s) : chkContract.pre (chkEntry E s) := by
  have sp := B.sp
  have spU : s.gpr .esp = E.sp := by rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), sp]
  have low := v.low
  have spLt := E.sp.isLt
  have nw := v.scratchFit
  have room := v.room
  have fit : 4 * chkRegs.length + 4 ≤ (s.gpr .esp).toNat := by rw [spU]; simp only [List.length_cons, List.length_nil]; omega_arith
  have hrs : Reg.esp ∉ chkRegs := by decide
  have uesp : (chkEntry E s).gpr .esp = s.gpr .esp - 28#32 := by
    change (pushed chkRegs s).callEntry.gpr .esp = _
    exact callEntry_esp' chkRegs s
  have uarg0 : argAddr (chkEntry E s) 0 = (s.gpr .esp - 24#32).setWidth 64 := by
    rw [chkEntry, argAddr_withRegions]; exact callEntry_argAddr0 chkRegs s
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := chkEntry_arg (E := E) (s := s) (by rw [spU]; omega_arith)
  rw [A.eax] at a0; rw [A.ecx] at a1; rw [A.edx] at a2; rw [A.ebx] at a3; rw [A.esi] at a4; rw [A.ebp] at a5
  have urd : (chkEntry E s).rd = chkRd E := rfl
  have uwr : (chkEntry E s).wr = chkWr E s := rfl
  have umem : Frame [below (s.gpr .esp) (4 * chkRegs.length + 4)] s.mem (chkEntry E s).mem :=
    callEntry_frame fit hrs
  generalize eu : chkEntry E s = u at *
  sig_pre [chkContract, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal,
    argBytes, stackBelow]
  have hs := B.scr
  have sz := v.size_ge
  have bd := G.bounds
  have pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega_arith)
  have cW := Scr.wide hs (d := sChk) (by simp only [sChk]; omega_arith)
  have pN := Scr.toNat_add hs (d := sPk) (by simp only [sPk]; omega_arith)
  have cN := Scr.toNat_add hs (d := sChk) (by simp only [sChk]; omega_arith)
  have l1 : (BitVec.ofNat 32 (2 * g.pLen + g.qLen)).toNat = 2 * g.pLen + g.qLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have l2 : (BitVec.ofNat 32 g.pLen).toNat = g.pLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have l3 : (BitVec.ofNat 32 g.qLen).toNat = g.qLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have l5 : (BitVec.ofNat 32 (16 * g.pLen)).toNat = 16 * g.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have nat28 : (s.gpr .esp - 28#32).toNat = E.sp.toNat - 28 := by rw [spU]; exact sub_toNat (by omega_arith)
  have callee : (s.gpr .esp - 28#32).setWidth 64 - 108#64 = (s.gpr .esp - 136#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [nat28]; omega_arith : 108 ≤ (s.gpr .esp - 28#32).toNat), BitVec.sub_sub]; rfl
  have oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  simp only [a0, a1, a2, a3, a4, a5, uesp, uarg0, urd, uwr, chkRd, chkWr, pW, cW, pN, cN, l1, l2, l3, l5, callee,
    oL, hp]
  have ss := v.scratchStack
  have subP : Region.Sub ⟨off E.base sPk, 2 * g.pLen + g.qLen⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPk]; omega_arith)
  have subC : Region.Sub ⟨off E.base sChk, 16 * g.pLen * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sChk]; omega_arith)
  have subArgs : Region.Sub ⟨(s.gpr .esp - 24#32).setWidth 64, 24⟩ E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega_arith)
  have subRet : Region.Sub ⟨(s.gpr .esp - 28#32).setWidth 64, 4⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 28) (by decide) (by omega_arith) (by decide))
  have subCal : Region.Sub ⟨(s.gpr .esp - 136#32).setWidth 64, 108⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 136) (by decide) (by omega_arith) (by decide))
  refine ⟨by rw [nat28]; omega_arith, by rw [nat28]; omega_arith, trivial, trivial,
    Offset.disjoint E.base (by simp only [sPk, sChk]; omega_arith) (by simp only [sPk]; omega_arith) (by simp only [sChk]; omega_arith),
    (ss.sub_left subP).sub_right subArgs, (ss.sub_left subC).sub_right subArgs,
    (ss.symm.sub_left subRet).sub_right subP, (ss.symm.sub_left subRet).sub_right subC, ?_,
    (ss.symm.sub_left subCal).sub_right subP, (ss.symm.sub_left subCal).sub_right subC, ?_,
    by simp only [sPk]; omega_arith, by simp only [sChk]; omega_arith, ?_, trivial, by simp only [Spec.Dsa.scratchWords]; omega_arith⟩
  · have nat24 : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
      rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
    have nat28' : ((s.gpr .esp - 28#32).setWidth 64).toNat = E.sp.toNat - 28 := by
      rw [BitVec.toNat_setWidth, nat28]; exact Nat.mod_eq_of_lt (by omega_arith)
    exact Offset.disjoint_of_le (by simp only [nat28', nat24]; omega_arith) (by simp only [nat24]; omega_arith)
  · have nat24 : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
      rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
    have nat60 : ((s.gpr .esp - 136#32).setWidth 64).toNat = E.sp.toNat - 136 := by
      rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
    exact Offset.disjoint_of_le (by simp only [nat60, nat24]; omega_arith) (by simp only [nat24]; omega_arith)
  · rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

/-- What the check's call needs. -/
theorem chk_callPre {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s t : State} (B : Base E s) (A : ChkArgs E g s t) : CallPre chkContract chkRegs (chkRd E) (chkWr E t) t := by
  have sz := v.size_ge
  have bd := G.bounds
  have room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  have subP : Region.Sub ⟨off E.base sPk, E.outLen⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [Env.outLen, sPk, hp, hq]; omega_arith)
  refine ⟨check_pre G v hp hq B A, ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [chkRd, chkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨E.scratchRegion, List.mem_append_right _ (.tail _ (A.wr ▸ B.scr.wr)), sPk, rfl,
        by simp only [Env.scratchRegion, Env.outLen, sPk, hp, hq]; omega_arith⟩
    · exact ⟨E.scratchRegion, List.mem_append_right _ (.tail _ (A.wr ▸ B.scr.wr)), sChk, rfl,
        by simp only [Env.scratchRegion, sChk]; omega_arith⟩
    · exact ⟨below (t.gpr .esp) (4 * chkRegs.length), List.mem_append_right _ (.head _), 0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [chkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨E.scratchRegion, .tail _ (A.wr ▸ B.scr.wr), sChk, rfl, by simp only [Env.scratchRegion, sChk]; omega_arith⟩
    · exact ⟨below (t.gpr .esp) (4 * chkRegs.length), .head _, 0, by simp, by simp⟩

/-- After the domain check's call and its comparison: ZF set exactly when
p||q||g passes. -/
structure ChkMid (E : Env) (g : Geo) (c : Bool) (s x : State) : Prop where
  base : Base E x
  zf : isa.eval .e x = some c
  chg : E.Chg [(sChk, 16 * g.pLen * 8), (fStatus, 4)] s.mem x.mem
  rd : x.rd = s.rd
  wr : x.wr = s.wr
  syms : x.syms = s.syms
  st : x.mem.readW (off E.base fStatus) 32 = s.mem.readW (off E.base fStatus) 32
  edi : x.gpr .edi = s.gpr .edi
  esp : x.gpr .esp = s.gpr .esp

/-- The domain check of p||q||g, up to the branch on its result. -/
theorem checkMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {P : Prog isa} {Q : State → Prop}
    (k : ∀ x, ChkMid E g (Spec.Dsa.checkParametersBytes g.pLen g.qLen
      (Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen))) s x → WP isa P x Q) :
    WP isa (Prog.chain [.block (scr .eax sPk ++ ([.mov .ecx (.imm (BitVec.ofNat 32 (2 * g.pLen + g.qLen))),
      .mov .edx (.imm (BitVec.ofNat 32 g.pLen)), .mov .ebx (.imm (BitVec.ofNat 32 g.qLen))] : List Instr) ++ scr .esi sChk ++
      ([.mov .ebp (.imm (BitVec.ofNat 32 (16 * g.pLen)))] : List Instr)),
      .frame (.push [.ebp, .esi, .ebx, .edx, .ecx, .eax]) (.call g.checkName g.checkCode) (.pop .ecx 6),
      .block [.alu .cmp .eax (.imm 1)]] P) s Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have low := v.low
  have nw := v.scratchFit
  have cs := G.cStack
  have room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  simp only [Prog.chain]
  refine chkArgs_ok (E := E) fun t A => ?_
  have spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have hsT : Scr t E.base E.size := Scr.of_eq B.scr (A.other _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) (by rw [spT, B.sp]) A.wr
  have cp := chk_callPre G v hp hq B A
  have fitT : 28 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_arith
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := chkEntry_arg (E := E) (s := t) fitT
  have Fm := chkEntry_mem (E := E) (s := t) fitT
  simp only [chkEntry] at e0 e1 e2 e3 e4 e5 Fm
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.esi] at e4; rw [A.ebp] at e5
  refine WP.seq (WP.of_syms (WP.callWithReturn G.cv.1 G.cNoSp (by decide) (by decide)
    (by rw [spT]; simp only [List.length_cons, List.length_nil]; omega_arith) cp fun u rdu wru csu Fu post usy => ?_))
  obtain ⟨s₂, m₂, ax₂, post⟩ := post
  generalize ew : (pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWr E t) = w at e0 e1 e2 e3 e4 e5 Fm post
  sig_post [chkContract, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal,
    argBytes, stackBelow] at post
  simp only [e0, e1, ret32] at post
  have hs := B.scr
  have pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega_arith)
  have l1 : (BitVec.ofNat 32 (2 * g.pLen + g.qLen)).toNat = 2 * g.pLen + g.qLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have l2 : (BitVec.ofNat 32 g.pLen).toNat = g.pLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have l3 : (BitVec.ofNat 32 g.qLen).toNat = g.qLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  rw [spT] at Fm
  have bytesW : Spec.Rsa.bytesAt w.mem (off E.base sPk) (2 * g.pLen + g.qLen) =
      Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen) := by
    rw [← A.mem]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine Frame.bytes Fm (R := ⟨off E.base sPk, 2 * g.pLen + g.qLen⟩) ?_ (by show 2 * g.pLen + g.qLen ≤ 2 ^ 64; omega_arith) hi
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (v.scratchStack.sub_left (Offset.sub_base _ (by simp only [sPk]; omega_arith))).sub_right
      (below_sub (by decide) (by omega_arith))
  simp only [pW, l1, l2, l3, e2, e3, bytesW] at post
  generalize hc : Spec.Dsa.checkParametersBytes g.pLen g.qLen
    (Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen)) = c at post k ⊢
  have uax : u.gpr .eax = BitVec.ofNat 32 (if c = true then 1 else 0) := by
    rw [← ax₂]; exact BitVec.eq_of_toNat_eq (by rw [post, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by split <;> decide)])
  have tdi : t.gpr .edi = s.gpr .edi := A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have udi : u.gpr .edi = s.gpr .edi := (csu .edi (by decide)).trans tdi
  have usp : u.gpr .esp = E.sp := (csu .esp (by decide)).trans spT
  have hsU : Scr u E.base E.size := Scr.of_eq B.scr udi (usp.trans B.sp.symm) (wru.trans A.wr)
  have Ac : E.Apart [(sChk, 16 * g.pLen * 8), (fStatus, 4)] := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [sChk, fStatus, fOut, fWitLen, hdr] <;> omega_arith
  have CH0 : E.Chg [(sChk, 16 * g.pLen * 8)] s.mem u.mem := by
    rw [← A.mem]
    refine Env.Chg.of_frame Fu fun r hr => ?_
    simp only [chkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← hp]; exact Env.in_range (List.mem_cons_self ..) (Nat.le_refl _) (by rw [hp])
    · rw [spT]; exact Env.in_stack (below_sub (by decide) (by omega_arith))
    · rw [spT]; exact Env.in_stack (below_sub (by simp only [List.length_cons, List.length_nil]; omega_arith) (by omega_arith))
  have CH : E.Chg [(sChk, 16 * g.pLen * 8), (fStatus, 4)] s.mem u.mem :=
    Env.Chg.widen CH0 fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact List.mem_cons_self ..,
      Nat.le_refl _, Nat.le_refl _⟩
  have urd : u.rd = s.rd := by rw [rdu, A.rd]
  have uwr : u.wr = s.wr := by rw [wru, A.wr]
  have usy' : u.syms = s.syms := by rw [usy, A.syms]
  have stU : u.mem.readW (off E.base fStatus) 32 = s.mem.readW (off E.base fStatus) 32 := by
    refine Env.Chg.word v CH0 (by simp only [fStatus, hdr]; omega_arith) fun o ho => ?_
    simp only [List.mem_singleton] at ho; subst ho
    simp only [sChk, fStatus, hdr]; omega_arith
  refine WP.seq (wp_cmpi fun x₁ f₁ _ z₁ => WP.block_nil ?_)
  have zf₁ : isa.eval .e x₁ = some c := by
    show x₁.zf = _
    rw [z₁, uax]; cases c <;> decide
  have hsX : Scr x₁ E.base E.size := Scr.of_eq hsU (by rw [f₁.gpr]) (by rw [f₁.gpr]) f₁.wr
  have B₁ : Base E x₁ := B.keep v (by rw [f₁.mem]; exact CH) Ac (by rw [f₁.gpr, udi]) (by rw [f₁.gpr, usp, B.sp])
    (by rw [f₁.rd, urd]) (by rw [f₁.wr, uwr]) (by rw [f₁.syms, usy'])
  exact k x₁ ⟨B₁, zf₁, by rw [f₁.mem]; exact CH, by rw [f₁.rd, urd], by rw [f₁.wr, uwr], by rw [f₁.syms, usy'],
    by rw [f₁.mem, stU], by rw [f₁.gpr, udi], by rw [f₁.gpr, usp, B.sp]⟩

/-- The domain check of p||q||g: `fStatus` := 1 if it passes. -/
theorem check_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) :
    WP isa (check g.pLen g.qLen (16 * g.pLen) g.checkName g.checkCode) s fun t =>
      Base E t ∧ E.Chg [(sChk, 16 * g.pLen * 8), (fStatus, 4)] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      t.mem.readW (off E.base fStatus) 32 =
        (if Spec.Dsa.checkParametersBytes g.pLen g.qLen
            (Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen)) then BitVec.ofNat 32 1
          else s.mem.readW (off E.base fStatus) 32) := by
  have sz := v.size_ge
  have bd := G.bounds
  have room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  have Ac : E.Apart [(sChk, 16 * g.pLen * 8), (fStatus, 4)] := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [sChk, fStatus, fOut, fWitLen, hdr] <;> omega_arith
  unfold check
  show WP isa (Prog.chain [_, _, _] (.ite .e _ _)) s _
  refine checkMid_ok G v hp hq B fun x₁ M => ?_
  generalize Spec.Dsa.checkParametersBytes g.pLen g.qLen
    (Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen)) = c at M ⊢
  refine WP.ite c M.zf (fun h1 => stImm_end M.base.scr (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega_arith)
    fun x₂ g₂ m₂' rd₂ wr₂ sy₂ => ?_) (fun h1 => WP.block_nil ?_)
  · have C₂ : E.Chg [(sChk, 16 * g.pLen * 8), (fStatus, 4)] s.mem x₂.mem := by
      rw [m₂']; exact M.chg.store (.tail _ (.head _)) (by decide) _
    refine ⟨B.keep v C₂ Ac (by rw [g₂ _ (by decide), M.edi]) (by rw [g₂ _ (by decide), M.esp])
      (by rw [rd₂, M.rd]) (by rw [wr₂, M.wr]) (by rw [sy₂, M.syms]), C₂,
      by rw [rd₂, M.rd], by rw [wr₂, M.wr], by rw [sy₂, M.syms], ?_⟩
    rw [m₂', Mem.readW_writeW_self32, h1]; rfl
  · refine ⟨M.base, M.chg, M.rd, M.wr, M.syms, ?_⟩
    rw [h1, M.st]; rfl

end VG.Proof.Dsa.X86.Generation
