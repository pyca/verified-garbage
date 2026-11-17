module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.AddBE
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCall
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Dsa.Contract

/-! ### `Dsa.X86.Generation.CheckCall`, which this module and modules that import it used -/

section

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
  obtain edi₄ : s₄.gpr .edi = s.gpr .edi := by
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
  obtain fit' : 4 * chkRegs.length + 4 ≤ (s.gpr .esp).toNat := by simpa using fit
  obtain hrs : Reg.esp ∉ chkRegs := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [chkEntry, arg_withRegions, callEntry_arg fit' hrs (by decide)]; rfl)

theorem chkEntry_mem {E : Env} {s : State} (fit : 28 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 28] s.mem (chkEntry E s).mem :=
  callEntry_frame (rs := chkRegs) (by simpa using fit) (by decide)

theorem check_pre {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s₀ s : State} (B : Base E s₀) (A : ChkArgs E g s₀ s) : chkContract.pre (chkEntry E s) := by
  have sp := B.sp
  obtain spU : s.gpr .esp = E.sp := by rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), sp]
  have low := v.low
  have spLt := E.sp.isLt
  have nw := v.scratchFit
  have room := v.room
  obtain fit : 4 * chkRegs.length + 4 ≤ (s.gpr .esp).toNat := by rw [spU]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain hrs : Reg.esp ∉ chkRegs := by decide
  obtain uesp : (chkEntry E s).gpr .esp = s.gpr .esp - 28#32 := by
    change (pushed chkRegs s).callEntry.gpr .esp = _
    exact callEntry_esp' chkRegs s
  obtain uarg0 : argAddr (chkEntry E s) 0 = (s.gpr .esp - 24#32).setWidth 64 := by
    rw [chkEntry, argAddr_withRegions]; exact callEntry_argAddr0 chkRegs s
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := chkEntry_arg (E := E) (s := s) (by rw [spU]; omega_arith)
  rw [A.eax] at a0; rw [A.ecx] at a1; rw [A.edx] at a2; rw [A.ebx] at a3; rw [A.esi] at a4; rw [A.ebp] at a5
  have urd : (chkEntry E s).rd = chkRd E := rfl
  have uwr : (chkEntry E s).wr = chkWr E s := rfl
  obtain umem : Frame [below (s.gpr .esp) (4 * chkRegs.length + 4)] s.mem (chkEntry E s).mem :=
    callEntry_frame fit hrs
  generalize eu : chkEntry E s = u at *
  sig_pre [chkContract, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal,
    argBytes, stackBelow]
  have hs := B.scr
  have sz := v.size_ge
  have bd := G.bounds
  obtain pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega_arith)
  obtain cW := Scr.wide hs (d := sChk) (by simp only [sChk]; omega_arith)
  obtain pN := Scr.toNat_add hs (d := sPk) (by simp only [sPk]; omega_arith)
  obtain cN := Scr.toNat_add hs (d := sChk) (by simp only [sChk]; omega_arith)
  obtain l1 : (BitVec.ofNat 32 (2 * g.pLen + g.qLen)).toNat = 2 * g.pLen + g.qLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain l2 : (BitVec.ofNat 32 g.pLen).toNat = g.pLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain l3 : (BitVec.ofNat 32 g.qLen).toNat = g.qLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain l5 : (BitVec.ofNat 32 (16 * g.pLen)).toNat = 16 * g.pLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain nat28 : (s.gpr .esp - 28#32).toNat = E.sp.toNat - 28 := by rw [spU]; exact sub_toNat (by omega_arith)
  obtain callee : (s.gpr .esp - 28#32).setWidth 64 - 108#64 = (s.gpr .esp - 136#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [nat28]; omega_arith : 108 ≤ (s.gpr .esp - 28#32).toNat), BitVec.sub_sub]; rfl
  obtain oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  simp only [a0, a1, a2, a3, a4, a5, uesp, uarg0, urd, uwr, chkRd, chkWr, pW, cW, pN, cN, l1, l2, l3, l5, callee,
    oL, hp]
  have ss := v.scratchStack
  obtain subP : Region.Sub ⟨off E.base sPk, 2 * g.pLen + g.qLen⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sPk]; omega_arith)
  obtain subC : Region.Sub ⟨off E.base sChk, 16 * g.pLen * 8⟩ E.scratchRegion :=
    Offset.sub_base _ (by simp only [sChk]; omega_arith)
  obtain subArgs : Region.Sub ⟨(s.gpr .esp - 24#32).setWidth 64, 24⟩ E.stackRegion := by
    rw [spU]; exact below_sub (by decide) (by omega_arith)
  obtain subRet : Region.Sub ⟨(s.gpr .esp - 28#32).setWidth 64, 4⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 28) (by decide) (by omega_arith) (by decide))
  obtain subCal : Region.Sub ⟨(s.gpr .esp - 136#32).setWidth 64, 108⟩ E.stackRegion :=
    sub_of_contains (by rw [spU]; exact below_top (k := 136) (by decide) (by omega_arith) (by decide))
  refine ⟨by rw [nat28]; omega_arith, by rw [nat28]; omega_arith, trivial, trivial,
    Offset.disjoint E.base (by simp only [sPk, sChk]; omega_arith) (by simp only [sPk]; omega_arith) (by simp only [sChk]; omega_arith),
    (ss.sub_left subP).sub_right subArgs, (ss.sub_left subC).sub_right subArgs,
    (ss.symm.sub_left subRet).sub_right subP, (ss.symm.sub_left subRet).sub_right subC, ?_,
    (ss.symm.sub_left subCal).sub_right subP, (ss.symm.sub_left subCal).sub_right subC, ?_,
    by simp only [sPk]; omega_arith, by simp only [sChk]; omega_arith, ?_, trivial, by simp only [Spec.Dsa.scratchWords]; omega_arith⟩
  · have nat24 : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
      rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
    obtain nat28' : ((s.gpr .esp - 28#32).setWidth 64).toNat = E.sp.toNat - 28 := by
      rw [BitVec.toNat_setWidth, nat28]; exact Nat.mod_eq_of_lt (by omega_arith)
    exact Offset.disjoint_of_le (by simp only [nat28', nat24]; omega_arith) (by simp only [nat24]; omega_arith)
  · have nat24 : ((s.gpr .esp - 24#32).setWidth 64).toNat = E.sp.toNat - 24 := by
      rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
    obtain nat60 : ((s.gpr .esp - 136#32).setWidth 64).toNat = E.sp.toNat - 136 := by
      rw [BitVec.toNat_setWidth, spU, sub_toNat (by omega_arith)]; exact Nat.mod_eq_of_lt (by omega_arith)
    exact Offset.disjoint_of_le (by simp only [nat60, nat24]; omega_arith) (by simp only [nat24]; omega_arith)
  · rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

/-- What the check's call needs. -/
theorem chk_callPre {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s t : State} (B : Base E s) (A : ChkArgs E g s t) : CallPre chkContract chkRegs (chkRd E) (chkWr E t) t := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  obtain subP : Region.Sub ⟨off E.base sPk, E.outLen⟩ E.scratchRegion :=
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
  obtain room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  simp only [Prog.chain]
  refine chkArgs_ok (E := E) fun t A => ?_
  obtain spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  obtain hsT : Scr t E.base E.size := Scr.of_eq B.scr (A.other _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) (by rw [spT, B.sp]) A.wr
  obtain cp := chk_callPre G v hp hq B A
  obtain fitT : 28 ≤ (t.gpr .esp).toNat := by rw [spT]; omega_arith
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := chkEntry_arg (E := E) (s := t) fitT
  obtain Fm := chkEntry_mem (E := E) (s := t) fitT
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
  obtain pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega_arith)
  obtain l1 : (BitVec.ofNat 32 (2 * g.pLen + g.qLen)).toNat = 2 * g.pLen + g.qLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain l2 : (BitVec.ofNat 32 g.pLen).toNat = g.pLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain l3 : (BitVec.ofNat 32 g.qLen).toNat = g.qLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  rw [spT] at Fm
  obtain bytesW : Spec.Rsa.bytesAt w.mem (off E.base sPk) (2 * g.pLen + g.qLen) =
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
  obtain uax : u.gpr .eax = BitVec.ofNat 32 (if c = true then 1 else 0) := by
    rw [← ax₂]; exact BitVec.eq_of_toNat_eq (by rw [post, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by split <;> decide)])
  obtain tdi : t.gpr .edi = s.gpr .edi := A.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain udi : u.gpr .edi = s.gpr .edi := (csu .edi (by decide)).trans tdi
  obtain usp : u.gpr .esp = E.sp := (csu .esp (by decide)).trans spT
  obtain hsU : Scr u E.base E.size := Scr.of_eq B.scr udi (usp.trans B.sp.symm) (wru.trans A.wr)
  obtain Ac : E.Apart [(sChk, 16 * g.pLen * 8), (fStatus, 4)] := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [sChk, fStatus, fOut, fWitLen, hdr] <;> omega_arith
  obtain CH0 : E.Chg [(sChk, 16 * g.pLen * 8)] s.mem u.mem := by
    rw [← A.mem]
    refine Env.Chg.of_frame Fu fun r hr => ?_
    simp only [chkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← hp]; exact Env.in_range (List.mem_cons_self ..) (Nat.le_refl _) (by rw [hp])
    · rw [spT]; exact Env.in_stack (below_sub (by decide) (by omega_arith))
    · rw [spT]; exact Env.in_stack (below_sub (by simp only [List.length_cons, List.length_nil]; omega_arith) (by omega_arith))
  obtain CH : E.Chg [(sChk, 16 * g.pLen * 8), (fStatus, 4)] s.mem u.mem :=
    Env.Chg.widen CH0 fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact List.mem_cons_self ..,
      Nat.le_refl _, Nat.le_refl _⟩
  obtain urd : u.rd = s.rd := by rw [rdu, A.rd]
  obtain uwr : u.wr = s.wr := by rw [wru, A.wr]
  obtain usy' : u.syms = s.syms := by rw [usy, A.syms]
  obtain stU : u.mem.readW (off E.base fStatus) 32 = s.mem.readW (off E.base fStatus) 32 := by
    refine Env.Chg.word v CH0 (by simp only [fStatus, hdr]; omega_arith) fun o ho => ?_
    simp only [List.mem_singleton] at ho; subst ho
    simp only [sChk, fStatus, hdr]; omega_arith
  refine WP.seq (wp_cmpi fun x₁ f₁ _ z₁ => WP.block_nil ?_)
  obtain zf₁ : isa.eval .e x₁ = some c := by
    show x₁.zf = _
    rw [z₁, uax]; cases c <;> decide
  obtain hsX : Scr x₁ E.base E.size := Scr.of_eq hsU (by rw [f₁.gpr]) (by rw [f₁.gpr]) f₁.wr
  obtain B₁ : Base E x₁ := B.keep v (by rw [f₁.mem]; exact CH) Ac (by rw [f₁.gpr, udi]) (by rw [f₁.gpr, usp, B.sp])
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
  obtain room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  obtain Ac : E.Apart [(sChk, 16 * g.pLen * 8), (fStatus, 4)] := by
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

end

end

/-! # One seed: q, p, g and the domain check (A.1.1.2, A.2.1) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Dsa.Generation
open VG.Impl.Mont.X86 (sc)

/-- The ranges a seed changes. -/
def atRanges (g : Geo) : List (Nat × Nat) :=
  qRanges g ++ ppRanges g ++ gRanges g ++ [(sChk, 16 * g.pLen * 8), (fStatus, 4), (fHs, 4), (fHsLen, 4)]

/-- A seed's result in memory `m`: `fStatus` 2 if `rand` ran out, 1 with
p||q||g if the domain passed, else 0; and the octets of `rand` read. -/
def ARes (E : Env) (g : Geo) (m : Mem) : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) → Prop
  | none => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 2
  | some (none, rest) => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 ∧
      ∃ u, u ≤ E.witLen ∧ m.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u ∧ E.witT.drop u = rest
  | some (some a, rest) => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.bytesAt m (off E.base sPk) (2 * g.pLen + g.qLen) = Spec.Dsa.encodeParams g.pLen g.qLen a ∧
      ∃ u, u ≤ E.witLen ∧ m.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u ∧ E.witT.drop u = rest

/-- What a seed keeps. -/
structure AKeep (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (atRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem generator_lt {p q g : Nat} {hs : List Nat} (hp : 0 < p) (h : Spec.Dsa.generator p q hs = some g) :
    g < p := by
  induction hs with
  | nil => simp [Spec.Dsa.generator] at h
  | cons x xs ih =>
    rw [VG.Proof.Dsa.Generation.generator_cons] at h
    split at h
    · dsimp only at h
      split at h
      · cases h; rw [VG.Proof.Dsa.powMod_eq]; exact Nat.mod_lt _ hp
      · exact ih h
    · exact ih h

theorem atRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    E.Apart (atRanges g) := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  intro o ho
  simp only [atRanges, List.mem_append] at ho
  rcases ho with ((h | h) | h) | h
  · have szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
      rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
    simp only [qRanges, qPre, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sState, sHScr, sPk, sPP, fRes, fUsed, fUsedOut, fOut, fWitLen, hdr] <;> omega_arith
  · exact ppRanges_apart G v o h
  · exact gRanges_apart G v o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp only [sChk, fStatus, fHs, fHsLen, fOut, fWitLen, hdr] <;> omega_arith

/-- The window's result: the generator over its candidates, and the
parameters' validation. -/
def winResult (pLen p q : Nat) (r : Spec.RsaKeyGen.Rand) : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) :=
  match Spec.Dsa.generator p q (windowCandidates pLen Spec.Dsa.generatorAttempts r) with
  | none =>
    if Spec.Dsa.generatorAttempts * pLen ≤ r.length then
      some (none, r.drop (Spec.Dsa.generatorAttempts * pLen))
    else none
  | some g =>
    some (if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none,
      r.drop (pLen * generatorCount p q (windowCandidates pLen Spec.Dsa.generatorAttempts r)))

/-- A seed's result after p's search `R`. -/
def pOutcome (pLen q : Nat) :
    Option (Option Nat × Spec.RsaKeyGen.Rand) → Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand)
  | none => none
  | some (none, rest) => some (none, rest)
  | some (some p, rest) => winResult pLen p q rest

/-- A seed's result after q's test `r`. -/
def qOutcome (pLen qLen q : Nat) (seed : List Byte) :
    Option (Bool × Spec.RsaKeyGen.Rand) → Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand)
  | none => none
  | some (false, rest) => some (none, rest)
  | some (true, rest) => pOutcome pLen q (Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) q seed rest)

theorem refillAttempt_eq (pLen qLen : Nat) (seed rand : List Byte) :
    refillAttempt pLen qLen seed rand =
      qOutcome pLen qLen (Spec.Dsa.qCandidate (8 * qLen) seed) seed
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * qLen) seed) rand) := by
  unfold refillAttempt qOutcome
  dsimp only
  rcases Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * qLen) seed) rand with _ | ⟨_ | _, r⟩
  · rfl
  · rfl
  · dsimp only
    unfold pOutcome winResult
    rcases Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) (Spec.Dsa.qCandidate (8 * qLen) seed) seed r with
      _ | ⟨_ | _, _⟩ <;> rfl

/-- Without a generator, every candidate is read. -/
theorem count_none {p q : Nat} :
    ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none → generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, e => by
    rw [generator_cons'] at e
    rw [generatorCount]
    by_cases hh : generatorHit p q h = true
    · simp [hh] at e
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at e ⊢
      rw [count_none e, List.length_cons]

/-- The `h` candidates of the window at `u`. -/
theorem hList_window {E : Env} {u : Nat} (hl : E.witT.length = E.witLen) :
    hList (E.window u) = windowCandidates E.pLen Spec.Dsa.generatorAttempts (E.witT.drop u) := by
  unfold hList windowCandidates
  congr 2
  simp only [Env.hT, Env.window]
  rw [List.take_eq_take_iff, List.length_drop, hl, Spec.Dsa.generatorAttempts]
  omega_using []

theorem AKeep.mem {E : Env} {g : Geo} {s t t' : State} (K : AKeep E g s t) (hm : t'.mem = t.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : AKeep E g s t' :=
  ⟨K.base.regs hm edi sp rd wr sy, by rw [hm]; exact K.chg, by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

theorem AKeep.store {E : Env} {g : Geo} {s t t' : State} (K : AKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {d : Nat} (hd : (d, 4) ∈ atRanges g) (x : BitVec 32)
    (hm : t'.mem = t.mem.writeW (off E.base d) x) (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : AKeep E g s t' := by
  obtain C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact ⟨K.base.keep v C (fun o ho => atRanges_apart G v hp o
      (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd)) edi sp rd wr sy,
    K.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- A word of the header apart from every range of a seed. -/
theorem AKeep.word {E : Env} {g : Geo} {s t : State} (K : AKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {d : Nat} (hd₁ : hdr ≤ d) (hd₂ : d + 4 ≤ fUsed) :
    t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 := by
  have sz := v.size_ge
  obtain Aat := atRanges_apart G v hp
  have bd := G.bounds
  obtain szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  obtain key : ∀ o ∈ atRanges g, o.1 + o.2 ≤ d ∨ d + 4 ≤ o.1 := by
    simp only [atRanges, qRanges, qPre, ppRanges, paRanges, pxRanges, aRanges, gRanges, rRanges, wRanges,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    simp only [sState, sHScr, sX, sPk, sPP, ppWords, arr, aTmp, aH, sChk, fRes, fUsed, fUsedOut, fP, fCounter,
      fOffset, fH, fHLeft, fG, fLo, fStatus, fHs, fHsLen, hdr] at hd₁ hd₂ ⊢
    repeat' apply And.intro
    all_goals omega_arith
  exact Env.Chg.word v K.chg (by simp only [fUsed, hdr] at hd₂; omega_using [hd₂, sz])
    fun o ho => ⟨(Aat o ho).1, key o ho⟩

/-- The cursor's word, which no range of a seed holds. -/
theorem AKeep.cur {E : Env} {g : Geo} {s t : State} (K : AKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) : t.mem.readW (off E.base fC) 32 = s.mem.readW (off E.base fC) 32 := by
  have sz := v.size_ge
  obtain Aat := atRanges_apart G v hp
  have bd := G.bounds
  obtain szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  obtain key : ∀ o ∈ atRanges g, o.1 + o.2 ≤ fC ∨ fC + 4 ≤ o.1 := by
    simp only [atRanges, qRanges, qPre, ppRanges, paRanges, pxRanges, aRanges, gRanges, rRanges, wRanges,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    simp only [sState, sHScr, sX, sPk, sPP, ppWords, arr, aTmp, aH, sChk, fRes, fUsed, fUsedOut, fP, fCounter,
      fOffset, fH, fHLeft, fG, fLo, fStatus, fHs, fHsLen, fC, hdr]
    repeat' apply And.intro
    all_goals omega_using []
  exact Env.Chg.word v K.chg (by simp only [fC, hdr]; omega_using [sz]) fun o ho => ⟨(Aat o ho).1, key o ho⟩

/-- After the window's block: `fHs` := `rand + u`, `fHsLen` := the octets of
`rand` after `u`, and CF whether they are fewer than the window's. -/
structure WinPost (E : Env) (g : Geo) (u : Nat) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg [(fHs, 4), (fHsLen, 4)] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  hs : t.mem.readW (off E.base fHs) 32 = (E.window u).hs.setWidth 32
  len : t.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (E.witLen - u)
  cf : isa.eval .b t = some (decide (E.witLen - u < 128 * g.pLen))

/-- The window's block. -/
theorem gWinBlock_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State}
    (B : Base E s) {u : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u) (hu : u ≤ E.witLen) :
    WP isa (.block [.mov .ecx (.mem (sc fUsed)), .mov .eax (.mem (sc fWit)), .alu .add .eax (.reg .ecx),
      .store (sc fHs) .eax, .mov .eax (.mem (sc fWitLen)), .alu .sub .eax (.reg .ecx), .store (sc fHsLen) .eax,
      .alu .cmp .eax (.imm (BitVec.ofNat 32 (128 * g.pLen)))]) s (WinPost E g u s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have wl := v.witLen32
  obtain ap : E.Apart [(fHs, 4), (fHsLen, 4)] := fun o ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, fOut, fUsedP, fWitLen, hdr] <;> omega_using [sz]
  refine ld_ok B.scr (d := fUsed) (by simp only [fUsed, hdr]; omega_using [sz]) fun t₁ u₁ =>
    ld_ok (Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) (d := fWit)
      (by simp only [fWit, hdr]; omega_using [sz]) fun t₂ u₂ => wp_add fun t₃ u₃ _ => ?_
  obtain hs₃ : Scr t₃ E.base E.size := Scr.of_eq B.scr (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  obtain ecx₃ : t₃.gpr .ecx = BitVec.ofNat 32 u := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hU]
  obtain eax₃ : t₃.gpr .eax = (E.wit + BitVec.ofNat 64 u).setWidth 32 := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, B.witW, hU, ptr_add]
  obtain m₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine st_ok hs₃ (d := fHs) (by simp only [fHs, hdr]; omega_using [sz]) fun t₄ M₄ => ?_
  obtain hs₄ := Scr.of_eq hs₃ (by rw [M₄.gpr]) (by rw [M₄.gpr]) M₄.wr
  refine ld_ok hs₄ (d := fWitLen) (by simp only [fWitLen, hdr]; omega_using [sz]) fun t₅ u₅ => wp_sub fun t₆ u₆ _ => ?_
  obtain hs₆ : Scr t₆ E.base E.size := Scr.of_eq hs₄ (by rw [u₆.other _ (by decide), u₅.other _ (by decide)])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide)]) (by rw [u₆.wr, u₅.wr])
  obtain eax₆ : t₆.gpr .eax = BitVec.ofNat 32 (E.witLen - u) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), M₄.gpr, ecx₃, M₄.mem, m₃,
      word_store_other v _ (by simp only [fWitLen, hdr]; omega_using [sz]) (by simp only [fHs, hdr]; omega_using [sz])
        (by simp only [fWitLen, fHs, hdr]; omega_using []), B.witLenW, sub_ofNat hu]
  refine st_ok hs₆ (d := fHsLen) (by simp only [fHsLen, hdr]; omega_using [sz]) fun t₇ M₇ =>
    wp_cmpi fun t₈ f₈ c₈ _ => WP.block_nil ?_
  obtain m₈ : t₈.mem = (s.mem.writeW (off E.base fHs) ((E.wit + BitVec.ofNat 64 u).setWidth 32)).writeW
      (off E.base fHsLen) (BitVec.ofNat 32 (E.witLen - u)) := by
    rw [f₈.mem, M₇.mem, u₆.mem, u₅.mem, M₄.mem, eax₆, m₃, eax₃]
  obtain C₈ : E.Chg [(fHs, 4), (fHsLen, 4)] s.mem t₈.mem := by
    rw [m₈]
    exact ((Env.Chg.refl _ _).store (d := fHs) (n := 4) (by simp) (by decide) _).store (d := fHsLen) (n := 4)
      (by simp) (by decide) _
  obtain rd₈ : t₈.rd = s.rd := by rw [f₈.rd, M₇.rd, u₆.rd, u₅.rd, M₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₈ : t₈.wr = s.wr := by rw [f₈.wr, M₇.wr, u₆.wr, u₅.wr, M₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain sy₈ : t₈.syms = s.syms := by rw [f₈.syms, M₇.syms, u₆.syms, u₅.syms, M₄.syms, u₃.syms, u₂.syms, u₁.syms]
  obtain edi₈ : t₈.gpr .edi = s.gpr .edi := by
    rw [f₈.gpr, M₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), M₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain esp₈ : t₈.gpr .esp = s.gpr .esp := by
    rw [f₈.gpr, M₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), M₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  refine ⟨B.keep v C₈ ap edi₈ esp₈ rd₈ wr₈ sy₈, C₈, rd₈, wr₈, sy₈, edi₈, esp₈, ?_, ?_, ?_⟩
  · rw [m₈, word_store_other v _ (by simp only [fHs, hdr]; omega_using [sz]) (by simp only [fHsLen, hdr]; omega_using [sz])
      (by simp only [fHs, fHsLen, hdr]; omega_using []), Mem.readW_writeW_self32]
    rfl
  · rw [m₈, Mem.readW_writeW_self32]
  · show t₈.cf = _
    rw [c₈, M₇.gpr, eax₆, toNat_ofNat_lt (by omega_using [wl]), toNat_ofNat_lt (by omega_using [bd])]

/-- The window's words: `fHs` := `rand + u`, `fHsLen` := the window's length. -/
theorem gWindow_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State}
    (B : Base E s) {u : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u) (hu : u ≤ E.witLen) :
    WP isa g.gWindow s fun t => Base E t ∧ E.Chg [(fHs, 4), (fHsLen, 4)] s.mem t.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms ∧ t.mem.readW (off E.base fHs) 32 = (E.window u).hs.setWidth 32 ∧
      t.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (E.window u).hsLen := by
  have sz := v.size_ge
  have bd := G.bounds
  unfold Geo.gWindow
  refine WP.seq (WP.mono (gWinBlock_ok G v B hU hu) fun t₈ W => ?_)
  refine WP.ite _ W.cf (fun h => WP.block_nil ⟨W.base, W.chg, W.rd, W.wr, W.syms, W.hs, ?_⟩) (fun h => ?_)
  · rw [W.len]
    simp only [Env.window, hp]
    rw [Nat.min_eq_left (by have := of_decide_eq_true h; omega_using [this])]
  · refine stImm_end W.base.scr (o := fHsLen) (v := 128 * g.pLen) (by simp only [fHsLen, hdr]; omega_using [sz])
      fun t₉ g₉ m₉ rd₉ wr₉ sy₉ => ?_
    obtain C₉ : E.Chg [(fHs, 4), (fHsLen, 4)] s.mem t₉.mem := by
      rw [m₉]; exact W.chg.store (d := fHsLen) (n := 4) (by simp) (by decide) _
    obtain ap : E.Apart [(fHs, 4), (fHsLen, 4)] := fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, fOut, fUsedP, fWitLen, hdr] <;> omega_using [sz]
    refine ⟨B.keep v C₉ ap (by rw [g₉ _ (by decide), W.edi]) (by rw [g₉ _ (by decide), W.esp])
      (by rw [rd₉, W.rd]) (by rw [wr₉, W.wr]) (by rw [sy₉, W.syms]), C₉, by rw [rd₉, W.rd], by rw [wr₉, W.wr],
      by rw [sy₉, W.syms], ?_, ?_⟩
    · rw [m₉, word_store_other v _ (by simp only [fHs, hdr]; omega_using [sz]) (by simp only [fHsLen, hdr]; omega_using [sz])
        (by simp only [fHs, fHsLen, hdr]; omega_using []), W.hs]
    · rw [m₉, Mem.readW_writeW_self32]
      simp only [Env.window, hp]
      rw [Nat.min_eq_right (by have := of_decide_eq_false h; omega_using [this])]

/-- The candidates read: `fUsed` := `fH − rand`. -/
theorem gUsed_wp {E : Env} {s : State} (hs : Scr s E.base E.size) (hsz : 73728 ≤ E.size) :
    WP isa (.block Geo.gUsed) s fun t => (∃ x : BitVec 32, t.mem = s.mem.writeW (off E.base fUsed) x) ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  refine ld_ok hs (d := fH) (by simp only [fH, hdr]; omega_using [hsz]) fun t₈ u₈ =>
    ld_ok (Scr.of_eq hs (u₈.other _ (by decide)) (u₈.other _ (by decide)) u₈.wr) (d := fWit)
      (by simp only [fWit, hdr]; omega_using [hsz]) fun t₉ u₉ => wp_sub fun t₁₀ u₁₀ _ =>
    st_ok (Scr.of_eq hs (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)])
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)])
      (by rw [u₁₀.wr, u₉.wr, u₈.wr])) (d := fUsed) (by simp only [fUsed, hdr]; omega_using [hsz]) fun t₁₁ M₁₁ =>
    WP.block_nil ⟨⟨_, by rw [M₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]⟩,
      by rw [M₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)],
      by rw [M₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)],
      by rw [M₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd], by rw [M₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr],
      by rw [M₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms]⟩

theorem attempt_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen)
    (hst : s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0) :
    WP isa g.attempt s fun t => AKeep E g s t ∧
      ARes E g t.mem (refillAttempt g.pLen g.qLen (chunk E k) (E.witT.drop used)) := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain Aat := atRanges_apart G v hp
  obtain wl : E.witT.length = E.witLen := by rw [← B.wit, VG.Proof.Bignum.bytesAt_length]
  obtain qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega_arith) (chunk E k)
  unfold Geo.attempt
  simp only [seqs]
  -- q.
  refine WP.seq (WP.mono (qPart_ok G v hp hq B hk hS hU hu) fun t₁ Q₁ => ?_)
  obtain ⟨r, hr⟩ : ∃ r, Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (E.witT.drop used) = r :=
    ⟨_, rfl⟩
  have res₁ := Q₁.res
  have used₁ := Q₁.used
  rw [hr] at res₁ used₁
  obtain K₁ : AKeep E g s t₁ := ⟨Q₁.base, Q₁.chg.widen fun o ho => ⟨o, by simp [atRanges, ho], Nat.le_refl _,
    Nat.le_refl _⟩, Q₁.rd, Q₁.wr, Q₁.syms⟩
  obtain st₁ : t₁.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [Env.Chg.word v Q₁.chg (by simp only [fStatus, hdr]; omega_arith) (fun o ho => ⟨(Aat o (by simp [atRanges, ho])).1, by
      obtain szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
        rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
      simp only [qRanges, qPre, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sHScr, sPk, sPP, fRes, fUsed, fUsedOut, fStatus, hdr] <;> omega_arith⟩), hst]
  rw [refillAttempt_eq, hr]
  refine WP.seq (cmpF_end K₁.base.scr (o := fRes) (v := 0) (by simp only [fRes, hdr]; omega_arith) res₁ (status_lt r)
    (by decide) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  obtain K₂ := K₁.mem m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  refine WP.ite _ z₂ (fun h0 => stImm_end K₂.base.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_arith)
    fun t₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_) (fun h0 => ?_)
  · -- The witnesses ran out at q.
    obtain hn : r = none := by
      rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status]
    subst hn
    exact ⟨K₂.store G v hp (by simp [atRanges]) _ m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃,
      by show _ = _; rw [m₃, Mem.readW_writeW_self32]⟩
  refine WP.seq (cmpF_end K₂.base.scr (o := fRes) (v := 1) (by simp only [fRes, hdr]; omega_arith) (by rw [m₂]; exact res₁)
    (status_lt r) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_)
  obtain K₃ := K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃
  obtain mem₃ : t₃.mem = t₁.mem := by rw [m₃, m₂]
  refine WP.ite _ z₃ (fun h1 => ?_) (fun h1 => WP.block_nil ?_)
  rotate_left
  · -- q composite: the next seed.
    obtain ⟨rest, hrest⟩ : ∃ rest, r = some (false, rest) := by
      rcases r with _ | ⟨_ | _, rest⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status]
    subst hrest
    obtain cur := probablePrime_cursor hr
    rw [wl] at cur
    refine ⟨K₃, by rw [mem₃]; exact st₁, E.witLen - rest.length, by omega_arith, ?_, cur⟩
    rw [mem₃, used₁]; rfl
  -- q a probable prime: p.
  obtain ⟨rest, hrest⟩ : ∃ rest, r = some (true, rest) := by
    rcases r with _ | ⟨_ | _, rest⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status]
  subst hrest
  obtain cur := probablePrime_cursor hr
  rw [wl] at cur
  show WP isa _ t₃ fun t => AKeep E g s t ∧ ARes E g t.mem (pOutcome g.pLen
    (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k))
    (Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (chunk E k) rest))
  obtain hS₃ : t₃.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32 := by
    rw [K₃.word G v hp (by simp only [fSeed]; omega_arith) (by simp only [fSeed, fUsed, hdr]; omega_arith), hS]
  obtain hQ₃ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.qLen) =
      Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) := by rw [mem₃]; exact Q₁.q
  obtain hU₃ : t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (E.witLen - rest.length) := by
    rw [mem₃, used₁]; rfl
  refine WP.seq (WP.mono (pPart_ok G v hq K₃.base hk hS₃ hQ₃ (by omega_arith) hU₃ (by omega_arith)) fun t₄ ⟨P₄, R₄⟩ => ?_)
  rw [cur] at R₄
  obtain K₄ : AKeep E g s t₄ := ⟨P₄.base, K₃.chg.trans (P₄.chg.widen fun o ho => ⟨o, by simp [atRanges, ho],
    Nat.le_refl _, Nat.le_refl _⟩), by rw [P₄.rd, K₃.rd], by rw [P₄.wr, K₃.wr], by rw [P₄.syms, K₃.syms]⟩
  obtain ppA := ppRanges_apart G v
  obtain word₄ : ∀ d, fStatus ≤ d → d + 4 ≤ sState → t₄.mem.readW (off E.base d) 32 = t₃.mem.readW (off E.base d) 32 :=
    fun d h₁ h₂ => Env.Chg.word v P₄.chg (by simp only [sState] at h₂; omega_arith) fun o ho => ⟨(ppA o ho).1, by
      simp only [ppRanges, paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fCounter, fOffset, fStatus,
          hdr] at h₁ h₂ ⊢ <;> omega_arith⟩
  obtain st₄ : t₄.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [word₄ fStatus (Nat.le_refl _) (by simp only [fStatus, sState, hdr]; omega_arith), mem₃, st₁]
  obtain ⟨R, hR⟩ : ∃ R, Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k))
      (chunk E k) rest = R := ⟨_, rfl⟩
  rw [hR] at R₄ ⊢
  rcases R with _ | ⟨_ | p, rest'⟩
  · -- The witnesses ran out at p.
    refine WP.seq (cmpF_end K₄.base.scr (o := fP) (v := 0) (w := 0) (by simp only [fP, hdr]; omega_arith) R₄ (by decide)
      (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    obtain K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun _ => stImm_end K₅.base.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_arith)
      fun t₆ g₆ m₆ rd₆ wr₆ sy₆ => ⟨K₅.store G v hp (by simp [atRanges]) _ m₆ (g₆ _ (by decide)) (g₆ _ (by decide))
        rd₆ wr₆ sy₆, by show _ = _; rw [m₆, Mem.readW_writeW_self32]⟩) (fun h => by simp at h)
  · -- No p: the next seed.
    obtain ⟨fp₄, u, hu', fu₄, du⟩ := R₄
    refine WP.seq (cmpF_end K₄.base.scr (o := fP) (v := 0) (w := 2) (by simp only [fP, hdr]; omega_arith) fp₄ (by decide)
      (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    obtain K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun h => by simp at h) (fun _ => ?_)
    refine WP.seq (cmpF_end K₅.base.scr (o := fP) (v := 1) (w := 2) (by simp only [fP, hdr]; omega_arith)
      (by rw [m₅]; exact fp₄) (by decide) (by decide) fun t₆ g₆ m₆ rd₆ wr₆ sy₆ z₆ => ?_)
    obtain K₆ := K₅.mem m₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆ wr₆ sy₆
    refine WP.ite _ z₆ (fun h => by simp at h) (fun _ => WP.block_nil ⟨K₆, ?_, u, hu', ?_, du⟩)
    · rw [m₆, m₅, st₄]
    · rw [m₆, m₅, fu₄]
  · -- p: g.
    obtain ⟨fp₄, plo, phi, podd, ⟨u, hu', fu₄, du⟩, pk₄, pm₄, e₄, pv₄, one₄⟩ := R₄
    refine WP.seq (cmpF_end K₄.base.scr (o := fP) (v := 0) (w := 1) (by simp only [fP, hdr]; omega_arith) fp₄ (by decide)
      (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    obtain K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun h => by simp at h) (fun _ => ?_)
    refine WP.seq (cmpF_end K₅.base.scr (o := fP) (v := 1) (w := 1) (by simp only [fP, hdr]; omega_arith)
      (by rw [m₅]; exact fp₄) (by decide) (by decide) fun t₆ g₆ m₆ rd₆ wr₆ sy₆ z₆ => ?_)
    obtain K₆ := K₅.mem m₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆ wr₆ sy₆
    obtain mem₆ : t₆.mem = t₄.mem := by rw [m₆, m₅]
    refine WP.ite _ z₆ (fun _ => ?_) (fun h => by simp at h)
    have Qlo := qsh.2.1
    obtain hxl : (p - 1) / Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) < 2 ^ (32 * g.e) := by
      obtain ex : 8 * g.pLen ≤ 32 * g.e + (8 * g.qLen - 1) := by
        rw [G.e]; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
      rw [Nat.div_lt_iff_lt_mul (by omega_arith)]
      have := Nat.mul_le_mul_left (2 ^ (32 * g.e)) Qlo
      rw [← Nat.pow_add] at this
      have := Nat.pow_le_pow_right (n := 2) (by decide) ex
      omega_arith
    -- The window.
    refine WP.seq (WP.mono (gWindow_ok G v hp K₆.base (u := u) (by rw [mem₆]; exact fu₄) hu')
      fun t₆' ⟨BW, CW, rdW, wrW, syW, hsW, hsLenW⟩ => ?_)
    obtain K₆' : AKeep E g s t₆' := ⟨BW, K₆.chg.trans (CW.widen fun o ho => ⟨o, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp [atRanges], Nat.le_refl _, Nat.le_refl _⟩),
      by rw [rdW, K₆.rd], by rw [wrW, K₆.wr], by rw [syW, K₆.syms]⟩
    obtain wA : ∀ d n, d + n ≤ fHs ∨ fHsLen + 4 ≤ d → d + n ≤ E.size →
        Spec.Rsa.bytesAt t₆'.mem (off E.base d) n = Spec.Rsa.bytesAt t₆.mem (off E.base d) n := fun d n h₁ h₂ =>
      Env.Chg.scratch v CW h₂ fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega_arith, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] at h₁ ⊢ <;> omega_arith⟩
    obtain wV : ∀ d, fHsLen + 4 ≤ d → d + 4 * g.n32 ≤ E.size →
        val32 t₆'.mem E.base d g.n32 = val32 t₆.mem E.base d g.n32 :=
      fun d h h' => Env.Chg.val32 v CW h' fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega_arith, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] at h ⊢ <;> omega_arith⟩
    have n32 : g.n32 = g.pLen / 4 := rfl
    obtain vW := v.window hu'
    have pW : (E.window u).pLen = g.pLen := hp
    refine WP.seq (WP.mono (gPart_ok G vW pW (BW.toWindow u) hsW hsLenW (p := p)
      (Q := Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k))
      (x := (p - 1) / Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) rfl
      (by rw [show (E.window u).base = E.base from rfl, wV _ (by simp only [aOne, arr, fHsLen, hdr]; omega_arith) (by simp only [aOne, arr]; omega_arith), mem₆];
          exact one₄)
      (by rw [show (E.window u).base = E.base from rfl, wV _ (by simp only [aPm1, arr, fHsLen, hdr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), mem₆];
          exact pm₄)
      (by rw [show (E.window u).base = E.base from rfl, wV _ (by simp only [aP, arr, fHsLen, hdr]; omega_arith) (by simp only [aP, arr]; omega_arith), mem₆];
          exact pv₄)
      (by rw [show (E.window u).base = E.base from rfl, wV _ (by simp only [aE, arr, fHsLen, hdr]; omega_arith) (by simp only [aE, arr]; omega_arith), mem₆];
          exact e₄) hxl
      (by have := Nat.one_lt_two_pow (n := 8 * g.pLen - 1) (by omega_arith); omega_arith) podd phi)
      fun t₇ ⟨GK, GR, GH⟩ => ?_)
    clear z₆
    obtain K₇ : AKeep E g s t₇ := ⟨GK.base.ofWindow, K₆'.chg.trans ((GK.chg : E.Chg _ _ _).widen fun o ho =>
      ⟨o, by simp [atRanges, ho], Nat.le_refl _, Nat.le_refl _⟩), by rw [GK.rd, K₆'.rd], by rw [GK.wr, K₆'.wr],
      by rw [GK.syms, K₆'.syms]⟩
    obtain gA := gRanges_apart G v
    obtain gR : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + g.pLen + g.qLen →
        ∀ o ∈ gRanges g, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + n ≤ o.1) := fun h₁ h₂ o ho => ⟨(gA o ho).1, by
      simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩
    obtain gW : ∀ d, hdr ≤ d → (d + 4 ≤ fH ∨ (fG + 4 ≤ d ∧ d + 4 ≤ fLo) ∨ fLo + 4 ≤ d) → d + 4 ≤ sState →
        t₇.mem.readW (off E.base d) 32 = t₆'.mem.readW (off E.base d) 32 :=
      fun d h₁ h₂ h₃ => Env.Chg.word v (GK.chg : E.Chg _ _ _) (by simp only [sState] at h₃; omega_arith)
        fun o ho => ⟨(gA o ho).1, by
        simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, sState, hdr] at h₁ h₂ h₃ ⊢ <;> omega_arith⟩
    obtain st₆' : t₆'.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
      rw [Env.Chg.word v CW (by simp only [fStatus, hdr]; omega_arith) (fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega_arith, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, fStatus, hdr] <;> omega_arith⟩), mem₆, st₄]
    obtain st₇ : t₇.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
      rw [gW fStatus (by simp only [fStatus]; omega_arith) (.inr (.inl (by simp only [fG, fStatus, fLo, hdr]; omega_arith)))
        (by simp only [fStatus, sState, hdr]; omega_arith), st₆']
    obtain hsLen₇ : t₇.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (E.window u).hsLen := by
      rw [gW fHsLen (by simp only [fHsLen]; omega_arith) (.inr (.inr (by simp only [fHsLen, fLo, hdr]; omega_arith)))
        (by simp only [fHsLen, sState, hdr]; omega_arith), hsLenW]
    obtain pk₇ : Spec.Rsa.bytesAt t₇.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p := by
      rw [Env.Chg.scratch v (GK.chg : E.Chg _ _ _) (by simp only [sPk]; omega_arith) (gR (Nat.le_refl _) (by omega_arith)),
        wA _ _ (by simp only [sPk, fHsLen, hdr]; omega_arith) (by simp only [sPk]; omega_arith), mem₆, pk₄]
    obtain qk₇ : Spec.Rsa.bytesAt t₇.mem (off E.base (sPk + g.pLen)) g.qLen =
        Spec.Dsa.encodeBE g.qLen (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) := by
      rw [Env.Chg.scratch v (GK.chg : E.Chg _ _ _) (by simp only [sPk]; omega_arith) (gR (by omega_arith) (by omega_arith)),
        wA _ _ (by simp only [sPk, fHsLen, hdr]; omega_arith) (by simp only [sPk]; omega_arith), mem₆,
        Env.Chg.scratch v P₄.chg (by simp only [sPk]; omega_arith) (fun o ho => ⟨(ppA o ho).1, by
          simp only [ppRanges, paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fCounter, fOffset,
              hdr] <;> omega_arith⟩)]
      rw [← hQ₃]
      obtain h := encodeBE_decodeBE (Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.qLen)
      rw [VG.Proof.Bignum.bytesAt_length] at h
      exact h.symm
    -- The candidates read.
    have hl' : E.witT.length = E.witLen := wl
    obtain hWin := hList_window (E := E) (u := u) hl'
    obtain ⟨cnt, hcnt⟩ : ∃ cnt, generatorCount p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k))
        (hList (E.window u)) = cnt := ⟨_, rfl⟩
    obtain cntLe : g.pLen * cnt ≤ E.witLen - u := by
      obtain c1 := generatorCount_le p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (hList (E.window u))
      rw [hcnt, hList_length, show (E.window u).pLen = g.pLen from hp] at c1
      obtain hTl : (E.window u).hT.length ≤ E.witLen - u := by
        simp only [Env.hT, Env.window, List.length_take, List.length_drop, hl']; omega_arith
      have := Nat.mul_le_mul_left g.pLen c1
      have := Nat.mul_div_le (E.window u).hT.length g.pLen
      omega_arith
    have wp := v.witPtr
    have wf := v.witFit
    refine WP.seq (ld_ok K₇.base.scr (d := fH) (by simp only [fH, hdr]; omega_arith) fun t₈ u₈ =>
      ld_ok (Scr.of_eq K₇.base.scr (u₈.other _ (by decide)) (u₈.other _ (by decide)) u₈.wr) (d := fWit)
        (by simp only [fWit, hdr]; omega_arith) fun t₉ u₉ => wp_sub fun t₁₀ u₁₀ _ =>
      st_ok (Scr.of_eq K₇.base.scr (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)])
        (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)])
        (by rw [u₁₀.wr, u₉.wr, u₈.wr])) (d := fUsed) (by simp only [fUsed, hdr]; omega_arith) fun t₁₁ M₁₁ =>
      WP.block_nil ?_)
    have GH' : t₇.mem.readW (off E.base fH) 32 = hEnd (E.window u) p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) :=
      GH
    obtain used₁₁ : t₁₁.mem = t₇.mem.writeW (off E.base fUsed) (BitVec.ofNat 32 (u + g.pLen * cnt)) := by
      rw [M₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, GH', u₈.mem, K₇.base.witW, hEnd,
        hcnt, show (E.window u).pLen = g.pLen from hp, show (E.window u).hs = E.wit + BitVec.ofNat 64 u from rfl,
        VG.Offset.add_add, ← ptr_add, BitVec.add_comm (E.wit.setWidth 32), BitVec.add_sub_cancel]
    obtain K₁₁ := K₇.store G v hp (d := fUsed) (by simp [atRanges, qRanges]) _ used₁₁
      (by rw [M₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)])
      (by rw [M₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)])
      (by rw [M₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd]) (by rw [M₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr])
      (by rw [M₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms])
    obtain w₁₁ : ∀ d, d + 4 ≤ fUsed ∨ fUsed + 4 ≤ d → d + 4 ≤ sState →
        t₁₁.mem.readW (off E.base d) 32 = t₇.mem.readW (off E.base d) 32 := fun d h₁ h₂ => by
      rw [used₁₁]; exact word_store_other v _ (by simp only [sState] at h₂; omega_arith)
        (by simp only [fUsed, hdr]; omega_arith) h₁ _
    obtain fu₁₁ : t₁₁.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (u + g.pLen * cnt) := by
      rw [used₁₁, Mem.readW_writeW_self32]
    obtain du' : E.witT.drop (u + g.pLen * cnt) = rest'.drop (g.pLen * cnt) := by rw [← du, List.drop_drop]
    obtain pk₁₁ : Spec.Rsa.bytesAt t₁₁.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p := by
      rw [used₁₁, Env.Chg.scratch v ((Env.Chg.refl [(fUsed, 4)] t₇.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, sPk, hdr]; omega_arith), pk₇]
    obtain qk₁₁ : Spec.Rsa.bytesAt t₁₁.mem (off E.base (sPk + g.pLen)) g.qLen =
        Spec.Dsa.encodeBE g.qLen (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) := by
      rw [used₁₁, Env.Chg.scratch v ((Env.Chg.refl [(fUsed, 4)] t₇.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, sPk, hdr]; omega_arith), qk₇]
    obtain gk₁₁ : ∀ gv, Spec.Rsa.bytesAt t₇.mem (off E.base (sPk + g.pLen + g.qLen)) g.pLen =
        Spec.Dsa.encodeBE g.pLen gv → Spec.Rsa.bytesAt t₁₁.mem (off E.base (sPk + g.pLen + g.qLen)) g.pLen =
        Spec.Dsa.encodeBE g.pLen gv := fun gv h => by
      rw [used₁₁, Env.Chg.scratch v ((Env.Chg.refl [(fUsed, 4)] t₇.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, sPk, hdr]; omega_arith), h]
    obtain st₁₁ : t₁₁.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
      rw [w₁₁ fStatus (.inr (by simp only [fUsed, fStatus, hdr]; omega_arith)) (by simp only [fStatus, sState, hdr]; omega_arith),
        st₇]
    show WP isa _ t₁₁ fun t => AKeep E g s t ∧ ARes E g t.mem
      (winResult g.pLen p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) rest')
    obtain hWin' : hList (E.window u) = windowCandidates g.pLen Spec.Dsa.generatorAttempts (E.witT.drop u) := by
      rw [← hp]; exact hWin
    obtain du'' : E.witT.drop (u + g.pLen * cnt) = (E.witT.drop u).drop (g.pLen * cnt) := by rw [List.drop_drop]
    obtain bnd : u + g.pLen * cnt ≤ E.witLen := by omega_arith
    unfold winResult
    rw [← du, ← hWin', hcnt]
    rcases hg : Spec.Dsa.generator p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (hList (E.window u)) with _ | gv
    · -- No g: rejected, or `rand` ran out inside the window.
      rw [hg] at GR
      obtain fg₁₁ : t₁₁.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 2 := by
        rw [w₁₁ fG (.inr (by simp only [fUsed, fG, hdr]; omega_arith)) (by simp only [fG, sState, hdr]; omega_arith)]
        exact GR
      refine WP.seq (cmpF_end K₁₁.base.scr (o := fG) (v := 1) (w := 2) (by simp only [fG, hdr]; omega_arith) fg₁₁
        (by decide) (by decide) fun t₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sy₁₂ z₁₂ => ?_)
      obtain K₁₂ := K₁₁.mem m₁₂ (g₁₂ _ (by decide)) (g₁₂ _ (by decide)) rd₁₂ wr₁₂ sy₁₂
      refine WP.ite _ z₁₂ (fun h => by simp at h) (fun _ => ?_)
      obtain cntAll : cnt = (E.window u).hT.length / g.pLen := by
        rw [← hcnt, count_none hg, hList_length, show (E.window u).pLen = g.pLen from hp]
      obtain hTl : (E.window u).hT.length = min (E.witLen - u) (128 * g.pLen) := by
        simp only [Env.hT, Env.window, List.length_take, List.length_drop, hl', hp]; omega_arith
      obtain wlen : (E.window u).hsLen = min (E.witLen - u) (128 * g.pLen) := by
        simp only [Env.window, hp]
      unfold Geo.gShort
      refine WP.seq (cmpFb_end K₁₂.base.scr (o := fHsLen) (v := 128 * g.pLen) (w := (E.window u).hsLen)
        (by simp only [fHsLen, hdr]; omega_arith)
        (by rw [m₁₂, w₁₁ fHsLen (.inr (by simp only [fUsed, fHsLen, hdr]; omega_arith))
          (by simp only [fHsLen, sState, hdr]; omega_arith)]; exact hsLen₇)
        (by rw [wlen]; omega_arith) (by omega_arith) fun t₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ sy₁₃ c₁₃ => ?_)
      obtain K₁₃ := K₁₂.mem m₁₃ (g₁₃ _ (by decide)) (g₁₃ _ (by decide)) rd₁₃ wr₁₃ sy₁₃
      refine WP.ite _ c₁₃ (fun hs => stImm_end K₁₃.base.scr (o := fStatus) (v := 2)
        (by simp only [fStatus, hdr]; omega_arith) fun t₁₄ g₁₄ m₁₄ rd₁₄ wr₁₄ sy₁₄ => ?_) (fun hs => WP.block_nil ?_)
      · -- The window was short: `rand` ran out.
        obtain short : ¬ Spec.Dsa.generatorAttempts * g.pLen ≤ (E.witT.drop u).length := by
          have := of_decide_eq_true hs
          rw [wlen] at this
          simp only [List.length_drop, hl', Spec.Dsa.generatorAttempts]
          omega_arith
        simp only [short, ↓reduceIte]
        exact ⟨K₁₃.store G v hp (by simp [atRanges]) _ m₁₄ (g₁₄ _ (by decide)) (g₁₄ _ (by decide)) rd₁₄ wr₁₄ sy₁₄,
          by show _ = _; rw [m₁₄, Mem.readW_writeW_self32]⟩
      · -- A whole window without g: rejected.
        obtain full : Spec.Dsa.generatorAttempts * g.pLen ≤ (E.witT.drop u).length := by
          have := of_decide_eq_false hs
          rw [wlen] at this
          simp only [List.length_drop, hl', Spec.Dsa.generatorAttempts]
          omega_arith
        obtain c128 : cnt = Spec.Dsa.generatorAttempts := by
          rw [cntAll, hTl]
          simp only [List.length_drop, hl', Spec.Dsa.generatorAttempts] at full
          rw [Nat.min_eq_right (by omega_arith), Spec.Dsa.generatorAttempts, Nat.mul_div_cancel _ (by omega_arith)]
        simp only [full, ↓reduceIte]
        refine ⟨K₁₃, by rw [m₁₃, m₁₂, st₁₁], u + g.pLen * cnt, bnd, by rw [m₁₃, m₁₂, fu₁₁], ?_⟩
        rw [du'', c128, Nat.mul_comm]
    · -- g: the domain check.
      rw [hg] at GR
      obtain ⟨fg₇, gk₇⟩ := GR
      obtain fg₁₁ : t₁₁.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 1 := by
        rw [w₁₁ fG (.inr (by simp only [fUsed, fG, hdr]; omega_arith)) (by simp only [fG, sState, hdr]; omega_arith)]
        exact fg₇
      refine WP.seq (cmpF_end K₁₁.base.scr (o := fG) (v := 1) (w := 1) (by simp only [fG, hdr]; omega_arith) fg₁₁
        (by decide) (by decide) fun t₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sy₁₂ z₁₂ => ?_)
      obtain K₁₂ := K₁₁.mem m₁₂ (g₁₂ _ (by decide)) (g₁₂ _ (by decide)) rd₁₂ wr₁₂ sy₁₂
      refine WP.ite _ z₁₂ (fun _ => ?_) (fun h => by simp at h)
      obtain glt := generator_lt (by omega_arith) hg
      obtain pq : Spec.Rsa.bytesAt t₁₂.mem (off E.base sPk) (2 * g.pLen + g.qLen) =
          Spec.Dsa.encodeParams g.pLen g.qLen ⟨p, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k), gv⟩ := by
        rw [m₁₂, show 2 * g.pLen + g.qLen = g.pLen + (g.qLen + g.pLen) by omega_arith, bytesAt_append, bytesAt_append,
          show VG.Proof.Bignum.off (off E.base sPk) g.pLen = off E.base (sPk + g.pLen) from off_add_ofNat _ _ _,
          show VG.Proof.Bignum.off (off E.base (sPk + g.pLen)) g.qLen = off E.base (sPk + g.pLen + g.qLen)
            from off_add_ofNat _ _ _, pk₁₁, qk₁₁, gk₁₁ gv gk₇, Spec.Dsa.encodeParams, List.append_assoc]
      obtain e256 : ∀ n, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [Nat.pow_mul]
      obtain ck := check_encodedParams (a := ⟨p, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k), gv⟩)
        (pLen := g.pLen) (qLen := g.qLen)
        (by rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide)
        (by rw [e256]; exact phi) (by rw [e256]; exact qsh.2.2) (by show gv < 256 ^ g.pLen; rw [e256]; omega_arith)
      refine WP.mono (check_ok G v hp hq K₁₂.base) fun t₉ ⟨B₉, C₉, rd₉, wr₉, sy₉, st₉⟩ => ?_
      rw [pq, ck] at st₉
      obtain K₉ : AKeep E g s t₉ := ⟨B₉, K₁₂.chg.trans (C₉.widen fun o ho => ⟨o, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp [atRanges],
        Nat.le_refl _, Nat.le_refl _⟩), by rw [rd₉, K₁₂.rd], by rw [wr₉, K₁₂.wr], by rw [sy₉, K₁₂.syms]⟩
      obtain chkR : ∀ o ∈ [(sChk, 16 * g.pLen * 8), (fStatus, 4)], o.1 + o.2 ≤ E.size := fun o ho => by
        obtain room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [sChk, fStatus, hdr] <;> omega_arith
      obtain fu₉ : t₉.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (u + g.pLen * cnt) := by
        rw [Env.Chg.word v C₉ (by simp only [fUsed, hdr]; omega_arith) (fun o ho => ⟨chkR o ho, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp only [sChk, fUsed, fStatus, hdr] <;> omega_arith⟩), m₁₂, fu₁₁]
      by_cases hv : Spec.Dsa.parametersValid ⟨p, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k), gv⟩
      · simp only [hv, decide_true, ↓reduceIte] at st₉ ⊢
        refine ⟨K₉, st₉, ?_, u + g.pLen * cnt, bnd, fu₉, du''⟩
        rw [Env.Chg.scratch v C₉ (by simp only [sPk]; omega_arith) (fun o ho => ⟨chkR o ho, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp only [sChk, sPk, fStatus, hdr] <;> omega_arith⟩), pq]
      · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte] at st₉ ⊢
        exact ⟨K₉, by rw [st₉, m₁₂, st₁₁], u + g.pLen * cnt, bnd, fu₉, du''⟩

end VG.Proof.Dsa.X86.Generation
