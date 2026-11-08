module

-- separate module: the proof, which needs none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.AesGcm.ScratchOpenTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToSplit.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, in one pass, x86-64: `Verified`

Untrusted: everything here is checked by Lean. `openToSplit` meets the contracts
of `Proof/AesGcm/RoundsTo.lean` for prepared key contexts with a working
space appended (`Proof/AesGcm/ScratchOpenTo.lean`) and 152 bytes of stack
(its frame of 88, the call's return address and the 56 bytes of
`vg_aes_gcm_open_split`), and so, in a frame of 2624 bytes holding its
working space (`Verified.stackArgScratch`), those contracts with 2776 bytes
of stack (`openToSplitPrepared_framed`). `openToSel` chooses on entry between
`open_to` by a copy (`OpenTo.openToPrepared_verified`, 2728 bytes) and that
frame (`Verified.entryBranch`): the comparison of `len` with the threshold
writes only `rax` and the flags, which no contract reads (`Same`), and leaks
only the address of `len`; the branch depends only on `len`, which is public
(`openToSelPrepared_verified`, `openToSelPrepared16_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenToSplit

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem toPre_prepared {s : State} (h : (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).pre s) :
    ToPreS CtxMode.prepared s := by
  sig_pre [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa'⟩, rk, rn, ra, rs, rdd, rt, rw, -,
    bk, bn, ba, bs, bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da dw rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, kw, nw, aw, sw, tw, dw, wa', rk, rn, ra, rs, rdd, rt, rw, bk, bn, ba, bs,
    bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, w₁, w₂, ro, dl, hpw⟩

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The comparison of `len` with `thr`. -/
theorem entry_run {thr : Nat} (hT : thr < 2 ^ 31) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    ∃ u, execBlock isa (Impl.AesGcm.X86_64.OpenToSplit.cmpLen thr) s = some (u, [.addr (stackArgAddr s 1)]) ∧
      (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.mxcsr = s.mxcsr ∧
      eval .ae u = some (decide (thr ≤ (stackArg s 1).toNat)) := by
  have ea : s.ea (Impl.AesGcm.X86_64.at_ .rsp 16) = stackArgAddr s 1 := rfl
  refine ⟨?u, ?h1, ?h2, ?h3, ?h4, ?h5, ?h6, ?h7⟩
  case h1 => simp [execBlock, Impl.AesGcm.X86_64.OpenToSplit.cmpLen, exec, readSrc, ea, hin, addrs, srcAddrs,
    State.load64, execAlu]; rfl
  case h3 => rfl
  case h4 => rfl
  case h5 => rfl
  case h6 => rfl
  case h2 => intro r hr; simp [gpr_arithFlags, gpr_setReg, hr]
  case h7 =>
    simp only [eval, cf_arithFlags, gpr_setReg, ↓reduceIte, sx_ofNat hT, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show thr < 2 ^ 64 by omega), Option.map_some, ← decide_not, Nat.not_lt]
    rfl

/-! ## The code -/

theorem openToSplit_mx (f : Impl.AesGcm.X86_64.Fn) (h : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Impl.AesGcm.X86_64.OpenToSplit.openToSplit f).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.AesGcm.X86_64.OpenToSplit.openToSplit, Impl.AesGcm.X86_64.OpenToSplit.callArgs,
    Impl.AesGcm.X86_64.OpenTo.after, Impl.AesGcm.X86_64.OpenTo.wipe, Code.allInstrs, h, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openToSplit_spAll (f : Impl.AesGcm.X86_64.Fn) (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.AesGcm.X86_64.OpenToSplit.openToSplit f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.AesGcm.X86_64.OpenToSplit.openToSplit, Impl.AesGcm.X86_64.OpenToSplit.callArgs,
    Impl.AesGcm.X86_64.OpenTo.after, Impl.AesGcm.X86_64.OpenTo.wipe, Code.all, h, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openToSplit_xdepth (f : Impl.AesGcm.X86_64.Fn) (h : f.code.x86_64Depth ≤ 56) :
    (Impl.AesGcm.X86_64.OpenToSplit.openToSplit f).x86_64Depth ≤ 152 := by
  simp only [Impl.AesGcm.X86_64.OpenToSplit.openToSplit, Impl.AesGcm.X86_64.OpenToSplit.callArgs,
    Impl.AesGcm.X86_64.OpenTo.after, Impl.AesGcm.X86_64.OpenTo.wipe, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, Nat.max_le]
  omega

theorem openToSel_spAll (thr : Nat) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (f fS : Impl.AesGcm.X86_64.Fn)
    (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (hS : fS.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.AesGcm.X86_64.OpenToSplit.openToSel thr w f fS).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.AesGcm.X86_64.OpenToSplit.openToSel, Code.iteCold, Code.all,
    X86_64.withStackArgScratch_spSafe (openToSplit_spAll fS hS), OpenTo.openTo_spAll w f h, Bool.and_true]
  rfl

/-! ## The contracts with the working space -/

theorem toPost_prepared {s s' : State} (h : OpenTo.toPost s s') :
    (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).post s s' := by
  sig_post [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq]
  exact fun _ => h

theorem toPub_prepared {s₁ s₂ : State} (hp : (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).pub s₁ s₂) :
    toPubS s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig, Spec.Gcm.openToLeak,
    X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := hp
  refine ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_⟩, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | 6, _ => exact a₆
  | n + 7, h => exact absurd h (by omega)

/-- A state satisfying the precondition of `openToSplit`: `OpenTo.toSatP`, with
`work` at `0x7000`. -/
def toSatS : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9029 then 0x60 else
      if a = 0x9039 then 0x70 else 0) else 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 56⟩]
  wr := [⟨0x5000, 0⟩, ⟨0x7000, 2560⟩]

theorem toSatS_pre : ∃ s, (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).pre s := by
  refine ⟨toSatS, ?_⟩
  sig_pre [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq, toSatS, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

theorem prepared_implies :
    (toSK CtxMode.prepared).Implies (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152) :=
  ⟨fun _ h => toPre_prepared h, fun _ _ _ h => toPost_prepared h, fun _ _ _ _ h => toPub_prepared h, toSatS_pre⟩

/-- `openToSplit`, calling an instance of `vg_aes_gcm_open_split` for a prepared
key context, with its working space as an argument. -/
theorem openToSplitPrepared_core (F : OpenSplitFn CtxMode.prepared) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn)
      (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152) :=
  Verified.of_correct (k := toSK CtxMode.prepared)
    (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs; exact ⟨t, s', he, ha, hp⟩) (openToSplit_ct F)
    prepared_implies

/-! ## In its frame -/

theorem toSatP2776_pre : ∃ s, (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre s := by
  refine ⟨OpenTo.toSatP, ?_⟩
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq, OpenTo.toSatP,
    OpenTo.toSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

/-- `openToSplit` in its frame of 2624 bytes, holding its working space. -/
theorem openToSplitPrepared_framed (F : OpenSplitFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn))
      (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openToPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.openToPowersPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 152)
    (leak := some (Spec.Gcm.openToLeak X86_64.abi.ptrBits)) (bytes := 2624) (openToSplitPrepared_core F)
    (by decide) (by decide) (by decide) (openToSplit_spAll F.fn F.spAll) (openToSplit_xdepth F.fn F.xd)
    (Proof.AesGcm.openToPreparedPre_local _) (Proof.AesGcm.openToRoundsPost_local _) toSatP2776_pre
    (hleak := Proof.AesGcm.openToLeak_local _)

/-! ## Choosing by length -/

/-- `u` is `s` but for `rax` and the flags. -/
structure Same (s u : State) : Prop where
  gpr : ∀ r, r ≠ .rax → u.gpr r = s.gpr r
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mx : u.mxcsr = s.mxcsr

theorem Same.saa {s u : State} (h : Same s u) (i : Nat) : stackArgAddr u i = stackArgAddr s i := by
  simp only [stackArgAddr, h.gpr .rsp (by decide)]

theorem Same.sa {s u : State} (h : Same s u) (i : Nat) : stackArg u i = stackArg s i := by
  simp only [stackArg, h.saa, h.mem]

theorem Same.abi {s u s' : State} (h : Same s u) (a : abiPreserved u s') : abiPreserved s s' :=
  ⟨fun r hr => by rw [a.1 r hr, h.gpr r (by rintro rfl; simp [calleeSaved] at hr)],
    by rw [← h.gpr .rsp (by decide), a.2.1, h.mem], by rw [a.2.2, h.mx]⟩

/-- What `open_to`'s contract with 2776 bytes of stack gives of `OpenTo.toK`'s
precondition, with 2728. -/
theorem toPre2776_prepared {s : State} (h : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre s) :
    OpenTo.ToPre CtxMode.prepared s := by
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, da⟩, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg,
    wk, wn, wa, ws, wd, wt, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da rdd bd wd
  have sb := Offset.sub_below (s.gpr .rsp) (a := 2728) (n := 2728) (b := 2776) (m := 2776) (by omega) (by omega)
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, rk, rn, ra, rs, rdd, rt, rarg, bk.sub_left sb, bn.sub_left sb,
    ba.sub_left sb, bs.sub_left sb, bd.sub_left sb, bt.sub_left sb, barg.sub_left sb, wk, wn, wa, ws, wd, wt,
    by omega, w₂, ro, dl, hpw⟩

theorem toPub2776_prepared {s₁ s₂ : State}
    (hp : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pub s₁ s₂) : OpenTo.toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅⟩ := hp
  refine ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | n + 6, h => exact absurd h (by omega)

theorem pre2776_congr {s u : State} (h : Same s u)
    (hs : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre s) :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre u := by
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at hs ⊢
  simp only [h.sa, h.saa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem, h.rd, h.wr]
  exact hs

theorem post2776_congr {s u s' : State} (h : Same s u)
    (q : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).post u s') :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).post s s' := by
  sig_post [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q ⊢
  simp only [h.sa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.mem] at q
  exact q

theorem pub2776_congr {s u s' u' : State} (h : Same s u) (h' : Same s' u')
    (q : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pub s s') :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pub u u' := by
  sig_pub [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q ⊢
  simp only [h.sa, h.saa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
    h'.sa, h'.saa, h'.gpr .rdi (by decide), h'.gpr .rsi (by decide), h'.gpr .rdx (by decide),
    h'.gpr .rcx (by decide), h'.gpr .r8 (by decide), h'.gpr .r9 (by decide), h'.gpr .rsp (by decide), h'.mem]
  exact q

theorem pre_narrow {s : State} (h : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre s) :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).pre s := by
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at h ⊢
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h ⊢
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h ⊢
  obtain ⟨w₁, w₂, rd, wr, hd, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg, rest⟩ := h
  have sb := Offset.sub_below (s.gpr .rsp) (a := 2728) (n := 2728) (b := 2776) (m := 2776) (by omega) (by omega)
  exact ⟨by omega, w₂, rd, wr, hd, rk, rn, ra, rs, rdd, rt, rarg, bk.sub_left sb, bn.sub_left sb, ba.sub_left sb,
    bs.sub_left sb, bd.sub_left sb, bt.sub_left sb, barg.sub_left sb, rest⟩

theorem post_widen {s u s' : State} (h : Same s u)
    (q : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).post u s') :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).post s s' := by
  sig_post [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q ⊢
  simp only [h.sa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.mem] at q
  exact q

theorem pub_narrow {s u s' u' : State} (h : Same s u) (h' : Same s' u')
    (q : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pub s s') :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).pub u u' := by
  have q' := pub2776_congr h h' q
  sig_pub [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q' ⊢
  exact q'

/-- `vg_aes_gcm_open_to_prepared`: by a copy below `thr` bytes, and in one
pass from `thr` on. -/
theorem openToSelPrepared_verified (thr : Nat) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width)
    (F : OpenTo.OpenFn CtxMode.prepared) (FS : OpenSplitFn CtxMode.prepared) (hT : thr < 2 ^ 31 := by decide) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSel thr w F.fn FS.fn)
      (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776) := by
  have run (s : State) (hs : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre s) :
      ∃ u, execBlock isa (Impl.AesGcm.X86_64.OpenToSplit.cmpLen thr) s = some (u, [.addr (stackArgAddr s 1)]) ∧
        (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.mxcsr = s.mxcsr ∧
        eval .ae u = some (decide (thr ≤ (stackArg s 1).toNat)) := by
    have hp := toPre2776_prepared hs
    refine entry_run hT s ⟨OpenTo.argR s, List.mem_append_left _ (by rw [hp.rd]; simp), ?_⟩
    have := hp.w₂
    show (⟨stackArgAddr s 0, 8 * 6⟩ : Region).Contains (stackArgAddr s 1) 8
    simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  refine Verified.entryBranch (p := fun s => decide (thr ≤ (stackArg s 1).toNat))
    (fun s => [.addr (stackArgAddr s 1)]) (openToSplitPrepared_framed FS) (OpenTo.openToPrepared_verified w F)
    (fun s hs => ?_) ?_ toSatP2776_pre
  · obtain ⟨u, e, g, hm, hrd, hwr, hmx, ev⟩ := run s hs
    have hS : Same s u := ⟨g, hm, hrd, hwr, hmx⟩
    exact ⟨u, e, ev, fun _ => ⟨pre2776_congr hS hs, fun s' a q => ⟨hS.abi a, post2776_congr hS q⟩⟩,
      fun _ => ⟨pre_narrow (pre2776_congr hS hs), fun s' a q => ⟨hS.abi a, post_widen hS q⟩⟩⟩
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, g, hm, hrd, hwr, hmx, -⟩ := run s hs
    obtain ⟨u₀', e₀', g', hm', hrd', hwr', hmx', -⟩ := run s' hs'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hS : Same s u₀ := ⟨g, hm, hrd, hwr, hmx⟩
    have hS' : Same s' u₀' := ⟨g', hm', hrd', hwr', hmx'⟩
    obtain ⟨-, -, -, -, -, -, qsp, qa, -⟩ := toPub2776_prepared hq
    refine ⟨by simp only [stackArgAddr, qsp], by simp only [Proof.AesGcm.arg] at qa; rw [qa 1 (by decide)],
      fun _ => pub2776_congr hS hS' hq, fun _ => pub_narrow hS hS' hq⟩


/-! ## With 16 prepared powers -/

theorem toPre_prepared16 {s : State} (h : (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).pre s) :
    ToPreS CtxMode.prepared16 s := by
  sig_pre [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Spec.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa'⟩, rk, rn, ra, rs, rdd, rt, rw, -,
    bk, bn, ba, bs, bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da dw rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, kw, nw, aw, sw, tw, dw, wa', rk, rn, ra, rs, rdd, rt, rw, bk, bn, ba, bs,
    bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, w₁, w₂, ro, dl, hpw⟩

theorem toPost_prepared16 {s s' : State} (h : OpenTo.toPost s s') :
    (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).post s s' := by
  sig_post [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq]
  exact fun _ => h

theorem toPub_prepared16 {s₁ s₂ : State} (hp : (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).pub s₁ s₂) :
    toPubS s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig, Spec.Gcm.openToLeak,
    X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := hp
  refine ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_⟩, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | 6, _ => exact a₆
  | n + 7, h => exact absurd h (by omega)

theorem toSatS16_pre : ∃ s, (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).pre s := by
  refine ⟨toSatS, ?_⟩
  sig_pre [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Spec.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq, toSatS, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowers16Repr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

theorem prepared16_implies :
    (toSK CtxMode.prepared16).Implies (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152) :=
  ⟨fun _ h => toPre_prepared16 h, fun _ _ _ h => toPost_prepared16 h, fun _ _ _ _ h => toPub_prepared16 h, toSatS16_pre⟩

/-- `openToSplit`, calling an instance of `vg_aes_gcm_open_split` for a prepared
key context, with its working space as an argument. -/
theorem openToSplitPrepared16_core (F : OpenSplitFn CtxMode.prepared16) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn)
      (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152) :=
  Verified.of_correct (k := toSK CtxMode.prepared16)
    (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs; exact ⟨t, s', he, ha, hp⟩) (openToSplit_ct F)
    prepared16_implies

theorem toSatP16_2776_pre : ∃ s, (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre s := by
  refine ⟨OpenTo.toSatP, ?_⟩
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq, OpenTo.toSatP,
    OpenTo.toSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowers16Repr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

/-- `openToSplit` in its frame of 2624 bytes, holding its working space. -/
theorem openToSplitPrepared16_framed (F : OpenSplitFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn))
      (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openToPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 152)
    (leak := some (Spec.Gcm.openToLeak X86_64.abi.ptrBits)) (bytes := 2624) (openToSplitPrepared16_core F)
    (by decide) (by decide) (by decide) (openToSplit_spAll F.fn F.spAll) (openToSplit_xdepth F.fn F.xd)
    (Proof.AesGcm.openToPrepared16Pre_local _) (Proof.AesGcm.openToRoundsPost_local _) toSatP16_2776_pre
    (hleak := Proof.AesGcm.openToLeak_local _)

/-- What `open_to`'s contract with 2776 bytes of stack gives of `OpenTo.toK`'s
precondition, with 2728. -/
theorem toPre2776_prepared16 {s : State} (h : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre s) :
    OpenTo.ToPre CtxMode.prepared16 s := by
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, da⟩, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg,
    wk, wn, wa, ws, wd, wt, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da rdd bd wd
  have sb := Offset.sub_below (s.gpr .rsp) (a := 2728) (n := 2728) (b := 2776) (m := 2776) (by omega) (by omega)
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, rk, rn, ra, rs, rdd, rt, rarg, bk.sub_left sb, bn.sub_left sb,
    ba.sub_left sb, bs.sub_left sb, bd.sub_left sb, bt.sub_left sb, barg.sub_left sb, wk, wn, wa, ws, wd, wt,
    by omega, w₂, ro, dl, hpw⟩

theorem toPub2776_prepared16 {s₁ s₂ : State}
    (hp : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pub s₁ s₂) : OpenTo.toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅⟩ := hp
  refine ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | n + 6, h => exact absurd h (by omega)

theorem pre2776_congr16 {s u : State} (h : Same s u)
    (hs : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre s) :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre u := by
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at hs ⊢
  simp only [h.sa, h.saa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem, h.rd, h.wr]
  exact hs

theorem post2776_congr16 {s u s' : State} (h : Same s u)
    (q : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).post u s') :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).post s s' := by
  sig_post [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q ⊢
  simp only [h.sa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.mem] at q
  exact q

theorem pub2776_congr16 {s u s' u' : State} (h : Same s u) (h' : Same s' u')
    (q : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pub s s') :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pub u u' := by
  sig_pub [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q ⊢
  simp only [h.sa, h.saa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
    h'.sa, h'.saa, h'.gpr .rdi (by decide), h'.gpr .rsi (by decide), h'.gpr .rdx (by decide),
    h'.gpr .rcx (by decide), h'.gpr .r8 (by decide), h'.gpr .r9 (by decide), h'.gpr .rsp (by decide), h'.mem]
  exact q

theorem pre_narrow16 {s : State} (h : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre s) :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).pre s := by
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at h ⊢
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h ⊢
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h ⊢
  obtain ⟨w₁, w₂, rd, wr, hd, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg, rest⟩ := h
  have sb := Offset.sub_below (s.gpr .rsp) (a := 2728) (n := 2728) (b := 2776) (m := 2776) (by omega) (by omega)
  exact ⟨by omega, w₂, rd, wr, hd, rk, rn, ra, rs, rdd, rt, rarg, bk.sub_left sb, bn.sub_left sb, ba.sub_left sb,
    bs.sub_left sb, bd.sub_left sb, bt.sub_left sb, barg.sub_left sb, rest⟩

theorem post_widen16 {s u s' : State} (h : Same s u)
    (q : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).post u s') :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).post s s' := by
  sig_post [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q ⊢
  simp only [h.sa, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
    h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.mem] at q
  exact q

theorem pub_narrow16 {s u s' u' : State} (h : Same s u) (h' : Same s' u')
    (q : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pub s s') :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).pub u u' := by
  have q' := pub2776_congr16 h h' q
  sig_pub [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] at q' ⊢
  exact q'

/-- `vg_aes_gcm_open_to_prepared16`: by a copy below `thr` bytes, and in one
pass from `thr` on. -/
theorem openToSelPrepared16_verified (thr : Nat) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width)
    (F : OpenTo.OpenFn CtxMode.prepared16) (FS : OpenSplitFn CtxMode.prepared16) (hT : thr < 2 ^ 31 := by decide) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSel thr w F.fn FS.fn)
      (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776) := by
  have run (s : State) (hs : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre s) :
      ∃ u, execBlock isa (Impl.AesGcm.X86_64.OpenToSplit.cmpLen thr) s = some (u, [.addr (stackArgAddr s 1)]) ∧
        (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.mxcsr = s.mxcsr ∧
        eval .ae u = some (decide (thr ≤ (stackArg s 1).toNat)) := by
    have hp := toPre2776_prepared16 hs
    refine entry_run hT s ⟨OpenTo.argR s, List.mem_append_left _ (by rw [hp.rd]; simp), ?_⟩
    have := hp.w₂
    show (⟨stackArgAddr s 0, 8 * 6⟩ : Region).Contains (stackArgAddr s 1) 8
    simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  refine Verified.entryBranch (p := fun s => decide (thr ≤ (stackArg s 1).toNat))
    (fun s => [.addr (stackArgAddr s 1)]) (openToSplitPrepared16_framed FS) (OpenTo.openToPrepared16_verified w F)
    (fun s hs => ?_) ?_ toSatP16_2776_pre
  · obtain ⟨u, e, g, hm, hrd, hwr, hmx, ev⟩ := run s hs
    have hS : Same s u := ⟨g, hm, hrd, hwr, hmx⟩
    exact ⟨u, e, ev, fun _ => ⟨pre2776_congr16 hS hs, fun s' a q => ⟨hS.abi a, post2776_congr16 hS q⟩⟩,
      fun _ => ⟨pre_narrow16 (pre2776_congr16 hS hs), fun s' a q => ⟨hS.abi a, post_widen16 hS q⟩⟩⟩
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, g, hm, hrd, hwr, hmx, -⟩ := run s hs
    obtain ⟨u₀', e₀', g', hm', hrd', hwr', hmx', -⟩ := run s' hs'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hS : Same s u₀ := ⟨g, hm, hrd, hwr, hmx⟩
    have hS' : Same s' u₀' := ⟨g', hm', hrd', hwr', hmx'⟩
    obtain ⟨-, -, -, -, -, -, qsp, qa, -⟩ := toPub2776_prepared16 hq
    refine ⟨by simp only [stackArgAddr, qsp], by simp only [Proof.AesGcm.arg] at qa; rw [qa 1 (by decide)],
      fun _ => pub2776_congr16 hS hS' hq, fun _ => pub_narrow16 hS hS' hq⟩

end VG.Proof.AesGcm.X86_64.OpenToSplit
