import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_seal_gather` calling any `vg_aes_gcm_stream_init`,
`vg_aes_gcm_stream_aad`, `vg_aes_gcm_stream_encrypt_to` and
`vg_aes_gcm_stream_finish` (`CallFn`), its code's static facts (no load of
`mxcsr`, `rsp` written only in frames, 4888 bytes of stack), the shared
contracts with a `scratch` buffer appended (`sealGatherScratchContract`),
and the shared contracts of `Spec/Gcm/OutOfPlace.lean` in a frame of 240
bytes holding the working space (`Verified.stackArgScratchL`): its 184
bytes, a copy of the five other stack arguments, and 16 more, for 5128
bytes of stack in all; for the key contexts of `vg_aes_gcm_init` and
`vg_aes_gcm_init_precomputed`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

/-! ## The callees -/

theorem framedS_mx {bytes : Nat} {r : Reg} {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Impl.StackScratch.X86_64.withStackScratch bytes r c).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq] at h ⊢
  simp only [Impl.StackScratch.X86_64.withStackScratch, instrs, List.all_append, List.all_cons, List.all_nil, h,
    Bool.and_true, Bool.true_and]
  rfl

theorem framedS_xdepth {bytes d : Nat} {r : Reg} {c : Prog isa} (h : c.x86_64Depth ≤ d) :
    (Impl.StackScratch.X86_64.withStackScratch bytes r c).x86_64Depth ≤ d + bytes := by
  simp only [Impl.StackScratch.X86_64.withStackScratch, Code.x86_64Depth, X86_64.Instr.frameBytes]
  omega

/-! ## The code -/

/-- The test of the length, whatever the threshold. -/
theorem shortTest_mx (t : Nat) : (Code.block (shortTest t) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true :=
  rfl
theorem shortTest_spAll (t : Nat) : (Code.block (shortTest t) : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true :=
  rfl
theorem shortTest_xdepth (t : Nat) : (Code.block (shortTest t) : Prog isa).x86_64Depth = 0 := rfl

section
variable {M : CtxMode} (S : SealFn M) (t : Nat) (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn)

theorem sealGather_mx : (sealGather S.fn t I.fn A.fn T.fn F.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := shortTest_mx t
  simp only [sealGather, Code.allInstrs] at h ⊢
  simp only [h, stream, copySeal, gatherCopy, copy, text, slices, Code.allInstrs, S.mx, I.mx, A.mx, T.mx, F.mx,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealGather_spAll : (sealGather S.fn t I.fn A.fn T.fn F.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := shortTest_spAll t
  simp only [sealGather, Code.all] at h ⊢
  simp only [h, stream, copySeal, gatherCopy, copy, text, slices, Code.all, S.spAll, I.spAll, A.spAll, T.spAll,
    F.spAll, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealGather_xdepth : (sealGather S.fn t I.fn A.fn T.fn F.fn).x86_64Depth ≤ 4888 := by
  have s₀ := S.xd
  have i := I.xd
  have a := A.xd
  have tt := T.xd
  have f := F.xd
  have h := shortTest_xdepth t
  simp only [sealGather, Code.x86_64Depth] at h ⊢
  simp only [h, stream, copySeal, gatherCopy, copy, text, slices, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, Nat.max_le]
  omega

theorem sealGather_correct {ht : t < 2 ^ 31} (s : State) (hs : (Proof.AesGcm.sealGatherX86_64M M).pre s) :
    ∃ tr s', Exec isa (sealGather S.fn t I.fn A.fn T.fn F.fn) s tr s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealGatherPostG s s' := by
  obtain ⟨tr, s', he, hg, hp⟩ := sealGather_wp (SG.ofM hs) S ht I A T F
  exact ⟨tr, s', he, abiPreserved_of_exec (sealGather_mx S t I A T F) he hg, hp⟩

end


/-! ## The contracts -/

theorem stackArgs_six (s : State) : List.map (stackArg s) (List.range 6) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

set_option linter.unusedSimpArgs false in
theorem gatherPre_of {s : State} (h : (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.base s := by
  sig_pre [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, dt, dw, dds, ⟨dl, da⟩, tw, tds, ⟨tl, ta⟩, wds, wl, wa⟩,
    rk, rn, ra, rdd, rt, rw, ⟨rds, ⟨rl, -⟩, bk, bn, ba, bd, bt, bw, bds, bl, -⟩, ok, on, oa, od, ot, ow, ⟨ods, ol⟩,
    hr, hg⟩ := h
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.base]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, wa, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, trivial⟩

set_option linter.unusedSimpArgs false in
theorem gatherPreP_of {s : State}
    (h : (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.powers s := by
  sig_pre [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, dt, dw, dds, ⟨dl, da⟩, tw, tds, ⟨tl, ta⟩, wds, wl, wa⟩,
    rk, rn, ra, rdd, rt, rw, ⟨rds, ⟨rl, -⟩, bk, bn, ba, bd, bt, bw, bds, bl, -⟩, ok, on, oa, od, ot, ow, ⟨ods, ol⟩,
    hr, hg, hpw⟩ := h
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.powers]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, wa, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, hpw⟩


theorem gatherPost_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPost,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi)⟩

theorem gatherPostP_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPost, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPubP_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi)⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather` with its
working space: no slices, no nonce, additional data or text; the tag at
`0x5000`, the working space at `0x6000`. -/
def gatherSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9029 then 0x50 else if a = 0x9031 then 0x60 else 0) else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 48⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 184⟩]

theorem gatherSat_pre : ∃ s, (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).pre s := by
  sig_implies_sat [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using gatherSat


/-- The key context at `0x1000` is below the stack arguments. -/
theorem ctx_low {i : Nat} (hi : i < 128 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), h]
  omega

/-- `gatherSat`, with a key context of 1024 bytes. -/
def gatherSatP : State :=
  { gatherSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 48⟩] }

theorem gatherSatP_pre : ∃ s, (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).pre s := by
  refine ⟨gatherSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    gatherSatP, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem gather_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.base).Implies
    (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPre_of h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem gatherP_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.powers).Implies
    (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPreP_of h, fun _ _ _ h => gatherPostP_of h, fun _ _ _ _ h => gatherPubP_of h, gatherSatP_pre⟩

theorem sealGather_core (S : SealFn CtxMode.base) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) :
    Verified X86_64.target (sealGather S.fn t I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.base) (sealGather_correct S t I A T F (ht := ht))
    (sealGather_ct S ht I A T F) gather_implies

theorem sealGatherP_core (S : SealFn CtxMode.powers) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.powers) (F : FinFn) :
    Verified X86_64.target (sealGather S.fn t I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.powers) (sealGather_correct S t I A T F (ht := ht))
    (sealGather_ct S ht I A T F) gatherP_implies

/-! ## In its frame -/

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`, without
the working space. -/
def gatherFrameSat : State :=
  { gatherSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩]
                   wr := [⟨0, 0⟩, ⟨0x5000, 16⟩] }

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

theorem gatherFrameSat_pre : ∃ s, (Spec.Gcm.sealGatherContract X86_64.abi 5128).pre s := by
  sig_implies_sat [Spec.Gcm.sealGatherContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq]
    [gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gatherFrameSat

theorem sealGather_framed (S : SealFn CtxMode.base) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather S.fn t I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherSig) (nm := "scratch") (e := .u64) (n := 23)
    (pre := Spec.Gcm.sealGatherPre X86_64.abi.ptrBits) (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits)
    (wa := true) (stack := 4888) (bytes := 240) (sealGather_core S ht I A T F) (by decide) (by decide) (by decide)
    (sealGather_spAll S t I A T F) (sealGather_xdepth S t I A T F) (Proof.AesGcm.sealGatherPre_local _)
    (Proof.AesGcm.sealGatherPost_local _) gatherFrameSat_pre

/-- `gatherFrameSat`, with a key context of 1024 bytes. -/
def gatherFrameSatP : State :=
  { gatherFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩] }

theorem gatherFrameSatP_pre : ∃ s, (Spec.Gcm.sealGatherPrecomputedContract X86_64.abi 5128).pre s := by
  refine ⟨gatherFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPrecomputedContract, Spec.Gcm.sealGatherPrecomputedSig,
    Spec.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq,
    gatherFrameSatP, gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem sealGatherP_framed (S : SealFn CtxMode.powers) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.powers) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather S.fn t I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherPrecomputedContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Spec.Gcm.sealGatherPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherP_core S ht I A T F) (by decide) (by decide) (by decide) (sealGather_spAll S t I A T F)
    (sealGather_xdepth S t I A T F) (Proof.AesGcm.sealGatherPrecomputedPre_local _)
    (Proof.AesGcm.sealGatherPrecomputedPost_local _) gatherFrameSatP_pre

end VG.Proof.AesGcm.X86_64.Gather
