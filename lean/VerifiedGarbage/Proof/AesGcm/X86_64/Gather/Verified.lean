module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Tls
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP

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

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
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

/-- A short path of `vg_aes_gcm_seal_gather`: a test that sets `CF` to `go`
of the arguments, which two runs with the same public data agree on, and the
code it runs then, with what correctness, constant time and the static facts
need of them. -/
structure ShortFn (M : CtxMode) where
  quick : Prog isa
  qgo : State → Bool
  hqgo : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → qgo s₀' = qgo s₀
  quickWp : ∀ {s : State}, SG M s → ∀ st, E2 s st → WP isa quick st fun st' =>
    E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (qgo s)
  quickRel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) quick fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (qgo s₀)) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (qgo s₀'))
  quickMx : quick.allInstrs (fun i => !loadsMxcsr i) = true
  quickSp : quick.all (fun i => !X86_64.isa.writesSp i) = true
  quickXd : quick.x86_64Depth ≤ 4888
  fast : Prog isa
  fastWp : ∀ {s : State}, SG M s → qgo s = true → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa fast st (Done s)
  fastRel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → qgo s₀ = true → ∀ {σ₁ σ₂ : State},
    E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) fast TT
  fastMx : fast.allInstrs (fun i => !loadsMxcsr i) = true
  fastSp : fast.all (fun i => !X86_64.isa.writesSp i) = true
  fastXd : fast.x86_64Depth ≤ 4888
  test : Prog isa
  code : Prog isa
  go : State → Bool
  hgo : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀' = go s₀
  testWp : ∀ {s : State}, SG M s → ∀ st, E2 s st →
    WP isa test st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (go s)
  testRel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) test fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (go s₀)) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (go s₀'))
  wp : ∀ {s : State}, SG M s → go s = true → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa code st (Done s)
  rel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀ = true → ∀ {σ₁ σ₂ : State},
    E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) code TT
  testMx : test.allInstrs (fun i => !loadsMxcsr i) = true
  codeMx : code.allInstrs (fun i => !loadsMxcsr i) = true
  testSp : test.all (fun i => !X86_64.isa.writesSp i) = true
  codeSp : code.all (fun i => !X86_64.isa.writesSp i) = true
  testXd : test.x86_64Depth ≤ 4888
  codeXd : code.x86_64Depth ≤ 4888

/-- The test of the texts the short path takes, whatever the threshold. -/
theorem splitTest_mx (t : Nat) : (splitTest t : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := rfl
theorem splitTest_spAll (t : Nat) : (splitTest t : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := rfl
theorem splitTest_xdepth (t : Nat) : (splitTest t : Prog isa).x86_64Depth = 0 := rfl

/-- The short path, for a text shorter than `t` bytes or whose first slice
holds all its whole blocks: sealed from its first slice by `Sp`
(`vg_aes_gcm_seal_split`) if that slice holds all the whole blocks and at
least `ts` bytes, and otherwise copied whole to the output and sealed there
by `Se` (`vg_aes_gcm_seal`). -/
def ShortFn.ofBoth {M : CtxMode} (Se : SealFn M) (Sp : SplitFn M) {t ts : Nat} (ht : t < 2 ^ 31) (hts : 1 ≤ ts)
    (htt : ts + 16 ≤ t) : ShortFn M where
  quick := .block (quickTest ts)
  qgo s := decide (L s < ts)
  hqgo := fun _ _ pb => by simp only [pb.eL]
  quickWp := fun hp _ h => w_quick hp (by omega) h
  quickRel := fun hp hp' pb => quick_rel hp hp' pb (by omega)
  quickMx := rfl
  quickSp := rfl
  quickXd := Nat.zero_le _
  fast := copySeal Se.fn
  fastWp := fun hp e st E r11 => sealShort_wp hp Se ht (by simp only [decide_eq_true_eq] at e ⊢; omega) st E r11
  fastRel := fun hp hp' pb e _ _ E₁ r₁ E₂ r₂ => sealShort_rel Se hp hp' pb
    (by simp only [decide_eq_true_eq] at e ⊢; omega) ht E₁ r₁ E₂ r₂
  fastMx := by
    simp only [copySeal, gatherCopy, copy, Code.allInstrs, Se.mx, Bool.true_and, Bool.and_true]
    rfl
  fastSp := by
    simp only [copySeal, gatherCopy, copy, Code.all, Se.spAll, Bool.true_and, Bool.and_true]
    rfl
  fastXd := by
    have s₀ := Se.xd
    simp only [copySeal, gatherCopy, copy, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons,
      List.length_nil, Nat.max_le]
    omega
  test := splitTest t
  code := copyShort ts Se.fn Sp.fn
  go s := decide (shortLen s < t)
  hgo := fun _ _ pb => by simp only [shortLen, pb.eL, pb.eFl]
  testWp := fun hp _ h => splitTest_wp hp ht h
  testRel := fun hp hp' pb => splitTest_rel hp hp' pb ht
  wp := fun {s} hp e st E r11 => by
    have hs : shortLen s < t := by simpa using e
    unfold copyShort
    refine WP.seq (WP.mono (selTest_wp hp (ts := ts) (by omega) E) fun st' ⟨E', r11', cf'⟩ => ?_)
    refine WP.ite (decide (selLen s < ts)) (by simp only [eval, cf']) (fun h => ?_) (fun h => ?_)
    · exact sealShort_wp hp Se ht (by simpa using lt_of_sel hp htt hs (by simpa using h)) st' E' r11'
    · exact copySplit_wp hp Sp (sub_lt_of_sel hp hts (by simpa using h)) E'.1 r11' E'.2.2.1 E'.2.2.2.1
  rel := fun {s₀ s₀'} hp hp' pb e σ₁ σ₂ E₁ r₁ E₂ r₂ => by
    have hs : shortLen s₀ < t := by simpa using e
    have esel : selLen s₀' = selLen s₀ := by simp only [selLen, pb.eL, pb.eFl]
    unfold copyShort
    refine RelCT.seq (R := fun (a b : State) => (E2 s₀ a ∧ a.gpr .r11 = W s₀ ∧ a.cf = some (decide (selLen s₀ < ts))) ∧
        (E2 s₀' b ∧ b.gpr .r11 = W s₀' ∧ b.cf = some (decide (selLen s₀' < ts))))
      ((selTest_rel hp hp' pb (ts := ts) (by omega)).mono (fun a b h => by rw [h.1, h.2]; exact ⟨E₁, E₂⟩)
        fun _ _ h => h)
      (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.2, g.2.2.2, esel]) ?_ ?_)
    · refine StreamTo.RelCT.of_imp (selLen s₀ < ts) (fun _ _ g => by
        have c := g.2; simp only [eval, g.1.1.2.2] at c; simpa using c) fun h => ?_
      exact rel_of_eq2 fun _ _ g => sealShort_rel Se hp hp' pb (by simpa using lt_of_sel hp htt hs h) ht g.1.1.1
        g.1.1.2.1 g.1.2.1 g.1.2.2.1
    · refine StreamTo.RelCT.of_imp (¬selLen s₀ < ts) (fun _ _ g => by
        have c := g.2; simp only [eval, g.1.1.2.2] at c; simpa using c) fun h => ?_
      exact rel_of_eq2 fun _ _ g => splitShort_rel Sp hp hp' pb e ht g.1.1.1 g.1.1.2.1 g.1.2.1 g.1.2.2.1
  testMx := splitTest_mx t
  codeMx := by
    simp only [copyShort, selTest, lenTest, selLast, copySeal, copySplit, gatherCopy, copy, Code.allInstrs, Se.mx,
      Sp.mx, Bool.true_and, Bool.and_true]
    rfl
  testSp := splitTest_spAll t
  codeSp := by
    simp only [copyShort, selTest, lenTest, selLast, copySeal, copySplit, gatherCopy, copy, Code.all, Se.spAll,
      Sp.spAll, Bool.true_and, Bool.and_true]
    rfl
  testXd := by rw [splitTest_xdepth]; decide
  codeXd := by
    have s₀ := Se.xd
    have s₁ := Sp.xd
    simp only [copyShort, selTest, lenTest, selLast, copySeal, copySplit, gatherCopy, copy, Code.x86_64Depth,
      X86_64.Instr.frameBytes, List.length_cons, List.length_nil, Nat.max_le]
    omega

/-- `ShortFn.ofBoth`, but a TLS record's text (`tlsTest long fill`) sealed
from its first slice by `Sp` first, at any length. -/
def ShortFn.ofTls {M : CtxMode} (Se : SealFn M) (Sp : SplitFn M) (long fill : Bool) {t ts : Nat} (ht : t < 2 ^ 31)
    (hts : 1 ≤ ts) (htt : ts + 16 ≤ t) : ShortFn M :=
  { ShortFn.ofBoth Se Sp ht hts htt with
    quick := tlsTest long fill
    qgo := tlsGo long fill
    hqgo := fun _ _ pb => pb.eTls long fill
    quickWp := fun hp _ h => tlsTest_wp hp long fill h
    quickRel := fun hp hp' pb => tlsTest_rel hp hp' pb long fill
    quickMx := tlsTest_mx long fill
    quickSp := tlsTest_spAll long fill
    quickXd := by rw [tlsTest_xdepth]; exact Nat.zero_le _
    fast := copySplit Sp.fn
    fastWp := fun hp e _ E r11 => copySplit_wp hp Sp (tls_sub hp e) E.1 r11 E.2.2.1 E.2.2.2.1
    fastRel := fun hp hp' pb e _ _ E₁ r₁ E₂ r₂ => copySplit_rel hp hp' pb Sp (tls_sub hp e) E₁.1 r₁ E₁.2.2.1
      E₁.2.2.2.1 E₂.1 r₂ E₂.2.2.1 E₂.2.2.2.1
    fastMx := by
      simp only [copySplit, gatherCopy, copy, Code.allInstrs, Sp.mx, Bool.true_and, Bool.and_true]
      rfl
    fastSp := by
      simp only [copySplit, gatherCopy, copy, Code.all, Sp.spAll, Bool.true_and, Bool.and_true]
      rfl
    fastXd := by
      have s₁ := Sp.xd
      simp only [copySplit, gatherCopy, copy, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons,
        List.length_nil, Nat.max_le]
      omega }

section
variable {M : CtxMode} (Sh : ShortFn M) (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn)

theorem sealGather_mx : (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sealGather, gatherRest, Code.allInstrs, Sh.quickMx, Sh.fastMx, Sh.testMx, Sh.codeMx, stream, text, slices, I.mx, A.mx, T.mx, F.mx,
    Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealGather_spAll :
    (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sealGather, gatherRest, Code.all, Sh.quickSp, Sh.fastSp, Sh.testSp, Sh.codeSp, stream, text, slices, I.spAll, A.spAll, T.spAll,
    F.spAll, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealGather_xdepth : (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn).x86_64Depth ≤ 4888 := by
  have s₃ := Sh.quickXd
  have s₂ := Sh.fastXd
  have s₀ := Sh.testXd
  have s₁ := Sh.codeXd
  have i := I.xd
  have a := A.xd
  have tt := T.xd
  have f := F.xd
  simp only [sealGather, gatherRest, stream, text, slices, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, Nat.max_le]
  omega

theorem sealGather_correct (s : State) (hs : (Proof.AesGcm.sealGatherX86_64M M).pre s) :
    ∃ tr s', Exec isa (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn) s tr s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealGatherPostG s s' := by
  have hp := SG.ofM hs
  obtain ⟨tr, s', he, hg, hpo⟩ := sealGatherG_wp hp (qgo := Sh.qgo s) (go := Sh.go s) (fun _ h => Sh.quickWp hp _ h)
    (fun e st E r11 => Sh.fastWp hp e st E r11) (fun st h => Sh.testWp hp st h)
    (fun e st E r11 => Sh.wp hp e st E r11) I A T F
  exact ⟨tr, s', he, abiPreserved_of_exec (sealGather_mx Sh I A T F) he hg, hpo⟩

theorem sealGather_ct :
    ConstantTime isa (Proof.AesGcm.sealGatherX86_64M M).pre Proof.AesGcm.sealGatherPub
      (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn) :=
  sealGatherG_ct Sh.qgo Sh.go Sh.hqgo Sh.hgo Sh.quickRel Sh.fastRel Sh.testRel Sh.rel I A T F

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

theorem sealGather_core (Sh : ShortFn CtxMode.base) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) :
    Verified X86_64.target (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.base) (sealGather_correct Sh I A T F)
    (sealGather_ct Sh I A T F) gather_implies

theorem sealGatherP_core (Sh : ShortFn CtxMode.powers) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.powers) (F : FinFn) :
    Verified X86_64.target (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.powers) (sealGather_correct Sh I A T F)
    (sealGather_ct Sh I A T F) gatherP_implies

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

theorem sealGather_framed (Sh : ShortFn CtxMode.base) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherSig) (nm := "scratch") (e := .u64) (n := 23)
    (pre := Spec.Gcm.sealGatherPre X86_64.abi.ptrBits) (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits)
    (wa := true) (stack := 4888) (bytes := 240) (sealGather_core Sh I A T F) (by decide) (by decide) (by decide)
    (sealGather_spAll Sh I A T F) (sealGather_xdepth Sh I A T F) (Proof.AesGcm.sealGatherPre_local _)
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

theorem sealGatherP_framed (Sh : ShortFn CtxMode.powers) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.powers) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherPrecomputedContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Spec.Gcm.sealGatherPrecomputedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherP_core Sh I A T F) (by decide) (by decide) (by decide) (sealGather_spAll Sh I A T F)
    (sealGather_xdepth Sh I A T F) (Proof.AesGcm.sealGatherPrecomputedPre_local _)
    (Proof.AesGcm.sealGatherPrecomputedPost_local _) gatherFrameSatP_pre

end VG.Proof.AesGcm.X86_64.Gather
