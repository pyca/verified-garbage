module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.RootCT
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.CodecFrame
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Pre

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

 theorem root_agree {c : Cfg} {s t : State} (hp : RootPublic c s t) :
    VG.X86.Taint.Agree (rootT c) s t := by
  rcases hp with ⟨hs, ht, hw, hb, he⟩
  refine ⟨⟨?_, (fun h => nomatch h)⟩, (fun _ => hw), hs, ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty,
    (fun _ => he), (fun _ _ h => False.elim (Nat.not_lt_zero _ h))⟩
  intro r hr
  simp only [rootT, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact he
  · exact hb

 def powerT (c : Cfg) : VG.X86.Taint.T :=
  { rootT c with regs := .ofList [.esp, .edi, .esi] }

 theorem power_agree {c : Cfg} {s t : State} (hp : PowerPublic c s t) :
    VG.X86.Taint.Agree (powerT c) s t := by
  have R := root_agree hp.1
  refine ⟨⟨?_, R.rf.2⟩, R.wr,
    ⟨R.wf₁.lens, R.wf₁.bases, R.wf₁.wbases, R.wf₁.args, R.wf₁.argBases, R.wf₁.stk, R.wf₁.frames, R.wf₁.room⟩,
    ⟨R.wf₂.lens, R.wf₂.bases, R.wf₂.wbases, R.wf₂.args, R.wf₂.argBases, R.wf₂.stk, R.wf₂.frames, R.wf₂.room⟩, R.ok, R.slots, R.sp, R.argMem⟩
  intro r hr
  simp only [powerT, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.1.2.2.2.2
  · exact hp.1.2.2.2.1
  · exact hp.2

 theorem root_wf {c : Cfg} {s t : State}
    (hp : codecPre (c.C.len + 1) (2 * c.C.len + 1) false s)
    (hs : Scr t (ptr s 2) size) (he : t.gpr .esp = s.gpr .esp) (hw : t.wr = s.wr) :
    VG.X86.Taint.Wf (rootT c) t where
  lens h := by rw [hw]; exact (codec_wf hp).lens h
  bases p h := by
    simp only [rootT, List.mem_singleton] at h
    subst p
    simpa only [addr, BitVec.add_zero, VG.X86.Taint.region,
      hw, hp.2.1, ptr, Bool.false_eq_true, ite_false, List.getD_cons_succ, List.getD_cons_zero] using hs.edi
  wbases _ h := nomatch h
  args h := by cases h
  argBases _ h := nomatch h
  stk := by simpa only [rootT, codecT, VG.X86.Taint.depth, Nat.add_zero, he] using (codec_wf hp).stk
  frames _ h := nomatch h
  room h := by
    simpa only [rootT, codecT, VG.X86.Taint.depth, VG.X86.Taint.nframes,
      Nat.add_zero, List.drop_zero, VG.X86.Taint.argByte, BitVec.add_zero, he, hw] using (codec_wf hp).room h

 def finishT (c : Cfg) : VG.X86.Taint.T :=
  { codecT (2 * c.C.len + 1) with regs := .ofList [.esp, .edi], bases := [(.edi, 1, 0)] }

 theorem finish_agree {c : Cfg} {s t : State}
    (hs : codecPre (c.C.len + 1) (2 * c.C.len + 1) false s)
    (ht : codecPre (c.C.len + 1) (2 * c.C.len + 1) false t)
    (hp : RootPublic c s t)
    (ha : s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2) :
    VG.X86.Taint.Agree (finishT c) s t := by
  have A := codec_agree hs ht ha
  have R := root_agree hp
  exact ⟨R.rf, A.wr,
    ⟨A.wf₁.lens, R.wf₁.bases, A.wf₁.wbases, A.wf₁.args, A.wf₁.argBases,
      A.wf₁.stk, A.wf₁.frames, A.wf₁.room⟩,
    ⟨A.wf₂.lens, R.wf₂.bases, A.wf₂.wbases, A.wf₂.args, A.wf₂.argBases,
      A.wf₂.stk, A.wf₂.frames, A.wf₂.room⟩,
    A.ok, A.slots, A.sp, A.argMem⟩

 def conversionFront (c : Cfg) : Prog isa :=
  .seq (.seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.block (Impl.EcKey.Compressed.X86.decompressPeer c)))
    (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c))

 theorem conversionFront_ok {c : Cfg} (hc : CfgOk c) {s : State}
    (hp : InputPre c (1 + c.C.len) s) :
    WP isa (conversionFront c) s (DecompressFront c s) := by
  have h := decompressFront_ok hc hp (rest := .block []) (fun _ F => WP.block_nil F)
  simpa only [conversionFront, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using h

theorem rel_assoc_left {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s t ts tt u v hp es et
  cases es with
  | seq ab c₁ =>
    cases ab with
    | seq a₁ b₁ =>
      cases et with
      | seq ab c₂ =>
        cases ab with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

 theorem decompress_tonelli_ct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C}
    (hroot : CandidateCorrect c root)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.decompress c) 28)
    (hfront : ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub (conversionFront c))
    (hprepare : ConstantTime isa (fun _ => True) (RootPublic c) (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c))
    (hmiddle : ConstantTime isa (fun _ => True) (RootPublic c)
      (.seq (Impl.EcKey.Compressed.X86.selectRoot c) (Impl.EcKey.Compressed.X86.checkRoot c)))
    (hfinish : ConstantTime isa (decompressContract c.C root).pre
      (fun s t => RootPublic c s t ∧ (decompressContract c.C root).pub s t)
      (.block (Impl.EcKey.Compressed.X86.decompressFinish c))) :
    ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub
      (Impl.EcKey.Compressed.X86.decompress c) := by
  let P := fun s t => (decompressContract c.C root).pre s ∧
    (decompressContract c.C root).pre t ∧ (decompressContract c.C root).pub s t
  have Hfront : RelCT isa P (conversionFront c) (RootPair c) := by
    have H : RelCT isa P (conversionFront c) (fun _ _ => True) :=
      fun _ _ _ _ _ _ ⟨hs, ht, hp⟩ es et => ⟨hfront _ _ _ _ _ _ hs ht hp es et, trivial⟩
    apply (H.wpDep (F := fun s t => DecompressFront c s t) (by
      rintro s t ⟨hs, ht, _⟩
      exact ⟨conversionFront_ok hc (by simpa only [Nat.add_comm] using codec_input (c := c) hs),
        conversionFront_ok hc (by simpa only [Nat.add_comm] using codec_input (c := c) ht)⟩)).mono
    · exact fun _ _ h => h
    · rintro u v ⟨_, s, t, ⟨hs, ht, hp⟩, F, G⟩
      have hb : ptr s 2 = ptr t 2 := congrArg (BitVec.setWidth 64) hp.2.2.2
      have J : RootInput c (ptr s 2) v := by
        rw [hb]; exact ⟨G.scr, modP_of hc G.fixed.mp, G.rhs_lt, G.fixed.onep⟩
      refine ⟨ptr s 2, ⟨F.scr, modP_of hc F.fixed.mp, F.rhs_lt, F.fixed.onep⟩, J,
        root_wf hs F.scr F.esp F.wr, root_wf ht G.scr G.esp G.wr, ?_, ?_, ?_⟩
      · simp only [F.wr, G.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2, Bool.false_eq_true, ite_false]
      · apply BitVec.eq_of_toNat_eq
        rw [F.scr.edi_toNat, J.scr.edi_toNat]
      · rw [F.esp, G.esp, hp.1]
  have Hbody : RelCT isa P (decompressBody c) (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc (RelCT.seq Hfront
      (RelCT.seq (rootCandidate_rel hc hp hprepare hprefix hsquare hrest) (rel_of_ct hmiddle))))
  have hbody : SpOk (decompressBody c) 28 :=
    hsp.left.seq (hsp.right.left.seq (hsp.right.right.left.seq hsp.right.right.right.left))
  have Hbody' := Hbody.wpDep (F := fun (s t : State) => DecompressChecked c root s t ∧
      Frame (s.wr ++ [below (s.gpr .esp) 28]) s.mem t.mem) (by
    rintro s t ⟨hs, ht, _⟩
    exact ⟨WP.spFrame hbody hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (decompressBody_ok hc hroot
        (by simpa only [Nat.add_comm] using codec_input (c := c) hs)),
      WP.spFrame hbody ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (decompressBody_ok hc hroot
        (by simpa only [Nat.add_comm] using codec_input (c := c) ht))⟩)
  apply RelCT.constantTime
  change RelCT isa P ([.block (c.setupWith Impl.EcKey.Compressed.X86.args),
    .block (Impl.EcKey.Compressed.X86.decompressPeer c),
    Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)].foldr .seq
    (.seq (Impl.EcKey.Compressed.X86.recoverCoordinate c)
      (.block (Impl.EcKey.Compressed.X86.decompressFinish c)))) (fun _ _ => True)
  -- Regroup the same prefix used by the correctness proof.
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.seq (rel_assoc_left (rel_assoc_left Hbody'))
  intro u v tu tv u' v' ⟨_, s, t, ⟨hs, ht, hp⟩, ⟨F, W⟩, ⟨G, V⟩⟩ eu ev
  have hu := codec_pre_frame hs F.esp F.rd F.wr W
  have hv := codec_pre_frame ht G.esp G.rd G.wr V
  have as_ := codec_args_frame hs F.esp W
  have at_ := codec_args_frame ht G.esp V
  have ha : (decompressContract c.C root).pub u v := by
    refine ⟨by rw [F.esp, G.esp, hp.1], ?_, ?_, ?_⟩
    · rw [as_ 0 (by decide), at_ 0 (by decide), hp.2.1]
    · rw [as_ 1 (by decide), at_ 1 (by decide), hp.2.2.1]
    · rw [as_ 2 (by decide), at_ 2 (by decide), hp.2.2.2]
  have hb : ptr s 2 = ptr t 2 := congrArg (BitVec.setWidth 64) hp.2.2.2
  have RP : RootPublic c u v := by
    refine ⟨root_wf hs F.scr F.esp F.wr, root_wf ht G.scr G.esp G.wr, ?_, ?_, ha.1⟩
    · simp only [F.wr, G.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2, Bool.false_eq_true, ite_false]
    · apply BitVec.eq_of_toNat_eq
      rw [F.scr.edi_toNat, G.scr.edi_toNat, hb]
  exact ⟨hfinish _ _ _ _ _ _ hu hv ⟨RP, ha⟩ eu ev, trivial⟩

end VG.Proof.EcKey.Compressed.X86
