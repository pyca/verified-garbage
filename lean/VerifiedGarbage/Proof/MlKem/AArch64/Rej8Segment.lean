module

public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
public import VerifiedGarbage.Impl.MlKem.AArch64.Lay
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
meta import VerifiedGarbage.Impl.MlKem.AArch64.Lay

/-! ### `MlKem.AArch64.Rej8Body`, which only this module used -/

section

/-! ### `MlKem.AArch64.Rej8Tail`, which this module and modules that import it used -/

section

/-! # Four scalar chunks at the end of the compacted polynomial -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def scalarFour (w16 : Bool := false) : Prog isa :=
  seqs [sampleBody w16,sampleBody w16,sampleBody w16,sampleBody w16]

theorem scalarFour_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte}
    {bP aP : Addr} {s₀ s : State} (hp : Scalar.LPreW w16 N B bP aP s₀)
    (h : Scalar.InvW w16 initial N B bP aP s₀ t s) (ht : t+4≤N) :
    WP isa (scalarFour w16) s fun u => Scalar.InvW w16 initial N B bP aP s₀ (t+4) u ∧ u.v=s.v := by
  have hw : WP isa (scalarFour w16) s (Scalar.InvW w16 initial N B bP aP s₀ (t+4)) := by
    refine WP.seq (WP.mono (Scalar.body_ok hp (by omega_using [ht]) h) fun a ⟨ha,_⟩ => ?_)
    refine WP.seq (WP.mono (Scalar.body_ok hp (by omega_using [ht]) ha) fun b ⟨hb,_⟩ => ?_)
    refine WP.seq (WP.mono (Scalar.body_ok hp (by omega_using [ht]) hb) fun c ⟨hc,_⟩ => ?_)
    exact WP.mono (Scalar.body_ok hp (by omega_using [ht]) hc) fun _ ⟨hd,_⟩ => hd
  obtain ⟨tr,u,he,hu⟩ := hw
  refine ⟨tr,u,he,hu,?_⟩
  funext r
  apply Exec.vec (c := scalarFour w16) (s := s) (s' := u) ?_ he
  intro i hi
  have hn : (instrs (scalarFour w16)).all (fun i => decide (vdstOf i=none))=true := by
    cases w16 <;> decide +kernel
  have hi' := of_decide_eq_true (List.all_eq_true.mp hn i hi)
  rw [hi']
  exact nofun

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # One mixed vector/scalar rejection iteration, including early success -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Choice.lean`, which only this module imported.
section

/-! # The public rejection-count branch selects a proved vector or scalar step -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def choosePrefix : List Instr := [.subImm .x .x6 .x4 8,.lsr .x .x6 .x6 63]

theorem choosePrefix_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (h : Scalar.InvW w16 initial N B bP aP s₀ t s) (hc : Constants s) :
    WP isa (.block choosePrefix) s fun u =>
      Scalar.InvW w16 initial N B bP aP s₀ t u ∧ Constants u ∧
        ((u.gpr .x6 == 0)=true ↔ 8≤(u.gpr .x4).toNat) := by
  have hw : WP isa (.block choosePrefix) s fun u =>
      Scalar.InvW w16 initial N B bP aP s₀ t u ∧
        ((u.gpr .x6 == 0)=true ↔ 8≤(u.gpr .x4).toNat) := by
    refine wp_subImm (by decide) fun a ha ea => wp_lsr (by decide) fun u hu eu => wp_nil ?_
    have hk := (ha.keep.trans hu.keep).mono (rs' := [.x6]) (by decide)
    have hm : u.mem=s.mem := hu.mem.trans ha.mem
    refine ⟨⟨Scalar.acc_keep h.acc hk hm,(h.keep.trans hk).mono (by decide),
      by rw [hk.get .x2,h.x2],by rw [hk.get .x5,h.x5],by rw [hk.get .x10,h.x10]⟩,?_⟩
    rw [eu,ea,hu.gpr .x4 (by decide),ha.gpr .x4 (by decide),beq_iff_eq]
    have hb : (s.gpr .x4).toNat≤256 := by rw [h.acc.x4]; omega_using []
    bv_omega
  refine WP.mono (WP.keepV (by decide) hw) fun u ⟨⟨hi,he⟩,hv⟩ => ⟨hi,?_,he⟩
  exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
    by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
    by simpa only [hv] using hc.zero⟩

end VG.Proof.MlKem.AArch64.Rej8
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def body (w16 : Bool := false) : Prog isa := .seq (.block choosePrefix)
  (.ite (.zero .x .x6) (.block (Impl.MlKem.AArch64.Rej8.rejEight w16))
    (.seq (scalarFour w16) (.ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block []))))

structure ResultW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (aP : Addr) (s₀ u : State) :
    Prop where
  acc : Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u
  keep : Keep Scalar.lRegs s₀ u
  constants : Constants u

private theorem constants_of_vec {s u : State} (h : Constants s) (hv : u.v=s.v) : Constants u :=
  ⟨by rw [hv]; exact h.index,by rw [hv]; exact h.mask,
   by simpa only [hv] using h.q,by simpa only [hv] using h.weights,by simpa only [hv] using h.zero⟩

theorem body_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : EnvW w16 N B bP aP s₀) (h : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hc : Constants s) (ht : t+4≤N) :
    WP isa (body w16) s fun u =>
      (Scalar.InvW w16 initial N B bP aP s₀ (t+4) u ∧ Constants u) ∨
        (ResultW w16 initial N B aP s₀ u ∧ u.gpr .x5=0) := by
  refine WP.seq (WP.mono (choosePrefix_ok h hc) fun a ⟨ha,hac,he⟩ => ?_)
  refine WP.ite (a.gpr .x6 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
  · exact WP.mono (vector_ok hp ha hac ht (he.mp hz)) fun _ hv => Or.inl hv
  · refine WP.seq (WP.mono (scalarFour_ok hp.toLPreW ha ht) fun b ⟨hb,hv⟩ => ?_)
    have hbc := constants_of_vec hac hv
    refine WP.ite (b.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
    · have hfull : (Scalar.LA initial B (t+4)).length=n := by
        rw [eq_zero_iff,decide_eq_true_eq,hb.acc.x4] at hz
        have := hb.acc.len
        change _=256
        omega_using [hz, this]
      have heq := sampleAfter_full hfull N ht
      have hw : WP isa (.block [.movz .x .x5 0 0]) b fun u =>
          Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u ∧
          Keep Scalar.lRegs s₀ u ∧ u.gpr .x5=0 := by
        refine wp_movz fun u hu eu => wp_nil ?_
        refine ⟨?_,(hb.keep.trans hu.keep).mono (by decide),eu⟩
        rw [show Scalar.LA initial B N=Scalar.LA initial B (t+4) from heq]
        exact Scalar.acc_keep hb.acc hu.keep hu.mem
      exact WP.mono (WP.keepV (by decide) hw) fun _ ⟨⟨ac,ke,x5⟩,ve⟩ =>
        Or.inr ⟨⟨ac,ke,constants_of_vec hbc ve⟩,x5⟩
    · exact wp_nil (Or.inl ⟨hb,hbc⟩)

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! ### `MlKem.AArch64.Rej8CT`, which only this module used -/

section

/-! ### `MlKem.AArch64.Rej8LoopCT`, which only this module used -/

section

/-! ### `MlKem.AArch64.Rej8BodyCT`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Rej8StepCT`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Rej8BatchCT`, which only this module used -/

section

/-! # Vector rejection leaks only its public matrix candidates and cursors -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

theorem probe_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block probeCode) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem storeAdvance_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x7])) (.block (storeCode w16++advanceCode w16)) := by
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x7])
    (fun _ _ _ _ h => h) (by taint_decide)

structure BatchPublic (s t : State) : Prop where
  cs : Constants s
  ct : Constants t
  candidates : candidatesAt s=candidatesAt t
  rs : InRegions (s.rd++s.wr) (s.gpr .x2) 16
  rt : InRegions (t.rd++t.wr) (t.gpr .x2) 16
  sp : s.sp=t.sp
  x2 : s.gpr .x2=t.gpr .x2
  x3 : s.gpr .x3=t.gpr .x3
  table : s.gpr .x16=t.gpr .x16

theorem batch_relCT (w16 : Bool) : RelCT isa BatchPublic (.block (Impl.MlKem.AArch64.Rej8.rejEight w16))
    (fun _ _ => True) := by
  have he : (.block (Impl.MlKem.AArch64.Rej8.rejEight w16) : Prog isa)=
      .block (probeCode++(storeCode w16++advanceCode w16)) := by
    cases w16 <;> rfl
  rw [he]
  apply RelCT.block_append
  intro s t tr ur s' t' hp es et
  cases es with
  | @seq _ _ _ a _ tr₁ tr₂ ep er =>
    cases et with
    | @seq _ _ _ b _ ur₁ ur₂ fp fr =>
      have htr := probe_ct s t tr₁ ur₁ a b trivial trivial
        ⟨hp.sp,fun r hr => by
          have hr' : r=.x2 := by simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] using hr
          subst r; exact hp.x2⟩ ep fp
      obtain ⟨_,a',epa,ha⟩ := probe_ok s hp.cs hp.rs
      obtain ⟨_,b',fpb,hb⟩ := probe_ok t hp.ct hp.rt
      obtain ⟨_,rfl⟩ := Exec.det ep epa
      obtain ⟨_,rfl⟩ := Exec.det fp fpb
      have hm : maskAt s=maskAt t := congrArg acceptanceMask hp.candidates
      have hrest := storeAdvance_ct w16 a b tr₂ ur₂ s' t' trivial trivial
        ⟨ha.keep.sp.trans (hp.sp.trans hb.keep.sp.symm),fun r hr => by
          have hr' : r=.x3 ∨ r=.x7 := by
            simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] using hr
          rcases hr' with rfl|rfl
          · rw [ha.keep.get .x3,hb.keep.get .x3,hp.x3]
          · rw [ha.index,hb.index,hp.table,hm]⟩ er fr
      exact ⟨by rw [htr,hrest],trivial⟩

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! ### `MlKem.AArch64.Rej8ScalarCT`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Rej8Public`, which this module and modules that import it used -/

section

/-! # Public stream prefixes determine the rejection loop's cursors -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem candidates_eq {s u : State} (h2 : s.gpr .x2=u.gpr .x2)
    (h : ∀i<12,s.mem (s.gpr .x2+BitVec.ofNat 64 i)=u.mem (u.gpr .x2+BitVec.ofNat 64 i)) :
    candidatesAt s=candidatesAt u := by
  apply Ntt16.vhalf_ext
  intro e he
  rw [candidatesAt,candidatesAt,parsed_candidate _ _ he,parsed_candidate _ _ he,candidate,candidate]
  have hr : s.mem.read (s.gpr .x2+BitVec.ofNat 64 (3*(e/2))) 3 =
      u.mem.read (u.gpr .x2+BitVec.ofNat 64 (3*(e/2))) 3 := by
    rw [←h2]
    apply Mem.read_congr
    intro i hi
    simp only [ptr_add]
    have hh := h (3*(e/2)+i) (by omega_using [he, hi])
    rwa [←h2] at hh
  rw [hr]

theorem inv_public {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ s u : State} (hs : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hu : Scalar.InvW w16 initial N B bP aP u₀ t u) (hsp : s₀.sp=u₀.sp) :
    s.sp=u.sp ∧ ∀r∈[Reg.x2,.x3,.x4,.x5,.x9,.x10],s.gpr r=u.gpr r := by
  refine ⟨hs.acc.sp.trans (hsp.trans hu.acc.sp.symm),?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · rw [hs.x2,hu.x2]
  · rw [hs.acc.x3,hu.acc.x3]
  · exact BitVec.eq_of_toNat_eq (hs.acc.x4.trans hu.acc.x4.symm)
  · exact BitVec.eq_of_toNat_eq (hs.x5.trans hu.x5.symm)
  · exact BitVec.eq_of_toNat_eq (hs.acc.x9.trans hu.acc.x9.symm)
  · exact BitVec.eq_of_toNat_eq (hs.x10.trans hu.x10.symm)

theorem inv_candidates {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ s u : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hs : Scalar.InvW w16 initial N B bP aP s₀ t s) (hu : Scalar.InvW w16 initial N B bP aP u₀ t u)
    (ht : t+4≤N) : candidatesAt s=candidatesAt u := by
  apply candidates_eq (by rw [hs.x2,hu.x2])
  intro i hi
  rw [hs.x2,hu.x2,ptr_add]
  rw [byte_frame hs.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact ps.disj)
      (by have := ps.bound; omega_using [this]) (by omega_using [ht, hi]),ps.buf _ (by omega_using [ht, hi])]
  rw [byte_frame hu.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact pu.disj)
      (by have := pu.bound; omega_using [this]) (by omega_using [ht, hi]),pu.buf _ (by omega_using [ht, hi])]

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Scalar tails branch only on candidates derived from the public seed -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def scalarTail (w16 : Bool := false) : Prog isa := .ite (.zero .x .x4) (.block [])
  (.seq (.block (sampleAccept .x11 w16)) (.ite (.zero .x .x4) (.block []) (.block (sampleAccept .x12 w16))))

theorem chunk_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block sampleChunk) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2]) (fun _ _ _ _ h => h) (by taint_decide)

theorem scalarTail_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4,.x9,.x11,.x12])) (scalarTail w16) := by
  unfold scalarTail
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4,.x9,.x11,.x12])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem scalarBody_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (ht : t<N) :
    RelCT isa (fun s u => Scalar.InvW w16 initial N B bP aP s₀ t s ∧ Scalar.InvW w16 initial N B bP aP u₀ t u)
      (sampleBody w16) (fun s u => Scalar.InvW w16 initial N B bP aP s₀ (t+1) s ∧
        Scalar.InvW w16 initial N B bP aP u₀ (t+1) u) := by
  intro s u tr ur s' u' hp es eu
  have hpub := inv_public hp.1 hp.2 hsp
  have trace : tr=ur := by
    cases es with
    | @seq _ _ _ a _ tr₁ tr₂ ep er =>
      cases eu with
      | @seq _ _ _ b _ ur₁ ur₂ fp fr =>
        have htr := chunk_ct s u tr₁ ur₁ a b trivial trivial
          ⟨hpub.1,fun r hr => by
            have hr' : r=.x2 := by simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] using hr
            subst r; exact hpub.2 .x2 (by simp)⟩ ep fp
        obtain ⟨_,a',epa,ha,ka,_,_,va,wa⟩ := Scalar.chunk_ok ps.toLPreW ht hp.1
        obtain ⟨_,b',fpb,hb,kb,_,_,vb,wb⟩ := Scalar.chunk_ok pu.toLPreW ht hp.2
        obtain ⟨_,rfl⟩ := Exec.det ep epa
        obtain ⟨_,rfl⟩ := Exec.det fp fpb
        have hrest := scalarTail_ct w16 a b tr₂ ur₂ s' u' trivial trivial
          ⟨ka.sp.trans (hpub.1.trans kb.sp.symm),fun r hr => by
            have hr' : r=.x3 ∨ r=.x4 ∨ r=.x9 ∨ r=.x11 ∨ r=.x12 := by
              simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] using hr
            rcases hr' with rfl|rfl|rfl|rfl|rfl
            · rw [ha.x3,hb.x3]
            · exact BitVec.eq_of_toNat_eq (ha.x4.trans hb.x4.symm)
            · exact BitVec.eq_of_toNat_eq (ha.x9.trans hb.x9.symm)
            · exact BitVec.eq_of_toNat_eq (va.trans vb.symm)
            · exact BitVec.eq_of_toNat_eq (wa.trans wb.symm)⟩ er fr
        rw [htr,hrest]
  obtain ⟨_,a,ea,ha,_⟩ := Scalar.body_ok ps.toLPreW ht hp.1
  obtain ⟨_,b,eb,hb,_⟩ := Scalar.body_ok pu.toLPreW ht hp.2
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  exact ⟨trace,ha,hb⟩

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Public invariants across vector and scalar rejection steps -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def PairInvW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr)
    (s₀ u₀ : State) (t : Nat) (s u : State) : Prop :=
  Scalar.InvW w16 initial N B bP aP s₀ t s ∧ Scalar.InvW w16 initial N B bP aP u₀ t u ∧
    Constants s ∧ Constants u

theorem vectorStep_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (ht : t+4≤N)
    (hroom : (Scalar.LA initial B t).length+8≤256) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t)
      (.block (Impl.MlKem.AArch64.Rej8.rejEight w16)) (PairInvW w16 initial N B bP aP s₀ u₀ (t+4)) := by
  intro s u tr ur s' u' hp es eu
  obtain ⟨hs,hu,cs,cu⟩ := hp
  have pub := inv_public hs hu hsp
  have htr := (batch_relCT w16 s u tr ur s' u'
    ⟨cs,cu,inv_candidates ps pu hs hu ht,
      by rw [hs.acc.rd,hs.acc.wr,hs.x2]; exact ps.input16 t ht,
      by rw [hu.acc.rd,hu.acc.wr,hu.x2]; exact pu.input16 t ht,
      pub.1,pub.2 .x2 (by simp),pub.2 .x3 (by simp),
      by rw [hs.keep.get .x16,hu.keep.get .x16,htab]⟩ es eu).1
  obtain ⟨_,a,ea,ha,ca⟩ := vector_ok ps hs cs ht (by rw [hs.acc.x4]; omega_using [hroom])
  obtain ⟨_,b,eb,hb,cb⟩ := vector_ok pu hu cu ht (by rw [hu.acc.x4]; omega_using [hroom])
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  exact ⟨htr,ha,hb,ca,cb⟩

theorem scalarFour_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (ht : t+4≤N) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t) (scalarFour w16)
      (PairInvW w16 initial N B bP aP s₀ u₀ (t+4)) := by
  have hct : RelCT isa (fun s u => Scalar.InvW w16 initial N B bP aP s₀ t s ∧
      Scalar.InvW w16 initial N B bP aP u₀ t u) (scalarFour w16)
      (fun s u => Scalar.InvW w16 initial N B bP aP s₀ (t+4) s ∧
        Scalar.InvW w16 initial N B bP aP u₀ (t+4) u) := by
    exact RelCT.seq (scalarBody_relCT ps pu hsp (by omega_using [ht]))
      (RelCT.seq (scalarBody_relCT ps pu hsp (by omega_using [ht]))
        (RelCT.seq (scalarBody_relCT ps pu hsp (by omega_using [ht]))
          (scalarBody_relCT ps pu hsp (by omega_using [ht]))))
  intro s u tr ur s' u' hp es eu
  obtain ⟨htr,hs,hu⟩ := hct s u tr ur s' u' ⟨hp.1,hp.2.1⟩ es eu
  obtain ⟨_,a,ea,_,va⟩ := scalarFour_ok ps.toLPreW hp.1 ht
  obtain ⟨_,b,eb,_,vb⟩ := scalarFour_ok pu.toLPreW hp.2.1 ht
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  refine ⟨htr,hs,hu,?_,?_⟩
  · exact ⟨by rw [va]; exact hp.2.2.1.index,by rw [va]; exact hp.2.2.1.mask,
      by simpa only [va] using hp.2.2.1.q,by simpa only [va] using hp.2.2.1.weights,
      by simpa only [va] using hp.2.2.1.zero⟩
  · exact ⟨by rw [vb]; exact hp.2.2.2.index,by rw [vb]; exact hp.2.2.2.mask,
      by simpa only [vb] using hp.2.2.2.q,by simpa only [vb] using hp.2.2.2.weights,
      by simpa only [vb] using hp.2.2.2.zero⟩

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Paired executions choose the same rejection path and early exit -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def BodyPairPostW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr)
    (s₀ u₀ : State) (t : Nat) (s u : State) : Prop :=
  PairInvW w16 initial N B bP aP s₀ u₀ (t+4) s u ∨
    (ResultW w16 initial N B aP s₀ s ∧ ResultW w16 initial N B aP u₀ u ∧ s.gpr .x5=0 ∧ u.gpr .x5=0)

theorem choice_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block choosePrefix) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)

theorem choice_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (hsp : s₀.sp=u₀.sp) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t) (.block choosePrefix)
      (fun s u => PairInvW w16 initial N B bP aP s₀ u₀ t s u ∧
        (s.gpr .x6 == 0)=(u.gpr .x6 == 0) ∧
        ((s.gpr .x6 == 0)=true ↔ 8≤(s.gpr .x4).toNat)) := by
  intro s u tr ur s' u' hp es eu
  have pub := inv_public hp.1 hp.2.1 hsp
  have htr := choice_ct s u tr ur s' u' trivial trivial ⟨pub.1,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩ es eu
  obtain ⟨_,a,ea,ha,ca,fa⟩ := choosePrefix_ok hp.1 hp.2.2.1
  obtain ⟨_,b,eb,hb,cb,fb⟩ := choosePrefix_ok hp.2.1 hp.2.2.2
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  refine ⟨htr,⟨ha,hb,ca,cb⟩,?_,fa⟩
  apply Bool.eq_iff_iff.mpr
  rw [fa,fb,(inv_public ha hb hsp).2 .x4 (by simp)]

theorem stop_full_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (h : Scalar.InvW w16 initial N B bP aP s₀ t s) (hc : Constants s)
    (ht : t≤N) (hf : (Scalar.LA initial B t).length=256) :
    WP isa (.block [.movz .x .x5 0 0]) s fun u => ResultW w16 initial N B aP s₀ u ∧ u.gpr .x5=0 := by
  have heq := sampleAfter_full (show (Scalar.LA initial B t).length=n from hf) N ht
  have hw : WP isa (.block [.movz .x .x5 0 0]) s fun u =>
      Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u ∧ Keep Scalar.lRegs s₀ u ∧ u.gpr .x5=0 := by
    refine wp_movz fun u hu eu => wp_nil ⟨?_,(h.keep.trans hu.keep).mono (by decide),eu⟩
    rw [show Scalar.LA initial B N=Scalar.LA initial B t from heq]
    exact Scalar.acc_keep h.acc hu.keep hu.mem
  refine WP.mono (WP.keepV (by decide) hw) fun u ⟨⟨ac,ke,x5⟩,ve⟩ => ⟨⟨ac,ke,?_⟩,x5⟩
  exact ⟨by rw [ve]; exact hc.index,by rw [ve]; exact hc.mask,
    by simpa only [ve] using hc.q,by simpa only [ve] using hc.weights,
    by simpa only [ve] using hc.zero⟩

theorem stop_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (hsp : s₀.sp=u₀.sp) (ht : t+4≤N) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ (t+4))
      (.ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block []))
      (BodyPairPostW w16 initial N B bP aP s₀ u₀ t) := by
  refine RelCT.ite (fun s u hp => by rw [eval_zero,eval_zero,(inv_public hp.1 hp.2.1 hsp).2 .x4 (by simp)]) ?_ ?_
  · intro s u tr ur s' u' hp es eu
    have hf : (Scalar.LA initial B (t+4)).length=256 := by
      have hz := hp.2
      rw [eval_zero] at hz
      have hz' : (s.gpr .x4).toNat=0 := by simpa only [Option.some.injEq,eq_zero_iff,decide_eq_true_eq] using hz
      rw [hp.1.1.acc.x4] at hz'
      have := hp.1.1.acc.len
      omega_using [hz', this]
    have ct : ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
        (.block [.movz .x .x5 0 0]) :=
      VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)
    have htr := ct s u tr ur s' u' trivial trivial
      ⟨(inv_public hp.1.1 hp.1.2.1 hsp).1,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩ es eu
    obtain ⟨_,a,ea,ha,xa⟩ := stop_full_ok hp.1.1 hp.1.2.2.1 ht hf
    obtain ⟨_,b,eb,hb,xb⟩ := stop_full_ok hp.1.2.1 hp.1.2.2.2 ht hf
    obtain ⟨_,rfl⟩ := Exec.det es ea
    obtain ⟨_,rfl⟩ := Exec.det eu eb
    exact ⟨htr,Or.inr ⟨ha,hb,xa,xb⟩⟩
  · exact RelCT.block_nil (fun _ _ h => Or.inl h.1)

theorem body_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (ht : t+4≤N) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t) (body w16)
      (BodyPairPostW w16 initial N B bP aP s₀ u₀ t) := by
  refine RelCT.seq (choice_relCT hsp) (RelCT.ite (fun s u hp => by
    rw [eval_zero,eval_zero,hp.2.1]) ?_ ?_)
  · intro s u tr ur s' u' hp es eu
    have hz : (s.gpr .x6 == 0)=true := by
      have hx := hp.2
      rw [eval_zero] at hx
      exact Option.some.inj hx
    have hr := hp.1.2.2.mp hz
    rw [hp.1.1.1.acc.x4] at hr
    have hlen := hp.1.1.1.acc.len
    obtain ⟨he,hp'⟩ := vectorStep_relCT ps pu hsp htab ht (by omega_using [hr]) s u tr ur s' u' hp.1.1 es eu
    exact ⟨he,Or.inl hp'⟩
  · exact RelCT.mono (RelCT.seq (scalarFour_relCT ps pu hsp ht) (stop_relCT hsp ht))
      (fun _ _ h => h.1.1) (fun _ _ h => h)

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Relational timing of bounded mixed rejection -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem iters_relCT {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (hN : 0<N) (hm : N%4=0) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ 0) (.loop (body w16) (.nonzero .x .x5))
      (fun s u => ResultW w16 initial N B aP s₀ s ∧ ResultW w16 initial N B aP u₀ u) := by
  let I := fun m s u => ∃t,m=N-t ∧ t<N ∧ t%4=0 ∧ PairInvW w16 initial N B bP aP s₀ u₀ t s u
  have step : ∀m,RelCT isa (I m) (body w16) (fun s u =>
      isa.eval (.nonzero .x .x5) s=isa.eval (.nonzero .x .x5) u ∧
      (isa.eval (.nonzero .x .x5) s=some false → ResultW w16 initial N B aP s₀ s ∧ ResultW w16 initial N B aP u₀ u) ∧
      (isa.eval (.nonzero .x .x5) s=some true → ∃m'<m,I m' s u)) := by
    intro m s u tr ur s' u' hp es eu
    obtain ⟨t,rfl,ht,htm,hp⟩ := hp
    have ht4 : t+4≤N := by omega_using [hm, ht, htm]
    obtain ⟨htr,hr⟩ := body_relCT ps pu hsp htab ht4 s u tr ur s' u' hp es eu
    refine ⟨htr,?_⟩
    rcases hr with hr|⟨rs,ru,xs,xu⟩
    · have hx := (inv_public hr.1 hr.2.1 hsp).2 .x5 (by simp)
      refine ⟨by rw [eval_nonzero,eval_nonzero,hx],?_,?_⟩
      · intro hz
        have hz' : N-(t+4)=0 := by
          rw [eval_nonzero,ne_zero_iff,hr.1.x5] at hz
          have hh := of_decide_eq_false (Option.some.inj hz)
          omega_using [hh]
        have he : t+4=N := by omega_using [hm, ht, htm, hz']
        rw [he] at hr
        exact ⟨⟨hr.1.acc,hr.1.keep,hr.2.2.1⟩,⟨hr.2.1.acc,hr.2.1.keep,hr.2.2.2⟩⟩
      · intro hz
        have hz' : N-(t+4)≠0 := by
          rw [eval_nonzero,ne_zero_iff,hr.1.x5] at hz
          exact of_decide_eq_true (Option.some.inj hz)
        exact ⟨N-(t+4),by omega_using [ht],t+4,rfl,by omega_using [hz'],by omega_using [htm],hr⟩
    · refine ⟨by rw [eval_nonzero,eval_nonzero,xs,xu],fun _ => ⟨rs,ru⟩,?_⟩
      intro hz
      rw [eval_nonzero,xs] at hz
      contradiction
  exact RelCT.mono (RelCT.loop I step N)
    (fun _ _ h => ⟨0,by omega_using [],hN,rfl,h⟩) (fun _ _ h => h)

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! ### `MlKem.AArch64.Rej8Finish`, which this module and modules that import it used -/

section

/-! # Preserve the accepted prefix and report bounded sampling success -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Loop.lean`, which only this module imported.
section

/-! # Termination and exact semantics of the mixed rejection loop -/

section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem iters_ok {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : EnvW w16 N B bP aP s₀) (hN : 0<N) (hm : N%4=0)
    (h : Scalar.InvW w16 initial N B bP aP s₀ 0 s) (hc : Constants s) :
    WP isa (.loop (body w16) (.nonzero .x .x5)) s (ResultW w16 initial N B aP s₀) := by
  refine WP.loop (M := isa)
    (fun m u => ∃t,m=N-t ∧ t<N ∧ t%4=0 ∧ Scalar.InvW w16 initial N B bP aP s₀ t u ∧ Constants u)
    ?_ N s ⟨0,by omega,hN,rfl,h,hc⟩
  rintro m u ⟨t,rfl,ht,htm,hi,hic⟩
  have ht4 : t+4≤N := by omega
  refine WP.mono (body_ok hp hi hic ht4) fun v hv => ?_
  rcases hv with ⟨hv,hvc⟩ | ⟨hv,hx5⟩
  · by_cases he : t+4=N
    · apply Or.inl
      refine ⟨?_,?_⟩
      · rw [eval_nonzero,ne_zero_iff,hv.x5,he,Nat.sub_self]
        rfl
      · rw [he] at hv
        exact ⟨hv.acc,hv.keep,hvc⟩
    · apply Or.inr
      refine ⟨?_,N-(t+4),by omega,t+4,rfl,by omega,by omega,hv,hvc⟩
      rw [eval_nonzero,ne_zero_iff,hv.x5]
      have hn : N-(t+4)≠0 := by omega
      exact congrArg some (decide_eq_true hn)
  · apply Or.inl
    refine ⟨?_,hv⟩
    rw [eval_nonzero,hx5]
    rfl

end VG.Proof.MlKem.AArch64.Rej8
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def fix : Prog isa := .ite (.zero .x .x4) (.block [])
  (.block [.movz .x .x13 0 0,.str .w .x13 .x3 0])

theorem fix_ok {w16 : Bool} {aP : Addr} {s₀ s : State} {L : List Zq}
    (hina : ∀i<256,InRegions s₀.wr (cAddr w16 aP i) 4)
    (h : Scalar.AccW w16 aP s₀ L s) : WP isa fix s fun u =>
      Scalar.AccW w16 aP s₀ L u ∧ Keep [.x13] s u := by
  have hl := h.len
  refine WP.ite (s.gpr .x4 == 0) (eval_zero _ _) (fun _ => wp_nil ⟨h,Keep.refl _ _⟩) (fun hz => ?_)
  rw [eq_zero_iff,decide_eq_false_iff_not,h.x4] at hz
  have hlt : L.length<256 := by omega_using [hz]
  refine wp_movz fun a ha ea => wp_strw (a := cAddr w16 aP L.length) (by decide)
    (by rw [ha.gpr .x3 (by decide),h.x3,ptr_zero])
    (by rw [ha.wr,h.wr]; exact hina _ hlt) fun u hu => wp_nil ?_
  have hk := (ha.keep.trans hu.keep).mono (rs' := [.x13]) (by decide)
  have hm : u.mem=s.mem.writeW (cAddr w16 aP L.length) (0 : BitVec 32) := by
    rw [hu.mem,ea,ha.mem]
    rfl
  refine ⟨⟨hk.rd.trans h.rd,hk.wr.trans h.wr,hk.sp.trans h.sp,h.len,
    by rw [hk.get .x3,h.x3],by rw [hk.get .x4,h.x4],by rw [hk.get .x9,h.x9],?_,?_⟩,hk⟩
  · rw [hm]; exact h.coeffs.reject hlt 0 (by decide)
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (cAddr_contains4 w16 _ hlt)

structure PostW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (aP : Addr) (s₀ u : State) :
    Prop where
  acc : Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u
  keep : Keep (.x0::Scalar.lRegs) s₀ u
  status : (u.gpr .x0).toNat=if (Scalar.LA initial B N).length=256 then 1 else 0

theorem loop_ok {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : EnvW w16 N B bP aP s₀) (hN : 0<N) (hm : N%4=0)
    (h : Scalar.InvW w16 initial N B bP aP s₀ 0 s) (hc : Constants s) :
    WP isa (Impl.MlKem.AArch64.Rej8.rejLoop w16) s (PostW w16 initial N B aP s₀) := by
  rw [show Impl.MlKem.AArch64.Rej8.rejLoop w16 = .seq (.loop (body w16) (.nonzero .x .x5))
    (.seq fix (.block [.subImm .x .x0 .x4 1,.lsr .x .x0 .x0 63])) from rfl]
  refine WP.seq (WP.mono (iters_ok hp hN hm h hc) fun a ha => ?_)
  refine WP.seq (WP.mono (fix_ok hp.ina ha.acc) fun b ⟨hb,hk⟩ => ?_)
  refine wp_subImm (by decide) fun c hc ec => wp_lsr (by decide) fun u hu eu => wp_nil ?_
  have k := hc.keep.trans hu.keep
  refine ⟨Scalar.acc_keep hb k (hu.mem.trans hc.mem),
    ((ha.keep.trans hk).trans k).mono (by decide),?_⟩
  have hl := hb.len
  rw [eu,toNat_lsr,ec,BitVec.toNat_sub,hb.x4]
  simp only [BitVec.toNat_ofNat]
  split <;> omega_arith

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # The complete SIMD/scalar rejection loop has public-seed-only timing -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def finish : Prog isa := .seq fix (.block [.subImm .x .x0 .x4 1,.lsr .x .x0 .x0 63])

theorem finish_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) finish := by
  unfold finish
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem loop_relCT {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (hN : 0<N) (hm : N%4=0) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ 0) (Impl.MlKem.AArch64.Rej8.rejLoop w16)
      (fun s u => PostW w16 initial N B aP s₀ s ∧ PostW w16 initial N B aP u₀ u) := by
  have hct : RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ 0) (Impl.MlKem.AArch64.Rej8.rejLoop w16)
      (fun _ _ => True) := by
    refine RelCT.seq (iters_relCT ps pu hsp htab hN hm) ?_
    intro s u tr ur s' u' hp es eu
    have hs := hp.1.acc
    have hu := hp.2.acc
    have htr := finish_ct s u tr ur s' u' trivial trivial
      ⟨hs.sp.trans (hsp.trans hu.sp.symm),fun r hr => by
        have hr' : r=.x3 ∨ r=.x4 := by
          simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] using hr
        rcases hr' with rfl|rfl
        · rw [hs.x3,hu.x3]
        · exact BitVec.eq_of_toNat_eq (hs.x4.trans hu.x4.symm)⟩ es eu
    exact ⟨htr,trivial⟩
  intro s u tr ur s' u' hp es eu
  have htr := (hct s u tr ur s' u' hp es eu).1
  obtain ⟨_,a,ea,ha⟩ := loop_ok ps hN hm hp.1 hp.2.2.1
  obtain ⟨_,b,eb,hb⟩ := loop_ok pu hN hm hp.2.1 hp.2.2.2
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  exact ⟨htr,ha,hb⟩

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # A reusable rejection segment with an existing accepted prefix -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem EnvW.transfer {w16 : Bool} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s u : State}
    (h : EnvW w16 N B bP aP s) (hm : u.mem=s.mem) (hr : u.rd=s.rd) (hw : u.wr=s.wr)
    (h16 : u.gpr .x16=s.gpr .x16) : EnvW w16 N B bP aP u := by
  refine ⟨⟨?_,?_,?_,h.disj,h.bound⟩,?_,?_,?_,?_,?_⟩
  · simpa only [hm] using h.buf
  · simpa only [hr,hw] using h.inb
  · simpa only [hw] using h.ina
  · simpa only [hr,hw] using h.input16
  · simpa only [hw] using h.output16
  · simpa only [hr,hw,h16] using h.tableRead
  · simpa only [hm,h16] using h.tableData
  · simpa only [h16] using h.tableDisj

structure EntryW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr) (s : State) :
    Prop where
  env : EnvW w16 N B bP aP s
  constants : Constants s
  len : initial.length≤256
  coeffs : Scalar.CoeffsW w16 s.mem aP initial
  x2 : s.gpr .x2=bP
  x3 : s.gpr .x3=cAddr w16 aP initial.length
  x4 : (s.gpr .x4).toNat=256-initial.length
  x5 : (s.gpr .x5).toNat=N
  x9 : (s.gpr .x9).toNat=q
  x10 : (s.gpr .x10).toNat=15

theorem EntryW.inv {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s : State}
    (h : EntryW w16 initial N B bP aP s) : Scalar.InvW w16 initial N B bP aP s 0 s :=
  ⟨⟨rfl,rfl,rfl,h.len,h.x3,h.x4,h.x9,h.coeffs,Frame.refl _ _⟩,Keep.refl _ _,
    by simpa only [Nat.mul_zero,ptr_zero] using h.x2,
    by simpa only [Nat.sub_zero] using h.x5,h.x10⟩

theorem segment_ok {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s : State}
    (h : EntryW w16 initial N B bP aP s) (hN : 0<N) (hm : N%4=0) :
    WP isa (Impl.MlKem.AArch64.Rej8.rejLoop w16) s (PostW w16 initial N B aP s) :=
  loop_ok h.env hN hm h.inv h.constants

theorem segment_relCT {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s u : State} (hs : EntryW w16 initial N B bP aP s) (hu : EntryW w16 initial N B bP aP u)
    (hsp : s.sp=u.sp) (htab : s.gpr .x16=u.gpr .x16) (hN : 0<N) (hm : N%4=0) :
    RelCT isa (fun a b => a=s ∧ b=u) (Impl.MlKem.AArch64.Rej8.rejLoop w16)
      (fun a b => PostW w16 initial N B aP s a ∧ PostW w16 initial N B aP u b) :=
  RelCT.mono (loop_relCT hs.env hu.env hsp htab hN hm)
    (by intro a b h; rcases h with ⟨rfl,rfl⟩; exact ⟨hs.inv,hu.inv,hs.constants,hu.constants⟩)
    (fun _ _ h => h)

end VG.Proof.MlKem.AArch64.Rej8
