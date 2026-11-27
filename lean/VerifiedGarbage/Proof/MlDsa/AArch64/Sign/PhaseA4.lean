module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Prims
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MlDsa.AArch64.Sign.Seed4`, which this module and modules that import it used -/

section

/-! Signing matrix expansion: four seeds, with the earlier matrix and caller state preserved. -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def seedCopy4 (j : Nat) : List Instr := lea .x10 .x28 (oRS4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oRS .x10 0

theorem copySeed4_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : inB (rbs++wbs) (sc oRS) 32 = true)
    (hdst : inB wbs (sc (oRS4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oRS) 32 (sc (oRS4+34*j)) 32 = true) :
    WP isa (.block (seedCopy4 j)) s fun t =>
      PPostB S s t [(sc (oRS4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oRS4+34*j))) 32 = bytesAt s.mem (pa s (sc oRS)) 32 := by
  unfold seedCopy4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oRS4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oRS,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oRS),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oRS4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oRS4+34*j))) (sb := .x28) (db := .x10) (so := oRS) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oRS),32⟩ : Region).Disjoint ⟨pa s (sc (oRS4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]


end VG.Proof.MlDsa.AArch64.Sign

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

structure AS (p : Params) (D : Nat) (σ : State) (e j : Nat) (s : State) : Prop where
  ia : IA p D σ e s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oRS4+34*k))) 34 = seedE p σ (e+k)

def slotChk (p : Params) (e j : Nat) : Bool :=
  let ws : List (Ptr × Nat) := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)]
  inB (sgB p) (sc oRS) 32 && inB (sgW p) (sc (oRS4+34*j)) 32 &&
    sepB (sgR p) (sgW p) (sc oRS) 32 (sc (oRS4+34*j)) 32 && stChk p ws &&
    keepB (sgR p) (sgW p) ws (sc oRS) 32 && famChk (sgR p) (sgW p) ws (aBase p) e &&
    inB (sgW p) (sc (oRS4+34*j+32)) 1 && inB (sgW p) (sc (oRS4+34*j+33)) 1 &&
    keepB (sgR p) (sgW p) [(sc (oRS4+34*j+33),1)] (sc (oRS4+34*j+32)) 1 &&
    keepB (sgR p) (sgW p) [(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)] (sc (oRS4+34*j)) 32 &&
    (List.range j).all (fun k => keepB (sgR p) (sgW p) ws (sc (oRS4+34*k)) 34)

theorem slotChk_ok : ∀ p ∈ [mlDsa44,mlDsa65,mlDsa87],∀ e < p.k*p.ℓ,∀ j < 4,slotChk p e j = true := by
  decide +kernel

theorem IA.keep {p : Params} {D : Nat} {σ s t : State} {e : Nat} (h : IA p D σ e s)
    {ws : List (Ptr × Nat)} (hp : PPostB D s t ws) (hc : stChk p ws = true)
    (hr : keepB (sgR p) (sgW p) ws (sc oRS) 32 = true) (hf : famChk (sgR p) (sgW p) ws (aBase p) e = true)
    (h24 : t.gpr .x24 = s.gpr .x24) : IA p D σ e t :=
  ⟨h.st.step hp hc,(h.st.lay.keepBytes hp hr).trans h.rs,h24 ▸ h.r01,
    fun ht => let ⟨ok,fam⟩ := h.ok (h24 ▸ ht); ⟨ok,Fam.keep h.st.lay hp hf fam⟩,
    fun ht => h.bad (h24 ▸ ht)⟩

theorem slot4_ok {p : Params} {D : Nat} {σ : State} {e j : Nat} (hj : j < 4)
    (hc : slotChk p e j = true) {s : State} (h : AS p D σ e j s) :
    WP isa (seedSlot4 p e j) s fun t => AS p D σ e (j+1) t ∧ t.gpr .x24 = s.gpr .x24 := by
  simp only [slotChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨csrc,cdst⟩,csep⟩,cst⟩,crs⟩,cfam⟩,cw1⟩,cw2⟩,ck12⟩,ck32⟩,ckprev⟩ := hc
  have L := h.ia.st.lay
  unfold seedSlot4
  change WP isa (.seq (.block (seedCopy4 j)) _) s _
  refine WP.seq (WP.mono (copySeed4_ok L csrc cdst csep) fun s1 ⟨hP1,k1,b1⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok (L.post hP1) (p := sc (oRS4+34*j+32)) (v := (e+j)%p.ℓ)
    (by dsimp only [oRS4]; omega_using [hj]) cw1 (by change Reg.x28 ∈ keptRegs; decide)) fun s2 ⟨hP2,k2,m2⟩ => ?_
  refine WP.mono (setB_ok ((L.post hP1).post hP2) (p := sc (oRS4+34*j+33)) (v := (e+j)/p.ℓ)
    (by dsimp only [oRS4]; omega_using [hj]) cw2 (by change Reg.x28 ∈ keptRegs; decide)) fun t ⟨hP3,k3,m3⟩ => ?_
  have hp12 := PPostB.trans hP1 hP2 (ws := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1)])
    (by simp [sc,keptRegs]) (by simp) (by simp)
  have hp := PPostB.trans hp12 hP3 (ws := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)])
    (by simp [sc,keptRegs]) (by simp) (by simp)
  have h24 : t.gpr .x24 = s.gpr .x24 := by rw [k3.get .x24,k2.get .x24,k1.get .x24]
  refine ⟨⟨h.ia.keep hp cst crs cfam h24,fun k hk => ?_⟩,h24⟩
  by_cases heq : k = j
  · subst k
    have hrho : bytesAt t.mem (pa t (sc (oRS4+34*j))) 32 = rhoOf p σ := by
      have hp23 := PPostB.trans hP2 hP3 (ws := [(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)])
        (by simp [sc,keptRegs]) (by simp) (by simp)
      rw [(L.post hP1).keepBytes hp23 ck32,hP1.pa (by change Reg.x28 ∈ keptRegs; decide),b1,h.ia.rs]
    refine seed34 hrho ?_ ?_
    · rw [pa_sc_add,((L.post hP1).post hP2).keepBytes hP3 ck12,m2,hP2.pa (by change Reg.x28 ∈ keptRegs; decide)]
      exact bytes1_write _ _ _
    · rw [pa_sc_add,m3,hP3.pa (by change Reg.x28 ∈ keptRegs; decide)]
      exact bytes1_write _ _ _
  · rw [L.keepBytes hp (ckprev k (by omega_using [hk, heq]))]
    exact h.done k (by omega_using [hk, heq])

end VG.Proof.MlDsa.AArch64.Sign

end

end

/-! ### `MlDsa.AArch64.Sign.Call4`, which only this module used -/

section

/-!
# ML-DSA signing on AArch64: calls of the samplers

For each call of `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_sample_in_ball`: what it
needs of the layout (`…Chk`), what it does (`…_ok`), and that two runs whose
layout registers agree, and whose sampler leaks the same, leak the same
(`…_tr`).
-/

@[expose] public section

/-! Calls of the four-way sampler through the shared contract, including public return values. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `RejNTTPoly` -/

def rej4Chk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 136 a 4096 && sepB rbs wbs seed 136 ss 8192 && sepB rbs wbs a 4096 ss 8192 &&
    inB (rbs ++ wbs) seed 136 && inB (rbs ++ wbs) a 4096 && inB (rbs ++ wbs) ss 8192 && inB wbs a 4096 &&
    inB wbs ss 8192

abbrev rej4Args (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : rej4Chk rbs wbs seed a ss = true)
include L hc

theorem rej4_cov : Covers ([⟨pa s seed, 136⟩] ++ [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩] s.wr := by
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej4_pre {s1 : State} (h1 : Args (rej4Args seed a ss) s s1) :
    (rejNTT4Contract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 136⟩] [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) := by
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rej4_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (c4 : inB bs seed 136 = true)
    (c5 : inB bs a 4096 = true) (c6 : inB bs ss 8192 = true) :
    ∀ x ∈ rej4Args seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩


theorem rej4AtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    (hr : RetPub (rejNTT4Contract AArch64.abi S) P.rej4)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 136 = bytesAt y.mem (pa y seed) 136 ∧ SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (rej4Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet C hr (rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej4_pre Lx hc h1, ?_, ?_, (rej4_cov Lx hc).1, (rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign

end

end


/-! Signing matrix expansion in batches of four: sampler outcomes, bounded failure, and the single-stream remainder. -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem aseeds_eq {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oRS4)) k = seedE p σ (e+k) := by
  unfold seed4
  rw [pa_sc_add]
  exact h.done k hk

theorem rej4Call_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {s : State} (L : Lay D (sgR p) (sgW p) s)
    {seed a ss : Ptr} (hc : rej4Chk (sgR p) (sgW p) seed a ss = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (rej4Args seed a ss)) s fun t =>
      PPostB D s t [(a,4096),(ss,8192)] ∧ t.gpr .x24 = s.gpr .x24 ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced t.mem (poly4 (pa s a) k)) ∧
      (((t.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt t.mem (poly4 (pa s a) k))) ∨
        ((t.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 4,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (pa s seed) k)).isSome) := by
  have hc' := hc
  simp only [rej4Chk,Bool.and_eq_true,and_assoc] at hc'
  obtain ⟨_,_,_,c4,c5,c6,_,_⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.rej4.withPost hP.rej4Max) (rej4_args L.ok c4 c5 c6)
    (by simp only [List.map_cons,List.map_nil]; decide) (fun s1 h1 => rej4_pre L hc h1) (rej4_cov L hc).1
    (rej4_cov L hc).2) fun t ⟨hp,s1,h1,hq,hx⟩ => ⟨hp.b,hp.cs .x24 (by decide) (by decide),?_⟩
  sig_post [rejNTT4Contract,rejNTT4Sig,AArch64.abi,AArch64.argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  simp only [State.withRegions_gpr,State.withRegions_mem,State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),Args.r0 h1,Args.mem h1,Arg.val] at hx
  exact ⟨hq.1,hq.2,hx⟩

def batchChk (p : Params) (g : Nat) : Bool :=
  let a := pS (aBase p+4*g)
  let ws : List (Ptr × Nat) := [(a,4096),(sc (oR4 p),8192)]
  rej4Chk (sgR p) (sgW p) (sc oRS4) a (sc (oR4 p)) && stChk p ws && stChk p [] &&
    keepB (sgR p) (sgW p) ws (sc oRS) 32 && famChk (sgR p) (sgW p) ws (aBase p) (4*g)

theorem batchChk_ok : ∀ p ∈ [mlDsa44,mlDsa65,mlDsa87],∀ g < p.k*p.ℓ/4,batchChk p g = true := by decide +kernel

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (pS e)) k = pa s (pS (e+k)) := by
  unfold poly4
  rw [pa_sc_add]
  rw [show oP e+1024*k = oP (e+k) by simp only [oP]; omega_using []]

theorem batch_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hc : batchChk p g = true) {s : State} (h : AS p D σ (4*g) 4 s) :
    WP isa (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4
      (rej4Args (sc oRS4) (pS (aBase p+4*g)) (sc (oR4 p)))) (.block and24)) s
      (IA p D σ (4*g+4)) := by
  simp only [batchChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨cr,cst⟩,c0⟩,crs⟩,cfam⟩ := hc
  refine WP.seq (WP.mono (rej4Call_ok hP h.ia.st.lay cr) fun s1 ⟨hp,h24,hred,hout,hmax⟩ => ?_)
  have S1 := h.ia.st.step hp cst
  refine WP.mono (and24_ok s1) fun t ⟨kt,et⟩ => ?_
  have hpt : PPostB D s1 t [] := postB24 kt _
  have hr : (s1.gpr .x0).setWidth 32 = 1 ∨ (s1.gpr .x0).setWidth 32 = 0 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inl h1,.inr h0]
  have et' : t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s1.gpr .x0).setWidth 32) := by rw [et,h24]
  refine ⟨S1.step hpt c0,by rw [kt.mem,hpt.pa (by decide),h.ia.st.lay.keepBytes hp crs]; exact h.ia.rs,
    ?_,fun ht => ?_,fun ht => ?_⟩
  · rw [et']
    rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] <;> decide
  · have hs : s.gpr .x24 = 1 ∧ (s1.gpr .x0).setWidth 32 = 1 := by
      rw [et'] at ht
      rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] at ht <;>
        first | exact ⟨e0,e1⟩ | exact absurd ht (by decide)
    obtain ⟨ok,fam⟩ := h.ia.ok hs.1
    have fm := Fam.of_eq kt.mem (hpt.bs _ (by decide)) (Fam.keep h.ia.st.lay hp cfam fam)
    refine ⟨fun e' he' => ?_,fun e' he' => ?_⟩
    · by_cases hlt : e' < 4*g
      · exact ok e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega_using [hlt]⟩
        rw [← aseeds_eq h (by omega_using [he'])]; exact hmax hs.2 k (by omega_using [he'])
    · by_cases hlt : e' < 4*g
      · exact fm e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega_using [hlt]⟩
        have hk : k < 4 := by omega_using [he']
        have hm := hmax hs.2 k hk
        have hv : polyAt s1.mem (poly4 (pa s (pS (aBase p+4*g))) k) = aVal p σ (4*g+k) := by
          obtain ⟨_,hb⟩ | ⟨h0,_⟩ := hout
          · have hv := rej_val (.inl ⟨hs.2,hb k hk⟩) hs.2 hm
            rw [aseeds_eq h hk] at hv
            exact hv
          · rw [hs.2] at h0; cases h0
        show PolyIs t.mem (pa t (pS (aBase p+(4*g+k)))) (aVal p σ (4*g+k))
        rw [kt.mem,hpt.pa (by change Reg.x28 ∈ keptRegs; decide),hp.pa (by change Reg.x28 ∈ keptRegs; decide),← Nat.add_assoc,← pa_poly4]
        exact ⟨hred hs.2 k hk,hv⟩
  · rw [et'] at ht
    rcases h.ia.r01 with e0 | e0
    · obtain ⟨e',he',hn⟩ := h.ia.bad e0; exact ⟨e',by omega_using [he'],hn⟩
    · rcases hr with e1 | e1
      · rw [e0,e1] at ht; exact absurd ht (by decide)
      · rcases hout with ⟨h1,_⟩ | ⟨_,k,hk,hn⟩
        · exact absurd (e1.symm.trans h1) (by decide)
        · exact ⟨4*g+k,by omega_using [hk],by rw [← aseeds_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Sign

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem sample4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hb : batchChk p g = true) (hs : ∀ j < 4,slotChk p (4*g) j = true) {s : State} (h : IA p D σ (4*g) s) :
    WP isa (sample4 P p g) s (IA p D σ (4*g+4)) := by
  unfold sample4
  refine WP.seq (WP.mono (seqR_ok (I := AS p D σ (4*g)) 4 0
    (fun j _ hj s h => WP.mono (slot4_ok (by omega_using [hj]) (hs j (by omega_using [hj])) h) fun _ ht => ht.1)
    s ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩) fun t ht => ?_)
  exact batch_ok hP hb (by simpa using ht)

theorem sampleAll_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p)
    (hc : aChk p = true) {σ s : State} (h : IA p D σ 0 s) :
    WP isa (sampleAll P p) s (IA p D σ (p.k*p.ℓ)) := by
  have hp : p ∈ [mlDsa44,mlDsa65,mlDsa87] := by rcases h3 with rfl | rfl | rfl <;> simp
  have he : ∀ e < p.k*p.ℓ,eChk p e = true := by
    simp only [aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc
    exact hc.1.1.1
  unfold sampleAll
  refine WP.seq (WP.mono (seqR_ok (I := fun g => IA p D σ (4*g)) (p.k*p.ℓ/4) 0
    (fun g _ hg s h => sample4_ok hP (batchChk_ok p hp g (by omega_using [hg]))
      (fun j hj => slotChk_ok p hp (4*g) (by omega_using [hg]) j hj) h) s h) fun t ht => ?_)
  have htail := seqR_ok (I := IA p D σ) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
    (fun e _ he' s h => sampleE_ok hP (he e (by omega_using [he'])) h) t (by simpa only [Nat.zero_add] using ht)
  have eqn : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega_using []
  simpa only [eqn] using htail

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .x24 = 1) : WP isa (Impl.MlDsa.AArch64.Sign.expandA P p) s (IA p D σ (p.k*p.ℓ)) := by
  have hc' := hc
  simp only [aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨_,hcp⟩,hst⟩,hsk⟩ := hc'
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine WP.seq (WP.mono (copyP_ok hs.lay hcp) fun s1 ⟨hP1,hcs1,hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24,h15]
  exact sampleAll_ok hP h3 hc ⟨S1,by rw [hP1.pa (by decide),hb,rhoOf,← hs.sk,VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15,fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _),fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩

end VG.Proof.MlDsa.AArch64.Sign
