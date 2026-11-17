module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Core
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Aes.AArch64.Ecb
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Correct
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Lit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block

/-! ### `AesCbc.AArch64.Encrypt.Correct`, which only this module used -/

section

/-! ### `AesCbc.AArch64.Encrypt.Loops`, which only this module used -/

section

/-! ### `AesCbc.AArch64.Encrypt.Step`, which only this module used -/

section

/-! ### `AesCbc.AArch64.Encrypt.Prefetch`, which only this module used -/

section

/-! The last block never reads past the data buffer. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem zero_count {s : State} {n : Nat} (hn : n < 2^64) (hc : s.gpr .x3=BitVec.ofNat 64 n) :
    isa.eval (.zero .x .x3) s=some (decide (n=0)) := by
  change some (s.read .x .x3 == 0)=_
  simp only [State.read,BitVec.setWidth_eq,hc]
  congr 1
  by_cases h : n=0
  · rw [h]; rfl
  · rw [decide_eq_false h,beq_eq_false_iff_ne]
    intro he
    have h' := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn] at h'
    exact h h'

theorem prefetch_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k+1 ≤ N s₀)
    (h : Core s₀ k (k+1) s) :
    WP isa (.ite (.zero .x .x3) (.block []) (.block Impl.AesCbc.AArch64.Encrypt.prefetch)) s
      fun t => Core s₀ k (k+1) t ∧ VFrame [.v0] s t ∧
        (k+1 < N s₀ → t.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ t.v .v7) := by
  have hev := zero_count (by have := hp.data_wrap; omega_using [this]) h.count
  by_cases he : k+1=N s₀
  · refine WP.ite true ?_ (fun _ => WP.block_nil ⟨h,VFrame.refl _ _,fun hc => by omega⟩)
      (fun hf => by cases hf)
    rw [hev,he,Nat.sub_self]; rfl
  · refine WP.ite false ?_ (fun hf => by cases hf) (fun _ => ?_)
    · rw [hev,decide_eq_false (by omega_using [hk, he])]
    · have ha : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 16) 16 := by
        rw [h.ptr,Offset.add_add_eq (Dp s₀) (show 16*k+16=16*(k+1) by omega_using []),h.env.wr,hp.wr]
        exact ⟨dataR s₀,List.mem_append_right _ (by simp),
          Offset.contains_base (Dp s₀) (d:=16*(k+1)) (n:=16) (k:=16*N s₀)
            (by omega_using [hk, he]) (by have := hp.data_wrap; omega_using [hk, he, this])⟩
      refine WP.mono (load_ok s 16 (by decide) ha) fun t ht => ?_
      subst ht
      have hf := loaded_frame s 16
      refine ⟨h.vframe hf (by decide),hf,?_⟩
      intro _
      change s.mem.readW (s.gpr .x2+BitVec.ofNat 64 16) 128 ^^^ s.v .v7=_
      rw [h.ptr,Offset.add_add_eq (Dp s₀) (show 16*k+16=16*(k+1) by omega_using []),
        original_read h.data (by omega_using []) (by omega_using [hk, he])]
      rfl
end VG.Proof.AesCbc.AArch64.Encrypt

end

end

/-! ### `AesCbc.AArch64.Encrypt.Store`, which only this module used -/

section

/-! Commit a ciphertext without disturbing the prepared successor. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.AArch64.RegUpd

theorem Env.store {s₀ s t : State} (h : Env s₀ s) (hv : t.v=s.v) (hg : t.gpr=s.gpr)
    (hf : Frame [dataR s₀] s.mem t.mem) (hr : t.rd=s.rd) (hw : t.wr=s.wr) : Env s₀ t :=
  ⟨h.keys.of_v live_regs (fun _ _ => congrFun hv _) (congrFun hg _) (congrFun hg _),
    by rw [hv]; exact h.folded,by rw [hg]; exact h.iv,h.frame.trans hf,hr.trans h.rd,hw.trans h.wr⟩

def outState (s : State) : State := s.setV .v1 (s.v .v31 ^^^ s.v .v30)

theorem output_ok (s : State) :
    WP isa (.block [.vop (.logic .eor .v1 .v31 .v30)]) s fun t => t=outState s := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,isa,exec,VOp.eval,Option.map_some]
  exact ⟨_,rfl,rfl⟩

theorem output_frame (s : State) : VFrame [.v1] s (outState s) :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun r hr => setV_v_of_ne _ _ (Ne.symm (fun h => hr (by simpa only [List.mem_singleton] using h.symm)))⟩

theorem store_advance_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k < N s₀)
    (hc : Core s₀ k (k+1) s) (hval : st (s.v .v31 ^^^ s.v .v30)=output s₀ k)
    (hn : k+1 < N s₀ → s.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ s.v .v7) :
    WP isa (.block [.vop (.logic .eor .v1 .v31 .v30),.strq .v1 .x2 0,.addImm .x .x2 .x2 16])
      s (Inv s₀ (k+1)) := by
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (output_ok s) fun t ht => ?_
  subst ht
  let u := outState s
  have fu := output_frame s
  have cu := hc.vframe fu (by decide)
  have hv : ∀ j (hj : j < ([VReg.v1] : List VReg).length), ∀ i < 16,
      vbyte (u.v ([VReg.v1][j])) i=(output s₀ (k+0+j)).getD i 0 := by
    intro j hj i hi
    have hj0 : j=0 := by simpa using (Nat.eq_zero_of_le_zero (by simpa using hj))
    subst hj0
    have hh := congrArg (fun x : Spec.Aes.State => x.getD i 0) hval
    simpa only [Nat.add_zero,List.getElem_cons_zero,u,outState,setV_v_self,getD_st _ hi] using hh
  change WP isa (.block (VG.Impl.Aes.AArch64.Aese.stData [.v1] 0 ++ [.addImm .x .x2 .x2 16])) u _
  rw [WP.block_append_iff]
  refine WP.mono (stData_ok (m₀:=s₀.mem) (n:=N s₀) (c:=k) (F:=output s₀)
    (by have := hp.data_wrap; omega_using [this]) [.v1] 0 u cu.ptr (by decide) (by simp only [List.length_singleton,Nat.add_zero]; omega_using [hk])
    (by rw [cu.env.wr,hp.wr]; simp) (by simpa using cu.data) hv)
    fun v ⟨hd,hf,hg,hv,_,hr,hw⟩ => ?_
  have ev := cu.env.store hv hg hf hr hw
  have hch : v.v .v31 ^^^ v.v .v30=chain s₀ (k+1) := by
    rw [hv,fu.v _ (by decide),fu.v _ (by decide),chain_succ]
    exact value_pack hval
  have hn' : k+1 < N s₀ → v.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ v.v .v7 := by
    rw [hv,fu.v _ (by decide),fu.v _ (by decide)]
    exact hn
  have pv := (congrFun hg .x2).trans cu.ptr
  have cv := (congrFun hg .x3).trans cu.count
  rw [WP.block_cons_iff]
  refine ⟨_,exec_addImm_x (imm:=16) (by decide),WP.block_nil ?_⟩
  refine ⟨by omega_using [hk],ev.transfer (fun _ _ => rfl) (gpr_write_of_ne _ _ _ (by decide)) (gpr_write_of_ne _ _ _ (by decide))
    (gpr_write_of_ne _ _ _ (by decide)) rfl rfl rfl,
    ?_,?_,hch,by change EcbInv s₀.mem v.mem (Dp s₀) (N s₀) (k+1) (output s₀); exact hd,hn'⟩
  · simp only [State.write,State.read,BitVec.setWidth_eq,ite_true,pv]
    change (Dp s₀+BitVec.ofNat 64 (16*k))+BitVec.ofNat 64 16=Dp s₀+BitVec.ofNat 64 (16*(k+1))
    exact Offset.add_add_eq (Dp s₀) (by omega_using [])
  · exact (gpr_write_of_ne _ _ _ (by decide : Reg.x3≠.x2)).trans cv
end VG.Proof.AesCbc.AArch64.Encrypt

end

end


/-! One pipelined block, including its guarded lookahead and in-place store. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem step_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k < N s₀) (h : Inv s₀ k s) :
    WP isa (Impl.AesCbc.AArch64.Encrypt.step (R s₀)) s (Inv s₀ (k+1)) := by
  rw [Impl.AesCbc.AArch64.Encrypt.step]
  refine WP.seq (WP.mono (first4_ok hp hk h) fun a ⟨ca,ra⟩ => ?_)
  refine WP.seq (WP.mono (prefetch_ok hp (by omega_using [hk]) ca) fun b ⟨cb,fb,nb⟩ => ?_)
  have rb : RInv chainRegs (wK s₀) (fun _ => st (input s₀ k)) 5 b := by
    intro r hr
    have hr' : r=.v31 := List.mem_singleton.mp hr
    subst hr'
    rw [fb.v _ (by decide)]
    exact ra _ hr
  rw [WP.block_append_iff]
  have h6 : 6 ≤ R s₀ := by have := hp.rounds; omega_using [this]
  refine WP.mono (rounds_ok cb.env.keys rb (R s₀-6) (by omega_using [h6])) fun c ⟨rc,fc⟩ => ?_
  have cc := cb.vframe fc (by decide)
  have nc : k+1 < N s₀ → c.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ c.v .v7 := by
    rw [fc.v _ (by decide),fc.v _ (by decide)]
    exact nb
  rw [show 5+(R s₀-6)=R s₀-1 by omega_using [h6]] at rc
  rw [show Impl.AesCbc.AArch64.Encrypt.finish=
    [.vop (.aese .v31 .v29)]++[.vop (.logic .eor .v1 .v31 .v30),.strq .v1 .x2 0,.addImm .x .x2 .x2 16]
      from rfl,WP.block_append_iff]
  refine WP.mono (last_ok cc.env.keys rc) fun d ⟨rd,fd⟩ => ?_
  have cd := cc.vframe fd (by decide)
  refine store_advance_ok hp hk cd rd ?_
  rw [fd.v _ (by decide),fd.v _ (by decide)]
  exact nc
end VG.Proof.AesCbc.AArch64.Encrypt

end

end

/-! ### `AesCbc.AArch64.Encrypt.Setup`, which only this module used -/

section

/-! # Reusing the verified resident encryption-key setup -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Encrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

open VG.AArch64.RegUpd

def adapted (s : State) : State :=
  ((((s.write .x .x11 (s.gpr .x2)).write .x .x2 (s.gpr .x3)).write .x .x3 (s.gpr .x4)).write
    .x .x4 (s.gpr .x5)).setV .v31 (s.mem.readW (s.gpr .x2) 128)

theorem prefix_ok {s : State} (hp : UPre s) :
    WP isa (.block Impl.AesCbc.AArch64.Decrypt.adaptArgs) s (fun t => t = adapted s) := by
  rw [Impl.AesCbc.AArch64.Decrypt.adaptArgs]
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (d := .x11) (n := .x2) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (d := .x2) (n := .x3) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (d := .x3) (n := .x4) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 0) (d := .x4) (n := .x5) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (off := 0) (t := .v31) (n := .x11) (by decide) ?_, WP.block_nil ?_⟩
  · simp only [State.read, rd_write, wr_write, gpr_write, BitVec.setWidth_eq,
      reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
    exact ⟨ivR s, by rw [hp.rd, hp.wr]; simp, by simp [Region.Contains]⟩
  · simp only [State.read, adapted, gpr_write, mem_write, BitVec.setWidth_eq,
      reduceCtorEq, ite_true, ite_false, BitVec.add_zero]

/-- The key setup reads the schedule but changes neither data nor chaining value. -/
theorem keys_ok {s : State} (hp : BPre s) :
    WP isa (.block encSetup) s fun t =>
      Keys (bnr s) (bsch s) t ∧
      t.gpr .x13 = BitVec.ofNat 64 (bnb s / 8) ∧
      t.gpr .x2 = s.gpr .x2 ∧ t.gpr .x3 = s.gpr .x3 ∧
      t.gpr .x11 = s.gpr .x11 ∧ t.v .v31 = s.v .v31 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨tr,t,he,hi,h13⟩ := encSetup_ok hp
  have hm := Exec.storeFrame (ok := fun _ => false) (c := .block encSetup)
    (by decide +kernel) he
  have hg := Exec.gpr (r := .x11) (c := .block encSetup) (by decide +kernel) he
  have hv := Exec.vec (r := .v31) (c := .block encSetup) (by decide +kernel) he
  refine ⟨tr,t,he,hi.keys,h13,?_,?_,hg,hv,?_,hi.rd,hi.wr⟩
  · simpa using hi.x2
  · simpa using hi.x3
  · funext a
    exact hm.2 a (by simp [Unstored])

/-- The AES setup's smaller data/scratch permissions are sufficient under CBC's permissions. -/
theorem base_setup_ok {s : State} (hp : UPre s) :
    WP isa (.block (Impl.AesCbc.AArch64.Decrypt.adaptArgs ++ encSetup)) s fun t =>
      Keys (R s) (wK s) t ∧ t.gpr .x13 = BitVec.ofNat 64 (N s / 8) ∧
      t.gpr .x2 = Dp s ∧ t.gpr .x3 = s.gpr .x4 ∧ t.gpr .x11 = Iv s ∧
      t.v .v31 = s.mem.readW (Iv s) 128 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [WP.block_append_iff]
  refine WP.mono (prefix_ok hp) fun u hu => ?_
  subst hu
  let a := adapted s
  let u := a.withRegions [schR s] [dataR s, ⟨S s,2048⟩]
  have hg : ∀ r, u.gpr r = a.gpr r := fun _ => rfl
  have hp' : BPre u := by
    constructor
    · rfl
    · rfl
    · exact hp.sch_data
    · exact hp.data_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.data_wrap
    · exact hp.rounds
  obtain ⟨tr,t,he,hK,h13,h2,h3,h11,h31,hm,hrd,hwr⟩ := keys_ok hp'
  have hw : Covers u.wr a.wr := by
    intro p n ⟨r,hr,hc⟩
    change r ∈ [dataR s, ⟨S s,2048⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [show a.wr = s.wr from rfl, hp.wr]
    rcases hr with rfl | rfl
    · exact ⟨dataR s, by simp, hc⟩
    · exact ⟨scrR s, by simp, by simp only [Region.Contains] at *; omega_using [hc]⟩
  have hc : Covers (u.rd ++ u.wr) (a.rd ++ a.wr) :=
    Covers.append (Covers.of_mem (by
      intro r hr
      change r ∈ [schR s] at hr
      change r ∈ s.rd
      rw [hp.rd]; exact hr)) hw
  have he' := VG.AArch64.Exec.widen he hc hw
  simp only [u, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr,t.withRegions a.rd a.wr,he',?_,?_,?_,?_,?_,h31,hm,rfl,rfl⟩
  · have hk : Keys (R s) (wK s) t := by
      simpa only [bnr,bsch,bkp,u,a,adapted, State.withRegions_gpr,State.withRegions_mem,
        State.setV,gpr_write,mem_write,BitVec.setWidth_eq,reduceCtorEq,ite_false] using hK
    exact ⟨hk.rounds,hk.full,hk.k29,hk.k30,hk.x6,hk.x7⟩
  · exact h13
  · exact h2
  · exact h3
  · exact h11


def finishSetup (s : State) : State :=
  (s.setV .v7 (s.v .v16 ^^^ s.v .v30)).setV .v31 (s.v .v31 ^^^ s.v .v30)

theorem setup_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block Impl.AesCbc.AArch64.Encrypt.setup) s₀ fun t =>
      Env s₀ t ∧ t.gpr .x2=Dp s₀ ∧ t.gpr .x3=s₀.gpr .x4 ∧
      t.v .v31 ^^^ t.v .v30=chain s₀ 0 ∧ t.mem=s₀.mem := by
  rw [Impl.AesCbc.AArch64.Encrypt.setup,WP.block_append_iff]
  refine WP.mono (base_setup_ok hp) fun s ⟨hk,_,h2,h3,h11,h31,hm,hr,hw⟩ => ?_
  have he : runBlock isa [.vop (.logic .eor .v7 .v16 .v30),.vop (.logic .eor .v31 .v31 .v30)] s=
      some (finishSetup s) := by
    simp only [runBlock_cons,runStep_some,runBlock_nil,isa,exec,VOp.eval,Option.map_some,
      setV_v_of_ne _ _ (by decide : VReg.v31≠.v7),setV_v_of_ne _ _ (by decide : VReg.v30≠.v7)]
    rfl
  have hf : VFrame [.v7,.v31] s (finishSetup s) := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact (setV_v_of_ne _ _ hr.2).trans (setV_v_of_ne _ _ hr.1)
  refine WP.of_runBlock ⟨_,he,⟨?_,h2,h3,?_,hm⟩⟩
  · refine ⟨hk.of_frame hf ⟨by decide,by decide⟩,?_,h11,?_,hr,hw⟩
    · simp only [finishSetup,setV_v_self,setV_v_of_ne _ _ (by decide : VReg.v7≠.v31),
        setV_v_of_ne _ _ (by decide : VReg.v16≠.v31),setV_v_of_ne _ _ (by decide : VReg.v30≠.v31),
        setV_v_of_ne _ _ (by decide : VReg.v16≠.v7),setV_v_of_ne _ _ (by decide : VReg.v30≠.v7)]
    · change Frame [dataR s₀] s₀.mem s.mem
      rw [hm]; exact Frame.refl _ _
  · simp only [finishSetup,setV_v_self,setV_v_of_ne _ _ (by decide : VReg.v30≠.v31),
      setV_v_of_ne _ _ (by decide : VReg.v30≠.v7),BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero,h31]
    rfl

end VG.Proof.AesCbc.AArch64.Encrypt

end

end


/-! The public block counter terminates, including the empty message. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem nonzero_count {s : State} {n : Nat} (hn : n < 2^64) (hc : s.gpr .x3=BitVec.ofNat 64 n) :
    isa.eval (.nonzero .x .x3) s=some (!decide (n=0)) := by
  change some (s.read .x .x3 != 0)=_
  simp only [State.read,BitVec.setWidth_eq,hc,ofNat_ne_zero hn]

theorem loop_ok {s₀ s : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) (h : Inv s₀ k s) :
    WP isa (.loop (Impl.AesCbc.AArch64.Encrypt.step (R s₀)) (.nonzero .x .x3)) s (Inv s₀ (N s₀)) := by
  let I := fun j t => ∃ k,k+j=N s₀ ∧ k<N s₀ ∧ Inv s₀ k t
  refine WP.loop (M:=isa) I (fun j t ⟨k,hkj,hk,hi⟩ => ?_) (N s₀-k) s ⟨k,by omega_using [hk],hk,h⟩
  refine WP.mono (step_ok hp hk hi) fun u hu => ?_
  have he := nonzero_count (by have := hp.data_wrap; omega_using [this]) hu.count
  by_cases hend : k+1=N s₀
  · refine Or.inl ⟨?_,?_⟩
    · rw [he,hend,Nat.sub_self]; rfl
    · rw [hend] at hu; exact hu
  · refine Or.inr ⟨?_,N s₀-(k+1),by omega_using [hkj, hk],k+1,?_⟩
    · rw [he,decide_eq_false (by omega_using [hk, hend])]; rfl
    · exact ⟨by omega_using [hk],by omega_using [hk, hend],hu⟩

def middle (nr : Nat) : Prog isa :=
  .ite (.zero .x .x3) (.block [])
    (.seq (.block (Impl.AesCbc.AArch64.Encrypt.enter nr))
      (.loop (Impl.AesCbc.AArch64.Encrypt.step nr) (.nonzero .x .x3)))

theorem middle_ok {s₀ s : State} (hp : UPre s₀) (he : Env s₀ s)
    (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4)
    (hch : s.v .v31 ^^^ s.v .v30=chain s₀ 0) (hm : s.mem=s₀.mem) :
    WP isa (middle (R s₀)) s (Inv s₀ (N s₀)) := by
  have hev := zero_count (n:=N s₀) (by exact (s₀.gpr .x4).isLt) (h3.trans (x4_ofNat s₀))
  by_cases hn : N s₀=0
  · refine WP.ite true (by rw [hev,hn]; rfl) (fun _ => WP.block_nil ?_) (fun hf => by cases hf)
    rw [hn]
    refine ⟨by omega_using [],he,?_,?_,hch,?_,fun hc => by omega⟩
    · simpa only [blk,Nat.mul_zero,BitVec.add_zero,hn] using h2
    · rw [h3,x4_ofNat,hn]
    · intro i hi; rw [hm]; rfl
  · refine WP.ite false (by rw [hev,decide_eq_false hn]) (fun hf => by cases hf) (fun _ => ?_)
    exact WP.seq (WP.mono (entry_ok hp (by omega_using [hn]) he h2 h3 hch hm)
      fun t ht => loop_ok hp (by omega_using [hn]) ht)
end VG.Proof.AesCbc.AArch64.Encrypt

end

end

/-! ### `AesCbc.AArch64.Encrypt.Result`, which only this module used -/

section

/-! Final indexed memory agrees with all ciphertext blocks of CBC. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem data_done {s₀ : State} {m : Mem}
    (hI : EcbInv s₀.mem m (Dp s₀) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m (Dp s₀) (N s₀)=
      Spec.Cbc.encrypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  have hs := statesAt_of_ecbInv hI
  have he : Spec.Cbc.blocksAt m (Dp s₀) (N s₀)=
      (Spec.Aes.statesAt m (Dp s₀) (N s₀)).map Vector.toList := by
    simp only [Spec.Cbc.blocksAt,Spec.Aes.statesAt,List.map_map,Function.comp_def]
    exact List.map_congr_left fun _ _ => bytesAt_toList _ _
  rw [he,hs,List.map_map]
  have hp := (chain_blocks s₀ (N s₀) (Nat.le_refl _)).1
  rw [outK,List.take_of_length_le (by rw [length_blocksAt])] at hp
  exact hp.symm
end VG.Proof.AesCbc.AArch64.Encrypt

end

end


/-! CBC encryption correctness and the complete memory frame. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem finish_iv {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) s) :
    WP isa (.block [.vop (.logic .eor .v31 .v31 .v30),.strq .v31 .x11 0]) s fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  rw [WP.block_cons_iff]
  let u := s.setV .v31 (s.v .v31 ^^^ s.v .v30)
  have he : exec (.vop (.logic .eor .v31 .v31 .v30)) s=some u := rfl
  refine ⟨_,he,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_strq (off:=0) (t:=.v31) (n:=.x11) (by decide) (by
    change InRegions s.wr (s.gpr .x11+BitVec.ofNat 64 0) 16
    rw [hI.env.iv,BitVec.add_zero,hI.env.wr,hp.wr]
    exact ⟨ivR s₀,by simp,Region.contains_self _ _⟩),WP.block_nil ?_⟩
  have hptr : u.gpr .x11=Iv s₀ := hI.env.iv
  have hv : u.v .v31=chain s₀ (N s₀) := hI.chain
  simp only [hptr,BitVec.add_zero]
  have hf : Frame [ivR s₀] s.mem (s.mem.write (Iv s₀) 16 (u.v .v31)) :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd := ecbInv_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp.iv_data.symm) (Decrypt.data_size hp) hI.data
  have hi : Spec.Aes.bytesAt (s.mem.write (Iv s₀) 16 (u.v .v31)) (Iv s₀) 16=
      Spec.Cbc.next (iv0 s₀)
        (Spec.Cbc.encrypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)) := by
    rw [bytesAt_toList,←st_readW]
    have hm : (s.mem.write (Iv s₀) 16 (u.v .v31)).readW (Iv s₀) 128=u.v .v31 :=
      Mem.readW_writeW_self s.mem (Iv s₀) 16 (u.v .v31) (by decide)
    rw [hm,hv,←(chain_blocks s₀ (N s₀) (Nat.le_refl _)).2]
    change Spec.Cbc.next _ (outK (cbcMode true) s₀ (N s₀))=_
    rw [outK,List.take_of_length_le (by rw [length_blocksAt])]
    rfl
  exact ⟨⟨data_done hd,hi⟩,(hI.env.frame.mono (by regions_sub)).trans (hf.mono (by regions_sub))⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (Impl.AesCbc.AArch64.Encrypt.body (R s₀)) s₀ fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  rw [Impl.AesCbc.AArch64.Encrypt.body]
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨he,h2,h3,hch,hm⟩ => ?_)
  exact WP.seq (WP.mono (middle_ok hp he h2 h3 hch hm) fun _ hi => finish_iv hp hi)

theorem code_ok {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.AesCbc.AArch64.Encrypt.code s₀ fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCbc.AArch64.Encrypt.code
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 10) (by decide),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 12) (by decide),WP.block_nil ?_⟩
  let s := (s₀.write .x .x9 (s₀.gpr .x1-10)).write .x .x10 (s₀.gpr .x1-12)
  have hs : UPre s := ⟨hp.rd,hp.wr,hp.sch_iv,hp.sch_data,hp.sch_scr,
    hp.iv_data,hp.iv_scr,hp.data_scr,hp.iv_wrap,hp.data_wrap,hp.scr_wrap,hp.rounds⟩
  have hR : R s=R s₀ := rfl
  have hpost : ∀ t, (cbcAArch64 true).post s t=(cbcAArch64 true).post s₀ t := fun _ => rfl
  have hb : WP isa (Impl.AesCbc.AArch64.Encrypt.body (R s₀)) s (fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem) := by
    have h := body_ok hs
    rw [hR] at h
    exact WP.mono h fun t ht => by rw [hpost t] at ht; exact ht
  have hx9 : s.gpr .x9 = BitVec.ofNat 64 (R s₀)-10 := by simp [s,State.write,R]
  have hx10 : s.gpr .x10 = BitVec.ofNat 64 (R s₀)-12 := by simp [s,State.write,R]
  change WP isa (.ite (.zero .x .x9) _ _) s _
  obtain hr | hr | hr := hp.rounds
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => by cases h)
    · simp [eval,State.read,hx9,hr] <;> decide +kernel
    · simpa only [hr] using hb
  · refine WP.ite false ?_ (fun h => by cases h) (fun _ => ?_)
    · simp [eval,State.read,hx9,hr] <;> decide +kernel
    · refine WP.ite true ?_ (fun _ => ?_) (fun h => by cases h)
      · simp [eval,State.read,hx10,hr] <;> decide +kernel
      · simpa only [hr] using hb
  · refine WP.ite false ?_ (fun h => by cases h) (fun _ => ?_)
    · simp [eval,State.read,hx9,hr] <;> decide +kernel
    · refine WP.ite false ?_ (fun h => by cases h) (fun _ => ?_)
      · simp [eval,State.read,hx10,hr] <;> decide +kernel
      · simpa only [hr] using hb

end VG.Proof.AesCbc.AArch64.Encrypt

end

end


/-! # The existing CBC contract, ABI, constant time, and scratch-write bound -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Encrypt

open VG VG.AArch64
open VG.Impl.AesCbc.AArch64.Encrypt (code)

theorem correct (s : State) (hp : (cbcAArch64 true).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (cbcAArch64 true).post s t := by
  have hk := instrs_keeps (c := code) (rs := preserved) (by lit_decide)
  have hg : code.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
    rwa [Code.allInstrs_eq]
  obtain ⟨tr,t,he,hq,hg⟩ := WP.gprs (rs := preserved) (code_ok (UPre.of hp)) hg (by lit_decide)
  exact ⟨tr,t,he,⟨hg,Exec.sp he,Exec.preservedV he (by lit_decide)⟩,hq.1⟩

theorem ct : ConstantTime isa (cbcAArch64 true).pre (cbcAArch64 true).pub code := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0,h1,h2,h3,h4,h5,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (cbcAArch64 true).Implies (Proof.AesCbc.encryptRoundsContract AArch64.abi) := by
  sig_implies [Proof.AesCbc.encryptRoundsContract,Spec.Cbc.aesSig,cbcAArch64,modeAArch64,cbcMode,
    ciphOf,cbc,cts,AArch64.abi,AArch64.argRegs] [sat] using sat

theorem verified : Verified AArch64.target code (Proof.AesCbc.encryptRoundsContract AArch64.abi) :=
  Verified.of_correct correct ct implies

/-- This path never writes scratch; no scratch bytes require clearing afterwards. -/
theorem written (s : State) (tr : List Leak) (t : State)
    (hp : (Proof.AesCbc.encryptRoundsContract AArch64.abi).pre s) (he : Exec isa code s tr t) :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cbc.aesSig [("scratch",0)] s t := by
  have h := UPre.of (implies.pre s hp)
  obtain ⟨tr',t',he',_,hf⟩ := code_ok h
  obtain ⟨_,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,AArch64.abi,AArch64.argRegs,Abi.withConsts,Spec.Cbc.aesSig,
    Sig.words,Sig.arrays,Param.words,ArgWord.bits]
  intro i hi
  apply hf
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  have hi' : i < 2176 := by simpa [Elem.size] using hi
  have hc : (scrR s).Contains (S s+BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi']) (by omega_using [hi'])
  rcases hr with rfl | rfl
  · exact fun hi => h.iv_scr _ hi hc
  · exact fun hi => h.data_scr _ hi hc

end VG.Proof.AesCbc.AArch64.Encrypt
