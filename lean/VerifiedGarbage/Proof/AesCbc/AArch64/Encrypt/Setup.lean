module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.State

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit

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
    · exact ⟨scrR s, by simp, by simp only [Region.Contains] at *; omega⟩
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
