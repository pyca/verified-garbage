module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Group
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.AesCcm.AArch64.Header
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit

/-! ### `AesCbc.AArch64.Decrypt.Loops`, which only this module used -/

section

/-! # The seven-block loop and the remaining-block loop -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

def advance (d : Nat) : List Instr :=
  [.addImm .x .x2 .x2 (16*d), .subImm .x .x3 .x3 d]

theorem advance_ok {s₀ s : State} {c d : Nat} (hd : d < 256) (hc : c+d ≤ N s₀)
    (hI : Inv s₀ (c+d) c s) :
    WP isa (.block (advance d)) s fun t => Inv s₀ (c+d) (c+d) t ∧ t.gpr .x13 = s.gpr .x13 := by
  rw [advance,WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16*d) (by omega_using [hd]), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := d) (by omega_using [hd]), WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_,?_,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,rfl⟩
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x2]
    exact Offset.add_add_eq _ (by omega_using [])
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), show N s₀-c-d=N s₀-(c+d) by omega_using []]

theorem flag_bound (m : Nat) : (if m<7 then 1 else 0) < 2^64 := by
  split <;> decide

theorem check_ok {s₀ s : State} (hp : UPre s₀) {c p : Nat} (hI : Inv s₀ c p s) :
    WP isa (.block Impl.AesCbc.AArch64.Decrypt.checkEnough) s fun t =>
      Inv s₀ c p t ∧ t.gpr .x13=BitVec.ofNat 64 (if N s₀-p<7 then 1 else 0) := by
  rw [Impl.AesCbc.AArch64.Decrypt.checkEnough,WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 7) (by decide),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_lsr_x (sh := 63) (by decide),WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    hI.x2,hI.x3,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,?_⟩
  simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hI.x3]
  exact Proof.AesCcm.AArch64.sign63 (by have := hp.data_wrap; omega_using [this]) (by decide)

theorem eval_short {s : State} {m : Nat}
    (h : s.gpr .x13=BitVec.ofNat 64 (if m<7 then 1 else 0)) :
    AArch64.eval (.nonzero .x .x13) s=some (decide (m<7)) := by
  rw [eval_nonzero h (flag_bound m)]
  by_cases hm : m<7 <;> simp [hm]

theorem batch_ok (sha3 : Bool) {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+7 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.batch sha3 (R s₀)) s fun t =>
      Inv s₀ (c+7) (c+7) t ∧
        t.gpr .x13=BitVec.ofNat 64 (if N s₀-(c+7)<7 then 1 else 0) := by
  unfold Impl.AesCbc.AArch64.Decrypt.batch
  rw [List.append_assoc]
  refine group_ok sha3 hp Impl.AesCbc.AArch64.Decrypt.regs7 (.inl rfl) hc hI _ fun u hi _ => ?_
  change WP isa (.block (advance 7 ++ Impl.AesCbc.AArch64.Decrypt.checkEnough)) u _
  rw [WP.block_append_iff]
  exact WP.mono (advance_ok (by decide) hc hi) fun _ ⟨hi',_⟩ => check_ok hp hi'

theorem tail_ok (sha3 : Bool) {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+1 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.tail sha3 (R s₀)) s (Inv s₀ (c+1) (c+1)) := by
  unfold Impl.AesCbc.AArch64.Decrypt.tail
  rw [show Impl.AesCbc.AArch64.Decrypt.finish sha3 .v0 0 =
    Impl.AesCbc.AArch64.Decrypt.finishData sha3 [.v0] 0 by
      simp only [Impl.AesCbc.AArch64.Decrypt.finishData, List.append_nil]]
  change WP isa (.seq (.block (ldData [.v0] 0))
    (.seq (Impl.AesCbc.AArch64.Decrypt.rounds (R s₀) [.v0])
      (.block (Impl.AesCbc.AArch64.Decrypt.finishData sha3 [.v0] 0 ++ advance 1)))) s _
  exact group_ok sha3 hp [.v0] (.inr rfl) hc hI _ fun _ hi _ =>
    WP.mono (advance_ok (by decide) hc hi) fun _ hi' => hi'.1

abbrev loops (sha3 : Bool) := Impl.AesCbc.AArch64.Decrypt.loops sha3

theorem loops_ok (sha3 : Bool) {s₀ s₁ : State} (hp : UPre s₀) (hI₀ : Inv s₀ 0 0 s₁) :
    WP isa (loops sha3 (R s₀)) s₁ (Inv s₀ (N s₀) (N s₀)) := by
  have hn : N s₀ < 2^64 := (s₀.gpr .x4).isLt
  unfold loops Impl.AesCbc.AArch64.Decrypt.loops
  refine WP.seq (WP.mono (check_ok hp hI₀) fun s₁ ⟨hI₁,h13⟩ => ?_)
  simp only [Nat.sub_zero] at h13
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀-c < 7 ∧ Inv s₀ c c s) ?_
    fun s₂ ⟨c,hc,hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀<7)) (eval_short h13) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0,by simp at h; omega_using [h],hI₁⟩
    · refine WP.seq ?_
      rw [WP.block_cons_iff]
      refine ⟨_,rfl,WP.block_nil ?_⟩
      let I7 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c+7≤N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I7 m s → WP isa (Impl.AesCbc.AArch64.Decrypt.batch sha3 (R s₀)) s
          (fun t => (AArch64.eval (.zero .x .x13) t=some false ∧
            ∃ c, N s₀-c<7 ∧ Inv s₀ c c t) ∨
          (AArch64.eval (.zero .x .x13) t=some true ∧ ∃ m'<m,I7 m' t)) := by
        rintro m s ⟨c,rfl,hc,hi⟩
        refine WP.mono (batch_ok sha3 hp hc hi) fun t ⟨hi',h13'⟩ => ?_
        rw [eval_zero h13' (flag_bound _)]
        by_cases hlt : N s₀-(c+7)<7
        · exact .inl ⟨by simp [hlt],c+7,hlt,hi'⟩
        · exact .inr ⟨by simp [hlt],N s₀-(c+7),by omega_using [hc],c+7,rfl,by omega_using [hlt],hi'⟩
      exact WP.loop (M := isa) I7 hstep (N s₀) s₁ ⟨0,rfl,by simp at h; omega_using [h],hI₁⟩
  refine WP.ite (decide (N s₀-c=0)) (eval_zero hI₂.x3 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · have he : c=N s₀ := by have := hI₂.le; simp at h; omega_using [this, h]
    exact WP.block_nil (he ▸ hI₂)
  · refine WP.seq ?_
    rw [WP.block_cons_iff]
    refine ⟨_,rfl,WP.block_nil ?_⟩
    let I1 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c<N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (Impl.AesCbc.AArch64.Decrypt.tail sha3 (R s₀)) s
        (fun t => (AArch64.eval (.nonzero .x .x3) t=some false ∧ Inv s₀ (N s₀) (N s₀) t) ∨
          (AArch64.eval (.nonzero .x .x3) t=some true ∧ ∃ m'<m,I1 m' t)) := by
      rintro m s ⟨c,rfl,hc,hi⟩
      refine WP.mono (tail_ok sha3 hp (by omega_using [hc]) hi) fun t hi' => ?_
      rw [eval_nonzero hi'.x3 (by omega_using [hn])]
      by_cases hlast : N s₀-(c+1)=0
      · have he : c+1=N s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [hlast],he ▸ hi'⟩
      · exact .inr ⟨by simp [hlast],N s₀-(c+1),by omega_using [hc],c+1,rfl,by omega_using [hlast],hi'⟩
    exact WP.loop (M := isa) I1 hstep (N s₀-c) s₂
      ⟨c,rfl,by have := hI₂.le; simp at h; omega_using [h],hI₂⟩

end VG.Proof.AesCbc.AArch64.Decrypt

end

end

/-! ### `AesCbc.AArch64.Decrypt.Setup`, which only this module used -/

section

/-! # Reusing the existing verified inverse-key setup for CBC -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

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
    WP isa (.block decSetup) s fun t =>
      DKeys (bnr s) (bsch s) t ∧
      t.gpr .x13 = BitVec.ofNat 64 (bnb s / 8) ∧
      t.gpr .x2 = s.gpr .x2 ∧ t.gpr .x3 = s.gpr .x3 ∧
      t.gpr .x11 = s.gpr .x11 ∧ t.v .v31 = s.v .v31 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨tr,t,he,hi,h13⟩ := decSetup_ok hp
  have hm := Exec.storeFrame (ok := fun _ => false) (c := .block decSetup)
    (by decide +kernel) he
  have hg := Exec.gpr (r := .x11) (c := .block decSetup) (by decide +kernel) he
  have hv := Exec.vec (r := .v31) (c := .block decSetup) (by decide +kernel) he
  refine ⟨tr,t,he,hi.keys,h13,?_,?_,hg,hv,?_,hi.rd,hi.wr⟩
  · simpa using hi.x2
  · simpa using hi.x3
  · funext a
    exact hm.2 a (by simp [Unstored])

/-- The AES setup's smaller data/scratch permissions are sufficient under CBC's permissions. -/
theorem setup_ok {s : State} (hp : UPre s) :
    WP isa (.block (Impl.AesCbc.AArch64.Decrypt.adaptArgs ++ decSetup)) s fun t =>
      DKeys (R s) (wK s) t ∧ t.gpr .x13 = BitVec.ofNat 64 (N s / 8) ∧
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
  · have hk : DKeys (R s) (wK s) t := by
      simpa only [bnr,bsch,bkp,u,a,adapted, State.withRegions_gpr,State.withRegions_mem,
        State.setV,gpr_write,mem_write,BitVec.setWidth_eq,reduceCtorEq,ite_false] using hK
    exact ⟨hk.rounds,hk.last,hk.mid,hk.k0,hk.x6,hk.x7⟩
  · exact h13
  · exact h2
  · exact h3
  · exact h11

end VG.Proof.AesCbc.AArch64.Decrypt

end

end


/-! # CBC decryption, including the unchanged scratch buffer -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem data_size {s₀ : State} (hp : UPre s₀) : 16*N s₀ < 2^64 := by
  refine Nat.lt_of_not_le fun hc => hp.data_scr (S s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (S s₀-Dp s₀).isLt
  omega_using [hc]

theorem initial {s₀ s : State} (hK : DKeys (R s₀) (wK s₀) s)
    (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4) (h11 : s.gpr .x11=Iv s₀)
    (h31 : s.v .v31=s₀.mem.readW (Iv s₀) 128) (hm : s.mem=s₀.mem)
    (hrd : s.rd=s₀.rd) (hwr : s.wr=s₀.wr) : Inv s₀ 0 0 s := by
  refine ⟨Nat.zero_le _,hK,by simpa [blk] using h2,by simpa using h3,h11,h31,?_,?_,hrd,hwr⟩
  · intro i _; simp [hm]
  · rw [hm]; exact Frame.refl _ _

theorem finish_iv {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) (N s₀) s) :
    WP isa (.block [.strq .v31 .x11 0]) s fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_,exec_strq (off := 0) (t := .v31) (n := .x11) (by decide) (by
    rw [hI.x11,BitVec.add_zero,hI.wr,hp.wr]
    exact ⟨ivR s₀,by simp,Region.contains_self _ _⟩),WP.block_nil ?_⟩
  simp only [hI.x11,BitVec.add_zero]
  have hf : Frame [ivR s₀] s.mem (s.mem.write (Iv s₀) 16 (s.v .v31)) :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd := ecbInv_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.symm) (data_size hp) hI.data
  have hi : Spec.Aes.bytesAt (s.mem.write (Iv s₀) 16 (s.v .v31)) (Iv s₀) 16 =
      Spec.Cbc.next (iv0 s₀) (blks s₀) := by
    rw [bytesAt_toList,← st_readW]
    have hm : (s.mem.write (Iv s₀) 16 (s.v .v31)).readW (Iv s₀) 128 = s.v .v31 :=
      Mem.readW_writeW_self s.mem (Iv s₀) 16 (s.v .v31) (by decide)
    rw [hm,hI.chain,chaining_bytes _ _ (Nat.le_refl _),List.take_of_length_le (by rw [length_blocksAt])]
  exact ⟨⟨data_done hd,hi⟩,(hI.frame.mono (by regions_sub)).trans (hf.mono (by regions_sub))⟩

theorem body_ok (sha3 : Bool) {s₀ : State} (hp : UPre s₀) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.body sha3 (R s₀)) s₀ fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCbc.AArch64.Decrypt.body
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨hK,_,h2,h3,h11,h31,hm,hrd,hwr⟩ => ?_)
  have hi := initial hK h2 h3 h11 h31 hm hrd hwr
  exact WP.seq (WP.mono (loops_ok sha3 hp hi) fun _ hI => finish_iv hp hI)

theorem code_ok (sha3 : Bool) {s₀ : State} (hp : UPre s₀) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.codeWith sha3) s₀ fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCbc.AArch64.Decrypt.codeWith
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 10) (by decide),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 12) (by decide),WP.block_nil ?_⟩
  let s := (s₀.write .x .x9 (s₀.gpr .x1-10)).write .x .x10 (s₀.gpr .x1-12)
  have hs : UPre s := ⟨hp.rd,hp.wr,hp.sch_iv,hp.sch_data,hp.sch_scr,
    hp.iv_data,hp.iv_scr,hp.data_scr,hp.iv_wrap,hp.data_wrap,hp.scr_wrap,hp.rounds⟩
  have hR : R s=R s₀ := rfl
  have hpost : ∀ t, (cbcAArch64 false).post s t=(cbcAArch64 false).post s₀ t := fun _ => rfl
  have hb : WP isa (Impl.AesCbc.AArch64.Decrypt.body sha3 (R s₀)) s (fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem) := by
    have h := body_ok sha3 hs
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

end VG.Proof.AesCbc.AArch64.Decrypt
