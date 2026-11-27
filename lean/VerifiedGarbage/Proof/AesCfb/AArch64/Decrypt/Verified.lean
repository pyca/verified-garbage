module

public import VerifiedGarbage.Proof.AesCfb.Rounds
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Group
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.AesCcm.AArch64.Header
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCbc.Decrypt
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Lit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Spec.Cfb.Contract

/-! ### `AesCfb.AArch64.Decrypt.Correct`, which only this module used -/

section

/-! ### `AesCfb.AArch64.Decrypt.Loops`, which only this module used -/

section

/-! # The eight-block loop and the remaining-block loop -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

abbrev advance := Impl.AesCfb.AArch64.Decrypt.advance

theorem advance_ok {s₀ s : State} {c d : Nat} (hd : d < 256) (hc : c+d ≤ N s₀)
    (hI : Inv s₀ (c+d) c s) :
    WP isa (.block (advance d)) s fun t => Inv s₀ (c+d) (c+d) t ∧ t.gpr .x13 = s.gpr .x13 := by
  rw [advance,Impl.AesCfb.AArch64.Decrypt.advance,WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16*d) (by omega_using [hd]), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := d) (by omega_using [hd]), WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_,?_,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,rfl⟩
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x2]
    exact Offset.add_add_eq _ (by omega_using [])
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), show N s₀-c-d=N s₀-(c+d) by omega_using []]

theorem flag_bound (d m : Nat) : (if m<d then 1 else 0) < 2^64 := by
  split <;> decide

theorem check_ok {s₀ s : State} (hp : UPre s₀) {c p : Nat} (hI : Inv s₀ c p s) (d : Nat) (hd : d < 256) :
    WP isa (.block (Impl.AesCfb.AArch64.Decrypt.checkEnough d)) s fun t =>
      Inv s₀ c p t ∧ t.gpr .x13=BitVec.ofNat 64 (if N s₀-p<d then 1 else 0) := by
  rw [Impl.AesCfb.AArch64.Decrypt.checkEnough,WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := d) (by omega_using [hd]),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_lsr_x (sh := 63) (by decide),WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    hI.x2,hI.x3,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,?_⟩
  simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hI.x3]
  exact Proof.AesCcm.AArch64.sign63 (by have := hp.data_wrap; omega_using [this]) (by omega_using [hd])

theorem eval_short {s : State} {d m : Nat}
    (h : s.gpr .x13=BitVec.ofNat 64 (if m<d then 1 else 0)) :
    AArch64.eval (.nonzero .x .x13) s=some (decide (m<d)) := by
  rw [eval_nonzero h (flag_bound d m)]
  by_cases hm : m<d <;> simp [hm]

theorem group_advance_ok {s₀ s : State} (hp : UPre s₀) (b : VReg) (bs : List VReg)
    (hbr : BlockRegs (b::bs)) (h31 : .v31 ∉ b::bs) (hlen : (b::bs).length ≤ 8)
    {c : Nat} (hc : c+(b::bs).length ≤ N s₀) (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCfb.AArch64.Decrypt.group (b::bs)) s
      (Inv s₀ (c+(b::bs).length) (c+(b::bs).length)) := by
  exact group_ok hp b bs hbr h31 hlen hc hI _ fun _ hi _ =>
    WP.mono (advance_ok (by omega_using [hlen]) hc hi) fun _ hi' => hi'.1

theorem batch_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+8 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa Impl.AesCfb.AArch64.Decrypt.batch s fun t =>
      Inv s₀ (c+8) (c+8) t ∧
        t.gpr .x13=BitVec.ofNat 64 (if N s₀-(c+8)<8 then 1 else 0) := by
  unfold Impl.AesCfb.AArch64.Decrypt.batch
  exact WP.seq (WP.mono (group_advance_ok hp .v0 [.v1,.v2,.v3,.v4,.v5,.v6,.v7]
    ⟨by decide,by decide⟩ (by decide) (by decide) hc hI) fun _ hi => check_ok hp hi 8 (by decide))

theorem tail_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+1 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCfb.AArch64.Decrypt.group [.v0]) s (Inv s₀ (c+1) (c+1)) :=
  group_advance_ok hp .v0 [] ⟨by decide,by decide⟩ (by decide) (by decide) hc hI

abbrev loops := Impl.AesCfb.AArch64.Decrypt.loops

theorem loops_ok {s₀ s₁ : State} (hp : UPre s₀) (hI₀ : Inv s₀ 0 0 s₁) :
    WP isa (loops) s₁ (Inv s₀ (N s₀) (N s₀)) := by
  have hn : N s₀ < 2^64 := (s₀.gpr .x4).isLt
  unfold loops Impl.AesCfb.AArch64.Decrypt.loops
  refine WP.seq (WP.mono (check_ok hp hI₀ 8 (by decide)) fun s₁ ⟨hI₁,h13⟩ => ?_)
  simp only [Nat.sub_zero] at h13
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀-c < 8 ∧ Inv s₀ c c s) ?_
    fun s₂ ⟨c,hc,hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀<8)) (eval_short h13) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0,by simp at h; omega_using [h],hI₁⟩
    · refine WP.seq ?_
      rw [WP.block_cons_iff]
      refine ⟨_,rfl,WP.block_nil ?_⟩
      let I8 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c+8≤N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (Impl.AesCfb.AArch64.Decrypt.batch) s
          (fun t => (AArch64.eval (.zero .x .x13) t=some false ∧
            ∃ c, N s₀-c<8 ∧ Inv s₀ c c t) ∨
          (AArch64.eval (.zero .x .x13) t=some true ∧ ∃ m'<m,I8 m' t)) := by
        rintro m s ⟨c,rfl,hc,hi⟩
        refine WP.mono (batch_ok hp hc hi) fun t ⟨hi',h13'⟩ => ?_
        rw [eval_zero h13' (flag_bound 8 _)]
        by_cases hlt : N s₀-(c+8)<8
        · exact .inl ⟨by simp [hlt],c+8,hlt,hi'⟩
        · exact .inr ⟨by simp [hlt],N s₀-(c+8),by omega_using [hc],c+8,rfl,by omega_using [hlt],hi'⟩
      exact WP.loop (M := isa) I8 hstep (N s₀) s₁ ⟨0,rfl,by simp at h; omega_using [h],hI₁⟩
  refine WP.seq (WP.mono (check_ok hp hI₂ 4 (by decide)) fun s₃ ⟨hi₃,h4⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun t => ∃ c, Inv s₀ c c t) ?_
    fun s₂ ⟨c,hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀-c<4)) (eval_short h4) (fun _ => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c,hi₃⟩
    · exact WP.mono (group_advance_ok hp .v0 [.v1,.v2,.v3] ⟨by decide,by decide⟩
        (by decide) (by decide) (by simp only [List.length_cons,List.length_nil]; simp at h; have := hi₃.le; omega_using [h]) hi₃) fun _ hi => ⟨c+4,hi⟩
  refine WP.ite (decide (N s₀-c=0)) (eval_zero hI₂.x3 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · have he : c=N s₀ := by have := hI₂.le; simp at h; omega_using [this, h]
    exact WP.block_nil (he ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c<N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (Impl.AesCfb.AArch64.Decrypt.group [.v0]) s
        (fun t => (AArch64.eval (.nonzero .x .x3) t=some false ∧ Inv s₀ (N s₀) (N s₀) t) ∨
          (AArch64.eval (.nonzero .x .x3) t=some true ∧ ∃ m'<m,I1 m' t)) := by
      rintro m s ⟨c,rfl,hc,hi⟩
      refine WP.mono (tail_ok hp (by omega_using [hc]) hi) fun t hi' => ?_
      rw [eval_nonzero hi'.x3 (by omega_using [hn])]
      by_cases hlast : N s₀-(c+1)=0
      · have he : c+1=N s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [hlast],he ▸ hi'⟩
      · exact .inr ⟨by simp [hlast],N s₀-(c+1),by omega_using [hc],c+1,rfl,by omega_using [hlast],hi'⟩
    exact WP.loop (M := isa) I1 hstep (N s₀-c) s₂
      ⟨c,rfl,by have := hI₂.le; simp at h; omega_using [h],hI₂⟩

end VG.Proof.AesCfb.AArch64.Decrypt

end

end

/-! ### `AesCfb.AArch64.Decrypt.Result`, which only this module used -/

section

/-! # The indexed register invariant is CBC decryption -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem decrypt_getD (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte))
    (k : Nat) (hk : k < xs.length) :
    (Spec.Cfb.decrypt ciph iv xs).getD k [] =
      Spec.Cbc.xor (xs.getD k []) (ciph (Spec.Cbc.next iv (xs.take k))) := by
  induction xs generalizing iv k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [Spec.Cfb.decrypt, List.getD_cons_succ, List.take_succ_cons, next_cons] using
        ih x k (by simpa using hk)

theorem list_getD {α : Type} {xs : List α} {k : Nat} {d : α} (hk : k < xs.length) :
    xs.getD k d = xs[k] := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]

theorem vector_listD (v : Spec.Aes.State) (i : Nat) (hi : i < 16) :
    v.toList.getD i 0 = v.getD i 0 := by
  rw [list_getD (by simpa using hi),Vector.getElem_toList]
  simp [Vector.getD,hi]

theorem chaining_bytes (s₀ : State) (k : Nat) (hk : k ≤ N s₀) :
    (st (chaining s₀ k)).toList = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
  cases k with
  | zero => simp only [chaining,st_readW,List.take_zero]; exact (bytesAt_toList _ _).symm
  | succ k =>
    rw [next_take_succ _ _ k (by rw [length_blocksAt]; omega_using [hk]),
      list_getD (by rw [length_blocksAt]; omega_using [hk]),getElem_blocksAt (hk := by omega_using [hk])]
    exact (congrArg Vector.toList (st_readW _ _)).trans (bytesAt_toList _ _).symm

theorem aesWith_st (nr : Nat) (w : List Byte) (v : BitVec 128) :
    Spec.Cbc.aesWith nr w (st v).toList = (Spec.Aes.cipher nr w (st v)).toList := by
  rw [Spec.Cbc.aesWith]
  apply congrArg Vector.toList
  apply congrArg (Spec.Aes.cipher nr w)
  apply st_ext
  intro i hi
  rw [getD_ofFn hi,vector_listD _ _ hi]

theorem block_bytes (s₀ : State) (k : Nat) (hk : k < N s₀) :
    (output s₀ k).toList =
      (Spec.Cfb.decrypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)).getD k [] := by
  rw [decrypt_getD _ _ _ k (by rw [length_blocksAt]; exact hk),
    list_getD (by rw [length_blocksAt]; exact hk),getElem_blocksAt (hk := hk),
    ← chaining_bytes _ _ (Nat.le_of_lt hk), aesWith_st, bytesAt_toList]
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [vector_listD _ _ hi]
  rw [xor_eq,Proof.Cmac.getD_xor (by simp) (by simpa using hi)]
  rw [vector_listD _ _ hi,vector_listD _ _ hi]
  rw [← st_readW, getD_st _ hi]
  rw [output,getD_ofFn hi]
  exact BitVec.xor_comm _ _

theorem data_done {s₀ : State} {m : Mem}
    (hI : EcbInv s₀.mem m (Dp s₀) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m (Dp s₀) (N s₀) =
      Spec.Cfb.decrypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  have hs := statesAt_of_ecbInv hI
  have he : Spec.Cbc.blocksAt m (Dp s₀) (N s₀) =
      ((Spec.Aes.statesAt m (Dp s₀) (N s₀)).map Vector.toList) := by
    simp only [Spec.Cbc.blocksAt,Spec.Aes.statesAt,List.map_map,Function.comp_def]
    exact List.map_congr_left fun _ _ => bytesAt_toList _ _
  rw [he,hs,List.map_map]
  apply List.ext_getElem
  · simp [length_decrypt,length_blocksAt]
  · intro k hk _
    have hk' : k < N s₀ := by simpa using hk
    simp only [List.getElem_map,List.getElem_range,Function.comp_def]
    rw [block_bytes _ _ hk',list_getD (by simp [length_decrypt,length_blocksAt]; omega_using [hk'])]

end VG.Proof.AesCfb.AArch64.Decrypt

end

end

/-! ### `AesCfb.AArch64.Decrypt.Setup`, which only this module used -/

section

/-! # Reusing the existing verified forward-key setup for CFB -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

open VG.AArch64.RegUpd

def adapted (s : State) : State :=
  ((((s.write .x .x11 (s.gpr .x2)).write .x .x2 (s.gpr .x3)).write .x .x3 (s.gpr .x4)).write
    .x .x4 (s.gpr .x5)).setV .v31 (s.mem.readW (s.gpr .x2) 128)

theorem prefix_ok {s : State} (hp : UPre s) :
    WP isa (.block Impl.AesCfb.AArch64.Decrypt.adaptArgs) s (fun t => t = adapted s) := by
  rw [Impl.AesCfb.AArch64.Decrypt.adaptArgs]
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

/-- The AES setup's smaller data/scratch permissions are sufficient under CFB's permissions. -/
theorem setup_ok {s : State} (hp : UPre s) :
    WP isa (.block (Impl.AesCfb.AArch64.Decrypt.adaptArgs ++ encSetup)) s fun t =>
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

end VG.Proof.AesCfb.AArch64.Decrypt

end

end


/-! # CBC decryption, including the unchanged scratch buffer -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem data_size {s₀ : State} (hp : UPre s₀) : 16*N s₀ < 2^64 := by
  refine Nat.lt_of_not_le fun hc => hp.data_scr (S s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (S s₀-Dp s₀).isLt
  omega_using [hc]

theorem initial {s₀ s : State} (hK : Keys (R s₀) (wK s₀) s)
    (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4) (h11 : s.gpr .x11=Iv s₀)
    (h31 : s.v .v31=s₀.mem.readW (Iv s₀) 128) (hm : s.mem=s₀.mem)
    (hrd : s.rd=s₀.rd) (hwr : s.wr=s₀.wr) : Inv s₀ 0 0 s := by
  refine ⟨Nat.zero_le _,hK,by simpa [blk] using h2,by simpa using h3,h11,h31,?_,?_,hrd,hwr⟩
  · intro i _; simp [hm]
  · rw [hm]; exact Frame.refl _ _

theorem finish_iv {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) (N s₀) s) :
    WP isa (.block [.strq .v31 .x11 0]) s fun t =>
      (modeAArch64 (cfbMode false)).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
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

theorem code_ok {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.AesCfb.AArch64.Decrypt.code s₀ fun t =>
      (modeAArch64 (cfbMode false)).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCfb.AArch64.Decrypt.code
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨hK,_,h2,h3,h11,h31,hm,hrd,hwr⟩ => ?_)
  have hi := initial hK h2 h3 h11 h31 hm hrd hwr
  exact WP.seq (WP.mono (loops_ok hp hi) fun _ hI => finish_iv hp hI)

end VG.Proof.AesCfb.AArch64.Decrypt

end

end


/-! # The existing CFB contract, ABI, constant time, and scratch-write bound -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc VG.Proof.AesCbc.AArch64
open VG.Impl.AesCfb.AArch64.Decrypt (code)

theorem correct (s : State) (hp : (modeAArch64 (cfbMode false)).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (modeAArch64 (cfbMode false)).post s t := by
  have hk := instrs_keeps (c := code) (rs := preserved) (by lit_decide)
  have hg : code.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
    rwa [Code.allInstrs_eq]
  obtain ⟨tr,t,he,hq,hg⟩ := WP.gprs (rs := preserved) (code_ok (UPre.of hp)) hg (by lit_decide)
  exact ⟨tr,t,he,⟨hg,Exec.sp he,Exec.preservedV he (by lit_decide)⟩,hq.1⟩

theorem ct : ConstantTime isa (modeAArch64 (cfbMode false)).pre (modeAArch64 (cfbMode false)).pub code := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0,h1,h2,h3,h4,h5,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (modeAArch64 (cfbMode false)).Implies (Proof.AesCfb.decryptRoundsContract AArch64.abi) := by
  sig_implies [Proof.AesCfb.decryptRoundsContract,Spec.Cfb.aesSig,Spec.Cbc.aesSig,modeAArch64,cfbMode,cfb,cts,AArch64.abi,AArch64.argRegs] [sat] using sat

theorem verified : Verified AArch64.target code (Proof.AesCfb.decryptRoundsContract AArch64.abi) :=
  Verified.of_correct correct ct implies

/-- This path never writes scratch; no scratch bytes require clearing afterwards. -/
theorem written (s : State) (tr : List Leak) (t : State)
    (hp : (Proof.AesCfb.decryptRoundsContract AArch64.abi).pre s) (he : Exec isa code s tr t) :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cfb.aesSig [("scratch",0)] s t := by
  have h := UPre.of (implies.pre s hp)
  obtain ⟨tr',t',he',_,hf⟩ := code_ok h
  obtain ⟨_,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,AArch64.abi,AArch64.argRegs,Abi.withConsts,Spec.Cfb.aesSig,Spec.Cbc.aesSig,
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

end VG.Proof.AesCfb.AArch64.Decrypt
