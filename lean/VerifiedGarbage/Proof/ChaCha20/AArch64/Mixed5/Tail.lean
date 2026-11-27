module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Args
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
public import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds

/-! ### `ChaCha20.AArch64.Mixed5.Spill`, which the modules that import this one used -/

section

/-! ### `ChaCha20.AArch64.Mixed5.Prepare`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock)

abbrev source (s : State) : CState := stateAt s.mem (s.gpr .x0)
abbrev sr (s : State) : Region := ⟨s.gpr .x0,64⟩
abbrev br (s : State) : Region := ⟨s.gpr .x3,320⟩
abbrev dr (s : State) : Region := ⟨s.gpr .x1,320⟩

structure CP (s : State) : Prop where
  x20 : s.gpr .x20 = s.gpr .x3
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (sr s).Disjoint (br s)
  st_d : (sr s).Disjoint (dr s)
  d_b : (dr s).Disjoint (br s)

structure Prepared (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (ctr (source s₀) j)) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock n (ctr (source s₀) 4)) s
  cnt : source s = ctr (source s₀) 4
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀] s₀.mem s.mem

 theorem prepare_ok (s : State) (hp : CP s) : WP isa prepare s (Prepared s) := by
  apply WP.seq
  refine (saveArgs_ok s).mono fun a ⟨hsaved,hg,hm₀,hr,hw,hv,hsp⟩ => ?_
  have ha : source a = source s := by
    rw [source,hm₀,hg _ (by decide) (by decide)]
  have hi : ∀ k : Fin 16, InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hg _ (by decide) (by decide),hr,hw]; exact hp.read k
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setup_ok a hi).mono fun b ⟨hb,hab,hbt⟩ => ?_
  have h0 : b.gpr .x0 = s.gpr .x0 := by rw [hab.gpr _ (by decide),hg _ (by decide) (by decide)]
  have hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.rd,hab.wr,h0,hr,hw]; exact hp.read 12
  have hco : InRegions b.wr (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.wr,hw,h0]; exact hp.counter
  apply WP.seq
  refine (counter_ok b (n := 4) (by decide) false hc hco).mono fun c
    ⟨hcm,hcg,hcr,hcw,hcv,hcsp⟩ => ?_
  have hcnt : source c = ctr (source s) 4 := by
    rw [source,hcg _ (by decide),hcm]
    change stateAt (b.mem.writeW (b.gpr .x0 + BitVec.ofNat 64 48)
      (b.mem.readW (b.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 4)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    rw [source,hab.mem,hab.gpr _ (by decide)]
    exact congrArg (fun v => ctr v 4) ha
  have hfc : Frame [sr s] b.mem c.mem := by
    rw [hcm,h0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hcs : SavedArgs (s.gpr .x2) (s.gpr .x1) c := by
    exact ⟨by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.len,
      by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.data⟩
  have hpc : VG.Proof.ChaCha20.AArch64.Pre c := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (c.rd ++ c.wr) (c.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcr,hcw,hab.rd,hab.wr,hr,hw,hcg _ (by decide),h0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcw,hab.wr,hw,hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide)]
      exact hp.data _ _ (by omega_using [hk])
    · change (⟨c.gpr .x1,256⟩ : Region).Disjoint ⟨c.gpr .x0,64⟩
      rw [hcg _ (by decide),hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide),h0]
      exact hp.st_d.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i
    rfl
  refine (keeps_vectors hload (scalarLoad_ok c hpc)).mono fun d ⟨⟨hd,hm,hdrr,hdwr,hdk⟩,hdv,hdsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,hdrr.trans (hcr.trans (hab.rd.trans hr)),
    hdwr.trans (hcw.trans (hab.wr.trans hw)),hdsp.trans (hcsp.trans (hab.sp.trans hsp)),?_⟩
  · intro k j hj
    rw [hdv,hcv]
    have hbb : VG.Proof.ChaCha20.AArch64.Neon4.Holds (ctr (source a)) b := hb
    rw [ha] at hbb
    exact hbb k j hj
  · rw [hdv,hcv,hbt]
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat] using hd
  · rw [source,hm,hdk _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact hcnt
  · exact ⟨by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.len,
      by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.data⟩
  · intro r hnr h21 h22
    rw [hdk r hnr,hcg r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),
      hab.gpr r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),hg r h21 h22]
  · rw [hm]
    rw [hab.mem,hm₀] at hfc
    exact hfc

end VG.Proof.ChaCha20.AArch64.Mixed5

end

end

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev lowBuf (s : State) : Region := ⟨s.gpr .x3,64⟩

/-- Move a public pointer, preserving all other state. -/
theorem move_ok (s : State) (d n : Reg) :
    WP isa (.block [.addImm .x d n 0]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u d (s.gpr n) ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x d (s.gpr n),?_,WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
  simpa only [State.read,BitVec.setWidth_eq,BitVec.add_zero] using
    exec_addImm_x (s := s) (d := d) (n := n) (imm := 0) (by decide)

structure Spilled (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Neon4.Holds
    (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) s
  cnt : source s = ctr (source s₀) 4
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  words : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 4))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,lowBuf s₀] s₀.mem s.mem

theorem spill_ok {s₀ s : State} (hp : CP s₀) (h : Prepared s₀ s 10) :
    WP isa spill s (Spilled s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide)
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (move_ok s .x1 .x20).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (source s₀) 4)) a := by
    intro k hk
    rw [ha.other _ (by
      intro he; exact VG.Proof.ChaCha20.AArch64.not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  have hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.rd,ha.wr,h.rd,h.wr,ha.other _ (by decide),hx0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.wr,h.wr,ha.gpr,hx20]
      exact hp.buffer _ _ (by omega_using [hk])
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by
    decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  have hfb : Frame [lowBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  have hcntₐ : source a = ctr (source s₀) 4 := by
    rw [source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  have hcntb : source b = ctr (source s₀) 4 := by
    rw [source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))]
    exact hcntₐ
  have hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,hcntb,hsavedb,?_,?_,?_,
    hr.trans (ha.rd.trans h.rd),hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds,hbv,hav] using h.vec
  · intro k hkk
    have he := hb k hkk
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr hr1 h21 h22; rw [hk r hnr,ha.other r hr1,h.keep r hnr h21 h22]
  · rw [hk _ VG.Proof.ChaCha20.AArch64.not_words_x1,ha.gpr,hx20]
  · rw [ha.mem] at hfb
    exact (h.frame.mono (by simp)).trans (hfb.mono (by simp))

theorem Spilled.read16 {s₀ s : State} (h : Spilled s₀ s) (r : Fin 4) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => block (ctr (source s₀) 4)) r := by
  rw [VG.AArch64.read16]
  have hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (block (ctr (source s₀) 4))[4 * r.val + e]'(by omega_using [he]) := by
    intro e he
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega_using []]
    exact h.words _ (by omega_using [he])
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.mod_eq_of_lt r.isLt,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed5

end

end

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Impl.ChaCha20.AArch64.Neon4 (vreg rowWord)
open VG.Proof.ChaCha20.AArch64.Neon4

/-- Only the first four slots of this data view have been written. -/
theorem Data.frame64 {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) (hd : ∀ k ∈ done, k < 4) : Frame [⟨p,64⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 64 := by
    have hh := hx ⟨p,64⟩ (by simp)
    simp only [Region.Contains] at hh
    omega_using [hh]
  rw [h x,ite_eq_right]
  rintro ⟨hslot,hlt⟩
  have hs := hd _ hslot
  omega_using [hn, hs]

theorem loadLast_ok (s : State) (r : Fin 4)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block [.ldrq (vreg (rowWord r 0)) .x3 (16 * r)]) s fun u =>
      u.v (vreg (rowWord r 0)) = s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 ∧
      Same s u := by
  have ha : (16 * r.val) % 16 = 0 ∧ 16 * r.val < 4096 * 16 := by omega_using []
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceMul, runBlock_cons,runBlock_nil,exec,addr,ha,and_self,
    State.load,hi,Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,
    exists_eq_left',RegUpd.v_setV_self]
  exact ⟨trivial,rfl,rfl,rfl,rfl,rfl⟩

theorem xorLastRows_ok (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p b : Addr} {v : CState} {done : List Nat}
    (hd : Data m₀ s.mem p (output (fun _ => v)) done)
    (hdone : ∀ k ∈ done, k < 4) (hp : s.gpr .x1 = p) (hb : s.gpr .x3 = b)
    (hbuf : ∀ r : Fin 4, s.mem.read (b + BitVec.ofNat 64 (16 * r)) 16 =
      output (fun _ => v) r)
    (hsep : (⟨b,64⟩ : Region).Disjoint ⟨p,64⟩)
    (hfresh : ∀ r ∈ rs, r.val ∉ done)
    (hin : ∀ r : Fin 4, InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (16 * r)) 16)
    (hout : ∀ r : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block (rs.flatMap xorLastRow)) s fun u =>
      Data m₀ u.mem p (output (fun _ => v)) (rs.map Fin.val ++ done) ∧
      Keep s u := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd,⟨rfl,rfl,rfl,rfl⟩⟩
  | cons r rs ih =>
    apply WP.block_append
    apply WP.block_append
    have hi : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 := hb ▸ hin r
    refine (loadLast_ok s r hi).mono fun a ⟨ha,hsa⟩ => ?_
    have hda : Data m₀ a.mem p (output (fun _ => v)) done := hsa.mem ▸ hd
    have hpa : a.gpr .x1 = p := by rw [hsa.gpr,hp]
    have hva : a.v (vreg (rowWord r 0)) = output (fun _ => v) (slot r 0) := by
      simpa only [slot,Fin.val_zero,Nat.mul_zero,Nat.zero_add,hb,hbuf r] using ha
    have hoa : InRegions a.wr (p + BitVec.ofNat 64 (64 * (0 : Fin 4) + 16 * r)) 16 := by
      rw [hsa.wr]; simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hout r
    have hoa' : InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (64 * (0 : Fin 4) + 16 * r)) 16 := by
      rw [hpa]; exact hoa
    refine (xorRow_ok a r 0 hoa').mono fun u ⟨hm,hau⟩ => ?_
    have hu : Data m₀ u.mem p (output (fun _ => v)) (slot r 0 :: done) := by
      rw [hm,hpa,hva,show 64 * (0 : Fin 4).val + 16 * r.val = 16 * slot r 0 by simp [slot]]
      exact hda.store (slot_lt r 0) (by simpa [slot] using hfresh r (by simp))
    have hsu : Keep s u := ⟨hau.gpr.trans hsa.gpr,hau.rd.trans hsa.rd,
      hau.wr.trans hsa.wr,hau.sp.trans hsa.sp⟩
    have hdone' : ∀ k ∈ slot r 0 :: done, k < 4 := by
      intro k hk
      rcases List.mem_cons.mp hk with he | he
      · subst k; simp [slot]
      · exact hdone k he
    have hf := Data.frame64 hu hdone'
    have hf₀ := Data.frame64 hd hdone
    have hbu : ∀ q : Fin 4, u.mem.read (b + BitVec.ofNat 64 (16 * q)) 16 =
        output (fun _ => v) q := by
      intro q
      rw [hf.read (r := ⟨b,64⟩) (Offset.contains_base _ (by omega_using []) (by omega_using []))
        (by intro z hz; simpa using (List.mem_singleton.mp hz ▸ hsep)) (by decide), ← hf₀.read (r := ⟨b,64⟩) (Offset.contains_base _ (by omega_using []) (by omega_using []))
        (by intro z hz; simpa using (List.mem_singleton.mp hz ▸ hsep)) (by decide),hbuf q]
    have hpu : u.gpr .x1 = p := by rw [hsu.gpr,hp]
    have hpb : u.gpr .x3 = b := by rw [hsu.gpr,hb]
    have hiu : ∀ q : Fin 4, InRegions (u.rd ++ u.wr) (b + BitVec.ofNat 64 (16 * q)) 16 := by
      intro q; rw [hsu.rd,hsu.wr]; exact hin q
    have hou : ∀ q : Fin 4, InRegions u.wr (p + BitVec.ofNat 64 (16 * q)) 16 := by
      intro q; rw [hsu.wr]; exact hout q
    have hfr : ∀ q ∈ rs, q.val ∉ slot r 0 :: done := by
      intro q hq
      simp only [List.mem_cons,not_or]
      refine ⟨?_,hfresh q (by simp [hq])⟩
      intro he
      have hne := (List.nodup_cons.mp hn).1
      apply hne
      have eq : q = r := Fin.ext (by simpa [slot] using he)
      exact eq ▸ hq
    refine (ih (List.nodup_cons.mp hn).2 hu hdone' hpu hpb hbu hfr hiu hou).mono
      fun z ⟨hz,huz⟩ => ⟨?_,hsu.trans huz⟩
    intro x
    simpa only [Data,List.map_cons,List.mem_append,List.mem_cons,slot,Fin.val_zero,
      Nat.mul_zero,Nat.zero_add,or_assoc,or_left_comm] using hz x

theorem xorLast_ok (s : State) (v : CState)
    (hbuf : ∀ r : Fin 4, s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      output (fun _ => v) r)
    (hsep : (⟨s.gpr .x3,64⟩ : Region).Disjoint ⟨s.gpr .x1,64⟩)
    (hin : ∀ r : Fin 4, InRegions (s.rd ++ s.wr)
      (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16)
    (hout : ∀ r : Fin 4, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap xorLastRow)) s fun u =>
      (∀ k < 64, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^ (VG.Spec.ChaCha20.serialize v).getD k 0) ∧
      Frame [⟨s.gpr .x1,64⟩] s.mem u.mem ∧ Keep s u := by
  refine (xorLastRows_ok (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (output (fun _ => v))) (by simp) rfl rfl hbuf hsep
    (by simp) hin hout).mono fun u ⟨hd,hk⟩ => ⟨?_,?_,hk⟩
  · intro k hk
    have hm : k / 16 ∈ (List.finRange 4).map Fin.val ++ ([] : List Nat) := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨⟨k / 16,by omega_using [hk]⟩,List.mem_finRange _,rfl⟩
    rw [hd _,Mem.sub_ofNat_toNat _ (by omega_using [hk] : k < 2 ^ 64),ite_eq_left ⟨hm,by omega_using [hk]⟩,
      output_byte (fun _ => v) (by omega_using [hk]),Nat.mod_eq_of_lt hk]
  · apply Data.frame64 hd
    intro k hk
    simp only [List.append_nil,List.mem_map] at hk
    obtain ⟨r,_,rfl⟩ := hk
    exact r.isLt

end VG.Proof.ChaCha20.AArch64.Mixed5
