module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Spill
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `ChaCha20.AArch64.Mixed5.Finish`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev firstR (s : State) : Region := ⟨s.gpr .x1,256⟩

structure Finished (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  buf : ∀ r : Fin 4, s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
    VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => block (ctr (source s₀) 4)) r
  data : ∀ k < 256, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,lowBuf s₀,firstR s₀] s₀.mem s.mem

theorem finish_ok {s₀ s : State} (hp : CP s₀) (h : Spilled s₀ s) :
    WP isa finish s (Finished s₀) := by
  obtain nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  obtain hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  apply WP.seq
  refine (restoreArgs_ok s h.saved).mono fun a
    ⟨ha1,ha2,ha3,hag,ham,har,haw,hav,hasp⟩ => ?_
  obtain ha0 : a.gpr .x0 = s₀.gpr .x0 := (hag _ (by decide) (by decide) (by decide)).trans hx0
  obtain ha₃ : a.gpr .x3 = s₀.gpr .x3 := ha3.trans hx20
  obtain har' : a.rd = s₀.rd := har.trans h.rd
  obtain haw' : a.wr = s₀.wr := haw.trans h.wr
  obtain hcnta : source a = ctr (source s₀) 4 := by
    rw [source,ham,hag _ (by decide) (by decide) (by decide)]; exact h.cnt
  obtain hc : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [har',haw',ha0]; exact hp.read 12
  obtain hco : InRegions a.wr (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [haw',ha0]; exact hp.counter
  apply WP.seq
  refine (counter_ok a (n := 4) (by decide) true hc hco).mono fun b
    ⟨hbm,hbg,hbr,hbw,hbv,hbsp⟩ => ?_
  obtain hb0 : b.gpr .x0 = s₀.gpr .x0 := (hbg _ (by decide)).trans ha0
  obtain hcntb : source b = source s₀ := by
    rw [source,hbg _ (by decide),hbm]
    change stateAt (a.mem.writeW (a.gpr .x0 + BitVec.ofNat 64 48)
      (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 48) 32 - BitVec.ofNat 32 4)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      ← VG.Proof.ChaCha20.AArch64.Xor.stateAt_getElem_counter]
    change (source a).set 12 ((source a)[12] - BitVec.ofNat 32 4) = _
    rw [hcnta,ctr,Vector.getElem_set_self,BitVec.add_sub_cancel,Vector.set_set,
      Vector.set_getElem_self]
  obtain hfb : Frame [sr s₀] a.mem b.mem := by
    rw [hbm,ha0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  obtain hv : VG.Proof.ChaCha20.AArch64.Neon4.Holds
      (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) b := by
    simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds,hbv,hav] using h.vec
  obtain hin : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hbr,hbw,har',haw',hb0]; exact hp.read k
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv hin).mono fun c ⟨hvc,hbc⟩ => ?_
  obtain hcb0 : c.gpr .x0 = s₀.gpr .x0 := (hbc.gpr _ (by decide)).trans hb0
  obtain hcb1 : c.gpr .x1 = s₀.gpr .x1 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha1)
  obtain hcb3 : c.gpr .x3 = s₀.gpr .x3 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha₃)
  obtain hrc : c.rd = s₀.rd := hbc.rd.trans (hbr.trans har')
  obtain hwc : c.wr = s₀.wr := hbc.wr.trans (hbw.trans haw')
  obtain hvc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => block (ctr (source s₀) j)) c := by
    intro k j hj
    rw [hvc k j hj,VG.Proof.ChaCha20.AArch64.Neon4.input_eq]
    change _ + (ctr (source b) j)[k] = _
    rw [hcntb]
    simp only [block,Vector.getElem_zipWith,Fin.getElem_fin]
  obtain hout : ∀ r j : Fin 4, InRegions c.wr
      (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hwc,hcb1]; exact hp.data _ _ (by omega_using [])
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hvc' hout).mono fun d ⟨hd,hfd,hcd⟩ => ?_
  obtain hfd' : Frame [firstR s₀] c.mem d.mem := by simpa only [hcb1] using hfd
  obtain hfc : Frame [sr s₀] s.mem c.mem := by rw [hbc.mem,← ham]; exact hfb
  obtain hpre : Frame [sr s₀,lowBuf s₀] s₀.mem c.mem :=
    h.frame.trans (hfc.mono (by simp))
  refine ⟨(congrFun hcd.gpr _).trans hcb0,(congrFun hcd.gpr _).trans hcb1,?_,
    (congrFun hcd.gpr _).trans hcb3,?_,hcd.rd.trans hrc,hcd.wr.trans hwc,
    hcd.sp.trans (hbc.sp.trans (hbsp.trans (hasp.trans h.sp))),?_,?_,?_,
    (hpre.mono (by simp)).trans (hfd'.mono (by simp))⟩
  · rw [hcd.gpr,hbc.gpr _ (by decide),hbg _ (by decide),ha2]
  · intro r hr h21 h22
    obtain n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    obtain n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    obtain n3 : r ≠ .x3 := by intro he; subst r; simp [preserved] at hr
    obtain n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    rw [hcd.gpr,hbc.gpr r n4,hbg r n4,hag r n1 n2 n3]
    exact h.keep r (VG.Proof.ChaCha20.AArch64.not_words_preserved hr) n1 h21 h22
  · rw [source,hcd.gpr,hcb0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfd' (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right (Region.sub_prefix (by decide : 256 ≤ 320))),hbc.mem]
    rw [← hb0]; exact hcntb
  · intro r
    rw [hfd'.read (r := lowBuf s₀) (Offset.contains_base _ (by omega_using []) (by omega_using []))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact (hp.d_b.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))).symm.sub_left
            (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide),
      hfc.read (r := lowBuf s₀) (Offset.contains_base _ (by omega_using []) (by omega_using []))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide)]
    exact h.read16 r
  · intro k hk
    rw [hcb1] at hd
    rw [hd k hk,hpre.bytes (R := dr s₀) (by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      · exact hp.st_d.symm
      · exact hp.d_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))
      (by change 320 ≤ 2 ^ 64; decide) (by change k < 320; omega_using [hk])]

end VG.Proof.ChaCha20.AArch64.Mixed5

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev lastR (s : State) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 256,64⟩

 theorem pointer_ok (s : State) {n : Nat} (hn : n < 4096) (sub : Bool) :
    WP isa (.block [if sub then .subImm .x .x1 .x1 n else .addImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1
        (if sub then s.gpr .x1 - BitVec.ofNat 64 n else s.gpr .x1 + BitVec.ofNat 64 n) ∧
      u.v = s.v ∧ u.sp = s.sp := by
  cases sub with
  | false =>
    change WP isa (.block [.addImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1 (s.gpr .x1 + BitVec.ofNat 64 n) ∧
        u.v = s.v ∧ u.sp = s.sp
    apply WP.block_cons_iff.mpr
    refine ⟨s.write .x .x1 (s.gpr .x1 + BitVec.ofNat 64 n),?_,
      WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
    simpa only [State.read,BitVec.setWidth_eq] using exec_addImm_x hn
  | true =>
    change WP isa (.block [.subImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1 (s.gpr .x1 - BitVec.ofNat 64 n) ∧
        u.v = s.v ∧ u.sp = s.sp
    apply WP.block_cons_iff.mpr
    refine ⟨s.write .x .x1 (s.gpr .x1 - BitVec.ofNat 64 n),?_,
      WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
    simpa only [State.read,BitVec.setWidth_eq] using exec_subImm_x hn

 theorem first_last_disjoint (s : State) : (firstR s).Disjoint (lastR s) := by
  exact Offset.base_disjoint (s.gpr .x1) (e := 256) (n := 64) (k := 256) (by decide) (by decide)

structure Chunked (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  data : ∀ k < 320, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,lowBuf s₀,dr s₀] s₀.mem s.mem

 theorem last_ok {s₀ s : State} (hp : CP s₀) (h : Finished s₀ s) :
    WP isa last s (Chunked s₀) := by
  apply WP.seq
  refine (pointer_ok s (n := 256) (by decide) false).mono fun a ⟨ha,hav,hasp⟩ => ?_
  obtain ha1 : a.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 256 := by simpa only [Bool.false_eq_true,ite_false,h.x1] using ha.gpr
  obtain ha3 : a.gpr .x3 = s₀.gpr .x3 := (ha.other _ (by decide)).trans h.x3
  obtain hf : ∀ r : Fin 4, a.mem.read (a.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => block (ctr (source s₀) 4)) r := by
    intro r; rw [ha.mem,ha3]; exact h.buf r
  obtain sep : (⟨a.gpr .x3,64⟩ : Region).Disjoint ⟨a.gpr .x1,64⟩ := by
    rw [ha3,ha1]
    exact (hp.d_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))).sub_right
      (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))
  obtain hin : ∀ r : Fin 4, InRegions (a.rd ++ a.wr) (a.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r; rw [ha.rd,ha.wr,h.rd,h.wr,ha3]
    obtain ⟨q,hq,hc⟩ := hp.buffer (16 * r.val) 16 (by omega_using [])
    exact ⟨q,List.mem_append_right _ hq,hc⟩
  obtain hout : ∀ r : Fin 4, InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r; rw [ha.wr,h.wr,ha1,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.data _ _ (by omega_using [])
  apply WP.seq
  refine (xorLast_ok a (block (ctr (source s₀) 4)) hf sep hin hout).mono fun b ⟨hb,hfb,hab⟩ => ?_
  obtain hfb' : Frame [lastR s₀] s.mem b.mem := by simpa only [ha1,ha.mem] using hfb
  refine (pointer_ok b (n := 256) (by decide) true).mono fun c ⟨hc,hcv,hcsp⟩ => ?_
  obtain hc1 : c.gpr .x1 = s₀.gpr .x1 := by
    rw [hc.gpr,hab.gpr,ha.gpr]
    simp only [ite_true,Bool.false_eq_true,ite_false,BitVec.add_sub_cancel,h.x1]
  have hd (r : Reg) (hr : r ≠ .x1) : c.gpr r = s.gpr r := by
    rw [hc.other r hr,hab.gpr,ha.other r hr]
  have hm : c.mem = b.mem := hc.mem
  refine ⟨(hd _ (by decide)).trans h.x0,hc1,(hd _ (by decide)).trans h.x2,
    (hd _ (by decide)).trans h.x3,?_,hc.rd.trans (hab.rd.trans (ha.rd.trans h.rd)),
    hc.wr.trans (hab.wr.trans (ha.wr.trans h.wr)),hcsp.trans (hab.sp.trans (hasp.trans h.sp)),?_,?_,?_⟩
  · intro r hr h21 h22
    obtain nr : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    rw [hd r nr]; exact h.cs r hr h21 h22
  · rw [source,hm,hd _ (by decide),h.x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb' (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact hp.st_d.sub_right (Offset.sub_base _ (by decide : 256 + 64 ≤ 320)))]
    rw [← h.x0]; exact h.cnt
  · intro k hk
    rw [hm]
    by_cases hk' : k < 256
    · have he : b.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) = s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) :=
        hfb'.bytes (R := firstR s₀) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact first_last_disjoint s₀) (by change 256 ≤ 2 ^ 64; decide) hk'
      rw [he]
      exact h.data k hk'
    · have he : a.gpr .x1 + BitVec.ofNat 64 (k - 256) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        rw [ha1,BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' (by omega_using [hk'])]
      obtain hh := hb (k - 256) (by omega_using [hk])
      rw [he,ha.mem] at hh
      obtain hh₀ := h.frame.bytes (R := lastR s₀) (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.st_d.symm.sub_left (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))
        · exact (hp.d_b.sub_left (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))).sub_right
            (Region.sub_prefix (by decide : 64 ≤ 320))
        · exact (first_last_disjoint s₀).symm)
        (by change 64 ≤ 2 ^ 64; decide) (i := k - 256) (by change k - 256 < 64; omega_using [hk])
      obtain he₀ : (lastR s₀).base + BitVec.ofNat 64 (k - 256) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        change s₀.gpr .x1 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (k - 256) = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' (by omega_using [hk'])]
      rw [he₀] at hh₀
      rw [hh,hh₀,show k / 64 = 4 by omega_using [hk, hk'],show k % 64 = k - 256 by omega_using [hk, hk']]
  · rw [hm]
    obtain hf₁ : Frame [sr s₀,lowBuf s₀,dr s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sr s₀,by simp,fun _ h => h⟩
      · exact ⟨lowBuf s₀,by simp,fun _ h => h⟩
      · exact ⟨dr s₀,by simp,Region.sub_prefix (by decide : 256 ≤ 320)⟩)
    exact hf₁.trans (hfb'.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨dr s₀,by simp,Offset.sub_base _ (by decide : 256 + 64 ≤ 320)⟩))

theorem chunk_ok {sve : Bool} (s : State) (hp : CP s) : WP isa (chunk sve) s (Chunked s) := by
  apply WP.seq
  refine (prepare_ok s hp).mono fun a h => ?_
  apply WP.seq
  refine (rounds_ok h.vec h.table h.scalar 10).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
  obtain h' : Prepared s b 10 := ⟨hv,ht,hc.holds,by
      rw [source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact h.cnt,
    ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩,
    fun r hr h21 h22 => (hc.keep r hr).trans (h.keep r hr h21 h22),hc.rd.trans h.rd,hc.wr.trans h.wr,
    hsp.trans h.sp,by rw [hc.mem]; exact h.frame⟩
  apply WP.seq
  refine (spill_ok hp h').mono fun c hc => ?_
  apply WP.seq
  refine (finish_ok hp hc).mono fun d hd => last_ok hp hd

end VG.Proof.ChaCha20.AArch64.Mixed5
