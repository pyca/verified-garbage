import VerifiedGarbage.Proof.Rc4.Arm.ApplyLoop
import VerifiedGarbage.Proof.Rc4.Arm.Init

/-! # RC4 on ARMv7: the stream function -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem apply_entry (s : State) (hs : applyC.pre s) :
    WP isa (.block entry) s fun a => a.mem = s.mem ∧ Keep [.r12] s a ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32) := by
  obtain ⟨_, hwr, _, _, _, cfit, _, _⟩ := hs
  have a256 : State.addr (s.gpr .r0 + BitVec.ofNat 32 256) = State.addr (s.gpr .r0) + 256#64 :=
    addr_add (a := s.gpr .r0) (k := 256) (by omega)
  have r256 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 256)) 1 := by
    rw [a256]
    refine region_in (region_offset _ _ 258 256 1 (by decide) (by decide) ?_)
    exact ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  refine WP.mono (WP.keep (Q := fun a => a.mem = s.mem ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32)) [.r12] ?_ (by decide))
    fun a ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2⟩
  unfold entry
  arun [r256]
  rw [a256]
  conj_rfl

theorem apply_start (b : State) {P : BitVec 32} (h0 : b.gpr .r0 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (h257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1) :
    WP isa (.block start) b fun c => c.mem = b.mem ∧ Keep [.r4, .r12, .r5, .r0, .r10] b c ∧
      c.gpr .r4 = b.gpr .r12 ∧ c.gpr .r12 = P ∧
      c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧ c.gpr .r0 = 0#32 ∧
      c.gpr .r10 = BitVec.allOnes 32 := by
  have a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega)
  have r257 : InRegions (b.rd ++ b.wr) (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact h257
  refine WP.mono (WP.keep (Q := fun c => c.mem = b.mem ∧ c.gpr .r4 = b.gpr .r12 ∧
      c.gpr .r12 = P ∧ c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧
      c.gpr .r0 = 0#32 ∧ c.gpr .r10 = BitVec.allOnes 32) [.r4, .r12, .r5, .r0, .r10] ?_
    (by decide)) fun c ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold start ones
  arun [h0, r257, ones_eq]
  rw [a257]
  conj_rfl

theorem apply_finish (d : State) (i j : Byte) {P : BitVec 32} (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (h4 : d.gpr .r4 = i.setWidth 32) (h5 : d.gpr .r5 = j.setWidth 32) (h12 : d.gpr .r12 = P)
    (hw : InRegions d.wr (State.addr P) 258) :
    WP isa (.block finish) d fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j ∧
      Keep [] d e := by
  have a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega)
  have a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega)
  have h256 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hw
  have h257 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact region_offset _ _ _ 257 1 (by decide) (by decide) hw
  refine WP.mono (WP.keep (Q := fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j)
    [] ?_ (by decide)) fun e ⟨h, hk⟩ => ⟨h, hk⟩
  unfold finish
  arun [h4, h5, h12, h256, h257]
  rw [a256, a257, writeW_byte8, writeW_byte8, low_byte32, low_byte32]

/-- The full stream function, including empty input. -/
theorem apply_ok (s : State) (hs : applyC.pre s) :
    WP isa VG.Impl.Rc4.Arm.apply s fun t => applyC.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  have hs' := hs
  obtain ⟨hrd, hwr, cd, cs, ds, cfit, dfit, sfit⟩ := hs'
  unfold applyC
  dsimp only
  generalize hP : s.gpr .r0 = P at hwr cd cs cfit ⊢
  generalize hD : s.gpr .r1 = D at hwr cd ds dfit ⊢
  generalize hL : s.gpr .r2 = L at hwr cd ds dfit ⊢
  generalize hS : s.gpr .r3 = Sc at hwr cs ds sfit
  have hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  have hdat : InRegions s.wr (State.addr D) L.toNat := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    Region.contains_self _ _⟩
  have hpres (t : State) (rs : List Reg) (hk : Keep rs s t) (hr : ∀ r ∈ preserved, r ∉ rs) :
      ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r h => hk.gpr (hr r h)
  unfold VG.Impl.Rc4.Arm.apply
  refine WP.seq (WP.mono (apply_entry s hs) fun a ⟨ham, hak, ha12, haz⟩ => ?_)
  rw [hP] at ha12
  rw [hL, BitVec.sub_zero] at haz
  refine WP.ite a.z (eval_eq a) (fun hz => ?_) (fun hnz => ?_)
  · have hL0 : L = 0#32 := by rw [haz, beq_iff_eq] at hz; exact hz
    refine WP.block_nil ⟨?_, hpres a _ hak (by decide), hak.2.2.2⟩
    rw [ham, hL0]
    exact ⟨rfl, rfl⟩
  have hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [haz, this] at hnz
    exact absurd hnz (by decide)
  refine WP.seq ?_
  have ha3 : a.gpr .r3 = Sc := (hak.gpr (by decide)).trans hS
  rw [WP.block_append_iff]
  refine WP.mono (save_ok a (by rw [ha3]; exact sfit) (by rw [hak.2.2.1, ha3]; exact hscr))
    fun b ⟨hbm, hbk⟩ => ?_
  rw [ha3] at hbm
  have ka : Keep [.r12] s b := (hak.trans hbk).mono (by decide)
  have hsave : Frame [⟨State.addr Sc, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact save_frame _ _ _
  have hctxb : contextAt b.mem (State.addr P) = contextAt s.mem (State.addr P) :=
    contextAt_frame hsave fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cs
  have r257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1 := by
    rw [ka.2.1, ka.2.2.1]
    exact region_in (region_offset _ _ _ 257 1 (by decide) (by decide) hctx)
  refine WP.mono (apply_start b ((ka.gpr (by decide)).trans hP) cfit r257)
    fun c ⟨hcm, hck, hc4, hc12, hc5, hc0, hc10⟩ => ?_
  have kc : Keep [.r12, .r4, .r5, .r0, .r10] s c := (ka.trans hck).mono (by decide)
  have hec : StepEnv c P D L :=
    { p := hc12
      d := (kc.gpr (by decide)).trans hD
      l := (kc.gpr (by decide)).trans hL
      ones := hc10
      pfit := cfit
      dfit := dfit
      table := by
        rw [kc.2.2.1]
        have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
        simpa only [BitVec.add_zero] using h'
      data := by rw [kc.2.2.1]; exact hdat
      sTD := sep_of_sub cd (contains_prefix _ (by decide)) (contains_prefix _ (Nat.le_refl _)) }
  have hinv : LoopInv s.mem P D L c 0 c := by
    have hu0 : upd s.mem P D 0 = (contextAt s.mem (State.addr P), []) := rfl
    refine
      { le := Nat.zero_le _
        table := by rw [hu0, hcm, hctxb]
        i := by
          rw [hu0, hc4, (hbk.gpr (by decide) : b.gpr .r12 = a.gpr .r12), ha12]
        j := by
          rw [hu0, hc5, ← hctxb]
          rfl
        data := by rw [hu0]; rfl
        tail := fun x _ hx => by
          rw [hcm]
          exact hsave.bytes (R := ⟨State.addr D, L.toNat⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr
            subst hr
            exact ds) (show L.toNat ≤ 2 ^ 64 by have := L.isLt; omega) hx
        frame := Frame.refl _ _
        count := hc0
        keep := Keep.refl _ _ }
  refine WP.seq (WP.mono (apply_loop s.mem c hec (Nat.pos_of_ne_zero hL0) c hinv)
    fun d hd => ?_)
  have kd : Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ stepRegs) s d := kc.trans hd.keep
  rw [WP.block_append_iff]
  refine WP.mono (apply_finish d (upd s.mem P D L.toNat).1.i (upd s.mem P D L.toNat).1.j cfit
    hd.i hd.j ((hd.keep.gpr (by decide)).trans hc12) (by rw [kd.2.2.1]; exact hctx))
    fun e ⟨hem, hek⟩ => ?_
  have hce : Frame [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] b.mem e.mem := by
    have hc258 : (⟨State.addr P, 258⟩ : Region) ∈
        [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] := List.mem_cons_self
    rw [hem]
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    have hbd : Frame (loopRegions P D L) b.mem d.mem := by rw [← hcm]; exact hd.frame
    refine hbd.sub fun r hr => ?_
    simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  have ke : Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ stepRegs) s e :=
    (kd.trans hek).mono (by decide)
  have he3 : e.gpr .r3 = Sc := (ke.gpr (by decide)).trans hS
  have hsaved : Spill.Saved e.mem (State.addr (e.gpr .r3)) a.gpr saved := by
    rw [he3]
    have h0 : Spill.Saved b.mem (State.addr Sc) a.gpr saved := by
      rw [hbm]
      exact Spill.saveMem_saved _ _ _ _ saved_slots
    refine h0.frame saved_slots hce fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [BitVec.add_zero]
    rcases hr with rfl | rfl
    · exact (cs.symm.sub_left (Region.sub_prefix (by decide)))
    · exact (ds.symm.sub_left (Region.sub_prefix (by decide)))
  refine WP.mono (restore_ok e (by rw [he3]; exact sfit)
    (by rw [ke.2.1, ke.2.2.1, he3]; exact region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (State.addr D) L.toNat (State.addr P + BitVec.ofNat 64 o) 1 :=
    sep_of_sub cd.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega) (by omega))
  have hLn : L.toNat < 2 ^ 64 := by have := L.isLt; omega
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_, hgk.2.2.2.trans ke.2.2.2⟩
  · rw [hgm, hem, context_finish]
    exact context_ext hd.table rfl rfl
  · rw [hgm, hem, bytes_write_sep _ _ _ _ _ hLn (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ hLn (hDP 256 (by decide))]
    exact hd.data
  · by_cases hs : r ∈ saved.map Prod.fst
    · rw [hgr r hs]
      exact hak.gpr (by rw [saved_regs] at hs; revert hs; revert r; decide)
    · rw [hgk.gpr (by rw [← saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact ke.gpr (by decide)

end VG.Proof.Rc4.Arm
