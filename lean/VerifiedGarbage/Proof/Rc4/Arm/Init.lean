import VerifiedGarbage.Proof.Rc4.Arm.Schedule
import VerifiedGarbage.Proof.Rc4.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-! # RC4 on ARMv7: checked initialization -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-! ## Our caller's registers -/

theorem saved_slots : Spill.Slots 0 32 saved := by decide

theorem saved_restorable : Spill.Restorable .r3 saved := by decide

/-- The registers `saved` lists. -/
theorem saved_regs : saved.map Prod.fst = [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := rfl

/-- Saving the registers in `scratch` at `S`. -/
theorem save_ok (s : State) (hfit : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r3)) 64) :
    WP isa (.block save) s fun t =>
      t.mem = Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Spill.save_block_ok saved_slots (by omega) fun d _ hd =>
    region_offset _ _ _ _ _ (by omega) (by omega) hw) (by decide)) fun t ⟨h, hk⟩ => ⟨h.2.2.2, hk⟩

/-- What saving changes: the first 32 bytes of `scratch`. -/
theorem save_frame (m : Mem) (S : Addr) (g : Reg → BitVec 32) :
    Frame [⟨S, 64⟩] m (Spill.saveMem m S g saved) :=
  Spill.saveMem_frame _ _ _ (by decide) _ (by decide)

/-- The saved registers survive writes to the table. -/
theorem saved_after {m m' : Mem} {S P : Addr} {g : Reg → BitVec 32}
    (h : Spill.Saved m S g saved) (hf : Frame [⟨P, 258⟩] m m')
    (hd : Region.Disjoint ⟨P, 258⟩ ⟨S, 64⟩) : Spill.Saved m' S g saved := by
  refine h.frame saved_slots hf fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact (hd.symm.sub_left (by
    rw [BitVec.add_zero]
    exact Region.sub_prefix (by decide)))

/-- Restoring them. -/
theorem restore_ok (s : State) {g : Reg → BitVec 32} (hfit : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3)) 64)
    (hs : Spill.Saved s.mem (State.addr (s.gpr .r3)) g saved) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ saved.map Prod.fst, t.gpr r = g r) ∧
      Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable (by omega)
    (fun d _ hd => region_offset _ _ _ _ _ (by omega) (by omega) hr) hs)
    fun t ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨fun r hr => Spill.restored_reg h₁ hr,
      ⟨fun r hr => h₂ r (by rw [saved_regs]; exact hr), h₄, h₅, h₆⟩, h₃⟩

/-! ## Initialization -/

theorem init_finish (s : State) {P : BitVec 32} (h12 : s.gpr .r12 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (hp : InRegions s.wr (State.addr P) 258) :
    WP isa (.block [.mov .r9 (imm 0), .strb .r9 .r12 256, .strb .r9 .r12 257]) s
      fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
          (State.addr P + 257#64) 1 0#8 ∧ Keep [.r9] s t := by
  have a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega)
  have a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega)
  have h256 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact region_offset _ _ _ 257 1 (by decide) (by decide) hp
  refine WP.mono (WP.keep (Q := fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
      (State.addr P + 257#64) 1 0#8) [.r9] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h, hk⟩
  arun [h12, h256, h257]
  rw [a256, a257, writeW_byte8, writeW_byte8]
  rfl

theorem init_valid (s : State) (hs : initC.pre s)
    (hlen : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) :
    WP isa initValid s fun t => t.gpr .r0 = 0#32 ∧
      contextAt t.mem (State.addr (s.gpr .r2)) =
        { table := keySchedule (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat),
          i := 0, j := 0 } ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  obtain ⟨hrd, hwr, kc, ks, cs, kfit, cfit, sfit⟩ := hs
  generalize hP : s.gpr .r2 = P at hwr kc cs cfit ⊢
  generalize hK : s.gpr .r0 = K at hrd kc ks kfit ⊢
  generalize hL : s.gpr .r1 = Lk at hrd kc ks kfit hlen ⊢
  generalize hS : s.gpr .r3 = Sc at hwr ks cs sfit
  have hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  have hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have htab : InRegions s.wr (State.addr P) 256 := by
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
    simpa only [BitVec.add_zero] using h'
  unfold initValid
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (by rw [hS]; exact sfit) (by rw [hS]; exact hscr))
    fun a ⟨ham, hak⟩ => ?_
  rw [hS] at ham
  have haf : Frame [⟨State.addr Sc, 64⟩] s.mem a.mem := by rw [ham]; exact save_frame _ _ _
  have hb : WP isa (.block [.mov .r12 (.reg .r2), .mov .r4 (imm 0)]) a fun b =>
      b.gpr .r12 = P ∧ b.gpr .r4 = 0#32 ∧ b.mem = a.mem := by
    arun [hak.gpr (r := .r2) (by decide), hP]
  refine WP.mono (WP.keep [.r12, .r4] hb (by decide)) fun b ⟨⟨hb12, hb4, hbm⟩, hbk⟩ => ?_
  have kb : Keep [.r12, .r4] s b := (hak.trans hbk).mono (by decide)
  have hpb : InRegions b.wr (State.addr (b.gpr .r12)) 256 := by rw [kb.2.2.1, hb12]; exact htab
  have hfit : (b.gpr .r12).toNat + 256 ≤ 2 ^ 32 := by rw [hb12]; omega
  have hib : IdentityInv b 0 b := ⟨by rw [identityMem_zero], Keep.refl _ _, hb4⟩
  refine WP.seq (WP.mono (identity_loop b b (by decide) hfit hpb hib) fun c hc => ?_)
  obtain ⟨hcm, hck, _⟩ := hc
  have hd : WP isa (.block (([.mov .r4 (imm 0), .mov .r2 (imm 0), .mov .r5 (imm 0)] : List Instr) ++
      ones)) c fun d => d.gpr .r4 = 0#32 ∧ d.gpr .r2 = 0#32 ∧ d.gpr .r5 = 0#32 ∧
        d.gpr .r10 = BitVec.allOnes 32 ∧ d.mem = c.mem := by
    unfold ones
    arun [ones_eq]
  refine WP.seq (WP.mono (WP.keep [.r4, .r2, .r5, .r10] hd (by decide))
    fun d ⟨⟨hd4, hd2, hd5, hd10, hdm⟩, hdk⟩ => ?_)
  have kd : Keep [.r4, .r2, .r5, .r10, .r9, .r12] s d :=
    ((kb.trans (hck.trans hdk)).mono (by decide))
  have hd12 : d.gpr .r12 = P := ((hck.trans hdk).gpr (by decide)).trans hb12
  have hdmem : d.mem = identityMem a.mem (State.addr P) 256 := by rw [hdm, hcm, hbm, hb12]
  -- The key is untouched by the saves and the identity permutation.
  have hkey : keyOf d.mem K Lk = bytesAt s.mem (State.addr K) Lk.toNat := by
    unfold keyOf bytesAt
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    have hin : (⟨State.addr K, Lk.toNat⟩ : Region).Contains (State.addr K + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    rw [hdmem, identityMem_frame _ _ _ (by decide) _ fun hl =>
      kc _ hin (by simp only [Region.Contains] at hl ⊢; omega)]
    exact haf _ fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ks _ hin
  have hen : ScheduleEnv d P K Lk :=
    { p := hd12
      k := (kd.gpr (by decide)).trans hK
      l := (kd.gpr (by decide)).trans hL
      ones := hd10
      len := hlen
      fit := by omega
      table := by rw [kd.2.2.1]; exact htab
      key := by
        rw [kd.2.1, kd.2.2.1, hrd]
        exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
      keyFit := kfit
      keySep := fun x h₁ h₂ => kc x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega) }
  have hid : ScheduleInv d P K Lk 0 d := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, Keep.refl _ _⟩
    · rw [hdmem, identityMem_table, schedule_zero]
    · rw [hd5]; rfl
    · rw [hd4]
    · rw [hd2, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop d d (by decide) hen hid) fun e he => ?_)
  have ke : Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s e :=
    (kd.trans he.keep).mono (by decide)
  have he12 : e.gpr .r12 = P := (he.keep.gpr (by decide)).trans hd12
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (init_finish e he12 cfit (by rw [ke.2.2.1]; exact hctx)) fun f ⟨hfm, hfk⟩ => ?_
  have kf : Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s f :=
    (ke.trans hfk).mono (by decide)
  have hctxf : Frame [⟨State.addr P, 258⟩] a.mem f.mem := by
    rw [hfm]
    refine frame_finish ?_ _ _
    have h1 := frame_of_table he.frame
    have h0 := frame_of_table (identityMem_frame a.mem (State.addr P) 256 (by decide))
    rw [hdmem] at h1
    exact h0.trans h1
  have hf3 : f.gpr .r3 = Sc := (kf.gpr (by decide)).trans hS
  have hsaved : Spill.Saved f.mem (State.addr (f.gpr .r3)) s.gpr saved := by
    rw [hf3]
    refine saved_after ?_ hctxf cs
    rw [ham]
    exact Spill.saveMem_saved _ _ _ _ saved_slots
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok f (by rw [hf3]; exact sfit)
    (by rw [kf.2.1, kf.2.2.1, hf3]; exact region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  have h0 : WP isa (.block [.mov .r0 (imm 0)]) g fun t => t.gpr .r0 = 0#32 ∧ t.mem = g.mem := by
    arun
  refine WP.mono (WP.keep [.r0] h0 (by decide)) fun t ⟨⟨t0, tm⟩, tk⟩ => ?_
  refine ⟨t0, ?_, ?_, tk.2.2.2.trans (hgk.2.2.2.trans kf.2.2.2)⟩
  · have ht := he.table
    rw [tm, hgm, hfm, context_finish, ht, ← keySchedule_eq, hkey]
    rfl
  · intro r hr
    rw [tk.gpr (by simp only [preserved] at hr; revert hr; revert r; decide)]
    by_cases hs : r ∈ saved.map Prod.fst
    · exact hgr r hs
    · rw [hgk.gpr (by rw [← saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact kf.gpr (by decide)

/-- `(len - 1) >> 8` is zero iff `len` is in `1..=256`. -/
theorem valid_len (L : BitVec 32) :
    ((L - BitVec.ofNat 32 1) >>> 8 - BitVec.ofNat 32 0 == 0#32) =
      decide (1 ≤ L.toNat ∧ L.toNat ≤ 256) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, BitVec.sub_zero,
    ← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
  have := L.isLt
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State) (hs : initC.pre s) :
    WP isa VG.Impl.Rc4.Arm.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
      | .ok ctx => t.gpr .r0 = 0#32 ∧ contextAt t.mem (State.addr (s.gpr .r2)) = ctx
      | .error .invalidKeyLength => t.gpr .r0 = 1#32) ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  have hcheck : WP isa (.block [.dp .sub .r12 .r1 (imm 1), .mov .r12 (.shifted .r12 .lsr 8),
      .cmp .r12 (imm 0)]) s fun t => t.mem = s.mem ∧
      t.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
    arun
    exact valid_len _
  unfold VG.Impl.Rc4.Arm.init
  refine WP.seq (WP.mono (WP.keep [.r12] hcheck (by decide)) fun t ⟨⟨htm, htz⟩, htk⟩ => ?_)
  have htp : initC.pre t := by
    obtain ⟨hrd, hwr, h⟩ := hs
    refine ⟨?_, ?_, ?_⟩ <;> simp only [htk.2.1, htk.2.2.1, htk.gpr (r := .r0) (by decide),
      htk.gpr (r := .r1) (by decide), htk.gpr (r := .r2) (by decide),
      htk.gpr (r := .r3) (by decide)] <;> with_reducible assumption
  have hreg (r : Reg) (hr : r ≠ .r12) : t.gpr r = s.gpr r := htk.gpr (by simpa using hr)
  refine WP.ite (!t.z) rfl (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
      intro hg; rw [htz, decide_eq_true hg] at hn; exact absurd hn (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    have h1 : WP isa (.block [.mov .r0 (imm 1)]) t fun u => u.gpr .r0 = 1#32 := by
      arun
    refine WP.mono (WP.keep [.r0] h1 (by decide)) fun u ⟨hu, huk⟩ => ⟨hu, ?_, ?_⟩
    · intro r hr
      have : r ≠ .r0 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [huk.gpr (by simpa using this.1), hreg r this.2]
    · exact huk.2.2.2.trans htk.2.2.2
  · have hg : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256 := by
      by_contra hg; rw [htz, decide_eq_false hg] at hy; exact absurd hy (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    refine WP.mono (init_valid t htp (by rw [hreg .r1 (by decide)]; exact hg))
      fun u ⟨hu0, huc, hup, husp⟩ => ?_
    rw [hreg .r0 (by decide), hreg .r1 (by decide), hreg .r2 (by decide), htm] at huc
    refine ⟨⟨hu0, huc⟩, fun r hr => ?_, husp.trans htk.2.2.2⟩
    rw [hup r hr]
    refine hreg r ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Rc4.Arm
