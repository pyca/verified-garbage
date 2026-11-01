module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Value
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce

-- separate module: setup and round groups are used by both the cipher and key loops.
/-! # POWER8 AES instruction groups -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (key mask byteMask)

/-- Only the listed registers may change; memory and permissions stay fixed. -/
structure Local (gs : List Reg) (vs : List VReg) (s t : State) : Prop where
  keep : Keep gs s t
  v : ∀ r, r ∉ vs → t.vpr r = s.vpr r
  mem : t.mem = s.mem

theorem Local.refl (gs : List Reg) (vs : List VReg) (s : State) : Local gs vs s s :=
  ⟨Keep.refl _ _, fun _ _ => rfl, rfl⟩

theorem Local.trans {gs hs : List Reg} {vs ws : List VReg} {s t u : State}
    (h : Local gs vs s t) (h' : Local hs ws t u) : Local (gs ++ hs) (vs ++ ws) s u :=
  ⟨h.keep.trans h'.keep, fun r hr => by
    rw [List.mem_append, not_or] at hr
    exact (h'.v r hr.2).trans (h.v r hr.1), h'.mem.trans h.mem⟩

theorem Local.weaken {gs hs : List Reg} {vs ws : List VReg} {s t : State}
    (h : Local gs vs s t) (hg : ∀ r ∈ gs, r ∈ hs) (hv : ∀ r ∈ vs, r ∈ ws) : Local hs ws s t :=
  ⟨h.keep.mono hg, fun r hr => h.v r (fun he => hr (hv r he)), h.mem⟩

theorem Local.of_vector {vs : List VReg} {s t : State} (h : VOnly vs s t) : Local [] vs s t :=
  ⟨⟨fun r _ => congrFun h.gpr r, h.rd, h.wr⟩, h.v, h.mem⟩

theorem Local.write (s : State) (d : Reg) (x : BitVec 64) : Local [d] [] s (s.write d x) := by
  refine ⟨⟨fun r hr => ?_, RegUpd.rd_write .., RegUpd.wr_write ..⟩, ?_, RegUpd.mem_write ..⟩
  · simp only [List.mem_singleton] at hr
    rw [RegUpd.gpr_write, ite_eq_right hr]
  · intro r _
    exact congrFun (vpr_write s d x) r

theorem Local.writeV (s : State) (d : VReg) (x : BitVec 128) : Local [] [d] s (s.writeV d x) := by
  refine ⟨⟨fun r _ => congrFun (gpr_writeV s d x) r, rd_writeV .., wr_writeV ..⟩, ?_, mem_writeV ..⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  rw [vpr_writeV, ite_eq_right hr]

theorem load_ok (d : VReg) (p : Reg) (s : State) (hp : p ≠ .r0) (hd : d ≠ mask)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr p) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.load d p)) s fun t =>
      t.vpr d = rev128 (s.mem.read (s.gpr p) 16) ∧ VOnly [d] s t := by
  refine WP.mono (loadPerm_ok d p mask byteMask s hp hd h0 hm hr) fun t ⟨hv, ho⟩ => ⟨?_, ho⟩
  rw [hv, perm_flip, flip_load]

theorem keyed_ok (op : VReg → Instr) (f : BitVec 128 → BitVec 128 → BitVec 128)
    (he : ∀ b s, exec (op b) s = some (s.writeV b (f (s.vpr b) (s.vpr key))))
    (rs : List VReg) (s : State) (hn : rs.Nodup) (hk : key ∉ rs)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.load key .r9 ++ rs.map op)) s fun t =>
      (∀ b ∈ rs, t.vpr b = f (s.vpr b) (rev128 (s.mem.read (s.gpr .r9) 16))) ∧
      VOnly (key :: rs) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (load_ok key .r9 s (by decide) (by decide) h0 hm hr) fun u ⟨hv, ho⟩ => ?_
  refine WP.mono (vector_map op f key he rs u hn hk) fun t ⟨hv', ho'⟩ => ⟨?_, ho.trans ho'⟩
  intro b hb
  have hbk : b ≠ key := fun he => hk (he ▸ hb)
  rw [hv' b hb, ho.v b (by simpa only [List.mem_singleton] using hbk), hv]

theorem round_ok (inverse last : Bool) (rs : List VReg) (s : State) (hn : rs.Nodup) (hk : key ∉ rs)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.round inverse last rs)) s fun t =>
      (∀ b ∈ rs, t.vpr b = vcipher inverse last (s.vpr b) (rev128 (s.mem.read (s.gpr .r9) 16))) ∧
      VOnly (key :: rs) s t :=
  keyed_ok (fun b => .vop (.cipher inverse last b b key)) (vcipher inverse last)
    (fun _ _ => rfl) rs s hn hk h0 hm hr

theorem setMask_ok (d : VReg) (x : BitVec 128) (s : State) (hd0 : d ≠ .v0) (hd1 : d ≠ .v1)
    (hz : s.vpr .v0 = 0) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.setMask d x)) s fun t =>
      t.vpr d = x ∧ Local [.r11, .r12] [d, .v1] s t := by
  rw [Impl.Aes.PPC64LE.Crypto.setMask]
  repeat rw [WP.block_append_iff]
  refine WP.mono (const64_ok .r11 (x.extractLsb' 64 64) s) fun u hu => ?_
  subst u
  refine WP.mono (const64_ok .r12 (x.extractLsb' 0 64) _) fun u hu => ?_
  subst u
  refine WP.mono (pair_ok d .v1 .v0 .r11 .r12 _ hd1 hd0 (by decide) (by
    simpa only [vpr_write] using hz)) fun t ⟨hv, ho⟩ => ⟨?_, ?_⟩
  · calc
      t.vpr d = x.extractLsb' 64 64 ++ x.extractLsb' 0 64 := by
        simpa only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false] using hv
      _ = x := BitVec.extractLsb'_append_extractLsb'
  · have hl := ((Local.write s .r11 (x.extractLsb' 64 64)).trans
        (Local.write _ .r12 (x.extractLsb' 0 64))).trans (Local.of_vector ho)
    exact hl.weaken (by simp) (by simp)


theorem setup_ok (s : State) : WP isa (.block Impl.Aes.PPC64LE.Crypto.setup) s fun t =>
    t.gpr .r0 = 0 ∧ t.vpr mask = byteMask ∧ t.vpr .v0 = 0 ∧ Local [.r0, .r11, .r12] [.v0, .v1, mask] s t := by
  rw [Impl.Aes.PPC64LE.Crypto.setup, WP.block_append_iff]
  have hstart : WP isa (.block [.li .r0 0, .vop (.logic .xor .v0 .v0 .v0)]) s
      (· = (s.write .r0 0).writeV .v0 0) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval,
      show 0 < 2^15 by decide, ite_true, Option.map_some, BitVec.xor_self, BitVec.ofNat_eq_ofNat,
      Option.some.injEq, exists_eq_left']
  refine WP.mono hstart fun u hu => ?_
  subst u
  have hzero : ((s.write .r0 0).writeV .v0 0).vpr .v0 = 0 := by
    simp only [vpr_writeV, ite_true]
  refine WP.mono (setMask_ok mask byteMask _ (by decide) (by decide) hzero) fun t ⟨hm, he⟩ => ⟨?_, hm, ?_, ?_⟩
  · rw [he.keep.gpr (by decide), gpr_writeV, RegUpd.gpr_write_self]
  · rw [he.v .v0 (by decide)]; exact hzero
  · exact (((Local.write s .r0 0).trans (Local.writeV _ .v0 0)).trans he).weaken (by simp) (by simp)

theorem blocks_setup_ok (s : State) :
    WP isa (.block ([Impl.Aes.PPC64LE.Crypto.mov .r7 .r6, Impl.Aes.PPC64LE.Crypto.mov .r6 .r5] ++
      Impl.Aes.PPC64LE.Crypto.setup)) s fun t =>
      t.gpr .r6 = s.gpr .r5 ∧ t.gpr .r7 = s.gpr .r6 ∧ t.gpr .r0 = 0 ∧
      t.vpr mask = byteMask ∧ Local [.r0, .r6, .r7, .r11, .r12] [.v0, .v1, mask] s t := by
  rw [WP.block_append_iff]
  have hm : WP isa (.block [Impl.Aes.PPC64LE.Crypto.mov .r7 .r6, Impl.Aes.PPC64LE.Crypto.mov .r6 .r5]) s
      (· = (s.write .r7 (s.gpr .r6)).write .r6 (s.gpr .r5)) := by
    apply WP.of_runBlock
    simp only [Impl.Aes.PPC64LE.Crypto.mov, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.or_self, Option.some.injEq, exists_eq_left']
  refine WP.mono hm fun u hu => ?_
  subst u
  refine WP.mono (setup_ok _) fun t ⟨h0, hmask, _, he⟩ => ⟨?_, ?_, h0, hmask, ?_⟩
  · rw [he.keep.gpr (by decide), RegUpd.gpr_write_self]
  · rw [he.keep.gpr (by decide), RegUpd.gpr_write, ite_eq_right (by decide), RegUpd.gpr_write_self]
  · exact (((Local.write s .r7 (s.gpr .r6)).trans (Local.write _ .r6 (s.gpr .r5))).trans he).weaken
      (by simp [or_left_comm]) (by simp)

theorem counter_ok (b : VReg) (s : State)
    (hc : s.vpr Impl.Aes.PPC64LE.Crypto.counterMask = Impl.Aes.PPC64LE.Crypto.counterControl) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.counter b)) s fun t =>
      t.vpr b = (s.vpr Impl.Aes.PPC64LE.Crypto.counterBase).extractLsb' 32 96 ++ (s.gpr .r8).extractLsb' 0 32 ∧
      t.gpr .r8 = s.gpr .r8 + 1 ∧
      Local [.r8] [b, Impl.Aes.PPC64LE.Crypto.counterWord] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.counter, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, reduceVOpEval, Option.map_some, vpr_writeV, gpr_writeV,
    reduceCtorEq, ne_eq, not_false_eq_true, ite_false, hc, counter_value, ite_true,
    show 1 < 2^15 by decide, and_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_, ?_⟩⟩
  · simp only [vpr_write, vpr_writeV, ite_true]
  · simp only [RegUpd.gpr_write_self, BitVec.ofNat_eq_ofNat]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false, gpr_writeV]
  · simp only [RegUpd.rd_write, rd_writeV]
  · simp only [RegUpd.wr_write, wr_writeV]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_write, vpr_writeV, hr.1, hr.2, ite_false]
  · simp only [RegUpd.mem_write, mem_writeV]


def inputVector (ctr : Bool) (s : State) : BitVec 128 :=
  if ctr then (s.vpr Impl.Aes.PPC64LE.Crypto.counterBase).extractLsb' 32 96 ++ (s.gpr .r8).extractLsb' 0 32
  else rev128 (s.mem.read (s.gpr .r6) 16)

theorem readBlock_ok (ctr : Bool) (b : VReg) (s : State) (hb : b ≠ mask)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hc : ctr = true → s.vpr Impl.Aes.PPC64LE.Crypto.counterMask = Impl.Aes.PPC64LE.Crypto.counterControl)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.readBlock ctr b)) s fun t =>
      t.vpr b = inputVector ctr s ∧
      t.gpr .r6 = (if ctr then s.gpr .r6 else s.gpr .r6 + 16) ∧
      t.gpr .r8 = (if ctr then s.gpr .r8 + 1 else s.gpr .r8) ∧
      Local [.r6, .r8] [b, Impl.Aes.PPC64LE.Crypto.counterWord] s t := by
  cases ctr
  · simp only [Impl.Aes.PPC64LE.Crypto.readBlock, inputVector, Bool.false_eq_true, ite_false]
    rw [WP.block_append_iff]
    refine WP.mono (load_ok b .r6 s (by decide) hb h0 hm hr) fun u ⟨hv, ho⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_addi' (d := .r6) (n := .r6) (imm := 16) (by decide), Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [vpr_write] using hv
    · simp only [RegUpd.gpr_write_self, ho.gpr, BitVec.ofNat_eq_ofNat]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ho.gpr]
    · exact ((Local.of_vector ho).trans (Local.write u .r6 (u.gpr .r6 + BitVec.ofNat 64 16))).weaken
        (by simp) (by simp)
  · simp only [Impl.Aes.PPC64LE.Crypto.readBlock, inputVector, ite_true]
    refine WP.mono (counter_ok b s (hc rfl)) fun t ⟨hv, hg, hf⟩ => ⟨hv, ?_, hg, ?_⟩
    · exact hf.keep.gpr (by decide : Reg.r6 ∉ [Reg.r8])
    · exact hf.weaken (by simp) (by simp)

theorem storePerm_ok (d n : VReg) (p offset : Reg) (s : State) (hp : p ≠ .r0)
    (hm : s.vpr mask = byteMask) (hw : InRegions s.wr (s.gpr p+s.gpr offset) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.storePerm d n p offset)) s
      (· = {s.writeV d (flip (s.vpr n)) with
        mem := s.mem.write (s.gpr p+s.gpr offset) 16 (rev128 (s.vpr n))}) := by
  have hw' : InRegions (s.writeV d (flip (s.vpr n))).wr
      ((s.writeV d (flip (s.vpr n))).gpr p + (s.writeV d (flip (s.vpr n))).gpr offset) 16 := by
    simpa only [wr_writeV, gpr_writeV] using hw
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.storePerm, runBlock_cons, runStep_some, runBlock_nil,
    exec_flip d n s hm, exec_stxvd2x d p offset _ hp hw', gpr_writeV, mem_writeV,
    vpr_writeV, ite_true, flip_store, Option.some.injEq, exists_eq_left']

theorem store_ok (b : VReg) (p : Reg) (s : State) (hp : p ≠ .r0)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask) (hw : InRegions s.wr (s.gpr p) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.store b p)) s
      (· = {s.writeV b (flip (s.vpr b)) with mem := s.mem.write (s.gpr p) 16 (rev128 (s.vpr b))}) := by
  have hs := storePerm_ok b b p .r0 s hp hm
    (by simpa only [h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw)
  simpa only [Impl.Aes.PPC64LE.Crypto.store, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hs


structure Stored (b : VReg) (s t : State) (out : BitVec 128) : Prop where
  mem : t.mem = s.mem.write (s.gpr .r6) 16 (rev128 out)
  ptr : t.gpr .r6 = s.gpr .r6 + 16
  keep : Keep [.r6] s t
  v : ∀ r, r ∉ [b, Impl.Aes.PPC64LE.Crypto.data] → t.vpr r = s.vpr r

theorem storeAdvance_ok (b : VReg) (s : State) (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hw : InRegions s.wr (s.gpr .r6) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.storeAdvance b)) s fun t => Stored b s t (s.vpr b) := by
  rw [Impl.Aes.PPC64LE.Crypto.storeAdvance, WP.block_append_iff]
  refine WP.mono (store_ok b .r6 s (by decide) h0 hm hw) fun u hu => ?_
  subst u
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_addi' (d := .r6) (n := .r6) (imm := 16) (by decide),
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_⟩
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.gpr_write_self, gpr_writeV, BitVec.ofNat_eq_ofNat]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false, gpr_writeV]
  · simp only [RegUpd.rd_write, rd_writeV]
  · simp only [RegUpd.wr_write, wr_writeV]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_write, vpr_writeV, hr.1, ite_false]

def outputAt (ctr : Bool) (v : BitVec 128) (m : Mem) (p : Addr) : BitVec 128 :=
  if ctr then v ^^^ rev128 (m.read p 16) else v

def outputVector (ctr : Bool) (b : VReg) (s : State) : BitVec 128 :=
  outputAt ctr (s.vpr b) s.mem (s.gpr .r6)

theorem writeBlock_ok (ctr : Bool) (b : VReg) (s : State) (hb : b ≠ mask)
    (hd : b ≠ Impl.Aes.PPC64LE.Crypto.data) (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hw : InRegions s.wr (s.gpr .r6) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.writeBlock ctr b)) s fun t => Stored b s t (outputVector ctr b s) := by
  cases ctr
  · simpa only [Impl.Aes.PPC64LE.Crypto.writeBlock, outputVector, outputAt, Bool.false_eq_true,
      ite_false, List.nil_append] using storeAdvance_ok b s h0 hm hw
  · simp only [Impl.Aes.PPC64LE.Crypto.writeBlock, outputVector, outputAt, ite_true]
    rw [WP.block_append_iff, WP.block_append_iff]
    have hr : InRegions (s.rd ++ s.wr) (s.gpr .r6) 16 := by
      obtain ⟨r, hr, hc⟩ := hw
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine WP.mono (load_ok Impl.Aes.PPC64LE.Crypto.data .r6 s (by decide) (by decide) h0 hm hr)
      fun u ⟨hv, ho⟩ => ?_
    refine WP.mono (vector_step (.vop (.logic .xor b b Impl.Aes.PPC64LE.Crypto.data)) b
      (u.vpr b ^^^ u.vpr Impl.Aes.PPC64LE.Crypto.data) u (by rfl)) fun w ⟨hx, ho'⟩ => ?_
    have hg : w.gpr = s.gpr := ho'.gpr.trans ho.gpr
    have hmem : w.mem = s.mem := ho'.mem.trans ho.mem
    have hmask : w.vpr mask = byteMask := (ho'.v mask (by simpa only [List.mem_singleton] using Ne.symm hb)).trans
      ((ho.v mask (by decide)).trans hm)
    have hz : w.gpr .r0 = 0 := (congrFun hg .r0).trans h0
    have hw' : InRegions w.wr (w.gpr .r6) 16 := by rw [ho'.wr, ho.wr, hg]; exact hw
    have hval : w.vpr b = s.vpr b ^^^ rev128 (s.mem.read (s.gpr .r6) 16) := by
      rw [hx, ho.v b (by simpa only [List.mem_singleton] using hd), hv]
    refine WP.mono (storeAdvance_ok b w hz hmask hw') fun t ht => ?_
    refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_⟩
    · rw [ht.mem, hmem, hg, hval]
    · rw [ht.ptr, hg]
    · exact (ht.keep.gpr hr).trans (congrFun hg r)
    · exact ht.keep.2.1.trans (ho'.rd.trans ho.rd)
    · exact ht.keep.2.2.trans (ho'.wr.trans ho.wr)
    · rw [ht.v r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [ho'.v r (by simpa only [List.mem_singleton] using hr.1),
        ho.v r (by simpa only [List.mem_singleton] using hr.2)]

end VG.Proof.Aes.PPC64LE.Crypto
