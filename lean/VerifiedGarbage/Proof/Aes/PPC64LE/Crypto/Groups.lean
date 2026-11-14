module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Value
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

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

theorem counter_ok (b : VReg) (s : State) (hb : b ≠ Impl.Aes.PPC64LE.Crypto.counterBase)
    (hbs : b ≠ Impl.Aes.PPC64LE.Crypto.counterStep)
    (hc : s.vpr Impl.Aes.PPC64LE.Crypto.counterStep = Impl.Aes.PPC64LE.Crypto.counterOne) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.counter b)) s fun t =>
      t.vpr b = s.vpr Impl.Aes.PPC64LE.Crypto.counterBase ∧
      t.vpr Impl.Aes.PPC64LE.Crypto.counterBase = ctrAdd (s.vpr Impl.Aes.PPC64LE.Crypto.counterBase) 1 ∧
      Local [] [b, Impl.Aes.PPC64LE.Crypto.counterBase] s t := by
  rw [Impl.Aes.PPC64LE.Crypto.counter, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (vector_step (.vop (.logic .or b Impl.Aes.PPC64LE.Crypto.counterBase
    Impl.Aes.PPC64LE.Crypto.counterBase)) b (s.vpr Impl.Aes.PPC64LE.Crypto.counterBase) s
    (by simp only [reduceExec, reduceVOpEval, BitVec.or_self, Option.map_some])) fun u ⟨hu, ho⟩ => ?_
  have hcb : u.vpr Impl.Aes.PPC64LE.Crypto.counterBase = s.vpr Impl.Aes.PPC64LE.Crypto.counterBase :=
    ho.v _ (by simpa only [List.mem_singleton] using hb.symm)
  have hst : u.vpr Impl.Aes.PPC64LE.Crypto.counterStep = Impl.Aes.PPC64LE.Crypto.counterOne :=
    (ho.v _ (by simpa only [List.mem_singleton] using hbs.symm)).trans hc
  refine WP.mono (vector_step (.vop (.add false Impl.Aes.PPC64LE.Crypto.counterBase
    Impl.Aes.PPC64LE.Crypto.counterBase Impl.Aes.PPC64LE.Crypto.counterStep))
    Impl.Aes.PPC64LE.Crypto.counterBase (ctrAdd (s.vpr Impl.Aes.PPC64LE.Crypto.counterBase) 1) u
    (by simp only [reduceExec, reduceVOpEval, Bool.false_eq_true, ite_false, Option.map_some, hst, hcb,
      counter_step])) fun t ⟨ht, ho'⟩ => ⟨?_, ht, (Local.of_vector (ho.trans ho')).weaken (by simp) (by simp)⟩
  rw [ho'.v b (by simpa only [List.mem_singleton] using hb), hu]

def inputVector (ctr : Bool) (s : State) : BitVec 128 :=
  if ctr then s.vpr Impl.Aes.PPC64LE.Crypto.counterBase else rev128 (s.mem.read (s.gpr .r6) 16)

theorem readBlock_ok (ctr : Bool) (b : VReg) (s : State) (hb : b ≠ mask)
    (hbc : b ≠ Impl.Aes.PPC64LE.Crypto.counterBase) (hbs : b ≠ Impl.Aes.PPC64LE.Crypto.counterStep)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hc : ctr = true → s.vpr Impl.Aes.PPC64LE.Crypto.counterStep = Impl.Aes.PPC64LE.Crypto.counterOne)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.readBlock ctr b)) s fun t =>
      t.vpr b = inputVector ctr s ∧
      t.gpr .r6 = (if ctr then s.gpr .r6 else s.gpr .r6 + 16) ∧
      t.vpr Impl.Aes.PPC64LE.Crypto.counterBase = (if ctr then ctrAdd (s.vpr Impl.Aes.PPC64LE.Crypto.counterBase) 1
        else s.vpr Impl.Aes.PPC64LE.Crypto.counterBase) ∧
      Local [.r6] [b, Impl.Aes.PPC64LE.Crypto.counterBase] s t := by
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
    · simp only [vpr_write]; exact ho.v _ (by simpa only [List.mem_singleton] using hbc.symm)
    · exact ((Local.of_vector ho).trans (Local.write u .r6 (u.gpr .r6 + BitVec.ofNat 64 16))).weaken
        (by simp) (by simp)
  · simp only [Impl.Aes.PPC64LE.Crypto.readBlock, inputVector, ite_true]
    refine WP.mono (counter_ok b s hbc hbs (hc rfl)) fun t ⟨hv, hg, hf⟩ => ⟨hv, ?_, hg, ?_⟩
    · exact hf.keep.gpr (by decide : Reg.r6 ∉ ([] : List Reg))
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


/-- A block stored at `r6 + o`, and `r6` advanced. -/
structure Stored (b : VReg) (o : Reg) (s t : State) (out : BitVec 128) : Prop where
  mem : t.mem = s.mem.write (s.gpr .r6 + s.gpr o) 16 (rev128 out)
  ptr : t.gpr .r6 = s.gpr .r6 + 16
  keep : Keep [.r6] s t
  v : ∀ r, r ∉ [b, Impl.Aes.PPC64LE.Crypto.data] → t.vpr r = s.vpr r

theorem storeAdvance_ok (b : VReg) (o : Reg) (s : State) (hm : s.vpr mask = byteMask)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr o) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.storeAdvance b o)) s fun t => Stored b o s t (s.vpr b) := by
  rw [Impl.Aes.PPC64LE.Crypto.storeAdvance, WP.block_append_iff]
  refine WP.mono (storePerm_ok b b .r6 o s (by decide) hm hw) fun u hu => ?_
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

theorem swapDwords_xor (x y : BitVec 128) : swapDwords (x ^^^ y) = swapDwords x ^^^ swapDwords y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_swapDwords _ hi, BitVec.getLsbD_xor]

def outputAt (ctr : Bool) (v : BitVec 128) (m : Mem) (p : Addr) : BitVec 128 :=
  if ctr then v ^^^ rev128 (m.read p 16) else v

def outputVector (ctr : Bool) (b : VReg) (s : State) : BitVec 128 :=
  outputAt ctr (s.vpr b) s.mem (s.gpr .r6)

theorem writeBlock_ok (ctr : Bool) (b : VReg) (o : Reg) (s : State)
    (hd : b ≠ Impl.Aes.PPC64LE.Crypto.data) (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6) 16) (hw : InRegions s.wr (s.gpr .r6 + s.gpr o) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.writeBlock ctr b o)) s fun t =>
      Stored b o s t (outputVector ctr b s) := by
  cases ctr
  · simpa only [Impl.Aes.PPC64LE.Crypto.writeBlock, outputVector, outputAt, Bool.false_eq_true,
      ite_false, List.nil_append] using storeAdvance_ok b o s hm hw
  · simp only [Impl.Aes.PPC64LE.Crypto.writeBlock, outputVector, outputAt, ite_true]
    have hr0 : InRegions (s.rd ++ s.wr) (s.gpr .r6 + s.gpr .r0) 16 := by
      rw [h0]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hr
    refine WP.cons (exec_lxvd2x Impl.Aes.PPC64LE.Crypto.data .r6 .r0 s (by decide) hr0) ?_
    refine WP.cons (exec_flip b b _ (by rw [vpr_writeV, ite_eq_right (by decide)]; exact hm)) ?_
    refine WP.cons (show exec (.vop (.logic .xor b b Impl.Aes.PPC64LE.Crypto.data)) _ = some _ from rfl) ?_
    refine WP.cons (exec_stxvd2x b .r6 o _ (by decide) (by simpa only [wr_writeV, gpr_writeV] using hw)) ?_
    refine WP.cons (exec_addi' (d := .r6) (n := .r6) (imm := 16) (by decide)) (wp_nil ?_)
    simp only [vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV, ite_true, ite_eq_right hd, h0,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Impl.Aes.PPC64LE.Crypto.data ≠ b from Ne.symm hd, ite_false]
    refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_⟩
    · simp only [RegUpd.mem_write]
      rw [swapDwords_xor, flip_store, swapDwords_involutive, rev128_xor, rev128_rev128]
    · simp only [RegUpd.gpr_write_self]; rfl
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [RegUpd.rd_write]
    · simp only [RegUpd.wr_write]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [vpr_write, vpr_writeV, hr.1, hr.2, ite_false]

end VG.Proof.Aes.PPC64LE.Crypto
