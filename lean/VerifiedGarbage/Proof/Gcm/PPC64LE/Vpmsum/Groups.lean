module

public import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Gcm.Clmul.Ops
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Gcm.PPC64LE.Base
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm

-- separate module: the symbolic executions are reused by the block loop and key setup.
/-! # POWER8 GHASH instruction groups -/

@[expose] public section
namespace VG.Proof.Gcm.PPC64LE.Vpmsum

open VG VG.PPC64LE
open VG.Impl.Gcm.PPC64LE.Vpmsum (Y C U LO MID HI A T H MASK Z)
open VG.Proof.Gcm.Clmul
open VG.Impl.Gcm.Clmul (poly xInv2Hi)
open VG.VectorCrypto (polyMul)

local notation "dw" => VG.Proof.Gcm.Clmul.vdword

def half (n m : BitVec 128) : BitVec 128 := dw n 0 ++ dw m 1

theorem half_self (v : BitVec 128) : half v v = ext8 v v := by
  rw [half, ext8_eq]

theorem dw_zero (i : Nat) : dw (0#128) i = 0#64 := by
  simp only [VG.Proof.Gcm.Clmul.vdword, BitVec.extractLsb'_zero]

theorem pm_zero (b : BitVec 64) : polyMul (0#64) b = 0#128 := polyMul_zero_left b

theorem exec_shift8 (d n m : VReg) (s : State) :
    exec (.vop (.sldoi d n m 8)) s = some (s.writeV d (half (s.vpr n) (s.vpr m))) := by
  change some (s.writeV d (((s.vpr n ++ s.vpr m) <<< 64).extractLsb' 128 128)) = _
  rw [sldoi8_eq]
  rfl

theorem exec_pm (d n m : VReg) (s : State) :
    exec (.vop (.pmsumd d n m)) s = some (s.writeV d
      (polyMul (dw (s.vpr n) 0) (dw (s.vpr m) 0) ^^^
       polyMul (dw (s.vpr n) 1) (dw (s.vpr m) 1))) := by
  change some (s.writeV d
    (polyMul (dw (s.vpr n) 1) (dw (s.vpr m) 1) ^^^
     polyMul (dw (s.vpr n) 0) (dw (s.vpr m) 0))) = _
  rw [BitVec.xor_comm]

theorem exec_xor (d n m : VReg) (s : State) :
    exec (.vop (.logic .xor d n m)) s = some (s.writeV d (s.vpr n ^^^ s.vpr m)) := rfl

def prod (s : State) : VG.Proof.Gcm.Clmul.Prod := ⟨s.vpr LO, s.vpr MID, s.vpr HI⟩

def Free (r : VReg) : Prop := r ≠ U ∧ r ≠ LO ∧ r ≠ MID ∧ r ≠ HI ∧ r ≠ T

theorem products_ok (a key : VReg) (s : State) (ha : Free a) (hk : Free key) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.products a key)) s fun s' =>
      prod s' = VG.Proof.Gcm.Clmul.Prod.zero.acc (s.vpr a) (ext8 (s.vpr key) (s.vpr key)) (s.vpr key) ∧
      VOnly [U, LO, MID, HI] s s' := by
  obtain ⟨ha2, ha3, ha4, ha5, -⟩ := ha
  obtain ⟨hk2, hk3, hk4, hk5, -⟩ := hk
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.products, runBlock_cons, runStep_some, runBlock_nil,
    exec_shift8, exec_pm, vpr_writeV, Option.some.injEq, exists_eq_left',
    ha2, ha3, ha5, hk2, hk3, hk5, ite_true, ite_false, reduceCtorEq]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [prod, vpr_writeV, ite_true, ite_false, reduceCtorEq, hz,
      VG.Proof.Gcm.Clmul.Prod.zero, VG.Proof.Gcm.Clmul.Prod.acc,
      half, vdword_append_0, vdword_append_1, vdword_ext8_0, vdword_ext8_1,
      dw_zero, pm_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, BitVec.xor_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (d : VReg) (s : State) (hc : s.vpr C = poly ++ poly) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.reduce d)) s fun s' =>
      s'.vpr d = VG.Proof.Gcm.Clmul.reduce (prod s) ∧ VOnly [LO, MID, HI, T, d] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.reduce, runBlock_cons, runStep_some, runBlock_nil,
    exec_shift8, exec_pm, exec_xor, vpr_writeV, Option.some.injEq, exists_eq_left',
    ite_true, ite_false, reduceCtorEq]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [prod, VG.Proof.Gcm.Clmul.reduce,
      hc, hz, half, vdword_append_0, vdword_append_1, dw_zero,
      pm_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, ext8_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem mul_ok (d a key : VReg) (s : State) (ha : Free a) (hk : Free key)
    (hc : s.vpr C = poly ++ poly) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.mul d a key)) s fun s' =>
      s'.vpr d = mulV (s.vpr a) (s.vpr key) ∧ VOnly [U, LO, MID, HI, T, d] s s' := by
  rw [Impl.Gcm.PPC64LE.Vpmsum.mul, WP.block_append_iff]
  refine WP.mono (products_ok a key s ha hk hz) fun s₁ ⟨hp, ho⟩ => ?_
  have hc₁ : s₁.vpr C = poly ++ poly := (ho.v C (by decide)).trans hc
  have hz₁ : s₁.vpr Z = 0 := (ho.v Z (by decide)).trans hz
  refine WP.mono (reduce_ok d s₁ hc₁ hz₁) fun s₂ ⟨hr, ho'⟩ => ⟨?_, ?_⟩
  · rw [hr, hp]; rfl
  · exact (ho.trans ho').weaken (by
      intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h | h) | (h | h | h | h | h) <;> simp_all)



theorem const64_ok (d : Reg) (x : BitVec 64) (s : State) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.const64 d x)) s (· = s.write d x) := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.const64, runBlock_cons, runStep_some,
    runBlock_nil, reduceExec, show 32 < 64 by decide, ite_true, RegUpd.gpr_write_self, write_overwrite,
    movImm64_eq, Option.some.injEq, exists_eq_left']

theorem pair_ok (d : VReg) (hi lo : Reg) (s : State)
    (hd : d ≠ T) (hdz : d ≠ Z) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.pair d hi lo)) s fun s' =>
      s'.vpr d = s.gpr hi ++ s.gpr lo ∧ VOnly [d, T] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.pair, runBlock_cons, runStep_some, runBlock_nil,
    exec_shift8, reduceExec, vpr_writeV, gpr_writeV, Option.some.injEq, exists_eq_left',
    hd, Ne.symm hd, Ne.symm hdz, ite_true, ite_false, reduceCtorEq]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [half, hz, BitVec.ofNat_eq_ofNat, dw_zero, vdword_append_0, vdword_append_1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2, ite_false]

theorem rev128_append (a b : BitVec 64) : rev128 (a ++ b) = rev64 b ++ rev64 a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rev128 _ hi, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h : i < 64
  · rw [ite_eq_left h, ite_eq_right (show ¬8*(15-i/8)+i%8 < 64 by omega)]
    have e := VG.Proof.Gcm.getLsbD_byteRev64 a i h
    change _ = (VG.byteRev64 a).getLsbD i
    rw [e]
    exact congrArg a.getLsbD (by omega)
  · rw [ite_eq_right h, ite_eq_left (show 8*(15-i/8)+i%8 < 64 by omega)]
    have e := VG.Proof.Gcm.getLsbD_byteRev64 b (i-64) (by omega)
    change _ = (VG.byteRev64 b).getLsbD (i-64)
    rw [e]
    exact congrArg b.getLsbD (by omega)

theorem swap_eq (x : BitVec 128) : swapDwords x = ext8 x x := by
  rw [ext8_eq]
  rfl

theorem load_value (m : Mem) (p : Addr) :
    rev128 (swapDwords (m.read p 16)) = ext8 (Spec.Gcm.blockAt m p) (Spec.Gcm.blockAt m p) := by
  rw [swap_eq, ext8_eq, vdword_read16 m p (by decide), vdword_read16 m p (by decide),
    rev128_append, ← blockAt_rev, ext8_eq, vdword_append_0, vdword_append_1]

theorem store_value (m : Mem) (p : Addr) (v : BitVec 128) :
    Spec.Gcm.blockAt (m.write p 16 (swapDwords (rev128 v))) p = ext8 v v := by
  have h := load_value (m.write p 16 (swapDwords (rev128 v))) p
  rw [read_write16, swap_eq, swap_eq, ext8_ext8, rev128_rev128] at h
  have e := congrArg (fun w => ext8 w w) h
  rw [ext8_ext8] at e
  rw [swap_eq]
  exact e.symm

theorem mask_byte {i : Nat} (hi : i < 16) :
    (vbyte Impl.Gcm.PPC64LE.Vpmsum.reverseMask i).toNat % 32 = 15-i := by
  have h : ∀ i : Fin 16,
      (vbyte Impl.Gcm.PPC64LE.Vpmsum.reverseMask i).toNat % 32 = 15-i.val := by decide
  exact h ⟨i, hi⟩

theorem exec_reverse (d n : VReg) (s : State)
    (hm : s.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask) :
    exec (.vop (.perm d n n MASK)) s = some (s.writeV d (rev128 (s.vpr n))) := by
  simp only [reduceExec, reduceVOpEval, hm, Option.map_some]
  apply congrArg (fun x => some (s.writeV d x))
  apply ofVBytes_congr
  intro i hi
  rw [mask_byte hi, ite_eq_left (show 15-i < 16 by omega)]

theorem loadRev_ok (d : VReg) (p : Reg) (s : State) (hp : p ≠ .r0)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask)
    (hd : d ≠ MASK) (hr : InRegions (s.rd ++ s.wr) (s.gpr p) 16) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.loadRev d p)) s fun s' =>
      s'.vpr d = ext8 (Spec.Gcm.blockAt s.mem (s.gpr p)) (Spec.Gcm.blockAt s.mem (s.gpr p)) ∧
      VOnly [d] s s' := by
  have hx : exec (.lxvd2x d p .r0) s = some (s.writeV d (swapDwords (s.mem.read (s.gpr p) 16))) := by
    simp only [reduceExec, addrX, hp, ne_eq, not_false_eq_true, ite_true, h0,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.bind_some, State.load, hr, Option.map_some]
  have hm' : (s.writeV d (swapDwords (s.mem.read (s.gpr p) 16))).vpr MASK =
      Impl.Gcm.PPC64LE.Vpmsum.reverseMask := by
    simpa only [vpr_writeV, Ne.symm hd, ite_false] using hm
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.loadRev, runBlock_cons, runStep_some, runBlock_nil,
    hx, exec_reverse _ _ _ hm', Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [vpr_writeV, ite_true, load_value]
  · have hrd : r ≠ d := by simpa only [List.mem_singleton] using hr
    simp only [vpr_writeV, hrd, ite_false]

/-- Scalar state shared by setup and every vector-only group. -/
structure Stable (s s' : State) : Prop where
  regs : ∀ r, r ∉ [.r0, .r8, .r9] → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Stable.refl (s : State) : Stable s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Stable.trans {s t u : State} (h : Stable s t) (h' : Stable t u) : Stable s u :=
  ⟨fun r hr => (h'.regs r hr).trans (h.regs r hr),
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem VOnly.stable {rs : List VReg} {s t : State} (h : VG.PPC64LE.VOnly rs s t) : Stable s t :=
  ⟨fun r _ => congrFun h.gpr r, h.mem, h.rd, h.wr⟩

theorem Stable.write {s t : State} (h : Stable s t) (d : Reg) (x : BitVec 64)
    (hd : d ∈ [.r0, .r8, .r9]) : Stable s (t.write d x) := by
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write, ite_eq_right (show r ≠ d from fun he => hr (he ▸ hd))]
    exact h.regs r hr
  · exact (RegUpd.mem_write ..).trans h.mem
  · exact (RegUpd.rd_write ..).trans h.rd
  · exact (RegUpd.wr_write ..).trans h.wr

structure Config (s : State) : Prop where
  zero : s.gpr .r0 = 0
  c : s.vpr C = poly ++ poly
  mask : s.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask
  z : s.vpr Z = 0

theorem consts_ok (s : State) :
    WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.consts) s fun t =>
      Config t ∧ t.vpr H = xInv2 ∧ Stable s t := by
  rw [Impl.Gcm.PPC64LE.Vpmsum.consts]
  repeat rw [WP.block_append_iff]
  have hz0 : WP isa (.block [.li .r0 0, .vop (.logic .xor Z Z Z)]) s
      (· = (s.write .r0 0).writeV Z 0) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_xor, reduceExec, show 0 < 2^15 by decide, ite_true, BitVec.ofNat_eq_ofNat,
      vpr_write, BitVec.xor_self, Option.some.injEq, exists_eq_left']
  refine WP.mono hz0 fun t ht => ?_
  subst t
  refine WP.mono (const64_ok .r8 poly _) fun t ht => ?_
  subst t
  have hz : (((s.write .r0 0).writeV Z 0).write .r8 poly).vpr Z = 0 := by
    simp only [vpr_write, vpr_writeV, ite_true]
  refine WP.mono (pair_ok C .r8 .r8 _ (by decide) (by decide) hz) fun t ⟨hc, hct⟩ => ?_
  have hc' : t.vpr C = poly ++ poly := by simpa only [RegUpd.gpr_write_self] using hc
  have hz' : t.vpr Z = 0 := by simpa only [vpr_write, vpr_writeV, ite_true] using hct.v Z (by decide)
  refine WP.mono (const64_ok .r8 (Impl.Gcm.PPC64LE.Vpmsum.reverseMask.extractLsb' 64 64) t)
    fun u hu => ?_
  subst u
  refine WP.mono (const64_ok .r9 (Impl.Gcm.PPC64LE.Vpmsum.reverseMask.extractLsb' 0 64) _)
    fun u hu => ?_
  subst u
  refine WP.mono (pair_ok MASK .r8 .r9 _ (by decide) (by decide) (by
    simpa only [vpr_write] using hz')) fun u ⟨hm, hmu⟩ => ?_
  have hm' : u.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask := by
    calc
      u.vpr MASK = dw Impl.Gcm.PPC64LE.Vpmsum.reverseMask 1 ++ dw Impl.Gcm.PPC64LE.Vpmsum.reverseMask 0 := by
        simpa only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, VG.Proof.Gcm.Clmul.vdword] using hm
      _ = _ := (vdwords _).symm
  have hz'' : u.vpr Z = 0 := by simpa only [vpr_write] using (hmu.v Z (by decide)).trans hz'
  refine WP.mono (const64_ok .r8 xInv2Hi u) fun w hw => ?_
  subst w
  have hli : WP isa (.block [.li .r9 3]) (u.write .r8 xInv2Hi) (· = (u.write .r8 xInv2Hi).write .r9 3) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, show 3 < 2^15 by decide, ite_true, BitVec.ofNat_eq_ofNat,
      Option.some.injEq, exists_eq_left']
  refine WP.mono hli fun w hw => ?_
  subst w
  refine WP.mono (pair_ok H .r8 .r9 _ (by decide) (by decide) (by
    simpa only [vpr_write] using hz'')) fun w ⟨hh, hhw⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [hhw.gpr, RegUpd.gpr_write, reduceCtorEq, ite_false,
      hmu.gpr, hct.gpr, gpr_writeV, ite_true]
  · simpa only [vpr_write] using (hhw.v C (by decide)).trans
      ((hmu.v C (by decide)).trans hc')
  · simpa only [vpr_write] using (hhw.v MASK (by decide)).trans hm'
  · simpa only [vpr_write] using (hhw.v Z (by decide)).trans hz''
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, xInv2, BitVec.ofNat_eq_ofNat] using hh
  · have hs : Stable s ((s.write .r0 0).writeV Z 0) :=
      ⟨fun r hr => by
        simp only [gpr_writeV, RegUpd.gpr_write]
        rw [ite_eq_right (show r ≠ .r0 from fun he => hr (by simp [he]))],
       rfl, rfl, rfl⟩
    have ht := (hs.write .r8 poly (by decide)).trans (VOnly.stable hct)
    have hu := ((ht.write .r8 _ (by decide)).write .r9 _ (by decide)).trans (VOnly.stable hmu)
    exact ((hu.write .r8 _ (by decide)).write .r9 3 (by decide)).trans (VOnly.stable hhw)

theorem vector_step (i : Instr) (d : VReg) (v : BitVec 128) (s : State)
    (he : exec i s = some (s.writeV d v)) :
    WP isa (.block [i]) s fun t => t.vpr d = v ∧ VOnly [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, he, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [vpr_writeV, ite_true], ⟨fun r hr => ?_, gpr_writeV ..,
    mem_writeV .., rd_writeV .., wr_writeV .., sp_writeV .., lr_writeV ..⟩⟩
  simp only [vpr_writeV, show r ≠ d by simpa only [List.mem_singleton] using hr, ite_false]

theorem Config.keep {rs : List VReg} {s t : State} (h : Config s) (ho : VOnly rs s t)
    (hc : C ∉ rs) (hm : MASK ∉ rs) (hz : Z ∉ rs) : Config t :=
  ⟨(congrFun ho.gpr .r0).trans h.zero, (ho.v C hc).trans h.c,
    (ho.v MASK hm).trans h.mask, (ho.v Z hz).trans h.z⟩

end VG.Proof.Gcm.PPC64LE.Vpmsum
