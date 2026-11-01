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

theorem productsWith_ok (reg : Fin 5 → VReg) (hinj : Function.Injective reg)
    (a key : VReg) (s : State) (ha : a ∉ [reg 0, reg 1, reg 2, reg 3])
    (hk : key ∉ [reg 0, reg 1, reg 2, reg 3]) (hz : s.vpr (reg 4) = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.productsWith
      (reg 0) (reg 1) (reg 2) (reg 3) (reg 4) a key)) s fun t =>
      (⟨t.vpr (reg 1), t.vpr (reg 2), t.vpr (reg 3)⟩ : VG.Proof.Gcm.Clmul.Prod) =
        VG.Proof.Gcm.Clmul.Prod.zero.acc (s.vpr a) (ext8 (s.vpr key) (s.vpr key)) (s.vpr key) ∧
      VOnly [reg 0, reg 1, reg 2, reg 3] s t := by
  have heq : ∀ i j : Fin 5, (reg i = reg j) ↔ i = j :=
    fun _ _ => ⟨fun h => hinj h, congrArg reg⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hk
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.productsWith, runBlock_cons, runStep_some, runBlock_nil,
    exec_shift8, exec_pm, vpr_writeV, Option.some.injEq, exists_eq_left',
    ha.1, ha.2.1, ha.2.2.2, hk.1, hk.2.1, hk.2.2.2,
    heq, Fin.reduceEq, ite_true, ite_false]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [hz, VG.Proof.Gcm.Clmul.Prod.zero, VG.Proof.Gcm.Clmul.Prod.acc,
      half, vdword_append_0, vdword_append_1, vdword_ext8_0, vdword_ext8_1,
      dw_zero, pm_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, BitVec.xor_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

def productRegs : Fin 5 → VReg
  | ⟨0, _⟩ => U | ⟨1, _⟩ => LO | ⟨2, _⟩ => MID | ⟨3, _⟩ => HI | _ => Z

theorem products_ok (a key : VReg) (s : State) (ha : Free a) (hk : Free key) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.products a key)) s fun s' =>
      prod s' = VG.Proof.Gcm.Clmul.Prod.zero.acc (s.vpr a) (ext8 (s.vpr key) (s.vpr key)) (s.vpr key) ∧
      VOnly [U, LO, MID, HI] s s' := by
  refine productsWith_ok productRegs
    (show ∀ i j : Fin 5, productRegs i = productRegs j → i = j from by decide) a key s ?_ ?_ hz
  · exact fun h => by
      simp only [productRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h
      · exact ha.1 h
      · exact ha.2.1 h
      · exact ha.2.2.1 h
      · exact ha.2.2.2.1 h
  · exact fun h => by
      simp only [productRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h
      · exact hk.1 h
      · exact hk.2.1 h
      · exact hk.2.2.1 h
      · exact hk.2.2.2.1 h

/-- A reduction can borrow any six distinct vector registers. -/
theorem reduceWith_ok (reg : Fin 6 → VReg) (hinj : Function.Injective reg)
    (d : VReg) (s : State) (hc : s.vpr (reg 5) = poly ++ poly) (hz : s.vpr (reg 4) = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.reduceWith
      (reg 0) (reg 1) (reg 2) (reg 3) (reg 4) (reg 5) d)) s fun t =>
      t.vpr d = VG.Proof.Gcm.Clmul.reduce ⟨s.vpr (reg 0), s.vpr (reg 1), s.vpr (reg 2)⟩ ∧
      VOnly [reg 0, reg 1, reg 2, reg 3, d] s t := by
  have heq : ∀ i j : Fin 6, (reg i = reg j) ↔ i = j :=
    fun _ _ => ⟨fun h => hinj h, congrArg reg⟩
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.reduceWith, runBlock_cons, runStep_some, runBlock_nil,
    exec_shift8, exec_pm, exec_xor, vpr_writeV, Option.some.injEq, exists_eq_left',
    heq, Fin.reduceEq, ite_true, ite_false]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [VG.Proof.Gcm.Clmul.reduce, hc, hz, half,
      vdword_append_0, vdword_append_1, dw_zero, pm_zero, BitVec.ofNat_eq_ofNat,
      BitVec.zero_xor, ext8_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

def reduceRegs : Fin 6 → VReg
  | ⟨0, _⟩ => LO | ⟨1, _⟩ => MID | ⟨2, _⟩ => HI
  | ⟨3, _⟩ => T | ⟨4, _⟩ => Z | _ => C

theorem reduce_ok (d : VReg) (s : State) (hc : s.vpr C = poly ++ poly) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.reduce d)) s fun s' =>
      s'.vpr d = VG.Proof.Gcm.Clmul.reduce (prod s) ∧ VOnly [LO, MID, HI, T, d] s s' :=
  reduceWith_ok reduceRegs (by
    exact (show ∀ i j : Fin 6, reduceRegs i = reduceRegs j → i = j from by decide)) d s hc hz

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



export VG.PPC64LE (const64_ok)

theorem pair_ok (d : VReg) (hi lo : Reg) (s : State)
    (hd : d ≠ T) (hdz : d ≠ Z) (hz : s.vpr Z = 0) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.pair d hi lo)) s fun s' =>
      s'.vpr d = s.gpr hi ++ s.gpr lo ∧ VOnly [d, T] s s' :=
  VG.PPC64LE.pair_ok d T Z hi lo s hd hdz (by decide) hz

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
  refine WP.mono (loadPerm_ok d p MASK _ s hp hd h0 hm hr) fun t ⟨hv, ho⟩ => ⟨?_, ho⟩
  rw [hv]
  have he : permSelf (swapDwords (s.mem.read (s.gpr p) 16)) Impl.Gcm.PPC64LE.Vpmsum.reverseMask =
      rev128 (swapDwords (s.mem.read (s.gpr p) 16)) := by
    apply ofVBytes_congr
    intro i hi
    rw [mask_byte hi, ite_eq_left (show 15-i < 16 by omega)]
  rw [he, load_value]

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


theorem Config.keep {rs : List VReg} {s t : State} (h : Config s) (ho : VOnly rs s t)
    (hc : C ∉ rs) (hm : MASK ∉ rs) (hz : Z ∉ rs) : Config t :=
  ⟨(congrFun ho.gpr .r0).trans h.zero, (ho.v C hc).trans h.c,
    (ho.v MASK hm).trans h.mask, (ho.v Z hz).trans h.z⟩


/-! Pure packed products are shared by standalone GHASH and fused AES-GCM. -/

def lowPair (a b : BitVec 128) : BitVec 128 := Clmul.vdword a 0 ++ Clmul.vdword b 0

def highPair (a b : BitVec 128) : BitVec 128 := Clmul.vdword a 1 ++ Clmul.vdword b 1

def pmPair (a b : BitVec 128) : BitVec 128 :=
  polyMul (Clmul.vdword a 0) (Clmul.vdword b 0) ^^^ polyMul (Clmul.vdword a 1) (Clmul.vdword b 1)

def pairedProd (a b ka kb : BitVec 128) : VG.Proof.Gcm.Clmul.Prod :=
  ⟨pmPair (highPair a b) (lowPair ka kb),
   pmPair (lowPair a b) (lowPair ka kb) ^^^ pmPair (highPair a b) (highPair ka kb),
   pmPair (lowPair a b) (highPair ka kb)⟩


def addProd (p q : VG.Proof.Gcm.Clmul.Prod) : VG.Proof.Gcm.Clmul.Prod :=
  ⟨p.lo ^^^ q.lo, p.mid ^^^ q.mid, p.hi ^^^ q.hi⟩


theorem half_swap_right (a b : BitVec 128) : half a (half b b) = lowPair a b := by
  rw [half, half, vdword_append_1]
  rfl

theorem swap_half_swap_left (a b : BitVec 128) :
    half (half (half b b) a) (half (half b b) a) = highPair a b := by
  rw [half_self, ext8_eq, half, half, vdword_append_0, vdword_append_1, vdword_append_0]
  rfl


def keyValue (h : BitVec 128) : Nat → BitVec 128
  | 0 => h
  | n+1 => ext8 (mulV (ext8 (keyValue h n) (keyValue h n)) h)
      (mulV (ext8 (keyValue h n) (keyValue h n)) h)


/-- The paired product supports both loaded GHASH blocks and canonical AES vectors. -/
theorem packedProductsWith_ok (reg : Fin 5 → VReg) (hinj : Function.Injective reg)
    (a b loKey hiKey : VReg) (canonical : Bool) (ka kb : BitVec 128) (s : State)
    (ha : ∀ i, a ≠ reg i) (hl : ∀ i, loKey ≠ reg i) (hh : ∀ i, hiKey ≠ reg i)
    (hlo : s.vpr loKey = lowPair ka kb) (hhi : s.vpr hiKey = highPair ka kb) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedProductsWith
      a b (reg 1) (reg 2) (reg 3) (reg 4) (reg 0) loKey hiKey canonical)) s fun t =>
      (⟨t.vpr (reg 3), t.vpr (reg 4), t.vpr (reg 0)⟩ : VG.Proof.Gcm.Clmul.Prod) =
        pairedProd (if canonical then ext8 (s.vpr a) (s.vpr a) else s.vpr a)
          (if canonical then ext8 (s.vpr b) (s.vpr b) else s.vpr b) ka kb ∧
      VOnly [reg 0, reg 1, reg 2, reg 3, reg 4] s t := by
  have heq : ∀ i j : Fin 5, (reg i = reg j) ↔ i = j :=
    fun _ _ => ⟨fun h => hinj h, congrArg reg⟩
  cases canonical <;> simp only [Impl.Gcm.PPC64LE.Vpmsum.packedProductsWith,Impl.Gcm.PPC64LE.Vpmsum.packedMultiplyWith,
    List.cons_append,List.nil_append,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift8, exec_pm, exec_xor,
      vpr_writeV, Option.some.injEq, exists_eq_left', ha, hl, hh, heq, Fin.reduceEq, ite_true, ite_false]
    refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
      by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
      by simp only [lr_writeV]⟩⟩
    · simp only [hlo, hhi, pairedProd, pmPair, lowPair, highPair, half,
        vdword_append_0, vdword_append_1, vdword_ext8_0, vdword_ext8_1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

def permPair (a b control : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let j := (vbyte control i).toNat % 32
    if j < 16 then vbyte a j else vbyte b (j-16)

theorem exec_permPair (d a b c : VReg) (s : State) :
    exec (.vop (.perm d a b c)) s =
      some (s.writeV d (permPair (s.vpr a) (s.vpr b) (s.vpr c))) := rfl

theorem pair_mask_control (i : Fin 16) :
    (vbyte Impl.Gcm.PPC64LE.Vpmsum.pairLowMask i).toNat % 32 =
      (if i.val<8 then i.val+8 else i.val+16) ∧
    (vbyte Impl.Gcm.PPC64LE.Vpmsum.pairHighMask i).toNat % 32 =
      (if i.val<8 then i.val else i.val+8) := by
  have h : ∀ i : Fin 16,
    (vbyte Impl.Gcm.PPC64LE.Vpmsum.pairLowMask i).toNat % 32 =
      (if i.val<8 then i.val+8 else i.val+16) ∧
    (vbyte Impl.Gcm.PPC64LE.Vpmsum.pairHighMask i).toNat % 32 =
      (if i.val<8 then i.val else i.val+8) := by decide
  exact h i

theorem permPair_halves (a b : BitVec 128) (low : Bool) :
    permPair a b (if low then Impl.Gcm.PPC64LE.Vpmsum.pairLowMask
      else Impl.Gcm.PPC64LE.Vpmsum.pairHighMask) =
      (dw a (if low then 0 else 1) ++ dw b (if low then 0 else 1)) := by
  unfold VG.Proof.Gcm.Clmul.vdword
  apply VG.PPC64LE.ext_vbyte
  intro i hi
  rw [permPair,vbyte_packed _ hi]
  have hm := pair_mask_control ⟨i,hi⟩
  cases low <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mul_zero,Nat.mul_one] at *
  all_goals
    rw [show (vbyte _ i).toNat % 32 = _ from (by first | exact hm.2 | exact hm.1)]
    by_cases h : i<8
    all_goals
      simp only [h,ite_true,ite_false]
      simp (disch := omega) only [↓ite_eq_left,↓ite_eq_right]
      apply BitVec.eq_of_getLsbD_eq
      intro r hr
      simp only [vbyte,BitVec.getLsbD_extractLsb',BitVec.getLsbD_append,hr,decide_true,Bool.true_and]
      simp (disch := omega) only [↓ite_eq_left,↓ite_eq_right]
      rw [decide_eq_true (by omega),Bool.true_and]
      congr 1 <;> omega

theorem packedPermProductsWith_ok (reg : Fin 5 → VReg) (hinj : Function.Injective reg)
    (a b loKey hiKey lowMask highMask : VReg) (ka kb : BitVec 128) (s : State)
    (ha : ∀ i, a ≠ reg i) (hb : ∀ i, b ≠ reg i)
    (hl : ∀ i, loKey ≠ reg i) (hh : ∀ i, hiKey ≠ reg i)
    (hmh : ∀ i, highMask ≠ reg i)
    (hlo : s.vpr loKey = lowPair ka kb) (hhi : s.vpr hiKey = highPair ka kb)
    (hmaskl : s.vpr lowMask = Impl.Gcm.PPC64LE.Vpmsum.pairLowMask)
    (hmaskh : s.vpr highMask = Impl.Gcm.PPC64LE.Vpmsum.pairHighMask) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedPermProductsWith
      a b (reg 1) (reg 2) (reg 3) (reg 4) (reg 0) loKey hiKey lowMask highMask)) s fun t =>
      (⟨t.vpr (reg 3),t.vpr (reg 4),t.vpr (reg 0)⟩ : VG.Proof.Gcm.Clmul.Prod) =
        pairedProd (ext8 (s.vpr a) (s.vpr a)) (ext8 (s.vpr b) (s.vpr b)) ka kb ∧
      VOnly [reg 0,reg 1,reg 2,reg 3,reg 4] s t := by
  have heq : ∀ i j : Fin 5, (reg i = reg j) ↔ i = j :=
    fun _ _ => ⟨fun h => hinj h,congrArg reg⟩
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.packedPermProductsWith,Impl.Gcm.PPC64LE.Vpmsum.packedMultiplyWith,
    List.cons_append,List.nil_append,
    runBlock_cons,runStep_some,runBlock_nil,exec_permPair,exec_pm,exec_xor,
    vpr_writeV,Option.some.injEq,exists_eq_left',ha,hb,hl,hh,hmh,heq,
    Fin.reduceEq,ite_true,ite_false]
  refine ⟨?_,⟨fun r hr => ?_,by simp only [gpr_writeV],by simp only [mem_writeV],
    by simp only [rd_writeV],by simp only [wr_writeV],by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · rw [hmaskl,hmaskh,show permPair (s.vpr a) (s.vpr b) Impl.Gcm.PPC64LE.Vpmsum.pairLowMask = _ from
      permPair_halves _ _ true,show permPair (s.vpr a) (s.vpr b) Impl.Gcm.PPC64LE.Vpmsum.pairHighMask = _ from
      permPair_halves _ _ false]
    simp only [hlo,hhi,pairedProd,pmPair,lowPair,highPair,Bool.false_eq_true,ite_false,ite_true,
      vdword_append_0,vdword_append_1,vdword_ext8_0,vdword_ext8_1]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [vpr_writeV,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,ite_false]

def pairedRegs : Fin 5 → VReg
  | ⟨0, _⟩ => HI | ⟨1, _⟩ => U | ⟨2, _⟩ => T | ⟨3, _⟩ => LO | _ => MID

theorem free_pairedRegs (r : VReg) (h : Free r) : ∀ i, r ≠ pairedRegs i := by
  have hc : ∀ i : Fin 5, pairedRegs i = U ∨ pairedRegs i = LO ∨ pairedRegs i = MID ∨
      pairedRegs i = HI ∨ pairedRegs i = T := by decide
  intro i
  rcases hc i with he | he | he | he | he
  · rw [he]; exact h.1
  · rw [he]; exact h.2.1
  · rw [he]; exact h.2.2.1
  · rw [he]; exact h.2.2.2.1
  · rw [he]; exact h.2.2.2.2

theorem packedProducts_ok (loKey hiKey : VReg) (ka kb : BitVec 128) (s : State)
    (hl : Free loKey) (hh : Free hiKey)
    (hlo : s.vpr loKey = lowPair ka kb) (hhi : s.vpr hiKey = highPair ka kb) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedProducts loKey hiKey)) s fun t =>
      prod t = pairedProd (s.vpr A) (s.vpr HI) ka kb ∧ VOnly [HI, U, T, LO, MID] s t :=
  packedProductsWith_ok pairedRegs
    (show ∀ i j : Fin 5, pairedRegs i = pairedRegs j → i = j from by decide)
    A HI loKey hiKey false ka kb s (by decide) (free_pairedRegs loKey hl) (free_pairedRegs hiKey hh) hlo hhi


/-- The adjusted hash key and the canonical eight-block folded result. -/
def adjustedKey (h : BitVec 128) : BitVec 128 :=
  let v := mulV (ext8 h h) xInv2
  ext8 v v

def canonicalTerm (h y : BitVec 128) (f : Nat → BitVec 128) (j : Nat) : VG.Proof.Gcm.Clmul.Prod :=
  let a := if j=0 then f (2*j) ^^^ y else f (2*j)
  let b := f (2*j+1)
  pairedProd (ext8 a a) (ext8 b b) (keyValue h (7-2*j)) (keyValue h (6-2*j))

def foldedProducts (h y : BitVec 128) (f : Nat → BitVec 128) : VG.Proof.Gcm.Clmul.Prod :=
  (List.range 4).foldl (fun p j => addProd p (canonicalTerm h y f j)) VG.Proof.Gcm.Clmul.Prod.zero

def canonicalFold (h y : BitVec 128) (f : Nat → BitVec 128) : BitVec 128 :=
  let v := VG.Proof.Gcm.Clmul.reduce (foldedProducts h y f)
  ext8 v v

/-- Registration supplies the field proof, keeping polynomial algebra out of callers. -/
class FoldLaw : Prop where
  correct : ∀ h y f, canonicalFold (adjustedKey h) y f =
    Spec.Gcm.ghashFrom h y ((List.range 8).map f)

end VG.Proof.Gcm.PPC64LE.Vpmsum
