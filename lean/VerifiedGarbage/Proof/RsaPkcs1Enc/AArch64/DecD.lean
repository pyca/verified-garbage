import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecPost
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `D = I2OSP(d, k)`

The result of the private-key operation to its slot (`dPtrs₁`), `k` zeros at
`scratch + sD` (`zeroLoop`), and `d` copied to their end (`dPtrs₂`,
`copyLoop`): `dBuild_ok`, from `Called` to `DB`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (bytesAt_eq add_add)

/-- The result's 32 bits, zero-extended. -/
def rOf (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

theorem dPtrs₁_ok {t : State} {Q : Addr} (hsp : t.sp = Q)
    (hw : InRegions t.wr (Q + BitVec.ofNat 64 176) 8) (h1 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 168) 8)
    (h2 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 120) 8) :
    WP isa (.block dPtrs₁) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0)) ∧
      u.gpr .x11 = (t.mem.writeW (Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0))).readW (Q + BitVec.ofNat 64 oScr) 64 +
        BitVec.ofNat 64 sD ∧
      u.gpr .x12 = (t.mem.writeW (Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0))).readW (Q + BitVec.ofNat 64 oK) 64 ∧
      u.gpr .x13 = 0 ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [dPtrs₁, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, BitVec.or_self,
    Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, hsp, BitVec.add_zero, oR, oScr, oK, sD,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, reduceCtorEq,
    ite_false, hw, h1, h2]
  refine ⟨trivial, trivial, trivial, trivial, rfl, rfl, rfl, by decide, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_false]

/-- After `j` zeros of `D`. -/
structure ZInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (j : Nat) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  x11 : t.gpr .x11 = scA L (sD + j)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - j)
  x13 : t.gpr .x13 = 0
  z : ∀ i < j, t.mem (scA L (sD + i)) = 0

/-- The private-key operation's result to its slot. -/
theorem dPtrs₁_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : Called L g vv m₀ t) :
    WP isa (.block dPtrs₁) t (ZInv L g vv m₀ (rOf (t.gpr .x0)) (Spec.Rsa.bytesAt t.mem L.out L.k.toNat) 0) := by
  have hc := h.ctx
  have hnQ := hL.nQ
  have hb := hL.bO
  refine WP.mono (dPtrs₁_ok hc.sp (hc.inFr (d := 176) (by decide)) (hc.inFrR (d := 168) (by decide))
    (hc.inFrR (d := 120) (by decide))) fun u ⟨hrd, hwr, hsp, hv, hm, h11, h12, h13, hpr⟩ => ?_
  have rd : ∀ d, d + 8 ≤ 344 → (d + 8 ≤ oR ∨ oR + 8 ≤ d) →
      (t.mem.writeW (L.Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0))).readW (L.Q + BitVec.ofNat 64 d) 64 =
        t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    unfold oR at h₂ ⊢
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
  have hf : Frame [⟨L.Q + BitVec.ofNat 64 oR, 8⟩] t.mem u.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨⟨hc.store hL hrd hwr hsp hv (fun r hr _ => hpr r hr) hf fun r hr => ?_, ?_, ?_⟩, ?_, ?_, h13,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · rw [List.mem_singleton.mp hr]
    exact .inr ⟨oR, Nat.le_refl _, by show oR + 8 ≤ frameBytes; decide, rfl⟩
  · rw [hm, Mem.readW_writeW_self64]
  · refine bytesAt_eq fun i hi => hf.bytes (R := L.OUT) (fun X hX => ?_) (by show L.k.toNat ≤ 2 ^ 64; omega) hi
    rw [List.mem_singleton.mp hX]
    exact (hL.kO.sub_left (Lay.Ok.sub_stk (by decide))).symm
  · rw [h11, rd oScr (by decide) (by decide), hc.kept.scr]; rfl
  · rw [h12, rd oK (by decide) (by decide), hc.kept.k, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem zBody_ok {t : State} (hw : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block [.strb .x13 .x11 0, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.mem = t.mem.write (t.gpr .x11) 1 ((t.gpr .x13).setWidth 8) ∧
      u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1 ∧ u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧
      ∀ r, r ≠ .x11 → r ≠ .x12 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  rw [runBlock_cons, Bytes.exec_strb0 hw, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    Nat.reduceLT, ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_, fun r h11 h12 => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h11, h12, ite_false]

theorem zeroLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : ZInv L g vv m₀ R EM 0 t) :
    WP isa zeroLoop t (ZInv L g vv m₀ R EM L.k.toNat) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  refine Bytes.count_loop (by omega) (ZInv L g vv m₀ R EM) (fun j hj u hu => ?_) h
  have hin : InRegions u.wr (u.gpr .x11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x11, BitVec.add_zero]
    exact (scCov hL hu.post.ctx (a := sD + j) (n := 1) (by unfold sD scrBytes; omega)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (zBody_ok hin) fun w ⟨hrd, hwr, hsp, hv, hm, h11, h12, ho⟩ => ?_
  have hm' : w.mem = u.mem.write (scA L (sD + j)) 1 0 := by rw [hm, hu.x11, hu.x13]; rfl
  have hf : Frame [⟨scA L (sD + j), 1⟩] u.mem w.mem := by
    rw [hm']; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - (j + 1)) := by
    rw [h12, hu.x12, Bytes.counter_step hj L.k.isLt]
  refine ⟨⟨hu.post.step hL hrd hwr hsp (fun r _ => by rw [hv]) (fun r hr _ => ho r (mem_ne hr (by decide))
    (mem_ne hr (by decide))) hf fun r hr => ?_, ?_, hx12, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [List.mem_singleton.mp hr]; exact .inl (scSub (by unfold sD scrBytes; omega))
  · rw [h11, hu.x11, add_add, Nat.add_assoc]
  · rw [ho .x13 (by decide) (by decide), hu.x13]
  · rw [hm']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by unfold sD; omega) (by have := hL.bS; have := hL.s8192; unfold sD; omega)
        (by have := hL.bS; have := hL.s8192; unfold sD; omega)), hu.z i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hx12]; exact Bytes.counter_ne hj L.k.isLt

theorem dPtrs₂_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h1 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 144) 8)
    (h2 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 152) 8) (h3 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 168) 8)
    (h4 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 120) 8) :
    WP isa (.block dPtrs₂) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.mem = t.mem ∧
      u.gpr .x14 = t.mem.readW (Q + BitVec.ofNat 64 oD) 64 ∧ u.gpr .x12 = t.mem.readW (Q + BitVec.ofNat 64 oDl) 64 ∧
      u.gpr .x11 = t.mem.readW (Q + BitVec.ofNat 64 oScr) 64 + BitVec.ofNat 64 sD +
        t.mem.readW (Q + BitVec.ofNat 64 oK) 64 - t.mem.readW (Q + BitVec.ofNat 64 oDl) 64 ∧
      ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [dPtrs₂, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, hsp, oD, oDl,
    oScr, oK, sD, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, reduceCtorEq, ite_false,
    h1, h2, h3, h4]
  refine ⟨trivial, trivial, trivial, trivial, trivial, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_false]

theorem x11_eq (p : Addr) (a : Nat) (k dl : BitVec 64) (h : dl.toNat ≤ k.toNat) :
    p + BitVec.ofNat 64 a + k - dl = p + BitVec.ofNat 64 (a + (k.toNat - dl.toNat)) := by
  have ek : k = BitVec.ofNat 64 k.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ed : dl = BitVec.ofNat 64 dl.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show p + BitVec.ofNat 64 a + k - dl = p + BitVec.ofNat 64 a + BitVec.ofNat 64 k.toNat -
    BitVec.ofNat 64 dl.toNat by rw [← ek, ← ed], add_add, Offset.add_ofNat_sub _ (by omega), Nat.add_sub_assoc h]

/-- After the zeros of `D` and `j` bytes of `d`. -/
structure CInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (j : Nat) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  x14 : t.gpr .x14 = L.d + BitVec.ofNat 64 j
  x11 : t.gpr .x11 = scA L (sD + (L.k.toNat - L.dl.toNat) + j)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.dl.toNat - j)
  z : ∀ i < L.k.toNat - L.dl.toNat, t.mem (scA L (sD + i)) = 0
  c : ∀ i < j, t.mem (scA L (sD + (L.k.toNat - L.dl.toNat) + i)) = m₀ (L.d + BitVec.ofNat 64 i)

theorem dPtrs₂_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : ZInv L g vv m₀ R EM L.k.toNat t) :
    WP isa (.block dPtrs₂) t (CInv L g vv m₀ R EM 0) := by
  have hc := h.post.ctx
  refine WP.mono (dPtrs₂_ok hc.sp (hc.inFrR (d := 144) (by decide)) (hc.inFrR (d := 152) (by decide))
    (hc.inFrR (d := 168) (by decide)) (hc.inFrR (d := 120) (by decide)))
    fun u ⟨hrd, hwr, hsp, hv, hm, h14, h12, h11, hpr⟩ => ?_
  refine ⟨h.post.regs hrd hwr hsp hm hv fun r hr _ => hpr r hr, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [h14, hc.kept.d, BitVec.add_zero]
  · rw [h11, hc.kept.scr, hc.kept.k, hc.kept.dl, x11_eq _ _ _ _ hL.dlk]; rfl
  · rw [h12, hc.kept.dl, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hm]; exact h.z i (by omega)
  · exact absurd hi (Nat.not_lt_zero _)

theorem cBody_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x14 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block [.ldrb .x10 .x14 0, .strb .x10 .x11 0, .addImm .x .x14 .x14 1, .addImm .x .x11 .x11 1,
      .subImm .x .x12 .x12 1]) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.mem = t.mem.write (t.gpr .x11) 1 (t.mem (t.gpr .x14)) ∧
      u.gpr .x14 = t.gpr .x14 + BitVec.ofNat 64 1 ∧ u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1 ∧
      u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧
      ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hr, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, trivial, trivial, trivial, fun r h10 h11 h12 h14 => ?_⟩
  · simp only [BitVec.add_zero, Bytes.read_one, Bytes.byte_rt]
  · simp only [h10, h11, h12, h14, ite_false]

theorem copyLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : CInv L g vv m₀ R EM 0 t) :
    WP isa copyLoop t (CInv L g vv m₀ R EM L.dl.toNat) := by
  have hk := hL.k1024
  have hdk := hL.dlk
  have hbS := hL.bS
  have h8 := hL.s8192
  refine Bytes.count_loop (by have := hL.dl1; omega) (CInv L g vv m₀ R EM) (fun j hj u hu => ?_) h
  have hc := hu.post.ctx
  have hin : InRegions u.wr (u.gpr .x11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x11, BitVec.add_zero]
    exact (scCov hL hc (a := sD + (L.k.toNat - L.dl.toNat) + j) (n := 1) (by unfold sD scrBytes; omega)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hrd : InRegions (u.rd ++ u.wr) (u.gpr .x14 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x14, BitVec.add_zero]
    exact ⟨L.D, by rw [hc.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (cBody_ok hrd hin) fun w ⟨hrd', hwr, hsp, hv, hm, h14, h11, h12, ho⟩ => ?_
  have hm' : w.mem = u.mem.write (scA L (sD + (L.k.toNat - L.dl.toNat) + j)) 1 (m₀ (L.d + BitVec.ofNat 64 j)) := by
    rw [hm, hu.x11, hu.x14, hc.byte_ro hL (ro_D L) hj]
  have hf : Frame [⟨scA L (sD + (L.k.toNat - L.dl.toNat) + j), 1⟩] u.mem w.mem := by
    rw [hm']; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.dl.toNat - (j + 1)) := by
    rw [h12, hu.x12, Bytes.counter_step hj L.dl.isLt]
  have hne : ∀ a, a < sD + (L.k.toNat - L.dl.toNat) + j →
      scA L a ≠ scA L (sD + (L.k.toNat - L.dl.toNat) + j) := fun a ha =>
    Offset.add_ofNat_ne _ (by unfold sD at *; omega) (by unfold sD; omega) (by omega)
  refine ⟨⟨hu.post.step hL hrd' hwr hsp (fun r _ => by rw [hv]) (fun r hr _ => ho r (mem_ne hr (by decide))
    (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_, ?_, ?_, hx12,
    fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [List.mem_singleton.mp hr]; exact .inl (scSub (by unfold sD scrBytes; omega))
  · rw [h14, hu.x14, add_add]
  · rw [h11, hu.x11, add_add, Nat.add_assoc]
  · rw [hm', Bytes.write1_ne _ _ (hne _ (by omega)), hu.z i hi]
  · rw [hm']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (hne _ (by omega)), hu.c i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hx12]; exact Bytes.counter_ne hj L.dl.isLt

/-- After `dBuild`: `R` in its slot, `EM` in `out`, and `D = I2OSP(d, k)` at `scratch + sD`. -/
structure DB (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  D : Spec.Rsa.bytesAt t.mem (scA L sD) L.k.toNat =
    Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.d L.dl.toNat)) L.k.toNat

theorem cinv_db {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
    {EM : List Byte} {u : State} (hu : CInv L g vv m₀ R EM L.dl.toNat u) : DB L g vv m₀ R EM u := by
  refine ⟨hu.post, ?_⟩
  have hdk := hL.dlk
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by simp [Spec.Rsa.bytesAt]; exact hdk)]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine List.ext_getElem (by simp; omega) fun i h₁ _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < L.k.toNat - L.dl.toNat
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate, add_add, hu.z i hi]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem_map, List.getElem_range]
    have := hu.c (i - (L.k.toNat - L.dl.toNat)) (by simp at h₁; omega)
    rw [add_add, show sD + i = sD + (L.k.toNat - L.dl.toNat) + (i - (L.k.toNat - L.dl.toNat)) by omega, this]

theorem dBuild_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : Called L g vv m₀ t) :
    WP isa dBuild t (DB L g vv m₀ (rOf (t.gpr .x0)) (Spec.Rsa.bytesAt t.mem L.out L.k.toNat)) := by
  refine WP.seq (WP.mono (dPtrs₁_inv hL h) fun _ h₁ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hL h₁) fun _ h₂ => ?_)
  refine WP.seq (WP.mono (dPtrs₂_inv hL h₂) fun _ h₃ => ?_)
  exact WP.mono (copyLoop_ok hL h₃) fun u hu => cinv_db hL hu

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
