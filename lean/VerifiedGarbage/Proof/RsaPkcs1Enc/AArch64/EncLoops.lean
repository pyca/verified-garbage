import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncStep

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the copies of `PS` and `M`

`psLoop` copies the padding string `PS` to `EM` after its first two bytes,
collecting in `x14` whether any byte is zero (`zmask`); `msgCopy` copies the
message after the separator. Both keep `Ctx`, since they write only `EM`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- The argument registers hold the arguments on entry. -/
structure Args (g : Reg → BitVec 64) (t : State) : Prop where
  x0 : t.gpr .x0 = g .x0
  x1 : t.gpr .x1 = g .x1
  x2 : t.gpr .x2 = g .x2
  x3 : t.gpr .x3 = g .x3
  x4 : t.gpr .x4 = g .x4
  x5 : t.gpr .x5 = g .x5
  x6 : t.gpr .x6 = g .x6
  x7 : t.gpr .x7 = g .x7

theorem Args.of {g : Reg → BitVec 64} {t u : State} (h : Args g t)
    (hk : ∀ r, r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] → u.gpr r = t.gpr r) : Args g u :=
  ⟨(hk _ (by simp)).trans h.x0, (hk _ (by simp)).trans h.x1, (hk _ (by simp)).trans h.x2,
    (hk _ (by simp)).trans h.x3, (hk _ (by simp)).trans h.x4, (hk _ (by simp)).trans h.x5,
    (hk _ (by simp)).trans h.x6, (hk _ (by simp)).trans h.x7⟩

theorem mem_ne {l : List Reg} {r d : Reg} (hr : r ∈ l) (hd : d ∉ l) : r ≠ d := fun e => hd (e ▸ hr)

theorem bytesAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Rsa.bytesAt m p (j + 1) = Spec.Rsa.bytesAt m p j ++ [m (p + BitVec.ofNat 64 j)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ]

theorem add_one (p : Addr) (j : Nat) : p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) :=
  add_add p j 1

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
  (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

omit hL in
/-- A byte of a buffer the function never writes, as on entry. -/
theorem byte_ro {R : Region} (hO : R.Disjoint L.OUT) (hS : R.Disjoint L.SCR) (hK : R.Disjoint L.STK)
    (hb : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  hc.frame.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hO, hS, hK]) hb hi

theorem ps_byte {i : Nat} (hi : i < L.pl.toNat) :
    t.mem (L.ps + BitVec.ofNat 64 i) = m₀ (L.ps + BitVec.ofNat 64 i) :=
  hc.byte_ro (R := L.PS) hL.oP.symm hL.pS hL.kP.symm (Nat.le_of_lt L.pl.isLt) hi

theorem msg_byte {i : Nat} (hi : i < L.ml.toNat) :
    t.mem (L.msg + BitVec.ofNat 64 i) = m₀ (L.msg + BitVec.ofNat 64 i) :=
  hc.byte_ro (R := L.MSG) hL.oM.symm hL.mS hL.kM.symm (Nat.le_of_lt L.ml.isLt) hi

/-- A byte of `PS` may be read. -/
theorem in_ps {i : Nat} (hi : i < L.pl.toNat) :
    InRegions (t.rd ++ t.wr) (L.ps + BitVec.ofNat 64 i + BitVec.ofNat 64 0) 1 :=
  ⟨L.PS, by rw [hc.rd, hc.wr]; simp,
    by rw [add_add, Nat.add_zero]; exact Offset.contains_base _ (by omega) (by have := hL.bP; omega)⟩

theorem in_msg {i : Nat} (hi : i < L.ml.toNat) :
    InRegions (t.rd ++ t.wr) (L.msg + BitVec.ofNat 64 i + BitVec.ofNat 64 0) 1 :=
  ⟨L.MSG, by rw [hc.rd, hc.wr]; simp,
    by rw [add_add, Nat.add_zero]; exact Offset.contains_base _ (by omega) (by have := hL.bM; omega)⟩

omit hL in
/-- A byte of the inner frame may be written. -/
theorem in_fr {d : Nat} (hd : d + 1 ≤ frameBytes) :
    InRegions t.wr (L.Q + BitVec.ofNat 64 d + BitVec.ofNat 64 0) 1 := by
  rw [add_add, Nat.add_zero]; exact hc.inFr hd

end Ctx

namespace Lay.Ok

variable {L : Lay} (hL : L.Ok)
include hL

theorem pl_le : L.pl.toNat + 3 ≤ L.k.toNat := by have := hL.plk; have := hL.mlk; omega
theorem pl8 : 8 ≤ L.pl.toNat := by have := hL.plk; have := hL.mlk; omega
theorem em_len : L.pl.toNat + L.ml.toNat + 3 = L.k.toNat := by have := hL.plk; have := hL.mlk; omega

end Lay.Ok

/-- After `j` bytes of `PS`. -/
structure PsInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (j : Nat) (t : State) :
    Prop where
  ctx : Ctx L g vv m₀ t
  args : Args g t
  x11 : t.gpr .x11 = L.ps + BitVec.ofNat 64 j
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.pl.toNat - j)
  x13 : t.gpr .x13 = L.Q + BitVec.ofNat 64 (oEM + 2 + j)
  x14 : t.gpr .x14 = zmask (Spec.Rsa.bytesAt m₀ L.ps j)
  x15 : t.gpr .x15 = 1
  b0 : t.mem (L.Q + BitVec.ofNat 64 oEM) = 0
  b1 : t.mem (L.Q + BitVec.ofNat 64 (oEM + 1)) = 2
  ps : ∀ i < j, t.mem (L.Q + BitVec.ofNat 64 (oEM + 2 + i)) = m₀ (L.ps + BitVec.ofNat 64 i)

theorem psLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : PsInv L g vv m₀ 0 t) : WP isa psLoop t (PsInv L g vv m₀ L.pl.toNat) := by
  have hnQ := hL.nQ
  have hpl := hL.pl_le
  have hk := hL.k1024
  refine Bytes.count_loop (by have := hL.pl8; omega) (PsInv L g vv m₀) (fun j hj u hu => ?_) h
  have hc := hu.ctx
  refine WP.mono (psBody_ok (by rw [hu.x11]; exact hc.in_ps hL hj)
    (by rw [hu.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega)) hu.x15) fun w hw => ?_
  have hne : ∀ d, d < oEM + 2 + j → L.Q + BitVec.ofNat 64 d ≠ L.Q + BitVec.ofNat 64 (oEM + 2 + j) :=
    fun d hd => Offset.add_ofNat_ne _ (by unfold oEM at hd; omega) (by unfold oEM; omega) (by omega)
  have hmem : w.mem = u.mem.write (L.Q + BitVec.ofNat 64 (oEM + 2 + j)) 1 (m₀ (L.ps + BitVec.ofNat 64 j)) := by
    rw [hw.mem, hu.x13, hu.x11, hc.ps_byte hL hj]
  have hf : Frame [⟨L.Q + BitVec.ofNat 64 (oEM + 2 + j), 1⟩] u.mem w.mem := by
    rw [hmem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.pl.toNat - (j + 1)) := by
    rw [hw.x12, hu.x12, Bytes.counter_step hj L.pl.isLt]
  refine ⟨⟨?_, ?_, ?_, hx12, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · refine hc.store hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => hw.other r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))
      (mem_ne hr (by decide))) hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨oEM + 2 + j, by unfold oEM; omega, by show oEM + 2 + j + 1 ≤ 1072; unfold oEM; omega, rfl⟩
  · exact hu.args.of fun r hr => hw.other r (mem_ne hr (by decide)) (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))
  · rw [hw.x11, hu.x11, add_one]
  · rw [hw.x13, hu.x13, add_add, Nat.add_assoc]
  · rw [hw.x14, hu.x14, hu.x11, hc.ps_byte hL hj, bytesAt_succ, zmask_snoc]
  · rw [hw.other .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.x15]
  · rw [hmem, Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega)), hu.b0]
  · rw [hmem, Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega)), hu.b1]
  · rw [hmem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (hne _ (by omega)), hu.ps i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hx12]; exact Bytes.counter_ne hj L.pl.isLt

/-- After the separator and `j` bytes of `M`. -/
structure MsgInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (j : Nat) (t : State) :
    Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = g .x0
  x1 : t.gpr .x1 = g .x1
  x2 : t.gpr .x2 = g .x2
  x3 : t.gpr .x3 = g .x3
  x4 : t.gpr .x4 = g .x4
  x5 : t.gpr .x5 = g .x5
  x6 : t.gpr .x6 = L.msg + BitVec.ofNat 64 j
  x7 : t.gpr .x7 = BitVec.ofNat 64 (L.ml.toNat - j)
  x13 : t.gpr .x13 = L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j)
  b0 : t.mem (L.Q + BitVec.ofNat 64 oEM) = 0
  b1 : t.mem (L.Q + BitVec.ofNat 64 (oEM + 1)) = 2
  ps : ∀ i < L.pl.toNat, t.mem (L.Q + BitVec.ofNat 64 (oEM + 2 + i)) = m₀ (L.ps + BitVec.ofNat 64 i)
  sep : t.mem (L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat)) = 0
  msg : ∀ i < j, t.mem (L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + i)) = m₀ (L.msg + BitVec.ofNat 64 i)
  z : t.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

theorem sep_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hg : L.msg = g .x6 ∧ L.ml = g .x7) (h : PsInv L g vv m₀ L.pl.toNat t) :
    WP isa (.block sep) t (MsgInv L g vv m₀ 0) := by
  have hnQ := hL.nQ
  have hpl := hL.pl_le
  have hk := hL.k1024
  have hc := h.ctx
  refine WP.mono (sep_ok (by rw [h.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega))
    (by rw [hc.sp, add_add]; exact hc.inFr (by decide))) fun w hw => ?_
  have hmem : w.mem = (t.mem.write (L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat)) 1 0#8).writeW
      (L.Q + BitVec.ofNat 64 oZ) (zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)) := by
    rw [hw.mem, h.x13, hc.sp, h.x14]
  have hf : Frame [⟨L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat), 1⟩, ⟨L.Q + BitVec.ofNat 64 oZ, 8⟩] t.mem w.mem := by
    rw [hmem]
    exact ((Frame.refl _ _).write (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  -- A byte of `EM` before the separator is not in the zero test's slot.
  have hz : ∀ d, oEM ≤ d → d + 1 ≤ frameBytes →
      w.mem (L.Q + BitVec.ofNat 64 d) = (t.mem.write (L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat)) 1 0#8)
        (L.Q + BitVec.ofNat 64 d) := fun d h₁ h₂ => by
    rw [hmem]
    exact Bytes.byte_writeW_sep (Offset.sep _ (by unfold oEM oZ at *; omega) (by unfold frameBytes at h₂; omega)
      (by unfold oZ; omega))
  have hne : ∀ d, d < oEM + 2 + L.pl.toNat →
      L.Q + BitVec.ofNat 64 d ≠ L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat) :=
    fun d hd => Offset.add_ofNat_ne _ (by unfold oEM at hd; omega) (by unfold oEM; omega) (by omega)
  have go : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x13 → w.gpr r = t.gpr r := hw.other
  refine ⟨?_, (go .x0 (by decide) (by decide) (by decide)).trans h.args.x0,
    (go .x1 (by decide) (by decide) (by decide)).trans h.args.x1,
    (go .x2 (by decide) (by decide) (by decide)).trans h.args.x2,
    (go .x3 (by decide) (by decide) (by decide)).trans h.args.x3,
    (go .x4 (by decide) (by decide) (by decide)).trans h.args.x4,
    (go .x5 (by decide) (by decide) (by decide)).trans h.args.x5, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_,
    fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
  · refine hc.store hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨oEM + 2 + L.pl.toNat, by unfold oEM; omega, by show oEM + 2 + L.pl.toNat + 1 ≤ 1072; unfold oEM; omega, rfl⟩
    · exact ⟨oZ, by decide, by show oZ + 8 ≤ 1072; decide, rfl⟩
  · rw [go .x6 (by decide) (by decide) (by decide), h.args.x6, ← hg.1, BitVec.add_zero]
  · rw [go .x7 (by decide) (by decide) (by decide), h.args.x7, ← hg.2, Nat.sub_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hw.x13, h.x13, add_add, show oEM + 2 + L.pl.toNat + 1 = oEM + 3 + L.pl.toNat + 0 by omega]
  · rw [hz _ (Nat.le_refl _) (by decide), Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega)), h.b0]
  · rw [hz _ (by unfold oEM; omega) (by decide), Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega)), h.b1]
  · rw [hz _ (by unfold oEM; omega) (by unfold oEM frameBytes; omega), Bytes.write1_ne _ _ (hne _ (by omega)),
      h.ps i hi]
  · rw [hz _ (by unfold oEM; omega) (by unfold oEM frameBytes; omega)]; exact Bytes.write1_self _ _ _
  · rw [hmem, Mem.readW_writeW_self64]

theorem msgLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hm : 0 < L.ml.toNat) (h : MsgInv L g vv m₀ 0 t) : WP isa msgLoop t (MsgInv L g vv m₀ L.ml.toNat) := by
  have hnQ := hL.nQ
  have hem := hL.em_len
  have hk := hL.k1024
  refine Bytes.count_loop hm (MsgInv L g vv m₀) (fun j hj u hu => ?_) h
  have hc := hu.ctx
  refine WP.mono (msgBody_ok (by rw [hu.x6]; exact hc.in_msg hL hj)
    (by rw [hu.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega))) fun w hw => ?_
  have hne : ∀ d, d < oEM + 3 + L.pl.toNat + j →
      L.Q + BitVec.ofNat 64 d ≠ L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j) :=
    fun d hd => Offset.add_ofNat_ne _ (by unfold oEM at hd; omega) (by unfold oEM; omega) (by omega)
  have hmem : w.mem = u.mem.write (L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j)) 1
      (m₀ (L.msg + BitVec.ofNat 64 j)) := by
    rw [hw.mem, hu.x13, hu.x6, hc.msg_byte hL hj]
  have hf : Frame [⟨L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j), 1⟩] u.mem w.mem := by
    rw [hmem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx7 : w.gpr .x7 = BitVec.ofNat 64 (L.ml.toNat - (j + 1)) := by
    rw [hw.x7, hu.x7, Bytes.counter_step hj L.ml.isLt]
  have go : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x13 → w.gpr r = u.gpr r := hw.other
  -- The bytes below `M`'s, and the zero test's slot, are as they were.
  have hlo : ∀ d, d < oEM + 3 + L.pl.toNat + j → w.mem (L.Q + BitVec.ofNat 64 d) = u.mem (L.Q + BitVec.ofNat 64 d) :=
    fun d hd => by rw [hmem, Bytes.write1_ne _ _ (hne d hd)]
  refine ⟨⟨?_, (go .x0 (by decide) (by decide) (by decide) (by decide)).trans hu.x0,
    (go .x1 (by decide) (by decide) (by decide) (by decide)).trans hu.x1,
    (go .x2 (by decide) (by decide) (by decide) (by decide)).trans hu.x2,
    (go .x3 (by decide) (by decide) (by decide) (by decide)).trans hu.x3,
    (go .x4 (by decide) (by decide) (by decide) (by decide)).trans hu.x4,
    (go .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.x5, ?_, hx7, ?_,
    by rw [hlo _ (by unfold oEM; omega)]; exact hu.b0, by rw [hlo _ (by unfold oEM; omega)]; exact hu.b1,
    fun i hi => by rw [hlo _ (by omega)]; exact hu.ps i hi, by rw [hlo _ (by omega)]; exact hu.sep,
    fun i hi => ?_, ?_⟩, ?_⟩
  · refine hc.store hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨oEM + 3 + L.pl.toNat + j, by unfold oEM; omega,
      by show oEM + 3 + L.pl.toNat + j + 1 ≤ 1072; unfold oEM; omega, rfl⟩
  · rw [hw.x6, hu.x6, add_one]
  · rw [hw.x13, hu.x13, add_add, Nat.add_assoc]
  · rw [hmem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (hne _ (by omega)), hu.msg i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by unfold oZ oEM; omega) (by unfold oZ; omega) (by unfold oEM; omega)) (by decide)]
    exact hu.z
  · rw [hx7]; exact Bytes.counter_ne hj L.ml.isLt

theorem msgCopy_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : MsgInv L g vv m₀ 0 t) : WP isa msgCopy t (MsgInv L g vv m₀ L.ml.toNat) := by
  refine WP.ite (t.gpr .x7 != 0) (Bytes.eval_nonzero t .x7) (fun hb => msgLoop_ok hL ?_ h) (fun hb => ?_)
  · rw [h.x7, Nat.sub_zero] at hb
    rcases Nat.eq_zero_or_pos L.ml.toNat with h0 | h0
    · rw [h0] at hb; exact absurd hb (by decide)
    · exact h0
  · have h0 : L.ml.toNat = 0 := by
      rw [h.x7, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
      have := (bne_eq_false_iff_eq).mp hb
      rw [this]; rfl
    exact WP.block_nil (h0 ▸ h)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
