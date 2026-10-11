import VerifiedGarbage.Proof.Cast5.Arm.KeyHalf
import VerifiedGarbage.Proof.Cast5.Arm.Ecb

/-!
# CAST5 key expansion on ARMv7

`expandKey` takes the working space from the stack, saves the callee-saved
registers in it, pads the key with zeros into `x` (§2.5), runs both halves
of §2.4 (`half_ok`) and restores the registers (`key_correct`).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

/-! ## The key, padded -/

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the first 64 bytes of the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_word (m : Mem) (c : Addr) {d e : Nat} (hd : d + 4 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 32)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 4 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) {cb : BitVec 32} (hc : s.gpr .r12 = cb) (hcf : cb.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr cb + BitVec.ofNat 64 off) w) (key : Addr) :
    WP isa (.block [.mov .r3 (.imm 0), .str .r3 .r12 xOff, .str .r3 .r12 (xOff + 4), .str .r3 .r12 (xOff + 8),
      .str .r3 .r12 (xOff + 12), .dp .add .r3 .r12 (.imm (BitVec.ofNat 32 xOff))]) s fun u =>
      CInv s.mem key (State.addr cb) 0 u.mem ∧ u.gpr .r3 = cb + BitVec.ofNat 32 16 ∧ Keep [.r3] s u := by
  have aS := addr_off hcf
  unfold xOff
  crun [hc, aS, hin]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · rw [zero_word _ _ (by decide) (by omega), zero_word _ _ (by decide) (by omega), zero_word _ _ (by decide) (by omega),
      zero_word _ _ (by decide) (by omega)]
    repeat' split
    all_goals first | rfl | omega
  · rw [zero_word _ _ (by decide) (by omega), zero_word _ _ (by decide) (by omega), zero_word _ _ (by decide) (by omega),
      zero_word _ _ (by decide) (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  · exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem copyStep_ok (u : State) {m0 : Mem} {kp cb : BitVec 32} {j : Nat} (hj : j < 16)
    (hI : CInv m0 (State.addr kp) (State.addr cb) j u.mem) (hcf : cb.toNat + 256 ≤ 2 ^ 32)
    (hkf : kp.toNat + (j + 1) ≤ 2 ^ 32)
    (h0 : u.gpr .r0 = kp + BitVec.ofNat 32 j) (h3 : u.gpr .r3 = cb + BitVec.ofNat 32 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (State.addr cb + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (State.addr kp + BitVec.ofNat 64 j) = m0 (State.addr kp + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 (State.addr kp) (State.addr cb) (j + 1) v.mem ∧ v.gpr .r0 = kp + BitVec.ofNat 32 (j + 1) ∧
      v.gpr .r3 = cb + BitVec.ofNat 32 (16 + (j + 1)) ∧ v.gpr .r1 = u.gpr .r1 - 1 ∧
      v.z = (u.gpr .r1 - 1 == 0) ∧ Keep [.r0, .r1, .r3, .r4] u v := by
  have e0 : State.addr (kp + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = State.addr kp + BitVec.ofNat 64 j := by
    rw [BitVec.add_zero, addr_add (by omega)]
  have e3 : State.addr (cb + BitVec.ofNat 32 (16 + j) + BitVec.ofNat 32 0) =
      State.addr cb + BitVec.ofNat 64 (16 + j) := by
    rw [BitVec.add_zero, addr_add (by omega)]
  unfold copyStep
  crun [e0, e3, hr, hw, hk, h0, h3]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega) (by omega)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega⟩, ite_eq_left (by omega), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega) (by omega), ite_eq_right (by omega)]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · rw [BitVec.add_assoc, BitVec.ofNat_add j 1]; rfl
  · rw [BitVec.add_assoc, show 16 + (j + 1) = (16 + j) + 1 by omega, BitVec.ofNat_add (16 + j) 1]; rfl

/-! ## The whole function -/

/-- Key expansion's contract on ARMv7, as its proof states it. -/
def keyArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let sch : Region := ⟨State.addr (s.gpr .r2), 128⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 256⟩
    s.rd = [key] ∧ s.wr = [sch, scr] ∧ key.Disjoint sch ∧ key.Disjoint scr ∧ sch.Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 32 ∧ Spec.Cast5.validKey (s.gpr .r1).toNat
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (State.addr (s.gpr .r2)) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem key_correct (s : State) (hs : keyArm.pre s) :
    WP isa expandKey s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyArm.post s s' := by
  obtain ⟨hrd, hwr, dkK, dkS, dKS, hkf, hKf, hcf, hn⟩ := hs
  obtain ⟨n, hnn⟩ : ∃ n, (s.gpr .r1).toNat = n := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp, s.gpr .r0 = kp := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ kb, s.gpr .r2 = kb := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb, s.gpr .r3 = cb := ⟨_, rfl⟩
  rw [hnn] at hrd dkK dkS hkf hn
  rw [hkp] at hrd dkK dkS hkf
  rw [hkb] at hwr dkK dKS hKf
  rw [hcb] at hwr dkS dKS hcf
  have hn5 : 5 ≤ n ∧ n ≤ 16 := hn
  have inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr cb + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨State.addr cb, 256⟩, by rw [hwr]; simp, Offset.contains_base _ hw (by omega)⟩
  unfold expandKey
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  -- The working space in `r12`, and the saved registers.
  have h1 : WP isa (.block [.mov .r12 (.reg .r3)]) s fun s₁ => s₁ = s.setReg .r12 cb := by
    crun [hcb]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff, save_eq]
  refine WP.mono (WP.keep [] (Spill.save_block_ok savedSlots_ok (s := s.setReg .r12 cb)
    (by simp only [gpr_setReg_self]; omega) fun d _ hd => by simp only [gpr_setReg_self, wr_setReg]; exact inC (by omega))
    (by decide)) fun s₂ ⟨⟨g₂, rd₂, wr₂, m₂⟩, k₂⟩ => ?_
  simp only [gpr_setReg_self] at m₂
  obtain ⟨M, hM⟩ : ∃ M, s₂.mem = M := ⟨_, rfl⟩
  have c₂ : s₂.gpr .r12 = cb := by rw [g₂, gpr_setReg_self]
  have g₂' (r : Reg) (hr : r ≠ .r12) : s₂.gpr r = s.gpr r := by rw [g₂]; exact gpr_setReg_of_ne _ _ hr
  have hMf : Frame [⟨State.addr cb, 256⟩] s.mem M := by
    rw [← hM, m₂]; exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  have hkM (j : Nat) (hj : j < n) : M (State.addr kp + BitVec.ofNat 64 j) = s.mem (State.addr kp + BitVec.ofNat 64 j) :=
    hMf.bytes (R := ⟨State.addr kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkS)
      (by show n ≤ 2 ^ 64; omega) hj
  refine WP.mono (zero_ok s₂ c₂ hcf (fun hw => by rw [wr₂]; exact inC hw) (State.addr kp))
    fun s₃ ⟨ci₃, r3₃, k₃⟩ => ?_
  rw [hM] at ci₃
  -- The key, copied.
  have hrK : ∀ j < n, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨State.addr kp, n⟩, by rw [hrd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have dkC : Region.Disjoint ⟨State.addr kp, n⟩ ⟨State.addr cb, 64⟩ := dkS.sub_right (Region.sub_prefix (by decide))
  have r0₃ : s₃.gpr .r0 = kp := by rw [k₃.gpr _ (by decide), g₂' _ (by decide), hkp]
  have r1₃ : s₃.gpr .r1 = BitVec.ofNat 32 n := by
    rw [k₃.gpr _ (by decide), g₂' _ (by decide), ← hnn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have copy : WP isa (.loop (.block copyStep) .ne) s₃ fun v =>
      CInv M (State.addr kp) (State.addr cb) n v.mem ∧ Keep [.r0, .r1, .r3, .r4] s₃ v := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = n - j ∧ j < n ∧
      CInv M (State.addr kp) (State.addr cb) j v.mem ∧ v.gpr .r0 = kp + BitVec.ofNat 32 j ∧
      v.gpr .r3 = cb + BitVec.ofNat 32 (16 + j) ∧ v.gpr .r1 = BitVec.ofNat 32 (n - j) ∧
      Keep [.r0, .r1, .r3, .r4] s₃ v) ?_ n s₃
      ⟨0, rfl, by omega, ci₃, by rw [r0₃, BitVec.add_zero], by rw [r3₃], by rw [r1₃, Nat.sub_zero], Keep.refl _ _⟩
    rintro m v ⟨j, rfl, hj, cv, v0, v3, v1, kv⟩
    have hk : v.mem (State.addr kp + BitVec.ofNat 64 j) = M (State.addr kp + BitVec.ofNat 64 j) :=
      cv.fr.bytes (R := ⟨State.addr kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkC)
        (by show n ≤ 2 ^ 64; omega) hj
    refine WP.mono (copyStep_ok v (by omega) cv hcf (by omega) v0 v3
      (by rw [kv.rd, kv.wr, k₃.rd, k₃.wr, rd₂, wr₂]; exact hrK j hj)
      (by rw [kv.wr, k₃.wr, wr₂]; exact inC (by omega)) hk) fun w ⟨cw, w0, w3, w1, wz, kw⟩ => ?_
    rw [v1, ofNat_sub_one (by omega) (by omega)] at w1 wz
    by_cases he : j + 1 = n
    · refine .inl ⟨by show some (!w.z) = _; rw [wz, show n - j - 1 = 0 by omega]; rfl, he ▸ cw, kv.trans kw⟩
    · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, cw, w0, w3, by rw [w1, Nat.sub_sub], kv.trans kw⟩
      show some (!w.z) = _
      have : BitVec.ofNat 32 (n - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega
      rw [wz]; simpa using this
  refine WP.seq (WP.mono copy fun v ⟨cv, kv⟩ => ?_)
  have r2v : v.gpr .r2 = kb := by rw [kv.gpr _ (by decide), k₃.gpr _ (by decide), g₂' _ (by decide), hkb]
  have r12v : v.gpr .r12 = cb := by rw [kv.gpr _ (by decide), k₃.gpr _ (by decide), c₂]
  have rdv : v.rd = s.rd := by rw [kv.rd, k₃.rd, rd₂]; rfl
  have wrv : v.wr = s.wr := by rw [kv.wr, k₃.wr, wr₂]; rfl
  refine WP.seq ?_
  crun [r2v]
  obtain ⟨w, hw⟩ : ∃ w, (v.setReg .lr kb).setReg .r3 2 = w := ⟨_, rfl⟩
  rw [hw]
  have wlr : w.gpr .lr = kb := by rw [← hw]; rfl
  have w3 : w.gpr .r3 = 2 := by rw [← hw]; rfl
  have w12 : w.gpr .r12 = cb := by rw [← hw]; exact r12v
  have wm : w.mem = v.mem := by rw [← hw]; rfl
  have wwr : w.wr = s.wr := by rw [← hw]; exact wrv
  have wrd : w.rd = s.rd := by rw [← hw]; exact rdv
  -- The state of key expansion: `x` the padded key, no subkeys yet.
  let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem (State.addr kp) n).getD j 0,
    fun j => M (State.addr cb + BitVec.ofNat 64 (32 + j))⟩
  have ks0 : KS M cb kb w ⟨st0, [], fun i => w.mem.readW (State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32⟩ :=
    { r12 := w12
      mem := ⟨fun a i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), by
        rw [wm]; exact cv.fr.mono (by simp)⟩
      ex := fun _ _ => rfl
      len := Nat.zero_le _
      cfit := hcf
      kfit := hKf
      scr := by rw [wwr, hwr]; simp
      sch := by rw [wwr, hwr]; simp
      dKS := dKS }
  case refine_1 =>
    rw [wm]
    cases a with
    | x =>
      rw [show off .x + i = 16 + i from rfl, cv.x i hi]
      show _ = (Spec.Cast5.bytesAt s.mem (State.addr kp) n).getD i 0
      rw [Proof.Cast5.bytesAt_getD]
      split
      · rw [hkM i (by omega)]
      · rfl
    | z => exact cv.z i hi
  -- The halves.
  have halves_loop : WP isa (.loop half .ne) w fun u => ∃ k, KS M cb kb u k ∧ k.xz = (halves st0 2).1 ∧
      k.ws = (halves st0 2).2 ∧ Keep halfRegs w u := by
    refine WP.loop (M := isa) (fun m (u : State) => ∃ hh, m = 2 - hh ∧ hh < 2 ∧ ∃ k, KS M cb kb u k ∧
      k.xz = (halves st0 hh).1 ∧ k.ws = (halves st0 hh).2 ∧ u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh) ∧
      u.gpr .r3 = BitVec.ofNat 32 (2 - hh) ∧ Keep halfRegs w u) ?_ 2 w
      ⟨0, rfl, by decide, _, ks0, rfl, rfl, by rw [wlr, Nat.mul_zero, BitVec.add_zero], by rw [w3]; rfl,
        Keep.refl _ _⟩
    rintro m u ⟨hh, rfl, hhh, k, hk, kx, kw, ulr, u3, ku⟩
    refine WP.mono (half_ok hk ulr (by rw [kw, halves_length]) hhh)
      fun x ⟨k', hk', kx', kw', xlr, x3, xz, kh⟩ => ?_
    have nx : k'.xz = (halves st0 (hh + 1)).1 ∧ k'.ws = (halves st0 (hh + 1)).2 := by
      rw [halves_succ, kx', kw', kx, kw]; exact ⟨rfl, rfl⟩
    rw [u3, ofNat_sub_one (by omega) (by omega)] at x3 xz
    by_cases he : hh + 1 = 2
    · exact .inl ⟨by show some (!x.z) = _; rw [xz, show 2 - hh - 1 = 0 by omega]; rfl, k', hk', he ▸ nx.1,
        he ▸ nx.2, ku.trans kh⟩
    · refine .inr ⟨?_, 2 - (hh + 1), by omega, hh + 1, rfl, by omega, k', hk', nx.1, nx.2, xlr,
        by rw [x3, Nat.sub_sub], ku.trans kh⟩
      have : hh = 0 := by omega
      subst this
      show some (!x.z) = _; rw [xz]; rfl
  refine WP.seq (WP.mono halves_loop fun u ⟨k, hk, kxz, kws, ku⟩ => ?_)
  -- The saved registers, restored.
  have hsv : Spill.Saved u.mem (State.addr (u.gpr .r12)) (s.setReg .r12 cb).gpr savedSlots := by
    rw [hk.r12]
    refine (Spill.saveMem_saved _ _ _ _ savedSlots_ok).frame savedSlots_ok ((by rw [← m₂, hM]; exact hk.mem.fr) :
      Frame [⟨State.addr cb, 64⟩, ⟨State.addr kb, 128⟩] (Spill.saveMem (s.setReg .r12 cb).mem (State.addr cb)
        (s.setReg .r12 cb).gpr savedSlots) u.mem) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact (dKS.symm.sub_left (Offset.sub_base _ (by decide)))
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok savedSlots_ok savedSlots_restorable (by rw [hk.r12]; omega)
    (fun d _ hd => by
      rw [ku.rd, ku.wr, wrd, wwr, hwr, hk.r12]
      exact ⟨⟨State.addr cb, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) hsv)
    fun s' ⟨hg, _, hm, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rw [Spill.restored_reg hg (savedSlots_preserved r hr)]
    exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact absurd hr (by decide))
  · show Spec.Cast5.scheduleAt s'.mem (State.addr (s.gpr .r2)) = _
    rw [hm, hkb, hkp, hnn, scheduleAt_keys hk.mem.keys (by rw [kws, halves_length]), kws,
      Proof.Cast5.expandKey_eq _ st0.z, halves_two]



end VG.Proof.Cast5.Arm
