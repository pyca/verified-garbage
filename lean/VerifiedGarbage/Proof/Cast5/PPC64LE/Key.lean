module

import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
import VerifiedGarbage.Proof.Cast5.PPC64LE.Ecb
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Impl.Cast5.PPC64LE
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeySteps
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill

/-!
# CAST5 key expansion on PPC64LE

`expandKey` saves `LR` and the callee-saved registers in the working space,
pads the key with zeros into `x` (§2.5), runs both halves of §2.4
(`half_ok`) and restores the registers (`key_wp`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5 VG.Impl.Cast5.PPC64LE VG.Proof.Cast5

/-! ## The key, padded -/

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the first 64 bytes of the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_dword (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 64)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) {cb : Addr} (hc : s.gpr wkK = cb) (h0 : s.gpr .r0 = 0)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (cb + BitVec.ofNat 64 off) w) (key : Addr) :
    WP isa (.block [.store .d zero wkK xOff, .store .d zero wkK (xOff + 8), .addi dst wkK xOff]) s fun u =>
      CInv s.mem key cb 0 u.mem ∧ u.gpr dst = cb + BitVec.ofNat 64 16 ∧ Keep [dst] s u := by
  have i16 := hin (off := 16) (w := 8) (by decide)
  have i24 := hin (off := 24) (w := 8) (by decide)
  unfold xOff
  refine wp_std (a := cb + BitVec.ofNat 64 16) (by decide) (by decide) (by rw [hc]) i16 fun u₁ h₁ => ?_
  refine wp_std (a := cb + BitVec.ofNat 64 24) (by decide) (by decide) (by rw [h₁.gpr]; exact congrArg (· + _) hc)
    (by rw [h₁.wr]; exact i24) fun u₂ h₂ => ?_
  refine wp_addi (by decide) (by decide) fun u₃ h₃ => wp_nil ?_
  have mem : u₃.mem = (s.mem.writeW (cb + BitVec.ofNat 64 16) (0 : BitVec 64)).writeW
      (cb + BitVec.ofNat 64 24) (0 : BitVec 64) := by
    rw [h₃.mem, h₂.mem, h₁.mem, h₁.gpr, h0]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, by rw [h₃.gpr, h₂.gpr, h₁.gpr, hc], ?_⟩
  · rw [mem, zero_dword _ _ (by decide) (by omega_arith), zero_dword _ _ (by decide) (by omega_arith)]
    repeat' split
    all_goals first | rfl | omega_arith
  · rw [mem, zero_dword _ _ (by decide) (by omega_arith), zero_dword _ _ (by decide) (by omega_arith),
      ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · rw [mem]
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide)))
  · exact ⟨fun r hr => by rw [h₃.other _ (by simpa using hr), h₂.gpr, h₁.gpr], by rw [h₃.rd, h₂.rd, h₁.rd],
      by rw [h₃.wr, h₂.wr, h₁.wr]⟩

theorem copyStep_ok (u : State) {m0 : Mem} {kp cb : Addr} {j : Nat} (hj : j < 16)
    (hI : CInv m0 kp cb j u.mem)
    (h0 : u.gpr key = kp + BitVec.ofNat 64 j) (h3 : u.gpr dst = cb + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (kp + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (cb + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (kp + BitVec.ofNat 64 j) = m0 (kp + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 kp cb (j + 1) v.mem ∧ v.gpr key = kp + BitVec.ofNat 64 (j + 1) ∧
      v.gpr dst = cb + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr klen = u.gpr klen - 1#64 ∧
      Keep [tmp, key, dst, klen] u v := by
  unfold copyStep
  c5run [hr, hw, hk, h0, h3]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [byte_write _ _ _ (by omega_arith) (by omega_arith)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega_arith⟩, ite_eq_left (by omega_arith), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega_arith), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hl, ite_eq_right (by omega_arith)]
  · rw [byte_write _ _ _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    exact hI.z i hi
  · exact hI.fr.write List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]
  · rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add, Nat.add_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The whole function -/

/-- What key expansion may assume: the key readable, the schedule and the
working space writable, the working space apart from both, none wrapping
around, a valid key length; and the table `VG_CAST5_S5678`, readable and
apart from the schedule and the working space. -/
structure KeyPre (s : State) : Prop where
  key : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region) ∈ s.rd ++ s.wr
  kfit : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  sch : (⟨s.gpr .r5, 128⟩ : Region) ∈ s.wr
  Kfit : (s.gpr .r5).toNat + 128 ≤ 2 ^ 64
  scr : (⟨s.gpr .r6, 256⟩ : Region) ∈ s.wr
  sfit : (s.gpr .r6).toNat + 256 ≤ 2 ^ 64
  keyScr : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  schScr : (⟨s.gpr .r5, 128⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  valid : Spec.Cast5.validKey (s.gpr .r4).toNat
  trd : (⟨s.syms s5678Sym, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.syms s5678Sym) s5678
  tblSch : (⟨s.syms s5678Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .r5, 128⟩
  tblScr : (⟨s.syms s5678Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : Spec.Cast5.scheduleAt s'.mem (s.gpr .r5) =
    Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  saved : ∀ r ∈ saved, s'.gpr r = s.gpr r
  lr : s'.lr = s.lr

theorem ofNat_sub_one64 {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 1#64 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem key_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  obtain ⟨n, hnn⟩ : ∃ n, (s.gpr .r4).toNat = n := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp, s.gpr .r3 = kp := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ kb, s.gpr .r5 = kb := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb, s.gpr .r6 = cb := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, s.syms s5678Sym = T := ⟨_, rfl⟩
  have hkey := h.key; have hkf := h.kfit; have hsch := h.sch; have hKf := h.Kfit; have hscr := h.scr
  have hcf := h.sfit; have dkS := h.keyScr; have dKS := h.schScr; have hn := h.valid
  have htrd := h.trd; have hheld := h.held; have dTK := h.tblSch; have dTS := h.tblScr
  rw [hnn] at hkey hkf dkS hn
  rw [hkp] at hkey hkf dkS
  rw [hkb] at hsch hKf dKS dTK
  rw [hcb] at hscr hcf dkS dKS dTS
  rw [hT] at htrd hheld dTK dTS
  have hn5 : 5 ≤ n ∧ n ≤ 16 := hn
  have inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (cb + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨cb, 256⟩, hscr, Offset.contains_base _ hw (by omega_arith)⟩
  have hw : ∀ p ∈ allSlots, InRegions s.wr (cb + BitVec.ofNat 64 p.2) 8 := fun p hp =>
    inC (by have := allSlots_lt p hp; omega_arith)
  have sub144 : Region.Sub ⟨cb + BitVec.ofNat 64 64, 144⟩ ⟨cb, 256⟩ := Offset.sub_base _ (by decide)
  unfold expandKey
  apply WP.seq
  refine prologue_ok s wkK (by decide) _ hcb hw fun s₀ sv₀ fr₀ k₀ t₀ c₀ z₀ sy₀ => ?_
  have g₀ (q : Reg) (hq : q ∉ [Reg.r0, tbl, c255] := by decide) : s₀.gpr q = s.gpr q := k₀.gpr hq
  -- `x` zeroed.
  refine WP.mono (zero_ok s₀ (cb := cb) (by rw [g₀ wkK, hcb]) z₀ (fun hw => by rw [k₀.2.2]; exact inC hw) kp)
    fun s₁ ⟨ci₁, d₁, k₁⟩ => ?_
  obtain ⟨M, hM⟩ : ∃ M, s₀.mem = M := ⟨_, rfl⟩
  rw [hM] at ci₁ sv₀ fr₀
  have dkC : Region.Disjoint ⟨kp, n⟩ ⟨cb, 64⟩ := dkS.sub_right (Region.sub_prefix (by decide))
  have hkM (j : Nat) (hj : j < n) : M (kp + BitVec.ofNat 64 j) = s.mem (kp + BitVec.ofNat 64 j) :=
    fr₀.bytes (R := ⟨kp, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dkS.sub_right sub144)
      (by show n ≤ 2 ^ 64; omega_arith) hj
  -- The key, copied.
  have hrK : ∀ j < n, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨kp, n⟩, hkey, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have r3₁ : s₁.gpr key = kp := by rw [k₁.gpr (by decide), g₀ key, hkp]
  have r4₁ : s₁.gpr klen = BitVec.ofNat 64 n := by
    rw [k₁.gpr (by decide), g₀ klen, ← hnn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have rw₁ : s₁.rd = s.rd ∧ s₁.wr = s.wr := ⟨by rw [k₁.2.1, k₀.2.1], by rw [k₁.2.2, k₀.2.2]⟩
  have copy : WP isa (.loop (.block copyStep) (.nonzero .d klen)) s₁ fun v =>
      CInv M kp cb n v.mem ∧ Keep [tmp, key, dst, klen] s₁ v := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = n - j ∧ j < n ∧
      CInv M kp cb j v.mem ∧ v.gpr key = kp + BitVec.ofNat 64 j ∧
      v.gpr dst = cb + BitVec.ofNat 64 (16 + j) ∧ v.gpr klen = BitVec.ofNat 64 (n - j) ∧
      Keep [tmp, key, dst, klen] s₁ v) ?_ n s₁
      ⟨0, rfl, by omega_arith, ci₁, by rw [r3₁]; simp, by rw [d₁], by rw [r4₁, Nat.sub_zero], Keep.refl _ _⟩
    rintro m v ⟨j, rfl, hj, cv, v0, v3, v1, kv⟩
    have hk : v.mem (kp + BitVec.ofNat 64 j) = M (kp + BitVec.ofNat 64 j) :=
      cv.fr.bytes (R := ⟨kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkC)
        (by show n ≤ 2 ^ 64; omega_arith) hj
    refine WP.mono (copyStep_ok v (by omega_arith) cv v0 v3
      (by rw [kv.2.1, kv.2.2, rw₁.1, rw₁.2]; exact hrK j hj)
      (by rw [kv.2.2, rw₁.2]; exact inC (by omega_arith)) hk) fun w ⟨cw, w0, w3, w1, kw⟩ => ?_
    rw [v1, ofNat_sub_one64 (by omega_arith) (by omega_arith)] at w1
    have ev : isa.eval (.nonzero .d klen) w = some (BitVec.ofNat 64 (n - j - 1) != 0) := by
      rw [eval_nonzero, w1]
    rw [ofNat_bne_zero (by omega_arith)] at ev
    by_cases he : j + 1 = n
    · refine .inl ⟨by rw [ev, show n - j - 1 = 0 by omega_arith]; rfl, he ▸ cw, (kv.trans kw).mono (by decide)⟩
    · refine .inr ⟨by rw [ev, decide_eq_false (by omega_arith)]; rfl, n - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, cw, w0, w3, by rw [w1, Nat.sub_sub], (kv.trans kw).mono (by decide)⟩
  refine WP.seq (WP.mono copy fun v ⟨cv, kv⟩ => ?_)
  have kv' := (k₁.trans kv)
  have gv (q : Reg) (hq : q ∉ [dst] ++ [tmp, key, dst, klen] := by decide) : v.gpr q = s₀.gpr q := kv'.gpr hq
  refine WP.seq (wp_li (by decide) fun w hw => wp_nil ?_)
  have kw := kv'.trans hw.keep
  have rdw : w.rd = s.rd := by rw [kw.2.1, k₀.2.1]
  have wrw : w.wr = s.wr := by rw [kw.2.2, k₀.2.2]
  -- The state of key expansion: `x` the padded key, no subkeys yet.
  let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem kp n).getD j 0, fun j => M (cb + BitVec.ofNat 64 (32 + j))⟩
  have ks0 : KS M cb kb T w ⟨st0, [], fun i => w.mem.readW (cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32⟩ :=
    { wk := by rw [kw.gpr (by decide), g₀ wkK, hcb]
      mem := ⟨fun a i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), by
        rw [hw.mem]; exact cv.fr.mono (by simp)⟩
      ex := fun _ _ => rfl
      len := Nat.zero_le _
      cfit := hcf
      kfit := hKf
      scr := by rw [wrw]; exact hscr
      sch := by rw [wrw]; exact hsch
      dKS := dKS
      zero := by rw [kw.gpr (by decide), z₀]
      tblR := by rw [kw.gpr (by decide), t₀, hT]
      trd := by rw [rdw, wrw]; exact htrd
      held0 := by
        rw [← hM]
        refine held_frame (hM ▸ fr₀) (fun r hr => ?_) (by rw [s5678_len]; decide) hheld
        simp only [List.mem_singleton] at hr; subst hr
        rw [s5678_len]; exact dTS.sub_right sub144
      dTS := dTS.sub_right (Region.sub_prefix (by decide))
      dTK := dTK }
  case refine_1 =>
    rw [hw.mem]
    cases a with
    | x =>
      rw [show off .x + i = 16 + i from rfl, cv.x i hi]
      show _ = (Spec.Cast5.bytesAt s.mem kp n).getD i 0
      rw [Proof.Cast5.bytesAt_getD]
      split
      · rw [hkM i (by omega_arith)]
      · rfl
    | z => exact cv.z i hi
  -- The halves.
  have halves_loop : WP isa (.loop half (.nonzero .d hlv)) w fun u => ∃ k, KS M cb kb T u k ∧
      k.xz = (halves st0 2).1 ∧ k.ws = (halves st0 2).2 ∧ Keep halfRegs w u := by
    refine WP.loop (M := isa) (fun m (u : State) => ∃ hh, m = 2 - hh ∧ hh < 2 ∧ ∃ k, KS M cb kb T u k ∧
      k.xz = (halves st0 hh).1 ∧ k.ws = (halves st0 hh).2 ∧ u.gpr out = kb + BitVec.ofNat 64 (64 * hh) ∧
      u.gpr hlv = BitVec.ofNat 64 (2 - hh) ∧ Keep halfRegs w u) ?_ 2 w
      ⟨0, rfl, by decide, _, ks0, rfl, rfl, by rw [kw.gpr (by decide), g₀ out, hkb]; simp, by rw [hw.gpr],
        Keep.refl _ _⟩
    rintro m u ⟨hh, rfl, hhh, k, hk, kx, kws, uout, u3, ku⟩
    refine WP.mono (half_ok hk uout (by rw [kws, halves_length]) hhh)
      fun x ⟨k', hk', kx', kw', xout, x3, kh⟩ => ?_
    have nx : k'.xz = (halves st0 (hh + 1)).1 ∧ k'.ws = (halves st0 (hh + 1)).2 := by
      rw [halves_succ, kx', kw', kx, kws]; exact ⟨rfl, rfl⟩
    rw [u3, ofNat_sub_one64 (by omega_arith) (by omega_arith)] at x3
    have ev : isa.eval (.nonzero .d hlv) x = some (BitVec.ofNat 64 (2 - hh - 1) != 0) := by
      rw [eval_nonzero, x3]
    rw [ofNat_bne_zero (by omega_arith)] at ev
    by_cases he : hh + 1 = 2
    · exact .inl ⟨by rw [ev, show 2 - hh - 1 = 0 by omega_arith]; rfl, k', hk', he ▸ nx.1, he ▸ nx.2,
        (ku.trans kh).mono (by decide)⟩
    · refine .inr ⟨by rw [ev, decide_eq_false (by omega_arith)]; rfl, 2 - (hh + 1), by omega_arith, hh + 1, rfl,
        by omega_arith, k', hk', nx.1, nx.2, xout, by rw [x3, Nat.sub_sub], (ku.trans kh).mono (by decide)⟩
  refine WP.seq (WP.mono halves_loop fun u ⟨k, hk, kxz, kws, ku⟩ => ?_)
  -- The saved registers, restored.
  rw [epilogue_eq]
  have r6 : u.gpr wkK = cb := hk.wk
  have hsv : Spill.Saved cb (s.write .r0 s.lr).gpr (savedSlots ++ [(.r0, lrOff)]) u.mem := by
    refine (sv₀.sub (by decide)).frame hk.mem.fr fun p hp r hr => ?_
    have hl := restoreSlots_lt p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (dKS.symm.sub_left (slot_sub _ hl))
  refine Spill.restore_ok (by decide) r6 restoreSlots_ok (by decide) (fun p hp => ?_) hsv fun s' R => ?_
  · rw [ku.2.1, ku.2.2, rdw, wrw]
    exact ⟨_, List.mem_append_right _ hscr, Offset.contains_base _
      (by have := restoreSlots_lt p hp; omega_arith) (by have := restoreSlots_lt p hp; omega_arith)⟩
  refine WP.cons exec_mtlr (wp_nil ⟨?_, fun r hr => ?_, ?_⟩)
  · show Spec.Cast5.scheduleAt s'.mem (s.gpr .r5) = _
    rw [R.mem, hkb, hkp, hnn, scheduleAt_keys hk.mem.keys (by rw [kws, halves_length]), kws,
      Proof.Cast5.expandKey_eq _ st0.z, halves_two]
  · show s'.gpr r = s.gpr r
    have hm : (r, savedOff + 8 * saved.idxOf r) ∈ savedSlots ++ [(.r0, lrOff)] := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    rw [R.gpr _ hm, RegUpd.gpr_write_of_ne s s.lr h0]
  · show s'.gpr .r0 = s.lr
    rw [R.gpr (.r0, lrOff) (by decide)]
    exact RegUpd.gpr_write_self s _ _

end VG.Proof.Cast5.PPC64LE
