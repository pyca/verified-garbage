module

public import VerifiedGarbage.Proof.RsaPss.X86.VfAcc
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtXor
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the scan

As on ARMv7 (`Proof/RsaPss/Arm/VfScan.lean`): the scan of `DB` finds the
index (`pzJ`) and the value (`vzJ`) of its first byte that is not zero, if
any (`nfJ`), without a branch (`scan_vp`). On x86 the index and the value
are kept in their slots, through `ebp`, which `posChk` loads with `scratch`
again: the loop's states are states of the body (`Lay.St`), not `Ctx`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- `DB`, as a list. -/
abbrev dbL (P : EP) (τ : State) : List Byte := (List.range (dbN h P)).map (dbF h P τ)

/-- Where the padding ends. -/
abbrev lzF (P : EP) (τ : State) : Nat := RsaPss.lz (dbL h P τ)

/-- The index and value of `DB`'s first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzJ (P : EP) (τ : State) (j : Nat) : Nat := if lzF h P τ < j then lzF h P τ else 0
abbrev vzJ (P : EP) (τ : State) (j : Nat) : Byte := if lzF h P τ < j then dbF h P τ (lzF h P τ) else 0
abbrev nfJ (P : EP) (τ : State) (j : Nat) : BitVec 32 := if lzF h P τ < j then 0 else BitVec.allOnes 32

/-- The mask `sub r, 1; sbb r, r` leaves of a byte. -/
theorem bz : ∀ b : Byte, (if decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32
    else 0) = if b = 0 then BitVec.allOnes 32 else (0 : BitVec 32) := by decide

/-- What the scan keeps. -/
abbrev Kd (P : EP) (τ : State) (m : Mem) : Prop :=
  Ka h P τ m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- A word stored in a slot apart from those `Kd` reads keeps it. -/
theorem Kd.slot {P : EP} {τ : State} {m : Mem} (hk : Kd h P τ m) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hs : ∀ e ∈ [sC, sLo, sDb, sAny, sAcc], d + 4 ≤ e ∨ e + 4 ≤ d) (v : BitVec 32) :
    Kd h P τ (m.writeW ((P.lay h.D).fr d) v) := by
  have hg := hk.1.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hf := hk.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hk.1.1 hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have rw' : ∀ e ∈ [sC, sLo, sDb, sAny, sAcc],
      (m.writeW ((P.lay h.D).fr d) v).readW ((P.lay h.D).fr e) 32 = m.readW ((P.lay h.D).fr e) 32 :=
    fun e he => Lay.readW_fr_other _ _ _ ((hs e he).symm) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> decide) (by unfold frameBytes at hd; omega)
  have kb : ∀ o, o + 1 ≤ oRsa → (m.writeW ((P.lay h.D).fr d) v) (sa P.scr o) = m (sa P.scr o) := fun o ho =>
    slot_frame (P.lay h.D) m d v _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := o) (n := 1) (by omega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)).symm _
        (Region.contains_self _ _)
  refine ⟨⟨hk.1.1, hf, ⟨?_, ?_, ?_, ?_⟩, ?_⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rw' sC (by simp)]; exact hk.1.2.2.1.1
  · rw [rw' sLo (by simp)]; exact hk.1.2.2.1.2.1
  · rw [rw' sDb (by simp)]; exact hk.1.2.2.1.2.2.1
  · rw [rw' sAny (by simp)]; exact hk.1.2.2.1.2.2.2
  · rw [rw' sAcc (by simp)]; exact hk.1.2.2.2
  · rw [kb _ (by omega)]; exact hk.2.1 i hi
  · rw [kb _ (by omega)]; exact hk.2.2 i hi

/-- After `j` bytes of the scan. -/
structure SC (P : EP) (τ : State) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P + j)
  edi : s.gpr .edi = BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (dbN h P - j)
  ebx : s.gpr .ebx = nfJ h P τ j
  pos : s.mem.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzJ h P τ j)
  val : s.mem.readW ((P.lay h.D).fr sVal) 32 = (vzJ h P τ j).setWidth 32

/-- The scan's registers and slots. -/
theorem scanSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (U0 h P) (.block scanSet)
      (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] scanSet_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hd, hh⟩ => ?_
  simp only [scanSet, atDb, atS, addSlot, addi, ld, mi, st, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
    List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
    (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
  have c3 : Ctx (P.lay h.D) P.scr τ t3 := c2.upd u3 (by decide) (by decide)
  refine c3.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_movi fun t5 u5 => wp_movi fun t6 u6 => ?_
  have c6 : Ctx (P.lay h.D) P.scr τ t6 := (c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
  refine c6.wp_st hg (d := sPos) (by decide) fun t7 c7 m7 => c7.wp_st hg (d := sVal) (by decide) fun t8 c8 m8 => ?_
  refine wp_movi fun t9 u9 => wp_subi fun t10 u10 _ _ => WP.block_nil ?_
  have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have ax : t6.gpr .eax = 0 := by rw [u6.gpr]; rfl
  have mem : t10.mem = (s.mem.writeW ((P.lay h.D).fr sPos) (0 : BitVec 32)).writeW ((P.lay h.D).fr sVal)
      (0 : BitVec 32) := by
    rw [u10.mem, u9.mem, m8.mem, m7.gpr, ax, m7.mem, ax, m6]
  have kd : Kd h P τ t10.mem := by
    rw [mem]
    exact (Kd.slot h ⟨hk, hd, hh⟩ (d := sPos) (by decide) (by decide) 0).slot h (d := sVal) (by decide)
      (by decide) 0
  refine ⟨(c8.upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide) |>.st, kd, hk.2.1, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.other, u3.gpr,
      u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp]
    rw [hg.aFr ok sLo (by decide), hk.2.2.1.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.gpr]
  · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.gpr]
    rw [u3.mem, u2.mem, u1.mem, hk.2.2.1.2.2.1]; rfl
  · rw [u10.gpr, u9.gpr]; simp only [nfJ, Nat.not_lt_zero, ite_false]; decide
  · rw [mem, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp only [pzJ, Nat.not_lt_zero, ite_false]; rfl
  · rw [mem, Mem.readW_writeW_self32]
    simp only [vzJ, Nat.not_lt_zero, ite_false]; rfl

theorem dbL_getD {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) : (dbL h P τ).getD j 0 = dbF h P τ j := by
  simp [dbL, List.getD_eq_getElem?_getD, hj]

/-- One byte of the scan. -/
theorem scan_step {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) (b : Byte) (hb : b = dbF h P τ j) :
    let m : BitVec 32 := ((if b = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&& nfJ h P τ j
    BitVec.ofNat 32 (pzJ h P τ j) ||| BitVec.ofNat 32 j &&& m = BitVec.ofNat 32 (pzJ h P τ (j + 1)) ∧
    (vzJ h P τ j).setWidth 32 ||| b.setWidth 32 &&& m = (vzJ h P τ (j + 1)).setWidth 32 ∧
    nfJ h P τ j &&& (m ^^^ BitVec.allOnes 32) = nfJ h P τ (j + 1) := by
  intro m
  have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  have za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  have oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  have hlt : lzF h P τ ≤ dbN h P := by
    have e := RsaPss.lz_le (dbL h P τ)
    rw [show (dbL h P τ).length = dbN h P by simp [dbL]] at e
    exact e
  rcases Nat.lt_trichotomy (lzF h P τ) j with hl | hl | hl
  · have h8 : m = 0 := by simp only [m, nfJ, ite_eq_left hl, az]
    simp only [h8, az, oz, pzJ, vzJ, nfJ, ite_eq_left hl, ite_eq_left (by omega : lzF h P τ < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← dbL_getD h (by omega)]
      exact RsaPss.getD_lz_ne (by
        show lzF h P τ < (dbL h P τ).length
        rw [show (dbL h P τ).length = dbN h P by simp [dbL]]; omega)
    have h8 : m = BitVec.allOnes 32 := by
      simp only [m, hne, ite_false, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega)]; decide
    simp only [h8, BitVec.and_allOnes, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega),
      ite_eq_left (show lzF h P τ < j + 1 by omega)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← dbL_getD h hj]; exact RsaPss.getD_lt_lz hl
    have h8 : m = 0 := by
      simp only [m, hz, ite_true]; rw [show BitVec.allOnes 32 ^^^ BitVec.allOnes 32 = 0 by decide, za]
    simp only [h8, az, oz, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega),
      ite_eq_right (show ¬ lzF h P τ < j + 1 by omega)]
    exact ⟨trivial, trivial, by decide⟩

/-- The scan of `DB`. -/
theorem scan_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s)
      (countLoop scanBody)
      (fun τ s => (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  let I : Nat → State → State → Prop := fun k τ s => k ≤ dbN h P ∧ (P.lay h.D).St τ s ∧ Kd h P τ s.mem ∧
    fits h P ∧ SC h P τ (dbN h P - k) s
  refine (VP.loop (I := I) (fun k => ?_) (dbN h P - 1)).mono (fun τ s ⟨hc, hx, hf', hs⟩ => ⟨by omega, hc, hx, hf',
    by rw [show dbN h P - (dbN h P - 1 + 1) = 0 by omega]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨hk, hs, hx, hf', hp⟩ => ?_
  · obtain ⟨-, s₁, -, -, p₁⟩ := h₁
    obtain ⟨-, s₂, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [s₁.sp, s₂.sp]
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : dbN h P - (k + 1) = j at hp
  have hjn : j < dbN h P := by omega
  have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P + j)) 0 = sa P.scr (oEm + lo P + j) := by
    rw [hg.addrD (by omega), Nat.add_zero]
  have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P + j)) 1 := hg.rd hs (by omega)
  have hb := hx.2.1 j hjn
  simp only [scanBody, isZero, ld, st, addi, Impl.RsaPkcs1Sig.X86.at_, List.cons_append, List.nil_append]
  refine wp_movzx8 (a := sa P.scr (oEm + lo P + j)) (by rw [ea_at, hp.esi]; exact ad) rd fun t1 u1 => ?_
  refine wp_mov fun t2 u2 => wp_subi fun t3 u3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => ?_
  refine wp_xorI fun t5 u5 => wp_and fun t6 u6 => wp_and fun t7 u7 => ?_
  have s7 : (P.lay h.D).St τ t7 := (((((((hs.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd u4
    (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide))
  refine s7.wp_slot (d := sVal) (by show sVal + 4 ≤ frameBytes; decide) (by decide) fun t8 s8 u8 => wp_or fun t9 u9 => ?_
  refine (s8.upd u9 (by decide)).wp_strFr (d := sVal) (by show sVal + 4 ≤ frameBytes; decide) fun t10 s10 m10 => ?_
  refine wp_mov fun t11 u11 => wp_and fun t12 u12 => ?_
  have s12 : (P.lay h.D).St τ t12 := (s10.upd u11 (by decide)).upd u12 (by decide)
  refine s12.wp_slot (d := sPos) (by show sPos + 4 ≤ frameBytes; decide) (by decide) fun t13 s13 u13 => wp_or fun t14 u14 => ?_
  refine (s13.upd u14 (by decide)).wp_strFr (d := sPos) (by show sPos + 4 ≤ frameBytes; decide) fun t15 s15 m15 => ?_
  refine wp_xorI fun t16 u16 => wp_and fun t17 u17 => wp_addi fun t18 u18 => wp_addi fun t19 u19 => ?_
  refine wp_subi fun t20 u20 _ z20 => WP.block_nil ?_
  -- The values.
  have b1 : t1.gpr .eax = (dbF h P τ j).setWidth 32 := by rw [u1.gpr, hb]
  have e2 : t2.gpr .edx = (dbF h P τ j).setWidth 32 := by rw [u2.gpr, b1]
  rw [e2, bz] at u4
  have mk : t6.gpr .edx = ((if dbF h P τ j = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&&
      nfJ h P τ j := by
    simp (disch := decide) only [u6.gpr, u5.gpr, u4.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ebx]
  have st := scan_step h hjn _ rfl (τ := τ)
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have a6 : t6.gpr .eax = (dbF h P τ j).setWidth 32 := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, b1]
  have vV : t9.gpr .ebp = (vzJ h P τ (j + 1)).setWidth 32 := by
    rw [u9.gpr, u8.gpr, u8.other .eax (by decide), u7.gpr, mk, m7, hp.val, a6]
    exact st.2.1
  have d9 : t9.gpr .edx = t6.gpr .edx := by simp (disch := decide) only [u9.other, u8.other, u7.other]
  have i9 : t9.gpr .edi = BitVec.ofNat 32 j := by
    simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
      u1.other, hp.edi]
  have mm10 : t10.mem = s.mem.writeW ((P.lay h.D).fr sVal) ((vzJ h P τ (j + 1)).setWidth 32) := by
    rw [m10.mem, vV, u9.mem, u8.mem, m7]
  have pV : t14.gpr .ebp = BitVec.ofNat 32 (pzJ h P τ (j + 1)) := by
    rw [u14.gpr, u13.gpr, u13.other .eax (by decide), u12.gpr, u11.gpr, u12.mem, u11.mem, mm10,
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hp.pos, u11.other .edx (by decide),
      m10.gpr, d9, mk, i9]
    exact st.1
  have mm15 : t20.mem = (s.mem.writeW ((P.lay h.D).fr sVal) ((vzJ h P τ (j + 1)).setWidth 32)).writeW
      ((P.lay h.D).fr sPos) (BitVec.ofNat 32 (pzJ h P τ (j + 1))) := by
    rw [u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, m15.mem, pV, u14.mem, u13.mem, u12.mem, u11.mem, mm10]
  have s20 : (P.lay h.D).St τ t20 :=
    ((((s15.upd u16 (by decide)).upd u17 (by decide)).upd u18 (by decide)).upd u19 (by decide)).upd u20 (by decide)
  have kd : Kd h P τ t20.mem := by
    rw [mm15]
    exact (Kd.slot h hx (d := sVal) (by decide) (by decide) _).slot h (d := sPos) (by decide) (by decide) _
  have c19 : t19.gpr .ecx = BitVec.ofNat 32 (dbN h P - j) := by
    simp (disch := decide) only [u19.other, u18.other, u17.other, u16.other, m15.gpr, u14.other, u13.other,
      u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
      u2.other, u1.other, hp.ecx]
  have sk : SC h P τ (j + 1) t20 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u20.other, u19.other, u18.gpr, u17.other, u16.other, m15.gpr, u14.other,
        u13.other, u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other,
        u3.other, u2.other, u1.other, hp.esi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · simp (disch := decide) only [u20.other, u19.gpr, u18.other, u17.other, u16.other, m15.gpr, u14.other,
        u13.other, u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other,
        u3.other, u2.other, u1.other, hp.edi]
      rw [BitVec.ofNat_add_ofNat]
    · rw [u20.gpr, c19, ofNat_pred (by omega), Nat.sub_sub]
    · have b9 : t9.gpr .ebx = nfJ h P τ j := by
        simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
          u2.other, u1.other, hp.ebx]
      have x16 : t16.gpr .edx = t6.gpr .edx ^^^ BitVec.allOnes 32 := by
        rw [u16.gpr, m15.gpr, u14.other .edx (by decide), u13.other .edx (by decide), u12.other .edx (by decide),
          u11.other .edx (by decide), m10.gpr, d9]
      have b16 : t16.gpr .ebx = t9.gpr .ebx := by
        rw [u16.other .ebx (by decide), m15.gpr, u14.other .ebx (by decide), u13.other .ebx (by decide),
          u12.other .ebx (by decide), u11.other .ebx (by decide), m10.gpr]
      rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide), u17.gpr, x16, b16, b9, mk]
      exact st.2.2
    · rw [mm15, Mem.readW_writeW_self32]
    · rw [mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  rw [c19, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega),
    show dbN h P - (j + 1) = k by omega] at z20
  refine ⟨?_, fun h0 => ⟨s20, kd, hf', by rw [show dbN h P = j + 1 by omega]; exact sk⟩,
    fun hpos => ⟨by omega, s20, kd, hf', by rw [show dbN h P - k = j + 1 by omega]; exact sk⟩⟩
  show eval .ne t20 = _
  simp only [eval, z20]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

end VG.Proof.RsaPss.X86.Vf
