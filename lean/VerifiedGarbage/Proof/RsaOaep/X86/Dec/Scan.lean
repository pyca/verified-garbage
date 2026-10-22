module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Acc
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: the scan of `T`

As on ARMv7 (`Proof/RsaOaep/Arm/DecScan.lean`): `scan_vp`: the scan of `n`
bytes of our part of `scratch` finds the index (`pzS`) and the value (`vzS`)
of their first byte that is not zero, if any (`nfS`), without a branch. As
in RSASSA-PSS (`Proof/RsaPss/X86/VfScan.lean`), the index and the value are
kept in their slots, through `ebp`, so the loop's states are states of the
body (`Lay.St`), not `Ctx`. `tscan_vp`: on `T = DB[hLen..]`, then `scanEnd`
loads `scratch` into `ebp` again, and `acc` takes in that this byte is
`0x01`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sAcc sPos sVal countLoop scanBody isZero)

/-! ## The scan -/

section Scan

/-- The bytes, as a list. -/
abbrev sL (n : Nat) (f : Nat → Byte) : List Byte := (List.range n).map f

/-- Where the zeros end. -/
abbrev lzS (n : Nat) (f : Nat → Byte) : Nat := RsaPss.lz (sL n f)

/-- The index and value of the first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzS (n : Nat) (f : Nat → Byte) (j : Nat) : Nat := if lzS n f < j then lzS n f else 0
abbrev vzS (n : Nat) (f : Nat → Byte) (j : Nat) : Byte := if lzS n f < j then f (lzS n f) else 0
abbrev nfS (n : Nat) (f : Nat → Byte) (j : Nat) : BitVec 32 := if lzS n f < j then 0 else BitVec.allOnes 32

/-- The mask `sub r, 1; sbb r, r` leaves of a byte. -/
theorem bz : ∀ b : Byte, (if decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32
    else 0) = if b = 0 then BitVec.allOnes 32 else (0 : BitVec 32) := by decide

variable {L : Lay} {scr : BitVec 32}

/-- After `j` bytes of the scan of the `n` bytes at `o`. -/
structure SC (L : Lay) (scr : BitVec 32) (o n : Nat) (f : Nat → Byte) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (o + j)
  edi : s.gpr .edi = BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  ebx : s.gpr .ebx = nfS n f j
  pos : s.mem.readW (L.fr sPos) 32 = BitVec.ofNat 32 (pzS n f j)
  val : s.mem.readW (L.fr sVal) 32 = (vzS n f j).setWidth 32

theorem sL_getD {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) : (sL n f).getD j 0 = f j := by
  simp [sL, List.getD_eq_getElem?_getD, hj]

theorem sL_length (n : Nat) (f : Nat → Byte) : (sL n f).length = n := by simp [sL]

theorem lzS_le (n : Nat) (f : Nat → Byte) : lzS n f ≤ n := by
  have e := RsaPss.lz_le (sL n f); rwa [sL_length] at e

/-- One byte of the scan. -/
theorem scan_step {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) (b : Byte) (hb : b = f j) :
    let m : BitVec 32 := ((if b = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&& nfS n f j
    BitVec.ofNat 32 (pzS n f j) ||| BitVec.ofNat 32 j &&& m = BitVec.ofNat 32 (pzS n f (j + 1)) ∧
    (vzS n f j).setWidth 32 ||| b.setWidth 32 &&& m = (vzS n f (j + 1)).setWidth 32 ∧
    nfS n f j &&& (m ^^^ BitVec.allOnes 32) = nfS n f (j + 1) := by
  intro m
  have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  have za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  have oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  have hlt := lzS_le n f
  rcases Nat.lt_trichotomy (lzS n f) j with hl | hl | hl
  · have h8 : m = 0 := by simp only [m, nfS, ite_eq_left hl, az]
    simp only [h8, az, oz, pzS, vzS, nfS, ite_eq_left hl, ite_eq_left (by omega : lzS n f < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← sL_getD (n := n) (f := f) (by omega)]
      exact RsaPss.getD_lz_ne (by rw [sL_length]; show lzS n f < n; omega)
    have h8 : m = BitVec.allOnes 32 := by
      simp only [m, hne, ite_false, nfS, ite_eq_right (show ¬ lzS n f < j by omega)]; decide
    simp only [h8, BitVec.and_allOnes, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega),
      ite_eq_left (show lzS n f < j + 1 by omega)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← sL_getD (n := n) (f := f) hj]; exact RsaPss.getD_lt_lz hl
    have h8 : m = 0 := by
      simp only [m, hz, ite_true]; rw [show BitVec.allOnes 32 ^^^ BitVec.allOnes 32 = 0 by decide, za]
    simp only [h8, az, oz, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega),
      ite_eq_right (show ¬ lzS n f < j + 1 by omega)]
    exact ⟨trivial, trivial, by decide⟩

/-- The scan of the `n` bytes at `o`, keeping `X`, which writes to the
index's and the value's slots keep. -/
theorem scan_vp (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) (hn : 0 < n) {f : State → Nat → Byte}
    {X : State → Mem → Prop} (hX : ∀ σ m, X σ m → ∀ i < n, m (sa scr (o + i)) = f σ i)
    (hW : ∀ σ m d (v : BitVec 32), X σ m → d = sVal ∨ d = sPos → X σ (m.writeW (L.fr d) v)) :
    VP (fun σ s => L.St σ s ∧ X σ s.mem ∧ SC L scr o n (f σ) 0 s)
      (countLoop scanBody)
      (fun σ s => L.St σ s ∧ X σ s.mem ∧ SC L scr o n (f σ) n s) := by
  have fit := hg.fit
  have hF := hg.F
  unfold oRsa at fit ho
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ L.St σ s ∧ X σ s.mem ∧ SC L scr o n (f σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, hs⟩ => ⟨by omega, hc, hx,
    by rw [show n - (n - 1 + 1) = 0 by omega]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hs, hx, hp⟩ => ?_
  · obtain ⟨-, s₁, -, p₁⟩ := h₁
    obtain ⟨-, s₂, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [s₁.sp, s₂.sp]
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega
  have ad : addr (scr + BitVec.ofNat 32 (o + j)) 0 = sa scr (o + j) := by
    rw [hg.addrD (by unfold oRsa; omega), Nat.add_zero]
  have rd : InRegions (s.rd ++ s.wr) (sa scr (o + j)) 1 := hg.rd hs (by unfold oRsa; omega)
  have hb := hX σ s.mem hx j hjn
  simp only [scanBody, isZero, ld, st, addi, Impl.RsaPkcs1Sig.X86.at_, List.cons_append, List.nil_append]
  refine wp_movzx8 (a := sa scr (o + j)) (by rw [ea_at, hp.esi]; exact ad) rd fun t1 u1 => ?_
  refine wp_mov fun t2 u2 => wp_subi fun t3 u3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => ?_
  refine wp_xorI fun t5 u5 => wp_and fun t6 u6 => wp_and fun t7 u7 => ?_
  have s7 : L.St σ t7 := (((((((hs.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd u4
    (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide))
  refine s7.wp_slot (d := sVal) (by rw [hF]; decide) (by decide) fun t8 s8 u8 => wp_or fun t9 u9 => ?_
  refine (s8.upd u9 (by decide)).wp_strFr (d := sVal) (by rw [hF]; decide) fun t10 s10 m10 => ?_
  refine wp_mov fun t11 u11 => wp_and fun t12 u12 => ?_
  have s12 : L.St σ t12 := (s10.upd u11 (by decide)).upd u12 (by decide)
  refine s12.wp_slot (d := sPos) (by rw [hF]; decide) (by decide) fun t13 s13 u13 => wp_or fun t14 u14 => ?_
  refine (s13.upd u14 (by decide)).wp_strFr (d := sPos) (by rw [hF]; decide) fun t15 s15 m15 => ?_
  refine wp_xorI fun t16 u16 => wp_and fun t17 u17 => wp_addi fun t18 u18 => wp_addi fun t19 u19 => ?_
  refine wp_subi fun t20 u20 _ z20 => WP.block_nil ?_
  -- The values.
  have b1 : t1.gpr .eax = (f σ j).setWidth 32 := by rw [u1.gpr, hb]
  have e2 : t2.gpr .edx = (f σ j).setWidth 32 := by rw [u2.gpr, b1]
  rw [e2, bz] at u4
  have mk : t6.gpr .edx = ((if f σ j = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&&
      nfS n (f σ) j := by
    simp (disch := decide) only [u6.gpr, u5.gpr, u4.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ebx]
  have stp := scan_step hjn _ rfl (f := f σ)
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have a6 : t6.gpr .eax = (f σ j).setWidth 32 := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, b1]
  have vV : t9.gpr .ebp = (vzS n (f σ) (j + 1)).setWidth 32 := by
    rw [u9.gpr, u8.gpr, u8.other .eax (by decide), u7.gpr, mk, m7, hp.val, a6]
    exact stp.2.1
  have d9 : t9.gpr .edx = t6.gpr .edx := by simp (disch := decide) only [u9.other, u8.other, u7.other]
  have i9 : t9.gpr .edi = BitVec.ofNat 32 j := by
    simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
      u1.other, hp.edi]
  have mm10 : t10.mem = s.mem.writeW (L.fr sVal) ((vzS n (f σ) (j + 1)).setWidth 32) := by
    rw [m10.mem, vV, u9.mem, u8.mem, m7]
  have pV : t14.gpr .ebp = BitVec.ofNat 32 (pzS n (f σ) (j + 1)) := by
    rw [u14.gpr, u13.gpr, u13.other .eax (by decide), u12.gpr, u11.gpr, u12.mem, u11.mem, mm10,
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hp.pos, u11.other .edx (by decide),
      m10.gpr, d9, mk, i9]
    exact stp.1
  have mm15 : t20.mem = (s.mem.writeW (L.fr sVal) ((vzS n (f σ) (j + 1)).setWidth 32)).writeW
      (L.fr sPos) (BitVec.ofNat 32 (pzS n (f σ) (j + 1))) := by
    rw [u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, m15.mem, pV, u14.mem, u13.mem, u12.mem, u11.mem, mm10]
  have s20 : L.St σ t20 :=
    ((((s15.upd u16 (by decide)).upd u17 (by decide)).upd u18 (by decide)).upd u19 (by decide)).upd u20 (by decide)
  have kd : X σ t20.mem := by
    rw [mm15]; exact hW _ _ _ _ (hW _ _ _ _ hx (.inl rfl)) (.inr rfl)
  have c19 : t19.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    simp (disch := decide) only [u19.other, u18.other, u17.other, u16.other, m15.gpr, u14.other, u13.other,
      u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
      u2.other, u1.other, hp.ecx]
  have sk : SC L scr o n (f σ) (j + 1) t20 := by
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
    · have b9 : t9.gpr .ebx = nfS n (f σ) j := by
        simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
          u2.other, u1.other, hp.ebx]
      have x16 : t16.gpr .edx = t6.gpr .edx ^^^ BitVec.allOnes 32 := by
        rw [u16.gpr, m15.gpr, u14.other .edx (by decide), u13.other .edx (by decide), u12.other .edx (by decide),
          u11.other .edx (by decide), m10.gpr, d9]
      have b16 : t16.gpr .ebx = t9.gpr .ebx := by
        rw [u16.other .ebx (by decide), m15.gpr, u14.other .ebx (by decide), u13.other .ebx (by decide),
          u12.other .ebx (by decide), u11.other .ebx (by decide), m10.gpr]
      rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide), u17.gpr, x16, b16, b9, mk]
      exact stp.2.2
    · rw [mm15, Mem.readW_writeW_self32]
    · rw [mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  rw [c19, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega), show n - (j + 1) = k by omega] at z20
  refine ⟨?_, fun h0 => ⟨s20, kd, (show j + 1 = n by omega) ▸ sk⟩,
    fun hpos => ⟨by omega, s20, kd, by rw [show n - k = j + 1 by omega]; exact sk⟩⟩
  show eval .ne t20 = _
  simp only [eval, z20]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

end Scan

/-! ## `T` -/

variable (h g : OHash)

/-- `T = DB[hLen..]`, its length, and the index after its first byte not zero. -/
abbrev tN (P : EP) : Nat := P.K - (2 * h.H.D + 1)
abbrev T (P : EP) (σ : State) (j : Nat) : Byte := V5 h g P σ (1 + 2 * h.H.D + j)
abbrev idx (P : EP) (σ : State) : Nat := pzS (tN h P) (T h g P σ) (tN h P)

/-- The decoding's checks all pass. -/
abbrev allOk (P : EP) (σ : State) : Prop :=
  hdOk h g P σ ∧ lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1

/-- After the scan. -/
abbrev A2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
    (∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧ (a = 0 ↔ allOk h g P σ)) ∧
    s.mem.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ)

theorem endB : ∀ b : Byte, (b.setWidth 32 ^^^ (1 : BitVec 32) = 0 ↔ b = 1) := by decide

/-- What the end of the scan adds to `acc`. -/
theorem endX (c : Prop) [Decidable c] (b : Byte) :
    ((if c then b else 0).setWidth 32 ^^^ (1 : BitVec 32)) ||| (if c then (0 : BitVec 32) else BitVec.allOnes 32) >>> 31
      = 0 ↔ c ∧ b = 1 := by
  by_cases hc : c
  · simp only [hc, ite_true, true_and]
    rw [show (0 : BitVec 32) >>> 31 = 0 from rfl, show ∀ x : BitVec 32, x ||| 0 = x from fun x => BitVec.or_zero]
    exact endB b
  · simp only [hc, ite_false, false_and, iff_false]
    decide

/-- What the scan keeps. -/
abbrev Xs (P : EP) (σ : State) (m : Mem) : Prop :=
  Y h g P σ m ∧ ∃ a : BitVec 32, m.readW (P.lay.fr sAcc) 32 = a ∧ (a = 0 ↔ hdOk h g P σ)

theorem Y.slot {P : EP} {σ : State} {m : Mem} (hy : Y h g P σ m) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hr : d + 4 ≤ sRes ∨ sRes + 4 ≤ d) (v : BitVec 32) : Y h g P σ (m.writeW (P.lay.fr d) v) := by
  have hg := hy.1.1.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hy.1.1.1.k1024
  have hD := h.D_le
  have fr := slot_frame P.lay m d v
  have dS : ∀ {o n : Nat}, o + n ≤ oRsa → ∀ r ∈ [slotR P.lay d], (sR P.scr o n).Disjoint r :=
    fun hon r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok hon (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)).symm
  refine ⟨⟨hy.1.1.keep h fr fun r hr => ?_, hy.1.2.1.keep h fr (dS (by oomega)), ?_⟩, hy.2.keep fr hK (dS (by oomega))⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) hd (by omega)
  · rw [← hy.1.2.2]
    exact sbytes_keep (o := oEm) (n := 1) fr (dS (by oomega)) (by oomega) (f := fun _ => m (sa P.scr (oEm + 0)))
      (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)

theorem tscan_vp (P : EP) :
    VP (A1 h g P) (.seq (.block (scanSet h.H)) (.seq (countLoop scanBody) (.block scanEnd))) (A2 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1.1, hs.2.1.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have xs : ∀ σ m d (v : BitVec 32), Xs h g P σ m → d = sVal ∨ d = sPos → Xs h g P σ (m.writeW (P.lay.fr d) v) := by
    intro σ m d v ⟨hy, a, ha, he⟩ hd
    refine ⟨hy.slot h g (d := d) (by rcases hd with rfl | rfl <;> decide)
      (by rcases hd with rfl | rfl <;> decide) v, a, ?_, he⟩
    rw [Lay.readW_fr_other _ _ _ (by rcases hd with rfl | rfl <;> decide) (by decide)
      (by rcases hd with rfl | rfl <;> decide)]
    exact ha
  refine VP.seq (G := fun σ s => P.lay.St σ s ∧ Xs h g P σ s.mem ∧
      SC P.lay P.scr (oEm + 1 + 2 * h.H.D) (tN h P) (T h g P σ) 0 s)
    (VP.taint [.esp, .ebp] h.certs.scanSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hy, ha⟩ => ?_)
    (VP.seq (scan_vp hg (o := oEm + 1 + 2 * h.H.D) (n := tN h P) (by unfold tN; oomega) (by unfold tN; omega) (f := T h g P)
      (X := Xs h g P) (fun σ m hx i hi => by
        rw [show oEm + 1 + 2 * h.H.D + i = oEm + (1 + 2 * h.H.D + i) by omega]; exact hx.1.2 _ (by unfold tN at hi; omega)) xs) ?_)
  · simp only [scanSet, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t3 c3 u3 => ?_
    refine wp_subi fun t4 u4 _ _ => wp_movi fun t5 u5 => wp_movi fun t6 u6 => ?_
    have c6 := ((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
    refine c6.wp_st hg (d := sPos) (by decide) fun t7 c7 m7 => c7.wp_st hg (d := sVal) (by decide) fun t8 c8 m8 => ?_
    refine wp_movi fun t9 u9 => wp_subi fun t10 u10 _ _ => WP.block_nil ?_
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    have ax : t6.gpr .eax = 0 := by rw [u6.gpr]; rfl
    have mem : t10.mem = (s.mem.writeW (P.lay.fr sPos) (0 : BitVec 32)).writeW (P.lay.fr sVal) (0 : BitVec 32) := by
      rw [u10.mem, u9.mem, m8.mem, m7.gpr, ax, m7.mem, ax, m6]
    refine ⟨((c8.upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide)).st, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem]; exact xs _ _ _ _ (xs _ _ _ _ ⟨hy, ha⟩ (.inr rfl)) (.inl rfl)
    · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.other, u3.other,
        u2.gpr, u1.gpr, hc.ebp, Nat.add_zero]
    · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.gpr]
    · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.gpr, u3.gpr]
      show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 1) = _
      rw [sub_ofNat (by omega)]; rfl
    · rw [u10.gpr, u9.gpr]; simp only [nfS, Nat.not_lt_zero, ite_false]; decide
    · rw [mem, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
      simp only [pzS, Nat.not_lt_zero, ite_false]; rfl
    · rw [mem, Mem.readW_writeW_self32]
      simp only [vzS, Nat.not_lt_zero, ite_false]; rfl
  -- `scratch` into `ebp`, and `acc |= (val ⊕ 1) | notFound`.
  refine VP.taint [.esp] scanEnd_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.sp, h₂.1.sp])
    fun σ s ⟨hs, ⟨hy, a, ha, he⟩, sc⟩ => ?_
  simp only [scanEnd, ld, st]
  refine hs.wp_arg (dec_arg (j := 21) (by decide)) (by decide) fun t0 s0 u0 => ?_
  have c0 : Ctx P.lay P.scr σ t0 := ⟨s0, by rw [u0.gpr]; rfl⟩
  refine c0.wp_slot hg (d := sAcc) (by decide) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_slot hg (d := sVal) (by decide) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine wp_xorI fun t3 u3 => wp_or fun t4 u4 => wp_shr (n := 31) (by decide) fun t5 u5 _ => wp_or fun t6 u6 => ?_
  have c6 := (((c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide)
    (by decide)).upd u6 (by decide) (by decide)
  refine c6.wp_st hg (d := sAcc) (by decide) fun t7 c7 m7 => WP.block_nil ?_
  have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u0.mem]
  have v6 : t6.gpr .eax = (a ||| ((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32))) |||
      nfS (tN h P) (T h g P σ) (tN h P) >>> 31 := by
    simp (disch := decide) only [u6.gpr, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
      u1.gpr, u1.other, u0.other, u1.mem, u0.mem, ha, sc.val, sc.ebx]
  refine ⟨c7, ?_, ⟨_, by rw [m7.mem, Mem.readW_writeW_self32], ?_⟩, ?_⟩
  · rw [m7.mem, m6]; exact hy.slot h g (d := sAcc) (by decide) (by decide) _
  · rw [v6, BitVec.or_assoc, or_eq_zero32, he, endX]
  · rw [m7.mem, m6, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact sc.pos

end VG.Proof.RsaOaep.X86.Dec
