module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Shift
import VerifiedGarbage.Proof.RsaOaep.X86.Instr
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: the output

As on ARMv7 (`Proof/RsaOaep/Arm/DecOut.lean`): `ok` (all ones exactly when
the private-key operation succeeded and every check passed) to its slot
(`okMask_vp`); then `out` from the buffer, each byte ANDed with `ok`
(`outLoop_vp`): the message after `T`'s padding, zeros after it, or zeros.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sAcc sPos countLoop)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## A masked copy -/

section
variable {L : Lay} {scr : BitVec 32}

theorem and8 (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 :=
  BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi, show i < 32 by omega]

/-- After `j` bytes of the masked copy. -/
structure OI (src dst : BitVec 32) (n : Nat) (f : Nat → Byte) (w : BitVec 32) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = src + BitVec.ofNat 32 j
  edi : s.gpr .edi = dst + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  edx : s.gpr .edx = w
  out : ∀ i < j, s.mem (byteAt dst i) = f i &&& w.setWidth 8

/-- The `n` bytes at `src`, ANDed with the low byte of `w σ`, to `dst`. -/
theorem outLoop_vp {src dst : BitVec 32} {n : Nat} (hd : WBuf L dst n) (hs : RBuf L src n)
    (hn : 0 < n) {X : State → Mem → Prop} (hX : ∀ σ m m', X σ m → Frame [⟨dst.setWidth 64, n⟩] m m' → X σ m')
    {f : State → Nat → Byte} (hf : ∀ σ m, X σ m → ∀ i < n, m (byteAt src i) = f σ i) {w : State → BitVec 32} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .esi = src ∧ s.gpr .edi = dst ∧
        s.gpr .ecx = BitVec.ofNat 32 n ∧ s.gpr .edx = w σ)
      (countLoop outBody)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ ∀ i < n, s.mem (byteAt dst i) = f σ i &&& (w σ).setWidth 8) := by
  have fit := hd.fit
  have fis := hs.fit
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧ X σ s.mem ∧
    OI src dst n (f σ) (w σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, si, di, cx, dx⟩ => ⟨by omega, hc, hx,
    ⟨by rw [si, show n - (n - 1 + 1) = 0 by omega, BitVec.add_zero],
      by rw [di, show n - (n - 1 + 1) = 0 by omega, BitVec.add_zero],
      by rw [cx, show n - (n - 1 + 1) = 0 by omega]; rfl, dx, fun i hi => by omega⟩⟩) fun _ _ h => h
  refine VP.taint _ outBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, hx, hp⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega
  have az : ∀ x : BitVec 32, addr x 0 = x.setWidth 64 := fun x => by simp [addr]
  simp only [outBody, addi, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_movzx8 (a := byteAt src j) (by rw [ea_at, hp.esi, az, byte32 fis hjn]) (hs.inR hc.st hjn)
    fun t1 u1 => wp_and fun t2 u2 => ?_
  have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_store8 (a := byteAt dst j)
    (by rw [ea_at, u2.other _ (by decide), u1.other _ (by decide), hp.edi, az, byte32 fit hjn])
    (by rw [u2.wr, u1.wr]; exact hd.inW hc.st hjn) fun t3 m3 => ?_
  refine wp_addi fun t4 u4 => wp_addi fun t5 u5 => wp_subi fun t6 u6 _ z6 => WP.block_nil ?_
  have v2 : t2.gpr .eax = (f σ j).setWidth 32 &&& w σ := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), hp.edx, hf σ s.mem hx j hjn]
  have mm : t6.mem = s.mem.writeW (byteAt dst j) (f σ j &&& (w σ).setWidth 8) := by
    rw [u6.mem, u5.mem, u4.mem, m3.mem]
    show t2.mem.writeW _ ((t2.gpr .eax).setWidth 8) = _
    rw [v2, and8, u2.mem, u1.mem]
  have fr : Frame [⟨dst.setWidth 64, n⟩] s.mem t6.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_byte (Region.contains_self _ _) fit hjn)
  have g6 : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ecx → r ≠ .eax → t6.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u6.other _ h3, u5.other _ h2, u4.other _ h1, m3.gpr, u2.other _ h4, u1.other _ h4]
  have c6 : Ctx L scr σ t6 := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.sub)
    (by rw [u6.rd, u5.rd, u4.rd, m3.rd, u2.rd, u1.rd]) (by rw [u6.wr, u5.wr, u4.wr, m3.wr, u2.wr, u1.wr])
    (g6 _ (by decide) (by decide) (by decide) (by decide)) (g6 _ (by decide) (by decide) (by decide) (by decide))
  have c5 : t5.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), m3.gpr, u2.other _ (by decide), u1.other _ (by decide), hp.ecx]
  have sk : OI src dst n (f σ) (w σ) (j + 1) t6 := by
    refine ⟨?_, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, m3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), hp.esi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), m3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), hp.edi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u6.gpr, c5, ofNat_pred (by omega), Nat.sub_sub]
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide), hp.edx]
    · rw [mm, VG.WriteBytes.writeW8_apply]
      by_cases e : i = j
      · subst e; simp
      · rw [ite_eq_right fun h' => e (byteAt_inj fit (by omega) hjn h')]
        exact hp.out i (by omega)
  rw [c5, ofNat_pred (by omega), Nat.sub_sub, ofNat_beq_zero (by omega), show n - (j + 1) = k by omega] at z6
  refine ⟨?_, fun h0 => ⟨c6, hX σ _ _ hx fr, fun i hi => sk.out i (by omega)⟩,
    fun hpos => ⟨by omega, c6, hX σ _ _ hx fr, by rw [show n - k = j + 1 by omega]; exact sk⟩⟩
  show eval .ne t6 = _
  simp only [eval, z6]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

end

theorem and_maskOf (b : Byte) (c : Prop) [Decidable c] : b &&& (maskOf c).setWidth 8 = if c then b else 0 := by
  unfold maskOf
  by_cases hc : c
  · rw [ifp hc, ifp hc]; exact BitVec.and_allOnes
  · rw [ifn hc, ifn hc]; exact BitVec.and_zero

theorem maskOf_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : maskOf p = maskOf q := by
  unfold maskOf
  by_cases hp : p
  · rw [ifp hp, ifp (h.mp hp)]
  · rw [ifn hp, ifn fun hq => hp (h.mpr hq)]

theorem lt_one_iff (x : BitVec 32) : x.toNat < (1 : BitVec 32).toNat ↔ x = 0 := by
  constructor
  · intro h
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [e1] at h
    apply BitVec.eq_of_toNat_eq
    show x.toNat = 0
    omega
  · rintro rfl; decide

/-- `ok`, as `okMask` computes it: the borrow of `((r ⊕ 1) ∨ acc) - 1`. -/
theorem okBit (o : Spec.Rsa.Outcome) (a : BitVec 32) :
    (if decide (((rOf o ^^^ 1) ||| a).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32 else 0) =
      maskOf (rOf o = 1 ∧ a = 0) := by
  have hx : (rOf o ^^^ 1) ||| a = 0 ↔ rOf o = 1 ∧ a = 0 := by
    rw [or_eq_zero32]
    cases o <;> simp only [rOf] <;> exact and_congr_left fun _ => by decide
  unfold maskOf
  by_cases hc : rOf o = 1 ∧ a = 0
  · rw [ifp hc, decide_eq_true ((lt_one_iff _).mpr (hx.mpr hc))]; rfl
  · rw [ifn hc, decide_eq_false fun h' => hc (hx.mp ((lt_one_iff _).mp h'))]; rfl

variable (h g : OHash)

/-- Every check passed, and the operation succeeded. -/
abbrev okP (P : EP) (σ : State) : Prop := rV P σ = 1 ∧ allOk h g P σ
abbrev okW (P : EP) (σ : State) : BitVec 32 := maskOf (okP h g P σ)

/-- The message's length, or zero. -/
abbrev mlV (P : EP) (σ : State) : Nat := if okP h g P σ then P.K - (2 * h.H.D + 2) - idx h g P σ else 0

/-- What the output keeps: `K0`, `idx` and `ok` in their slots. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  K0 h P σ m ∧ m.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ) ∧
    m.readW (P.lay.fr sOk) 32 = okW h g P σ

theorem Ko.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hk : Ko h g P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, (slotR P.lay sRes).Disjoint r ∧ (slotR P.lay sPos).Disjoint r ∧ (slotR P.lay sOk).Disjoint r) :
    Ko h g P σ m' :=
  ⟨hk.1.keep h hf fun r hr => (ha r hr).1, slot_keep hf (fun r hr => (ha r hr).2.1) hk.2.1,
    slot_keep hf (fun r hr => (ha r hr).2.2) hk.2.2⟩

/-- After `ok`: `out` from the buffer. -/
abbrev O1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧ ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ)

theorem okMask_vp (P : EP) : VP (SF h g P) (.block okMask) (O1 h g P) := by
  refine VP.taint [.esp, .ebp] okMask_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hx, ⟨a, ha, hae⟩, hp⟩, hb⟩ => ?_
  have hi := hx.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  simp only [okMask, ld, st, Impl.RsaPkcs1Sig.X86.stk]
  refine hc.wp_slot hg (d := sRes) (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_xorI fun t2 u2 => ?_
  have c2 := c1.upd u2 (by decide) (by decide)
  refine wp_orm (B := P.lay.B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sAcc (by decide)]; exact c2.rFr hg sAcc (by decide))
    fun t3 u3 => wp_cmpi fun t4 f4 cf4 _ => wp_sbb_self cf4 fun t5 u5 => ?_
  have c5 := ((c2.upd u3 (by decide) (by decide)).fupd f4).upd u5 (by decide) (by decide)
  refine c5.wp_st hg (d := sOk) (by decide) fun t6 c6 m6 => WP.block_nil ?_
  have m5 : t5.mem = s.mem := by rw [u5.mem, f4.mem, u3.mem, u2.mem, u1.mem]
  have v5 : t5.gpr .eax = okW h g P σ := by
    rw [u5.gpr, u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hg.aFr ok sAcc (by decide), hx.1.2.2.1, ha, okBit]
    exact maskOf_congr (and_congr_right fun _ => hae)
  have fr : Frame [slotR P.lay sOk] s.mem t6.mem := by rw [m6.mem, m5, v5]; exact slot_frame _ _ _ _
  refine ⟨c6, ⟨hx.1.keep h fr fun r hr => ?_, slot_keep fr (fun r hr => ?_) hp,
    by rw [m6.mem, m5, v5, Mem.readW_writeW_self32]⟩, sbytes_keep fr (fun r hr => ?_) (by oomega) hb⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

/-- After the output: `out` holds the message, or zeros. -/
abbrev O3 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    ∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0

theorem out_vp (P : EP) : VP (O1 h g P) (.seq (.block outSet) (countLoop outBody)) (O3 h g P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hK' := hi₀.k64
  let X : State → Mem → Prop := fun σ m => Ko h g P σ m ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ)
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ X σ s.mem ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧
      s.gpr .edi = P.out ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .edx = okW h g P σ)
    (VP.taint [.esp, .ebp] outSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hb⟩ => ?_) ?_
  · simp only [outSet, atS, addi, ld, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg (dec_arg (j := 0) (by decide)) (by decide) (by decide) fun t3 c3 u3 =>
      c3.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t4 c4 u4 =>
      c4.wp_slot hg (d := sOk) (by decide) (by decide) (by decide) fun t5 c5 u5 => WP.block_nil ?_
    have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨c5, m5 ▸ ⟨hk, hb⟩, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
    · rw [u5.other _ (by decide), u4.gpr]; rfl
    · rw [u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, hk.2.2]
  have hf := ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at hf
  have wb : WBuf P.lay P.out P.K := ⟨hf, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩
  have sO : ∀ {o n : Nat}, o + n ≤ oRsa → (sR P.scr o n).Disjoint P.OUT := by
    intro o n hon
    have hs := hi₀.slK
    unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
    have d : P.OUT.Disjoint P.SCR := by
      have := ok.wrw
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at this
      exact this.1.2
    have hf' := ok.fits P.SCR (by simp)
    simp only [BitVec.toNat_setWidth] at hf'
    exact (d.sub_right (Offset.sub_base _ (by unfold oRsa at hon; omega))).symm
  have ko : ∀ σ m m', X σ m → Frame [⟨P.out.setWidth 64, P.K⟩] m m' → X σ m' := fun σ m m' ⟨hk, hb⟩ hf' =>
    ⟨hk.keep h g hf' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨out_slot hk.1.1 (by decide), out_slot hk.1.1 (by decide), out_slot hk.1.1 (by decide)⟩,
     fun j hj => by
      rw [← hb j hj]
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sO (o := oBuf + j) (n := 1) (by oomega) _ (Region.contains_self _ _)⟩
  refine (outLoop_vp wb (hg.rbuf (o := oBuf) (n := P.K) (by oomega) (by omega)) (by omega) (X := X) ko
    (f := fun σ i => Bp h g P σ (i + aV h g P σ))
    (fun σ m hx i hi => by rw [hg.byteAt_scr (by oomega)]; exact hx.2 i (by omega)) (w := okW h g P)).mono
    (fun σ s hh => hh) fun σ s ⟨hc, ⟨hk, _⟩, hb⟩ => ⟨hc, hk, fun i hi => by rw [hb i hi, and_maskOf]⟩

end VG.Proof.RsaOaep.X86.Dec
