module

public import VerifiedGarbage.Proof.RsaPss.X86.VfCall
public import VerifiedGarbage.Proof.RsaPss.X86.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: after the call

As on ARMv7 (`Proof/RsaPss/Arm/VfAcc.lean`): the pieces after the call are
proven over the state `τ` the call leaves (`VQ.reidx`), so that `EM`'s bytes
are those of `τ` (`emv`). `acc` (`accW`): `EM`'s last byte `⊕ 0xbc`, its first
if `lo = 1`, and the top bits of `maskedDB`'s first byte (`acc_vp`); then
`DB = maskedDB ⊕ MGF1(H, dbLen)` with its top bits cleared (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (andByte add_ofNat_sub away3_scr away3_slot away3_ctW Away3)

variable (h : PssHash)

/-- A state of a body is one the body may start from. -/
theorem St.ok_self {L : Lay} {σ s : State} (hs : L.St σ s) : L.Ok s :=
  { sp := hs.sp, rd := hs.rd.trans hs.ok.rd, wr := hs.wr.trans hs.ok.wr, BC := hs.ok.BC, fit := hs.ok.fit,
    stk := hs.ok.stk, ret := hs.ok.ret, wro := hs.ok.wro, wrw := hs.ok.wrw, fits := hs.ok.fits,
    args := fun _ hj => hs.arg hj }

theorem In.self {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) : In h.D P s :=
  { ok := St.ok_self hs, kv := hi.kv, el1 := hi.el1, elK := hi.elK, glK := hi.glK, scrK := hi.scrK, rlK := hi.rlK,
    slt32 := hi.slt32, scl32 := hi.scl32, nB := nB_at h hi hs, eB := eB_at h hi hs, pw := pw_at h hi hs }

/-- `EM`'s bytes, as the call leaves them. -/
abbrev emv (P : EP) (τ : State) (i : Nat) : Byte := τ.mem (sa P.scr (oEm + i))

/-- `acc`. -/
abbrev accW (P : EP) (τ : State) : BitVec 32 :=
  ((emv P τ (P.K - 1)).setWidth 32 ^^^ 0xbc ||| (emv P τ 0).setWidth 32 &&& (0 - BitVec.ofNat 32 (lo P))) |||
    (emv P τ (lo P)).setWidth 32 &&& (cW ((n0 P).setWidth 32) ^^^ 0xFF)

/-- After the call, over the state `τ` it leaves. -/
abbrev W0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ In h.D P τ ∧ fits h P ∧ Bm h P s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i

theorem w0_self {P : EP} {σ s : State} (hv : V2 h P σ s) : W0 h P s s := by
  obtain ⟨⟨hc, hi, hf, hb⟩, -⟩ := hv
  have hi' := In.self h hi hc.st
  exact ⟨⟨⟨hi'.ok, hc.st.sp, rfl, rfl, Frame.refl _ _⟩, hc.ebp⟩, hi', hf, hb, fun _ _ => rfl⟩

/-- What `acc` keeps. -/
abbrev Ka (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ m.readW ((P.lay h.D).fr sAcc) 32 = accW P τ

/-- The bounds of the encoding when everything fits. -/
theorem fitB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ eLen P + 1 ≤ dbN h P ∧ lo P + dbN h P + h.D + 1 = P.K ∧ P.K ≤ 1024 ∧ h.D ≤ 64 ∧ 0 < h.D ∧
      64 ≤ P.K := by
  have := hf.2
  have := hi.k1024
  have := hi.k64
  have := h.D_le
  have := h.N_le
  have := h.D_pos
  have : lo P ≤ 1 := by unfold lo; split <;> omega
  refine ⟨this, ?_, ?_, hi.k1024, by omega, h.D_pos, hi.k64⟩ <;> unfold dbN <;> omega

/-- `acc`, to its slot. -/
theorem acc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (W0 h P) (.seq (.block accSet) (.block acc0))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i) := by
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
  refine VP.seq (G := fun τ s => W0 h P τ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oEm ∧
      s.gpr .edi = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P))
    (VP.taint [.esp, .ebp] accSet_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hi, hf', hb, he⟩ => ?_)
    (VP.taint _ acc0_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hi, hf', hb, he⟩, si, di, bx⟩ => ?_)
  · simp only [accSet, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => ?_
    have c3 : Ctx (P.lay h.D) P.scr τ t3 :=
      ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp]) (by rw [hg.aArg ok 1 (by simp)]; exact
      (by rw [c3.st.rd, c3.st.wr]; exact c3.st.ok.arg_read (vf_arg h (by decide)))) fun t4 u4 => ?_
    refine wp_subi fun t5 u5 _ _ => wp_mov fun t6 u6 => ?_
    have c6 : Ctx (P.lay h.D) P.scr τ t6 :=
      ((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c6.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c6.rFr hg sLo (by decide)) fun t7 u7 => WP.block_nil ?_
    have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    have esi2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 oEm := by rw [u2.gpr, u1.gpr, hc.ebp]
    refine ⟨⟨c6.upd u7 (by decide) (by decide), hi, hf', m7 ▸ hb, m7 ▸ he⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other]; exact esi2
    · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, u4.gpr, u3.gpr, esi2, u3.mem, u2.mem, u1.mem,
        hg.aArg ok 1 (by simp), hc.st.arg (vf_arg h (by decide)),
        show (P.lay h.D).argv.getD 1 0 = BitVec.ofNat 32 P.K from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        add_ofNat_sub (by omega)]
    · rw [u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), esi2, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide),
        hb.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have aK : addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) 0 = sa P.scr (oEm + (P.K - 1)) := by
      rw [hg.addrD (by omega)]; congr 1; omega
    have a0 : addr (P.scr + BitVec.ofNat 32 oEm) 0 = sa P.scr (oEm + 0) := hg.addrD (by omega)
    have al : addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) 0 = sa P.scr (oEm + lo P) := by
      rw [hg.addrD (by omega), Nat.add_zero]
    have rK : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + (P.K - 1))) 1 := hg.rd hc.st (by omega)
    have r0' : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + 0)) 1 := hg.rd hc.st (by omega)
    have rl : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    simp only [acc0, mi, ld, st, Impl.RsaPkcs1Sig.X86.at_, Impl.RsaPkcs1Sig.X86.stk]
    refine wp_movzx8 (a := sa P.scr (oEm + (P.K - 1))) (by rw [ea_at, di]; exact aK) rK fun t1 u1 => ?_
    refine wp_xorI fun t2 u2 => ?_
    refine wp_movzx8 (a := sa P.scr (oEm + 0))
      (by rw [ea_at, u2.other _ (by decide), u1.other _ (by decide), si]; exact a0)
      (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact r0') fun t3 u3 => ?_
    refine wp_movi fun t4 u4 => ?_
    have c4 : Ctx (P.lay h.D) P.scr τ t4 :=
      (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4
        (by decide) (by decide)
    refine wp_subm (B := (P.lay h.D).B) (by rw [c4.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c4.rFr hg sLo (by decide)) fun t5 u5 => ?_
    refine wp_and fun t6 u6 => wp_or fun t7 u7 => ?_
    refine wp_movzx8 (a := sa P.scr (oEm + lo P))
      (by simp (disch := decide) only [ea_at, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
        u1.other]; rw [bx]; exact al)
      (by rw [u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]
          exact rl) fun t8 u8 => ?_
    have c8 : Ctx (P.lay h.D) P.scr τ t8 :=
      (((c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8
        (by decide) (by decide)
    refine c8.wp_slot hg (d := sC) (by decide) (by decide) (by decide) fun t9 c9 u9 => ?_
    refine wp_xorI fun t10 u10 => wp_and fun t11 u11 => wp_or fun t12 u12 => ?_
    have c12 : Ctx (P.lay h.D) P.scr τ t12 :=
      ((c9.upd u10 (by decide) (by decide)).upd u11 (by decide) (by decide)).upd u12 (by decide) (by decide)
    refine c12.wp_st hg (d := sAcc) (by decide) fun t13 c13 m13 => WP.block_nil ?_
    have mm : t12.mem = s.mem := by
      rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    have v : t12.gpr .eax = accW P τ := by
      simp (disch := decide) only [u12.gpr, u11.gpr, u11.other, u10.gpr, u10.other, u9.gpr, u9.other,
        u8.gpr, u8.other, u7.gpr, u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr,
        u3.other, u2.gpr, u1.gpr]
      rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide), hb.2.1,
        hb.1, he _ (by omega), he _ (by omega), he _ (by omega)]
      rfl
    have m : t13.mem = s.mem.writeW ((P.lay h.D).fr sAcc) (accW P τ) := by rw [m13.mem, mm, v]
    have fr : Frame [slotR (P.lay h.D) sAcc] s.mem t13.mem := by rw [m]; exact slot_frame _ _ _ _
    refine ⟨c13, ⟨hi, hf', ?_, by rw [m, Mem.readW_writeW_self32]⟩, fun i hi' => ?_⟩
    · rw [m]
      exact ⟨by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.1,
        by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.1,
        by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.1,
        by rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.2⟩
    · rw [← he i hi']
      exact fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hg.slot ok (o := oEm + i) (n := 1) (d := sAcc) (k := 4) (by omega) (by rw [hg.F]; decide)).symm _
          (Region.contains_self _ _)

/-- `H`, as the call leaves it. -/
abbrev seedV (P : EP) (τ : State) : List Byte := (List.range h.D).map fun i => emv P τ (lo P + dbN h P + i)

/-- The mask. -/
abbrev mkV (P : EP) (τ : State) : List Byte := Spec.Mgf1.mgf1 h.G (seedV h P τ) (dbN h P)

/-- `DB`, unmasked, with its top bits cleared. -/
abbrev dbF (P : EP) (τ : State) (i : Nat) : Byte :=
  if i = 0 then (emv P τ (lo P) ^^^ (mkV h P τ).getD 0 0) &&& (cW ((n0 P).setWidth 32)).setWidth 8
  else emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0

/-- After the unmasking. -/
abbrev U0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
    (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- `DB = maskedDB ⊕ MGF1(H, dbLen)`, its top bits cleared. -/
theorem unmask_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i)
      (.seq (.seq (mgfXor h.H) (.block topSet)) (.block topAnd)) (U0 h P) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  have hB := h.B_le
  have mp : MP h (P.lay h.D) P.scr (lo P) (dbN h P) (seedV h P) (Ka h P) := by
    refine ⟨hg, by omega, by omega, fun τ => by simp, fun τ m m' ⟨hi, hf', hb, ha⟩ hf'' => ⟨hi, hf', ?_⟩,
      fun τ m hk => hk.2.2.1.2.1, fun τ m hk => hk.2.2.1.2.2.1⟩
    have away : ∀ r ∈ mgfW h (P.lay h.D) P.scr (lo P) (dbN h P), Away3 (P.lay h.D) r ∧
        (slotR (P.lay h.D) sAny).Disjoint r ∧ (slotR (P.lay h.D) sAcc).Disjoint r := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨away3_ctW h hg (by omega) r hr, ctW_slot h hg (by omega) (by decide) (by decide) (by decide) r hr,
          ctW_slot h hg (by omega) (by decide) (by decide) (by decide) r hr⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨away3_scr hg (by omega), hg.slot ok (by omega) (by rw [hg.F]; decide),
            hg.slot ok (by omega) (by rw [hg.F]; decide)⟩
        all_goals exact ⟨away3_slot (by decide) (by decide), slotSep (by decide) (by decide) (by decide),
          slotSep (by decide) (by decide) (by decide)⟩
    refine ⟨⟨slot_keep hf'' (fun r hr => (away r hr).1.1) hb.1, slot_keep hf'' (fun r hr => (away r hr).1.2.1) hb.2.1,
      slot_keep hf'' (fun r hr => (away r hr).1.2.2) hb.2.2.1, slot_keep hf'' (fun r hr => (away r hr).2.1) hb.2.2.2⟩,
      slot_keep hf'' (fun r hr => (away r hr).2.2) ha⟩
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P))
    ((mgf_vp h mp (dbv := fun τ i => emv P τ (lo P + i))).mono (fun τ s ⟨hc, hk, he⟩ => ⟨hc, hk,
      fun i hi => by rw [Nat.add_assoc]; exact he _ (by omega),
      fun i hi => by rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega)]; simp [hi, Nat.add_assoc]⟩)
      (fun _ _ h => h) |>.seq
    (VP.taint [.esp, .ebp] topSet_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hd, hh⟩ => ?_))
    (VP.taint _ topAnd_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hk, hd, hh⟩, si⟩ => ?_)
  · simp only [topSet, atDb, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => WP.block_nil ?_
    have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c2.upd u3 (by decide) (by decide), m3 ▸ hk, m3 ▸ hd, m3 ▸ hh⟩, ?_⟩
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.2.2.1.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) 0 = sa P.scr (oEm + lo P) := by
      rw [hg.addrD (by omega), Nat.add_zero]
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega)
    simp only [topAnd, Impl.RsaPkcs1Sig.X86.at_, Impl.RsaPkcs1Sig.X86.stk]
    refine wp_movzx8 (a := sa P.scr (oEm + lo P)) (by rw [ea_at, si]; exact ad) rd fun t1 u1 => ?_
    have c1 : Ctx (P.lay h.D) P.scr τ t1 := hc.upd u1 (by decide) (by decide)
    have rC := c1.rFr hg sC (by decide)
    refine wp_andS (readSrc_mem (B := (P.lay h.D).B) (by rw [c1.st.sp]) (by rw [hg.aFr ok sC (by decide)]; exact rC))
      fun t2 u2 => ?_
    have a2 : t2.ea ⟨.esi, 0⟩ = sa P.scr (oEm + lo P) := by
      rw [ea_at, u2.other .esi (by decide), u1.other .esi (by decide), si]; exact ad
    refine wp_store8 (a := sa P.scr (oEm + lo P)) a2 (by rw [u2.wr, u1.wr]; exact wd) fun t3 u3 => WP.block_nil ?_
    have m3 : t3.mem = s.mem.writeW (sa P.scr (oEm + lo P))
        (s.mem (sa P.scr (oEm + lo P)) &&& (cW ((n0 P).setWidth 32)).setWidth 8) := by
      rw [u3.mem, Reg8.reg, u2.gpr, u2.mem, u1.gpr, u1.mem, hg.aFr ok sC (by decide), hk.2.2.1.1, andByte]
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t3.mem := by
      rw [m3]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    have kk : ∀ d, d + 4 ≤ frameBytes → t3.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
      fun d hd => by
        rw [slot_keep (v := s.mem.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega)
            (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)) rfl]
    have hb' : Bm h P t3.mem := ⟨by rw [kk _ (by decide)]; exact hk.2.2.1.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.1,
      by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.2⟩
    have ha' : t3.mem.readW ((P.lay h.D).fr sAcc) 32 = accW P τ := by rw [kk _ (by decide)]; exact hk.2.2.2
    refine ⟨(c1.upd u2 (by decide) (by decide)).write (by rw [u2.mem, u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)) u3.rd u3.wr (by rw [u3.gpr])
        (by rw [u3.gpr]), ⟨hk.1, hk.2.1, hb', ha'⟩, fun i hi => ?_, fun i hi => ?_⟩
    · rw [m3, sa_write P.scr _ _ (by omega) (by omega)]
      unfold dbF
      by_cases e : i = 0
      · subst e
        rw [ite_eq_left (by omega), ite_eq_left rfl, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega),
          Nat.add_zero]
      · rw [ite_eq_right (by omega), ite_eq_right e, hd i hi]
    · rw [m3, sa_write P.scr _ _ (by omega) (by omega), ite_eq_right (by omega), hh i hi]

end VG.Proof.RsaPss.X86.Vf
