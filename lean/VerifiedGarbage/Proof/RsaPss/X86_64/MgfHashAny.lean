module

public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect
public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments: MGF1's hash

`mgfHashAny G` leaves the digest of the message of `ℓ` bytes (`sL`) in `Y`,
followed by zeros up to two blocks (`sNb`), at `scratch + oDig`
(`mgfHashAny_ok`): `0x80` at the offset `ℓ` (`slotPad80_ok`), the length
field, and one block compressed directly if the padded message fits it
(`lastBlk = 0`), as `mgfDirectHash` does, or two, as `ctHash` does.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.RsaPss (lastBlk padded)

theorem slotPad80_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ N : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ) (hℓ : ℓ < N) (hN : N ≤ 2048) :
    WP isa slotPad80 t (PadResult t F S V W ℓ N) := by
  unfold slotPad80
  have h27 : t.mem.readW (off F sL) 64 = BitVec.ofNat 64 ℓ := by rw [R.rd (d := sL) 27 rfl (by decide), hl]
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdx] (Q := fun u => u.gpr .rcx = off S oY ∧
      u.gpr .rdx = BitVec.ofNat 64 ℓ ∧ u.mem = t.mem) ?_ rfl) fun u ⟨⟨hcx, hdx, hm⟩, ku⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.word] at hs
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide), L.ld (d := sL) (by decide), h27]
  have Lu := L.congr (ku.gpr (by decide)) ku.2.2 (by rw [hm])
  have Ru : Rep u.mem F S V W := hm ▸ R
  have hb : oY + ℓ < oRsa := by unfold oY oRsa; omega
  refine WP.mono (WP.keep [.rax] (Q := fun v =>
      v.mem = u.mem.writeW (off S (oY + ℓ)) (u.mem (off S (oY + ℓ)) ||| 0x80)) ?_ rfl)
    fun v ⟨hv, kv⟩ => ?_
  · xrun [ea_ix0, hcx, hdx, off_plus, Lu.sld8 hb, Lu.sst8 hb, fixed_or80]
  · have Rv : Rep v.mem F S (v80 V ℓ N) W := by
      rw [hv]
      have rr := Ru.wb Lu.geo (o := oY + ℓ) hb (u.mem (off S (oY + ℓ)) ||| 0x80)
      refine (congrArg (fun V' => Rep _ F S V' W) (funext fun o => ?_)).mpr rr
      simp only [v80, upd, Ru.scr (oY + ℓ) hb]
      by_cases he : o = oY + ℓ
      · subst he
        simp [hℓ]
      · by_cases hi : oY ≤ o ∧ o < oY + N
        · rw [ifp hi, ifn he, ifn (by omega)]
          exact BitVec.or_zero
        · rw [ifn hi, ifn he]
    exact ⟨Lu.of_rep Ru Rv (kv.gpr (by decide)) kv.2.2, (ku.trans kv).mono (by decide), Rv⟩

variable {G : Hash} (hG : HashOK G) (K : Callees G)

/-- `rax := [sFb]`, ZF set if it is zero. -/
theorem testFb_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {fb : Nat} (hf : W 30 = BitVec.ofNat 64 fb) (hfb : fb < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (sp sFb)), .alu .test .rax (.reg .rax)]) u fun u' =>
      u'.zf = some (decide (fb = 0)) ∧ u'.mem = u.mem ∧ Keep [.rax] u u' := by
  have h30 : u.mem.readW (off F sFb) 64 = BitVec.ofNat 64 fb := by rw [R.rd (d := sFb) 30 rfl (by decide), hf]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.zf = some (decide (fb = 0)) ∧ u'.mem = u.mem) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [ea_sp, L.rsp, L.ld (d := sFb) (by decide), h30, BitVec.and_self, ofNat_beq_zero hfb]

include K in
/-- The digest of the message of `ℓ` bytes in `Y`, followed by zeros up to
two blocks. -/
theorem mgfHashAny_gen {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ)
    (hn : W 28 = BitVec.ofNat 64 2) (hfit : ℓ + 1 + G.P.L ≤ 2 * G.P.B) :
    WP isa (mgfHashAny G) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧
      ∃ V' W', Rep t'.mem F S V' W' ∧ (∀ o < oRsa, ctOut o → V' o = V o) ∧
        (∀ k < nW, k ≠ 29 → k ≠ 30 → W' k = W k) ∧
        ∀ msg : List Byte, msg.length = ℓ → (∀ i < 2 * G.P.B, V (oY + i) = msg.getD i 0) →
          (List.range G.D).map (fun i => V' (oDig + i)) = hG.SH.H.hash msg := by
  have hB := hG.B_le
  have hB0 := hG.B_pos
  have hN := hG.N_le
  have hL := hG.dims.L
  have hNL := hG.hNL
  have hDN := hG.hDN
  have hso := hG.hso
  have c1 : oY = 3584 := rfl
  have c2 : oLen = 2368 := rfl
  have c3 : oDig = 2304 := rfl
  have c4 : oSt = 2048 := rfl
  have c5 : oSel = 2240 := rfl
  have hnb : 2 * G.P.B ≤ 2048 := by omega
  have hfb : lastBlk G.P.B G.P.L ℓ < 2 := (Nat.div_lt_iff_lt_mul hB0).mpr (by omega)
  unfold mgfHashAny seqs seqs seqs seqs
  -- `init`.
  refine WP.seq (WP.mono (ctInit_ok hG K L R) fun u1 ⟨L1, rd1, wr1, cs1, R1, iv1⟩ => ?_)
  -- `0x80`.
  refine WP.seq (WP.mono (slotPad80_ok L1 R1 (N := 2 * G.P.B) hl (by omega) hnb) fun u2 P => ?_)
  -- The length field.
  refine WP.seq (WP.mono (lenField_ok hG P.L P.R hl (by omega)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  have hlen : ∀ (V' : Nat → Byte), ∀ i < G.P.L, lenV V' (hG.md.lenBytes ℓ) (oLen + i) = (hG.md.lenBytes ℓ).getD i 0 :=
    fun V' i hi => by simp only [lenV, hG.md.lenBytes_length]; rw [ifp (by omega), Nat.add_sub_cancel_left]
  -- Whether one block holds the padded message.
  refine WP.seq (WP.mono (testFb_ok L3 R3 (fb := lastBlk G.P.B G.P.L ℓ) (by simp [upd]) (by omega)) fun u4 ⟨hz4, hm4, k4⟩ => ?_)
  have L4 : Lay u4 F S := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 := hm4 ▸ R3
  have hcs : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], r ∈ calleeSaved := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
  refine WP.ite (M := isa) _ (show isa.eval .e u4 = _ from hz4) (fun hb => ?_) (fun hb => ?_)
  · -- One block.
    rw [decide_eq_true_eq] at hb
    have hone : ℓ + G.P.L < G.P.B := by
      by_contra h
      have : 1 ≤ lastBlk G.P.B G.P.L ℓ := (Nat.le_div_iff_mul_le hB0).mpr (by omega)
      omega
    unfold directRest seqs seqs seqs
    refine WP.seq (WP.mono (directLen_ok hG L4 R4 (hlen _)) fun u5 ⟨L5, k5, R5⟩ => ?_)
    refine WP.seq (WP.mono (startZero_ok L5 R5) fun u0 ⟨L0, k0, R0⟩ => ?_)
    refine WP.seq (WP.mono (compCall_ok hG L0 R0 (b := 0) (by omega) (by simp [upd]))
      fun u6 ⟨L6, rd6, wr6, cs6, R6, st6⟩ => ?_)
    have iv0 : hG.md.stateAt u0.mem (off S oSt) = hG.iv := by
      rw [← iv1]
      refine stateAt_rep hG R1 R0 (by unfold oSt oRsa; omega) fun i hi => ?_
      simp only [cpV, lenV, v80]
      rw [ifn (by unfold oY oSt; omega), ifn (by unfold oLen oSt; omega), ifn (by unfold oY oSt; omega)]
    refine WP.mono (digestAt_ok hG L6 R6 (src := oSt) (by unfold oSt oDig; omega))
      fun u7 ⟨L7, k7, R7⟩ => ?_
    refine ⟨L7, k7.2.1.trans (rd6.trans (k0.2.1.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (P.keep.2.1.trans rd1)))))),
      k7.2.2.trans (wr6.trans (k0.2.2.trans (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (P.keep.2.2.trans wr1)))))),
      ?_, _, _, R7, ?_, ?_, ?_⟩
    · intro r hr
      have hc := hcs r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [k7.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide), cs6 r hc,
        k0.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        k5.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        k4.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        k3.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        P.keep.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide), cs1 r hc]
    · intro o ho ⟨h1, h2⟩
      have hno : ¬ (oDig ≤ o ∧ o < oDig + G.P.N) := by omega
      simp only [hno, ite_false]
      simp only [cpV, lenV, v80, inR_cons, inR_nil, or_false]
      rw [ifn (by omega), ifn (by omega), ifn (by rw [hG.md.lenBytes_length]; omega), ifn (by omega), ifn (by omega)]
    · intro k hk h29 h30
      simp [upd, h29, h30]
    · intro msg hml hY
      subst hml
      have fb0 : lastBlk G.P.B G.P.L msg.length = 0 := Nat.div_eq_of_lt hone
      rw [hG.hash, MdStream.Md.hash, ← range_map_getD (by rw [hG.md.digest_length]; exact hDN)]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      simp only [show oDig ≤ oDig + i ∧ oDig + i < oDig + G.P.N from ⟨by omega, by omega⟩,
        Nat.add_sub_cancel_left]
      rw [st6, iv0]
      refine congrArg (fun x => (hG.md.digest x).getD i 0) ?_
      rw [RsaPss.pad_length hG.md msg hB0 (by omega), fb0,
        Nat.zero_add, Nat.mul_one, Nat.div_self hB0, MdStream.Md.compressList_one]
      refine congrArg (hG.md.compress hG.iv) (hG.md.parse_congr fun j hj => ?_)
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [RsaPss.pad_getD hG.md msg hB0 (by omega) (by simpa only [fb0, Nat.zero_add, Nat.mul_one] using hj)]
      refine y_copied msg _ hone (hG.md.lenBytes_length _) _ (fun j' hj' => ?_) j hj
      simp only [lenV, v80, inR_cons, inR_nil, or_false, hG.md.lenBytes_length]
      rw [ifn (by omega), ifp (by omega), ifn (by omega), Nat.add_sub_cancel_left, hY j' (by omega)]
  · -- Two blocks.
    rw [decide_eq_false_iff_not] at hb
    unfold genericRest seqs seqs
    refine WP.seq (WP.mono (lenLoop_ok hG L4 R4 (len := hG.md.lenBytes ℓ) (hlen _)
      (by simp [upd]) (by simp [upd, hn]) hfb hnb) fun u5 O => ?_)
    refine WP.seq (WP.mono (compLoop_ok hG O.L O.R ?_ (by simp [upd]) (by simp [upd, hn]) hfb hnb)
      fun u6 ⟨L6, rd6, wr6, cs6, V6, R6, keep6, st6, sel6⟩ => ?_)
    · rw [← iv1]
      refine stateAt_rep hG R1 O.R (by unfold oSt oRsa; omega) fun i hi => ?_
      simp only [lenAt, lenV, v80]
      rw [ifn (by unfold oY oSt; omega), ifn (by unfold oLen oSt; omega), ifn (by unfold oY oSt; omega)]
    refine WP.mono (digestOut_ok hG L6 R6) fun u7 ⟨L7, k7, R7⟩ => ?_
    have hO : (if lastBlk G.P.B G.P.L ℓ < 2 then G.P.L else 0) = G.P.L := by rw [ifp hfb]
    have hfbB' : G.P.B * lastBlk G.P.B G.P.L ℓ + G.P.B ≤ 2048 := by
      rw [← Nat.mul_add_one]
      have : G.P.B * (lastBlk G.P.B G.P.L ℓ + 1) ≤ G.P.B * 2 := Nat.mul_le_mul_left _ hfb
      omega
    have hfbB : G.P.B * (lastBlk G.P.B G.P.L ℓ + 1) ≤ 2 * G.P.B := by
      rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ hfb
    have hsel := sel6 hfb
    refine ⟨L7, k7.2.1.trans (rd6.trans (O.keep.2.1.trans (k4.2.1.trans (k3.2.1.trans (P.keep.2.1.trans rd1))))),
      k7.2.2.trans (wr6.trans (O.keep.2.2.trans (k4.2.2.trans (k3.2.2.trans (P.keep.2.2.trans wr1))))), ?_, _, _, R7,
      ?_, ?_, ?_⟩
    · intro r hr
      have hc := hcs r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [k7.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide), cs6 r hc,
        O.keep.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        k4.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        k3.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        P.keep.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide), cs1 r hc]
    · intro o ho ⟨h1, h2⟩
      have hno : ¬ (oDig ≤ o ∧ o < oDig + G.P.N) := by omega
      simp only [hno, ite_false]
      rw [keep6 o ho (by simp only [inR_cons, inR_nil, or_false]; omega)]
      simp only [lenAt, lenV, v80, inR_cons, inR_nil, or_false]
      rw [ifn (by omega), ifn (by rw [hG.md.lenBytes_length]; omega), ifn (by omega), ifn (by omega)]
    · intro k hk h29 h30
      simp [upd, h29, h30]
    · intro msg hml hY
      subst hml
      rw [hG.hash, MdStream.Md.hash, ← range_map_getD (by rw [hG.md.digest_length]; exact hDN)]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      simp only [show oDig ≤ oDig + i ∧ oDig + i < oDig + G.P.N from ⟨by omega, by omega⟩,
        Nat.add_sub_cancel_left]
      rw [hsel]
      refine congrArg (fun x => (hG.md.digest x).getD i 0) ?_
      rw [RsaPss.pad_length hG.md msg hB0 (by omega), Nat.mul_div_cancel_left _ hB0]
      refine hG.md.compressList_congr fun j hj => ?_
      rw [yList_getD _ (by omega), RsaPss.pad_getD hG.md msg hB0 (by omega) hj, hO]
      refine y_padded msg _ rfl (by omega) (hG.md.lenBytes_length _) _ (fun j' hj' => ?_) j hj
      simp only [lenV, v80, inR_cons, inR_nil, or_false, hG.md.lenBytes_length]
      rw [ifn (by omega), ifp (by omega), ifn (by omega), Nat.add_sub_cancel_left, hY j' (by omega)]

end VG.Proof.RsaPss.X86_64.Any
