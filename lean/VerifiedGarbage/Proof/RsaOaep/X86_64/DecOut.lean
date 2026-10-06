import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out

/-!
# RSAES-OAEP decryption on x86-64: the outputs

The mask `ok` (`okMask_ok`), the buffer ANDed with it to `out`
(`outLoop_ok`), the length and the result (`decRet_ok`), and the failure
before decoding (`decFail_ok`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

/-- `ok`: all ones iff the private-key operation's result `r` (word 30) is 1
and the accumulator (word 31) is zero. -/
def okW (W : Nat → BitVec 64) : BitVec 64 := zM (W 30 ^^^ 1) &&& zM (W 31)

theorem okMask_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block okMask) u fun u' => Lay u' F S ∧ Keep [.rax, .r11] u u' ∧ u'.gpr .r11 = okW W ∧
      Rep u'.mem F S V (upd W 33 (okW W)) := by
  have G' := L.geo
  refine WP.mono (WP.keep [.rax, .r11] (Q := fun u' => u'.gpr .r11 = okW W ∧
    u'.mem = u.mem.writeW (off F (8 * 33)) (okW W)) ?_ rfl) fun u' ⟨⟨h11, hm⟩, k⟩ => ?_
  · xrun [okMask, ea_sp, L.rsp, L.ld (d := sR) (by decide), L.ld (d := sAcc) (by decide), L.st (d := sOk) (by decide),
      R.slot (d := sR) (k := 30) rfl (by decide) rfl, R.slot (d := sAcc) (k := 31) rfl (by decide) rfl,
      sbb_zM, sbb0_zM, okW]
    exact ⟨BitVec.and_comm _ _, by rw [BitVec.and_comm]; rfl⟩
  have R' : Rep u'.mem F S V (upd W 33 (okW W)) := hm ▸ R.wf G' (k := 33) (by decide) _
  exact ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, h11, R'⟩

/-! ## `out` -/

/-- A byte of the buffer ANDed with the mask `m`. -/
def andB (b : Byte) (m : BitVec 64) : Byte := BitVec.setWidth 8 (BitVec.setWidth 64 b &&& m)

structure OutI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (o : Addr) (k : Nat)
    (m : BitVec 64) (j : Nat) (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S V W
  fr : Frame [⟨o, k⟩] u₀.mem v.mem
  out : ∀ i < j, v.mem (o + BitVec.ofNat 64 i) = andB (V (oBuf + i)) m

/-- The buffer's first `k` bytes, ANDed with `ok` (word 33), to `out` (word
21), a region apart from the frame, our working space and the stack below
the frame. -/
theorem outLoop_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k : Nat} (ho : W 21 = o) (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k)
    (hk1 : k ≤ 1024) (hw : (⟨o, k⟩ : Region) ∈ u.wr) (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa outLoop u fun u' => Lay u' F S ∧ Keep [.rdi, .rcx, .r10, .r11, .r8, .rax] u u' ∧ Rep u'.mem F S V W ∧
      (∀ i < k, u'.mem (o + BitVec.ofNat 64 i) = andB (V (oBuf + i)) (W 33)) ∧ Frame [⟨o, k⟩] u.mem u'.mem := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c3 : oBuf = 1024 := rfl
  unfold outLoop
  refine WP.seq (WP.mono (WP.keep [.rdi, .rcx, .r10, .r11, .r8] (Q := fun v => v.gpr .rdi = o ∧
      v.gpr .rcx = off S oBuf ∧ v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .r11 = W 33 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk'⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sOut) (by decide), L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide),
      L.ld (d := sOk) (by decide), hs, R.slot (d := sOut) (k := 21) rfl (by decide) ho,
      R.slot (d := sK) (k := 23) rfl (by decide) hk, R.slot (d := sOk) (k := 33) rfl (by decide) rfl,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  have hsc : Scr v o k := Scr.of_mem (by rw [hk'.2.2]; exact hw) hnw
  refine WP.mono (byteLoop_ok hk0 (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₃)
    (OutI v F S V W o k (W 33)) ?_ ⟨Lv, Keep.refl _ _, h₅, hm ▸ R, Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun w I => ?_
  · intro j hj w I
    have hdw : w.gpr .rdi = o := (I.keep.gpr (by decide)).trans h₁
    have hcw : w.gpr .rcx = off S oBuf := (I.keep.gpr (by decide)).trans h₂
    have h11w : w.gpr .r11 = W 33 := (I.keep.gpr (by decide)).trans h₄
    have hst : InRegions w.wr (o + BitVec.ofNat 64 j) 1 := by
      have := hsc.st8 (d := j) (by omega); rw [I.keep.2.2]; exact this
    have vb : w.mem (off S (oBuf + j)) = V (oBuf + j) := I.R.scr _ (by unfold oRsa; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.mem = w.mem.writeW (o + BitVec.ofNat 64 j) (andB (V (oBuf + j)) (W 33))) ?_ rfl)
      fun w' ⟨⟨h8', hm'⟩, k'⟩ => ⟨(I.keep.trans k').mono (by decide), h8', fun w'' k'' hm'' h8'' => ?_⟩
    · xrun [ea_ix0, ea_ix, hdw, hcw, h11w, I.r8, off_plus, I.L.sld8 (d := oBuf + j) (by unfold oRsa; omega), vb,
        show o + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = o + BitVec.ofNat 64 j from BitVec.add_zero _, hst, andB]
    · have fw : Frame [⟨o, k⟩] w.mem w''.mem := by
        rw [hm'', hm']
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
      refine ⟨I.L.of_rep I.R (Rep.apart I.R ha fw) (by rw [k''.gpr (by decide), k'.gpr (by decide)])
          (k''.2.2.trans k'.2.2), (I.keep.trans (k'.trans k'')).mono (by decide), h8'', Rep.apart I.R ha fw,
        I.fr.trans fw, fun i hi => ?_⟩
      rw [hm'', hm', VG.WriteBytes.writeW8_apply]
      by_cases h : i = j
      · subst h; simp
      · rw [ifn (Offset.add_ofNat_ne o (by omega) (by omega) h), I.out i (by omega)]
  · have fr : Frame [⟨o, k⟩] u.mem w.mem := by rw [← hm]; exact I.fr
    exact ⟨I.L, (hk'.trans I.keep).mono (by decide), I.R, I.out, fr⟩

/-! ## The length and the result -/

/-- `(r = 2) ? 2 : 0`, from word 30. -/
def faultW (W : Nat → BitVec 64) : BitVec 64 := zM (W 30 ^^^ 2) &&& 2

theorem faultBit_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block faultBit) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧ u'.gpr .rax = faultW W := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = faultW W) ?_ rfl)
    fun u' ⟨⟨hm, h⟩, k⟩ => ⟨k, hm, h⟩
  xrun [faultBit, ea_sp, L.rsp, L.ld (d := sR) (by decide), R.slot (d := sR) (k := 30) rfl (by decide) rfl,
    sbb_zM, sbb0_zM, faultW]

/-- The length to `*msg_len`, a region apart from the frame, our working
space and the stack below it. -/
theorem decRet_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pm : Addr} {k : Nat} (hpm : W 29 = pm) (hk : W 23 = BitVec.ofNat 64 k)
    (hkD : 2 * Hm.D + 2 ≤ k) (hD64 : Hm.D ≤ 64) (hw : (⟨pm, 8⟩ : Region) ∈ u.wr)
    (hnw : pm.toNat + 8 ≤ 2 ^ 64) (ha : Apart F S ⟨pm, 8⟩) :
    WP isa (.block (decRet Hm)) u fun u' => Keep [.r11, .rax, .rdi] u u' ∧
      u'.mem = u.mem.writeW pm ((BitVec.ofNat 64 (k - (2 * Hm.D + 2)) - W 32) &&& W 33) ∧
      u'.gpr .rax = faultW W ||| (W 33 &&& 1) := by
  have hst : InRegions u.wr pm 8 := by
    have := (Scr.of_mem hw hnw).st (d := 0) (by decide)
    rwa [show off pm 0 = pm from BitVec.add_zero _] at this
  rw [show decRet Hm = [.mov .r11 (.mem (sp sOk)), .mov .rax (.mem (sp sK)), .alu .sub .rax (im (2 * Hm.D + 2)),
      .alu .sub .rax (.mem (sp sIdx)), .alu .and .rax (.reg .r11), .mov .rdi (.mem (sp sMl)),
      .store (at_ .rdi) .rax] ++ (([.alu .and .r11 (.imm 1)] : List Instr) ++ faultBit ++
      ([.alu .or .rax (.reg .r11)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .rax, .rdi] (Q := fun v => v.gpr .r11 = W 33 ∧
      v.mem = u.mem.writeW pm ((BitVec.ofNat 64 (k - (2 * Hm.D + 2)) - W 32) &&& W 33)) ?_ rfl)
    fun v ⟨⟨h11, hm⟩, kv⟩ => ?_
  · xrun [im, ea_sp, ea_at0, L.rsp, L.ld (d := sOk) (by decide), L.ld (d := sK) (by decide),
      L.ld (d := sIdx) (by decide), L.ld (d := sMl) (by decide), hst,
      R.slot (d := sOk) (k := 33) rfl (by decide) rfl, R.slot (d := sK) (k := 23) rfl (by decide) hk,
      R.slot (d := sIdx) (k := 32) rfl (by decide) rfl, R.slot (d := sMl) (k := 29) rfl (by decide) hpm,
      VG.Proof.MlKem.X86_64.sx_ofNat (show 2 * Hm.D + 2 < 2 ^ 31 by omega),
      VG.Offset.ofNat_sub_ofNat (show 2 * Hm.D + 2 ≤ k by omega)]
  have fv : Frame [⟨pm, 8⟩] u.mem v.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have Rv := Rep.apart R ha fv
  have Lv : Lay v F S := L.of_rep R Rv (kv.gpr (by decide)) kv.2.2
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun x => x.gpr .r11 = W 33 &&& 1 ∧ x.mem = v.mem) ?_ rfl)
    fun x ⟨⟨h11x, hmx⟩, kx⟩ => ?_
  · xrun [h11]
  have Lx : Lay x F S := Lv.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  refine WP.mono (faultBit_ok Lx (hmx ▸ Rv)) fun y ⟨ky, hmy, hay⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun z => z.gpr .rax = faultW W ||| (W 33 &&& 1) ∧ z.mem = y.mem) ?_ rfl)
    fun z ⟨⟨haz, hmz⟩, kz⟩ => ⟨(((kv.trans kx).trans ky).trans kz).mono (by decide), by rw [hmz, hmy, hmx, hm], haz⟩
  xrun [hay, ky.gpr (show Reg.r11 ∉ [Reg.rax] by decide), h11x]

/-- The failure before decoding: zeros to `out` and `*msg_len`, and
`(r = 2) ? 2 : 0`. -/
theorem decFail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o pm : Addr} {k : Nat} (ho : W 21 = o) (hpm : W 29 = pm)
    (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k) (hk1 : k ≤ 1024) (hw : (⟨o, k⟩ : Region) ∈ u.wr)
    (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) (hwm : (⟨pm, 8⟩ : Region) ∈ u.wr)
    (hnm : pm.toNat + 8 ≤ 2 ^ 64) (ham : Apart F S ⟨pm, 8⟩) (hom : Region.Disjoint ⟨o, k⟩ ⟨pm, 8⟩) :
    WP isa decFail u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      Spec.Rsa.bytesAt u'.mem o k = List.replicate k 0 ∧ u'.mem.readW pm 64 = 0 ∧
      Frame [⟨o, k⟩, ⟨pm, 8⟩] u.mem u'.mem ∧ u'.gpr .rax = faultW W := by
  unfold decFail
  refine WP.seq (WP.mono (zeroOut_ok L R ho hk hk0 hk1 hw hnw ha) fun t1 ⟨L1, k1, R1, hax1, hz1, f1⟩ => ?_)
  have hst : InRegions t1.wr pm 8 := by
    have := (Scr.of_mem (by rw [k1.2.2]; exact hwm) hnm).st (d := 0) (by decide)
    rwa [show off pm 0 = pm from BitVec.add_zero _] at this
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi] (Q := fun v => v.mem = t1.mem.writeW pm (0#64)) ?_ rfl) fun v ⟨hm, kv⟩ => ?_
  · xrun [ea_sp, ea_at0, L1.rsp, L1.ld (d := sMl) (by decide), hst, hax1,
      R1.slot (d := sMl) (k := 29) rfl (by decide) hpm]
    rfl
  have fv : Frame [⟨pm, 8⟩] t1.mem v.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have Rv := Rep.apart R1 ham fv
  have Lv : Lay v F S := L1.of_rep R1 Rv (kv.gpr (by decide)) kv.2.2
  refine WP.mono (faultBit_ok Lv Rv) fun y ⟨ky, hmy, hay⟩ => ?_
  have hmy' : y.mem = t1.mem.writeW pm (0#64) := hmy.trans hm
  refine ⟨Lv.congr (ky.gpr (by decide)) ky.2.2 (by rw [hmy]), ((k1.trans kv).trans ky).mono (by decide),
    hmy ▸ Rv, ?_, by rw [hmy']; exact Mem.readW_writeW_self64 _ _ _, ?_, hay⟩
  · rw [← hz1]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [hmy]
    exact fv.bytes (R := ⟨o, k⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hom) (show k ≤ 2 ^ 64 by omega)
      (List.mem_range.mp hi)
  · rw [hmy]
    exact (f1.sub fun r hr => ⟨r, by simp [List.mem_singleton.mp hr], fun _ h => h⟩).trans
      (fv.sub fun r hr => ⟨r, by simp [List.mem_singleton.mp hr], fun _ h => h⟩)

end VG.Proof.RsaOaep.X86_64
