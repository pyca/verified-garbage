import VerifiedGarbage.Proof.RsaOaep.AArch64.DecLoops

/-!
# RSAES-OAEP decryption on AArch64: the outputs

As on x86-64 (`Proof/RsaOaep/X86_64/DecOut.lean`): the mask `ok`
(`okMask_ok`), the buffer ANDed with it to `out` (`outLoop_ok`), the length
and the result (`decRet_ok`), and zeros to `out` (`zeroOut_ok`, which
encryption's failure uses too).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- A region apart from the frame, our working space and the stack below
the frame. -/
structure Apart (F S : Addr) (r : Region) : Prop where
  dF : Region.Disjoint r ⟨F, frameBytes⟩
  dS : Region.Disjoint r ⟨S, oRsa⟩
  dK : Region.Disjoint r (retR F)

/-- What a step in `r`, apart from the frame and our working space, leaves of `Rep`. -/
theorem Rep.apart {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (_ : Geo F S)
    (R : Rep m F S V W) {r : Region} (ha : Apart F S r) (hf : Frame [r] m m') : Rep m' F S V W where
  scr o ho := by
    rw [hf _ fun r' hr' hc => ?_]
    · exact R.scr o ho
    rw [List.mem_singleton.mp hr'] at hc
    exact ha.dS _ hc ((cS S (o := o) (n := 1) (by omega)).byte (by rw [BitVec.sub_self]; decide))
  fr k hk := by
    rw [word, hf.readW (r := ⟨off F (8 * k), 8⟩) (Region.contains_self _ _) (fun r' hr' => ?_) (by decide)]
    · exact R.fr k hk
    rw [List.mem_singleton.mp hr']
    exact (ha.dF.sub_right (Offset.sub_base F (by unfold nW frameBytes at *; omega))).symm

/-! ## `ok` -/

/-- `ok`: all ones iff the private-key operation's result `r` (word 28) is 1
and the accumulator (word 29) is zero. -/
def okW (W : Nat → BitVec 64) : BitVec 64 := zM (W 29) &&& zM (W 28 ^^^ 1)

theorem okMask_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block okMask) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S V (upd W 31 (okW W)) := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F 248) 8 (okW W)) F S V (upd W 31 (okW W)) := R.wq G' (k := 31) (by decide) _
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := L.ld (d := 224) (by decide)
  have h232 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 232) 8 := L.ld (d := 232) (by decide)
  have w248 : InRegions u.wr (F + BitVec.ofNat 64 248) 8 := L.st (d := 248) (by decide)
  have rr := R.rd8 (d := 224) (k := 28) rfl (by decide) rfl
  have ra := R.rd8 (d := 232) (k := 29) rfl (by decide) rfl
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 248) 8 (okW W) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [okMask, isZero, sR, sAcc, sOk, h224, h232, w248, L.sp, rr, ra, BitVec.add_zero, sbc_one, okW,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1 by decide]
    oaep_fin
  have R' : Rep u'.mem F S V (upd W 31 (okW W)) := by rw [hm]; exact R1
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))

/-! ## `out` -/

/-- A byte of the buffer ANDed with the mask `m`. -/
def andB (b : Byte) (m : BitVec 64) : Byte := BitVec.setWidth 8 (BitVec.setWidth 32 (b.setWidth 64 &&& m))

theorem outBody_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k j : Nat} (hj : j < k) (hk : k ≤ 1024) (hw : Covers [⟨o, k⟩] u.wr)
    (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) (h11 : u.gpr .x11 = off o j)
    (h12 : u.gpr .x12 = off S (oBuf + j)) :
    WP isa (.block [.ldrb .x10 .x12 0, .logic .and .x .x10 .x10 .x15, .strb .x10 .x11 0, .addImm .x .x11 .x11 1,
      .addImm .x .x12 .x12 1, .subImm .x .x13 .x13 1]) u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩] u u' ∧
      Rep u'.mem F S V W ∧ u'.mem = u.mem.write (off o j) 1 (andB (V (oBuf + j)) (u.gpr .x15)) ∧
      u'.gpr .x11 = off o (j + 1) ∧ u'.gpr .x12 = off S (oBuf + j + 1) ∧ u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧
      u'.gpr .x15 = u.gpr .x15 := by
  have cb : oBuf = 1024 := rfl
  have co : oRsa = 8192 := rfl
  have r1 : InRegions (u.rd ++ u.wr) (off S (oBuf + j)) 1 := L.sld (by omega)
  have v1 : u.mem (off S (oBuf + j)) = V (oBuf + j) := R.scr _ (by omega)
  have cj : Region.Contains ⟨o, k⟩ (off o j) 1 := Offset.contains_base o (by omega) (by omega)
  have w1 : InRegions u.wr (off o j) 1 := hw _ _ ⟨_, List.mem_singleton_self _, cj⟩
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off o j) 1 (andB (V (oBuf + j)) (u.gpr .x15)) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = off o j + BitVec.ofNat 64 1 ∧ u'.gpr .x12 = off S (oBuf + j) + BitVec.ofNat 64 1 ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧ u'.gpr .x15 = u.gpr .x15) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13, x15⟩ => ?_
  · oaep_run [h11, h12, BitVec.add_zero, r1, w1, read_one, byte64, v1, andB]
    oaep_fin
  have hf : Frame [⟨o, k⟩] u.mem u'.mem := by
    rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ cj
  have R' : Rep u'.mem F S V W := R.apart L.geo ha hf
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], hf.mono (by simp)⟩, R', hm,
    x11.trans (off_off o j 1), x12.trans (off_off S _ 1), x13, x15⟩
  rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]

/-- The buffer's first `k` bytes, ANDed with `ok` (word 31), to `out` (word
19), a region apart from the frame, our working space and the stack below
the frame. -/
theorem outLoop_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k : Nat} (ho : W 19 = o) (hk : W 21 = BitVec.ofNat 64 k) (hk0 : 0 < k)
    (hk1 : k ≤ 1024) (hw : Covers [⟨o, k⟩] u.wr) (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa outLoop u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩] u u' ∧ Rep u'.mem F S V W ∧
      (∀ i < k, u'.mem (off o i) = andB (V (oBuf + i)) (W 31)) := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h152 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h248 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 248) 8 := L.ld (d := 248) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) ho
  have rk := R.rdK hk
  have rok := R.rd8 (d := 248) (k := 31) rfl (by decide) rfl
  unfold outLoop
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x12 = off S oBuf ∧
      u'.gpr .x11 = o ∧ u'.gpr .x13 = BitVec.ofNat 64 k ∧ u'.gpr .x15 = W 31) ?_
    fun v ⟨hm, hrd, hwr, hsp, hv, hcs, x12, x11, x13, x15⟩ => ?_)
  · oaep_run [scr, Mgf1.scr, lay, sScr, sOut, sK, sOk, oBuf, h96, h152, h168, h248, L.sp, hs, ro, rk, rok]
    oaep_fin
  have Lv : Lay v F S := L.congr hsp hwr (by rw [hm])
  have Sv : Step F S [⟨o, k⟩] u v := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.mono (count_loop hk0 (fun j w => Lay w F S ∧ Step F S [⟨o, k⟩] u w ∧ Rep w.mem F S V W ∧
      (∀ i < j, w.mem (off o i) = andB (V (oBuf + i)) (W 31)) ∧ w.gpr .x11 = off o j ∧
      w.gpr .x12 = off S (oBuf + j) ∧ w.gpr .x13 = BitVec.ofNat 64 (k - j) ∧ w.gpr .x15 = W 31)
    (fun j hj w ⟨Lw, Sw, Rw, Ow, w11, w12, w13, w15⟩ => ?_)
    ⟨Lv, Sv, hm ▸ R, fun _ h => absurd h (Nat.not_lt_zero _), by rw [x11]; exact (BitVec.add_zero o).symm,
      by rw [x12]; rfl, x13, x15⟩) fun w ⟨Lw, Sw, Rw, Ow, _⟩ => ⟨Lw, Sw, Rw, Ow⟩
  refine WP.mono (outBody_ok Lw Rw hj hk1 (by rw [Sw.wr]; exact hw) hnw ha w11 w12)
    fun w' ⟨L', S', R', hm', x11', x12', x13', x15'⟩ => ⟨⟨L', Sw.trans S', R', fun i hi => ?_, x11', x12', ?_,
      x15'.trans w15⟩, ?_⟩
  · rw [hm', write1_apply]
    by_cases hij : i = j
    · subst hij; rw [ifp rfl, w15]
    · rw [ifn (Offset.add_ofNat_ne o (by omega) (by omega) hij), Ow i (by omega)]
  · rw [x13', w13, counter_step hj (by omega)]
  · rw [x13', w13, counter_step hj (by omega)]; exact counter_ne hj (by omega)

/-! ## The length and the result -/

/-- `(r = 2) ? 2 : 0`, from word 28. -/
def fltW (W : Nat → BitVec 64) : BitVec 64 := zM (W 28 ^^^ 2) &&& 2

theorem decRet_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {ml : Addr} {k : Nat} (hml : W 27 = ml) (hk : W 21 = BitVec.ofNat 64 k)
    (hD : 2 * H.D + 2 < 4096) (hw : Covers [⟨ml, 8⟩] u.wr) (ha : Apart F S ⟨ml, 8⟩) :
    WP isa (.block (decRet H)) u fun u' => Lay u' F S ∧ Step F S [⟨ml, 8⟩] u u' ∧ Rep u'.mem F S V W ∧
      u'.mem.readW ml 64 = (BitVec.ofNat 64 k - BitVec.ofNat 64 (2 * H.D + 2) - W 30) &&& W 31 ∧
      u'.gpr .x0 = fltW W ||| (W 31 &&& 1) := by
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h216 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 216) 8 := L.ld (d := 216) (by decide)
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := L.ld (d := 224) (by decide)
  have h240 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 240) 8 := L.ld (d := 240) (by decide)
  have h248 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 248) 8 := L.ld (d := 248) (by decide)
  have rk := R.rdK hk
  have rml := R.rd8 (d := 216) (k := 27) rfl (by decide) hml
  have rr := R.rd8 (d := 224) (k := 28) rfl (by decide) rfl
  have ri := R.rd8 (d := 240) (k := 30) rfl (by decide) rfl
  have rok := R.rd8 (d := 248) (k := 31) rfl (by decide) rfl
  have cm : Region.Contains ⟨ml, 8⟩ ml 8 := Region.contains_self _ _
  have w1 : InRegions u.wr (ml + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact hw _ _ ⟨_, List.mem_singleton_self _, cm⟩
  have R1 : Rep (u.mem.write (ml + BitVec.ofNat 64 0) 8
      ((BitVec.ofNat 64 k - BitVec.ofNat 64 (2 * H.D + 2) - W 30) &&& W 31)) F S V W :=
    R.apart L.geo ha (by rw [BitVec.add_zero]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ cm)
  have rr1 := R1.rd8 (d := 224) (k := 28) rfl (by decide) rfl
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (ml + BitVec.ofNat 64 0) 8
      ((BitVec.ofNat 64 k - BitVec.ofNat 64 (2 * H.D + 2) - W 30) &&& W 31) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x0 = fltW W ||| (W 31 &&& 1)) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x0⟩ => ?_
  · oaep_run [decRet, faultBit, isZero, sOk, sK, sIdx, sMl, sR, h168, h216, h224, h240, h248, L.sp, rk, rml, rr, ri,
      rok, w1, rr1, sbc_one, fltW, hD, show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1 by decide,
      show BitVec.setWidth 64 (2 : BitVec 16) <<< 0 = 2 by decide]
    and_intros <;> first | trivial | exact cs_rfl | exact BitVec.or_comm _ _
  have hf : Frame [⟨ml, 8⟩] u.mem u'.mem := by
    rw [hm, BitVec.add_zero]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ cm
  have R' : Rep u'.mem F S V W := R.apart L.geo ha hf
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], hf.mono (by simp)⟩, R', ?_, x0⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm, BitVec.add_zero]
    simpa only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] using Mem.readW_writeW_self64 u.mem ml
      ((BitVec.ofNat 64 k - BitVec.ofNat 64 (2 * H.D + 2) - W 30) &&& W 31)

/-! ## Zeros to `out` -/

theorem zeroOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k : Nat} (ho : W 19 = o) (hk : W 21 = BitVec.ofNat 64 k) (hk0 : 0 < k)
    (hk1 : k ≤ 1024) (hw : Covers [⟨o, k⟩] u.wr) (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa zeroOut u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩] u u' ∧ Rep u'.mem F S V W ∧ u'.gpr .x13 = 0 ∧
      (∀ i < k, u'.mem (off o i) = 0) := by
  have h152 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) ho
  have rk := R.rdK hk
  unfold zeroOut
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = o ∧
      u'.gpr .x12 = BitVec.ofNat 64 k ∧ u'.gpr .x13 = 0) ?_
    fun v ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [sOut, sK, h152, h168, L.sp, ro, rk]
    oaep_fin
  have Lv : Lay v F S := L.congr hsp hwr (by rw [hm])
  have Sv : Step F S [⟨o, k⟩] u v := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.mono (count_loop hk0 (fun j w => Lay w F S ∧ Step F S [⟨o, k⟩] u w ∧ Rep w.mem F S V W ∧
      (∀ i < j, w.mem (off o i) = 0) ∧ w.gpr .x11 = off o j ∧ w.gpr .x12 = BitVec.ofNat 64 (k - j) ∧
      w.gpr .x13 = 0)
    (fun j hj w ⟨Lw, Sw, Rw, Ow, w11, w12, w13⟩ => ?_)
    ⟨Lv, Sv, hm ▸ R, fun _ h => absurd h (Nat.not_lt_zero _), by rw [x11]; exact (BitVec.add_zero o).symm,
      x12, x13⟩) fun w ⟨Lw, Sw, Rw, Ow, _, _, w13⟩ => ⟨Lw, Sw, Rw, w13, Ow⟩
  have cj : Region.Contains ⟨o, k⟩ (off o j) 1 := Offset.contains_base o (by omega) (by omega)
  have w1 : InRegions w.wr (off o j) 1 := by rw [Sw.wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, cj⟩
  refine WP.mono (Q := fun (w' : State) => w'.mem = w.mem.write (off o j) 1 0 ∧ w'.rd = w.rd ∧ w'.wr = w.wr ∧
      w'.sp = w.sp ∧ w'.v = w.v ∧ (∀ r ∈ preserved, r ≠ .x30 → w'.gpr r = w.gpr r) ∧
      w'.gpr .x11 = off o j + BitVec.ofNat 64 1 ∧ w'.gpr .x12 = w.gpr .x12 - BitVec.ofNat 64 1 ∧ w'.gpr .x13 = 0) ?_
    fun w' ⟨hm', hrd', hwr', hsp', hv', hcs', x11', x12', x13'⟩ => ?_
  · oaep_run [w11, w13, BitVec.add_zero, w1]
    and_intros <;> first | trivial | exact cs_rfl | decide
  have hf : Frame [⟨o, k⟩] w.mem w'.mem := by
    rw [hm']; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ cj
  have R' : Rep w'.mem F S V W := Rw.apart Lw.geo ha hf
  refine ⟨⟨Lw.congr hsp' hwr' ?_, Sw.trans ⟨hrd', hwr', hsp', hcs', fun r _ => by rw [hv'], hf.mono (by simp)⟩, R',
    fun i hi => ?_, x11'.trans (off_off o j 1), by rw [x12', w12, counter_step hj (by omega)], x13'⟩, ?_⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), Rw.fr 12 (by decide)]
  · rw [hm', write1_apply]
    by_cases hij : i = j
    · subst hij; rw [ifp rfl]
    · rw [ifn (Offset.add_ofNat_ne o (by omega) (by omega) hij), Ow i (by omega)]
  · rw [x12', w12, counter_step hj (by omega)]; exact counter_ne hj (by omega)

end VG.Proof.RsaOaep.AArch64
