import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Layout
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Header
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Base

/-!
# Ed448 signing with a cached public key on ARMv7: the hashes

`hdr_step`: the first ten bytes of `dom4(0, C)` at `HDR`. `seed_step`:
`SHAKE256(seed, 114)` at `S`, and `prune_step`: its first half pruned in
place. `nonce_step` and `chal_step`: `SHAKE256(dom4(0, C) ‖ prefix ‖ M)` and
`SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M)` at `HASH`, the prefix at `K` and `R` the
first half of `out`. Each states what it may write (`W ex`: the outgoing
stack arguments, the regions `ex`, the state and the working space).
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit Args argVal kWr kArgs sqzWr ScrAt DataOk hdrBytes valid_const
  valid_frame frame_bytes frame_within hdr_len dom4_eq)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem scr_at (L : Lay) : ScrAt 12 L.value SC L.scr := ⟨by decide, rfl⟩

/-! ## What the steps write -/

/-- The outgoing stack arguments, `ex`, the state and the working space. -/
abbrev W (L : Lay) (ex : List Region) : List Region := kArgs L.E 8 :: ex ++ kWr L.scr

theorem Away.bytes {D : Region} (h : Away L D) {ex : List Region} (hx : ∀ r ∈ ex, D.Disjoint r)
    {m m' : Mem} (hf : Frame (W L ex) m m') (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := by
  refine frame_bytes hf (fun r hr => ?_) hn
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.args.symm
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  · exact h.kwr r hr

theorem W.zero {ex : List Region} {m m' : Mem} (h : Frame [⟨State.addr L.scr, 200⟩] m m') : Frame (W L ex) m m' :=
  h.mono fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [kWr]))

theorem W.abs {ex : List Region} {m m' : Mem} (h : Frame (kArgs L.E 8 :: kWr L.scr) m m') : Frame (W L ex) m m' :=
  h.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hr)

theorem W.sqz {ex : List Region} {d : Nat} (hd : L.fr d 114 ∈ ex) {m m' : Mem}
    (h : Frame (kArgs L.E 8 :: sqzWr L.E L.scr d) m m') : Frame (W L ex) m m' :=
  h.mono fun r hr => by
    simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [kWr]))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [kWr]))

/-! ## Absorptions, in this layout -/

/-- Data in an input. -/
theorem Lay.Ok.input_data (hL : L.Ok) {R D : Region} (hR : R ∈ L.inputs) (hw : Whole.Within D R) :
    DataOk L.E L.inputs L.outputs D ∧ Away L D :=
  let h := hL.kit.data_input hR hw
  ⟨.inr ⟨R, List.mem_append_left _ hR, hw⟩, h.2, h.1⟩

theorem first_abs (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {src len : Value}
    (vs : valid 12 src) (vl : valid 12 len) {P : BitVec 32} {N : Nat} (hP : argVal L.E L.value src = P)
    (hN : (argVal L.E L.value len).toNat = N) (hcov : DataOk L.E L.inputs L.outputs ⟨State.addr P, N⟩)
    (hd : Away L ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 []) :
    WP isa (absorb (firstArgs SC src len)) t fun v => Ctx L g m₀ v ∧
      Frame (kArgs L.E 8 :: kWr L.scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr L.scr) 136 (Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 (N % 136) :=
  hL.kit.firstAt hc ha (scr_at L) vs vl hP hN hcov hd.kwr hd.args hfit hr

theorem next_abs (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {src len : Value}
    (vs : valid 12 src) (vl : valid 12 len) {P : BitVec 32} {N : Nat} (hP : argVal L.E L.value src = P)
    (hN : (argVal L.E L.value len).toNat = N) (hcov : DataOk L.E L.inputs L.outputs ⟨State.addr P, N⟩)
    (hd : Away L ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs SC src len)) t fun v => Ctx L g m₀ v ∧
      Frame (kArgs L.E 8 :: kWr L.scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr L.scr) 136 (msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N).length % 136) :=
  hL.kit.nextAt hc ha (scr_at L) vs vl hP hN hcov hd.kwr hd.args hfit hr hpos

/-! ## The header -/

theorem hdr_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.block (hdrAt 4 HDR)) t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L.ctxLen :=
  WP.mono (hL.kit.hdr_ok hc ha (j := 4) (by decide) hL.cl (by decide)) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

/-! ## `SHAKE256(seed, 114)`, and `s` -/

theorem seed_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa seedHash t fun u => Ctx L g m₀ u ∧ Frame (W L [L.fr S 114]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 S) 114 =
        Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114 := by
  have hk := hL.kit
  have hw : Whole.Within ⟨State.addr L.seed, 57⟩ L.SEED := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have hR : L.SEED ∈ L.inputs := by simp [Lay.inputs]
  obtain ⟨hcov, hd⟩ := hL.input_data hR hw
  unfold seedHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  refine WP.seq (WP.mono (first_abs hc1 hL ha (src := .caller 1 0) (len := .const 57) (P := L.seed) (N := 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl hcov hd hL.ne
    (PublicKey.repr_nil hz))
    fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  refine WP.seq (WP.mono (hk.pad_step hc2 ha (scr_at L) hr2 (by rw [hp2]; simp [Spec.Ed448.bytesAt]))
    fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  refine WP.mono (hk.sqz_step hc3 ha (scr_at L) (d := S) (by decide) (by decide)) fun u ⟨hu, hf4, hb⟩ =>
    ⟨hu, ((W.zero hf1).trans (W.abs hf2)).trans ((W.abs hf3).trans (W.sqz (by simp) hf4)), ?_⟩
  have e := hk.input_bytes hc1 hR hw (by change 57 ≤ 2 ^ 64; decide)
  simp only at e
  rw [hb, hs3, ← PublicKey.shake256_eq, e]

theorem prune_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa prune t fun u => Ctx L g m₀ u ∧ Frame [L.fr S 57] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 S) 57) =
        Spec.Ed448.prune (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 S) 114) := by
  unfold prune
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons (s' := t.setReg .r12 (t.sp + BitVec.ofNat 32 S))
    (by simp [exec, S]) (WP.block_nil ?_))
  have hsp := hc.sp
  have ht := hL.top
  have e12 : (t.setReg .r12 (t.sp + BitVec.ofNat 32 S)).gpr .r12 = L.E + BitVec.ofNat 32 S := by
    simp [State.setReg, hsp]
  refine WP.mono (PublicKey.pruneOps_ok (q := State.addr L.E + BitVec.ofNat 64 S)
    (by rw [e12]; exact hL.kit.frame_addr (by decide))
    (by rw [e12]; exact hL.kit.frame_fit (by decide))
    (fun j hj => by
      have h := hc.writable_frame (Offset.contains_base (State.addr L.E) (d := S + j) (n := 1)
        (k := 248) (by simp only [S]; omega) (by simp only [S]; omega))
      rw [← Offset.add_add] at h
      exact h))
    fun u ⟨um, usp, urd, uwr, ug⟩ => ?_
  have hf : Frame [L.fr S 57] t.mem u.mem := by
    rw [um]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      ?_).writeW (List.mem_singleton_self _) _ ?_
    · have h := Offset.contains_base (State.addr L.E + BitVec.ofNat 64 S) (d := 0) (n := 1) (k := 57) (by omega) (by omega)
      rw [show State.addr L.E + BitVec.ofNat 64 S + BitVec.ofNat 64 0 = State.addr L.E + BitVec.ofNat 64 S from
        BitVec.add_zero _] at h
      exact h
    · exact Offset.contains_base _ (by omega) (by omega)
    · exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨?_, hf, ?_⟩
  · refine hc.of_frame urd uwr usp ?_ hf ?_
    · intro r hr _
      rw [ug r (by rintro rfl; simp [preserved] at hr)]
      exact RegUpd.gpr_setReg_of_ne _ _ (by rintro rfl; simp [preserved] at hr)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by simp only [S]; omega))
  · rw [um, PublicKey.pruned_value]
    unfold Spec.Ed448.prune
    rw [PublicKey.bytesAt_take57]
    rfl

/-! ## The nonce's and the challenge's hashes -/

theorem len_append (msg : List Byte) (m : Mem) (p : Addr) (n : Nat) :
    (msg ++ Spec.Ed448.bytesAt m p n).length = msg.length + n := by
  simp [Spec.Ed448.bytesAt]

theorem Lay.Ok.away_hdr (hL : L.Ok) : Away L (L.fr HDR 10) := hL.away_fr (by decide) (by decide)
theorem Lay.Ok.away_k (hL : L.Ok) : Away L (L.fr K 57) := hL.away_fr (by decide) (by decide)
theorem Lay.Ok.away_s (hL : L.Ok) : Away L (L.fr S 57) := hL.away_fr (by decide) (by decide)

/-- `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` in the frame at `HASH`, the
header of `dom4` at `HDR` and the prefix at `K`. -/
theorem nonce_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L.ctxLen) :
    WP isa nonceHash t fun u => Ctx L g m₀ u ∧ Frame (W L [L.fr HASH 114]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 ++
            Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have wx : Whole.Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ L.CTX := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have wm : Whole.Within ⟨State.addr L.msg, L.len.toNat⟩ L.MSG := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have rx : L.CTX ∈ L.inputs := by simp [Lay.inputs]
  have rm : L.MSG ∈ L.inputs := by simp [Lay.inputs]
  obtain ⟨cx, dx⟩ := hL.input_data rx wx
  obtain ⟨cm, dm⟩ := hL.input_data rm wm
  unfold nonceHash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  -- The header.
  refine WP.seq (WP.mono (first_abs hc1 hL ha (src := .frame HDR) (len := .const 10)
    (P := L.E + BitVec.ofNat 32 HDR) (N := 10) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hL.away_hdr) (hk.frame_fit (by decide)) (PublicKey.repr_nil hz))
    fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  have hh1 := hL.away_hdr.bytes (ex := []) (fun _ h => nomatch h) (W.zero hf1) (by change 10 ≤ 2 ^ 64; decide)
  simp only at hh1
  rw [hk.frame_addr (by decide), hh1, hh] at hr2
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L.ctxLen).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (next_abs hc2 hL ha (src := .caller 3 0) (len := .caller 4 0) (P := L.ctx)
    (N := L.ctxLen.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cx dx hL.nx hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex := hk.input_bytes hc2 rx wx (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega)
  simp only at ex
  rw [ex] at hr3 hp3
  -- The prefix.
  refine WP.seq (WP.mono (next_abs hc3 hL ha (src := .frame K) (len := .const 57)
    (P := L.E + BitVec.ofNat 32 K) (N := 57) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hL.away_k) (hk.frame_fit (by decide)) hr3 hp3)
    fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  have hk3 := hL.away_k.bytes (ex := []) (fun _ h => nomatch h)
    (((W.zero hf1).trans (W.abs hf2)).trans (W.abs hf3)) (by change 57 ≤ 2 ^ 64; decide)
  simp only at hk3
  rw [hk.frame_addr (by decide), hk3] at hr4 hp4
  -- The message.
  refine WP.seq (WP.mono (next_abs hc4 hL ha (src := .caller 5 0) (len := LEN) (P := L.msg)
    (N := L.len.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value, LEN]) cm dm hL.nm hr4 hp4) fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have em := hk.input_bytes hc4 rm wm (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega)
  simp only at em
  rw [em] at hr5 hp5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc5 ha (scr_at L) hr5 hp5) fun t6 ⟨hc6, hf6, hs6⟩ => ?_)
  refine WP.mono (hk.sqz_step hc6 ha (scr_at L) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf7, hb⟩ =>
    ⟨hu, ((((W.zero hf1).trans (W.abs hf2)).trans ((W.abs hf3).trans (W.abs hf4))).trans
      ((W.abs hf5).trans ((W.abs hf6).trans (W.sqz (by simp) hf7)))), ?_⟩
  rw [hb, hs6, ← PublicKey.shake256_eq, Spec.Ed448.hash,
    dom4_eq L.ctxLen _ _ (by simp [Spec.Ed448.bytesAt])]
  simp only [List.append_assoc]

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame at `HASH`, the header
of `dom4` at `HDR` and `R` the first half of `out`. -/
theorem chal_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L.ctxLen) :
    WP isa chalHash t fun u => Ctx L g m₀ u ∧ Frame (W L [L.fr HASH 114]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt t.mem (State.addr L.out) 57 ++ Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 ++
            Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have wx : Whole.Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ L.CTX := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have wp : Whole.Within ⟨State.addr L.pk, 57⟩ L.PK := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have wm : Whole.Within ⟨State.addr L.msg, L.len.toNat⟩ L.MSG := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have rx : L.CTX ∈ L.inputs := by simp [Lay.inputs]
  have rp : L.PK ∈ L.inputs := by simp [Lay.inputs]
  have rm : L.MSG ∈ L.inputs := by simp [Lay.inputs]
  obtain ⟨cx, dx⟩ := hL.input_data rx wx
  obtain ⟨cp, dp⟩ := hL.input_data rp wp
  obtain ⟨cm, dm⟩ := hL.input_data rm wm
  unfold chalHash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  -- The header.
  refine WP.seq (WP.mono (first_abs hc1 hL ha (src := .frame HDR) (len := .const 10)
    (P := L.E + BitVec.ofNat 32 HDR) (N := 10) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hL.away_hdr) (hk.frame_fit (by decide)) (PublicKey.repr_nil hz))
    fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  have hh1 := hL.away_hdr.bytes (ex := []) (fun _ h => nomatch h) (W.zero hf1) (by change 10 ≤ 2 ^ 64; decide)
  simp only at hh1
  rw [hk.frame_addr (by decide), hh1, hh] at hr2
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L.ctxLen).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (next_abs hc2 hL ha (src := .caller 3 0) (len := .caller 4 0) (P := L.ctx)
    (N := L.ctxLen.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cx dx hL.nx hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex := hk.input_bytes hc2 rx wx (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega)
  simp only at ex
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (next_abs hc3 hL ha (src := .caller 0 0) (len := .const 57) (P := L.out) (N := 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl
    (.inr ⟨L.OUT, List.mem_append_right _ (out_in L), r0_within L⟩) hL.away_r0 (by have := hL.no; omega) hr3 hp3)
    fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  have hr3' := hL.away_r0.bytes (ex := []) (fun _ h => nomatch h)
    (((W.zero hf1).trans (W.abs hf2)).trans (W.abs hf3)) (by change 57 ≤ 2 ^ 64; decide)
  simp only at hr3'
  rw [hr3'] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (next_abs hc4 hL ha (src := .caller 2 0) (len := .const 57) (P := L.pk) (N := 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cp dp hL.np hr4 hp4)
    fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have ep := hk.input_bytes hc4 rp wp (by change 57 ≤ 2 ^ 64; decide)
  simp only at ep
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (next_abs hc5 hL ha (src := .caller 5 0) (len := LEN) (P := L.msg)
    (N := L.len.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value, LEN]) cm dm hL.nm hr5 hp5) fun t6 ⟨hc6, hf6, hr6, hp6⟩ => ?_)
  have em := hk.input_bytes hc5 rm wm (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega)
  simp only at em
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (scr_at L) hr6 hp6) fun t7 ⟨hc7, hf7, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (scr_at L) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf8, hb⟩ =>
    ⟨hu, ((((W.zero hf1).trans (W.abs hf2)).trans ((W.abs hf3).trans (W.abs hf4))).trans
      (((W.abs hf5).trans (W.abs hf6)).trans ((W.abs hf7).trans (W.sqz (by simp) hf8)))), ?_⟩
  rw [hb, hs7, ← PublicKey.shake256_eq, Spec.Ed448.hash,
    dom4_eq L.ctxLen _ _ (by simp [Spec.Ed448.bytesAt])]
  simp only [List.append_assoc]

end VG.Proof.Ed448.Arm.SignCached
