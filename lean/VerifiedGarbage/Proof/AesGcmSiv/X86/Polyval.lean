import VerifiedGarbage.Proof.AesGcmSiv.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops

/-!
# AES-GCM-SIV on x86: POLYVAL and the tag input (`absorb`, `polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`), from the slots `alenO` and `lenO`; `tagIn` turns POLYVAL's
result into the tag input (`tagIn_ok`). `polyval_ok`: the tag input of
RFC 8452 §4, with POLYVAL as GHASH with the key `H · x`
(`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.Cmac (le4)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv slotv_eq GcmImpl readW_writeW_off covers_left covers_off
  zero4_fold LoopPre CopyPost copyLoop_ok length_bytesAt sub_beq32)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero4 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero4_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.X86.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.X86.bytesAt_add,
    Proof.AesGcm.X86.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.X86.bytesAt_frame (Proof.AesGcm.X86.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hsi : t.gpr .esi = p.W + BitVec.ofNat 32 224) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 16) :
    WP isa (chunk v.callees) t (Absorbed p (absR p)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (chunk_ok v L E (m := 16) (by decide) (by decide) (srcB L E.perm) hsi hn) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [elemsAt, L.aW (show 224 < 4096 by decide)] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  esi : t₃.gpr .esi = p.W + BitVec.ofNat 32 224
  n : slotv t₃.mem p.W nO = BitVec.ofNat 32 16
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨w64 P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩) (hsi : t.gpr .esi = P)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    WP isa absTailPre t (TailPre p (w64 P) r t) := by
  have hw := L.ww
  simp only [slotv_eq, nO] at hn
  have hz := zero4_fold t.mem p.W 224
  simp only [Nat.reduceAdd] at hz
  have rn : (Proof.Cmac.zero4 t.mem (w64 p.W + BitVec.ofNat 64 224)).readW (w64 p.W + BitVec.ofNat 64 176) 32 =
      t.mem.readW (w64 p.W + BitVec.ofNat 64 176) 32 := by
    rw [← hz]; simp (disch := decide) only [readW_writeW_off]
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (zero4 bO ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm bO),
        .mov .ecx (slot nO)] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 t.mem (w64 p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .edi = P ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .ecx = BitVec.ofNat 32 r ∧ t₁.gpr .ebp = p.W ∧
      t₁.gpr .esp = p.SP ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [zero4]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hn, hz, rn], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · gmems [hz]
    · gregs [hsi]
    · gregs [E.ebp]
    · gmems [hz, rn, hn]
    · gregs [E.ebp]
    · gregs [E.esp]
    all_goals rfl
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have dB : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 (p.W + BitVec.ofNat 32 224), r⟩ := by
    rw [L.aW (by decide)]
    exact (hd.sub_right (Lay.wSub (show 224 + 16 ≤ 4096 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r :=
    ⟨di₁, dx₁, cx₁, by omega, by omega, hf, by rw [L.nW (by decide)]; omega, by rw [rd₁, wr₁]; exact hc,
      by rw [L.aW (by decide)]; exact covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 4096 by decide)) (by omega), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ lp) fun t₂ O => ?_)
  have hm₂ := O.mem
  rw [L.aW (by decide)] at hm₂
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem (w64 P) r = bytesAt t.mem (w64 P) r :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide))) (by omega)
  have hb₂ : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
      bytesAt t.mem (w64 P) r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem (w64 P) r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega), hl]
  have f₂' : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t₁.mem t₂.mem := by
    rw [hm₂]
    exact (Proof.AesGcm.X86.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := f₁.trans f₂'
  have bp₂ : t₂.gpr .ebp = p.W := by rw [O.other _ (by decide) (by decide) (by decide) (by decide), bp₁]
  have sp₂ : t₂.gpr .esp = p.SP := by rw [O.other _ (by decide) (by decide) (by decide) (by decide), sp₁]
  have E₂ : Env p t₂ := E₁.mut L bp₂ sp₂ O.rd O.wr (frame_toMut f₂' fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem
      (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fm₃ := frame_toMut f₃ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine WP.of_runBlock ⟨_, by grun [E₂.ebp, L.aW, E₂.perm.wW], ?_⟩
  refine ⟨E₂.mut L (by gregs [E₂.ebp]) (by gregs [E₂.esp]) (by gmems []) (by gmems []) (by gmems []; exact fm₃),
    by gmems [O.rd, rd₁], by gmems [O.wr, wr₁], by gregs [E₂.ebp], by gmems [slotv_eq], ?_, ?_⟩
  · gmems []
    exact (f₂.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (f₃.mono fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_of_mem _ List.mem_cons_self)
  · gmems []
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), hb₂]

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨w64 P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩) (hsi : t.gpr .esi = P)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    WP isa (absTail v.callees) t
      (AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 P) r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (absTailPre_ok L E hr1 hr hc hf hd hsi hn) fun t₃ T => ?_)
  refine WP.mono (chunkB_ok v L T.env T.esi T.n) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩], ∀ d,
      d + 16 ≤ 176 → (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.sub fun q hq => ?_).trans (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · rw [C.out, Proof.AesGcm.X86.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
      Proof.AesGcm.X86.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.X86.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once ZF says whether there are any. -/
theorem absMid_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : Src p t Q m) (hsi : t.gpr .esi = Q) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m)
    (hz : t.zf = some (decide (m / 16 = 0))) :
    WP isa (.ite .e (.block []) (.loop (chunk v.callees) .ne)) t fun t₂ =>
      Absorbed p (absR p) (elemsAt t.mem (w64 Q) (m / 16)) t t₂ ∧
        t₂.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv t₂.mem p.W nO = BitVec.ofNat 32 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_e hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [hsi, h0, Nat.mul_zero, BitVec.add_zero], by rw [hn]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_ok v L E hm (by omega) (hQ.take (by omega)) hsi hn

/-- `anyLeft`: ZF set iff no byte is left. -/
theorem anyLeft_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa anyLeft t = some t' ∧ t'.zf = some (decide (r = 0)) ∧ Env p t' ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by simp only [anyLeft]; grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, by gregs [], by gmems [],
    by gmems [], by gmems []⟩
  · gmems [hn]
    rw [BitVec.and_self, show BitVec.ofNat 32 r = BitVec.ofNat 32 r - BitVec.ofNat 32 0 by simp,
      sub_beq32 hr (by decide)]
  · exact E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems [])

theorem absorb_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : Src p t Q m) (hd : (⟨w64 Q, m⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩)
    (hsi : t.gpr .esi = Q) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (absorb v.callees) t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (w64 Q) m))) t) := by
  obtain ⟨t₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := wholeLeft_ok L E hm hn
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (absMid_ok v L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [si₁, hsi]) (by rw [slotv_eq, m₁]; exact hn)
    z₁) fun t₂ ⟨P₂, si₂, n₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [elems_pad16_bytesAt]
  obtain ⟨t₃, run₃, z₃, E₃, si₃, m₃, rd₃, wr₃⟩ := anyLeft_ok L P₂'.env (by omega) n₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have P₃ : Absorbed p (absR p) (elemsAt t.mem (w64 Q) (m / 16)) t t₃ :=
    ⟨E₃, rd₃.trans P₂'.rd, wr₃.trans P₂'.wr, m₃ ▸ P₂'.frame, by rw [m₃]; exact P₂'.out⟩
  refine WP.ite (decide (m % 16 = 0)) (eval_e z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₃.sub (absR_sub p))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
    have ea := hQ.addr (j := 16 * (m / 16)) (by omega)
    have dT : (⟨w64 (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩ := by
      rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega))
    refine WP.mono (absTail_ok v L P₃.env (by omega) (by omega) (by rw [P₃.rd, P₃.wr]; exact hs.rd) hs.wrap dT
      (by rw [si₃, si₂]) (by rw [slotv_eq, m₃]; exact n₂)) fun t₄ T => ?_
    have e := Proof.AesGcm.X86.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.stk.symm) (by omega)
    rw [e, ea] at T
    exact AbsPost.trans L (P₃.sub (absR_sub p)) T

/-! ## The lengths, and the tag input -/

/-- The memory `lensBlock` leaves. -/
def lensMem (m : Mem) (W : Addr) (al n : Nat) : Mem :=
  (Proof.Cmac.store4 m (W + BitVec.ofNat 64 224) (BitVec.ofNat 32 al <<< 3) (BitVec.ofNat 32 al >>> 29)
    (BitVec.ofNat 32 n <<< 3) (BitVec.ofNat 32 n >>> 29)).writeW (W + BitVec.ofNat 64 176) (BitVec.ofNat 32 16)

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (lens v.callees) t (AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  have ha := E.slots.alen
  have hn := E.slots.len
  simp only [slotv_eq, alenO, lenO] at ha hn
  obtain ⟨t₁, run₁, hm₁, si₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = lensMem t.mem (w64 p.W) p.al p.n ∧ t₁.gpr .esi = p.W + BitVec.ofNat 32 224 ∧
      t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [lensBlock, le64At]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, ha, hn], ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · gmems [ha, hn, add_self32_3, lensMem, Proof.Cmac.store4, add_ofNat_assoc]
    · gregs [E.ebp]
    · gregs [E.ebp]
    · gregs [E.esp]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, lensMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  refine WP.mono (chunkB_ok v L E₁ si₁ (by rw [slotv_eq, hm₁, lensMem, Mem.readW_writeW_self32])) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    have ea := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.al)
    have en := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.n)
    rw [toNat_ofNat32 L.al32] at ea
    rw [toNat_ofNat32 L.n32] at en
    rw [hm₁, lensMem, Proof.AesGcm.X86.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide),
      Proof.Cmac.bytesAt_store4, ea, en, List.append_assoc]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region),
      ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩], (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁], (f₁.sub fun q hq => ?_).trans
    (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · rw [C.out, Proof.AesGcm.X86.blockAt_frame f₁ (dHY 64 (by decide)),
      Proof.AesGcm.X86.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96)
    (bswap (m.readW (W + BitVec.ofNat 64 92) 32) ^^^ m.readW (N + BitVec.ofNat 64 0) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 88) 32) ^^^ m.readW (N + BitVec.ofNat 64 4) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 84) 32) ^^^ m.readW (N + BitVec.ofNat 64 8) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 80) 32) &&& 0x7FFFFFFF#32)

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  have e := GcmSiv.Words32.tagOf_words (bswap (m.readW (W + BitVec.ofNat 64 92) 32))
    (bswap (m.readW (W + BitVec.ofNat 64 88) 32)) (bswap (m.readW (W + BitVec.ofNat 64 84) 32))
    (bswap (m.readW (W + BitVec.ofNat 64 80) 32)) (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32)
    (m.readW (N + BitVec.ofNat 64 8) 32)
  rw [GcmSiv.Words32.shl_shr_one] at e
  rw [tagInMem, Proof.Cmac.bytesAt_store4, blockAt_bswap, GcmSiv.Words32.toBytes_append4,
    show (12 : Nat) = 4 + 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]
  simp only [add_ofNat_assoc, Nat.reduceAdd, BitVec.add_zero]
  rw [e]

theorem tagIn_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = tagInMem t.mem (w64 p.W) (w64 p.N) ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hN := E.slots.nonce
  simp only [slotv_eq, nonceO] at hN
  have n₀ := E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn, tagInW]; grun [E.ebp, L.aW, L.aN, E.perm.wW, E.perm.wR, hN, n₀, n₄, n₈], ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [hN, tagInMem, Proof.Cmac.store4, add_ofNat_assoc]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W N) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (p : Prm) : List Region := ⟨w64 p.W + BitVec.ofNat 64 96, 16⟩ :: absorbR p

theorem inMut_polyR (p : Prm) : InMut p (polyR p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact inMut_w p (.inl (by decide))
  · exact inMut_absorbR p r hr

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR p) t.mem t'.mem
  out : bytesAt t'.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem (w64 p.N) 12)
      (bytesAt t.mem (w64 p.D) p.n) (bytesAt t.mem (w64 p.A) p.al)

/-- A buffer apart from `W` and the stack below `SP` misses what absorbing writes. -/
theorem absorbR_buf {p : Prm} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩)
    (hb : (stk p).Disjoint ⟨P, k⟩) : ∀ r ∈ absorbR p, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- `onStr s l`: the string at `W + s` (`W + l` bytes) to absorb. -/
theorem onStr_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {s l : Nat} {Q : BitVec 32} {k : Nat}
    (hs : s + 4 ≤ 176 ∧ 128 ≤ s) (hl : l + 4 ≤ 176 ∧ 128 ≤ l) (hQ : slotv t.mem p.W s = Q)
    (hk : slotv t.mem p.W l = BitVec.ofNat 32 k) :
    ∃ t₁ : State, runBlock isa (onStr s l) t = some t₁ ∧ Env p t₁ ∧ t₁.gpr .esi = Q ∧
      slotv t₁.mem p.W nO = BitVec.ofNat 32 k ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
  simp only [slotv_eq] at hQ hk
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem (t.mem.writeW (w64 p.W + BitVec.ofNat 64 176)
      (BitVec.ofNat 32 k)) := (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fm := frame_toMut f fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨_, by simp only [onStr]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hQ, hk], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.mut L (by gregs [E.ebp]) (by gregs [E.esp]) (by gmems []) (by gmems []) (by gmems [hQ, hk]; exact fm)
  · gregs [hQ]
  · gmems [slotv_eq, hk]
  · gmems []
  · gmems []
  · gmems [hk]; exact f

theorem polyval_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (PolyPost p t) := by
  have hw := L.ww
  -- The additional data.
  obtain ⟨t₁, run₁, E₁, si₁, n₁, rd₁, wr₁, f₁⟩ := onStr_ok L E (s := aadO) (l := alenO) (by decide) (by decide)
    E.slots.aad E.slots.alen
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have d176 : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩ →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)], (⟨P, k⟩ : Region).Disjoint q := fun hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide))
  have eA₁ : bytesAt t₁.mem (w64 p.A) p.al = bytesAt t.mem (w64 p.A) p.al :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (d176 L.a_w) (by have := L.aw; omega)
  refine WP.seq (WP.mono (absorb_ok v L E₁ (Q := p.A) (m := p.al) L.al32
    (srcBuf E₁.perm.aad L.aw L.a_w L.ba) L.a_w si₁ n₁) fun t₂ P₂ => ?_)
  rw [eA₁] at P₂
  -- The data.
  obtain ⟨t₃, run₃, E₃, si₃, n₃, rd₃, wr₃, f₃⟩ := onStr_ok L P₂.env (s := dataO) (l := lenO) (by decide) (by decide)
    P₂.env.slots.data P₂.env.slots.len
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have eD₃ : bytesAt t₃.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (d176 L.d_w) (by have := L.dw; omega),
      Proof.AesGcm.X86.bytesAt_frame P₂.frame (absorbR_buf L.d_w L.bd) (by have := L.dw; omega),
      Proof.AesGcm.X86.bytesAt_frame f₁ (d176 L.d_w) (by have := L.dw; omega)]
  refine WP.seq (WP.mono (absorb_ok v L E₃ (Q := p.D) (m := p.n) L.n32
    (srcBuf (covers_left E₃.perm.d) L.dw L.d_w L.bd) L.d_w si₃ n₃) fun t₄ P₄ => ?_)
  rw [eD₃] at P₄
  -- From `t`: the writes of `onStr` are in `absorbR`, apart from GHASH's key and accumulator.
  have dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  have sub176 : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)], ∃ q' ∈ absorbR p, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have pre : ∀ {xs : List Spec.GcmSiv.Elem} {u u₁ u₂ : State},
      Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] u.mem u₁.mem → u₁.rd = u.rd → u₁.wr = u.wr →
      AbsPost p xs u₁ u₂ → AbsPost p xs u u₂ := fun f hrd hwr P =>
    ⟨P.env, P.rd.trans hrd, P.wr.trans hwr, (f.sub sub176).trans P.frame, by
      rw [P.out, Proof.AesGcm.X86.blockAt_frame f (dHY 64 (by decide)),
        Proof.AesGcm.X86.blockAt_frame f (dHY 80 (by decide))]⟩
  have P₂₄ := AbsPost.trans L (pre f₁ rd₁ wr₁ P₂) (pre f₃ rd₃ wr₃ P₄)
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := tagIn_ok L P₂₅.env
  have f₆ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 16⟩] t₅.mem t₆.mem := by rw [hm₆]; exact tagInMem_frame _ _ _
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.mut L bp₆ sp₆ rd₆ wr₆ (frame_toMut f₆ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inl (by decide))),
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    exact f₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem (w64 p.N) 12 = bytesAt t.mem (w64 p.N) 12 :=
      Proof.AesGcm.X86.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w L.bn) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.X86
