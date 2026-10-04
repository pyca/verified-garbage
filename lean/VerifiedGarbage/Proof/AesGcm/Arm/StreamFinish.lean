import VerifiedGarbage.Proof.AesGcm.Arm.FinTag
import VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. `stream_finish` saves our
caller's registers in `work` (`W`), writes the tag to its first 16 bytes
with `finTag` and copies it to `tag` (`tagOut_ok`, `streamFinish_wp`). The
entry is shared with `stream_verify` (`fin1_wp`, for `n` words of stack
arguments, `work` the `wi`-th).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (store4)

theorem lensBlock_mod (L c : Nat) : lensBlock (L % 2 ^ 64) c = lensBlock L c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (L % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * L)]
  congr 2; omega

theorem toNat_of_eq {x : BitVec 64} {L : Nat} (h : x = BitVec.ofNat 64 L) : x.toNat = L % 2 ^ 64 := by
  rw [h, BitVec.toNat_ofNat]

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- `tagOut`: the tag at `W` copied to `T`, the stack argument at `[sp + 16]`. -/
theorem tagOut_ok {s : State} (he : Env c st w sp k7 k8 s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2560 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2560 by decide)
  have w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  have w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  have w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  have w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa tagOut s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [tagOut]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, hg, hk.1,
    hk.2.1, hk.2.2⟩

end

section
variable {n wi : Nat}

theorem finLay {s₀ : State} (h : finPre n wi s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, dsW, -, -, bc, bs, bW, fc, fs, fW, sp8, -, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SF1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ wi) s₀
  frame : Frame [savedR (arg s₀ wi)] s₀.mem s₁.mem

theorem fin1_wp {s₀ : State} (h : finPre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, SF1 n wi s₀ s₁ → Q s₁) : WP isa (.block (finEntry (4 * wi))) s₀ Q := by
  obtain ⟨⟨hc, hin⟩, ⟨hs, hw, -⟩, -, -, -, -, dWA, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hA : ∀ r ∈ [savedR (arg s₀ wi)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := covers_of_mem hs
  have hW : Covers [⟨State.addr (arg s₀ wi), 2560⟩] s₀.wr := covers_of_mem hw
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 :=
    arg_in (n := n) hn spf hin
  refine entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem fin_argsTag {s₀ : State} (h : finPre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame (s₀.gpr .r2) (arg s₀ wi) s₀.sp o, (args s₀ n).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, dsA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Region.sub_prefix (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- The tag, from the entry. -/
theorem fin_tag {s₀ s₁ : State} (h : finPre n wi s₀) (hn : 4 ≤ n) (h1 : SF1 n wi s₀ s₁) {o : Nat}
    (ho : o = 0 ∨ o = 112) {a ct : List Byte} (ha : a.length % 16 = (arg s₀ 0).toNat % 16)
    (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s₁ (FinOut (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct s₁.mem) := by
  have L := finLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact finTag_ok L hn ho h1.env h1.args spf h.1.2 (fin_argsTag h ho) (by simp) hR
    (ctxH_keep h1.frame (ctx_saved L)) ha hP

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀` that
differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} (h : finPre n wi s₀) {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r2), 80⟩ : Region).Disjoint r) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ wi) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct m₀ s)
    (hs : StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct) (hl : arg64 s₀ 0 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (State.addr (arg s₀ wi) + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
        iv a ct := by
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  simp only [ofNat_lit] at hab hj
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  rw [hf.out (hab.congr (blockAt_frame hf₀ (dS (by decide)))
      (bytesAt_frame hf₀ (dS (by omega)) (by omega))),
    ciph_keep hf₀ hdc hR,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

end

theorem streamFinish_wp {s₀ : State} (h : streamFinishArm.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishArm.post s₀ s' := by
  have h' : finPre 6 5 s₀ := streamFinishPreArm.fin h
  have L := finLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, tA, -, -, -, -, -, -, -, fT, -⟩ := h
  have hin : args s₀ 6 ∈ s₀.rd := h'.1.2
  have hTw : Covers [⟨State.addr (arg s₀ 4), 16⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (arg s₀ 4), 16⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (arg s₀ 0).toNat % 16 → (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → arg64 s₀ 0 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (State.addr (arg s₀ 4)) 16 =
          fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
            (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := fun ha hP =>
    WP.seq (fin1_wp (wi := 5) h' (by decide) (by decide) fun s₁ h1 =>
      WP.seq (WP.mono (fin_tag h' (by decide) h1 (.inl rfl) ha hP) fun s₂ hf => by
        obtain ⟨k7, he⟩ := hf.env
        obtain ⟨i4, v4⟩ := hf.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
        obtain ⟨s₃, run₃, hb₃, hf₃, g₃, rd₃, wr₃, sp₃⟩ := tagOut_ok L he i4 v4
          (by rw [hf.args.wr]; exact hTw) fT (by simpa using dW (d := 0) (k := 16) (by decide))
        refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
        have he₃ := he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) sp₃ rd₃ wr₃
        have sv₂ := h1.saved.frame hf.frame (saved_tagFrame L (.inl rfl))
        exact WP.mono (restore_ok he₃.r11 fW (covers_left he₃.perm.w)
          (sv₂.frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact (dW (by decide)).symm)) he₃.sp)
          fun s' hh => ⟨hh.1, fun iv hs hl => by
            have := fin_out h' h1.frame (ctx_saved L) (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr; simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)) hf hs hl
            rw [add_ofNat_zero] at this
            rw [hh.2.1, hb₃, this]⟩))
  have h₀ := run (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1 i.2.1 i.2.2 ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (low_mod16 hi.2.1).symm hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.AesGcm.Arm
