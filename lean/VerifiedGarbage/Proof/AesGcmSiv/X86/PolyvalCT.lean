import VerifiedGarbage.Proof.AesGcmSiv.X86.KeysCT

/-!
# AES-GCM-SIV on x86: POLYVAL is constant time

Untrusted: everything here is checked by Lean. A chunk branches on the
number of bytes left, its loop copies the blocks from the pointer in `esi`,
and `vg_ghash` absorbs as many blocks as the number left says: all public
(`chunk_ct`); the chunks of a string, its last bytes and the lengths
(`absorb_ct`, `lens_ct`), and the tag input (`tagIn_ct`), from the public
arguments (`polyval_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl copyLoop_ct LoopPre copyLoop_ok covers_left covers_off
  length_bytesAt)

/-! ## A chunk -/

theorem chunkLen_ct {p : Prm} (L : Lay p) {m : Nat} (hm : m < 2 ^ 32) {I : State → Prop}
    (hI : ∀ s, I s → Env p s ∧ slotv s.mem p.W nO = BitVec.ofNat 32 m) : CT I chunkLen := by
  refine CT.seq (J := fun t₁ => t₁.gpr .ebp = p.W ∧ t₁.cf = some (decide (m / 16 < 64)))
    (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide)) (fun s h => ?_) ?_
  · obtain ⟨t₁, run₁, _, cf₁, bp₁, _⟩ := chunkLen1_ok L (hI s h).1 hm (hI s h).2
    exact WP.of_runBlock ⟨t₁, run₁, bp₁, cf₁⟩
  have hmov : CT (fun t₁ => t₁.gpr .ebp = p.W ∧ t₁.cf = some (decide (m / 16 < 64))) (.block [.mov .ecx (imm 64)]) :=
    CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (CT.ite (decide (m / 16 < 64)) (fun s h => eval_b h.2) (fun _ => CT.nil) (fun _ => hmov))
    (fun s h => WP.ite (decide (m / 16 < 64)) (eval_b h.2) (fun _ => WP.block_nil h.1)
      (fun _ => WP.of_runBlock ⟨_, by grun [], by gregs [h.1]⟩))
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

/-- What a chunk of the `m` bytes at `Q` starts from. -/
structure ChunkI (p : Prm) (Q : BitVec 32) (m : Nat) (s : State) : Prop where
  env : Env p s
  src : Src p s Q (16 * (m / 16))
  esi : s.gpr .esi = Q
  n : slotv s.mem p.W nO = BitVec.ofNat 32 m

/-- Before `revLoop`. -/
structure RevI (p : Prm) (Q : BitVec 32) (k : Nat) (s : State) : Prop where
  env : Env p s
  src : Src p s Q (16 * k)
  esi : s.gpr .esi = Q
  edx : s.gpr .edx = p.W + BitVec.ofNat 32 768
  ecx : s.gpr .ecx = BitVec.ofNat 32 k

theorem chunkPre_ct {p : Prm} (L : Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) :
    CT (ChunkI p Q m) chunkPre := by
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  refine CT.seq (J := fun s => Env p s ∧ Src p s Q (16 * min (m / 16) 64) ∧ s.gpr .esi = Q ∧
      s.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64))
    (chunkLen_ct L hm fun s h => ⟨h.env, h.n⟩)
    (fun s h => WP.mono (chunkLen_ok L h.env hm h.n) fun s₁ ⟨E₁, cx₁, _, _, si₁, rd₁, wr₁, _⟩ =>
      ⟨E₁, (h.src.take (by omega)).of_eq rd₁ wr₁, by rw [si₁, h.esi], cx₁⟩) ?_
  refine CT.seq (J := RevI p Q (min (m / 16) 64))
    (CT.taint [.ebp] (pin_ebp fun s h => h.1.ebp) (by taint_decide))
    (fun s ⟨E, hQ, si, cx⟩ => WP.of_runBlock ⟨_, by grun [],
      ⟨E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems []), hQ.of_eq (by gmems []) (by gmems []),
        by gregs [si], by gregs [E.ebp], by gregs [cx]⟩⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (CT.taint [.esi, .edx, .ecx] (pin3 fun s h => ⟨h.esi, h.edx, h.ecx⟩) (by taint_decide))
    (fun s h => WP.mono (revLoop_ok L h.env hk1 (by omega) h.src h.esi h.edx h.ecx) fun _ ⟨_, _, _, bp, _⟩ => by
      rw [bp, h.env.ebp]) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem chunk_ct (v : GcmImpl) {p : Prm} (L : Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) :
    CT (ChunkI p Q m) (chunk v.callees) := by
  have hk : min (m / 16) 64 ≤ 64 := by omega
  refine CT.seq (J := fun t₅ => ∃ t, ChunkI p Q m t ∧ ChunkPre p Q m (min (m / 16) 64) t t₅)
    (chunkPre_ct L hm h16) (fun t h => WP.mono (chunkPre_ok L h.env hm h16 h.src h.esi h.n) fun t₅ Pr => ⟨t, h, Pr⟩)
    (CT.seq (J := fun s => s.gpr .ebp = p.W)
      (callGh_ct v L hk fun s ⟨_, _, Pr⟩ => ⟨Pr.env, Pr.eax, Pr.edx, Pr.ebx, Pr.edi⟩)
      (fun s ⟨_, _, Pr⟩ => WP.mono (callGh_ok v L Pr.env hk Pr.eax Pr.edx Pr.ebx Pr.edi) fun _ P => P.env.ebp)
      (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)))

/-! ## The chunks of a string -/

/-- The chunks of the `m` bytes at `Q`, from some `σ`, after `d` blocks. -/
def ChunksI (p : Prm) (Q : BitVec 32) (m d : Nat) (s : State) : Prop :=
  ∃ σ, CInv p σ Q m d s ∧ Src p σ Q (16 * (m / 16))

/-- The number of chunks of `b` whole blocks. -/
abbrev nChunks (b : Nat) : Nat := (b + 63) / 64

theorem chunks_ct (v : GcmImpl) {p : Prm} (L : Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) : CT (ChunksI p Q m 0) (.loop (chunk v.callees) .ne) := by
  have hN1 : 0 < nChunks (m / 16) := by unfold nChunks; omega
  have hN2 : 64 * (nChunks (m / 16) - 1) < m / 16 := by unfold nChunks; omega
  have hN3 : m / 16 ≤ 64 * nChunks (m / 16) := by unfold nChunks; omega
  refine (CT.loopN (fun k s => 0 < k ∧ k ≤ nChunks (m / 16) ∧ ChunksI p Q m (64 * (nChunks (m / 16) - k)) s)
    (fun k => ?_) (fun k s ⟨hk0, hk, σ, I, hQ⟩ => ?_) (nChunks (m / 16))).mono
    fun s h => ⟨by omega, Nat.le_refl _, by rw [Nat.sub_self, Nat.mul_zero]; exact h⟩
  · by_cases hkk : 0 < k ∧ k ≤ nChunks (m / 16)
    · have hd : 64 * (nChunks (m / 16) - k) < m / 16 := by omega
      exact (chunk_ct v L (Q := Q + BitVec.ofNat 32 (16 * (64 * (nChunks (m / 16) - k))))
        (m := m - 16 * (64 * (nChunks (m / 16) - k))) (by omega) (by omega)).mono fun s ⟨_, _, σ, I, hQ⟩ =>
          ⟨I.abs.env, I.src hQ hd, I.esi, I.n⟩
    · exact CT.of_empty fun s ⟨hk0, hk, _⟩ => hkk ⟨hk0, hk⟩
  · have hd : 64 * (nChunks (m / 16) - k) < m / 16 := by omega
    refine WP.mono (chunk_ok v L I.abs.env (by omega) (by omega) (I.src hQ hd) I.esi I.n) fun s' C => ?_
    obtain ⟨I', z⟩ := I.step L hQ hd C
    refine ⟨hk0, by rw [eval_ne z]; simp; omega, fun hk1 => ⟨by omega, by omega, σ, ?_, hQ⟩⟩
    have e : 64 * (nChunks (m / 16) - k) + min (m / 16 - 64 * (nChunks (m / 16) - k)) 64 =
        64 * (nChunks (m / 16) - (k - 1)) := by omega
    rw [e] at I'
    exact I'

/-! ## The last bytes -/

/-- What the last `r` bytes at `P` start from. -/
structure TailI (p : Prm) (P : BitVec 32) (r : Nat) (s : State) : Prop where
  env : Env p s
  esi : s.gpr .esi = P
  n : slotv s.mem p.W nO = BitVec.ofNat 32 r
  r1 : 1 ≤ r
  r16 : r < 16
  rd : Covers [⟨w64 P, r⟩] (s.rd ++ s.wr)
  wrap : P.toNat + r ≤ 2 ^ 32
  w : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩

theorem absTailPre_ct {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} : CT (TailI p P r) absTailPre := by
  have hw := L.ww
  refine CT.seq (J := fun t₁ => LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r ∧ t₁.gpr .ebp = p.W)
    (CT.taint [.ebp, .esi] (pin2 fun s h => ⟨h.env.ebp, h.esi⟩) (by taint_decide)) (fun t T => ?_) ?_
  · obtain ⟨t₁, run₁, hm₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ := absTail1_ok L T.env T.esi T.n
    have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
      rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have E₁ : Env p t₁ := T.env.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
    have dB : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 (p.W + BitVec.ofNat 32 224), r⟩ := by
      rw [L.aW (by decide)]
      exact (T.w.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right
        (Region.sub_prefix (by have := T.r16; omega))
    have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r := by
      refine ⟨di₁, dx₁, cx₁, T.r1, by have := T.r16; omega, T.wrap, ?_, by rw [rd₁, wr₁]; exact T.rd, ?_, dB⟩
      · rw [L.nW (by decide)]; have := T.r16; omega
      · rw [L.aW (by decide)]
        exact covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 2816 by decide)) (by have := T.r16; omega)
    exact WP.of_runBlock ⟨t₁, run₁, lp, bp₁⟩
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (copyLoop_ct (pin3 fun s h => ⟨h.1.edi, h.1.edx, h.1.ecx⟩))
    (fun s h => WP.mono (copyLoop_ok s h.1) fun _ O => by
      rw [O.other _ (by decide) (by decide) (by decide) (by decide), h.2])
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem absTail_ct (v : GcmImpl) {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} :
    CT (TailI p P r) (absTail v.callees) :=
  CT.seq (J := fun t₃ => ∃ t, TailI p P r t ∧ TailPre p (w64 P) r t t₃) (absTailPre_ct L)
    (fun t T => WP.mono (absTailPre_ok L T.env T.r1 T.r16 T.rd T.wrap T.w T.esi T.n) fun t₃ h => ⟨t, T, h⟩)
    ((chunk_ct v L (Q := p.W + BitVec.ofNat 32 224) (m := 16) (by decide) (by decide)).mono
      fun s ⟨_, _, h⟩ => ⟨h.env, srcB L h.env.perm, h.esi, h.n⟩)

/-! ## Absorbing a string -/

/-- What absorbing the `m` bytes at `Q` starts from. -/
structure AbsI (p : Prm) (Q : BitVec 32) (m : Nat) (s : State) : Prop where
  env : Env p s
  src : Src p s Q m
  w : (⟨w64 Q, m⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  esi : s.gpr .esi = Q
  n : slotv s.mem p.W nO = BitVec.ofNat 32 m

theorem AbsI.keep {p : Prm} {Q : BitVec 32} {m : Nat} {s s' : State} (h : AbsI p Q m s) (E : Env p s')
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) (hsi : s'.gpr .esi = s.gpr .esi) :
    AbsI p Q m s' :=
  ⟨E, h.src.of_eq hrd hwr, h.w, by rw [hsi, h.esi], by rw [slotv_eq, hm]; exact h.n⟩

theorem absorb_ct (v : GcmImpl) {p : Prm} (L : Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) :
    CT (AbsI p Q m) (absorb v.callees) := by
  refine CT.seq (J := fun s => AbsI p Q m s ∧ s.zf = some (decide (m / 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)) (fun t A => ?_) ?_
  · obtain ⟨t₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := wholeLeft_ok L A.env hm A.n
    exact WP.of_runBlock ⟨t₁, run₁, A.keep E₁ rd₁ wr₁ m₁ si₁, z₁⟩
  refine CT.seq (J := fun s => ∃ t, AbsI p Q m t ∧ Env p s ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
      s.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 (m % 16))
    (CT.ite (decide (m / 16 = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) fun hf => ?_)
    (fun t ⟨A, z⟩ => WP.mono (absMid_ok v L A.env hm A.src A.esi A.n z) fun s ⟨P, si, n⟩ =>
      ⟨t, A, P.env, P.rd, P.wr, si, n⟩) ?_
  · have h0 : m / 16 ≠ 0 := of_decide_eq_false hf
    exact (chunks_ct v L (Q := Q) hm (by omega)).mono fun s ⟨A, _⟩ =>
      ⟨s, CInv.zero A.env A.esi A.n, A.src.take (by omega)⟩
  refine CT.seq (J := fun s => (∃ t, AbsI p Q m t ∧ Env p s ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
      s.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 (m % 16)) ∧
      s.zf = some (decide (m % 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun s ⟨_, _, E, _⟩ => E.ebp) (by taint_decide)) (fun s ⟨t, A, E, rd, wr, si, n⟩ => ?_) ?_
  · obtain ⟨s₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := anyLeft_ok L E (by omega) n
    exact WP.of_runBlock ⟨s₁, run₁, ⟨t, A, E₁, by rw [rd₁, rd], by rw [wr₁, wr], by rw [si₁, si],
      by rw [slotv_eq, m₁]; exact n⟩, z₁⟩
  refine CT.ite (decide (m % 16 = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) fun hf => ?_
  have h0 : m % 16 ≠ 0 := of_decide_eq_false hf
  refine (absTail_ct v L (P := Q + BitVec.ofNat 32 (16 * (m / 16))) (r := m % 16)).mono
    fun s ⟨⟨t, A, E, rd, wr, si, n⟩, _⟩ => ?_
  have hs := A.src.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
  have ea := A.src.addr (j := 16 * (m / 16)) (by omega)
  exact ⟨E, si, n, by omega, by omega, by rw [rd, wr]; exact hs.rd, hs.wrap,
    by rw [ea]; exact A.w.sub_left (Offset.sub_base _ (by omega))⟩

/-! ## The lengths, the tag input, and `polyval` -/

theorem lens_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (lens v.callees) := by
  refine CT.seq (J := ChunkI p (p.W + BitVec.ofNat 32 224) 16)
    (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)) (fun t E => ?_) (chunk_ct v L (by decide) (by decide))
  obtain ⟨t₁, run₁, hm₁, si₁, bp₁, sp₁, rd₁, wr₁⟩ := lensBlock_ok L E
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
  exact WP.of_runBlock ⟨t₁, run₁, E₁, srcB L E₁.perm, si₁, by rw [slotv_eq, hm₁, lensMem, Mem.readW_writeW_self32]⟩

theorem tagIn_ct {p : Prm} (L : Lay p) : CT (Env p) (.block tagIn) :=
  ldPin (r := .ecx) (o := nonceO) (x := p.N) (W := p.W)
    (fun s h => ⟨h.ebp, h.slots.nonce, h.perm.wR (by decide)⟩) (by have := L.ww; unfold nonceO; omega)
    (by decide) (by taint_decide) (by taint_decide)

theorem polyval_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (polyval v.callees) := by
  refine CT.seq (J := AbsI p p.A p.al) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.seq (J := Env p) (absorb_ct v L L.al32)
      (fun t A => WP.mono (absorb_ok v L A.env L.al32 A.src A.w A.esi A.n) fun _ P => P.env)
      (CT.seq (J := AbsI p p.D p.n) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
        (CT.seq (J := Env p) (absorb_ct v L L.n32)
          (fun t A => WP.mono (absorb_ok v L A.env L.n32 A.src A.w A.esi A.n) fun _ P => P.env)
          (CT.seq (J := Env p) (lens_ct v L) (fun t E => WP.mono (lens_ok v L E) fun _ P => P.env) (tagIn_ct L)))))
  · obtain ⟨t₁, run₁, E₁, si₁, n₁, _, _, _⟩ := onStr_ok L E (s := aadO) (l := alenO) (by decide) (by decide)
      E.slots.aad E.slots.alen
    exact WP.of_runBlock ⟨t₁, run₁, E₁, srcBuf E₁.perm.aad L.aw L.a_w L.ba, L.a_w, si₁, n₁⟩
  · obtain ⟨t₁, run₁, E₁, si₁, n₁, _, _, _⟩ := onStr_ok L E (s := dataO) (l := lenO) (by decide) (by decide)
      E.slots.data E.slots.len
    exact WP.of_runBlock ⟨t₁, run₁, E₁, srcBuf (covers_left E₁.perm.d) L.dw L.d_w L.bd, L.d_w, si₁, n₁⟩

end VG.Proof.AesGcmSiv.X86
