module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
import VerifiedGarbage.Proof.AesGcmSiv.X86.KeysCT
import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.KeysCT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Crypt
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.Crypt
import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Common

/-! ### `AesGcmSiv.X86.PolyvalCT`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86: POLYVAL is constant time

Untrusted: everything here is checked by Lean. A chunk branches on the
number of bytes left, its loop copies the blocks from the pointer in `esi`,
and `vg_ghash` absorbs as many blocks as the number left says: all public
(`chunk_ct`); the chunks of a string, its last bytes and the lengths
(`absorb_ct`, `lens_ct`), and the tag input (`tagIn_ct`), from the public
arguments (`polyval_ct`).
-/

@[expose] public section

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
  have hk1 : 1 ≤ min (m / 16) 64 := by omega_using [h16]
  refine CT.seq (J := fun s => Env p s ∧ Src p s Q (16 * min (m / 16) 64) ∧ s.gpr .esi = Q ∧
      s.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64))
    (chunkLen_ct L hm fun s h => ⟨h.env, h.n⟩)
    (fun s h => WP.mono (chunkLen_ok L h.env hm h.n) fun s₁ ⟨E₁, cx₁, _, _, si₁, rd₁, wr₁, _⟩ =>
      ⟨E₁, (h.src.take (by omega_using [])).of_eq rd₁ wr₁, by rw [si₁, h.esi], cx₁⟩) ?_
  refine CT.seq (J := RevI p Q (min (m / 16) 64))
    (CT.taint [.ebp] (pin_ebp fun s h => h.1.ebp) (by taint_decide))
    (fun s ⟨E, hQ, si, cx⟩ => WP.of_runBlock ⟨_, by grun [],
      ⟨E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems []), hQ.of_eq (by gmems []) (by gmems []),
        by gregs [si], by gregs [E.ebp], by gregs [cx]⟩⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (CT.taint [.esi, .edx, .ecx] (pin3 fun s h => ⟨h.esi, h.edx, h.ecx⟩) (by taint_decide))
    (fun s h => WP.mono (revLoop_ok L h.env hk1 (by omega_using []) h.src h.esi h.edx h.ecx) fun _ ⟨_, _, _, bp, _⟩ => by
      rw [bp, h.env.ebp]) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem chunk_ct (v : GcmImpl) {p : Prm} (L : Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) :
    CT (ChunkI p Q m) (chunk v.callees) := by
  have hk : min (m / 16) 64 ≤ 64 := by omega_using []
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
  have hN1 : 0 < nChunks (m / 16) := by unfold nChunks; omega_using [h16]
  have hN2 : 64 * (nChunks (m / 16) - 1) < m / 16 := by unfold nChunks; omega_using [h16]
  have hN3 : m / 16 ≤ 64 * nChunks (m / 16) := by unfold nChunks; omega_using []
  refine (CT.loopN (fun k s => 0 < k ∧ k ≤ nChunks (m / 16) ∧ ChunksI p Q m (64 * (nChunks (m / 16) - k)) s)
    (fun k => ?_) (fun k s ⟨hk0, hk, σ, I, hQ⟩ => ?_) (nChunks (m / 16))).mono
    fun s h => ⟨by omega_using [hN1], Nat.le_refl _, by rw [Nat.sub_self, Nat.mul_zero]; exact h⟩
  · by_cases hkk : 0 < k ∧ k ≤ nChunks (m / 16)
    · have hd : 64 * (nChunks (m / 16) - k) < m / 16 := by omega_using [hN2, hkk]
      exact (chunk_ct v L (Q := Q + BitVec.ofNat 32 (16 * (64 * (nChunks (m / 16) - k))))
        (m := m - 16 * (64 * (nChunks (m / 16) - k))) (by omega_using [hm]) (by omega_using [hN2, hkk])).mono fun s ⟨_, _, σ, I, hQ⟩ =>
          ⟨I.abs.env, I.src hQ hd, I.esi, I.n⟩
    · exact CT.of_empty fun s ⟨hk0, hk, _⟩ => hkk ⟨hk0, hk⟩
  · have hd : 64 * (nChunks (m / 16) - k) < m / 16 := by omega_using [hN2, hk0]
    refine WP.mono (chunk_ok v L I.abs.env (by omega_using [hm]) (by omega_using [hN2, hk0]) (I.src hQ hd) I.esi I.n) fun s' C => ?_
    obtain ⟨I', z⟩ := I.step L hQ hd C
    refine ⟨hk0, by rw [eval_ne z]; simp; omega_using [hN2, hN3, hk0, hk], fun hk1 => ⟨by omega_using [hk0, hk1], by omega_using [hk], σ, ?_, hQ⟩⟩
    have e : 64 * (nChunks (m / 16) - k) + min (m / 16 - 64 * (nChunks (m / 16) - k)) 64 =
        64 * (nChunks (m / 16) - (k - 1)) := by omega_using [hN2, hN3, hk, hk1]
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
        (Region.sub_prefix (by have := T.r16; omega_using [this]))
    have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r := by
      refine ⟨di₁, dx₁, cx₁, T.r1, by have := T.r16; omega_using [this], T.wrap, ?_, by rw [rd₁, wr₁]; exact T.rd, ?_, dB⟩
      · rw [L.nW (by decide)]; have := T.r16; omega_using [hw, this]
      · rw [L.aW (by decide)]
        exact covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 2816 by decide)) (by have := T.r16; omega_using [this])
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
    exact (chunks_ct v L (Q := Q) hm (by omega_using [h0])).mono fun s ⟨A, _⟩ =>
      ⟨s, CInv.zero A.env A.esi A.n, A.src.take (by omega_using [])⟩
  refine CT.seq (J := fun s => (∃ t, AbsI p Q m t ∧ Env p s ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
      s.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 (m % 16)) ∧
      s.zf = some (decide (m % 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun s ⟨_, _, E, _⟩ => E.ebp) (by taint_decide)) (fun s ⟨t, A, E, rd, wr, si, n⟩ => ?_) ?_
  · obtain ⟨s₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := anyLeft_ok L E (by omega_using []) n
    exact WP.of_runBlock ⟨s₁, run₁, ⟨t, A, E₁, by rw [rd₁, rd], by rw [wr₁, wr], by rw [si₁, si],
      by rw [slotv_eq, m₁]; exact n⟩, z₁⟩
  refine CT.ite (decide (m % 16 = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) fun hf => ?_
  have h0 : m % 16 ≠ 0 := of_decide_eq_false hf
  refine (absTail_ct v L (P := Q + BitVec.ofNat 32 (16 * (m / 16))) (r := m % 16)).mono
    fun s ⟨⟨t, A, E, rd, wr, si, n⟩, _⟩ => ?_
  have hs := A.src.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_using []) (by omega_using [h0])
  have ea := A.src.addr (j := 16 * (m / 16)) (by omega_using [h0])
  exact ⟨E, si, n, by omega_using [h0], by omega_using [], by rw [rd, wr]; exact hs.rd, hs.wrap,
    by rw [ea]; exact A.w.sub_left (Offset.sub_base _ (by omega_using []))⟩

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
    (fun s h => ⟨h.ebp, h.slots.nonce, h.perm.wR (by decide)⟩) (by have := L.ww; unfold nonceO; omega_using [this])
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

end

end

/-! ### `AesGcmSiv.X86.CryptCT`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. `tag o` calls `vg_aes_ctr32_to`
on public pointers (`tag_ct`); counter mode encrypts block after block of
the data, through the pointer in `esi`, as many as its public length says
(`crypt_ct`), and XORs the last bytes in a loop from public pointers and
counts (`cryptTail_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl xorLoop_ct XorPre xorLoop_ok covers_off covers_left)

theorem tag_ct (v : GcmImpl) {p : Prm} (L : Lay p) {o : Nat} (ho : TagO o) : CT (Env p) (tag v.callees o) := by
  have hc : CT (Env p) (.block (copy16 cbO ccO ++ zero4 o ++ ctrArgs o)) := by
    rcases ho with rfl | rfl | rfl <;> exact CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)
  refine CT.seq (J := fun t₁ => ∃ t, TagCall p o t t₁) hc
    (fun t E => by obtain ⟨t₁, run₁, C⟩ := tagArgs_ok L E ho; exact WP.of_runBlock ⟨t₁, run₁, t, C⟩)
    (callCtr_ct v L fun t₁ ⟨_, C⟩ => ⟨C.env, keyS L C.env.perm, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)

/-! ## A block -/

/-- What a block's call starts from. -/
structure BlkCall (p : Prm) (j : Nat) (t₁ : State) : Prop where
  env : Env p t₁
  dst : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1)
  eax : t₁.gpr .eax = p.W + BitVec.ofNat 32 512
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.D + BitVec.ofNat 32 (16 * j)
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  esi : t₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)

theorem blkCall_of {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁, runBlock isa blockArgs t = some t₁ ∧ BlkCall p j t₁ := by
  have hw := L.ww
  have hn' := L.n32
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ := blkArgs_ok L E hsi
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inl (by decide)))
  have eQ : w64 (p.D + BitVec.ofNat 32 (16 * j)) = w64 p.D + BitVec.ofNat 64 (16 * j) := L.dA (by omega_using [hj])
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_using [hj]))
  have hD : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1) := by
    refine ⟨?_, by rw [L.dN (by omega_using [hj])]; omega_using [hj, hdw], ?_, ?_, ?_, ?_⟩ <;> rw [eQ]
    · exact covers_off E₁.perm.d (by omega_using [hj]) (by omega_using [hn'])
    · rw [L.aW (by decide)]; exact (dQ.sub_right (Lay.wSub (show 512 + 240 ≤ 2816 by decide))).symm
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact L.bd.sub_right (Offset.sub_base _ (by omega_using [hj]))
  exact ⟨t₁, run₁, E₁, hD, eax, ecx, edx, ebx, edi, by rw [si₁, hsi]⟩

theorem cryptBlock_ct (v : GcmImpl) {p : Prm} (L : Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) :
    CT (fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) (cryptBlock v.callees) := by
  have hdw := L.dw
  refine CT.seq (J := BlkCall p j)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => ⟨h.1.ebp, h.2⟩) (by taint_decide))
    (fun t ⟨E, si⟩ => by obtain ⟨t₁, run₁, C⟩ := blkCall_of L E hj si; exact WP.of_runBlock ⟨t₁, run₁, C⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * j))
    (callCtr_ct v L fun t₁ C => ⟨C.env, keyS L C.env.perm, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)
    (fun t₁ C => WP.mono (callCtr_ok v L C.env (keyS L C.env.perm) C.dst
      (by rw [L.dA (by omega_using [hj])]; exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_using [hj])⟩) C.eax C.ecx C.edx
      C.ebx C.edi) fun s P => ⟨P.env.ebp, by rw [P.saved _ (by decide), C.esi]⟩)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => h) (by taint_decide))

/-- The whole blocks of the data, from `t`. -/
def BlocksI (p : Prm) (j : Nat) (s : State) : Prop :=
  ∃ t ciph icb x, x.length = p.n ∧ Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph ∧
    BlocksPost p ciph icb x j t s

theorem blocks_ct (v : GcmImpl) {p : Prm} (L : Lay p) (hb1 : 1 ≤ p.n / 16) :
    CT (BlocksI p 0) (.loop (cryptBlock v.callees) .ne) := by
  refine (CT.loopN (fun k s => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksI p j s) (fun k => ?_)
    (fun k s ⟨j, hk, hj, t, ciph, icb, x, hxl, hc, P⟩ => ?_) (p.n / 16)).mono
    fun s h => ⟨0, by omega_using [], by omega_using [hb1], h⟩
  · by_cases hkk : 0 < k ∧ k ≤ p.n / 16
    · exact (cryptBlock_ct v L (j := p.n / 16 - k) (by omega_using [hkk])).mono fun s ⟨j, hk', hj, _, _, _, _, _, _, P⟩ => by
        rw [show p.n / 16 - k = j by omega_using [hkk, hk']]; exact ⟨P.env, P.esi⟩
    · exact CT.of_empty fun s ⟨j, hk', hj, _⟩ => hkk ⟨by omega_using [hk', hj], by omega_using [hk']⟩
  · have hc' : Spec.GcmSiv.ctxCiph s.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
      rw [ciph_cryR L P.frame, hc]
    refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega_using [hj]) P.esi P.n P.ctr P.data hc') fun t'' Q => ?_
    refine ⟨by omega_using [hk, hj], by rw [eval_ne Q.z]; simp; omega_using [hk, hj], fun hk1 => ⟨j + 1, by omega_using [hk], by omega, t, ciph, icb, x, hxl, hc,
      ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.esi, Q.n, Q.ctr, Q.data, P.frame.trans Q.frame⟩⟩⟩

/-! ## The last bytes -/

theorem cryptTail_ct (v : GcmImpl) {p : Prm} (L : Lay p) {b r : Nat} (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r)
    (hr : r < 16) :
    CT (fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * b) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 r)
      (cryptTail v.callees) := by
  have hn' := L.n32
  have hdw := L.dw
  have hw := L.ww
  refine CT.seq (J := fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * b) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 r) ((tag_ct v L (o := 224) (by decide)).mono fun _ h => h.1)
    (fun t ⟨E, si, n⟩ => WP.mono (tag_ok v L E (o := 224) (by decide)) fun t₂ T => ⟨T.env, by rw [T.esi, si], ?_⟩) ?_
  · rw [← n]
    exact T.frame.readW (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  refine CT.seq (J := fun s => XorPre s (p.W + BitVec.ofNat 32 224) (p.D + BitVec.ofNat 32 (16 * b)) r)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => ⟨h.1.ebp, h.2.1⟩) (by taint_decide)) (fun t₂ ⟨E, si, n⟩ => ?_)
    (xorLoop_ct (pin3 fun _ h => ⟨h.edi, h.edx, h.ecx⟩))
  simp only [slotv_eq, nO] at n
  obtain ⟨t₃, run₃, dx₃, di₃, cx₃, m₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi), .mov .ecx (slot nO)] t₂ = some t₃ ∧
      t₃.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₃.gpr .edi = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .ecx = BitVec.ofNat 32 r ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, n], by gregs [E.ebp], by gregs [si], by gregs [n], by gmems [], by gmems [],
      by gmems []⟩
  have eD := L.dA (j := 16 * b) (by omega_using [hn, hr1])
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_using [hn]))
  refine WP.of_runBlock ⟨t₃, run₃, dx₃, di₃, cx₃, by omega_using [hr1], by omega_using [hr], by rw [L.nW (by decide)]; omega_using [hr, hw],
    by rw [L.dN (by omega_using [hn, hr1])]; omega_using [hn, hdw], ?_, ?_, ?_⟩
  · rw [rd₃, wr₃, L.aW (by decide)]
    exact covers_prefix (E.perm.wCR (show 224 + 16 ≤ 2816 by decide)) (by omega_using [hr])
  · rw [wr₃, eD]; exact covers_off E.perm.d (by omega_using [hn]) (by omega_using [hn'])
  · rw [eD, L.aW (by decide)]
    exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega_using [hr]))).symm

/-! ## `crypt` -/

theorem crypt_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (crypt v.callees) := by
  have hn := L.n32
  refine CT.seq (J := fun s => ∃ t, CStart p t s) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => by obtain ⟨t₁, run₁, S⟩ := cryptStart_ok L E; exact WP.of_runBlock ⟨t₁, run₁, t, S⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 (p.n % 16))
    (CT.ite (decide (p.n / 16 = 0)) (fun s ⟨_, S⟩ => eval_e S.z) (fun _ => CT.nil) fun hf => ?_)
    (fun t₁ ⟨t, S⟩ => ?_) ?_
  · have h0 : p.n / 16 ≠ 0 := of_decide_eq_false hf
    refine (blocks_ct v L (by omega_using [h0])).mono fun s ⟨t, S⟩ => ⟨s, _, _, bytesAt s.mem (w64 p.D) p.n,
      Proof.Cmac.bytesAt_length _ _ _, rfl, ⟨S.env, rfl, rfl, by rw [S.esi, Nat.mul_zero, BitVec.add_zero],
        by rw [S.n, Nat.mul_zero, Nat.sub_zero], S.ctr, by rw [Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  · have hxl : (bytesAt t₁.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
    refine WP.mono (Q := BlocksPost p (Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t₁.mem (w64 p.D) p.n) (p.n / 16) t₁)
      ?_ fun t₂ B => ⟨B.env, B.esi, by rw [B.n]; congr 1; omega_using []⟩
    refine WP.ite (decide (p.n / 16 = 0)) (eval_e S.z) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨S.env, rfl, rfl, by rw [S.esi, Nat.mul_zero, BitVec.add_zero], by rw [S.n, Nat.mul_zero, Nat.sub_zero],
        S.ctr, by rw [Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok v L S.env hxl (by omega_using [h0]) S.esi S.n S.ctr rfl rfl
  refine CT.seq (J := fun s => (Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 (p.n % 16)) ∧ s.zf = some (decide (p.n % 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun s ⟨E, si, n⟩ => ?_) ?_
  · obtain ⟨s₁, run₁, z₁, E₁, si₁, m₁, -, -⟩ := anyLeft_ok L E (by omega_using []) n
    exact WP.of_runBlock ⟨s₁, run₁, ⟨E₁, by rw [si₁, si], by rw [slotv_eq, m₁]; exact n⟩, z₁⟩
  refine CT.ite (decide (p.n % 16 = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) fun hf => ?_
  have h0 : p.n % 16 ≠ 0 := of_decide_eq_false hf
  exact (cryptTail_ct v L (b := p.n / 16) (r := p.n % 16) (by omega_using []) (by omega_using [h0]) (by omega_using [])).mono
    fun s ⟨h, _⟩ => h

end VG.Proof.AesGcmSiv.X86

end

end

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public, and so is everything the pieces' preconditions say (`prmOf`). The
entry loads `work` from the stack, at `esp`, and saves our caller's registers
and the arguments through it (`entry_ct`); `cmp` computes the result without
a branch, and `mask` loops over the data's length alone (`mask_ct`); the
other pieces are constant time from `Env` (`keys_ct`, `polyval_ct`,
`tag_ct`, `crypt_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp)
open VG.Proof.AesGcm.X86 (CT w64 GcmImpl argA argA_contains)

/-- The public arguments are a function of what `onePub` says is public. -/
theorem prmOf_pub {s₁ s₂ : State} (h : onePub s₁ s₂) : prmOf s₁ = prmOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [prmOf, h₁, h₂ 0 (by decide), h₂ 1 (by decide), h₂ 2 (by decide), h₂ 3 (by decide), h₂ 4 (by decide),
    h₂ 5 (by decide), h₂ 6 (by decide), h₂ 7 (by decide), h₂ 8 (by decide)]

theorem entryLoad_ok {p : Prm} {s : State} (h : onePre s) (hp : prmOf s = p) :
    ∃ s', runBlock isa [.mov .eax (argOp 8)] s = some s' ∧ s'.gpr .eax = p.W ∧ s'.gpr .esp = p.SP := by
  have Ao := argsOk_of h
  have hw : p.W = arg s 8 := hp ▸ rfl
  have hsp : p.SP = s.gpr .esp := hp ▸ rfl
  have rA := Ao.rA
  have fa := Ao.fa
  generalize hSP : s.gpr .esp = SP at rA fa hsp
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 :=
    rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine ⟨_, by grun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, hw, ← hSP]; rfl
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP, hsp]

theorem entrySave_ct {p : Prm} :
    CT (fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
      (.block (Impl.AesGcm.X86.saveAt ++ entryPs.flatMap (fun q => Impl.AesGcm.X86.keep q.1 q.2))) :=
  CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide)

theorem entry_ct {p : Prm} : CT (fun s => onePre s ∧ prmOf s = p) sivEntry := by
  have e : ∀ s, prmOf s = p → s.gpr .esp = p.SP := fun s h => h ▸ rfl
  rw [sivEntry_eq]
  refine CT.seq (J := fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
    (CT.taint [.esp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e _ h₁.2, e _ h₂.2]) (by taint_decide))
    (fun s ⟨h, hp⟩ => let ⟨s', run, ax, sp⟩ := entryLoad_ok h hp; WP.of_runBlock ⟨s', run, ax, sp⟩) entrySave_ct

/-! ## The mask -/

theorem mask_ct {p : Prm} (L : Lay p) : CT (Env p) mask := by
  refine CT.block_seq (F := fun _ s₁ => s₁.zf = some (decide (p.n = 0)) ∧ Env p s₁ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.n) [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)
    (fun s E => let ⟨s₁, run, _, _, cx, zf, _, E₁, _⟩ := maskTest_ok L E; ⟨s₁, run, zf, E₁, cx⟩) ?_
  refine CT.ite (decide (p.n = 0)) (fun _ ⟨_, _, zf, _⟩ => eval_e zf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq (F := fun _ s₂ => s₂.gpr .edi = p.D ∧ s₂.gpr .ecx = BitVec.ofNat 32 p.n) [.ebp]
    (pin_ebp fun _ ⟨_, _, _, E, _⟩ => E.ebp) (by taint_decide)
    (fun s₁ ⟨_, _, _, E₁, cx⟩ => let ⟨s₂, run, _, di, g, _⟩ := maskArgs_ok L E₁;
      ⟨s₂, run, di, by rw [g _ (by decide), cx]⟩) ?_
  exact CT.taint [.edi, .ecx] (pin2 fun _ ⟨_, _, di, cx⟩ => ⟨di, cx⟩) (by taint_decide)

/-! ## `seal` -/

theorem seal_top_ct (v : GcmImpl) {p : Prm} (L : Lay p) :
    CT (fun s => sealPre s ∧ prmOf s = p) («seal» v.callees) := by
  have tw : ∀ s, sealPre s → prmOf s = p → Covers [⟨w64 p.T, 16⟩] s.wr := fun s h hp => by
    subst hp; exact covers_of_mem (by rw [h.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine CT.seq (J := fun s₁ => ∃ s, (sealPre s ∧ prmOf s = p) ∧ Entered s p s₁)
    (entry_ct.mono fun s h => ⟨onePre_seal h.1, h.2⟩)
    (fun s ⟨h, hp⟩ => WP.mono (entry_ok (onePre_seal h)) fun s₁ En => ⟨s, ⟨h, hp⟩, hp ▸ En⟩) ?_
  refine CT.seq (J := fun s => ∃ σ, KeysPost p σ s ∧ Covers [⟨w64 p.T, 16⟩] σ.wr)
    ((keys_ct v L).mono fun _ ⟨_, _, En⟩ => En.env)
    (fun _ ⟨s, ⟨h, hp⟩, En⟩ => WP.mono (keys_ok v L En.env) fun _ Ky => ⟨_, Ky, by rw [En.wr]; exact tw s h hp⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr) ((polyval_ct v L).mono fun _ ⟨_, Ky, _⟩ => Ky.env)
    (fun _ ⟨_, Ky, t⟩ => WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun _ Po =>
      ⟨Po.env, by rw [Po.wr, Ky.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr)
    ((tag_ct v L (o := 0) (by decide)).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (tag_ok v L E (o := 0) (by decide)) fun _ Tg => ⟨Tg.env, by rw [Tg.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr) ((crypt_ct v L).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (crypt_ok v L E) fun _ Cr => ⟨Cr.env, by rw [Cr.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W) ((tagOut_ct L).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (tagOut_ok L E t) fun _ ⟨_, _, bp, _⟩ => bp) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callees) :=
  CT.constantTime prmOf (fun _ _ _ _ h => prmOf_pub h) fun p => by
    by_cases hex : ∃ s, sealPre s ∧ prmOf s = p
    · obtain ⟨z, hz, rfl⟩ := hex
      exact seal_top_ct v (lay_of (onePre_seal hz))
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

/-! ## `open` -/

theorem open_top_ct (v : GcmImpl) {p : Prm} (L : Lay p) :
    CT (fun s => openPre s ∧ prmOf s = p) («open» v.callees) := by
  refine CT.seq (J := fun s₁ => ∃ s, (openPre s ∧ prmOf s = p) ∧ Entered s p s₁)
    (entry_ct.mono fun s h => ⟨onePre_open h.1, h.2⟩)
    (fun s ⟨h, hp⟩ => WP.mono (entry_ok (onePre_open h)) fun s₁ En => ⟨s, ⟨h, hp⟩, hp ▸ En⟩) ?_
  refine CT.seq (J := Env p) ((recvTag_ct L).mono fun _ ⟨_, _, En⟩ => En.env)
    (fun _ ⟨_, _, En⟩ => WP.mono (recvTag_ok L En.env) fun _ h => h.1) ?_
  refine CT.seq (J := fun s => ∃ σ, KeysPost p σ s) (keys_ct v L)
    (fun _ E => WP.mono (keys_ok v L E) fun s Ky => ⟨_, Ky⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧
      Spec.Gcm.blockAt s.mem (w64 p.W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt s.mem (w64 p.W + BitVec.ofNat 64 80) = 0)
    ((crypt_ct v L).mono fun _ ⟨_, Ky⟩ => Ky.env)
    (fun _ ⟨_, Ky⟩ => WP.mono (crypt_ok v L Ky.env) fun _ Cr => ⟨Cr.env, (keys_crypt L Ky Cr).1, (keys_crypt L Ky Cr).2.1⟩) ?_
  refine CT.seq (J := Env p) ((polyval_ct v L).mono fun _ h => h.1)
    (fun _ h => WP.mono (polyval_ok v L h.1 h.2.1 h.2.2) fun _ Po => Po.env) ?_
  refine CT.seq (J := Env p) (tag_ct v L (o := 240) (by decide))
    (fun _ E => WP.mono (tag_ok v L E (o := 240) (by decide)) fun _ Tg => Tg.env) ?_
  refine CT.seq (J := fun s => Env p s ∧ ∃ c : Bool, s.gpr .eax = BitVec.ofNat 32 (if c then 1 else 0))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun s E => ?_) ?_
  · obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := cmp_ok L E
    refine WP.of_runBlock ⟨s₆, run₆, E.keep (by rw [bp₆, E.ebp]) (by rw [sp₆, E.esp]) rd₆ wr₆ hm₆,
      decide (bytesAt s.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 240) 16), ?_⟩
    rw [ax₆]; simp only [okVal, decide_eq_true_eq]
  refine CT.seq (J := Env p) ((mask_ct L).mono fun _ h => h.1)
    (fun _ ⟨E, _, hc⟩ => WP.mono (mask_ok L E hc) fun _ Mk => Mk.env) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)

theorem open_ct (v : GcmImpl) : ConstantTime isa openX86.pre openX86.pub («open» v.callees) :=
  CT.constantTime prmOf (fun _ _ _ _ h => prmOf_pub h) fun p => by
    by_cases hex : ∃ s, openPre s ∧ prmOf s = p
    · obtain ⟨z, hz, rfl⟩ := hex
      exact open_top_ct v (lay_of (onePre_open hz))
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesGcmSiv.X86
