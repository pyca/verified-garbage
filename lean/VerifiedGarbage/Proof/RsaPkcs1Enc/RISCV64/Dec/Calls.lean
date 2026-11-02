module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.D
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Calls
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the calls after the private-key operation

Untrusted: everything here is checked by Lean. After the private-key
operation, every call is of SHA-256's streaming functions or of HMAC-SHA-256's
`init` and `finalize`, on states, keys and digests in `scratch`: each keeps
`Post` (`Post.after`), and gives what its contract says (`shaInit_ok`,
`shaUpd_ok`, `shaFin_ok`, `macInit_ok`, `macFin_ok`), with the memory it
changed (`After`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

/-- What the proofs know of SHA-256's streaming functions. -/
abbrev hH : HashOK sha256 := VG.Proof.Hmac.Stream.RISCV64.Sha256Family.ok256

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (t : State) (ws : List Region) (w : State) : Prop where
  rd : w.rd = t.rd
  wr : w.wr = t.wr
  sp : w.sp = t.sp
  cs : ∀ r ∈ preserved, w.gpr r = t.gpr r
  frame : Frame ws t.mem w.mem

/-- `[scratch + a, scratch + a + l)`. -/
abbrev scR (s : State) (a l : Nat) : Region := ⟨scA s a, l⟩

/-- The largest stack the callees use, below our frame. -/
def callX : Nat := 2048

theorem hmac_sizes : sha256.ibytes + sha256.F ≤ callX ∧ sha256.fbytes + sha256.F ≤ callX ∧
    sha256.F ≤ callX ∧ sha256.S = 96 ∧ sha256.D = 32 ∧ sha256.B = 64 := by decide

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

omit h in
theorem low_sub {X : Nat} (hX : X ≤ callX) : Region.Sub (below (fb s) X) (lowR s) :=
  below_sub (by unfold callX Impl.Rsa.RISCV64.Priv.frameBytes at *; omega) (by decide)

/-- `Post` is kept by a call writing `scratch` and the callees' frames. -/
theorem Post.after {t w : State} (hp : Post s R EM t) {ws : List Region} (a : After t ws w)
    (hs : ∀ r ∈ ws, Region.Sub r (sR s) ∨ Region.Sub r (lowR s)) : Post s R EM w := by
  have cs := callee_sub s
  have g : ∀ r ∈ kept, w.gpr r = t.gpr r := fun r hr => a.cs r (by revert r; decide)
  refine ⟨hp.toMid.of g a.sp a.rd a.wr (hp.mem.trans (a.frame.sub fun r hr => ?_))
    (hp.sv.frame a.frame fun q hq r hr => ?_), (a.cs _ (by decide)).trans hp.r, ?_⟩
  · rcases hs r hr with hr' | hr'
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), hr'⟩
    · exact ⟨_, List.mem_cons_self .., sub_trans hr' cs⟩
  · have := saved_offs q hq
    rcases hs r hr with hr' | hr'
    · exact (h.ks.sub_left (frame_sub s (by unfold oEnd frameBytes at *; omega))).sub_right hr'
    · exact (slot_low s (by unfold oEnd frameBytes at *; omega)).sub_right hr'
  · rw [← hp.em]
    exact bytes_of_frame (s := t) a.frame (fun r hr => by
      rcases hs r hr with hr' | hr'
      · have := h.os.sub_right hr'; simp only [oR, h.h1] at this; exact this
      · have := (h.ko.symm.sub_right cs).sub_right hr'; simp only [oR, h.h1] at this; exact this)
      (by have := h.wo; have := h.h1; omega)

omit h in
/-- Two parts of `scratch` apart. -/
theorem scDisj {a l b m : Nat} (hab : a + l ≤ b ∨ b + m ≤ a) (ha : a + l ≤ scrBytes) (hb : b + m ≤ scrBytes) :
    Region.Disjoint (scR s a l) (scR s b m) :=
  Offset.disjoint _ hab (by unfold scrBytes at ha; omega) (by unfold scrBytes at hb; omega)

/-- The callees' stack misses `scratch`. -/
theorem lowSc {X a l : Nat} (hX : X ≤ callX) (ha : a + l ≤ scrBytes) :
    (below (fb s) X).Disjoint (scR s a l) :=
  ((h.ks.sub_left (sub_trans (low_sub hX) (callee_sub s))).sub_right (scSub h ha))

/-- The callees' stack is below the stack pointer. -/
theorem fb_ge {X : Nat} (hX : X ≤ callX) : X ≤ (fb s).toNat := by
  have := kb_toNat h; have := fb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes callX at *; omega

/-- Writes of `scratch` and the callees' stack keep `Post`. -/
theorem Post.after_sc {t w : State} (hp : Post s R EM t) {ws : List (Nat × Nat)} {X : Nat} (hX : X ≤ callX)
    (hws : ∀ p ∈ ws, p.1 + p.2 ≤ scrBytes)
    (a : After t (ws.map (fun p => scR s p.1 p.2) ++ [below t.sp X]) w) : Post s R EM w :=
  hp.after h a fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      exact .inl (scSub h (hws p hp'))
    · rw [List.mem_singleton.mp hr, hp.sp]; exact .inr (low_sub hX)

/-! ## SHA-256 -/

/-- `init` of the state at `scratch + a`. -/
theorem shaInit_ok {t : State} (hp : Post s R EM t) {a : Nat} (ha : a + 96 ≤ scrBytes)
    (h0 : t.gpr .a0 = scA s a) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w → After t ([scR s a 96] ++ [below t.sp sha256.F]) w →
      hH.SH.Repr w.mem (scA s a) [] → Q w) :
    WP isa sha256.callInit t Q := by
  have hc := scCov h hp.wr ha
  refine hH.callInit_ok h0 (Covers.right hc) hc fun w hrd hwr hsp hf hg hr => ?_
  have A : After t ([scR s a 96] ++ [below t.sp sha256.F]) w := ⟨hrd, hwr, hsp, hg, hf⟩
  exact hQ w (hp.after_sc h (ws := [(a, 96)]) (X := sha256.F) (by decide)
    (by simp only [List.mem_singleton]; rintro _ rfl; exact ha) A) A hr

/-- `update` of the state at `scratch + a` with the `len` bytes at `dat`. -/
theorem shaUpd_ok {t : State} (hp : Post s R EM t) {a : Nat} (ha : a + 96 ≤ scrBytes) {dat : Addr} {len : Nat}
    (h0 : t.gpr .a0 = scA s a) (h2 : t.gpr .a2 = dat) (h3 : (t.gpr .a3).toNat = len)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)) (hd : Region.Disjoint ⟨dat, len⟩ (scR s a 96))
    (hdl : (below (fb s) sha256.F).Disjoint ⟨dat, len⟩) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w → After t ([scR s a 96] ++ [below t.sp sha256.F]) w →
      (∀ m, hH.SH.Repr t.mem (scA s a) m → t.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr w.mem (scA s a) (m ++ Spec.Sha256.bytesAt t.mem dat len)) → Q w) :
    WP isa sha256.callUpd t Q := by
  have hc := scCov h hp.wr ha
  refine hH.callUpd_ok h0 h2 h3 hd (by rw [hp.sp]; exact fb_al h) (by rw [hp.sp]; exact fb_ge h (by decide))
    (by rw [hp.sp]; exact lowSc h (by decide) ha) (by rw [hp.sp]; exact hdl)
    (Covers.append_left hdc (Covers.right hc)) hc fun w hrd hwr hsp hf hg hr => ?_
  have A : After t ([scR s a 96] ++ [below t.sp sha256.F]) w := ⟨hrd, hwr, hsp, hg, hf⟩
  exact hQ w (hp.after_sc h (ws := [(a, 96)]) (X := sha256.F) (by decide)
    (by simp only [List.mem_singleton]; rintro _ rfl; exact ha) A) A hr

/-- `finalize` of the state at `scratch + a`, into `scratch + o`. -/
theorem shaFin_ok {t : State} (hp : Post s R EM t) {a o : Nat} (ha : a + 96 ≤ scrBytes) (ho : o + 32 ≤ scrBytes)
    (hao : a + 96 ≤ o ∨ o + 32 ≤ a) (h0 : t.gpr .a0 = scA s a) (h2 : t.gpr .a2 = scA s o) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w → After t ([scR s a 96, scR s o 32] ++ [below t.sp sha256.F]) w →
      (∀ m, hH.SH.Repr t.mem (scA s a) m → m.length < 2 ^ 64 → t.gpr .a1 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt w.mem (scA s o) 32 = hH.SH.H.hash m) → Q w) :
    WP isa sha256.callFin t Q := by
  have hc := scCov h hp.wr ha
  have hc' := scCov h hp.wr ho
  refine hH.callFin_ok h0 h2 (scDisj (s := s) hao ha ho) (by rw [hp.sp]; exact fb_al h)
    (by rw [hp.sp]; exact fb_ge h (by decide)) (by rw [hp.sp]; exact lowSc h (by decide) ha)
    (by rw [hp.sp]; exact lowSc h (by decide) ho) (Covers.right (Covers.pair hc hc')) (Covers.pair hc hc')
    fun w hrd hwr hsp hf hg hr => ?_
  have A : After t ([scR s a 96, scR s o 32] ++ [below t.sp sha256.F]) w := ⟨hrd, hwr, hsp, hg, hf⟩
  exact hQ w (hp.after_sc h (ws := [(a, 96), (o, 32)]) (X := sha256.F) (by decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> assumption) A) A hr

/-! ## HMAC-SHA-256 -/

omit h in
theorem hi_sdepth : sdepth sha256.init ≤ sha256.ibytes + sha256.F := by
  have := hH.initSd; have := hH.updSd; have := hH.finSd
  simp only [Hash.init, Hash.initMain, Hash.longKey, Hash.padKey, Hash.updBlock, Hash.callInit, Hash.callUpd,
    Hash.callFin, Hash.keyLoop, Hash.padLoop, sdepth, Instr.frameBytes]
  omega

omit h in
theorem hf_sdepth : sdepth sha256.finalize ≤ sha256.fbytes + sha256.F := by
  have := hH.updSd; have := hH.finSd
  simp only [Hash.finalize, Hash.finalizeMain, Hash.callUpd, Hash.callFin, sdepth, Instr.frameBytes]
  omega

/-- HMAC's `init` of the inner state at `scratch + i` and the outer one at
`scratch + u`, with the 32-byte key at `scratch + k`. -/
theorem macInit_ok {t : State} (hp : Post s R EM t) {i u k : Nat} (hi : i + 96 ≤ scrBytes)
    (hu : u + 96 ≤ scrBytes) (hk : k + 32 ≤ scrBytes) (hiu : i + 96 ≤ u ∨ u + 96 ≤ i)
    (hki : k + 32 ≤ i ∨ i + 96 ≤ k) (hku : k + 32 ≤ u ∨ u + 96 ≤ k)
    (h0 : t.gpr .a0 = scA s i) (h1 : t.gpr .a1 = scA s u) (h2 : t.gpr .a2 = scA s k)
    (h3 : t.gpr .a3 = BitVec.ofNat 64 32) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w →
      After t ([scR s i 96, scR s u 96] ++ [below t.sp (sha256.ibytes + sha256.F)]) w →
      hH.SH.Repr w.mem (scA s i) (xorPad (blockKey hH.SH.H (Spec.Sha256.bytesAt t.mem (scA s k) 32)) ipad) →
      hH.SH.Repr w.mem (scA s u) (xorPad (blockKey hH.SH.H (Spec.Sha256.bytesAt t.mem (scA s k) 32)) opad) →
      Q w) :
    WP isa macInitCall t Q := by
  have hl := VG.Proof.Hmac.Stream.RISCV64.HashOK.lay hH
  have zz := hmac_sizes
  have ci := scCov h hp.wr hi
  have cu := scCov h hp.wr hu
  have ck := scCov h hp.wr hk
  have c0 : t.callEntry.gpr .a0 = scA s i := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : t.callEntry.gpr .a1 = scA s u := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : t.callEntry.gpr .a2 = scA s k := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : (t.callEntry.gpr .a3).toNat = 32 := by rw [State.callEntry_gpr _ (by decide), h3]; rfl
  have X : sha256.ibytes + sha256.F ≤ callX := zz.1
  refine WP.callAny (k := initG hH.SH (sha256.ibytes + sha256.F))
    (fun _ hs => VG.Proof.Hmac.Stream.RISCV64.Init.correct hH hs) (rd := [scR s k 32])
    (wr := [scR s i 96, scR s u 96]) ?_ (Covers.append_left (Covers.right ck) (Covers.right (Covers.pair ci cu)))
    (Covers.pair ci cu) ?_ (Nat.lt_of_le_of_lt hi_sdepth (Nat.lt_of_le_of_lt X (by decide)))
  · simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, hp.sp]
    exact ⟨trivial, rfl, scDisj (s := s) hiu hi hu, scDisj (s := s) hki hk hi, scDisj (s := s) hku hk hu, fb_al h, fb_ge h X,
      lowSc h X hi, lowSc h X hu, lowSc h X hk⟩
  · intro w hrd hwr hsp hf hcs hpost
    simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
      at hpost
    have A : After t ([scR s i 96, scR s u 96] ++ [below t.sp (sha256.ibytes + sha256.F)]) w :=
      ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hi_sdepth (Nat.lt_of_le_of_lt X (by decide))⟩
    exact hQ w (hp.after_sc h (ws := [(i, 96), (u, 96)]) X
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> assumption) A)
      A hpost.1 hpost.2

/-- HMAC's `finalize` of the inner state at `scratch + i` and the outer one at
`scratch + u`, with the count in `a2`, into `scratch + o`. -/
theorem macFin_ok {t : State} (hp : Post s R EM t) {i u o : Nat} (hi : i + 96 ≤ scrBytes)
    (hu : u + 96 ≤ scrBytes) (ho : o + 32 ≤ scrBytes) (hiu : i + 96 ≤ u ∨ u + 96 ≤ i)
    (hio : i + 96 ≤ o ∨ o + 32 ≤ i) (huo : u + 96 ≤ o ∨ o + 32 ≤ u)
    (h0 : t.gpr .a0 = scA s i) (h1 : t.gpr .a1 = scA s u) (h3 : t.gpr .a3 = scA s o) {Q : State → Prop}
    (hQ : ∀ w, Post s R EM w →
      After t ([scR s i 96, scR s o 32] ++ [below t.sp (sha256.fbytes + sha256.F)]) w →
      (∀ k0 text, k0.length = 64 → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr t.mem (scA s i) (xorPad k0 ipad ++ text) →
        t.gpr .a2 = BitVec.ofNat 64 (64 + text.length) →
        hH.SH.Repr t.mem (scA s u) (xorPad k0 opad) →
        Spec.Sha256.bytesAt w.mem (scA s o) 32 = hmacBlockKey hH.SH.H k0 text) → Q w) :
    WP isa macFinCall t Q := by
  have zz := hmac_sizes
  have ci := scCov h hp.wr hi
  have cu := scCov h hp.wr hu
  have co := scCov h hp.wr ho
  have c0 : t.callEntry.gpr .a0 = scA s i := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : t.callEntry.gpr .a1 = scA s u := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : t.callEntry.gpr .a2 = t.gpr .a2 := State.callEntry_gpr _ (by decide)
  have c3 : t.callEntry.gpr .a3 = scA s o := (State.callEntry_gpr _ (by decide)).trans h3
  have X : sha256.fbytes + sha256.F ≤ callX := zz.2.1
  refine WP.callAny (k := finG hH.SH (sha256.fbytes + sha256.F))
    (fun _ hs => VG.Proof.Hmac.Stream.RISCV64.Finalize.correct hH hs) (rd := [scR s u 96])
    (wr := [scR s i 96, scR s o 32]) ?_ (Covers.append_left (Covers.right cu) (Covers.right (Covers.pair ci co)))
    (Covers.pair ci co) ?_ (Nat.lt_of_le_of_lt hf_sdepth (Nat.lt_of_le_of_lt X (by decide)))
  · simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c3, hp.sp]
    exact ⟨rfl, rfl, scDisj (s := s) hiu hi hu, scDisj (s := s) hio hi ho, scDisj (s := s) huo hu ho, fb_al h, fb_ge h X,
      lowSc h X hi, lowSc h X hu, lowSc h X ho⟩
  · intro w hrd hwr hsp hf hcs hpost
    simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
      at hpost
    have A : After t ([scR s i 96, scR s o 32] ++ [below t.sp (sha256.fbytes + sha256.F)]) w :=
      ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hf_sdepth (Nat.lt_of_le_of_lt X (by decide))⟩
    exact hQ w (hp.after_sc h (ws := [(i, 96), (o, 32)]) X
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> assumption) A)
      A hpost

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
