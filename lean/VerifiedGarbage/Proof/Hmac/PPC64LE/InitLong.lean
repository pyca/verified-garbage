module

public import VerifiedGarbage.Proof.Hmac.PPC64LE.Init
meta import VerifiedGarbage.Proof.Hmac.PPC64LE.Init
public import VerifiedGarbage.Proof.Hmac.PPC64LE.Finalize
meta import VerifiedGarbage.Proof.Hmac.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# HMAC-SHA-256 on PPC64LE: `init` for a key longer than a block

Untrusted: everything here is checked by Lean. `initLong` hashes the key
into its scratch space with three calls, each used as a black box through
its proof (`WP.callF`), inside the frame saving the link register
(`WP.frameReg`): `vg_sha256_update_scratch` absorbs the key into a state
holding `H⁽⁰⁾`, `vg_sha256_finalize_scratch` writes its digest, and
`vg_hmac_sha256_init_scratch` (`init`) sets up the HMAC states from the
digest, whose `blockKey` is the key's (`blockKey_digest`). The caller's
`r20`–`r24` are saved in `scratch[288..328)`, which no call writes.
-/

@[expose] public section

namespace VG.Proof.Hmac.PPC64LE.InitLong

open VG VG.PPC64LE VG.Impl.Hmac.PPC64LE
open VG.Impl.Sha256.PPC64LE.Stream (mov)
open VG.Proof.Hmac.PPC64LE
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.PPC64LE (contains_offset sub_offset toNat_ofNat_lt writeState stateAt_writeState)
open VG.Proof.Sha256.PPC64LE.Stream (Upd Mupd wp_mov wp_li wp_addi wp_std wp_ld frame_bytes
  write_frame_bytes readW_writeW_save frame_sub)
open VG.Proof.Sha256.PPC64LE.Stream.WP (cons)
open VG.Spec.Sha256 (bytesAt stateAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .r3
abbrev out : Addr := s₀.gpr .r4
abbrev kp : Addr := s₀.gpr .r5
abbrev kl : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev inR : Region := ⟨inn s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 96⟩
abbrev kR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 328⟩
/-- The SHA-256 state the key is hashed in. -/
abbrev st : Addr := scr s₀ + 160
abbrev stR : Region := ⟨st s₀, 96⟩
/-- Where its digest goes. -/
abbrev dg : Addr := scr s₀ + 256
abbrev dgR : Region := ⟨dg s₀, 32⟩
/-- The scratch space of the functions called. -/
abbrev cR : Region := ⟨scr s₀, 160⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (kp s₀) (kl s₀)

end

structure Pre (s₀ : State) : Prop where
  kl_gt : 64 < kl s₀
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  k_i : (kR s₀).Disjoint (inR s₀)
  k_o : (kR s₀).Disjoint (outR s₀)
  k_s : (kR s₀).Disjoint (scR s₀)

/-- The frame a call pushes, below the stack pointer `s` has, is disjoint from
the buffers. -/
structure Stack (s : State) : Prop where
  sp48 : 48 ≤ s.sp.toNat
  i : (below s.sp 48).Disjoint (inR s)
  o : (below s.sp 48).Disjoint (outR s)
  k : (below s.sp 48).Disjoint (kR s)
  s : (below s.sp 48).Disjoint (scR s)

/-- On entry: our frame and the callee's are in the 96 bytes below the stack
pointer, disjoint from the buffers. -/
structure Stack₀ (s₀ : State) : Prop where
  sp96 : 96 ≤ s₀.sp.toNat
  i : (below s₀.sp 96).Disjoint (inR s₀)
  o : (below s₀.sp 96).Disjoint (outR s₀)
  k : (below s₀.sp 96).Disjoint (kR s₀)
  s : (below s₀.sp 96).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.initLongSha256PPC64LE.pre s₀) : Pre s₀ ∧ Stack₀ s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13⟩⟩

theorem sub_st (s₀ : State) : Region.Sub (stR s₀) (scR s₀) := sub_offset (off := 160) (by omega) (by omega)
theorem sub_dg (s₀ : State) : Region.Sub (dgR s₀) (scR s₀) := sub_offset (off := 256) (by omega) (by omega)
theorem sub_c (s₀ : State) : Region.Sub (cR s₀) (scR s₀) := Region.sub_prefix (by omega)

theorem st_c (s₀ : State) : (stR s₀).Disjoint (cR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
theorem dg_c (s₀ : State) : (dgR s₀).Disjoint (cR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
theorem st_dg (s₀ : State) : (stR s₀).Disjoint (dgR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-! ## The key's digest -/

theorem hash_length (k : List Byte) : (Spec.Sha256.hash k).length = 32 := by
  simp [Spec.Sha256.hash, Spec.Sha256.finalHash, Spec.Sha256.wordBytes, List.length_flatMap, List.map_const']

/-- A key longer than a block and its digest make the same block key. -/
theorem blockKey_digest {k : List Byte} (hk : 64 < k.length) :
    blockKey sha256 (Spec.Sha256.hash k) = blockKey sha256 k := by
  have hl : (Spec.Sha256.hash k).length = 32 := hash_length k
  simp only [blockKey, sha256, hl, show ¬ (64 < 32) by decide, ite_false, hk, ite_true]

/-! ## The calls -/

theorem upd_exec : ∀ s, Proof.Sha256.updatePPC64LE.pre s → ∃ t s',
    Exec isa Impl.Sha256.PPC64LE.Stream.update s t s' ∧ abiPreserved s s' ∧
      Proof.Sha256.updatePPC64LE.post s s' := by
  intro s hs
  have h := Proof.Sha256.PPC64LE.Stream.Update.pre_of hs
  exact Proof.Sha256.PPC64LE.Stream.Update.correct h.1 h.2

theorem hi_exec : ∀ s, Proof.Hmac.initSha256PPC64LE.pre s → ∃ t s',
    Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Hmac.initSha256PPC64LE.post s s' := by
  intro s hs
  have h := Init.pre_of hs
  exact Init.correct h.1 h.2

theorem upd_fdepth : Impl.Sha256.PPC64LE.Stream.update.fdepth = 1 := by decide +kernel
theorem hi_fdepth : init.fdepth = 1 := by decide +kernel

/-- The call of `vg_sha256_update_scratch`: the key into the state at `st`. -/
theorem upd_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h3 : s.gpr .r3 = st s₀) (h4 : s.gpr .r4 = 0) (h5 : s.gpr .r5 = kp s₀) (h6 : s.gpr .r6 = s₀.gpr .r6)
    (h7 : s.gpr .r7 = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([stR s₀, cR s₀] ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (Spec.Sha256.ReprFrom H0 s.mem (st s₀) [] →
        Repr s'.mem (st s₀) (bytesAt s.mem (kp s₀) (kl s₀))) → Q s') :
    WP isa sha256Update s Q := by
  have c3 : s.callEntry.gpr .r3 = st s₀ := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = 0 := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : s.callEntry.gpr .r5 = kp s₀ := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : s.callEntry.gpr .r6 = s₀.gpr .r6 := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : s.callEntry.gpr .r7 = scr s₀ := (State.callEntry_gpr _ (by decide)).trans h7
  refine WP.callF (k := Proof.Sha256.updatePPC64LE) upd_exec (rd := [kR s₀]) (wr := [stR s₀, cR s₀])
    ?_ ?_ ?_ ?_ (by rw [upd_fdepth]; decide)
  · simp only [Proof.Sha256.updatePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c3, c5, c6, c7, hsp]
    exact ⟨trivial, trivial, st_c s₀, hp.k_s.sub_right (sub_st s₀), hp.k_s.sub_right (sub_c s₀), hs.sp48,
      hs.s.sub_right (sub_st s₀), hs.k, hs.s.sub_right (sub_c s₀)⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 160, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR s₀, by simp, 160, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [Proof.Sha256.updatePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5, c6] at hpost
    rw [upd_fdepth, hsp] at h₄
    exact hQ s' h₁ h₂ h₃ h₄ hcs fun hr => by simpa [Spec.Sha256.Repr] using hpost H0 [] hr rfl

/-- The call of `vg_sha256_finalize_scratch`: the digest of the state at `st`
into `dg`. -/
theorem fin_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h3 : s.gpr .r3 = st s₀) (h4 : s.gpr .r4 = s₀.gpr .r6) (h5 : s.gpr .r5 = dg s₀)
    (h6 : s.gpr .r6 = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([stR s₀, dgR s₀, cR s₀] ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, Repr s.mem (st s₀) m → s₀.gpr .r6 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (dg s₀) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa sha256Finalize s Q := by
  have c3 : s.callEntry.gpr .r3 = st s₀ := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = s₀.gpr .r6 := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : s.callEntry.gpr .r5 = dg s₀ := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : s.callEntry.gpr .r6 = scr s₀ := (State.callEntry_gpr _ (by decide)).trans h6
  refine WP.callF (k := Proof.Sha256.finalizePPC64LE) Finalize.fin_exec (rd := [])
    (wr := [stR s₀, dgR s₀, cR s₀]) ?_ ?_ ?_ ?_ (by rw [Finalize.fin_fdepth]; decide)
  · simp only [Proof.Sha256.finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c3, c5, c6, hsp]
    exact ⟨trivial, trivial, st_dg s₀, st_c s₀, dg_c s₀, hs.sp48, hs.s.sub_right (sub_st s₀),
      hs.s.sub_right (sub_dg s₀), hs.s.sub_right (sub_c s₀)⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s₀, by simp, 160, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 256, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s₀, by simp, 160, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 256, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [Proof.Sha256.finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5] at hpost
    rw [Finalize.fin_fdepth, hsp] at h₄
    exact hQ s' h₁ h₂ h₃ h₄ hcs fun m hr hc => hpost H0 m hr hc

/-- The call of `vg_hmac_sha256_init_scratch` with the 32-byte digest at `dg`
as its key. -/
theorem hi_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h3 : s.gpr .r3 = inn s₀) (h4 : s.gpr .r4 = out s₀) (h5 : s.gpr .r5 = dg s₀)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 32) (h7 : s.gpr .r7 = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([inR s₀, outR s₀, cR s₀] ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (Repr s'.mem (inn s₀) (xorPad (blockKey sha256 (bytesAt s.mem (dg s₀) 32)) ipad) ∧
        Repr s'.mem (out s₀) (xorPad (blockKey sha256 (bytesAt s.mem (dg s₀) 32)) opad)) → Q s') :
    WP isa hmacInitScratch s Q := by
  have c3 : s.callEntry.gpr .r3 = inn s₀ := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = out s₀ := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : s.callEntry.gpr .r5 = dg s₀ := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : s.callEntry.gpr .r6 = BitVec.ofNat 64 32 := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : s.callEntry.gpr .r7 = scr s₀ := (State.callEntry_gpr _ (by decide)).trans h7
  have e32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  refine WP.callF (k := Proof.Hmac.initSha256PPC64LE) hi_exec (rd := [dgR s₀])
    (wr := [inR s₀, outR s₀, cR s₀]) ?_ ?_ ?_ ?_ (by rw [hi_fdepth]; decide)
  · simp only [Proof.Hmac.initSha256PPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c3, c4, c5, c6, c7, hsp, e32]
    exact ⟨by decide, trivial, trivial, hp.i_o, hp.i_s.sub_right (sub_c s₀), hp.o_s.sub_right (sub_c s₀),
      (hp.i_s.sub_right (sub_dg s₀)).symm, (hp.o_s.sub_right (sub_dg s₀)).symm, dg_c s₀, hs.sp48, hs.i,
      hs.o, hs.s.sub_right (sub_dg s₀), hs.s.sub_right (sub_c s₀)⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨scR s₀, by simp, 256, rfl, by simp⟩
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [Proof.Hmac.initSha256PPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5, c6, e32] at hpost
    rw [hi_fdepth, hsp] at h₄
    exact hQ s' h₁ h₂ h₃ h₄ hcs hpost

/-! ## The prologue: saving `r20`–`r24`, and `H⁽⁰⁾` into the state -/

/-- The memory after saving our caller's `r20`–`r24` in `scratch[288..328)`. -/
abbrev svMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (scr s₀ + BitVec.ofNat 64 288) (s₀.gpr .r20)).writeW (scr s₀ + BitVec.ofNat 64 296)
    (s₀.gpr .r21)).writeW (scr s₀ + BitVec.ofNat 64 304) (s₀.gpr .r22)).writeW
    (scr s₀ + BitVec.ofNat 64 312) (s₀.gpr .r23)).writeW (scr s₀ + BitVec.ofNat 64 320) (s₀.gpr .r24)

/-- The registers `initLong` keeps its variables in. -/
abbrev vars : List Reg := [.r20, .r21, .r22, .r23, .r24]

/-- After the prologue: our caller's `r20`–`r24` are saved, the state at `st`
holds `H⁽⁰⁾`, and the arguments of `vg_sha256_update_scratch` are set. -/
structure Saved (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = 0
  r5 : s.gpr .r5 = kp s₀
  r6 : s.gpr .r6 = s₀.gpr .r6
  r7 : s.gpr .r7 = scr s₀
  r20 : s.gpr .r20 = st s₀
  r21 : s.gpr .r21 = scr s₀
  r22 : s.gpr .r22 = inn s₀
  r23 : s.gpr .r23 = out s₀
  r24 : s.gpr .r24 = s₀.gpr .r6
  cs : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  mem : s.mem = writeState (svMem s₀) (st s₀) H0

theorem svMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (svMem s₀) :=
  (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))

/-- Everything the prologue writes is in the scratch space. -/
theorem Saved.frame {s₀ s : State} (h : Saved s₀ s) : Frame [scR s₀] s₀.mem s.mem := by
  rw [h.mem]
  refine (svMem_frame s₀).trans (Frame.sub (Init.writeState_frame _ _ _) ?_)
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scR s₀, by simp, fun a h => sub_st s₀ a (Region.sub_prefix (by omega) a h)⟩

theorem Saved.key {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) :
    bytesAt s.mem (kp s₀) (kl s₀) = K s₀ :=
  Proof.Sha256.Stream.bytesAt_congr fun i hi =>
    frame_bytes h.frame (R := kR s₀) (by simpa using hp.k_s) (Nat.le_of_lt (s₀.gpr .r6).isLt) hi

theorem Saved.repr {s₀ s : State} (h : Saved s₀ s) : Spec.Sha256.ReprFrom H0 s.mem (st s₀) [] := by
  rw [h.mem]
  exact Proof.Sha256.Stream.repr_nil (stateAt_writeState _ _ _)

theorem not_pres {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 :=
  (by decide : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8) r hr

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (([.store .d .r20 .r7 288, .store .d .r21 .r7 296, .store .d .r22 .r7 304,
        .store .d .r23 .r7 312, .store .d .r24 .r7 320,
        mov .r21 .r7, mov .r22 .r3, mov .r23 .r4, mov .r24 .r6, .addi .r20 .r7 160] : List Instr) ++
        h0 .r20 ++ ([mov .r3 .r20, .li .r4 0, mov .r7 .r21] : List Instr))) s₀ (Saved s₀) := by
  have hw : ∀ o, o + 8 ≤ 328 → InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 o) 8 := fun o h =>
    ⟨scR s₀, by simp [hp.wr], contains_offset h (by omega)⟩
  simp only [List.cons_append, List.nil_append]
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 288) (by decide) ⟨by omega, by omega⟩ rfl (hw 288 (by omega))
    fun sa ua => ?_
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 296) (by decide) ⟨by omega, by omega⟩ (by rw [ua.gpr])
    (by rw [ua.wr]; exact hw 296 (by omega)) fun sb ub => ?_
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 304) (by decide) ⟨by omega, by omega⟩ (by rw [ub.gpr, ua.gpr])
    (by rw [ub.wr, ua.wr]; exact hw 304 (by omega)) fun sc uc => ?_
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 312) (by decide) ⟨by omega, by omega⟩
    (by rw [uc.gpr, ub.gpr, ua.gpr]) (by rw [uc.wr, ub.wr, ua.wr]; exact hw 312 (by omega)) fun sd ud => ?_
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 320) (by decide) ⟨by omega, by omega⟩
    (by rw [ud.gpr, uc.gpr, ub.gpr, ua.gpr]) (by rw [ud.wr, uc.wr, ub.wr, ua.wr]; exact hw 320 (by omega))
    fun se ue => ?_
  have g : se.gpr = s₀.gpr := by rw [ue.gpr, ud.gpr, uc.gpr, ub.gpr, ua.gpr]
  have me : se.mem = svMem s₀ := by
    simp only [ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, ud.gpr, uc.gpr, ub.gpr, ua.gpr]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addi (imm := 160) (by decide) (by omega) fun s₅ u₅ => ?_
  have k₅ : ∀ r, r ∉ vars → s₅.gpr r = s₀.gpr r := fun r hr => by
    simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.1, u₄.other _ hr.2.2.2.2, u₃.other _ hr.2.2.2.1, u₂.other _ hr.2.2.1,
      u₁.other _ hr.2.1, g]
  have e26 : s₅.gpr .r20 = st s₀ := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g]; rfl
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr]
  refine Init.h0_ok (b := .r20) (by decide) (by decide) (fun k hk => ?_) fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => ?_
  · rw [wr₅, e26, show st s₀ + BitVec.ofNat 64 (4 * k) = scr s₀ + BitVec.ofNat 64 (160 + 4 * k) by
      rw [show st s₀ = scr s₀ + BitVec.ofNat 64 160 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  refine wp_mov fun s₇ u₇ => wp_li (imm := 0) (by decide) fun s₈ u₈ => wp_mov fun s₉ u₉ => WP.block_nil ?_
  have k₆ : ∀ r, r ≠ .r8 → s₆.gpr r = s₅.gpr r := g₆
  have k₉ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → r ≠ .r8 → s₉.gpr r = s₅.gpr r := fun r a b c d => by
    rw [u₉.other _ c, u₈.other _ b, u₇.other _ a, k₆ _ d]
  have e27 : s₅.gpr .r21 = scr s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, g]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hv => ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅]
  · rw [u₉.sp, u₈.sp, u₇.sp, sp₆, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, k₆ _ (by decide), e26]
  · rw [u₉.other _ (by decide), u₈.gpr]; rfl
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), k₅ _ (by decide)]
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), k₅ _ (by decide)]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), k₆ _ (by decide), e27]
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), e26]
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), e27]
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g]
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [k₉ _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g]
  · have := not_pres hr
    rw [k₉ _ this.1 this.2.1 this.2.2.2.2.1 this.2.2.2.2.2, k₅ _ hv]
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆, e26, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, me]

/-! ## What the calls keep -/

/-- The bytes of `scratch` holding our caller's registers. -/
abbrev Kept (o : Nat) : Prop := 288 ≤ o ∧ o < 328

/-- A byte `Kept` survives a call writing the regions `ws` and its frame. -/
theorem kept {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {ws : List Region}
    (hws : ∀ r ∈ ws, r = inR s₀ ∨ r = outR s₀ ∨ r = stR s₀ ∨ r = dgR s₀ ∨ r = cR s₀) {m m' : Mem}
    (hf : Frame (ws ++ [below s₀.sp 48]) m m') {o : Nat} (ho : Kept o) :
    m' (scr s₀ + BitVec.ofNat 64 o) = m (scr s₀ + BitVec.ofNat 64 o) := by
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ (scR s₀) := sub_offset (by omega) (by omega)
  have ht : (BitVec.ofNat 64 o).toNat = o := toNat_ofNat_lt (by omega)
  have := frame_bytes hf (R := ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩) (fun r hr => ?_) Nat.one_le_two_pow
    (i := 0) Nat.one_pos
  · simpa using this
  rcases List.mem_append.mp hr with hr | hr
  · rcases hws r hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.i_s.symm.sub_left hsub
    · exact hp.o_s.symm.sub_left hsub
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · simp only [List.mem_singleton] at hr; subst hr
    exact hs.s.symm.sub_left hsub

/-- A saved register survives the calls. -/
theorem sv_kept {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {m₁ m₂ m₃ m₄ : Mem}
    (f₂ : Frame ([stR s₀, cR s₀] ++ [below s₀.sp 48]) m₁ m₂)
    (f₃ : Frame ([stR s₀, dgR s₀, cR s₀] ++ [below s₀.sp 48]) m₂ m₃)
    (f₄ : Frame ([inR s₀, outR s₀, cR s₀] ++ [below s₀.sp 48]) m₃ m₄) {o : Nat}
    (ho : 288 ≤ o ∧ o + 8 ≤ 328) :
    m₄.readW (scr s₀ + BitVec.ofNat 64 o) 64 = m₁.readW (scr s₀ + BitVec.ofNat 64 o) 64 := by
  simp only [Mem.readW]
  refine congrArg _ (Mem.read_congr fun i hi => ?_)
  have e : scr s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i = scr s₀ + BitVec.ofNat 64 (o + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hi' : i < 8 := hi
  rw [e, kept hp hs (by simp) f₄ (by omega), kept hp hs (by simp) f₃ (by omega),
    kept hp hs (by simp) f₂ (by omega)]

/-- The saved registers, read back from the prologue's memory. -/
theorem svMem_read {s₀ : State} {s : State} (h : Saved s₀ s) {o : Nat} {r : Reg}
    (hr : (o, r) ∈ [(288, Reg.r20), (296, .r21), (304, .r22), (312, .r23), (320, .r24)]) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 = s₀.gpr r := by
  have hs : s.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 = (svMem s₀).readW (scr s₀ + BitVec.ofNat 64 o) 64 := by
    rw [h.mem]
    refine (Init.writeState_frame _ _ _).readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton]; rintro r' rfl
    have ho : 288 ≤ o ∧ o ≤ 320 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
    have ht : (BitVec.ofNat 64 o).toNat = o := toNat_ofNat_lt (by omega)
    intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  rw [hs]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [svMem, readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [svMem, readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [svMem, readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [svMem, readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [svMem, Mem.readW_writeW_self64]

/-! ## Correctness -/

/-- `initLong` without its frame. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa initLongMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Hmac.initLongSha256PPC64LE.post s₀ s' := by
  unfold initLongMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  -- The key into the state.
  refine WP.seq (upd_ok hp hs h₁.rd h₁.wr h₁.sp h₁.r3 h₁.r4 h₁.r5 h₁.r6 h₁.r7
    fun s₂ rd₂ wr₂ sp₂ fr₂ cs₂ post₂ => ?_)
  have v₂ : ∀ r ∈ vars, s₂.gpr r = s₁.gpr r := fun r hr => cs₂ r (by revert r hr; decide)
  refine WP.seq (wp_mov fun sa ua => wp_mov fun sb ub => wp_addi (imm := 256) (by decide) (by omega)
    fun sc uc => wp_mov fun sd ud => WP.block_nil ?_)
  have gd : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → sd.gpr r = s₂.gpr r := fun r a b c d => by
    rw [ud.other _ d, uc.other _ c, ub.other _ b, ua.other _ a]
  have md : sd.mem = s₂.mem := by rw [ud.mem, uc.mem, ub.mem, ua.mem]
  have r27d : sd.gpr .r21 = scr s₀ := by
    rw [gd _ (by decide) (by decide) (by decide) (by decide), v₂ _ (by decide), h₁.r21]
  -- Its digest.
  refine WP.seq (fin_ok hp hs (s := sd) (by rw [ud.rd, uc.rd, ub.rd, ua.rd, rd₂, h₁.rd])
    (by rw [ud.wr, uc.wr, ub.wr, ua.wr, wr₂, h₁.wr]) (by rw [ud.sp, uc.sp, ub.sp, ua.sp, sp₂, h₁.sp])
    (by rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      v₂ _ (by decide), h₁.r20])
    (by rw [ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide),
      v₂ _ (by decide), h₁.r24])
    (by rw [ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide),
      v₂ _ (by decide), h₁.r21]; rfl)
    (by rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide),
      v₂ _ (by decide), h₁.r21])
    fun s₃ rd₃ wr₃ sp₃ fr₃ cs₃ post₃ => ?_)
  have v₃ : ∀ r ∈ vars, s₃.gpr r = s₁.gpr r := fun r hr => by
    rw [cs₃ r (by revert r hr; decide), gd r (by revert r hr; decide) (by revert r hr; decide)
      (by revert r hr; decide) (by revert r hr; decide), v₂ r hr]
  refine WP.seq (wp_mov fun se ue => wp_mov fun sf uf => wp_addi (imm := 256) (by decide) (by omega)
    fun sg ug => wp_li (imm := 32) (by omega) fun sh uh => wp_mov fun si ui => WP.block_nil ?_)
  have mi : si.mem = s₃.mem := by rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem]
  have gi : ∀ r ∈ vars, si.gpr r = s₁.gpr r := fun r hr => by
    have h := (by decide : ∀ r ∈ vars, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7) r hr
    rw [ui.other _ h.2.2.2.2, uh.other _ h.2.2.2.1, ug.other _ h.2.2.1, uf.other _ h.2.1,
      ue.other _ h.1, v₃ r hr]
  -- The HMAC states from the digest.
  refine WP.seq (hi_ok hp hs (s := si) (by rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, rd₃, ud.rd, uc.rd,
      ub.rd, ua.rd, rd₂, h₁.rd])
    (by rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, wr₃, ud.wr, uc.wr, ub.wr, ua.wr, wr₂, h₁.wr])
    (by rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, sp₃, ud.sp, uc.sp, ub.sp, ua.sp, sp₂, h₁.sp])
    (by rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.gpr, v₃ _ (by decide), h₁.r22])
    (by rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr,
      ue.other _ (by decide), v₃ _ (by decide), h₁.r23])
    (by rw [ui.other _ (by decide), uh.other _ (by decide), ug.gpr, uf.other _ (by decide),
      ue.other _ (by decide), v₃ _ (by decide), h₁.r21]; rfl)
    (by rw [ui.other _ (by decide), uh.gpr])
    (by rw [ui.gpr, uh.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), v₃ _ (by decide), h₁.r21])
    fun s₄ rd₄ wr₄ sp₄ fr₄ cs₄ post₄ => ?_)
  -- Restoring `r20`–`r24`.
  have r27₄ : s₄.gpr .r21 = scr s₀ := by rw [cs₄ _ (by decide), gi _ (by decide), h₁.r21]
  have hin : ∀ o, o + 8 ≤ 328 → InRegions (s₄.rd ++ s₄.wr) (scr s₀ + BitVec.ofNat 64 o) 8 := fun o h =>
    ⟨scR s₀, by simp [wr₄, ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, wr₃, ud.wr, uc.wr, ub.wr, ua.wr, wr₂, h₁.wr,
      hp.wr], contains_offset h (by omega)⟩
  have sv : ∀ o r, (o, r) ∈ [(288, Reg.r20), (296, .r21), (304, .r22), (312, .r23), (320, .r24)] →
      s₄.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 = s₀.gpr r := fun o r hr => by
    have ho : 288 ≤ o ∧ o + 8 ≤ 328 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
    rw [sv_kept hp hs fr₂ (by rw [md] at fr₃; exact fr₃) (by rw [mi] at fr₄; exact fr₄) ho,
      svMem_read h₁ hr]
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 288) (by decide) ⟨by omega, by omega⟩ (by rw [r27₄])
    (hin 288 (by omega)) fun s₅ u₅ => ?_
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 304) (by decide) ⟨by omega, by omega⟩
    (by rw [u₅.other _ (by decide), r27₄]) (by rw [u₅.rd, u₅.wr]; exact hin 304 (by omega)) fun s₆ u₆ => ?_
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 312) (by decide) ⟨by omega, by omega⟩
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), r27₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr]; exact hin 312 (by omega)) fun s₇ u₇ => ?_
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 320) (by decide) ⟨by omega, by omega⟩
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), r27₄])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr]; exact hin 320 (by omega)) fun s₈ u₈ => ?_
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 296) (by decide) ⟨by omega, by omega⟩
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      r27₄])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr]; exact hin 296 (by omega))
    fun s₉ u₉ => WP.block_nil ⟨fun r hr => ?_, ?_, ?_⟩
  · have m₈ : s₈.mem = s₄.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem]
    by_cases h27 : r = .r21
    · subst h27; rw [u₉.gpr, m₈, sv 296 .r21 (by simp)]
    by_cases h30 : r = .r24
    · subst h30; rw [u₉.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, u₅.mem, sv 320 .r24 (by simp)]
    by_cases h29 : r = .r23
    · subst h29; rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem,
        sv 312 .r23 (by simp)]
    by_cases h28 : r = .r22
    · subst h28; rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        u₅.mem, sv 304 .r22 (by simp)]
    by_cases h26 : r = .r20
    · subst h26; rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, sv 288 .r20 (by simp)]
    have hv : r ∉ vars := by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h26, h27, h28, h29, h30⟩
    have hn := not_pres hr
    rw [u₉.other _ h27, u₈.other _ h30, u₇.other _ h29, u₆.other _ h28, u₅.other _ h26, cs₄ _ hr,
      ui.other _ hn.2.2.2.2.1, uh.other _ hn.2.2.2.1, ug.other _ hn.2.2.1, uf.other _ hn.2.1,
      ue.other _ hn.1, cs₃ _ hr, gd _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1, cs₂ _ hr, h₁.cs _ hr hv]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, sp₄, ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, sp₃, ud.sp, uc.sp,
      ub.sp, ua.sp, sp₂, h₁.sp]
  · -- The digest of the key, and its block key.
    have hk := h₁.key hp
    have hrepr := post₂ h₁.repr
    have hd := post₃ (bytesAt s₁.mem (kp s₀) (kl s₀)) (by rw [md]; exact hrepr)
      (by rw [Proof.Hmac.Common.bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    have hbk : blockKey sha256 (bytesAt si.mem (dg s₀) 32) = blockKey sha256 (K s₀) := by
      rw [mi, hd, hk, blockKey_digest (by rw [Proof.Hmac.Common.bytesAt_length]; exact hp.kl_gt)]
    rw [hbk] at post₄
    simp only [Proof.Hmac.initLongSha256PPC64LE]
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
    exact post₄

/-- The state `initLongMain` starts in: the link register moved to `r0`,
then pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack₀ s₀) :
    WP isa initLong s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.initLongSha256PPC64LE.post s₀ s' := by
  have hsp := hs.sp96
  have hb : Region.Sub (below (s₀.sp - 48) 48) (below s₀.sp 96) := below_body s₀.sp 48
  have hf : Region.Sub ⟨s₀.sp - 48, 48⟩ (below s₀.sp 96) := Finalize.sub48 s₀.sp
  have hsi : Stack (inner s₀) :=
    ⟨by show 48 ≤ (s₀.sp - 48).toNat; bv_omega, hs.i.sub_left hb, hs.o.sub_left hb, hs.k.sub_left hb,
      hs.s.sub_left hb⟩
  refine WP.seq (cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by show 48 ≤ s₀.sp.toNat; omega) (fun R hR => ?_)
    (WP.mono (correctMain (s₀ := inner s₀)
      ⟨hp.kl_gt, hp.rd, hp.wr, hp.i_o, hp.i_s, hp.o_s, hp.k_i, hp.k_o, hp.k_s⟩ hsi)
      fun s' ⟨hk, _, hpost⟩ => ?_)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hs.i.sub_left hf).sub_left (frame_sub _)
    · exact (hs.o.sub_left hf).sub_left (frame_sub _)
    · exact (hs.s.sub_left hf).sub_left (frame_sub _)
  · refine cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have e : bytesAt (inner s₀).mem (kp s₀) (kl s₀) = bytesAt s₀.mem (kp s₀) (kl s₀) :=
        Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          write_frame_bytes (R := kR s₀) (hs.k.sub_left hf) (s₀.gpr .r6).isLt hi
      simp only [Proof.Hmac.initLongSha256PPC64LE] at hpost ⊢
      rw [show (inner s₀).gpr .r5 = kp s₀ from rfl, show (inner s₀).gpr .r6 = s₀.gpr .r6 from rfl, e]
        at hpost
      exact hpost

/-! ## `Verified` -/

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Hmac.initLongSha256PPC64LE.pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x5000 | .r6 => 100 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x5000, 100⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x3000, 328⟩]

theorem initLong_verified : Verified PPC64LE.target initLong Proof.Hmac.initLongSha256PPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · refine ⟨sat, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Hmac.PPC64LE.InitLong
