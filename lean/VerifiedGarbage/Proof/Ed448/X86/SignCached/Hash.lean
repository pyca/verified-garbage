import VerifiedGarbage.Proof.Ed448.X86.SignCached.Layout
import VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.X86.Shake.Header
import VerifiedGarbage.Impl.Ed448.X86.SignCached

/-!
# Ed448 signing with a cached key on x86 (32-bit): the three hashes

`SHAKE256(seed, 114)` into the frame at `S` (`seed_ok`);
`H(dom4(0, C) ‖ prefix ‖ M)` (`nonce_ok`) and `H(dom4(0, C) ‖ R ‖ A ‖ M)`
(`chal_ok`) into the frame at `HASH`, from the header of `dom4` there, the
prefix in the frame at `K` and `R` in the first half of `out`. Each writes
only `Lo E`, the state and the sponge functions' working space, and its
output (`W`).
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed25519.X86.Whole (Value)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.Within Whole.FR)

variable {s t : State} {g : Reg → BitVec 32} {m : Mem}

/-- The frame's invariant, from any registers and memory on entry. -/
abbrev GCtx (s : State) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.X86.Whole.Ctx (base s) g m (scRd s) (scWr s) t

theorem scr_at (s : State) : ScrAt 8 (arg s) 7 (arg s 7) := ⟨by decide, rfl⟩

/-- What a hash into the frame at `d` writes. -/
abbrev W (s : State) (d : Nat) : List Region := Lo (base s) :: fr (base s) d 114 :: kWr (arg s 7)

theorem lift_abs {s : State} {d : Nat} {m m' : Mem} (h : Frame (Lo (base s) :: kWr (arg s 7)) m m') :
    Frame (W s d) m m' :=
  h.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

theorem lift_zero {s : State} {d : Nat} {m m' : Mem} (h : Frame [⟨(arg s 7).setWidth 64, 200⟩] m m') :
    Frame (W s d) m m' :=
  h.mono fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (kWr_state _))

theorem away_lo {E scr : BitVec 32} {D : Region} (hd : Away E scr D) : ∀ r ∈ Lo E :: kWr scr, D.Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hd.lo.symm
  · exact hd.kwr r hr

theorem away_state {E scr : BitVec 32} {D : Region} (hd : Away E scr D) :
    ∀ r ∈ [(⟨scr.setWidth 64, 200⟩ : Region)], D.Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact hd.kwr _ (kWr_state _)

section
variable (h : Facts s)
include h

/-- `SHAKE256(seed, 114)` into the frame at `S`. -/
theorem seed_ok (hc : GCtx s g m t) (ha : Args (base s) 8 (arg s) m) :
    WP isa seedHash t fun u => GCtx s g m u ∧ Frame (W s S) t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) 57) 114 := by
  have hk := kit h
  unfold seedHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (scr_at s) (src := .caller 1 0) (len := .const 57)
    (P := arg s 1) (N := 57) (show 1 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨SEED s, List.mem_append_left _ (seed_in s), whole _⟩) (hk.away_input (seed_in s) (whole _))
    h.seed (repr_nil hz)) fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  have e1 : Spec.Sha3.bytesAt t1.mem ((arg s 1).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) 57 :=
    hk.input_bytes hc1 (seed_in s) (whole (SEED s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [e1] at hr2
  refine WP.seq (WP.mono (hk.pad_step hc2 ha (scr_at s) hr2 (by rw [hp2, length_sbytes]))
    fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  refine WP.mono (hk.sqz_step hc3 ha (scr_at s) (d := S) (by decide) (by decide)) fun u ⟨hu, hf4, hb⟩ =>
    ⟨hu, (lift_zero hf1).trans ((lift_abs hf2).trans ((lift_abs hf3).trans hf4)), ?_⟩
  rw [hb, hs3, ← shake256_eq]

/-- `H(dom4(0, C) ‖ P ‖ M)`, the header at `HASH` and `P` at `K`, into the frame at `HASH`. -/
theorem nonce_ok (hc : GCtx s g m t) (ha : Args (base s) 8 (arg s) m)
    (hh : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 10 = hdrBytes (arg s 4))
    {P : List Byte} (hp : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 = P) :
    WP isa nonceHash t fun u => GCtx s g m u ∧ Frame (W s HASH) t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
          (P ++ Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
  have hk := kit h
  have fa := hk.fr_addr (d := HASH) (by decide)
  have fk := hk.fr_addr (d := K) (by decide)
  have aK : Away (base s) (arg s 7) (fr (base s) K 57) := hk.away_fr (by decide) (by decide)
  have aH : Away (base s) (arg s 7) (fr (base s) HASH 10) := hk.away_fr (by decide) (by decide)
  unfold nonceHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := (sframe_bytes hf1 (D := fr (base s) HASH 10) (away_state aH) (by show 10 ≤ 2 ^ 64; decide)).trans hh
  have hp1 := (sframe_bytes hf1 (D := fr (base s) K 57) (away_state aK) (by show 57 ≤ 2 ^ 64; decide)).trans hp
  -- The header.
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (scr_at s) (src := .frame HASH) (len := .const 10)
    (P := base s + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide))) (by rw [fa]; exact aH)
    (hk.fr_fit (by decide)) (repr_nil hz)) fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  rw [fa, hh1] at hr2
  have hp2' : t2.gpr .eax = BitVec.ofNat 32 ((hdrBytes (arg s 4)).length % 136) := by rw [hp2, hdr_len]
  have hpk2 := (sframe_bytes hf2 (D := fr (base s) K 57) (away_lo aK) (by show 57 ≤ 2 ^ 64; decide)).trans hp1
  -- The context.
  refine WP.seq (WP.mono (hk.next_abs hc2 ha (scr_at s) (src := .caller 3 0) (len := .caller 4 0)
    (P := arg s 3) (N := (arg s 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in s), whole _⟩) (hk.away_input (ctx_in s) (whole _)) h.ctx
    hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex : Spec.Sha3.bytesAt t2.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat :=
    hk.input_bytes hc2 (ctx_in s) (whole (CTX s)) (by show (arg s 4).toNat ≤ 2 ^ 64; have := (arg s 4).isLt; omega)
  rw [ex] at hr3 hp3
  have hpk3 := (sframe_bytes hf3 (D := fr (base s) K 57) (away_lo aK) (by show 57 ≤ 2 ^ 64; decide)).trans hpk2
  -- The prefix.
  refine WP.seq (WP.mono (hk.next_abs hc3 ha (scr_at s) (src := .frame K) (len := .const 57)
    (P := base s + BitVec.ofNat 32 K) (N := 57) trivial trivial rfl rfl
    (by rw [fk]; exact .inl (frame_within _ (by decide))) (by rw [fk]; exact aK)
    (hk.fr_fit (by decide)) hr3 hp3) fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  rw [fk, hpk3] at hr4 hp4
  -- The message.
  refine WP.seq (WP.mono (hk.next_abs hc4 ha (scr_at s) (src := .caller 5 0) (len := .caller 6 0)
    (P := arg s 5) (N := (arg s 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in s), whole _⟩) (hk.away_input (msg_in s) (whole _)) h.msg
    hr4 hp4) fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have em : Spec.Sha3.bytesAt t4.mem ((arg s 5).setWidth 64) (arg s 6).toNat =
      Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat :=
    hk.input_bytes hc4 (msg_in s) (whole (MSG s)) (by show (arg s 6).toNat ≤ 2 ^ 64; have := (arg s 6).isLt; omega)
  rw [em] at hr5 hp5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc5 ha (scr_at s) hr5 hp5) fun t6 ⟨hc6, hf6, hs6⟩ => ?_)
  refine WP.mono (hk.sqz_step hc6 ha (scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf7, hb⟩ =>
    ⟨hu, (lift_zero hf1).trans ((lift_abs hf2).trans ((lift_abs hf3).trans ((lift_abs hf4).trans
      ((lift_abs hf5).trans ((lift_abs hf6).trans hf7))))), ?_⟩
  rw [hb, hs6, ← shake256_eq, Spec.Ed448.hash, dom4_eq (arg s 4) _ _ (length_sbytes _ _ _)]
  simp only [List.append_assoc]

/-- `H(dom4(0, C) ‖ R ‖ A ‖ M)`, the header at `HASH` and `R` in the first
half of `out`, into the frame at `HASH`. -/
theorem chal_ok (hc : GCtx s g m t) (ha : Args (base s) 8 (arg s) m)
    (hh : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 10 = hdrBytes (arg s 4))
    {R : List Byte} (hR : Spec.Sha3.bytesAt t.mem ((arg s 0).setWidth 64) 57 = R) :
    WP isa chalHash t fun u => GCtx s g m u ∧ Frame (W s HASH) t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
          (R ++ Spec.Sha3.bytesAt m ((arg s 2).setWidth 64) 57 ++
            Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
  have hk := kit h
  have fa := hk.fr_addr (d := HASH) (by decide)
  have aR : Away (base s) (arg s 7) (OUT1 s) := hk.away_output (out_in s) h.oc (out1_within s)
  have aH : Away (base s) (arg s 7) (fr (base s) HASH 10) := hk.away_fr (by decide) (by decide)
  unfold chalHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := (sframe_bytes hf1 (D := fr (base s) HASH 10) (away_state aH) (by show 10 ≤ 2 ^ 64; decide)).trans hh
  have hR1 := (sframe_bytes hf1 (D := OUT1 s) (away_state aR) (by show 57 ≤ 2 ^ 64; decide)).trans hR
  -- The header.
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (scr_at s) (src := .frame HASH) (len := .const 10)
    (P := base s + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide))) (by rw [fa]; exact aH)
    (hk.fr_fit (by decide)) (repr_nil hz)) fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  rw [fa, hh1] at hr2
  have hp2' : t2.gpr .eax = BitVec.ofNat 32 ((hdrBytes (arg s 4)).length % 136) := by rw [hp2, hdr_len]
  have hR2 := (sframe_bytes hf2 (D := OUT1 s) (away_lo aR) (by show 57 ≤ 2 ^ 64; decide)).trans hR1
  -- The context.
  refine WP.seq (WP.mono (hk.next_abs hc2 ha (scr_at s) (src := .caller 3 0) (len := .caller 4 0)
    (P := arg s 3) (N := (arg s 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in s), whole _⟩) (hk.away_input (ctx_in s) (whole _)) h.ctx
    hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex : Spec.Sha3.bytesAt t2.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat :=
    hk.input_bytes hc2 (ctx_in s) (whole (CTX s)) (by show (arg s 4).toNat ≤ 2 ^ 64; have := (arg s 4).isLt; omega)
  rw [ex] at hr3 hp3
  have hR3 := (sframe_bytes hf3 (D := OUT1 s) (away_lo aR) (by show 57 ≤ 2 ^ 64; decide)).trans hR2
  -- `R`.
  refine WP.seq (WP.mono (hk.next_abs hc3 ha (scr_at s) (src := .caller 0 0) (len := .const 57)
    (P := arg s 0) (N := 57) (show 0 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_right _ (out_in s), out1_within s⟩) aR (by have := h.out; omega) hr3 hp3)
    fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  rw [hR3] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (hk.next_abs hc4 ha (scr_at s) (src := .caller 2 0) (len := .const 57)
    (P := arg s 2) (N := 57) (show 2 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (pk_in s), whole _⟩) (hk.away_input (pk_in s) (whole _)) h.pk
    hr4 hp4) fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have ep : Spec.Sha3.bytesAt t4.mem ((arg s 2).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 2).setWidth 64) 57 :=
    hk.input_bytes hc4 (pk_in s) (whole (PK s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (hk.next_abs hc5 ha (scr_at s) (src := .caller 5 0) (len := .caller 6 0)
    (P := arg s 5) (N := (arg s 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in s), whole _⟩) (hk.away_input (msg_in s) (whole _)) h.msg
    hr5 hp5) fun t6 ⟨hc6, hf6, hr6, hp6⟩ => ?_)
  have em : Spec.Sha3.bytesAt t5.mem ((arg s 5).setWidth 64) (arg s 6).toNat =
      Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat :=
    hk.input_bytes hc5 (msg_in s) (whole (MSG s)) (by show (arg s 6).toNat ≤ 2 ^ 64; have := (arg s 6).isLt; omega)
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (scr_at s) hr6 hp6) fun t7 ⟨hc7, hf7, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf8, hb⟩ =>
    ⟨hu, (lift_zero hf1).trans ((lift_abs hf2).trans ((lift_abs hf3).trans ((lift_abs hf4).trans
      ((lift_abs hf5).trans ((lift_abs hf6).trans ((lift_abs hf7).trans hf8)))))), ?_⟩
  rw [hb, hs7, ← shake256_eq, Spec.Ed448.hash, dom4_eq (arg s 4) _ _ (length_sbytes _ _ _)]
  simp only [List.append_assoc]

end

end VG.Proof.Ed448.X86.SignCached
