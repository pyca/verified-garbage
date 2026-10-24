module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.LoadCT
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.WitnessCT
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.RoundCT
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Loop
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.LoadCT
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.WitnessCT
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.RoundCT
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on PPC64LE: constant time

`draw_ct`: a draw's load, witness and round (`load_ct`, `witness_ct`,
`round_ct`), from the public data each takes (the octets read, the draw, the
witness: functions of the tape). `body_ct`: an iteration, whose check of the
octets left (`check_ok`) is a function of the witnesses so far. `loop_ct`:
the loop, whose runs exit together, since an iteration exits exactly when it
is the last one (`body_ok`). `millerRabin_ct`: the whole loop, from no
octets read.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot Frm word off wv writeW_outside word_writeW_self)
open VG.Spec.RsaKeyGen (Rand loop mrStep)
open VG.Proof.RsaKeyGen (mrSB wit seg)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)

/-- The loop's state after `a.2` witnesses, with `n + 1` iterations left. -/
def BS (n : Nat) (a : BD × Nat) (s : State) : Prop :=
  ∃ σ, LInv σ s a.1.B a.1.R a.1.L a.1.w a.1.c a.1.rl a.1.t a.1.b a.1.ch a.1.r a.2 n ∧ σ.sp = a.1.sp

/-- A draw's start. -/
def DS (a : BD × Nat) (s : State) : Prop :=
  (∃ n, BS n a s) ∧ 8 * (a.1.t + 1) * a.2 + 8 * (a.1.t + 1) ≤ a.1.rl

/-- After the load. -/
def D1 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, DS a s₀ ∧ (wv s.mem a.1.B (slot a.1.w 4) a.1.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem
      (a.1.R + BitVec.ofNat 64 (8 * (a.1.t + 1) * a.2)) (8 * (a.1.t + 1))) % 2 ^ (64 * a.1.t + a.1.b) ∧
    word s.mem a.1.B (8 * hUsed) = BitVec.ofNat 64 (8 * (a.1.t + 1) * a.2 + 8 * (a.1.t + 1)) ∧
    Frm a.1.B [(8 * hUsed, 8), (slot a.1.w 4, 8 * (a.1.w + 2))] s₀.mem s.mem ∧
    s.gpr .r10 = off a.1.B (slot a.1.w 0)) ∧ Keep loadRegs s₀ s

/-- After the witness. -/
def D2 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₁, D1 a s₁ ∧ (wv s.mem a.1.B (slot a.1.w 4) a.1.w =
      (wit a.1.c (8 * (a.1.t + 1)) a.1.r (0 + 8 * (a.1.t + 1) * a.2)).1 ∧
    word s.mem a.1.B (8 * hUni) = BitVec.ofNat 64 ((mrSB a.1.c (8 * (a.1.t + 1)) 0 a.1.r a.2).2 +
      if (wit a.1.c (8 * (a.1.t + 1)) a.1.r (0 + 8 * (a.1.t + 1) * a.2)).2 then 1 else 0) ∧
    Frm a.1.B (witRanges a.1.w) s₁.mem s.mem) ∧ Keep witRegs s₁ s

theorem draw_ct (Ri : RoundImpl) :
    RelCT isa (Two DS) (Impl.MillerRabin.PPC64LE.Blinded.draw Ri.name Ri.code) fun _ _ => True := by
  unfold Impl.MillerRabin.PPC64LE.Blinded.draw
  refine RelCT.seq (two_post (Ψ := D1) (two_map (fun a => (a.1, 8 * (a.1.t + 1) * a.2))
      (fun a s ⟨⟨n, σ, h, sp⟩, hav⟩ => ⟨⟨h.ctx, h.tape, h.sp.trans sp⟩, h.used, hav⟩) load_ct)
    fun a s hd => ?_) ?_
  · obtain ⟨⟨n, σ, h, sp⟩, hav⟩ := id hd
    exact WP.mono (load_ok h.ctx h.used hav) fun t ht => ⟨s, hd, ht⟩
  refine RelCT.seq (two_post (Ψ := D2)
      (two_map (fun a => (a.1, Spec.Rsa.os2ip (seg a.1.r (0 + 8 * (a.1.t + 1) * a.2) (8 * (a.1.t + 1)))))
        (fun a s ⟨s₀, ⟨⟨n, σ, h, sp⟩, hav⟩, hl⟩ => by
          obtain ⟨-, ctx1, -, -, v1⟩ := after_load h hav hl
          exact ⟨ctx1, hl.2.sp.trans (h.sp.trans sp), v1⟩) witness_ct)
      fun a s hd => ?_) ?_
  · obtain ⟨s₀, ⟨⟨n, σ, h, sp⟩, hav⟩, hl⟩ := id hd
    obtain ⟨e1, ctx1, -, hu1, v1⟩ := after_load h hav hl
    have ctx := h.ctx
    exact WP.mono (witness_ok e1 ctx1.prep.n ctx1.prep.odd ctx.shape ctx1.top ctx1.topOff ctx.t0 ctx.tw ctx.b1
      ctx.b64 v1 hu1) fun t ht => ⟨s, hd, ht⟩
  exact two_map (fun a => (a.1, (wit a.1.c (8 * (a.1.t + 1)) a.1.r (0 + 8 * (a.1.t + 1) * a.2)).1))
    (fun a s ⟨s₁, ⟨s₀, ⟨⟨n, σ, h, sp⟩, hav⟩, hl⟩, hw⟩ => by
      obtain ⟨-, ctx2, -, ha, hac⟩ := after_witness h hav hl hw
      exact ⟨ctx2.prep, ha, hac, ctx2.sp, ctx2.stk, hw.2.sp.trans (hl.2.sp.trans (h.sp.trans sp))⟩)
    (round_ct Ri)

/-- The loop's check. -/
abbrev chk : List Instr := [ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4

/-- After the check. -/
def C1 (n : Nat) (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, BS n a s₀ ∧ ((s.gpr .r5 = BitVec.ofNat 64
      (if 8 * (a.1.t + 1) ≤ a.1.rl - 8 * (a.1.t + 1) * a.2 then 1 else 0) ∧ s.mem = s₀.mem) ∧
    Keep [.r0, .r3, .r4, .r5] s₀ s)

theorem C1.bs {n : Nat} {a : BD × Nat} {s : State} (h : C1 n a s) : BS n a s := by
  obtain ⟨s₀, ⟨σ, hl, sp⟩, ⟨-, hm⟩, k⟩ := h
  exact ⟨σ, hl.ofMem hm (hl.ctx.prep.env.keep k (by decide)) k.sp k.rd k.wr, sp⟩

theorem BS.env {n : Nat} {a : BD × Nat} {s : State} (h : BS n a s) :
    Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp := by
  obtain ⟨σ, hl, sp⟩ := h
  exact ⟨hl.ctx.prep.env, hl.sp.trans sp⟩

/-- The working space's address in `r31`, and the stack pointer. -/
def R3 (a : BD × Nat) (s : State) : Prop := s.gpr .r31 = a.1.B ∧ s.sp = a.1.sp

theorem pins_R3 : Pins R3 [.r31] := by
  intro a s₁ s₂ ⟨a31, asp⟩ ⟨b31, bsp⟩
  refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [a31, b31]

theorem body_ct (Ri : RoundImpl) (n : Nat) :
    RelCT isa (Two (BS n)) (.seq (.block chk) (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat])
      (Impl.MillerRabin.PPC64LE.Blinded.draw Ri.name Ri.code)) (.block [ldh .r3 hStat, .subi .r3 .r3 4])))
      fun _ _ => True := by
  have pB : Pins (BS n) [.r10, .r11, .r29, .r31] := pins_env (fun a => a.1) fun a s h => h.env
  have pC : Pins (C1 n) [.r10, .r11, .r29, .r31] := Pins.of_imp pB fun _ _ h => h.bs
  refine RelCT.seq (two_post (Ψ := C1 n) (two_taint _ pB (by taint_decide)) fun a s h => ?_)
    (RelCT.seq (two_ite (fun a s₁ s₂ ⟨_, _, ⟨a5, _⟩, _⟩ ⟨_, _, ⟨b5, _⟩, _⟩ => by
      rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, a5, b5]) ?_ ?_) (two_taint _ pins_R3 (by taint_decide)))
  · obtain ⟨σ, hl, sp⟩ := id h
    exact WP.mono (check_ok hl) fun t ht => ⟨s, h, ht⟩
  · refine two_post (two_taint _ (Pins.of_imp pC fun _ _ h => h.1) (by taint_decide)) fun a s ⟨h, _⟩ => ?_
    obtain ⟨e, sp⟩ := h.bs.env
    have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
    exact WP.mono (WP.keep [.r3] (Q := fun _ => True) (by
      simp only [sth, hStat]; prun [e.h31, e.hs.st (d := 160) (n := 8) (by omega)]; exact ⟨_, rfl⟩) (by decide))
      fun t ⟨_, kt⟩ => ⟨(kt.gpr .r31 (by decide)).trans e.h31, kt.sp.trans sp⟩
  · refine two_map id (Ψ := DS) (fun a s ⟨h, hz⟩ => ⟨⟨n, h.bs⟩, ?_⟩) (two_post (draw_ct Ri) fun a s h => ?_)
    · obtain ⟨⟨m, σ, hl, sp⟩, hav⟩ := h
      exact WP.mono (draw_ok Ri hl hav) fun t ⟨lk, _⟩ => ⟨lk.prep.env.h31, lk.sp.trans sp⟩
    · obtain ⟨s₀, ⟨σ, hl, -⟩, ⟨h5, -⟩, -⟩ := h
      rw [VG.PPC64LE.eval_zero, h5] at hz
      dsimp only [id]
      by_contra hc
      have : ¬ 8 * (a.1.t + 1) ≤ a.1.rl - 8 * (a.1.t + 1) * a.2 := by omega
      simp only [this, ↓reduceIte] at hz
      exact absurd hz (by decide)

/-- After an iteration: the end, or the next state. -/
def BP (n : Nat) (a : BD × Nat) (s : State) : Prop :=
  ∃ σ, ((isa.eval (.zero .d .r3) s = some false ∧ n = 0 ∧
      MOut σ s a.1.B a.1.L a.1.w a.1.c a.1.rl a.1.ch a.1.r) ∨
    (isa.eval (.zero .d .r3) s = some true ∧ 0 < n ∧
      LInv σ s a.1.B a.1.R a.1.L a.1.w a.1.c a.1.rl a.1.t a.1.b a.1.ch a.1.r (a.2 + 1) (n - 1))) ∧ σ.sp = a.1.sp

theorem loop_ct (Ri : RoundImpl) (n : Nat) :
    RelCT isa (Two (BS n)) (.loop (.seq (.block chk) (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat])
      (Impl.MillerRabin.PPC64LE.Blinded.draw Ri.name Ri.code)) (.block [ldh .r3 hStat, .subi .r3 .r3 4])))
      (.zero .d .r3)) fun _ _ => True := by
  refine RelCT.loop (M := isa) (fun n => Two (BS n)) (fun n => ?_) n
  refine (two_post (Ψ := BP n) (body_ct Ri n) fun a s ⟨σ, hl, sp⟩ =>
    WP.mono (body_ok Ri hl) fun t ht => ⟨σ, ht, sp⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨a, ⟨σ₁, h₁, sp₁⟩, ⟨σ₂, h₂, sp₂⟩⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · obtain ⟨e₁, -⟩ := h₁.resolve_right fun ⟨_, h, _⟩ => by omega
    obtain ⟨e₂, -⟩ := h₂.resolve_right fun ⟨_, h, _⟩ => by omega
    refine ⟨by rw [e₁, e₂], fun _ => trivial, fun he => ?_⟩
    rw [e₁] at he; cases he
  · obtain ⟨e₁, -, l₁⟩ := h₁.resolve_left fun ⟨_, h, _⟩ => by omega
    obtain ⟨e₂, -, l₂⟩ := h₂.resolve_left fun ⟨_, h, _⟩ => by omega
    exact ⟨by rw [e₁, e₂], fun _ => trivial, fun _ => ⟨n - 1, by omega, (a.1, a.2 + 1), ⟨σ₁, l₁, sp₁⟩, ⟨σ₂, l₂, sp₂⟩⟩⟩

/-- The loop's start: the context, no octets read, the tape. -/
def MS (a : BD) (s : State) : Prop :=
  BCtx s a.B a.L a.w a.c a.R a.rl a.t a.b a.ch ∧ word s.mem a.B (8 * hUsed) = BitVec.ofNat 64 0 ∧
    Spec.Rsa.bytesAt s.mem a.R a.rl = a.r ∧ s.sp = a.sp

theorem millerRabin_ct (Ri : RoundImpl) :
    RelCT isa (Two MS) (Impl.MillerRabin.PPC64LE.Blinded.millerRabin Ri.name Ri.code) fun _ _ => True := by
  have pM : Pins MS [.r10, .r11, .r29, .r31] := pins_env id fun a s h => ⟨h.1.prep.env, h.2.2.2⟩
  unfold Impl.MillerRabin.PPC64LE.Blinded.millerRabin
  refine RelCT.seq (two_post (Ψ := fun (a : BD) s => BS (iters0 a.c a.ch a.t a.r) (a, 0) s)
    (two_taint _ pM (by taint_decide)) fun a s h => WP.mono (init_ok h.1 h.2.1 h.2.2.1) fun t ht => ⟨s, ht, h.2.2.2⟩) ?_
  exact (RelCT.exists_ fun n => loop_ct Ri n).mono
    (fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨iters0 a.c a.ch a.t a.r, (a, 0), h₁, h₂⟩) fun _ _ h => h

end VG.Proof.MillerRabin.PPC64LE.Blinded
