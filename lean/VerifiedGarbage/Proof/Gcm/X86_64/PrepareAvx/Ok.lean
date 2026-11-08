module

public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Step
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareAvx
public import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# `vg_aes_gcm_prepare16_pclmul_avx`

`PrepareAvx.prepare16` is proven on its SSE code (`WP.lane0`): the setup
leaves `H'` in `xmm3`, stored; each step of `plan` computes a power from two
the registers hold (`Inv`: which register holds which power, and which powers
are stored), and stores it. `valid`, decided on the plan, checks that each
step's operands hold powers adding up to its own and that it writes nothing
the steps use (`stepS_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.PrepareAvx

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepOff)
open VG.Impl.Gcm.X86_64.PrepareAvx (step plan plan48 setup stepS setupS sqS mulDS)
open VG.Proof.Gcm.X86_64.Pclmul (Only eq_prepared constImm_ok ldrev_ok hInvImm_ok rev_eq)
open VG.Proof.Gcm.X86_64.Stitch (in_sub in_sub_int)
open VG.Spec.Gcm (Block hpow)

/-- A step: destination, operands, and the power it computes. -/
abbrev Step := XReg × XReg × XReg × Nat

theorem lane0_prepare16 :
    lane0Block (setup ++ plan.flatMap step) = some (setupS ++ plan.flatMap stepS) := by
  decide +kernel

theorem lane0_prepare :
    lane0Block (setup ++ plan48.flatMap step) = some (setupS ++ plan48.flatMap stepS) := by
  decide +kernel

/-- Each step's operands hold powers adding up to its own, which is one of
the first `N`, and no step writes or reads a scratch register. -/
def valid (N : Nat) : List (XReg × Nat) → List Step → Bool
  | _, [] => true
  | env, (d, a, b, n) :: ps =>
    !scratch.contains d && !scratch.contains a && !scratch.contains b &&
    (match env.lookup a, env.lookup b with
     | some ea, some eb => ea + eb == n
     | _, _ => false) && 1 ≤ n && n ≤ N && valid N ((d, n) :: env) ps

/-- The registers' powers after the steps. -/
def envAfter : List (XReg × Nat) → List Step → List (XReg × Nat)
  | env, [] => env
  | env, (d, _, _, n) :: ps => envAfter ((d, n) :: env) ps

/-- The powers stored after the steps. -/
def storedAfter : List Nat → List Step → List Nat
  | S, [] => S
  | S, (_, _, _, n) :: ps => storedAfter (n :: S) ps

/-- What holds between steps, computing the first `N` powers (16 or 48):
register `r` holds `H'ᵉ` if `env` says so, and the powers `S` are in their
places. -/
structure Inv (N : Nat) (H : Block) (C : Addr) (m₀ : Mem) (env : List (XReg × Nat)) (S : List Nat) (t : State) : Prop where
  h1 : t.xmm .xmm1 = poly
  pw : ∀ r e, env.lookup r = some e → r ∉ scratch ∧ x * φ (t.xmm r) = φ H ^ e
  st : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N ∧
    t.mem.readW (C + BitVec.ofNat 64 (prepOff n)) 128 = Spec.Gcm.preparedPower (hpow H n)
  fr : Frame [⟨C + BitVec.ofNat 64 256, 16 * N⟩] m₀ t.mem
  rdi : t.gpr .rdi = C
  wr : InRegions t.wr C 1024
  hN : N = 16 ∨ N = 48

/-! ## The places of the powers -/

theorem prepOff_bound {n N : Nat} (hN : N = 16 ∨ N = 48) (h1 : 1 ≤ n) (h48 : n ≤ N) :
    256 ≤ prepOff n ∧ prepOff n + 16 ≤ 256 + 16 * N := by
  simp only [prepOff]; split <;> omega

theorem prepOff_sep {n n' : Nat} (h : n ≠ n') : prepOff n + 16 ≤ prepOff n' ∨ prepOff n' + 16 ≤ prepOff n := by
  simp only [prepOff]; split <;> split <;> omega

theorem prepOff_pair {k l : Nat} (hl : l < 2) : prepOff (2 * k + 2 - l) = 256 + 32 * k + 16 * l := by
  simp only [prepOff]; split <;> omega

theorem readW_sep {m : Mem} {C : Addr} {n n' N : Nat} {v : BitVec 128} (hN : N = 16 ∨ N = 48)
    (h1 : 1 ≤ n) (h48 : n ≤ N) (h1' : 1 ≤ n') (h48' : n' ≤ N) (h : n ≠ n') :
    (m.writeW (C + BitVec.ofNat 64 (prepOff n')) v).readW (C + BitVec.ofNat 64 (prepOff n)) 128 =
      m.readW (C + BitVec.ofNat 64 (prepOff n)) 128 := by
  have b := prepOff_bound hN h1 h48
  have b' := prepOff_bound hN h1' h48'
  exact Mem.readW_writeW_sep (Offset.sep C (prepOff_sep h) (by omega) (by omega)) (by decide)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem st_ok (r : XReg) (d : Nat) (t : State)
    (hin : InRegions t.wr (t.gpr .rdi + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquStore (at_ .rdi d) r]) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .rdi + BitVec.ofInt 64 (d : Int)) (t.xmm r) ∧ t'.gpr = t.gpr ∧
      t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  rw [WP.block_cons_iff]
  refine ⟨{ t with mem := t.mem.writeW (t.gpr .rdi + BitVec.ofInt 64 (d : Int)) (t.xmm r) },
    by simp only [isa, exec, State.store128, ea_at, hin, ite_true], WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Storing `H'ⁿ` from `r` at its place. -/
theorem store_ok {N : Nat} {H : Block} {C : Addr} {m₀ : Mem} {env : List (XReg × Nat)} {S : List Nat}
    {r : XReg} {n : Nat}
    (t : State) (hi : Inv N H C m₀ env S t) (hr : x * φ (t.xmm r) = φ H ^ n) (h1 : 1 ≤ n) (h48 : n ≤ N) :
    WP isa (.block [.movdquStore (at_ .rdi (prepOff n)) r]) t fun t' =>
      Inv N H C m₀ env (n :: S) t' ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have b := prepOff_bound hi.hN h1 h48
  have hN := hi.hN
  have hin : InRegions t.wr (t.gpr .rdi + BitVec.ofInt 64 ((prepOff n : Nat) : Int)) 16 := by
    rw [hi.rdi]; exact in_sub_int hi.wr (by omega)
  refine WP.mono (st_ok r _ t hin) fun t' ⟨m', g', x', rd', wr'⟩ => ?_
  rw [hi.rdi, BitVec.ofInt_natCast] at m'
  refine ⟨⟨by rw [x']; exact hi.h1, fun q e hq => by rw [x']; exact hi.pw q e hq, fun k hk => ?_, ?_,
    by rw [g']; exact hi.rdi, by rw [wr']; exact hi.wr, hi.hN⟩, g', rd', wr'⟩
  · rw [m']
    simp only [List.mem_cons] at hk
    by_cases hkn : k = n
    · subst hkn
      exact ⟨h1, h48, by rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]; exact eq_prepared hr⟩
    · obtain ⟨k1, k48, hs⟩ := hi.st k (hk.resolve_left hkn)
      exact ⟨k1, k48, by rw [readW_sep hi.hN k1 k48 h1 h48 hkn]; exact hs⟩
  · rw [m']
    exact hi.fr.writeW (List.mem_singleton_self _) _ (Offset.contains C (by omega) (by omega) (by omega))

theorem lookup_cons {env : List (XReg × Nat)} {d r : XReg} {n : Nat} :
    ((d, n) :: env).lookup r = if r = d then some n else env.lookup r := by
  rw [List.lookup_cons]
  by_cases h : r = d
  · subst h; simp
  · rw [beq_false_of_ne h]; simp [h]

/-- One step: `H'ⁿ` into `d`, and stored. -/
theorem stepS_ok {N : Nat} {H : Block} {C : Addr} {m₀ : Mem} {env : List (XReg × Nat)} {S : List Nat}
    {d a b : XReg} {n : Nat} {ps : List Step} (hv : valid N env ((d, a, b, n) :: ps) = true)
    (t : State) (hi : Inv N H C m₀ env S t) :
    WP isa (.block (stepS (d, a, b, n))) t fun t' =>
      Inv N H C m₀ ((d, n) :: env) (n :: S) t' ∧ (∀ q, q ≠ .rax → t'.gpr q = t.gpr q) ∧
        t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨hd, ha⟩, hb⟩, hab⟩, h1⟩, h48⟩, -⟩ := hv
  obtain ⟨-, d8, d9, d10, d11⟩ := not_scratch hd
  obtain ⟨-, a8, a9, a10, -⟩ := not_scratch ha
  obtain ⟨-, b8, b9, b10, b11⟩ := not_scratch hb
  -- The operands' powers.
  obtain ⟨ea, eb, hea, heb, hn⟩ : ∃ ea eb, env.lookup a = some ea ∧ env.lookup b = some eb ∧ ea + eb = n := by
    revert hab; cases env.lookup a <;> cases env.lookup b <;> simp
  have pa := (hi.pw a ea hea).2
  have pb := (hi.pw b eb heb).2
  -- The product, whichever code computes it.
  have hm : WP isa (.block (if a = b then sqS d a else mulDS d a b)) t fun t' =>
      x * φ (t'.xmm d) = φ H ^ n ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11, d] t t' := by
    have fin : ∀ t' : State, φ (t'.xmm d) = x * φ (t.xmm a) * φ (t.xmm b) → x * φ (t'.xmm d) = φ H ^ n :=
      fun t' e => by
        rw [e, show x * (x * φ (t.xmm a) * φ (t.xmm b)) = (x * φ (t.xmm a)) * (x * φ (t.xmm b)) by ring,
          pa, pb, ← pow_add, hn]
    split
    · next hab' =>
      subst hab'
      exact WP.mono (sqS_ok d a t a8 a10 d8 d10 d11 hi.h1) fun t' ⟨e, o⟩ =>
        ⟨fin t' e, o.weaken fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with h | h | h | h <;> simp [h]⟩
    · exact WP.mono (mulDS_ok d a b t a8 a9 a10 b8 b9 b10 b11 d8 d9 d10 d11 hi.h1) fun t' ⟨e, o⟩ =>
        ⟨fin t' e, o⟩
  rw [stepS, WP.block_append_iff]
  refine WP.mono hm fun t₁ ⟨e₁, o₁⟩ => ?_
  have hi₁ : Inv N H C m₀ ((d, n) :: env) S t₁ := by
    refine ⟨?_, fun r e hr => ?_, fun k hk => ?_, by rw [o₁.mem]; exact hi.fr,
      by rw [o₁.gpr _ (by decide)]; exact hi.rdi, by rw [o₁.wr]; exact hi.wr, hi.hN⟩
    · rw [o₁.xmm _ (by simp [Ne.symm (not_scratch hd).1])]
      exact hi.h1
    · rw [lookup_cons] at hr
      split at hr
      · next hrd => subst hrd; cases hr; exact ⟨hd, e₁⟩
      · next hrd =>
        obtain ⟨hs, hp⟩ := hi.pw r e hr
        obtain ⟨-, r8, r9, r10, r11⟩ := not_scratch hs
        refine ⟨hs, ?_⟩
        rw [o₁.xmm _ (by simp [r8, r9, r10, r11, hrd])]
        exact hp
    · rw [o₁.mem]; exact hi.st k hk
  refine WP.mono (store_ok t₁ hi₁ e₁ h1 h48) fun t' ⟨hi', g', rd', wr'⟩ =>
    ⟨hi', fun q hq => by rw [g', o₁.gpr q hq], by rw [rd', o₁.rd], by rw [wr', o₁.wr]⟩

/-- The steps, one after the other. -/
theorem planS_ok {N : Nat} {H : Block} {C : Addr} {m₀ : Mem} :
    ∀ (ps : List Step) (env : List (XReg × Nat)) (S : List Nat) (t : State), valid N env ps = true →
      Inv N H C m₀ env S t →
      WP isa (.block (ps.flatMap stepS)) t fun t' =>
        Inv N H C m₀ (envAfter env ps) (storedAfter S ps) t' ∧ (∀ q, q ≠ .rax → t'.gpr q = t.gpr q) ∧
          t'.rd = t.rd ∧ t'.wr = t.wr
  | [], _, _, _, _, hi => WP.block_nil ⟨hi, fun _ _ => rfl, rfl, rfl⟩
  | (d, a, b, n) :: ps, env, S, t, hv, hi => by
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (stepS_ok hv t hi) fun t₁ ⟨hi₁, g₁, rd₁, wr₁⟩ => ?_
    have hv' : valid N ((d, n) :: env) ps = true := by
      simp only [valid, Bool.and_eq_true] at hv; exact hv.2
    refine WP.mono (planS_ok ps _ _ t₁ hv' hi₁) fun t' ⟨hi', g', rd', wr'⟩ =>
      ⟨hi', fun q hq => by rw [g' q hq, g₁ q hq], rd'.trans rd₁, wr'.trans wr₁⟩

/-- The setup: `H'` in `xmm3`, and stored. -/
theorem setupS_ok {N : Nat} (hN : N = 16 ∨ N = 48) (t : State) (hw : InRegions t.wr (t.gpr .rdi) 1024) :
    WP isa (.block setupS) t fun t' =>
      Inv N (Spec.Gcm.ctxH t.mem (t.gpr .rdi)) (t.gpr .rdi) t.mem [(.xmm3, 1)] [1] t' ∧
        (∀ q, q ≠ .rax → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)) 16 := by
    obtain ⟨r, hr, hc⟩ := in_sub_int (off := 240) (n := 16) hw (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [setupS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 t₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun t₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInvImm_ok t₃) fun t₄ ⟨h₄, o₄⟩ => ?_
  have o₁₄ := (o₁₂.trans o₃).trans o₄
  rw [o₁₂.mem, o₁₂.gpr _ (by decide)] at l₃
  have hi₄ : Inv N (Spec.Gcm.ctxH t.mem (t.gpr .rdi)) (t.gpr .rdi) t.mem [(.xmm3, 1)] [] t₄ := by
    refine ⟨by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂], fun r e hr => ?_, fun k hk => absurd hk (by simp),
      by rw [o₁₄.mem]; exact Frame.refl _ _, by rw [o₁₄.gpr _ (by decide)], by rw [o₁₄.wr]; exact hw, hN⟩
    rw [lookup_cons] at hr
    split at hr
    · next h =>
      subst h; cases hr
      refine ⟨by decide, ?_⟩
      rw [h₄, l₃, pow_one, BitVec.ofInt_natCast]
      rfl
    · cases hr
  have p₄ := (hi₄.pw .xmm3 1 (by simp)).2
  refine WP.mono (store_ok t₄ hi₄ p₄ (by decide) (by omega)) fun t' ⟨hi', g', rd', wr'⟩ =>
    ⟨hi', fun q hq => by rw [g', o₁₄.gpr q hq], by rw [rd', o₁₄.rd], by rw [wr', o₁₄.wr]⟩

theorem plan_valid : valid 16 [(.xmm3, 1)] plan = true := by decide

theorem plan_stored : ∀ k < 8, ∀ l < 2, 2 * k + 2 - l ∈ storedAfter [1] plan := by decide

/-- `prepare16`: the first 16 prepared powers of the hash subkey at `C + 240`
into pairs 0–7 of the context at `C`, nothing outside bytes 256–1023 of it
written. -/
theorem prepare16_ok' {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024) :
    WP isa Impl.Gcm.X86_64.PrepareAvx.prepare16 s₀ fun s =>
      Prepare16.PrepOk16W s₀ s ∧ Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 256⟩] s₀.mem s.mem := by
  have hS : WP isa (.block (setupS ++ plan.flatMap stepS)) (s₀.proj 0) fun t' =>
      Inv 16 (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (s₀.gpr .rdi) s₀.mem (envAfter [(.xmm3, 1)] plan)
        (storedAfter [1] plan) t' ∧ (∀ q, q ≠ .rax → t'.gpr q = s₀.gpr q) ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
    rw [WP.block_append_iff]
    refine WP.mono (setupS_ok (.inl rfl) (s₀.proj 0) (by rw [State.proj_wr, State.proj_gpr]; exact hw))
      fun t₁ ⟨hi₁, g₁, rd₁, wr₁⟩ => ?_
    rw [State.proj_mem, State.proj_gpr] at hi₁
    refine WP.mono (planS_ok plan _ _ t₁ plan_valid hi₁) fun t' ⟨hi', g', rd', wr'⟩ =>
      ⟨hi', fun q hq => by rw [g' q hq, g₁ q hq, State.proj_gpr], by rw [rd', rd₁, State.proj_rd],
        by rw [wr', wr₁, State.proj_wr]⟩
  refine WP.mono (WP.lane0 lane0_prepare16 hS) fun s ⟨⟨hi, g, rd, wr⟩, _, _⟩ =>
    ⟨⟨fun k hk l hl => ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have := (hi.st _ (plan_stored k hk l hl)).2.2
    rw [prepOff_pair hl, State.proj_mem] at this
    exact this
  · have := hi.fr; rw [State.proj_mem] at this
    exact this.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      obtain rfl := List.mem_singleton.mp hr; exact Offset.sub _ (Nat.le_refl _) (by omega)⟩
  · rw [← State.proj_gpr s 0, g r hr]
  · rw [← State.proj_rd s 0, rd]
  · rw [← State.proj_wr s 0, wr]
  · have := hi.fr; rw [State.proj_mem] at this; exact this

theorem prepare16_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024) :
    WP isa Impl.Gcm.X86_64.PrepareAvx.prepare16 s₀ (Prepare16.PrepOk16W s₀) :=
  WP.mono (prepare16_ok' hw) fun _ h => h.1

/-- It writes none of the context from byte 512 on. -/
theorem prepare16_written (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.Gcm.prepare16Contract X86_64.abi).pre s)
    (he : Exec isa Impl.Gcm.X86_64.PrepareAvx.prepare16 s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Gcm.prepareSig [("ctx", 512)] s s' :=
  Prepare16.written16 (fun _ hw _ => WP.mono (prepare16_ok' hw) fun _ h => h.2) s t s' hs he

theorem prepare16_verified :
    Verified X86_64.target Impl.Gcm.X86_64.PrepareAvx.prepare16 (Spec.Gcm.prepare16Contract X86_64.abi) :=
  Prepare16.verified_ofW _ (fun _ hw _ => prepare16_ok hw) (by decide +kernel) Prepare16.prepare16Avx_ct

/-! ## `vg_aes_gcm_prepare`: the 48 powers -/

theorem plan48_valid : valid 48 [(.xmm3, 1)] plan48 = true := by decide

theorem plan48_stored : ∀ k < 24, ∀ l < 2, 2 * k + 2 - l ∈ storedAfter [1] plan48 := by decide

/-- `prepare`: the 48 prepared powers of the hash subkey at `C + 240` into
pairs 0–23 of the context at `C`, nothing else written. -/
theorem prepare_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024) :
    WP isa Impl.Gcm.X86_64.PrepareAvx.prepare s₀ (Prepare.PrepOk s₀) := by
  have hS : WP isa (.block (setupS ++ plan48.flatMap stepS)) (s₀.proj 0) fun t' =>
      Inv 48 (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (s₀.gpr .rdi) s₀.mem (envAfter [(.xmm3, 1)] plan48)
        (storedAfter [1] plan48) t' ∧ (∀ q, q ≠ .rax → t'.gpr q = s₀.gpr q) ∧ t'.rd = s₀.rd ∧
        t'.wr = s₀.wr := by
    rw [WP.block_append_iff]
    refine WP.mono (setupS_ok (.inr rfl) (s₀.proj 0) (by rw [State.proj_wr, State.proj_gpr]; exact hw))
      fun t₁ ⟨hi₁, g₁, rd₁, wr₁⟩ => ?_
    rw [State.proj_mem, State.proj_gpr] at hi₁
    refine WP.mono (planS_ok plan48 _ _ t₁ plan48_valid hi₁) fun t' ⟨hi', g', rd', wr'⟩ =>
      ⟨hi', fun q hq => by rw [g' q hq, g₁ q hq, State.proj_gpr], by rw [rd', rd₁, State.proj_rd],
        by rw [wr', wr₁, State.proj_wr]⟩
  refine WP.mono (WP.lane0 lane0_prepare hS) fun s ⟨⟨hi, g, rd, wr⟩, _, _⟩ =>
    ⟨fun k hk l hl => ?_, ?_, fun r hr _ => ?_, ?_, ?_⟩
  · have := (hi.st _ (plan48_stored k hk l hl)).2.2
    rw [prepOff_pair hl, State.proj_mem] at this
    exact this
  · have := hi.fr; rw [State.proj_mem] at this; exact this
  · rw [← State.proj_gpr s 0, g r hr]
  · rw [← State.proj_rd s 0, rd]
  · rw [← State.proj_wr s 0, wr]

theorem prepare_verified :
    Verified X86_64.target Impl.Gcm.X86_64.PrepareAvx.prepare (Spec.Gcm.prepareContract X86_64.abi) :=
  Prepare.verified_of _ (fun _ hw _ => prepare_ok hw) (by decide +kernel) Prepare16.prepareAvx_ct

/-- `prepareSse`, the SSE code itself: the 48 prepared powers of the hash
subkey at `C + 240` into pairs 0–23 of the context at `C`, nothing else
written. -/
theorem prepareSse_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024) :
    WP isa Impl.Gcm.X86_64.PrepareAvx.prepareSse s₀ (Prepare.PrepOk s₀) := by
  simp only [Impl.Gcm.X86_64.PrepareAvx.prepareSse]
  rw [WP.block_append_iff]
  refine WP.mono (setupS_ok (.inr rfl) s₀ hw) fun t₁ ⟨hi₁, g₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (planS_ok plan48 _ _ t₁ plan48_valid hi₁) fun s ⟨hi, g, rd, wr⟩ =>
    ⟨fun k hk l hl => ?_, hi.fr, fun r hr _ => by rw [g r hr, g₁ r hr], by rw [rd, rd₁], by rw [wr, wr₁]⟩
  have := (hi.st _ (plan48_stored k hk l hl)).2.2
  rw [prepOff_pair hl] at this
  exact this

theorem prepareSse_verified :
    Verified X86_64.target Impl.Gcm.X86_64.PrepareAvx.prepareSse (Spec.Gcm.prepareContract X86_64.abi) :=
  Prepare.verified_of _ (fun _ hw _ => prepareSse_ok hw) (by decide +kernel) Prepare16.prepareSse_ct

/-- `prepare` after setting the flag word to 0, on the prepared key context. -/
theorem prepareFlagged_verified :
    Verified X86_64.target (Impl.Gcm.X86_64.Flag.prepareFlagged Impl.Gcm.X86_64.PrepareAvx.prepare)
      (Proof.AesGcm.Flag.prepareContract X86_64.abi) :=
  Prepare.flagged_verified _ (fun _ hw _ => prepare_ok hw) (by decide +kernel) Prepare.flaggedAvx_ct

end VG.Proof.Gcm.X86_64.PrepareAvx
