module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.SpongeStream
public import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.SpongeStream
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

-- separate module: the taint proof and call narrowing cost more than their imports.

@[expose] public section
namespace VG.Proof.MlDsa.X86_64.Sample.SpongeStream
open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample

/-- The squeeze position returned is public as well as its trace. -/
theorem squeeze_regs : RelCT isa (fun x y => Proof.Sha3.squeezeX86_64.pre x ∧
    Proof.Sha3.squeezeX86_64.pre y ∧ Proof.Sha3.squeezeX86_64.pub x y)
    Impl.Sha3.X86_64.Stream.squeeze (fun x y => x.gpr .rax = y.gpr .rax) := by
  refine RelCT.mono (RelCT.taintRegs (τ := Proof.Sha3.X86_64.Stream.Squeeze.τ₀)
    (fun _ _ h => Proof.Sha3.X86_64.Stream.Squeeze.agree₀ h.1 h.2.1 h.2.2) [.rax]
    (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)) (fun _ _ h => h) ?_
  intro x y h; exact h .rax (by simp)

/-- Public squeeze arguments leave equal returned positions even when the
caller grants wider memory permissions. -/
theorem squeeze_call_regs {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      Proof.Sha3.squeezeX86_64.pre (x.callEntry.withRegions rd₁ wr₁) ∧
      Proof.Sha3.squeezeX86_64.pre (y.callEntry.withRegions rd₂ wr₂) ∧
      Proof.Sha3.squeezeX86_64.pub (x.callEntry.withRegions rd₁ wr₁) (y.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x.rd ++ x.wr) ∧ Covers wr₁ x.wr ∧
      Covers (rd₂ ++ wr₂) (y.rd ++ y.wr) ∧ Covers wr₂ y.wr ∧ x.gpr .rsp = y.gpr .rsp) :
    RelCT isa P (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze)
      (fun x y => x.gpr .rax = y.gpr .rax) := by
  intro x y tx ty x' y' hp ex ey
  have ht := (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct hP x y tx ty x' y' hp ex ey).1
  refine ⟨ht, ?_⟩
  obtain ⟨r₁, w₁, r₂, w₂, p₁, p₂, hpub, c₁, cw₁, c₂, cw₂, _⟩ := hP x y hp
  cases ex with
  | call cs bs rs =>
    cases ey with
    | call ct bt rt =>
      have hs := Option.some.inj ((call_callEntry x).symm.trans cs)
      have ht := Option.some.inj ((call_callEntry y).symm.trans ct)
      subst hs; subst ht
      obtain ⟨nx, en₁⟩ := trace_narrow Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct p₁ c₁ cw₁ bs
      obtain ⟨ny, en₂⟩ := trace_narrow Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct p₂ c₂ cw₂ bt
      have ax := Exec.widen en₁ (rd := x.rd) (wr := x.wr) (by simpa using c₁) (by simpa using cw₁)
      have ay := Exec.widen en₂ (rd := y.rd) (wr := y.wr) (by simpa using c₂) (by simpa using cw₂)
      simp only [State.withRegions_withRegions] at ax ay
      change Exec isa _ x.callEntry _ _ at ax
      change Exec isa _ y.callEntry _ _ at ay
      obtain ⟨_, hx⟩ := Exec.det bs ax
      obtain ⟨_, hy⟩ := Exec.det bt ay
      have hrax := (squeeze_regs _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ en₁ en₂).2
      rw [(ret_gpr rs .rax).2, (ret_gpr rt .rax).2]
      simpa only [hx, hy, State.withRegions_gpr, ite_eq_right (by decide : Reg.rax ≠ .rsp)] using hrax

theorem core_env_pub {P₁ P₂ : Sp} {σ₁ σ₂ s₁ s₂ : State} (hq : Public P₁ P₂ σ₁ σ₂)
    (e₁ : Env P₁ σ₁ s₁) (e₂ : Env P₂ σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  rw [e₁.rbx, e₂.rbx, e₁.rbp, e₂.rbp, e₁.rsp, e₂.rsp, hq.scr, hq.a, hq.rsp]
  exact ⟨rfl, rfl, rfl⟩

theorem core_at_pub {P₁ P₂ : Sp} {σ₁ σ₂ : State} (hq : Public P₁ P₂ σ₁ σ₂) (k : Nat) :
    P₁.at' k = P₂.at' k := by simp only [Sp.at', hq.scr]

theorem taint_core {Pre : State → Prop} {Pub : State → State → Prop} {f : State → Sp}
    (hpub : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → Public (f σ₁) (f σ₂) σ₁ σ₂)
    {J : Sp → State → State → Prop} (hJ : ∀ σ s, J (f σ) σ s → Env (f σ) σ s) {c : Prog isa}
    (rs : List Reg) (hr : ∀ s₁ s₂, Rel2 Pre Pub (fun σ => J (f σ) σ) s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (X86_64.Taint.ofRegs (([.rbx, .rbp, .rsp] : List Reg) ++ rs)) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c fun _ _ => True := by
  refine taintRel _ (fun x y hs r hr' => ?_) h
  rcases List.mem_append.mp hr' with hr' | hr'
  · obtain ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ := hs
    have he := core_env_pub (hpub σ₁ σ₂ p₁ p₂ hq) (hJ _ _ h₁) (hJ _ _ h₂)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    exacts [he.1, he.2.1, he.2.2]
  · exact hr x y hs r hr'

section
/-! The runs of a sampling function whose entry states satisfy `Pre` and
agree by `Pub`, each making the call `f σ` of its entry state `σ`. -/
variable {Pre : State → Prop} {Pub : State → State → Prop} {f : State → Sp}
  (hok : ∀ σ, Pre σ → SpOk (f σ) σ)
  (hpub : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → Public (f σ₁) (f σ₂) σ₁ σ₂)
include hok hpub

theorem state_ct {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2024)
    {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .rsp]) (.block (zeroSt ++ absArgs rate)) h1).isSome
      = true)
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .rsp, .rax]) (.block (padArgs rate)) h2).isSome = true)
    (c3 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .rsp]) (.block (sqzArgs rate outlen)) h3).isSome
      = true) :
    RelCT isa (Rel2 Pre Pub fun σ => J0 (f σ) σ) (sponge rate outlen)
      (fun x y => x.gpr .rax = y.gpr .rax ∧
        Rel2 Pre Pub (fun σ => Output rate.toNat outlen.toNat (f σ) σ) x y) := by
  refine RelCT.seq (relSp hok (J' := J1 rate.toNat) (fun P σ s hp h => blk1_ok hp hr h)
    (taint_core hpub (fun _ _ h => h.env) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by simpa using c1))) ?_
  refine RelCT.seq (relSp hok (J' := J2 rate.toNat) (fun P σ s hp h => call1_ok hp h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)) ?_
  · have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, absorb_pre h₁.args, absorb_pre h₂.args, ?_, (covA o₁ h₁.env).1, (covA o₁ h₁.env).2,
      (covA o₂ h₂.env).1, (covA o₂ h₂.env).2, (core_env_pub hq h₁.env h₂.env).2.2⟩
    simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
      ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
      h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
      h₁.args.r9, h₂.args.r9, hq.scr, hq.sd, hq.len, core_at_pub hq, (core_env_pub hq h₁.env h₂.env).2.2, and_self]
  refine RelCT.seq (relSp hok (J' := J3 rate.toNat) (fun P σ s hp h => blk2_ok hp hr h)
    (taint_core hpub (fun _ _ h => h.env) [.rax] (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, i₁, i₂⟩ r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [i₁.rax, i₂.rax, (hpub σ₁ σ₂ p₁ p₂ hq).len]) (by simpa using c2))) ?_
  refine RelCT.seq (relSp hok (J' := J4 rate.toNat) (fun P σ s hp h => call2_ok hp h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)) ?_
  · have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, pad_pre h₁.args, pad_pre h₂.args, ?_, (covP o₁ h₁.env).1, (covP o₁ h₁.env).2,
      (covP o₂ h₂.env).1, (covP o₂ h₂.env).2, (core_env_pub hq h₁.env h₂.env).2.2⟩
    simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.r8 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
      h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.r8, h₂.args.r8, hq.scr, hq.len, core_at_pub hq,
      (core_env_pub hq h₁.env h₂.env).2.2, and_self]
  refine RelCT.seq (relSp hok (J' := J5 rate.toNat outlen.toNat) (fun P σ s hp h => blk3_ok hp hr ho h)
    (taint_core hpub (fun _ _ h => h.env) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by simpa using c3))) ?_
  have ha : ∀ s₁ s₂, (Rel2 Pre Pub fun σ => J5 rate.toNat outlen.toNat (f σ) σ) s₁ s₂ →
      ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      Proof.Sha3.squeezeX86_64.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧
      Proof.Sha3.squeezeX86_64.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Proof.Sha3.squeezeX86_64.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
    intro s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩
    have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, squeeze_pre h₁.2, squeeze_pre h₂.2, ?_, (covS o₁ ho h₁.1.env).1, (covS o₁ ho h₁.1.env).2,
      (covS o₂ ho h₂.1.env).1, (covS o₂ ho h₂.1.env).2, (core_env_pub hq h₁.1.env h₂.1.env).2.2⟩
    simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
        ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.2.rdi, h₂.2.rdi,
        h₁.2.rsi, h₂.2.rsi, h₁.2.rdx, h₂.2.rdx, h₁.2.rcx, h₂.2.rcx, h₁.2.r8, h₂.2.r8,
        h₁.2.r9, h₂.2.r9, hq.scr, core_at_pub hq, (core_env_pub hq h₁.1.env h₂.1.env).2.2, and_self]
  intro x y tx ty x' y' h ex ey
  obtain ⟨ht, hax⟩ := squeeze_call_regs ha x y tx ty x' y' h ex ey
  obtain ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ := h
  obtain ⟨_, _, e₁, o₁⟩ := call_ok (hok σ₁ p₁) ho h₁
  obtain ⟨_, _, e₂, o₂⟩ := call_ok (hok σ₂ p₂) ho h₂
  obtain ⟨_, rfl⟩ := Exec.det ex e₁
  obtain ⟨_, rfl⟩ := Exec.det ey e₂
  exact ⟨ht, hax, σ₁, σ₂, p₁, p₂, hq, o₁, o₂⟩

theorem stream_ct {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2008)
    {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .rsp]) (.block (zeroSt ++ absArgs rate)) h1).isSome = true)
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .rsp, .rax]) (.block (padArgs rate)) h2).isSome = true)
    (c3 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .rsp]) (.block (sqzArgs rate outlen)) h3).isSome = true) :
    RelCT isa (Rel2 Pre Pub fun σ => J0 (f σ) σ) (spongeStream rate outlen)
      (fun x y => ∃ pos, Rel2 Pre Pub (fun σ s => J6 rate.toNat outlen.toNat {f σ with prm := pos} σ s ∧
        Stream rate.toNat outlen.toNat {f σ with prm := pos} σ pos s) x y) := by
  refine RelCT.seq (state_ct hok hpub hr (by omega_arith) c1 c2 c3) ?_
  intro x y tx ty x' y' h ex ey
  have ht := (taintRel (P := fun x y => x.gpr .rax = y.gpr .rax ∧
      Rel2 Pre Pub (fun σ => Output rate.toNat outlen.toNat (f σ) σ) x y) [.rbx] (fun x y h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨_, σ₁, σ₂, p₁, p₂, hq, o₁, o₂⟩ := h
    exact (core_env_pub (hpub σ₁ σ₂ p₁ p₂ hq) o₁.env o₂.env).1)
    (by taint_decide) x y tx ty x' y' h ex ey).1
  obtain ⟨hax, σ₁, σ₂, p₁, p₂, hq, o₁, o₂⟩ := h
  obtain ⟨_, _, e₁, j₁⟩ := save_ok o₁
  obtain ⟨_, _, e₂, j₂⟩ := save_ok o₂
  obtain ⟨_, rfl⟩ := Exec.det ex e₁
  obtain ⟨_, rfl⟩ := Exec.det ey e₂
  rw [← hax] at j₂
  exact ⟨ht, x.gpr .rax, σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩

end

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {f : State → Sp}
  (hok : ∀ σ, Pre σ → SpOk (f σ) σ)
  (hpub : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → SpPub (f σ₁) (f σ₂) σ₁ σ₂)
include hok hpub

theorem count_ct {rate done : Nat} {pos : BitVec 64} :
    RelCT isa (Rel2 Pre Pub fun σ s => Env (f σ) σ s ∧ Stream rate done (f σ) σ pos s)
      (.block saveCount) (Rel2 Pre Pub fun σ s => Env (f σ) σ s ∧ Stream rate done (f σ) σ pos s) := by
  refine relInv (fun σ s hp h => WP.mono (count_ok (hok σ hp) h.1) fun s' ⟨he, _, _, hf⟩ =>
    ⟨he, h.2.frame hf
      (by simpa using (disj_scr0 (P := f σ) (n := 200) (b := 2016) (m := 8) (by decide) (by decide)))⟩)
    (taintSp hpub (J := fun _ σ s => Env (f σ) σ s ∧ Stream rate done (f σ) σ pos s)
      (fun _ _ h => h.1) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))

theorem more_ct {rate offset len : BitVec 32} {done : Nat} {pos : BitVec 64}
    (hr : spRate rate) (ho : 840 + done + len.toNat ≤ 2008)
    (hprm : ∀ σ, Pre σ → (f σ).prm = pos)
    (hx : BitVec.signExtend 64 offset = BitVec.ofNat 64 (840 + done))
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (hcheck : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp])
      (.block (moreArgs rate offset len)) hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub fun σ s => Env (f σ) σ s ∧ Stream rate.toNat done (f σ) σ pos s)
      (squeezeMore rate offset len) (Rel2 Pre Pub fun σ s => Env (f σ) σ s) := by
  refine RelCT.seq (relInv (I' := fun σ => More rate.toNat done len.toNat (f σ) σ pos)
    (fun σ s hp h => WP.mono (more_args_ok (hok σ hp) hr ho (hprm σ hp) hx h.1 h.2) fun _ h' => h'.1)
    (taintSp hpub (J := fun _ σ s => Env (f σ) σ s ∧ Stream rate.toNat done (f σ) σ pos s)
      (fun _ _ h => h.1) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) hcheck)) ?_
  refine relInv (fun σ s hp h => WP.mono (more_call_ok (hok σ hp) ho h) fun _ h' => h'.1)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)
  have hq := hpub σ₁ σ₂ p₁ p₂ hq'
  refine ⟨_, _, _, _, squeeze_pre h₁.args, squeeze_pre h₂.args, ?_,
    ?_, ?_, ?_, ?_, (env_pub hq h₁.env h₂.env).2.2.2⟩
  · simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
      ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp),
      h₁.args.rdi, h₂.args.rdi, h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx,
      h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8, h₁.args.r9, h₂.args.r9,
      hq.scr, at_pub hq, (env_pub hq h₁.env h₂.env).2.2.2, and_self]
  · exact (cov_more (hok σ₁ p₁) ho h₁.env).1
  · exact (cov_more (hok σ₁ p₁) ho h₁.env).2
  · exact (cov_more (hok σ₂ p₂) ho h₂.env).1
  · exact (cov_more (hok σ₂ p₂) ho h₂.env).2

end

end VG.Proof.MlDsa.X86_64.Sample.SpongeStream
