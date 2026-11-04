module

public import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CTReady
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CopyDigest
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CTReady
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.CopyDigest
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedKey
import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Spec.Ed25519.ExpandedKey
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-! Merged from `Proof.Ed25519.X86.PublicKey.CT`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value setup)
variable {n : Nat}

def Two (n : Nat) (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Ctx n s₁ a ∧ Ctx n s₂ b ∧ P s₁ a ∧ P s₂ b

variable {s₁ s₂ : State}

theorem esp_eq (pub : pkPub s₁ s₂) : esp s₁ = esp s₂ := congrArg (· - BitVec.ofNat 32 256) pub.1

theorem argValue_eq (pub : pkPub s₁ s₂) {v : Value} (hv : Whole.valid 3 v) : argValue s₁ v = argValue s₂ v := by
  cases v with
  | const _ => rfl
  | frame d => exact congrArg (· + BitVec.ofNat 32 d) (esp_eq pub)
  | caller i d =>
    apply congrArg (· + BitVec.ofNat 32 d)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by change i < 3 at hv; omega) with rfl | rfl | rfl
    · exact pub.2.1
    · exact pub.2.2.1
    · exact pub.2.2.2.1

theorem two_esp (pub : pkPub s₁ s₂) {P : State → State → Prop} {a b : State} (h : Two n s₁ s₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans ((esp_eq pub).trans h.2.1.esp.symm)

theorem two_wp (h₁ : Facts n s₁) (h₂ : Facts n s₂) {P Q : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two n s₁ s₂ P) c fun _ _ => True)
    (hw : ∀ s t, Facts n s → Ctx n s t → P s t → WP isa c t fun u => Ctx n s u ∧ Q s u) :
    RelCT isa (Two n s₁ s₂ P) c (Two n s₁ s₂ Q) :=
  (hct.wp fun a b h => ⟨hw s₁ a h₁ h.1 h.2.2.1, hw s₂ b h₂ h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two n s₁ s₂ fun _ _ => True) (.block (setup 0 vs)) (Two n s₁ s₂ (Slots vs)) :=
  two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) ht) fun _ _ h hc _ =>
    WP.mono (setup_ok h hc hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {a b : State} (h : Two n s₁ s₂ (Slots vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  rw [Whole.call_arg h.1.esp h₁.toBounds.call (by have := h₁.toBounds.frame; omega) (by omega),
    Whole.call_arg h.2.1.esp h₂.toBounds.call (by have := h₂.toBounds.frame; omega) (by omega),
    h.2.2.1 j hj, h.2.2.2 j hj]
  exact argValue_eq pub (hv _ (List.getElem_mem hj))

theorem call_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {s t : State}, Facts n s → Ctx n s t → Slots vs s t →
      Whole.CallReady k (esp s) (pkRd n s) (pkWr s) t)
    (kp : ∀ (a b : State) ar aw br bw, a.gpr .esp = b.gpr .esp →
      (∀ j < vs.length, arg a.callEntry j = arg b.callEntry j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two n s₁ s₂ (Slots vs)) (.call name c) (Two n s₁ s₂ fun _ _ => True) := by
  apply two_wp h₁ h₂
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h₁ h.1 h.2.2.1
    let rb := ready h₂ h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (two_esp pub h) (fun _ hj => call_args_eq h₁ h₂ pub hn hv h hj),
      ca, wa, cb, wb, two_esp pub h⟩
  · intro s t h hc hs
    exact WP.mono ((ready h hc hs).wp hc correct sp stack h.toBounds.call) fun _ hu => ⟨hu, trivial⟩

/-- `Two`, with each state naming the statics its entry names. -/
def TwoS (n : Nat) (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Two n s₁ s₂ P a b ∧ a.syms = s₁.syms ∧ b.syms = s₂.syms

theorem two_syms {P Q : State → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two n s₁ s₂ P) c (Two n s₁ s₂ Q)) : RelCT isa (TwoS n s₁ s₂ P) c (TwoS n s₁ s₂ Q) := by
  intro a b ta tb a' b' ⟨hp, ya, yb⟩ ea eb
  obtain ⟨e, q⟩ := h _ _ _ _ _ _ hp ea eb
  exact ⟨e, q, (Exec.syms ea).trans ya, (Exec.syms eb).trans yb⟩

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
variable {n : Nat}

variable {s₁ s₂ : State}

theorem base_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) :
    RelCT isa (TwoS n s₁ s₂ (Slots baseValues)) (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (TwoS n s₁ s₂ fun _ _ => True) := by
  have hct : RelCT isa (TwoS n s₁ s₂ (Slots baseValues))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) fun _ _ => True := by
    refine Whole.callEx scalarBase_ok scalarBase_ct fun a b h => ?_
    let ra := base_ready h₁ h.1.1 h.2.1 h.1.2.2.1
    let rb := base_ready h₂ h.1.2.1 h.2.2 h.1.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.1.2.1
    have hj := fun j (hj : j < baseValues.length) =>
      call_args_eq h₁ h₂ pub (by decide) (Whole.valid_all (by decide)) h.1 hj
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre, ⟨congrArg (· - 4) (two_esp pub h.1),
      hj 0 (by decide), hj 1 (by decide), hj 2 (by decide), ?_⟩, ca, wa, cb, wb, two_esp pub h.1⟩
    change a.syms _ = b.syms _
    rw [h.2.1, h.2.2]
    exact pub.2.2.2.2
  have fw : ∀ (u₀ u : State), Facts n u₀ → Ctx n u₀ u → u.syms = u₀.syms → Slots baseValues u₀ u →
      WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) u
        (fun v => Ctx n u₀ v ∧ v.syms = u₀.syms) := fun u₀ u hf hc hy hs =>
    WP.mono_syms ((base_ready hf hc hy hs).wp hc scalarBase_ok base_nosp (by rw [base_stack]; decide)
      hf.toBounds.call) fun _ hv yv => ⟨hv, yv.trans hy⟩
  exact (hct.wp fun a b h => ⟨fw s₁ a h₁ h.1.1 h.2.1 h.1.2.2.1, fw s₂ b h₂ h.1.2.1 h.2.2 h.1.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨⟨h.2.1.1, h.2.2.1, trivial, trivial⟩, h.2.1.2, h.2.2.2⟩

theorem prune_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) : RelCT isa (Two n s₁ s₂ fun _ _ => True) (.block prune) (Two n s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by native_taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (prune_step h hc (digest := Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64) rfl)
    fun _ hu => ⟨hu.1, trivial⟩

theorem wipe_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) : RelCT isa (Two n s₁ s₂ fun _ _ => True) (.block wipe) (Two n s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by native_taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun _ hu => ⟨hu.1, trivial⟩

/-- The frame's body after any `first` whose runs are related. -/
theorem bodyFrom_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) {first : Prog isa}
    (hh : RelCT isa (TwoS n s₁ s₂ fun _ _ => True) first (TwoS n s₁ s₂ fun _ _ => True)) :
    RelCT isa (TwoS n s₁ s₂ fun _ _ => True) (bodyFrom first) (TwoS n s₁ s₂ fun _ _ => True) := by
  have b := setup_ct h₁ h₂ pub baseValues (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  exact hh.seq ((two_syms (prune_ct h₁ h₂ pub)).seq (((two_syms b).seq (base_ct h₁ h₂ pub)).seq
      (two_syms (wipe_ct h₁ h₂ pub))))

/-- The frame around `bodyFrom first`, for any `first` whose runs are related. -/
theorem frame_ct {post : State → State → Prop} {first : Prog isa}
    (hh : ∀ {s₁ s₂ : State}, Facts n s₁ → Facts n s₂ → pkPub s₁ s₂ →
      RelCT isa (TwoS n s₁ s₂ fun _ _ => True) first (TwoS n s₁ s₂ fun _ _ => True)) :
    ConstantTime isa (pkLocalWith n post).pre pkPub
      (.frame (.push (List.replicate 64 .eax)) (bodyFrom first) (.pop .eax 64)) := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have f₁ := facts p₁
  have f₂ := facts p₂
  exact ⟨(bodyFrom_ct f₁ f₂ hp (hh f₁ f₂ hp) _ _ _ _ _ _
    ⟨⟨push_ctx p₁, push_ctx p₂, trivial, trivial⟩, rfl, rfl⟩ ea eb).1, trivial⟩

/-! ## The copy of the cached digest -/

/-- The digest's bytes: the 64 bytes at the second argument, apart from the frame. -/
theorem digest_disjoint {s : State} (h : Facts 64 s) :
    Region.Disjoint ⟨(arg s 1).setWidth 64, 64⟩ ⟨(esp s).setWidth 64 + BitVec.ofNat 64 192, 64⟩ :=
  h.ks.symm.sub_right fun p hp => Whole.frame_sub (esp s) p (Offset.sub_base _ (by decide) p hp)

/-- `copyExpanded` leaves the 64 bytes at the second argument at frame offset 192. -/
theorem copy_ok {s t : State} (h : Facts 64 s) (hc : Ctx 64 s t) :
    WP isa copyExpanded t fun u => Ctx 64 s u ∧
      Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 =
        Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 := by
  refine WP.mono (Whole.copyExpanded_ok hc (by have := h.toBounds.frame; omega)
    (original_arg_readable h hc (j := 1) (by decide)) (original_arg h hc (j := 1) (by decide)) h.seed
    (by rw [hc.rd]; exact List.mem_append_left _ List.mem_cons_self) (digest_disjoint h))
    fun u ⟨hu, hb⟩ => ⟨hu, hb.trans (seed_same h hc)⟩

theorem copy_ct (h₁ : Facts 64 s₁) (h₂ : Facts 64 s₂) (pub : pkPub s₁ s₂) :
    RelCT isa (TwoS 64 s₁ s₂ fun _ _ => True) copyExpanded (TwoS 64 s₁ s₂ fun _ _ => True) := by
  have p : RelCT isa (Two 64 s₁ s₂ fun _ _ => True) (.block copyPtr)
      (Two 64 s₁ s₂ fun s u => u.gpr .ecx = arg s 1) :=
    two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by native_taint_decide)) fun s t h hc _ =>
      WP.mono (Whole.copyPtr_ok hc (original_arg_readable h hc (j := 1) (by decide)))
        fun _ ⟨hu, _, he⟩ => ⟨hu, he.trans (original_arg h hc (j := 1) (by decide))⟩
  have w : RelCT isa (Two 64 s₁ s₂ fun s u => u.gpr .ecx = arg s 1) (.block copyDigestWords)
      (Two 64 s₁ s₂ fun _ _ => True) := by
    refine two_wp h₁ h₂ (RelCT.taint (A := taint) (τr [.esp, .ecx]) (fun a b h => agree_regs fun r hr => ?_)
      (by native_taint_decide)) fun s t h hc he =>
        WP.mono (Whole.copyWords_ok hc (by have := h.toBounds.frame; omega) he h.seed
          (by rw [hc.rd]; exact List.mem_append_left _ List.mem_cons_self) (digest_disjoint h))
          fun _ hu => ⟨hu.1, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact two_esp pub h
    · exact h.2.2.1.trans (pub.2.2.1.trans h.2.2.2.symm)
  exact two_syms (p.seq w)

theorem copy_nosp : NoSp copyExpanded := NoSp.of_all (by decide +kernel)

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.PublicKey
materialize_code publicKeyExpanded
end VG.Impl.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Contract`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym combConsts)
variable {n : Nat}

def pkWideWith (n : Nat) (post : State → State → Prop) : Contract isa := { pkLocalWith n post with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, n⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, TBL ((s.syms combSym).setWidth 64)] ∧ s.wr = [out, scratch, args] ∧
      out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + n ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ CombHeld s [out, scratch, stack]
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

theorem pkWide_pre {post : State → State → Prop} (s : State) (h : (pkWideWith n post).pre s) :
    (pkLocalWith n post).pre (s.withRegions (pkRd n s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na, held⟩ := h
  simp only [pkLocalWith, pkRd, pkWr, arg_withRegions, argAddr_withRegions, State.withRegions_syms,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, below,
    Taint.sub_setWidth nb, CombHeld]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na, held⟩

end VG.Proof.Ed25519.X86.PublicKey
end

/-! ## Derivation from the seed's cached digest -/

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86 (combSym combConsts)
open VG.Proof.Ed25519 (sha512_length)

/-- The public key of every seed whose SHA-512 digest is at the second argument. -/
def pkPostE (s t : State) : Prop :=
  ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.publicKey seed

def pkLocalE : Contract isa := pkLocalWith 64 pkPostE
def pkWideE : Contract isa := pkWideWith 64 pkPostE

theorem publicKeyExpanded_ok {s : State} (h : pkLocalE.pre s) :
    WP isa publicKeyExpanded s fun t => abiPreserved s t ∧ pkLocalE.post s t :=
  frame_ok h copy_nosp (bodyFrom_ok (t := pushed (List.replicate 64 .eax) s) (facts h) rfl
    (copy_ok (facts h) (push_ctx h)))
    fun _ ht _ _ hE => ht.trans (congrArg (fun d =>
      Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune d) Spec.Ed25519.basePoint)) hE)

theorem publicKeyExpanded_ct : ConstantTime isa pkLocalE.pre pkLocalE.pub publicKeyExpanded :=
  frame_ct fun h₁ h₂ pub => copy_ct h₁ h₂ pub

def satSeedE : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satDigestE : List Byte := Spec.Sha512.sha512 satSeedE

theorem satSeedE_length : satSeedE.length = 32 := by
  simp only [satSeedE, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

/-- `pkSatMem`, with the digest at `0x2000`. -/
def pkSatMemE : Mem := fun a =>
  if a.toNat < 0x2000 then 0 else if a.toNat < 0x2040 then satDigestE[a.toNat - 0x2000]?.getD 0
  else pkSatMem a

def pkSatStateE : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith pkSatMemE
  rd := [⟨0x2000, 64⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]
  syms _ := 0x100000

theorem pkSatE_arg (j : Nat) (hj : j < 3) :
    arg pkSatStateE j = pkSatMemE.readW (argAddr pkSatStateE j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith pkSatMemE _ = _
  rw [satMemWith_out]
  have : ∀ j < 3, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr pkSatStateE j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega)

theorem satE_digest : Spec.Ed25519.bytesAt (satMemWith pkSatMemE) 0x2000 64 = satDigestE := by
  have out : ∀ i < 64, 8 * 32 * 96 ≤ ((0x2000 : Addr) + BitVec.ofNat 64 i - 0x100000).toNat := by
    decide
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigestE, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range]
    rw [satMemWith_out _ (out i hi')]
    unfold pkSatMemE
    simp only [ha, show ¬ 0x2000 + i < 0x2000 from by omega, ite_false,
      show 0x2000 + i < 0x2040 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem pkE_sat :
    (Spec.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280).pre pkSatStateE := by
  have hl := combWords_length
  have a0 : arg pkSatStateE 0 = 0x1000 := (pkSatE_arg 0 (by decide)).trans (by decide)
  have a1 : arg pkSatStateE 1 = 0x2000 := (pkSatE_arg 1 (by decide)).trans (by decide)
  have a2 : arg pkSatStateE 2 = 0x4000 := (pkSatE_arg 2 (by decide)).trans (by decide)
  have held : TblWords ((pkSatStateE.syms combSym).setWidth 64) pkSatStateE.mem :=
    satMemWith_held pkSatMemE
  have key : Spec.Ed25519.bytesAt pkSatStateE.mem ((0x2000 : BitVec 32).setWidth 64) 64 =
      Spec.Sha512.sha512 satSeedE := satE_digest
  generalize e : pkSatStateE = s
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, by decide, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | exact ⟨satSeedE, satSeedE_length, key⟩ |
      decide

theorem pkWideE_implies :
    pkWideE.Implies (Spec.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280) where
  pre s h := by
    sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h280, hsp, hd, held, hfit, hdw, -, hstk, -, ht, hw, os, oc, oa, sc, -, ca, ro, -, rc, -,
      ko, ks, kc, -, f0, f1, f2, -⟩ := h
    refine ⟨?_, hw, os, oc, sc, oa.symm, ca.symm, ro, rc, ko, ks, kc, f0, f1, f2, h280, by omega,
      held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hstk
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨pkSatStateE, pkE_sat⟩

theorem publicKeyExpanded_verified :
    Verified X86.target publicKeyExpanded
      (Spec.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280) := by
  have hsat := pkWideE_implies.sat_left
  have satLocal : ∃ s, pkLocalE.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target publicKeyExpanded pkLocalE :=
    Verified.of_correct (fun _ h => publicKeyExpanded_ok h) publicKeyExpanded_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal (pkRd 64) pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWideE_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl) <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWideE, pkWideWith, pkLocalE, pkLocalWith, pkPostE, arg_withRegions,
      State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWideE, pkWideWith, pkLocalE, pkLocalWith, pkPub, arg_withRegions, State.withRegions_gpr,
      State.withRegions_syms] using h

end VG.Proof.Ed25519.X86.PublicKey
