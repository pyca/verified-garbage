module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CallOpen
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
meta import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.Framework.EntryBranch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CallOpen
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT

/-! # Shared small-message fallbacks, with their argument and stack frames -/

@[expose] public section
namespace VG.Proof.ChaCha20Poly1305.X86_64.Shared
open VG VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.Shared
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64 (XorImpl)
open VG.Impl.ChaCha20Poly1305.X86_64.Stitch (smallLim winLo winHi ifmaLo ifmaHi)

/-- Public contracts, including the extra forwarding frame and return address. -/
def contract (enc : Bool) (stack : Nat) : Contract isa :=
  if enc then Spec.ChaCha20Poly1305.sealContract abi stack
  else Spec.ChaCha20Poly1305.openZeroContract abi stack

theorem sat (enc : Bool) : ∃ s, (contract enc 1768).pre s := by
  cases enc
  · implies_sat [contract, Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
      Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, abi, argRegs]
      [openFrameSat, openSat] using openFrameSat
  · implies_sat [contract, Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Spec.ChaCha20Poly1305.sealPost, abi, argRegs] [sealFrameSat, sealSat] using sealFrameSat

/-- A larger reserved stack area implies the existing framed contract. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (h : (sig.contract abi pre post wa 1768 leak).pre s) :
    (sig.contract abi pre post wa 1752 leak).pre s := by
  rw [pre_args hk] at h ⊢
  obtain ⟨⟨hs, hwf⟩, hr, hw, hp, hd, hb, ht⟩ := h
  refine ⟨⟨?_, hwf⟩, hr, hw, hp, ?_, hb, ht⟩
  · right; rcases hs with hs | hs <;> omega
  · intro r hr a ha
    simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd _ (by simp) a ha
    · exact (hd (below (s.gpr .rsp) 1768) (by simp [stackBelow]) a ha).sub_left
        (below_sub (a := 1752) (b := 1768) (by decide) (by decide))

theorem pre_old (enc : Bool) {s : State} (h : (contract enc 1768).pre s) :
    (contract enc 1752).pre s := by
  cases enc
  · exact pre_stack (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h
  · exact pre_stack (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (leak := none) (by decide) h

theorem widen {c : Prog isa} (h : Verified target c (contract true 1752)) :
    Verified target c (contract true 1768) :=
  h.of_implies ⟨fun _ hp => pre_old true hp, fun _ _ _ hp => hp, fun _ _ _ _ hp => hp, sat true⟩

/-! ## `seal` -/

theorem body_verified (v : XorImpl) : Verified target (body v.callee v.poly) (contract true 1752) := by
  by_cases hv : v.poly = .avx2
  · have h := sealS_framed v hv
    simpa only [body, framed, contract, ↓reduceIte, hv] using h
  · simpa only [body, framed, contract, ↓reduceIte, hv] using seal_framed v

theorem body_sp (v : XorImpl) : (body v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  apply withStackArgScratchWipedX_spSafe
  by_cases hv : v.poly = .avx2
  · have h := sealS_spSafe v hv
    simpa only [↓reduceIte, hv] using h
  · simpa only [↓reduceIte, hv] using seal_spSafe v

theorem body_depth (v : XorImpl) : (body v.callee v.poly).x86_64Depth ≤ 1752 := by
  have hd : (if v.poly = .avx2 then Impl.ChaCha20Poly1305.X86_64.Stitch.sealStitched
        { v.callee with pass := 512 } .avx2 else Impl.ChaCha20Poly1305.X86_64.«seal» v.callee v.poly).x86_64Depth
        ≤ 24 := by
    by_cases hv : v.poly = .avx2
    · simpa only [↓reduceIte, hv] using sealS_xdepth v
    · simpa only [↓reduceIte, hv] using seal_xdepth v
  change max _ 0 + 1728 ≤ 1752
  rw [Nat.max_zero]
  exact Nat.add_le_add_right hd 1728

theorem call_sp (v : XorImpl) : (bodyCall v.callee v.poly).all (fun i => !isa.writesSp i) = true :=
  forward_spSafe (body_sp v)

theorem call_depth (v : XorImpl) : (bodyCall v.callee v.poly).x86_64Depth ≤ 1768 := by
  change max 0 (_ + 8) + 8 ≤ 1768
  rw [Nat.zero_max]
  exact Nat.add_le_add_right (Nat.add_le_add_right (body_depth v) 8) 8

theorem call_verified (v : XorImpl) : Verified target (bodyCall v.callee v.poly) (contract true 1768) :=
  Verified.forward (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8) (leak := none)
    (show Verified target _ (Spec.ChaCha20Poly1305.sealContract abi 1752) from body_verified v)
    (by decide) (by decide) (by decide) (by decide) (body_sp v) (body_depth v)
    (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp)
    (fun vs m₁ m₂ m' r hl hb _ hp => sealPost_local _ vs m₁ m₂ m' r hl hb hp) (sat true)

theorem small_verified (v : XorImpl) (hv : v.poly = .avx2) :
    Verified target (smallCall v.callee) (contract true 1768) := by
  have h := call_verified v
  rwa [hv] at h

theorem large_sp (v : XorImpl) (hv : v.poly = .avx512) :
    (largeCode v.callee).all (fun i => !isa.writesSp i) = true := by
  have h := body_sp v
  rw [hv] at h
  have hc := call_sp v
  rw [hv] at hc
  unfold largeCode
  split
  · simpa only [body, reduceCtorEq, ↓reduceIte] using h
  · exact hc

theorem large_depth (v : XorImpl) (hv : v.poly = .avx512) :
    (largeCode v.callee).x86_64Depth ≤ 1768 := by
  have h := body_depth v
  rw [hv] at h
  have hc := call_depth v
  rw [hv] at hc
  unfold largeCode
  split
  · have h' := Nat.le_trans h (show 1752 ≤ 1768 by decide)
    simpa only [body, reduceCtorEq, ↓reduceIte] using h'
  · exact hc

theorem large_verified (v : XorImpl) (hv : v.poly = .avx512) :
    Verified target (largeCode v.callee) (contract true 1768) := by
  have h := widen (body_verified v)
  rw [hv] at h
  have hc := call_verified v
  rw [hv] at hc
  unfold largeCode
  split
  · simpa only [body, reduceCtorEq, ↓reduceIte] using h
  · exact hc

/-! The entry comparison changes no arguments, buffer, or calling-convention state. -/

theorem flags_args {s t : State} (h : FlagsOnly s t) (sig : Sig) :
    allArgs sig t = allArgs sig s := by
  simp only [allArgs, argRegs, List.map_cons, List.map_nil, h.rdi, h.rsi, h.rdx,
    h.rcx, h.r8, h.r9]
  rw [show stackArg t = stackArg s from funext h.arg]

theorem flags_regions {s t : State} (h : FlagsOnly s t) (sig : Sig) :
    allRegions sig t = allRegions sig s := by
  simp only [allRegions, bufRegions, argArea, flags_args h, h.mem, h.argAddr]

theorem flags_pre_sig {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s t : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (h : FlagsOnly s t)
    (hp : (sig.contract abi pre post wa stack leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre t := by
  rw [pre_args hk] at hp ⊢
  simpa only [flags_args h, flags_regions h, h.rsp, h.mem, h.rd, h.wr,
    bufRegions] using hp

theorem flags_pre (enc : Bool) {stack : Nat} {s t : State} (h : FlagsOnly s t)
    (hp : (contract enc stack).pre s) : (contract enc stack).pre t := by
  cases enc
  · exact flags_pre_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h hp
  · exact flags_pre_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (leak := none) (by decide) h hp

theorem flags_post_sig {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s t z : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (h : FlagsOnly s t)
    (hp : (sig.contract abi pre post wa stack leak).post t z) :
    (sig.contract abi pre post wa stack leak).post s z := by
  rw [post_args hk] at hp ⊢
  simpa only [flags_args h, h.mem] using hp

theorem flags_pub_sig {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ t₁ t₂ : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (h₁ : FlagsOnly s₁ t₁) (h₂ : FlagsOnly s₂ t₂)
    (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂) :
    (sig.contract abi pre post wa stack leak).pub t₁ t₂ := by
  rw [pubL_args hk] at hp ⊢
  simpa only [flags_args h₁, flags_args h₂, h₁.rsp, h₂.rsp, h₁.mem, h₂.mem] using hp

theorem flags_post (enc : Bool) {stack : Nat} {s t z : State} (h : FlagsOnly s t)
    (hp : (contract enc stack).post t z) : (contract enc stack).post s z := by
  cases enc
  · exact flags_post_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (stack := stack) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h hp
  · exact flags_post_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (stack := stack) (leak := none) (by decide) h hp

theorem flags_pub (enc : Bool) {stack : Nat} {s₁ s₂ t₁ t₂ : State} (h₁ : FlagsOnly s₁ t₁)
    (h₂ : FlagsOnly s₂ t₂) (hp : (contract enc stack).pub s₁ s₂) : (contract enc stack).pub t₁ t₂ := by
  cases enc
  · exact flags_pub_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (stack := stack) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h₁ h₂ hp
  · exact flags_pub_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (stack := stack) (leak := none) (by decide) h₁ h₂ hp

theorem pub_len (enc : Bool) {stack : Nat} {s t : State} (h : (contract enc stack).pub s t) :
    s.gpr .r9 = t.gpr .r9 := by
  cases enc
  · simp only [contract, Bool.false_eq_true, ↓reduceIte] at h
    rw [Spec.ChaCha20Poly1305.openZeroContract, pubL_args (by decide)] at h
    have hh := h.2.1 5 (by decide)
    change (s.gpr .r9).setWidth 64 = (t.gpr .r9).setWidth 64 at hh
    simpa only [BitVec.setWidth_eq] using hh
  · simp only [contract, ↓reduceIte] at h
    rw [Spec.ChaCha20Poly1305.sealContract, pubL_args (by decide)] at h
    have hh := h.2.1 5 (by decide)
    change (s.gpr .r9).setWidth 64 = (t.gpr .r9).setWidth 64 at hh
    simpa only [BitVec.setWidth_eq] using hh

/-- A public length choice between two framed implementations of the same
contract `k`, which the comparison (changing only the flags, `rax` and
`r10`) keeps, and whose public data includes the length, `r9`. -/
theorem chooseK {k : Contract isa}
    (hpre : ∀ s t, FlagsOnly s t → k.pre s → k.pre t)
    (hpost : ∀ s t z, FlagsOnly s t → k.post t z → k.post s z)
    (hpub : ∀ s₁ s₂ t₁ t₂, FlagsOnly s₁ t₁ → FlagsOnly s₂ t₂ → k.pub s₁ s₂ → k.pub t₁ t₂)
    (hlen : ∀ s t, k.pub s t → s.gpr .r9 = t.gpr .r9) (hsat : ∃ s, k.pre s)
    {b : List Instr} {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified target a k) (hc : Verified target c k)
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified target (.seq (.block b) (Code.iteCold .b a c)) k := by
  have cmp (s : State) : ∃ u, execBlock isa b s = some (u, []) ∧
      isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u := by
    obtain ⟨t, u, he, hp⟩ := hb s
    have e := Exec.block_eq (T := target) he
    have hn := execBlock_trace_nil ht e
    exact ⟨u, hn ▸ e, hp⟩
  refine Verified.entryBranch (p := fun s => p (s.gpr .r9)) (fun _ => []) ha hc ?_ ?_ hsat
  · intro s hs
    obtain ⟨u, he, hp, hf⟩ := cmp s
    exact ⟨u, he, hp, fun _ => ⟨hpre _ _ hf hs,
      fun _ hA hP => ⟨hf.abi hA, hpost _ _ _ hf hP⟩⟩,
      fun _ => ⟨hpre _ _ hf hs, fun _ hA hP => ⟨hf.abi hA, hpost _ _ _ hf hP⟩⟩⟩
  · intro s t u v _ _ hp eu ev
    obtain ⟨u', eu', _, hf⟩ := cmp s
    obtain ⟨v', ev', _, hg⟩ := cmp t
    have ee := Option.some.inj (eu.symm.trans eu')
    have ef := Option.some.inj (ev.symm.trans ev')
    obtain rfl := (Prod.mk.inj ee).1
    obtain rfl := (Prod.mk.inj ef).1
    exact ⟨rfl, congrArg p (hlen _ _ hp), fun _ => hpub _ _ _ _ hf hg hp,
      fun _ => hpub _ _ _ _ hf hg hp⟩

/-- A public length choice between two framed implementations of the same API. -/
theorem choose (enc : Bool) {stack : Nat} (hsat : ∃ s, (contract enc stack).pre s) {b : List Instr}
    {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified target a (contract enc stack)) (hc : Verified target c (contract enc stack))
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified target (.seq (.block b) (Code.iteCold .b a c)) (contract enc stack) :=
  chooseK (fun _ _ hf hs => flags_pre enc hf hs) (fun _ _ _ hf hP => flags_post enc hf hP)
    (fun _ _ _ _ hf hg hp => flags_pub enc hf hg hp) (fun _ _ hp => pub_len enc hp) hsat ha hc hb ht

/-- The dispatch tests access no memory. -/
theorem small_trace (lim : Nat) : ∀ i ∈ Impl.ChaCha20Poly1305.X86_64.Stitch.smallTest lim,
    ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [Impl.ChaCha20Poly1305.X86_64.Stitch.smallTest, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem window_trace : ∀ i ∈ Impl.ChaCha20Poly1305.X86_64.Stitch.ifmaTest,
    ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [Impl.ChaCha20Poly1305.X86_64.Stitch.ifmaTest, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem seal_verified (v : XorImpl) :
    Verified target (sealCode v.callee v.poly) (contract true 1768) := by
  cases hb : v.poly with
  | avx512 =>
    have hs := small_verified v.small v.small_poly
    rw [XorImpl.small_callee] at hs
    have hg := large_verified v hb
    exact choose true (sat true) (p := fun n => decide (n.toNat < smallLim v.callee.small.vl ∨
      (winLo ≤ n.toNat ∧ n.toNat < winHi))) hs hg (fun s => cmpSmall_ok v.callee.small.vl s) (small_trace _)
  | _ =>
    have h := call_verified v
    rw [hb] at h
    exact h

theorem seal_sp (v : XorImpl) : (sealCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := call_sp v
  have hg : v.poly = .avx512 → (largeCode v.callee).all (fun i => !isa.writesSp i) = true := large_sp v
  have hs := call_sp v.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  change (smallCall v.callee.small).all (fun i => !isa.writesSp i) = true at hs
  cases hb : v.poly with
  | avx512 =>
    have hg := hg hb
    simp only [sealCode, Code.iteCold, Code.all, hs, hg, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | _ => rw [hb] at ho; exact ho

theorem seal_depth (v : XorImpl) : (sealCode v.callee v.poly).x86_64Depth ≤ 1768 := by
  have ho := call_depth v
  have hs := call_depth v.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  cases hb : v.poly with
  | avx512 =>
    have hg := large_depth v hb
    simp only [sealCode, Code.iteCold, Code.x86_64Depth, Nat.max_le]
    exact ⟨by decide, ⟨⟨by decide, by decide⟩, hs⟩, hg⟩
  | _ => rw [hb] at ho; exact ho

/-! ## `open`

`open`, in its frame of `work`, loads the arguments of the body and calls it
(`openCall`), as `open_to` does (`OpenTo.lean`): from `open`'s precondition
with the 56 bytes of stack the call uses (`openPre`), the state after the
loads satisfies what the call needs (`ocpre_of`: `CallOpen.CPre`), with the
data as the ciphertext. -/

/-- `open`'s precondition (`preX86_64 false`), with the 56 bytes of stack
below the return address that the call uses. -/
def openPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .rdi, 32⟩
  let nonce : Region := ⟨s.gpr .rsi, 12⟩
  let aad : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1696⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stack : Region := ⟨s.gpr .rsp - 56, 56⟩
  s.rd = [key, nonce, aad, tag, args] ∧ s.wr = [data, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧ data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  ret.Disjoint work ∧ ret.Disjoint data ∧
  stack.Disjoint work ∧ stack.Disjoint key ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧
  stack.Disjoint data ∧ stack.Disjoint tag ∧
  (stackArg s 1).toNat + 1696 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
  (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64 ∧ 56 ≤ (s.gpr .rsp).toNat

/-- `open` in its frame of `work`, as the proofs state it. -/
def openK : Contract isa where
  pre := openPre
  post := openX86_64.post
  pub := openX86_64.pub

/-- After `openArgs`: the data's address, `work` and `tag` in `r11`, `rax`
and `r10`. -/
structure OLoaded (s h : State) : Prop where
  r11 : h.gpr .r11 = s.gpr .r8
  rax : h.gpr .rax = stackArg s 1
  r10 : h.gpr .r10 = stackArg s 0
  keep : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → h.gpr r = s.gpr r
  mem : h.mem = s.mem
  rd : h.rd = s.rd
  wr : h.wr = s.wr
  mx : h.mxcsr = s.mxcsr

theorem openArgs_ok {s : State} (hs : openPre s) : WP isa (.block openArgs) s (OLoaded s) := by
  obtain ⟨hrd, -⟩ := hs
  have hg : ∀ k, k + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 + k)) 8 := by
    intro k hk
    refine ⟨⟨stackArgAddr s 0, 16⟩, by rw [hrd]; simp, ?_⟩
    rw [off_eq, show s.gpr .rsp + BitVec.ofNat 64 (8 + k) = stackArgAddr s 0 + BitVec.ofNat 64 k by
      simp only [stackArgAddr, BitVec.ofNat_add, BitVec.add_assoc]]
    exact Offset.contains_base _ hk (by omega)
  have h16 := hg 8 (by omega)
  have h8 := hg 0 (by omega)
  simp only [show 8 + 8 = 16 from rfl, show 8 + 0 = 8 from rfl] at h16 h8
  have e16 : s.mem.readW (off (s.gpr .rsp) 16) 64 = stackArg s 1 := by
    simp only [stackArg, stackArgAddr, off_eq]
  have e8 : s.mem.readW (off (s.gpr .rsp) 8) 64 = stackArg s 0 := by
    simp only [stackArg, stackArgAddr, off_eq]
  apply WP.of_runBlock
  simp only [openArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, ↓reduceIte, h16, h8,
    e16, e8, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [RegUpd.gpr_setReg], by simp [RegUpd.gpr_setReg], by simp [RegUpd.gpr_setReg],
    fun r h₁ h₂ h₃ => by simp [RegUpd.gpr_setReg, h₁, h₂, h₃], by simp [RegUpd.mem_setReg],
    by simp [RegUpd.rd_setReg], by simp [RegUpd.wr_setReg], by simp [RegUpd.mxcsr_setReg]⟩

namespace OLoaded

variable {s h : State} (hh : OLoaded s h)
include hh

theorem rsp : h.gpr .rsp = s.gpr .rsp := hh.keep _ (by decide) (by decide) (by decide)
theorem rdi : h.gpr .rdi = s.gpr .rdi := hh.keep _ (by decide) (by decide) (by decide)
theorem rsi : h.gpr .rsi = s.gpr .rsi := hh.keep _ (by decide) (by decide) (by decide)
theorem rdx : h.gpr .rdx = s.gpr .rdx := hh.keep _ (by decide) (by decide) (by decide)
theorem rcx : h.gpr .rcx = s.gpr .rcx := hh.keep _ (by decide) (by decide) (by decide)
theorem r8 : h.gpr .r8 = s.gpr .r8 := hh.keep _ (by decide) (by decide) (by decide)
theorem r9 : h.gpr .r9 = s.gpr .r9 := hh.keep _ (by decide) (by decide) (by decide)

theorem ek : CallOpen.hkR h = ⟨s.gpr .rdi, 32⟩ := by show (⟨h.gpr .rdi, 32⟩ : Region) = _; rw [hh.rdi]
theorem en : CallOpen.hnR h = ⟨s.gpr .rsi, 12⟩ := by show (⟨h.gpr .rsi, 12⟩ : Region) = _; rw [hh.rsi]
theorem ea : CallOpen.haR h = ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ := by
  show (⟨h.gpr .rdx, (h.gpr .rcx).toNat⟩ : Region) = _; rw [hh.rdx, hh.rcx]
theorem es : CallOpen.hsR h = ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
  show (⟨h.gpr .r11, (h.gpr .r9).toNat⟩ : Region) = _; rw [hh.r11, hh.r9]
theorem ed : CallOpen.hdR h = ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
  show (⟨h.gpr .r8, (h.gpr .r9).toNat⟩ : Region) = _; rw [hh.r8, hh.r9]
theorem et : CallOpen.htR h = ⟨stackArg s 0, 16⟩ := by show (⟨h.gpr .r10, 16⟩ : Region) = _; rw [hh.r10]
theorem ew : CallOpen.hwR h = ⟨stackArg s 1, 1696⟩ := by show (⟨h.gpr .rax, 1696⟩ : Region) = _; rw [hh.rax]
theorem eb : CallOpen.hstk h = ⟨s.gpr .rsp - 56, 56⟩ := by
  show (⟨h.gpr .rsp - BitVec.ofNat 64 56, 56⟩ : Region) = _; rw [hh.rsp]; rfl

end OLoaded

/-- The state after `openArgs` is ready for the call. -/
theorem ocpre_of {s h : State} (hs : openPre s) (hh : OLoaded s h) : CallOpen.CPre h := by
  obtain ⟨hrd, hwr, wk, wn, wa, wd, wt, dk, dn, da, dt, -, -, bw, bk, bn, ba, bd, bt, ow, oa, od, ot, ok, on,
    lo⟩ := hs
  refine ⟨by rw [hh.rsp]; exact lo, ?_, ?_, by rw [hh.ew, hh.ek]; exact wk, by rw [hh.ew, hh.en]; exact wn,
    by rw [hh.ew, hh.ea]; exact wa, by rw [hh.ew, hh.ed]; exact wd, by rw [hh.ew, hh.et]; exact wt,
    by rw [hh.ed, hh.ek]; exact dk, by rw [hh.ed, hh.en]; exact dn, by rw [hh.ed, hh.ea]; exact da,
    by rw [hh.ed, hh.et]; exact dt, by rw [hh.es, hh.ew]; exact wd.symm,
    .inl (by show h.gpr .r11 = h.gpr .r8; rw [hh.r11, hh.r8]),
    by rw [hh.eb, hh.ek]; exact bk, by rw [hh.eb, hh.en]; exact bn, by rw [hh.eb, hh.ea]; exact ba,
    by rw [hh.eb, hh.es]; exact bd, by rw [hh.eb, hh.ed]; exact bd, by rw [hh.eb, hh.et]; exact bt,
    by rw [hh.eb, hh.ew]; exact bw, by rw [hh.rdi]; exact ok, by rw [hh.rsi]; exact on,
    by rw [hh.rdx, hh.rcx]; exact oa, by show (h.gpr .r11).toNat + (h.gpr .r9).toNat ≤ _; rw [hh.r11, hh.r9]; exact od,
    by show (h.gpr .r8).toNat + (h.gpr .r9).toNat ≤ _; rw [hh.r8, hh.r9]; exact od,
    by show (h.gpr .r10).toNat + 16 ≤ _; rw [hh.r10]; exact ot,
    by show (h.gpr .rax).toNat + 1696 ≤ _; rw [hh.rax]; exact ow⟩
  · rw [hh.ek, hh.en, hh.ea, hh.et, hh.es, hh.rd, hh.wr, hrd, hwr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hh.ed, hh.ew, hh.wr, hwr]
    exact Covers.refl _

/-- The return address is apart from the stack below it. -/
theorem ret_stk (s : State) : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - 56, 56⟩ :=
  Offset.base_disjoint_below (n := 56) (k := 8) _ (by decide)

theorem openCall_correct (v : XorImpl) (s : State) (hs : openK.pre s) :
    ∃ t s', Exec isa (openCall v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ openK.post s s' := by
  have hs : openPre s := hs
  have rw' := hs.2.2.2.2.2.2.2.2.2.2.2
  refine WP.seq (WP.mono (openArgs_ok hs) fun h hh => ?_)
  refine WP.mono (CallOpen.callOpen_ok v (ocpre_of hs hh)) fun z hz => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [hz.cs r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hh.keep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · -- The return address: apart from the data, `work` and the stack.
    have hf := hz.mem
    simp only [CallOpen.hdR, CallOpen.hwR, CallOpen.hstk, CallOpen.hB, CallOpen.hD, CallOpen.hW, CallOpen.hL,
      hh.r8, hh.rax, hh.r9, hh.rsp, hh.mem] at hf
    exact hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rw'.2.1
      · exact rw'.1
      · exact ret_stk s) (by decide)
  · rw [hz.mx, hh.mx]
  · have hp := hz.post
    unfold CallOpen.hPost at hp
    show openX86_64.post s z
    simp only [openX86_64]
    rw [hh.mem, hh.rdi, hh.rsi, hh.rdx, hh.rcx, CallOpen.hS, CallOpen.hT, CallOpen.hD, CallOpen.hL, hh.r11,
      hh.r10, hh.r8, hh.r9] at hp
    exact hp

theorem openCall_ct (v : XorImpl) : ConstantTime isa openK.pre openK.pub (openCall v.callee v.poly) := by
  refine Gather.ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have p₁ : openPre σ₁ := p₁
  have p₂ : openPre σ₂ := p₂
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁⟩, ql⟩ := hq
  refine Gather.rel_seq (Gather.rel_regs [.rsp] (by simp [qsp]) ⟨_, by taint_decide⟩) (openArgs_ok p₁)
    (openArgs_ok p₂) fun h₁ h₂ hh₁ hh₂ => CallOpen.callOpen_rel v (ocpre_of p₁ hh₁) (ocpre_of p₂ hh₂)
      ⟨by rw [hh₁.rdi, hh₂.rdi, q₁], by rw [hh₁.rsi, hh₂.rsi, q₂], by rw [hh₁.rdx, hh₂.rdx, q₃],
        by rw [hh₁.rcx, hh₂.rcx, q₄], by rw [hh₁.r8, hh₂.r8, q₅], by rw [hh₁.r9, hh₂.r9, q₆],
        by rw [hh₁.r10, hh₂.r10, a₀], by rw [hh₁.r11, hh₂.r11, q₅],
        by rw [hh₁.rax, hh₂.rax, a₁], by rw [hh₁.rsp, hh₂.rsp, qsp], ?_⟩
  have leak : ∀ {σ h : State}, OLoaded σ h → CallOpen.hLeak h = openLeakX86_64 σ := fun {σ h} hh => by
    unfold CallOpen.hLeak openLeakX86_64
    rw [hh.mem, hh.rdi, hh.rsi, hh.rdx, hh.rcx, CallOpen.hS, CallOpen.hT, CallOpen.hL, hh.r11, hh.r10, hh.r9]
  rw [leak hh₁, leak hh₂, ql]

theorem openCall_verified (v : XorImpl) :
    Verified X86_64.target (openCall v.callee v.poly) (openZeroScratchContract X86_64.abi 212 56) :=
  Verified.of_correct (k := openK) (openCall_correct v) (openCall_ct v)
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakX86_64,
          Proof.ChaCha20Poly1305.openX86_64, openK, openPre,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, X86_64.argRegs]
        simp only [openK, Proof.ChaCha20Poly1305.openX86_64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakX86_64,
          Proof.ChaCha20Poly1305.openX86_64, openK, openPre,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakX86_64,
          Proof.ChaCha20Poly1305.openX86_64, openK, openPre,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
          [openSat] using openSat }

theorem openCall_spSafe (v : XorImpl) : (openCall v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  simp only [openCall, Code.all, CallOpen.callOpen_spSafe v, Bool.and_true]
  decide

theorem openCall_xdepth (v : XorImpl) : (openCall v.callee v.poly).x86_64Depth ≤ 56 := by
  have h := CallOpen.callOpen_xdepth v
  simp only [openCall, Code.x86_64Depth, Nat.max_le]
  exact ⟨Nat.zero_le _, h⟩

theorem sat_open : ∃ s, (contract false 1784).pre s := by
  implies_sat [contract, Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, abi, argRegs]
    [openFrameSat, openSat] using openFrameSat

/-- `open` of the instance calling the implementation `v` of
`vg_chacha20_xor`, without a choice by the length, in its frame of `work`. -/
theorem framed_verified (v : XorImpl) :
    Verified target (framed (openCall v.callee v.poly)) (contract false 1784) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.openZeroPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (leak := some (Spec.ChaCha20Poly1305.openLeak X86_64.abi.ptrBits))
    (bytes := 1728) (k := 42) (openCall_verified v) (by decide) (by decide) (by decide)
    (openCall_spSafe v) (openCall_xdepth v) (by decide) (pre_local _ _) (openZeroPost_local _)
    (openZeroPost_out _) sat_open (hleak := openLeak_local _)

theorem framed_sp (v : XorImpl) :
    (framed (openCall v.callee v.poly)).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratchWipedX_spSafe (openCall_spSafe v)

theorem open_verified (v : XorImpl) :
    Verified target (openCode v.callee v.poly) (contract false 1784) := by
  cases hb : v.poly with
  | avx512 =>
    have hs := framed_verified v.small
    rw [XorImpl.small_callee, v.small_poly] at hs
    have hg := framed_verified v
    rw [hb] at hg
    have heq : Impl.ChaCha20Poly1305.X86_64.Stitch.openLim v.callee.small.vl =
        Impl.ChaCha20Poly1305.X86_64.Stitch.smallLim v.callee.small.vl := rfl
    rw [openCode, heq]
    exact choose false sat_open (p := fun n => decide (n.toNat < smallLim v.callee.small.vl ∨
      (winLo ≤ n.toNat ∧ n.toNat < winHi))) hs hg (fun s => cmpSmall_ok v.callee.small.vl s) (small_trace _)
  | ifma =>
    have hs := framed_verified XorImpl.avx512vl.small
    rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hs
    have hg := framed_verified v
    rw [hb] at hg
    exact choose false sat_open (p := fun n => decide (ifmaLo ≤ n.toNat ∧ n.toNat < ifmaHi)) hs hg
      cmpWin_ok window_trace
  | _ =>
    have h := framed_verified v
    rw [hb] at h
    exact h

theorem open_sp (v : XorImpl) : (openCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := framed_sp v
  have hs := framed_sp v.small
  have hw := framed_sp XorImpl.avx512vl.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hw
  change (framed (openCall Impl.ChaCha20.X86_64.Callee.avx512vl.small .avx2)).all
    (fun i => !isa.writesSp i) = true at hw
  cases hb : v.poly with
  | avx512 =>
    rw [hb] at ho
    simp only [openCode, Code.iteCold, Code.all, hs, ho, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | ifma =>
    rw [hb] at ho
    simp only [openCode, Code.iteCold, Code.all, hw, ho, Bool.and_true]
    decide
  | _ => rw [hb] at ho; exact ho

end VG.Proof.ChaCha20Poly1305.X86_64.Shared
