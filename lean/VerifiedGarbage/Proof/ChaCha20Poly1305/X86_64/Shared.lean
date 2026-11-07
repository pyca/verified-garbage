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

theorem widen (enc : Bool) {c : Prog isa} (h : Verified target c (contract enc 1752)) :
    Verified target c (contract enc 1768) :=
  h.of_implies ⟨fun _ hp => pre_old enc hp, fun _ _ _ hp => by cases enc <;> exact hp,
    fun _ _ _ _ hp => by cases enc <;> exact hp, sat enc⟩

theorem body_verified (enc : Bool) (v : XorImpl) :
    Verified target (body enc v.callee v.poly) (contract enc 1752) := by
  cases enc
  · by_cases hv : v.poly = .avx2
    · have h := openS_framed v hv
      simpa only [body, framed, contract, Bool.false_eq_true, ↓reduceIte, hv] using h
    · simpa only [body, framed, contract, Bool.false_eq_true, ↓reduceIte, hv] using open_framed v
  · by_cases hv : v.poly = .avx2
    · have h := sealS_framed v hv
      simpa only [body, framed, contract, ↓reduceIte, hv] using h
    · simpa only [body, framed, contract, ↓reduceIte, hv] using seal_framed v

theorem body_sp (enc : Bool) (v : XorImpl) :
    (body enc v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  apply withStackArgScratchWipedX_spSafe
  cases enc
  · by_cases hv : v.poly = .avx2
    · have h := openS_spSafe v hv
      simpa only [Bool.false_eq_true, ↓reduceIte, hv] using h
    · simpa only [Bool.false_eq_true, ↓reduceIte, hv] using open_spSafe v
  · by_cases hv : v.poly = .avx2
    · have h := sealS_spSafe v hv
      simpa only [↓reduceIte, hv] using h
    · simpa only [↓reduceIte, hv] using seal_spSafe v

theorem body_depth (enc : Bool) (v : XorImpl) : (body enc v.callee v.poly).x86_64Depth ≤ 1752 := by
  have hd : (if enc then
      if v.poly = .avx2 then Impl.ChaCha20Poly1305.X86_64.Stitch.sealStitched
        { v.callee with pass := 512 } .avx2 else Impl.ChaCha20Poly1305.X86_64.«seal» v.callee v.poly
    else
      if v.poly = .avx2 then Impl.ChaCha20Poly1305.X86_64.Stitch.openStitched v.callee .avx2
      else Impl.ChaCha20Poly1305.X86_64.«open» v.callee v.poly).x86_64Depth ≤ 24 := by
    cases enc
    · by_cases hv : v.poly = .avx2
      · simpa only [Bool.false_eq_true, ↓reduceIte, hv] using openS_xdepth v
      · simpa only [Bool.false_eq_true, ↓reduceIte, hv] using open_xdepth v
    · by_cases hv : v.poly = .avx2
      · simpa only [↓reduceIte, hv] using sealS_xdepth v
      · simpa only [↓reduceIte, hv] using seal_xdepth v
  change max _ 0 + 1728 ≤ 1752
  rw [Nat.max_zero]
  exact Nat.add_le_add_right hd 1728

theorem call_sp (enc : Bool) (v : XorImpl) :
    (bodyCall enc v.callee v.poly).all (fun i => !isa.writesSp i) = true :=
  forward_spSafe (body_sp enc v)

theorem call_depth (enc : Bool) (v : XorImpl) : (bodyCall enc v.callee v.poly).x86_64Depth ≤ 1768 := by
  change max 0 (_ + 8) + 8 ≤ 1768
  rw [Nat.zero_max]
  exact Nat.add_le_add_right (Nat.add_le_add_right (body_depth enc v) 8) 8

theorem call_verified (enc : Bool) (v : XorImpl) :
    Verified target (bodyCall enc v.callee v.poly) (contract enc 1768) := by
  cases enc
  · exact Verified.forward (sig := Spec.ChaCha20Poly1305.openSig) (bytes := 8)
      (leak := some (Spec.ChaCha20Poly1305.openLeak 64))
      (show Verified target _ (Spec.ChaCha20Poly1305.openZeroContract abi 1752) from body_verified false v)
      (by decide) (by decide) (by decide) (by decide) (body_sp false v) (body_depth false v)
      (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp)
      (fun vs m₁ m₂ m' r hl hb _ hp => openZeroPost_local _ vs m₁ m₂ m' r hl hb hp)
      (sat false) (fun vs m₁ m₂ hl hb _ => openLeak_local _ vs m₁ m₂ hl hb)
  · exact Verified.forward (sig := Spec.ChaCha20Poly1305.sealSig) (bytes := 8) (leak := none)
      (show Verified target _ (Spec.ChaCha20Poly1305.sealContract abi 1752) from body_verified true v)
      (by decide) (by decide) (by decide) (by decide) (body_sp true v) (body_depth true v)
      (fun vs m₁ m₂ hl hb _ hp => pre_local _ _ vs m₁ m₂ hl hb hp)
      (fun vs m₁ m₂ m' r hl hb _ hp => sealPost_local _ vs m₁ m₂ m' r hl hb hp) (sat true)

theorem small_verified (enc : Bool) (v : XorImpl) (hv : v.poly = .avx2) :
    Verified target (smallCall enc v.callee) (contract enc 1768) := by
  have h := call_verified enc v
  rwa [hv] at h

theorem large_sp (enc : Bool) (v : XorImpl) (hv : v.poly = .avx512) :
    (largeCode enc v.callee).all (fun i => !isa.writesSp i) = true := by
  have h := body_sp enc v
  rw [hv] at h
  have hc := call_sp enc v
  rw [hv] at hc
  unfold largeCode
  split
  · simpa only [body, reduceCtorEq, ↓reduceIte] using h
  · exact hc

theorem large_depth (enc : Bool) (v : XorImpl) (hv : v.poly = .avx512) :
    (largeCode enc v.callee).x86_64Depth ≤ 1768 := by
  have h := body_depth enc v
  rw [hv] at h
  have hc := call_depth enc v
  rw [hv] at hc
  unfold largeCode
  split
  · have h' := Nat.le_trans h (show 1752 ≤ 1768 by decide)
    simpa only [body, reduceCtorEq, ↓reduceIte] using h'
  · exact hc

theorem large_verified (enc : Bool) (v : XorImpl) (hv : v.poly = .avx512) :
    Verified target (largeCode enc v.callee) (contract enc 1768) := by
  have h := widen enc (body_verified enc v)
  rw [hv] at h
  have hc := call_verified enc v
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

theorem flags_pre (enc : Bool) {s t : State} (h : FlagsOnly s t)
    (hp : (contract enc 1768).pre s) : (contract enc 1768).pre t := by
  cases enc
  · exact flags_pre_sig (sig := Spec.ChaCha20Poly1305.openSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.openZeroPost 64)
      (wa := true) (leak := some (Spec.ChaCha20Poly1305.openLeak 64)) (by decide) h hp
  · exact flags_pre_sig (sig := Spec.ChaCha20Poly1305.sealSig)
      (pre := Curry.const (fun _ => True) _) (post := Spec.ChaCha20Poly1305.sealPost 64)
      (wa := true) (leak := none) (by decide) h hp

theorem flags_post (enc : Bool) {s t z : State} (h : FlagsOnly s t)
    (hp : (contract enc 1768).post t z) : (contract enc 1768).post s z := by
  cases enc
  · simp only [contract, Bool.false_eq_true, ↓reduceIte] at hp ⊢
    rw [Spec.ChaCha20Poly1305.openZeroContract, post_args (by decide)] at hp ⊢
    simpa only [flags_args h, h.mem] using hp
  · simp only [contract, ↓reduceIte] at hp ⊢
    rw [Spec.ChaCha20Poly1305.sealContract, post_args (by decide)] at hp ⊢
    simpa only [flags_args h, h.mem] using hp

theorem flags_pub (enc : Bool) {s₁ s₂ t₁ t₂ : State} (h₁ : FlagsOnly s₁ t₁) (h₂ : FlagsOnly s₂ t₂)
    (hp : (contract enc 1768).pub s₁ s₂) : (contract enc 1768).pub t₁ t₂ := by
  cases enc
  · simp only [contract, Bool.false_eq_true, ↓reduceIte] at hp ⊢
    rw [Spec.ChaCha20Poly1305.openZeroContract, pubL_args (by decide)] at hp ⊢
    simpa only [flags_args h₁, flags_args h₂, h₁.rsp, h₂.rsp, h₁.mem, h₂.mem] using hp
  · simp only [contract, ↓reduceIte] at hp ⊢
    rw [Spec.ChaCha20Poly1305.sealContract, pubL_args (by decide)] at hp ⊢
    simpa only [flags_args h₁, flags_args h₂, h₁.rsp, h₂.rsp, h₁.mem, h₂.mem] using hp

theorem pub_len (enc : Bool) {s t : State} (h : (contract enc 1768).pub s t) :
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

/-- A public length choice between two framed implementations of the same API. -/
theorem choose (enc : Bool) {b : List Instr} {p : Addr → Bool} {a c : Prog isa}
    (ha : Verified target a (contract enc 1768)) (hc : Verified target c (contract enc 1768))
    (hb : ∀ s, WP isa (.block b) s fun u => isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u)
    (ht : ∀ i ∈ b, ∀ s, isa.addrs i s = []) :
    Verified target (.seq (.block b) (Code.iteCold .b a c)) (contract enc 1768) := by
  have cmp (s : State) : ∃ u, execBlock isa b s = some (u, []) ∧
      isa.eval .b u = some (p (s.gpr .r9)) ∧ FlagsOnly s u := by
    obtain ⟨t, u, he, hp⟩ := hb s
    have e := Exec.block_eq (T := target) he
    have hn := execBlock_trace_nil ht e
    exact ⟨u, hn ▸ e, hp⟩
  refine Verified.entryBranch (p := fun s => p (s.gpr .r9)) (fun _ => []) ha hc ?_ ?_ (sat enc)
  · intro s hs
    obtain ⟨u, he, hp, hf⟩ := cmp s
    exact ⟨u, he, hp, fun _ => ⟨flags_pre enc hf hs,
      fun _ hA hP => ⟨hf.abi hA, flags_post enc hf hP⟩⟩,
      fun _ => ⟨flags_pre enc hf hs, fun _ hA hP => ⟨hf.abi hA, flags_post enc hf hP⟩⟩⟩
  · intro s t u v _ _ hp eu ev
    obtain ⟨u', eu', _, hf⟩ := cmp s
    obtain ⟨v', ev', _, hg⟩ := cmp t
    have ee := Option.some.inj (eu.symm.trans eu')
    have ef := Option.some.inj (ev.symm.trans ev')
    obtain rfl := (Prod.mk.inj ee).1
    obtain rfl := (Prod.mk.inj ef).1
    exact ⟨rfl, congrArg p (pub_len enc hp), fun _ => flags_pub enc hf hg hp,
      fun _ => flags_pub enc hf hg hp⟩

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
    have hs := small_verified true v.small v.small_poly
    rw [XorImpl.small_callee] at hs
    have hg := large_verified true v hb
    exact choose true (p := fun n => decide (n.toNat < smallLim v.callee.small.vl ∨
      (winLo ≤ n.toNat ∧ n.toNat < winHi))) hs hg (fun s => cmpSmall_ok v.callee.small.vl s) (small_trace _)
  | _ =>
    have h := call_verified true v
    rw [hb] at h
    exact h

theorem open_verified (v : XorImpl) :
    Verified target (openCode v.callee v.poly) (contract false 1768) := by
  cases hb : v.poly with
  | avx512 =>
    have hs := small_verified false v.small v.small_poly
    rw [XorImpl.small_callee] at hs
    have hg := large_verified false v hb
    have heq : Impl.ChaCha20Poly1305.X86_64.Stitch.openLim v.callee.small.vl =
        Impl.ChaCha20Poly1305.X86_64.Stitch.smallLim v.callee.small.vl := rfl
    rw [openCode, heq]
    exact choose false (p := fun n => decide (n.toNat < smallLim v.callee.small.vl ∨
      (winLo ≤ n.toNat ∧ n.toNat < winHi))) hs hg (fun s => cmpSmall_ok v.callee.small.vl s) (small_trace _)
  | ifma =>
    have hs := small_verified false XorImpl.avx512vl.small XorImpl.avx512vl.small_poly
    rw [XorImpl.small_callee] at hs
    have hg := call_verified false v
    rw [hb] at hg
    exact choose false (p := fun n => decide (ifmaLo ≤ n.toNat ∧ n.toNat < ifmaHi)) hs hg cmpWin_ok window_trace
  | _ =>
    have h := call_verified false v
    rw [hb] at h
    exact h

theorem seal_sp (v : XorImpl) : (sealCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := call_sp true v
  have hg : v.poly = .avx512 → (largeCode true v.callee).all (fun i => !isa.writesSp i) = true := large_sp true v
  have hs := call_sp true v.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  change (smallCall true v.callee.small).all (fun i => !isa.writesSp i) = true at hs
  cases hb : v.poly with
  | avx512 =>
    have hg := hg hb
    simp only [sealCode, Code.iteCold, Code.all, hs, hg, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | _ => rw [hb] at ho; exact ho

theorem open_sp (v : XorImpl) : (openCode v.callee v.poly).all (fun i => !isa.writesSp i) = true := by
  have ho := call_sp false v
  have hg : v.poly = .avx512 → (largeCode false v.callee).all (fun i => !isa.writesSp i) = true := large_sp false v
  have hs := call_sp false v.small
  have hw := call_sp false XorImpl.avx512vl.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  change (smallCall false v.callee.small).all (fun i => !isa.writesSp i) = true at hs
  rw [XorImpl.small_callee, XorImpl.avx512vl.small_poly] at hw
  change (smallCall false Impl.ChaCha20.X86_64.Callee.avx512vl.small).all
    (fun i => !isa.writesSp i) = true at hw
  cases hb : v.poly with
  | avx512 =>
    have hg := hg hb
    simp only [openCode, Code.iteCold, Code.all, hs, hg, Bool.and_true]
    generalize v.callee.small.vl = vl
    cases vl <;> decide
  | ifma =>
    rw [hb] at ho
    simp only [openCode, Code.iteCold, Code.all, hw, ho, Bool.and_true]
    decide
  | _ => rw [hb] at ho; exact ho

theorem seal_depth (v : XorImpl) : (sealCode v.callee v.poly).x86_64Depth ≤ 1768 := by
  have ho := call_depth true v
  have hs := call_depth true v.small
  rw [XorImpl.small_callee, v.small_poly] at hs
  cases hb : v.poly with
  | avx512 =>
    have hg := large_depth true v hb
    simp only [sealCode, Code.iteCold, Code.x86_64Depth, Nat.max_le]
    exact ⟨by decide, ⟨⟨by decide, by decide⟩, hs⟩, hg⟩
  | _ => rw [hb] at ho; exact ho

end VG.Proof.ChaCha20Poly1305.X86_64.Shared
