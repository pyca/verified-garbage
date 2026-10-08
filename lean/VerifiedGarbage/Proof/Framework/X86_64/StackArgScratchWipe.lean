import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# A scratch buffer on the stack, after stack arguments, wiped after use (x86-64)

`Verified.stackArgScratchWiped`: as `Verified.stackArgScratch`, for
`withStackArgScratchWiped`, which zeroes the first `words` quadwords of the
buffer after the code, and `Verified.stackArgScratchWipedX`, for
`withStackArgScratchWipedX`, which zeroes its first `n` 16-byte words. Both
are `Verified.stackArgScratchWipedBy`, for any wipe (`Wiper`): it stores
only into the buffer, within the frame (`wipeAt_run`, `wipeAtX_run`), and
writes no callee-saved register, `rax` or MXCSR, so the run of the code
followed by the wipe keeps what the calling convention requires and the
return value, and its trace depends only on the stack pointer. The
postcondition holds of the memory after the wipe if it reads the memory on
return only within the function's buffers (`hpost`), which are disjoint from
the frame.
-/

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-- The trace of `wipeStoresAt off words` from a state whose `rsp` is `sp`. -/
def wipeAtTrace (sp : Addr) (off words : Nat) : List Leak :=
  (List.range words).map fun k => .addr (sp + BitVec.ofNat 64 (off + 8 * k))

theorem wipeStoresAt_succ (off w : Nat) :
    wipeStoresAt off (w + 1) =
      wipeStoresAt off w ++
        ([.store { base := .rsp, disp := ((off + 8 * w : Nat) : Int) } .r11] : List Instr) := by
  simp only [wipeStoresAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStoresAt` change memory only in the region `R`, which
holds each of them and which `u` may write. -/
theorem wipeStoresAt_run (R : Region) (u : State) (off : Nat) (hR : R ∈ u.wr) : ∀ words,
    (∀ k < words, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + 8 * k)) 8) →
    ∃ m', execBlock isa (wipeStoresAt off words) u =
        some ({ u with mem := m' }, wipeAtTrace (u.gpr .rsp) off words) ∧ Frame [R] u.mem m'
  | 0, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hc => by
    obtain ⟨m', he, hf⟩ := wipeStoresAt_run R u off hR w fun k hk => hc k (by omega)
    have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (off + 8 * w)) 8 :=
      ⟨R, hR, hc w (by omega)⟩
    refine ⟨m'.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + 8 * w)) (u.gpr .r11), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega))⟩
    rw [wipeStoresAt_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa, exec, State.store64, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil,
      wipeAtTrace, List.range_succ, List.map_append]

/-- `wipeAt off words` from `u`, with the `words` quadwords at `rsp + off`
in the region `R`, which `u` may write: it sets `r11` to zero and changes
memory only in `R`, with a trace of the addresses alone. -/
theorem wipeAt_run (R : Region) (u : State) (off words : Nat) (hR : R ∈ u.wr)
    (hc : ∀ k < words, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + 8 * k)) 8) :
    ∃ m', execBlock isa (wipeAt off words) u =
        some ({ u.setReg32 .r11 0 with mem := m' }, wipeAtTrace (u.gpr .rsp) off words) ∧
      Frame [R] u.mem m' := by
  have hsp : (u.setReg32 .r11 0).gpr .rsp = u.gpr .rsp := by simp [State.setReg32, State.setReg]
  obtain ⟨m', he, hf⟩ := wipeStoresAt_run R (u.setReg32 .r11 0) off
    (by simpa [State.setReg32, State.setReg]) words (by rw [hsp]; exact hc)
  refine ⟨m', ?_, by simpa [State.setReg32, State.setReg] using hf⟩
  simp only [wipeAt, execBlock, isa, exec, readSrc32, Option.map_some]
  rw [he, hsp]
  simp [addrs, srcAddrs]

theorem wipeAt_spSafe (off words : Nat) : (wipeAt off words).all (fun i => !isa.writesSp i) = true := by
  simp [wipeAt, wipeStoresAt, Instr.dst]

/-- The trace of `wipeStoresAtX off n` from a state whose `rsp` is `sp`. -/
def wipeAtXTrace (sp : Addr) (off n : Nat) : List Leak :=
  (List.range n).map fun k => .addr (sp + BitVec.ofNat 64 (off + 16 * k))

theorem wipeStoresAtX_succ (off w : Nat) :
    wipeStoresAtX off (w + 1) =
      wipeStoresAtX off w ++
        ([.movdquStore { base := .rsp, disp := ((off + 16 * w : Nat) : Int) } .xmm0] : List Instr) := by
  simp only [wipeStoresAtX, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStoresAtX` change memory only in the region `R`,
which holds each of them and which `u` may write. -/
theorem wipeStoresAtX_run (R : Region) (u : State) (off : Nat) (hR : R ∈ u.wr) : ∀ n,
    (∀ k < n, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * k)) 16) →
    ∃ m', execBlock isa (wipeStoresAtX off n) u =
        some ({ u with mem := m' }, wipeAtXTrace (u.gpr .rsp) off n) ∧ Frame [R] u.mem m'
  | 0, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hc => by
    obtain ⟨m', he, hf⟩ := wipeStoresAtX_run R u off hR w fun k hk => hc k (by omega)
    have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * w)) 16 :=
      ⟨R, hR, hc w (by omega)⟩
    refine ⟨m'.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * w)) (u.xmm .xmm0), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega))⟩
    rw [wipeStoresAtX_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa, exec, State.store128, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil,
      wipeAtXTrace, List.range_succ, List.map_append]

/-- `wipeAtX off n` from `u`, with the `n` 16-byte words at `rsp + off` in
the region `R`, which `u` may write: it sets `xmm0` to zero and changes
memory only in `R`, with a trace of the addresses alone. -/
theorem wipeAtX_run (R : Region) (u : State) (off n : Nat) (hR : R ∈ u.wr)
    (hc : ∀ k < n, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * k)) 16) :
    ∃ m', execBlock isa (wipeAtX off n) u =
        some ({ u.setXmm .xmm0 0 with mem := m' }, wipeAtXTrace (u.gpr .rsp) off n) ∧
      Frame [R] u.mem m' := by
  have hx : XOp.exec (.bin .pxor .xmm0 .xmm0) u = u.setXmm .xmm0 0 := by
    simp [XOp.exec, XBinOp.eval]
  obtain ⟨m', he, hf⟩ := wipeStoresAtX_run R (u.setXmm .xmm0 0) off (by simpa [State.setXmm]) n
    (by simpa [State.setXmm] using hc)
  refine ⟨m', ?_, by simpa [State.setXmm] using hf⟩
  simp only [wipeAtX, execBlock, isa, exec, Option.map_some, hx]
  rw [he]
  simp [addrs, State.setXmm]

theorem wipeAtX_spSafe (off n : Nat) : (wipeAtX off n).all (fun i => !isa.writesSp i) = true := by
  simp [wipeAtX, wipeStoresAtX, Instr.dst]

/-- A wipe: code `code off` that zeroes the `len` bytes at `rsp + off`, of
which the proofs need that it changes memory only in a region `R` holding
them that it may write, and no callee-saved register, `rax`, MXCSR or the
regions; that its trace depends on `rsp` alone; and that it never writes
`rsp`. -/
structure Wiper where
  code : Nat → List Instr
  len : Nat
  trace : Addr → Nat → List Leak
  run : ∀ (R : Region) (u : State) (off : Nat), R ∈ u.wr →
    (∀ a k, a + k ≤ len → R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + a)) k) →
    ∃ u', execBlock isa (code off) u = some (u', trace (u.gpr .rsp) off) ∧ Frame [R] u.mem u'.mem ∧
      (∀ r, r ∈ calleeSaved ∨ r = .rax → u'.gpr r = u.gpr r) ∧ u'.mxcsr = u.mxcsr ∧
      u'.rd = u.rd ∧ u'.wr = u.wr
  spSafe : ∀ off, (code off).all (fun i => !isa.writesSp i) = true

/-- `wipeAt`, zeroing `words` quadwords. -/
def Wiper.q (words : Nat) : Wiper where
  code off := wipeAt off words
  len := 8 * words
  trace sp off := wipeAtTrace sp off words
  run R u off hR hc := by
    obtain ⟨m', he, hf⟩ := wipeAt_run R u off words hR fun k hk => hc (8 * k) 8 (by omega)
    refine ⟨_, he, hf, fun r hr => ?_, rfl, rfl, rfl⟩
    have : r ≠ .r11 := by rintro rfl; rcases hr with hr | hr <;> simp [calleeSaved] at hr
    simp [State.setReg32, State.setReg, this]
  spSafe off := wipeAt_spSafe off words

/-- `wipeAtX`, zeroing `n` 16-byte words. -/
def Wiper.x (n : Nat) : Wiper where
  code off := wipeAtX off n
  len := 16 * n
  trace sp off := wipeAtXTrace sp off n
  run R u off hR hc := by
    obtain ⟨m', he, hf⟩ := wipeAtX_run R u off n hR fun k hk => hc (16 * k) 16 (by omega)
    exact ⟨_, he, hf, fun r _ => rfl, rfl, rfl, rfl⟩
  spSafe off := wipeAtX_spSafe off n

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

/-- Code verified for a function whose last argument, a scratch buffer of `n`
elements `e`, is passed on the stack after the six argument registers and
`nStack sig` other stack arguments, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `w.len` bytes after the
code with the wipe `w`, if its precondition reads memory only within the
function's buffers (`hpre`), and its postcondition both the memory on entry
and the memory on return (`hpost`, `hpostOut`). -/
theorem Verified.stackArgScratchWipedBy (w : Wiper) {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : w.len ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackArgScratch bytes (nStack sig) (.seq c (.block (w.code (16 + 8 * nStack sig)))))
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe : SpSafe (.seq c (.block (w.code (16 + 8 * nStack sig))) : Prog isa) :=
    SpSafe.of_all (by simp only [Code.all, hsp, w.spSafe, Bool.and_self])
  have hdep : (Code.seq c (.block (w.code (16 + 8 * nStack sig))) : Prog isa).x86_64Depth ≤
      stack := by
    simp only [Code.x86_64Depth]; omega
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega
  obtain ⟨hb0, hb1, hb2⟩ := hb
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (allArgs sig s),
        b.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig),
          n * e.size⟩ := by
    intro s hs b hb'
    rw [pre_args hk] at hs
    obtain ⟨⟨hwf, -⟩, -, -, -, hres, -, -⟩ := hs
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega
    have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
        (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
      rw [stackBelow_pos _ (by omega)]; simp
    rw [sub_add_ofNat _ (by omega)]
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ (List.mem_append_left _ hb')))).sub_right
      (Offset.sub_below _ (by omega) (by omega))
  -- Every run is `setArgs`, then the code's run from `narrowS`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ u,
      Exec isa c (narrowS sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrowS sig e n bytes s) s₃ ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig),
        n * e.size⟩] s₃.mem u.mem ∧
      Exec isa (withStackArgScratch bytes (nStack sig) (.seq c (.block (w.code (16 + 8 * nStack sig))))) s
        (setArgsTrace bytes (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) ++
          (t ++ w.trace (s.gpr .rsp - BitVec.ofNat 64 bytes) (16 + 8 * nStack sig)))
        (popState bytes s u) ∧
      abiPreserved s (popState bytes s u) ∧ (popState bytes s u).mem = u.mem ∧
      (popState bytes s u).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowS_pre hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs)
    obtain ⟨hrsp, -, -, -, -⟩ := narrowS_facts (nm := nm) hk hb0 hb1 hs
    have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
      (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
    have hwr₃ : s₃.wr = (narrowS sig e n bytes s).wr := (Exec.rdwr he).2
    have hbuf : (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig),
        n * e.size⟩ : Region) ∈ s₃.wr := by
      rw [hwr₃]
      simp [narrowS, oldRegions, List.filter_append]
    obtain ⟨u, hblk, hfr, hg, hmx, -, -⟩ := w.run _ s₃ (16 + 8 * nStack sig) hbuf
      (fun a k hak => by
        rw [hrsp₃]
        exact Offset.contains _ (by omega) (by omega) (by omega))
    have he' := Exec.seq he (Exec.block hblk)
    rw [hrsp₃] at he'
    have ha' : abiPreserved (narrowS sig e n bytes s) u := by
      refine ⟨fun q hq => ?_, ?_, by rw [hmx]; exact ha.2.2⟩
      · rw [hg q (.inl hq)]
        exact ha.1 q hq
      · rw [hrsp]
        rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.base_disjoint _ (e := 16 + 8 * nStack sig) (k := 8) (by omega) (by omega))
          (by decide)]
        have h2 := ha.2.1
        rwa [hrsp] at h2
    obtain ⟨hex, habi, hm, hrax⟩ :=
      withStackArgScratch_run hk ⟨hb0, hb1, hb2⟩ hst hsafe hdep hs he' ha'
    exact ⟨t, s₃, u, he, hq, hfr, hex, habi, hm, by rw [hrax, hg .rax (.inr rfl)]⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, u, -, hq, hfr, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hk]
    have hq' := (post_args (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb0 hb1 hs
    rw [hargs] at hq'
    rw [hm, hrax]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (allArgs_length sig s hk)) _) s₃.mem) _) hq'
    have h₄ := hpost _ _ _ _ _ (allArgs_length sig s hk) (narrowS_agree hk hb0 hb1 hs) h₃
    refine hpostOut _ _ _ _ _ (allArgs_length sig s hk) (fun b hb' a ha' => ?_) h₄
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    have hsp₁₂ : s₁.gpr .rsp = s₂.gpr .rsp := ((pub_args hk).mp hp).1
    rw [hct _ _ _ _ _ _ (narrowS_pre hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) h₁)
      (narrowS_pre hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) h₂)
      (narrowS_pub hk hb0 hb1 h₁ h₂ hp) f₁ f₂, hsp₁₂]


/-- `Verified.stackArgScratchWipedBy`, for `withStackArgScratchWiped`, which
zeroes the first `words` quadwords of the buffer. -/
theorem Verified.stackArgScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : 8 * words ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackArgScratchWiped bytes (nStack sig) words c)
      (sig.contract abi pre post wa (stack + bytes)) :=
  Verified.stackArgScratchWipedBy (.q words) h hk hb hst hsp hd hw hpre hpost hpostOut hsat

/-- `Verified.stackArgScratchWipedBy`, for `withStackArgScratchWipedX`, which
zeroes the first `k` 16-byte words of the buffer. -/
theorem Verified.stackArgScratchWipedX {c : Prog isa} {k : Nat}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : 16 * k ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackArgScratchWipedX bytes (nStack sig) k c)
      (sig.contract abi pre post wa (stack + bytes)) :=
  Verified.stackArgScratchWipedBy (.x k) h hk hb hst hsp hd hw hpre hpost hpostOut hsat

/-- `withStackArgScratchWiped` writes `rsp` only in its frame if its code
does. -/
theorem withStackArgScratchWiped_spSafe {bytes m words : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratchWiped bytes m words c).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratch_spSafe (by simp only [Code.all, h, wipeAt_spSafe, Bool.and_self])

/-- So does `withStackArgScratchWipedX`. -/
theorem withStackArgScratchWipedX_spSafe {bytes m k : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratchWipedX bytes m k c).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratch_spSafe (by simp only [Code.all, h, wipeAtX_spSafe, Bool.and_self])

end

end VG.X86_64
