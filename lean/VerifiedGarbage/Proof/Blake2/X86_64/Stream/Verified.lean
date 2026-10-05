import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Blake2.X86_64.Compress
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Impl.Blake2.X86_64.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common`. -/
section

/-!
# Streaming BLAKE2 on x86-64: common lemmas

The contracts the proofs of `init`, `update` and `finalize` are written
against, what they need of the compression function they call (`CalleeOk`),
the call (`compressWith_ok`), and the loops copying bytes into the buffer and
zeroing it.
-/

namespace VG.Proof.Blake2

open VG.X86_64 VG.Spec.Blake2

section
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- x86-64 contract for `init(state = rdi, outlen = rsi, key = rdx, keylen =
rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, bufOff w + blockBytes w⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧ ret.Disjoint state ∧
    1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ P.maxBytes ∧ (s.gpr .rcx).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .rsi).toNat (s.gpr .rcx).toNat) s'.mem
    (s.gpr .rdi) (keyBlock w (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

/-- x86-64 contract for `update(state = rdi, count = rsi, data = rdx, len =
rcx, scratch = r8)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, bufOff w + blockBytes w⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 576⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .rdi) d →
    s.gpr .rsi = BitVec.ofNat 64 d.length → d.length + (s.gpr .rcx).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (s.gpr .rdi) (d ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- x86-64 contract for `finalize(state = rdi, count = rsi, out = rdx, scratch =
rcx)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, bufOff w + blockBytes w⟩
    let out : Region := ⟨s.gpr .rdx, bufOff w⟩
    let scratch : Region := ⟨s.gpr .rcx, 576⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .rdi) d → d.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 d.length → bytesAt s'.mem (s.gpr .rdx) (bufOff w) = finalHash P h0 d
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end

namespace X86_64.Stream

open VG.Impl.Blake2.X86_64.Stream
open VG.Impl.Blake2.X86_64 (at_ compress)
open VG.Proof.MdStream.X86_64 (Upd ofInt_natCast toNat_ofNat_lt callEntry_byte wp_mov wp_movm wp_store
  wp_addi wp_subi wp_sub wp_add wp_cmp wp_test wp_movzx8 wp_store8 wp_mov32i wp_andi)

variable {w : Nat} {P : VG.Spec.Blake2.Params w} {callee : Impl.Blake2.X86_64.Stream.Callee}

/-- The word sizes. -/
structure Ok (P : VG.Spec.Blake2.Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : VG.Proof.Blake2.X86_64.Stream.Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N (h : VG.Proof.Blake2.X86_64.Stream.Ok P) : bufOff w = blockBytes w / 2 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : VG.Proof.Blake2.X86_64.Stream.Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

theorem N_eq : Impl.Blake2.X86_64.Stream.N w = bufOff w := rfl
theorem B_eq : Impl.Blake2.X86_64.Stream.B w = blockBytes w := rfl

/-- What the calls need of the compression function: its contract, and that it
does not touch `rsp` or the stack and keeps `rdi` and `r9`. -/
structure CalleeOk (P : VG.Spec.Blake2.Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressX86_64 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressX86_64 P).post s s'
  nosp : NoSp code
  depth : code.depth = 0
  keeps_rdi : ∀ i ∈ instrs code, Taint.clobbers i .rdi = false
  keeps_r9 : ∀ i ∈ instrs code, Taint.clobbers i .r9 = false

/-- The facts about the instructions of `code`, from one kernel check. -/
theorem CalleeOk.of_verified {code : Prog isa}
    (hv : ∀ s, (compressX86_64 P).pre s →
      ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressX86_64 P).post s s')
    (hk : ((instrs code).all fun i => !Taint.clobbers i .rdi && !Taint.clobbers i .r9 &&
      !Taint.clobbers i .rsp) = true)
    (hd : code.depth = 0) : VG.Proof.Blake2.X86_64.Stream.CalleeOk P code := by
  have h := fun i hi => List.all_eq_true.mp hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨hv, fun i hi => (h i hi).2, hd, fun i hi => (h i hi).1.1, fun i hi => (h i hi).1.2⟩

/-- What the call of the compression function needs of the state `s` before
the argument set-up: the hash value `st` at `rbx`, the scratch space `scr` at
`r15` and the `len` bytes of blocks at `src` do not overlap each other or the
return address, and may be accessed. -/
structure CallOk (s : State) (st scr src : Addr) (len : Nat) : Prop where
  rbx : s.gpr .rbx = st
  r15 : s.gpr .r15 = scr
  d₁ : Region.Disjoint ⟨st, bufOff w⟩ ⟨scr, 512⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, bufOff w⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, 512⟩
  d₄ : (below (s.gpr .rsp) 8).Disjoint ⟨st, bufOff w⟩
  d₅ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩
  d₆ : (below (s.gpr .rsp) 8).Disjoint ⟨src, len⟩
  hc : Covers [⟨src, len⟩, ⟨st, bufOff w⟩, ⟨scr, 512⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, bufOff w⟩, ⟨scr, 512⟩] s.wr
  hN : bufOff w ≤ 2 ^ 64
  hlen : len ≤ 2 ^ 64

/-- The arguments of the call, set up from `σ`. -/
structure Setup (σ s : State) (src n t : BitVec 64) (last : Bool) : Prop where
  rdi : s.gpr .rdi = σ.gpr .rbx
  rsi : s.gpr .rsi = src
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = t
  r8 : ((s.gpr .r8).setWidth 32 != 0) = last
  r9 : s.gpr .r9 = σ.gpr .r15
  cs : ∀ r ∈ calleeSaved, s.gpr r = σ.gpr r
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- The call's precondition, narrowed to the regions it is given. -/
theorem call_hyps {σ s : State} {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (h : VG.Proof.Blake2.X86_64.Stream.CallOk (w := w) σ st scr src (blockBytes w * n.toNat)) (hs : VG.Proof.Blake2.X86_64.Stream.Setup σ s src n t last) :
    (compressX86_64 P).pre (s.callEntry.withRegions [⟨src, blockBytes w * n.toNat⟩]
      [⟨st, bufOff w⟩, ⟨scr, 512⟩]) ∧
    Covers ([⟨src, blockBytes w * n.toNat⟩] ++ [⟨st, bufOff w⟩, ⟨scr, 512⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨st, bufOff w⟩, ⟨scr, 512⟩] s.wr := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.r9 ≠ .rsp), hs.rdi, hs.rdx, hs.r9, hs.rsi, h.rbx, h.r15, hsp]
    exact ⟨trivial, trivial, h.d₁, by simpa using h.d₂, by simpa using h.d₃, h.d₄, h.d₅⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw

/-- Compressing the `n` blocks at `src` into the hash value at `rbx`, with
scratch space at `r15`, by calling the compression function, after `args`
set up its arguments. -/
theorem compressWith_ok {args : List Instr} (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code) {s : State}
    {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (hs : WP isa (.block (([.mov .rdi (.reg .rbx)] : List Instr) ++ args ++ ([.mov .r9 (.reg .r15)] : List Instr))) s
      fun s' => VG.Proof.Blake2.X86_64.Stream.Setup s s' src n t last)
    (h : VG.Proof.Blake2.X86_64.Stream.CallOk (w := w) s st scr src (blockBytes w * n.toNat))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, bufOff w⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt w s'.mem st = compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last →
      Q s') :
    WP isa (compressWith callee args) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono hs fun s₁ hs => ?_)
  have e₁ : s₁.gpr .rdi = st := hs.rdi.trans h.rbx
  have e₃ : s₁.gpr .r9 = scr := hs.r9.trans h.r15
  have hsp : s₁.gpr .rsp = s.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  obtain ⟨hpre, hc, hw⟩ := VG.Proof.Blake2.X86_64.Stream.call_hyps (P := P) h hs
  refine WP.seq (WP.call (k := compressX86_64 P) hf.verified hf.nosp (by rw [hf.depth]; decide)
    (rd := [⟨src, blockBytes w * n.toNat⟩]) (wr := [⟨st, bufOff w⟩, ⟨scr, 512⟩]) hpre hc hw ?_)
  intro s₂ hrd hwr hcs hfr hkeep ⟨s₃, hm₃, _, hpost⟩
  have k₁ := hkeep .rdi hf.keeps_rdi
  have k₃ := hkeep .r9 hf.keeps_r9
  simp only [compressX86_64, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp),
    hne _ (by decide : Reg.r8 ≠ .rsp), e₁, hs.rsi, hs.rdx, hs.rcx, hs.r8, hm₃] at hpost
  have hst : stateAt w s₁.callEntry.mem st = stateAt w s.mem st :=
    (stateAt_congr fun i hi => callEntry_byte s₁ (R := ⟨st, bufOff w⟩) (by rw [hsp]; exact h.d₄)
      h.hN hi).trans (by rw [hs.mem])
  have hblk : compressBlocks P (stateAt w s.mem st) s₁.callEntry.mem src n.toNat t.toNat last =
      compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last :=
    compressBlocks_congr P fun j hj => by
      rw [callEntry_byte s₁ (R := ⟨src, blockBytes w * n.toNat⟩) (by rw [hsp]; exact h.d₆) h.hlen hj,
        hs.mem]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine hQ _ (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr => ?_) (by
    rw [hf.depth, hsp, hs.mem] at hfr; simpa [State.setReg] using hfr)
    (by simp only [State.setReg]; rw [hpost, hst, hblk])
  have h₂ := hcs r hr
  simp only [State.setReg]
  by_cases h15 : r = .r15
  · subst h15; simp [k₃, e₃, h.r15]
  · by_cases hbx : r = .rbx
    · subst hbx; simp [k₁, e₁, h.rbx]
    · simp [h15, hbx, h₂, hs.cs r hr]

/-! ## Copying bytes into the buffer -/

open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)
open VG.Proof.MdStream.X86_64 (sx1 ofNat_succ ofNat_pred ofNat_beq_zero)

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (dst src : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  rbp : s.gpr .rbp = src + BitVec.ofNat 64 j
  r13 : s.gpr .r13 = BitVec.ofNat 64 (r + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

/-- The loop copying `k ≥ 1` bytes from `src` (at `rbp`) to the buffer, from
byte `r` on (in `r13`). -/
theorem copyLoop_ok {s₀ : State} {st src : Addr} {r k : Nat} (hk : 1 ≤ k) (hk' : r + k < 2 ^ 32)
    (hrbx : s₀.gpr .rbx = st) (hrbp : s₀.gpr .rbp = src) (hr13 : s₀.gpr .r13 = BitVec.ofNat 64 r)
    (hrax : s₀.gpr .rax = BitVec.ofNat 64 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, k⟩ ⟨st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, VG.Proof.Blake2.X86_64.Stream.CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.X86_64.Stream.CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hrbp],
      by rw [hr13, Nat.add_zero], by rw [hrax, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hxs : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (VG.WriteBytes.writeBytes_frame s₀.mem _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix (k := k) _ (by simp; omega))).bytes (R := ⟨src, k⟩)
      (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  -- The byte written.
  have hout : InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hrbx' : s.gpr .rbx = st := by rw [h.other .rbx (by decide) (by decide) (by decide) (by decide), hrbx]
  refine wp_movzx8 (d := .r9) (a := src + BitVec.ofNat 64 j) (by simp [State.ea, h.rbp]) hin
    fun s₁ u₁ => ?_
  refine wp_store8 (r := .r9) (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) ?_
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, bufByte, u₁.other .rbx (by decide), u₁.other .r13 (by decide), hrbx', h.r13,
      VG.Proof.Blake2.X86_64.Stream.N_eq, BitVec.ofNat_add, BitVec.mul_one, VG.Proof.MdStream.X86_64.ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ x, x ≠ .rax → x ≠ .r13 → x ≠ .rbp → x ≠ .r9 → s₅.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h3, g₂, u₁.other x h4]
  have hrax' : s₅.gpr .rax = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      sx1, ofNat_pred (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.X86_64.Stream.CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hrax', fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
    · rw [u₅.other .rbp (by decide), u₄.other .rbp (by decide), u₃.gpr, g₂, u₁.other .rbp (by decide), h.rbp,
        sx1, ofNat_succ, BitVec.add_assoc]
    · rw [u₅.other .r13 (by decide), u₄.gpr, u₃.other .r13 (by decide), g₂, u₁.other .r13 (by decide), h.r13,
        sx1, ← Nat.add_assoc, ofNat_succ]
    · rw [g x h2 h4 h3 h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega
      have hlen : (List.take j (bytesAt s₀.mem src k)).length < 2 ^ 64 := by
        simp only [List.length_take]; omega
      rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, VG.WriteBytes.writeBytes_snoc _ _ _ _ hlen]
      have hl : (List.take j (bytesAt s₀.mem src k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [hl, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      congr 1
      simp [bytesAt]
  have hzf : s₅.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide),
      h.rax, sx1, ofNat_pred (show 1 ≤ k - j by omega), ofNat_beq_zero (by omega),
      show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

end X86_64.Stream

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT`. -/
section

section

/-!
# Streaming BLAKE2 on x86-64: the code as literals

`init`, `update` and `finalize` of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), whose calls refer to the
literals of the compression functions (`Proof/Blake2/X86_64/Lit.lean`).
-/

namespace VG.Proof.Blake2.X86_64.Stream

materialize_code initB := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
materialize_code updateB := Impl.Blake2.X86_64.Stream.update Spec.Blake2.b
materialize_code finalizeB := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b
materialize_code initS := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
materialize_code updateS := Impl.Blake2.X86_64.Stream.update Spec.Blake2.s
materialize_code finalizeS := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s

end VG.Proof.Blake2.X86_64.Stream

end

/-!
# Streaming BLAKE2 on x86-64: constant time

The taint analysis of `init`, `update` and `finalize` (the compression
function they call included), from the public arguments: the pointers,
`outlen`, `keylen`, `count` and `len`.
-/

namespace VG.Proof.Blake2.X86_64.Stream

open VG VG.X86_64 VG.Spec.Blake2

section
variable (w : Nat)

/-- `init` (which makes no calls): the arguments are public; `rdi` points at
the state. -/
def τInit : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [bufOff w + blockBytes w],
    bases := [(.rdi, 0, 0)] }

/-- `update`: the arguments are public; `rdi` and `r8` point at the state and
the scratch space. -/
def τUpdate : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [bufOff w + blockBytes w, 576], bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

/-- `finalize`: the arguments are public; `rdi`, `rdx` and `rcx` point at the
state, the output and the scratch space. -/
def τFinalize : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [bufOff w + blockBytes w, bufOff w, 576],
    bases := [(.rdi, 0, 0), (.rdx, 1, 0), (.rcx, 2, 0)] }

end

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

theorem init_agree (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₁ s₂ : State} (h₁ : (VG.Proof.Blake2.initX86_64 P).pre s₁) (h₂ : (VG.Proof.Blake2.initX86_64 P).pre s₂)
    (hpub : (VG.Proof.Blake2.initX86_64 P).pub s₁ s₂) : X86_64.Taint.Agree (VG.Proof.Blake2.X86_64.Stream.τInit w) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  have wf : ∀ s, (VG.Proof.Blake2.initX86_64 P).pre s → X86_64.Taint.Wf (VG.Proof.Blake2.X86_64.Stream.τInit w) s := by
    intro s hs
    obtain ⟨-, hw, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Blake2.X86_64.Stream.τInit], by simp [hw], by simp [hw]; rcases hP.w with rfl | rfl <;> decide⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Blake2.X86_64.Stream.τInit, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Blake2.X86_64.Stream.τInit, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1]
  · intro sl h; simp [VG.Proof.Blake2.X86_64.Stream.τInit] at h
  · intro sl h; simp [VG.Proof.Blake2.X86_64.Stream.τInit] at h

theorem update_agree (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₁ s₂ : State} (h₁ : (VG.Proof.Blake2.updateX86_64 P).pre s₁)
    (h₂ : (VG.Proof.Blake2.updateX86_64 P).pre s₂) (hpub : (VG.Proof.Blake2.updateX86_64 P).pub s₁ s₂) :
    X86_64.Taint.Agree (VG.Proof.Blake2.X86_64.Stream.τUpdate w) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, (VG.Proof.Blake2.updateX86_64 P).pre s → X86_64.Taint.Wf (VG.Proof.Blake2.X86_64.Stream.τUpdate w) s := by
    intro s hs
    obtain ⟨-, hw, hd, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Blake2.X86_64.Stream.τUpdate], by simp [hw, hd], by
      simp [hw]; rcases hP.w with rfl | rfl <;> decide⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Blake2.X86_64.Stream.τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Blake2.X86_64.Stream.τUpdate, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [VG.Proof.Blake2.X86_64.Stream.τUpdate] at h
  · intro sl h; simp [VG.Proof.Blake2.X86_64.Stream.τUpdate] at h

theorem finalize_agree (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₁ s₂ : State} (h₁ : (VG.Proof.Blake2.finalizeX86_64 P).pre s₁)
    (h₂ : (VG.Proof.Blake2.finalizeX86_64 P).pre s₂) (hpub : (VG.Proof.Blake2.finalizeX86_64 P).pub s₁ s₂) :
    X86_64.Taint.Agree (VG.Proof.Blake2.X86_64.Stream.τFinalize w) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, (VG.Proof.Blake2.finalizeX86_64 P).pre s → X86_64.Taint.Wf (VG.Proof.Blake2.X86_64.Stream.τFinalize w) s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Blake2.X86_64.Stream.τFinalize], by simp [hw, d1, d2, d3], by
      simp [hw]; rcases hP.w with rfl | rfl <;> decide⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Blake2.X86_64.Stream.τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Blake2.X86_64.Stream.τFinalize, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3, p4]
  · intro sl h; simp [VG.Proof.Blake2.X86_64.Stream.τFinalize] at h
  · intro sl h; simp [VG.Proof.Blake2.X86_64.Stream.τFinalize] at h

theorem okB : VG.Proof.Blake2.X86_64.Stream.Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩
theorem okS : VG.Proof.Blake2.X86_64.Stream.Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem initB_ct : ConstantTime isa (VG.Proof.Blake2.initX86_64 b).pre (VG.Proof.Blake2.initX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (VG.Proof.Blake2.X86_64.Stream.τInit 64) (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.Stream.init_agree VG.Proof.Blake2.X86_64.Stream.okB h₁ h₂ hp)
    (by taint_decide)

theorem initS_ct : ConstantTime isa (VG.Proof.Blake2.initX86_64 s).pre (VG.Proof.Blake2.initX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (VG.Proof.Blake2.X86_64.Stream.τInit 32) (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.Stream.init_agree VG.Proof.Blake2.X86_64.Stream.okS h₁ h₂ hp)
    (by taint_decide)

theorem updateB_ct : ConstantTime isa (VG.Proof.Blake2.updateX86_64 b).pre (VG.Proof.Blake2.updateX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.update b) :=
  VG.Taint.constantTime (A := taint) (VG.Proof.Blake2.X86_64.Stream.τUpdate 64) (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.Stream.update_agree VG.Proof.Blake2.X86_64.Stream.okB h₁ h₂ hp)
    (by taint_decide)

theorem updateS_ct : ConstantTime isa (VG.Proof.Blake2.updateX86_64 s).pre (VG.Proof.Blake2.updateX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.update s) :=
  VG.Taint.constantTime (A := taint) (VG.Proof.Blake2.X86_64.Stream.τUpdate 32) (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.Stream.update_agree VG.Proof.Blake2.X86_64.Stream.okS h₁ h₂ hp)
    (by taint_decide)

theorem finalizeB_ct : ConstantTime isa (VG.Proof.Blake2.finalizeX86_64 b).pre (VG.Proof.Blake2.finalizeX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.finalize b) :=
  VG.Taint.constantTime (A := taint) (VG.Proof.Blake2.X86_64.Stream.τFinalize 64)
    (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.Stream.finalize_agree VG.Proof.Blake2.X86_64.Stream.okB h₁ h₂ hp) (by taint_decide)

theorem finalizeS_ct : ConstantTime isa (VG.Proof.Blake2.finalizeX86_64 s).pre (VG.Proof.Blake2.finalizeX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.finalize s) :=
  VG.Taint.constantTime (A := taint) (VG.Proof.Blake2.X86_64.Stream.τFinalize 32)
    (fun _ _ h₁ h₂ hp => VG.Proof.Blake2.X86_64.Stream.finalize_agree VG.Proof.Blake2.X86_64.Stream.okS h₁ h₂ hp) (by taint_decide)

end VG.Proof.Blake2.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init`. -/
section

/-!
# Streaming BLAKE2 on x86-64: `init`

`initState` stores the initial hash value (`initState_ok`); for a key,
`keyBlock` zeroes the buffer (`zero_ok`) and copies the key into it
(`keyLoop_ok`).
-/

namespace VG.Proof.Blake2.X86_64.Stream.Init

open VG VG.X86_64 VG.Spec.Blake2
open VG.Impl.Blake2.X86_64.Stream (initState)
open VG.Impl.Blake2.X86_64 (at_ ws imm)
open VG.Proof.Blake2 (initX86_64 bufOff repr_keyBlock stateAt_congr)
open VG.Proof.Blake2.X86_64.Stream (Ok N_eq B_eq)
open VG.Proof.MdStream.X86_64 (Upd WP.cons wp_mov wp_mov32i wp_store wp_store32 wp_store8 wp_movzx8
  wp_addi wp_subi wp_test ofInt_natCast sx1 ofNat_succ ofNat_pred ofNat_beq_zero toNat_ofNat_lt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  write_eq_writeBytes)

/-! ## Instructions at the word size -/

section
variable {w : Nat} {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_imm (hw : w = 64 ∨ w = 32) {d : Reg} {v : BitVec w}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (imm w d v :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.setReg _ _ _))
  · exact WP.cons rfl (k _ (BitVec.setWidth_eq v ▸ Upd.setReg s d ((v.setWidth 32).setWidth 64)))

theorem wp_st (hw : w = 64 ∨ w = 32) {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a)
    (hout : InRegions s.wr a (w / 8))
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth w) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Blake2.X86_64.st w m r :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact wp_store ha hout fun s' g m rd wr => k s' g (by rw [m, BitVec.setWidth_eq]) rd wr
  · exact wp_store32 ha hout k

theorem wp_xorw (hw : w = 64 ∨ w = 32) {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth w ^^^ (s.gpr r).setWidth w).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Blake2.X86_64.xor w d (.reg r) :: is)) s Q := by
  rcases hw with rfl | rfl
  · refine WP.cons rfl (k _ ?_)
    simp only [BitVec.setWidth_eq]
    exact Upd.flags s d (s.gpr d ^^^ s.gpr r) false false _
  · exact WP.cons rfl (k _ (Upd.flags s d (w := 32) _ false false _))

theorem wp_rorw (hw : w = 64 ∨ w = 32) {d : Reg}
    (k : ∀ s', Upd s s' d ((((s.gpr d).setWidth w).rotateRight (w - 8)).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Blake2.X86_64.ror w d (w - 8) :: is)) s Q := by
  rcases hw with rfl | rfl
  · refine WP.cons rfl (k _ ?_)
    simp only [BitVec.setWidth_eq]
    exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩
  · refine WP.cons rfl (k _ ?_)
    exact ⟨by simp [State.setReg32, State.setReg], fun r h => by simp [State.setReg32, State.setReg, h]; rfl,
      rfl, rfl, rfl⟩

end

/-! ## Arithmetic -/

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  show s.gpr b + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.MdStream.X86_64.ofInt_natCast]

theorem ws_eq (w : Nat) : ws w = w / 8 := rfl

theorem rotr_eq {w : Nat} (hw : w = 64 ∨ w = 32) (x : BitVec w) (h : x.toNat < 2 ^ (w - 8)) :
    x.rotateRight (w - 8) = x <<< 8 := by
  have h0 : x >>> ((w - 8) % w) = 0#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt h]; rfl
  rw [BitVec.rotateRight_def, h0, BitVec.zero_or, Nat.mod_eq_of_lt (by omega),
    show w - (w - 8) = 8 by omega]

section
variable {w : Nat} (hw : w = 64 ∨ w = 32)
include hw

theorem w_le : w ≤ 64 := by omega

theorem word_in {j : Nat} (hj : j < 8) : w / 8 * j + w / 8 ≤ bufOff w := by
  rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega

theorem word_sep {j k : Nat} (h : j ≠ k) :
    w / 8 * j + w / 8 ≤ w / 8 * k ∨ w / 8 * k + w / 8 ≤ w / 8 * j := by
  rcases hw with rfl | rfl <;> omega

theorem sizes : bufOff w + blockBytes w < 2 ^ 32 ∧ 16 ≤ blockBytes w ∧ blockBytes w % 8 = 0 ∧
    blockBytes w < 2 ^ (w - 8) ∧ w / 8 < 2 ^ 64 := by
  rcases hw with rfl | rfl <;> decide

theorem readW_writeW_self_w (m : Mem) (a : Addr) (v : BitVec w) : (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

end

/-! ## Bytes -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    VG.WriteBytes.writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx : xs.length ≤ n) (hz : ∀ i < n, m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Blake2.X86_64.Stream.Init.writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · simp only [hi, ↓reduceIte]
    rw [hz i h1, List.getElem_append_right (by omega), List.getElem_replicate]

theorem writeW_zero (m : Mem) (a : Addr) :
    m.writeW a (0 : BitVec 64) = VG.WriteBytes.writeBytes m a (List.replicate 8 0) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl

/-! ## The initial hash value -/

section
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec w := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  [imm w .rax (VG.Proof.Blake2.X86_64.Stream.Init.ivAt P (k + 1)), VG.Impl.Blake2.X86_64.st w (at_ .rdi (ws w * (k + 1))) .rax]

theorem initState_eq : initState P = (List.range 7).flatMap (VG.Proof.Blake2.X86_64.Stream.Init.ivStep P) ++
    [imm w .rax (P.IV[0] ^^^ 0x01010000), .mov .r8 (.reg .rcx),
      VG.Impl.Blake2.X86_64.ror w .r8 (w - 8), VG.Impl.Blake2.X86_64.xor w .rax (.reg .r8),
      VG.Impl.Blake2.X86_64.xor w .rax (.reg .rsi), VG.Impl.Blake2.X86_64.st w (at_ .rdi 0) .rax] := rfl

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rdi, bufOff w⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (j + 1))) w = VG.Proof.Blake2.X86_64.Stream.Init.ivAt P (j + 1)

variable {P}

theorem iv_step (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .rdi, bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : VG.Proof.Blake2.X86_64.Stream.Init.IvInv P s₀ k s) :
    WP isa (.block (VG.Proof.Blake2.X86_64.Stream.Init.ivStep P k)) s (VG.Proof.Blake2.X86_64.Stream.Init.IvInv P s₀ (k + 1)) := by
  have hin : (⟨s₀.gpr .rdi, bufOff w⟩ : Region).Contains
      (s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (k + 1))) (w / 8) :=
    Offset.contains_base _ (VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (by omega))
      (by have := VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (j := k + 1) (by omega); have := (VG.Proof.Blake2.X86_64.Stream.Init.sizes hw).1; omega)
  refine VG.Proof.Blake2.X86_64.Stream.Init.wp_imm hw fun s₁ u₁ => VG.Proof.Blake2.X86_64.Stream.Init.wp_st hw (a := s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (k + 1))) ?_ ?_
    fun s₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  · rw [VG.Proof.Blake2.X86_64.Stream.Init.ea_at, u₁.other _ (by decide), h.gpr _ (by decide), VG.Proof.Blake2.X86_64.Stream.Init.ws_eq]
  · rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have hv : (s₁.gpr .rax).setWidth w = VG.Proof.Blake2.X86_64.Stream.Init.ivAt P (k + 1) := by
    rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (w_le hw), BitVec.setWidth_eq]
  refine ⟨fun r hr => by rw [g₂, u₁.other r hr, h.gpr r hr], by rw [rd₂, u₁.rd, h.rd],
    by rw [wr₂, u₁.wr, h.wr], ?_, fun j hj => ?_⟩
  · rw [m₂, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [m₂, hv, u₁.mem]
    by_cases e : j = k
    · subst e; exact VG.Proof.Blake2.X86_64.Stream.Init.readW_writeW_self_w hw _ _ _
    · have hs := VG.Proof.Blake2.X86_64.Stream.Init.sizes hw
      rw [Mem.readW_writeW_sep (Offset.sep _ (VG.Proof.Blake2.X86_64.Stream.Init.word_sep hw (fun h => e (by omega)))
        (by have := VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (j := j + 1) (by omega); omega)
        (by have := VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (j := k + 1) (by omega); omega)) hs.2.2.2.2]
      exact h.words j (by omega)

/-- The state after `initState` and the test of `keylen`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .r8 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rdi, bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (s₀.gpr .rdi) = Spec.Blake2.init P (s₀.gpr .rsi).toNat (s₀.gpr .rcx).toNat
  zf : s.zf = some (decide ((s₀.gpr .rcx).toNat = 0))

theorem initState_ok (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .rdi, bufOff w⟩] a n → InRegions s₀.wr a n)
    (hkk : (s₀.gpr .rcx).toNat < 2 ^ (w - 8)) :
    WP isa (.block (initState P ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) s₀ (VG.Proof.Blake2.X86_64.Stream.Init.StateOk (P := P) s₀) := by
  have hs := VG.Proof.Blake2.X86_64.Stream.Init.sizes hw
  have hle := w_le hw
  rw [VG.Proof.Blake2.X86_64.Stream.Init.initState_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86_64.Stream.Init.IvInv P s₀) (VG.Proof.Blake2.X86_64.Stream.Init.iv_step hw hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .rdi, bufOff w⟩ : Region).Contains (s₀.gpr .rdi + BitVec.ofNat 64 0) (w / 8) :=
    Offset.contains_base _ (by have := VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (j := 0) (by omega); omega) (by omega)
  refine VG.Proof.Blake2.X86_64.Stream.Init.wp_imm hw fun s₁ u₁ => wp_mov fun s₂ u₂ _ _ => VG.Proof.Blake2.X86_64.Stream.Init.wp_rorw hw fun s₃ u₃ => VG.Proof.Blake2.X86_64.Stream.Init.wp_xorw hw fun s₄ u₄ =>
    VG.Proof.Blake2.X86_64.Stream.Init.wp_xorw hw fun s₅ u₅ => VG.Proof.Blake2.X86_64.Stream.Init.wp_st hw (a := s₀.gpr .rdi + BitVec.ofNat 64 0) ?_ ?_
    fun s₆ g₆ m₆ rd₆ wr₆ => wp_test fun s₇' g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_
  · rw [VG.Proof.Blake2.X86_64.Stream.Init.ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide)]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s₇'.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₇, g₆, u₅.other r h1, u₄.other r h1, u₃.other r h2, u₂.other r h2, u₁.other r h1, h₇.gpr r h1]
  -- The word stored.
  have hv : (s₅.gpr .rax).setWidth w = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat w (s₀.gpr .rcx).toNat <<< 8) ^^^ BitVec.ofNat w (s₀.gpr .rsi).toNat := by
    have sw : ∀ x : BitVec w, (x.setWidth 64).setWidth w = x := fun x => by
      rw [BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq]
    simp only [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₄.other .rsi (by decide),
      u₃.other .rax (by decide), u₃.other .rsi (by decide), u₂.other .rax (by decide),
      u₂.other .rsi (by decide), u₁.other .rsi (by decide), u₁.other .rcx (by decide),
      h₇.gpr .rsi (by decide), h₇.gpr .rcx (by decide), sw]
    rw [← BitVec.ofNat_toNat w (s₀.gpr .rcx), ← BitVec.ofNat_toNat w (s₀.gpr .rsi),
      VG.Proof.Blake2.X86_64.Stream.Init.rotr_eq hw _ (by rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hkk)]
    rfl
  have hm : s₇'.mem = s₇.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 0) ((s₅.gpr .rax).setWidth w) := by
    rw [m₇, m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [rd₇, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd],
    by rw [wr₇, wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr], ?_, ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, VG.Proof.Blake2.X86_64.Stream.Init.readW_writeW_self_w hw, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsep : Mem.Sep (s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (j + 1))) (w / 8)
          (s₀.gpr .rdi + BitVec.ofNat 64 0) (w / 8) :=
        Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega))
          (by have := VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (j := j + 1) hj; omega) (by have := VG.Proof.Blake2.X86_64.Stream.Init.word_in hw (j := 0) (by omega); omega)
      rw [Mem.readW_writeW_sep hsep hs.2.2.2.2, h₇.words j (by omega)]
      simp only [VG.Proof.Blake2.X86_64.Stream.Init.ivAt, hj, ↓reduceDIte]
  · rw [z₇, g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide), BitVec.and_self,
      ← ofNat_beq_zero (s₀.gpr .rcx).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end

/-! ## The key block -/

section
variable {w : Nat}

/-- After zeroing `8 · j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = VG.WriteBytes.writeBytes σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (bufOff w)) (List.replicate (8 * j) 0)

theorem zero_ok (hw : w = 64 ∨ w = 32) {σ : State} (hrax : σ.gpr .rax = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .rdi, bufOff w + blockBytes w⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (Impl.Blake2.X86_64.Stream.B w / 8)).flatMap fun j =>
      [.store (at_ .rdi (Impl.Blake2.X86_64.Stream.N w + 8 * j)) .rax])) σ
      (VG.Proof.Blake2.X86_64.Stream.Init.ZInv (w := w) σ (blockBytes w / 8)) := by
  have hs := VG.Proof.Blake2.X86_64.Stream.Init.sizes hw
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86_64.Stream.Init.ZInv (w := w) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Blake2.X86_64.Stream.B_eq] at hj
  refine wp_store (a := σ.gpr .rdi + BitVec.ofNat 64 (bufOff w + 8 * j)) (by rw [VG.Proof.Blake2.X86_64.Stream.Init.ea_at, h.gpr, VG.Proof.Blake2.X86_64.Stream.N_eq])
    ?_ fun s' g' m' rd' wr' => WP.block_nil ⟨g'.trans h.gpr, rd'.trans h.rd, wr'.trans h.wr, ?_⟩
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · have e := VG.WriteBytes.writeBytes_append σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (bufOff w))
      (List.replicate (8 * j) 0) (List.replicate 8 0) (by simp; omega)
    rw [List.length_replicate] at e
    rw [m', h.mem, h.gpr, hrax, VG.Proof.Blake2.X86_64.Stream.Init.writeW_zero, ← Offset.add_ofNat_add_ofNat, e,
      List.replicate_append_replicate, Nat.mul_succ]

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kk : Nat := (s₀.gpr .rcx).toNat
abbrev buf (w : Nat) : Addr := VG.Proof.Blake2.X86_64.Stream.Init.st s₀ + BitVec.ofNat 64 (bufOff w)
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Init.st s₀, bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Init.kp s₀, VG.Proof.Blake2.X86_64.Stream.Init.kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Init.kp s₀) (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ VG.Proof.Blake2.X86_64.Stream.Init.kk s₀
  r8 : s.gpr .r8 = BitVec.ofNat 64 j
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - j)
  other : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.WriteBytes.writeBytes Z (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) ((VG.Proof.Blake2.X86_64.Stream.Init.key s₀).take j)

theorem keyLoop_ok (hw : w = 64 ∨ w = 32) {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [VG.Proof.Blake2.X86_64.Stream.Init.kR s₀]) (hwr : s₀.wr = [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w]) (hd : (VG.Proof.Blake2.X86_64.Stream.Init.kR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w))
    (hk : 1 ≤ VG.Proof.Blake2.X86_64.Stream.Init.kk s₀) (hkb : VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ ≤ blockBytes w) (hZ : Frame [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w] s₀.mem Z)
    (hσ : VG.Proof.Blake2.X86_64.Stream.Init.KInv (w := w) s₀ Z 0 σ) :
    WP isa (.loop (.block [.movzx8 .rax { base := .rdx, index := some .r8, scale := 1 },
        .store8 { base := .rdi, index := some .r8, scale := 1, disp := Impl.Blake2.X86_64.Stream.N w } .rax,
        .alu .add .r8 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) σ
      (VG.Proof.Blake2.X86_64.Stream.Init.KInv (w := w) s₀ Z (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀)) := by
  have hs := VG.Proof.Blake2.X86_64.Stream.Init.sizes hw
  have hkl : VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  have hxs : (VG.Proof.Blake2.X86_64.Stream.Init.key s₀).length = VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ := by simp [bytesAt]
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - j ∧ j < VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ ∧ VG.Proof.Blake2.X86_64.Stream.Init.KInv (w := w) s₀ Z j s)
    ?_ (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀) σ ⟨0, by omega, by omega, hσ⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The key byte read is unchanged.
  have hbyte : s.mem (VG.Proof.Blake2.X86_64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) = s₀.mem (VG.Proof.Blake2.X86_64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hf : Frame [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w] s₀.mem (VG.WriteBytes.writeBytes Z (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) ((VG.Proof.Blake2.X86_64.Stream.Init.key s₀).take j)) :=
      hZ.trans (VG.WriteBytes.writeBytes_frame Z _ _ (Offset.contains_base _ (by simp; omega) (by omega)))
    exact hf.bytes (R := VG.Proof.Blake2.X86_64.Stream.Init.kR s₀) (by simpa using hd) (by simp; omega) hj
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.Blake2.X86_64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hrd]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hout : InRegions s.wr (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w + BitVec.ofNat 64 j) 1 := by
    rw [h.wr, hwr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_movzx8 (d := .rax) (a := VG.Proof.Blake2.X86_64.Stream.Init.kp s₀ + BitVec.ofNat 64 j)
    (by simp [State.ea, h.r8, h.other .rdx (by decide) (by decide) (by decide)]) hin fun s₁ u₁ => ?_
  refine wp_store8 (r := .rax) (a := VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, u₁.other .rdi (by decide), u₁.other .r8 (by decide),
      h.other .rdi (by decide) (by decide) (by decide), h.r8, VG.Proof.Blake2.X86_64.Stream.N_eq, BitVec.mul_one, VG.Proof.MdStream.X86_64.ofInt_natCast]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), ← BitVec.add_assoc]
  refine wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ hz₄ => WP.block_nil ?_
  have hrcx : s₄.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - (j + 1)) := by
    rw [u₄.gpr, u₃.other .rcx (by decide), g₂, u₁.other .rcx (by decide), h.rcx, sx1,
      ofNat_pred (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.X86_64.Stream.Init.KInv (w := w) s₀ Z (j + 1) s₄ := by
    refine ⟨by omega, ?_, hrcx, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · rw [u₄.other .r8 (by decide), u₃.gpr, g₂, u₁.other .r8 (by decide), h.r8, sx1, ofNat_succ]
    · rw [u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1, h.other r h1 h2 h3]
    · rw [u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
    · have hj' : j < (VG.Proof.Blake2.X86_64.Stream.Init.key s₀).length := by omega
      have hl : (List.take j (VG.Proof.Blake2.X86_64.Stream.Init.key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl,
        BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      congr 1
      simp [bytesAt]
  have hzf : s₄.zf = some (decide (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - (j + 1) = 0)) := by
    rw [hz₄, u₃.other .rcx (by decide), g₂, u₁.other .rcx (by decide), h.rcx, sx1,
      ofNat_pred (show 1 ≤ VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - j by omega), ofNat_beq_zero (by omega),
      show VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - j - 1 = VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - (j + 1) by omega]
  by_cases hjk : j + 1 = VG.Proof.Blake2.X86_64.Stream.Init.kk s₀
  · refine .inl ⟨?_, hjk ▸ hI⟩
    simp only [eval, hzf, show VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

end

section
variable {w : Nat} {P : VG.Spec.Blake2.Params w}

theorem keyBlock_ok (hw : w = 64 ∨ w = 32) {s₀ σ : State}
    (hrd : s₀.rd = [VG.Proof.Blake2.X86_64.Stream.Init.kR s₀]) (hwr : s₀.wr = [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w]) (hd : (VG.Proof.Blake2.X86_64.Stream.Init.kR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w))
    (hk : 1 ≤ VG.Proof.Blake2.X86_64.Stream.Init.kk s₀) (hkb : VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ ≤ blockBytes w) (hσ : VG.Proof.Blake2.X86_64.Stream.Init.StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.X86_64.Stream.keyBlock (w := w)) σ fun s =>
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r) ∧
      Frame [⟨VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w, blockBytes w⟩] σ.mem s.mem ∧
      bytesAt s.mem (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) (blockBytes w) = VG.Proof.Blake2.X86_64.Stream.Init.key s₀ ++ List.replicate (blockBytes w - VG.Proof.Blake2.X86_64.Stream.Init.kk s₀) 0 := by
  have hs := VG.Proof.Blake2.X86_64.Stream.Init.sizes hw
  have hxs : (VG.Proof.Blake2.X86_64.Stream.Init.key s₀).length = VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes w → (VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w).Contains (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) n := fun n hn =>
    Offset.contains_base _ (by omega) (by omega)
  have hσdi : σ.gpr .rdi = VG.Proof.Blake2.X86_64.Stream.Init.st s₀ := hσ.gpr _ (by decide) (by decide)
  unfold Impl.Blake2.X86_64.Stream.keyBlock
  rw [List.map_eq_flatMap]
  refine WP.seq (wp_mov32i fun σ₁ u₁ _ _ => WP.mono (VG.Proof.Blake2.X86_64.Stream.Init.zero_ok hw (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_)
    fun s₂ h₂ => ?_)
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσdi]; exact fun _ _ h => h
  have hZ : s₂.mem = VG.WriteBytes.writeBytes σ.mem (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) (List.replicate (blockBytes w) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσdi, u₁.mem, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.2.2.1)]
  have hfZ : Frame [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans
      (VG.WriteBytes.writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine WP.seq (wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ?_)
  refine WP.mono (VG.Proof.Blake2.X86_64.Stream.Init.keyLoop_ok hw hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, by rw [u₃.gpr]; rfl, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3
    rw [u₃.other r h2, h₂.gpr, u₁.other r h1, hσ.gpr r h1 h2]
  · rw [u₃.mem, List.take_zero, VG.WriteBytes.writeBytes_nil]
  have hm : s.mem = VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes σ.mem (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) (List.replicate (blockBytes w) 0))
      (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) (VG.Proof.Blake2.X86_64.Stream.Init.key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega), hZ]
  refine ⟨h.other, ?_, ?_⟩
  · rw [hm]
    exact (VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by simp))).trans
      (VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by omega)))
  · rw [hm, VG.Proof.Blake2.X86_64.Stream.Init.bytesAt_writeBytes (by omega) (by omega) fun i hi => ?_, hxs]
    rw [VG.Proof.Blake2.X86_64.Stream.Init.writeBytes_at _ _ _ (by omega)]
    simp [hi]

theorem finish {s₀ s : State} (hw : w = 64 ∨ w = 32) (hkb : VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ ≤ blockBytes w)
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ (VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w))
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hf : Frame [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w] s₀.mem s.mem)
    (hst : stateAt w s.mem (VG.Proof.Blake2.X86_64.Stream.Init.st s₀) = Spec.Blake2.init P (s₀.gpr .rsi).toNat (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀))
    (hb : VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ ≠ 0 → bytesAt s.mem (VG.Proof.Blake2.X86_64.Stream.Init.buf s₀ w) (blockBytes w) =
      VG.Proof.Blake2.X86_64.Stream.Init.key s₀ ++ List.replicate (blockBytes w - VG.Proof.Blake2.X86_64.Stream.Init.kk s₀) 0) :
    gprPreserved s₀ s ∧ (VG.Proof.Blake2.initX86_64 P).post s₀ s := by
  have hxs : (VG.Proof.Blake2.X86_64.Stream.Init.key s₀).length = VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ := by simp [bytesAt]
  refine ⟨⟨hg, hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)⟩, ?_⟩
  exact repr_keyBlock P (by have := (VG.Proof.Blake2.X86_64.Stream.Init.sizes hw).2.1; omega) (hxs ▸ hkb) hst
    fun h => by rw [hxs]; exact hb (hxs ▸ h)

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ : State} (hP : VG.Proof.Blake2.X86_64.Stream.Ok P)
    (hp : (VG.Proof.Blake2.initX86_64 P).pre s₀) :
    WP isa (Impl.Blake2.X86_64.Stream.init P) s₀ fun s' =>
      gprPreserved s₀ s' ∧ (VG.Proof.Blake2.initX86_64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, hret, -, -, hkk⟩ := hp
  have hw := hP.w
  have hs := VG.Proof.Blake2.X86_64.Stream.Init.sizes hw
  have hmax := hP.max
  have hkb : VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ ≤ blockBytes w := Nat.le_trans hkk hmax
  have hsub : ∀ r ∈ [(⟨VG.Proof.Blake2.X86_64.Stream.Init.st s₀, bufOff w⟩ : Region)], ∃ r' ∈ [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .rcx := by decide
  unfold Impl.Blake2.X86_64.Stream.init
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Init.initState_ok (P := P) hw (fun a n h => ?_) (by omega)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  refine WP.ite (decide (VG.Proof.Blake2.X86_64.Stream.Init.kk s₀ = 0)) hσ.zf (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact VG.Proof.Blake2.X86_64.Stream.Init.finish hw hkb hret (fun r hr => hσ.gpr r (hcs r hr).1 (hcs r hr).2.1) (hσ.frame.sub hsub)
      hσ.state fun h => absurd hb h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (VG.Proof.Blake2.X86_64.Stream.Init.keyBlock_ok hw hrd hwr hd (by omega) hkb hσ) fun s ⟨hg, hf, hb'⟩ => ?_
    have hf' : Frame [VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w] σ.mem s.mem := hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Blake2.X86_64.Stream.Init.stR s₀ w, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
    refine VG.Proof.Blake2.X86_64.Stream.Init.finish hw hkb hret (fun r hr => hg r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2)
      ((hσ.frame.sub hsub).trans hf') ?_ fun _ => hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨VG.Proof.Blake2.X86_64.Stream.Init.st s₀, bufOff w⟩)
      (by simpa using Offset.base_disjoint (VG.Proof.Blake2.X86_64.Stream.Init.st s₀) (Nat.le_refl (bufOff w)) (n := blockBytes w) (by omega))
      (by simp only; omega) hi

end VG.Proof.Blake2.X86_64.Stream.Init

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Stream.Finalize`. -/
section

/-!
# Streaming BLAKE2 on x86-64: `finalize`

`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_ok`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`compressWith_ok`), copies the
hash value out (`output_ok`) and restores the registers (`restore_ok`).
-/

namespace VG.Proof.Blake2.X86_64.Stream.Finalize

open VG VG.X86_64 VG.Spec.Blake2
open VG.Impl.Blake2.X86_64.Stream (saved save restore output)
open VG.Impl.Blake2.X86_64 (at_ compress)
open VG.Proof.Blake2 (finalizeX86_64 bufOff final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.Proof.Blake2.X86_64.Stream (Ok N_eq B_eq CalleeOk CallOk Setup compressWith_ok)
open VG.Proof.Blake2.X86_64.Stream.Init (ea_at writeBytes_at)
open VG.Proof.MdStream.X86_64 (Upd WP.cons wp_mov wp_movm wp_mov32i wp_store wp_store8 wp_addi wp_subi
  wp_sub wp_andi wp_test ofInt_natCast sx1 sx_ofNat zx_ofNat and_mask sub_ofNat ofNat_succ ofNat_pred
  ofNat_beq_zero toNat_ofNat_lt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev op : Addr := s₀.gpr .rdx
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.op s₀, bufOff w⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀, 576⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀) s₀.gpr saved

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀]
  st_out : (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w)
  st_scr : (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀)
  out_scr : (VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀)
  ret_st : (VG.Proof.Blake2.X86_64.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w)
  ret_out : (VG.Proof.Blake2.X86_64.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w)
  ret_scr : (VG.Proof.Blake2.X86_64.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀)
  stk_st : (VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w)
  stk_out : (VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w)
  stk_scr : (VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀)

theorem pre_of {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ : State} (h : (VG.Proof.Blake2.finalizeX86_64 P).pre s₀) : VG.Proof.Blake2.X86_64.Stream.Finalize.Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem ret_stk (s₀ : State) : (VG.Proof.Blake2.X86_64.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀) :=
  Offset.base_disjoint_below _ (by decide)

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w : Nat} {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Finalize.Pre w s₀) {m m' : Mem} (h : VG.Proof.Blake2.X86_64.Stream.Finalize.Saved s₀ m)
    (hf : Frame [VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w, ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀, 512⟩, VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀] m m') : VG.Proof.Blake2.X86_64.Stream.Finalize.Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have := VG.Proof.Blake2.X86_64.Stream.Finalize.saved_bound p hp'
    have hsub : Region.Sub ⟨Spill.slot (VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀) p.2, 8⟩ (VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left hsub
    · exact hp.out_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.stk_scr.symm.sub_left hsub

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀
  r15 : s.gpr .r15 = VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀
  rbp : s.gpr .rbp = VG.Proof.Blake2.X86_64.Stream.Finalize.op s₀
  r14 : s.gpr .r14 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀ + BitVec.ofNat 64 512, 48⟩] s₀.mem s.mem
  saved : VG.Proof.Blake2.X86_64.Stream.Finalize.Saved s₀ s.mem

theorem prologue_ok {w : Nat} {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Finalize.Pre w s₀) :
    WP isa (.block (save .rcx ++ ([.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rsi)] : List Instr))) s₀ (VG.Proof.Blake2.X86_64.Stream.Finalize.Start s₀) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .rcx saved s₀ fun p hp' => ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  · have := VG.Proof.Blake2.X86_64.Stream.Finalize.saved_bound p hp'
    exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  have f₁ : Frame [⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀ + BitVec.ofNat 64 512, 48⟩] s₀.mem s₁.mem :=
    m₁ ▸ Spill.saveMem_frame _ _ _ _ fun p hp' => by
      have := VG.Proof.Blake2.X86_64.Stream.Finalize.saved_bound p hp'; exact Offset.contains _ (by omega) (by omega) (by omega)
  have v₁ : VG.Proof.Blake2.X86_64.Stream.Finalize.Saved s₀ s₁.mem := m₁ ▸ Spill.saveMem_saved _ _ _ _ (by decide)
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ =>
    wp_mov fun s₅ u₅ _ _ => WP.block_nil ?_
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁], ?_, ?_, ?_,
    ?_, ?_, by rw [hm]; exact f₁, by rw [hm]; exact v₁⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]

/-! ## The number of buffered bytes -/

section
variable {w : Nat}

theorem bufLen_ok (hP : blockBytes w = 64 ∨ blockBytes w = 128) {s : State} :
    WP isa (Impl.Blake2.X86_64.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (bufLen w (s.gpr .r14).toNat) ∧
      (∀ r, r ≠ .r13 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.Blake2.X86_64.Stream.bufLen
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_)
  have hn := (s.gpr .r14).isLt
  generalize hn' : (s.gpr .r14).toNat = n at hn
  have hr14 : s.gpr .r14 = BitVec.ofNat 64 n := by rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have g : ∀ r, r ≠ .r13 → s₅.gpr r = s.gpr r := fun r h => by
    rw [g₅, u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have hm : s₅.mem = s.mem := by rw [m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₅.rd = s.rd := by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₅.wr = s.wr := by rw [wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hz : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← congrFun g₅ .r14, g .r14 (by decide), BitVec.and_self, hr14, ofNat_beq_zero hn]
  refine WP.ite (decide (n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_mov32i fun s₆ u₆ _ _ => WP.block_nil ⟨?_, fun r h => by rw [u₆.other r h, g r h],
      by rw [u₆.mem, hm], by rw [u₆.rd, hrd], by rw [u₆.wr, hwr]⟩
    rw [u₆.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr⟩
    rw [g₅, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hr14, sx1, ofNat_pred (by omega), VG.Proof.Blake2.X86_64.Stream.B_eq, and_mask hP,
      toNat_ofNat_lt (by omega), ← ofNat_succ]
    simp only [bufLen, hb, ↓reduceIte]

/-! ## Zeroing the rest of the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r13 : s.gpr .r13 = BitVec.ofNat 64 (r + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .rax → x ≠ .r13 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer, from byte `r` on (in `r13`). -/
theorem zeroLoop_ok {s₀ : State} {st : Addr} {r k : Nat} (hk : 1 ≤ k) (hk' : r + k < 2 ^ 32)
    (hrbx : s₀.gpr .rbx = st) (hr13 : s₀.gpr .r13 = BitVec.ofNat 64 r)
    (hrax : s₀.gpr .rax = BitVec.ofNat 64 k) (hr9 : s₀.gpr .r9 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, VG.Proof.Blake2.X86_64.Stream.Finalize.ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (Impl.Blake2.X86_64.Stream.zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.X86_64.Stream.Finalize.ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by rw [hr13, Nat.add_zero], by rw [hrax, Nat.sub_zero],
      fun _ _ _ => rfl, rfl, rfl, by rw [List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hrbx' : s.gpr .rbx = st := by rw [h.other .rbx (by decide) (by decide), hrbx]
  refine wp_store8 (r := .r9) (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) ?_
    (by rw [h.wr]; exact hdst j hj) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, Impl.Blake2.X86_64.Stream.bufByte, hrbx', h.r13, VG.Proof.Blake2.X86_64.Stream.N_eq, BitVec.ofNat_add,
      BitVec.mul_one, VG.Proof.MdStream.X86_64.ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ hz₄ => WP.block_nil ?_
  have hrax' : s₄.gpr .rax = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other .rax (by decide), g₂, h.rax, sx1, ofNat_pred (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.X86_64.Stream.Finalize.ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hrax', fun x h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₄.other .r13 (by decide), u₃.gpr, g₂, h.r13, sx1, ← Nat.add_assoc, ofNat_succ]
    · rw [u₄.other x h1, u₃.other x h2, g₂, h.other x h1 h2]
    · rw [u₄.rd, u₃.rd, rd₂, h.rd]
    · rw [u₄.wr, u₃.wr, wr₂, h.wr]
    · rw [u₄.mem, u₃.mem, m₂, h.other .r9 (by decide) (by decide), hr9, h.mem,
        List.replicate_succ', VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hzf : s₄.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₄, u₃.other .rax (by decide), g₂, h.rax, sx1, ofNat_pred (show 1 ≤ k - j by omega),
      ofNat_beq_zero (by omega), show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

/-- Zeroing the buffer from byte `r` (in `r13`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2 ^ 31) (hrbx : s.gpr .rbx = st) (hr13 : s.gpr .r13 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (Impl.Blake2.X86_64.Stream.pad (w := w)) s fun s' =>
      (∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .r13 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold Impl.Blake2.X86_64.Stream.pad
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_mov32i fun s₂ u₂ _ _ => wp_sub fun s₃ u₃ z₃ =>
    WP.block_nil ?_)
  have g : ∀ x, x ≠ .r9 → x ≠ .rax → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  have hrax : s₃.gpr .rax = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .r13 (by decide), u₂.gpr, u₁.other .r13 (by decide), hr13, VG.Proof.Blake2.X86_64.Stream.B_eq,
      zx_ofNat (by omega), sub_ofNat hr]
  have hz : s₃.zf = some (decide (blockBytes w - r = 0)) := by
    rw [z₃, ← u₃.gpr, hrax, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (blockBytes w - r = 0)) hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ => g x h1 h2, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], ?_⟩
    rw [hb, List.replicate_zero, VG.WriteBytes.writeBytes_nil, u₃.mem, u₂.mem, u₁.mem]
  · simp only [decide_eq_false_iff_not] at hb
    have hwr : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
    refine VG.Proof.Blake2.X86_64.Stream.Finalize.zeroLoop_ok (st := st) (r := r) (by omega) (by omega)
      (by rw [g _ (by decide) (by decide), hrbx])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr13]) hrax
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl)
      (fun i hi => by rw [hwr]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 => by rw [h.other x h2 h3, g x h1 h2], by rw [h.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [h.wr, hwr], ?_⟩
    rw [h.mem, u₃.mem, u₂.mem, u₁.mem]

end

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = VG.WriteBytes.writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Blake2.X86_64.Stream.Init.writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = VG.WriteBytes.writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    bytesAt m' (st + BitVec.ofNat 64 N) bb =
      bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv_lhs => rw [show bb = r + (bb - r) by omega]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      VG.WriteBytes.writeBytes_before m st _ (by omega : N + i < N + r) (by simp; omega)]
  · rw [hm]; exact VG.Proof.Blake2.X86_64.Stream.Finalize.bytesAt_writeBytes_self _ _ (by simp) (by omega)

/-! ## The call -/

section
variable {w : Nat}

theorem args_ok {σ : State} (hN : bufOff w < 2 ^ 31) :
    WP isa (.block (([.mov .rdi (.reg .rbx)] : List Instr) ++
      ([.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (Impl.Blake2.X86_64.Stream.N w))),
        .mov32 .rdx (.imm 1), .mov .rcx (.reg .r14), .mov32 .r8 (.imm 1)] : List Instr) ++
      ([.mov .r9 (.reg .r15)] : List Instr))) σ
      fun s => VG.Proof.Blake2.X86_64.Stream.Setup σ s (σ.gpr .rbx + BitVec.ofNat 64 (bufOff w)) 1 (σ.gpr .r14) true := by
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ =>
    wp_mov fun s₅ u₅ _ _ => wp_mov32i fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₇.gpr r = σ.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h2,
        u₁.other r h1]
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ≠ .r9 := by
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), VG.Proof.Blake2.X86_64.Stream.N_eq, sx_ofNat hN]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.gpr]; rfl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · have h := hcs r hr
    exact g r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem callOk_of {s₀ σ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Finalize.Pre w s₀) (hs : bufOff w + blockBytes w < 2 ^ 32)
    (hrd : σ.rd = s₀.rd) (hwr : σ.wr = s₀.wr) (hrbx : σ.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀) (hr15 : σ.gpr .r15 = VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀)
    (hsp : σ.gpr .rsp = s₀.gpr .rsp) :
    VG.Proof.Blake2.X86_64.Stream.CallOk (w := w) σ (VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀) (VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀) (VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (1 : BitVec 64).toNat) := by
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mul_one]
  have hstN : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀, bufOff w⟩ (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w) := Region.sub_prefix (by omega)
  have hbuf : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w) :=
    Offset.sub_base _ (by omega)
  have hscr : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀, 512⟩ (VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀) := Region.sub_prefix (by omega)
  refine ⟨hrbx, hr15, (hp.st_scr.sub_left hstN).sub_right hscr,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hp.st_scr.sub_left hbuf).sub_right hscr,
    by rw [hsp]; exact hp.stk_st.sub_right hstN, by rw [hsp]; exact hp.stk_scr.sub_right hscr,
    by rw [hsp]; exact hp.stk_st.sub_right hbuf, ?_, ?_, by omega, by omega⟩
  · rw [hrd, hwr, hp.rd, hp.wr, List.nil_append]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, by simp, bufOff w, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩

end

/-! ## Copying the hash value out -/

section
variable {w : Nat}

theorem output_eq : output (w := w) = (List.range (Impl.Blake2.X86_64.Stream.N w / 8)).flatMap fun k =>
    [.mov .rax (.mem (at_ .rbx (8 * k))), .store (at_ .rbp (8 * k)) .rax] := rfl

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .rax → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
    s.mem = VG.WriteBytes.writeBytes σ.mem (σ.gpr .rbp) (bytesAt σ.mem (σ.gpr .rbx) (8 * k))

theorem output_ok {σ : State} (hN : bufOff w < 2 ^ 32) (hN8 : bufOff w % 8 = 0)
    (hin : ∀ a n, (⟨σ.gpr .rbx, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .rbp, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .rbx, bufOff w⟩ ⟨σ.gpr .rbp, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .rax → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      s.mem = VG.WriteBytes.writeBytes σ.mem (σ.gpr .rbp) (bytesAt σ.mem (σ.gpr .rbx) (bufOff w)) := by
  have e : 8 * (Impl.Blake2.X86_64.Stream.N w / 8) = bufOff w := by rw [VG.Proof.Blake2.X86_64.Stream.N_eq]; omega
  rw [VG.Proof.Blake2.X86_64.Stream.Finalize.output_eq, ← e]
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86_64.Stream.Finalize.OInv σ) (fun k s hk ⟨hg, hrd, hwr, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Blake2.X86_64.Stream.N_eq] at hk
  have hk8 : 8 * k + 8 ≤ bufOff w := by omega
  have hl : (bytesAt σ.mem (σ.gpr .rbx) (8 * k)).length = 8 * k := by simp [bytesAt]
  refine wp_movm (a := σ.gpr .rbx + BitVec.ofNat 64 (8 * k))
    (by rw [VG.Proof.Blake2.X86_64.Stream.Init.ea_at, hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ hk8 (by omega)))
    fun s₁ u₁ => wp_store (a := σ.gpr .rbp + BitVec.ofNat 64 (8 * k)) ?_ ?_ fun s₂ g₂ m₂ rd₂ wr₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂, u₁.other r hr, hg r hr], by rw [rd₂, u₁.rd, hrd],
        by rw [wr₂, u₁.wr, hwr], ?_⟩
  · rw [VG.Proof.Blake2.X86_64.Stream.Init.ea_at, u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ hk8 (by omega))
  · have hv : s.mem.readW (σ.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64 =
        σ.mem.readW (σ.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64 := by
      rw [hm]
      exact (VG.WriteBytes.writeBytes_frame (R := ⟨σ.gpr .rbp, bufOff w⟩) _ _ _
        (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by omega))).readW
        (Offset.contains_base (k := bufOff w) _ hk8 (by omega)) (by simpa using hd) (by decide)
    have e := VG.WriteBytes.writeBytes_append σ.mem (σ.gpr .rbp) (bytesAt σ.mem (σ.gpr .rbx) (8 * k))
      (wordBytes (σ.mem.readW (σ.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64))
      (by rw [hl]; simp [wordBytes]; omega)
    rw [hl] at e
    rw [m₂, u₁.gpr, u₁.mem, hv, hm, VG.Proof.Blake2.X86_64.Stream.Finalize.writeW_eq, e, VG.Proof.Blake2.wordBytes_readW _ _ (.inr rfl),
      ← bytesAt_add, Nat.mul_succ]

end

/-! ## The epilogue -/

theorem restore_ok {w : Nat} {s₀ s₁ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Finalize.Pre w s₀) (hr15 : s₁.gpr .r15 = VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀)
    (hsp : s₁.gpr .rsp = s₀.gpr .rsp) (hwr : s₁.wr = s₀.wr) (hsv : VG.Proof.Blake2.X86_64.Stream.Finalize.Saved s₀ s₁.mem) :
    WP isa (.block restore) s₁ fun s =>
      (∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) ∧ s.mem = s₁.mem := by
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₁ (by decide) (fun p hp' => ?_)
    (by rw [hr15]; exact hsv)) fun s' ⟨h₁, h₂, m, _⟩ => ⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hsp, m⟩
  have := VG.Proof.Blake2.X86_64.Stream.Finalize.saved_bound p hp'
  rw [hr15]
  exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, by simp [hwr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩

/-! ## The whole function -/

theorem correct {callee : Impl.Blake2.X86_64.Stream.Callee} {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ : State} (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code)
    (hpre : (VG.Proof.Blake2.finalizeX86_64 P).pre s₀) :
    WP isa (Impl.Blake2.X86_64.Stream.finalize P callee) s₀ fun s' =>
      gprPreserved s₀ s' ∧ (VG.Proof.Blake2.finalizeX86_64 P).post s₀ s' := by
  have hp := VG.Proof.Blake2.X86_64.Stream.Finalize.pre_of hpre
  have hw := hP.w
  obtain ⟨hs, hs16, -, -, -⟩ := Init.sizes hw
  have hbb := hP.bb
  have hNe := hP.N
  have hN8 : bufOff w % 8 = 0 := by simp only [bufOff]; omega
  have hN : bufOff w < 2 ^ 31 := by omega
  have hstN : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀, bufOff w⟩ (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w) := Region.sub_prefix (by omega)
  have hsave_st : ∀ r ∈ [(⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀ + BitVec.ofNat 64 512, 48⟩ : Region)], (VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega))
  unfold Impl.Blake2.X86_64.Stream.finalize
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Finalize.prologue_ok hp) fun s₁ h₁ => ?_)
  have hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ + BitVec.ofNat 64 i) :=
    fun i hi => h₁.frame.bytes (R := VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w) hsave_st (by simp only; omega) hi
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Finalize.bufLen_ok hbb) fun s₂ ⟨r13₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  rw [h₁.r14] at r13₂
  generalize hn : (s₀.gpr .rsi).toNat = n at r13₂
  have hr : bufLen w n ≤ blockBytes w := bufLen_le (by omega) n
  have hrbx₂ : s₂.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ := by rw [g₂ _ (by decide), h₁.rbx]
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Finalize.pad_ok (st := VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀) hr (by omega) hrbx₂ r13₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have g₃' : ∀ r, r ≠ .r9 → r ≠ .rax → r ≠ .r13 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 => by
    rw [g₃ r h1 h2 h3, g₂ r h3]
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have hsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.rsp]
  have hrbx₃ : s₃.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.rbx]
  have hm₃ : s₃.mem = VG.WriteBytes.writeBytes s₁.mem (VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ + BitVec.ofNat 64 (bufOff w + bufLen w n))
      (List.replicate (blockBytes w - bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  refine WP.seq (VG.Proof.Blake2.X86_64.Stream.compressWith_ok hf (WP.mono (VG.Proof.Blake2.X86_64.Stream.Finalize.args_ok (σ := s₃) hN) fun s' h => by rw [hrbx₃] at h; exact h)
    (VG.Proof.Blake2.X86_64.Stream.Finalize.callOk_of hp hs hrd₃ hwr₃ hrbx₃ (by rw [g₃' _ (by decide) (by decide) (by decide), h₁.r15]) hsp₃)
    fun s₄ rd₄ wr₄ cs₄ f₄ e₄ => ?_)
  have hrbx₄ : s₄.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Finalize.st s₀ := by rw [cs₄ _ (by decide), hrbx₃]
  have hrbp₄ : s₄.gpr .rbp = VG.Proof.Blake2.X86_64.Stream.Finalize.op s₀ := by
    rw [cs₄ _ (by decide), g₃' _ (by decide) (by decide) (by decide), h₁.rbp]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.X86_64.Stream.Finalize.output_ok (σ := s₄) (by omega) hN8 (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hrbx₄] at h
    exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega⟩
  · rw [hwr₄, hp.wr]
    rw [hrbp₄] at h
    exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w, by simp, h⟩
  · rw [hrbx₄, hrbp₄]; exact hp.st_out.sub_left hstN
  -- What the calls and stores wrote.
  have F₁ : Frame [VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w, ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scr s₀, 512⟩, VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀] s₁.mem s₅.mem := by
    have f₃ : Frame [VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega) (by omega))
    have f₅ : Frame [VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hrbp₄]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by simp [bytesAt]))
    rw [hsp₃] at f₄
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine WP.mono (VG.Proof.Blake2.X86_64.Stream.Finalize.restore_ok hp (by rw [g₅ _ (by decide), cs₄ _ (by decide),
                                             g₃' _ (by decide) (by decide) (by decide), h₁.r15])
    (by rw [g₅ _ (by decide), cs₄ _ (by decide), hsp₃]) (by rw [wr₅, hwr₄])
    (h₁.saved.frame hp F₁)) fun s₆ ⟨cs₆, m₆⟩ => ?_
  refine ⟨⟨cs₆, ?_⟩, fun h0 d hR hlt hcnt => ?_⟩
  · have F₀ : Frame [VG.Proof.Blake2.X86_64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, VG.Proof.Blake2.X86_64.Stream.Finalize.stkR s₀] s₀.mem s₆.mem := by
      rw [m₆]
      refine (h₁.frame.sub fun r hr => ?_).trans (F₁.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, by simp, Offset.sub_base _ (by omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨VG.Proof.Blake2.X86_64.Stream.Finalize.scR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    exact F₀.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_out, hp.ret_scr, VG.Proof.Blake2.X86_64.Stream.Finalize.ret_stk s₀⟩) (by decide)
  · have hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    have hr14 : (s₃.gpr .r14).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide), h₁.r14, hn]
    rw [m₆, m₅, hrbp₄, hrbx₄, VG.Proof.Blake2.X86_64.Stream.Finalize.bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega),
      bytesAt_state _ _ (hw.symm), e₄, show (1 : BitVec 64).toNat = 0 + 1 from rfl, compressBlocks_succ,
      compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero, hr14]
    refine final_eq P (by omega) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, VG.WriteBytes.writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + bufLen w d.length)
          (by simp; omega), hkeep i (by omega)]
    · rw [VG.Proof.Blake2.X86_64.Stream.Finalize.pad_bytes hr (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega)]

end VG.Proof.Blake2.X86_64.Stream.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Stream.Update`. -/
section

/-!
# Streaming BLAKE2 on x86-64: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`).
-/

namespace VG.Proof.Blake2.X86_64.Stream.Update

open VG VG.X86_64 VG.Spec.Blake2
open VG.Impl.Blake2.X86_64.Stream
open VG.Impl.Blake2.X86_64 (at_ compress)
open VG.Proof.MdStream.X86_64 (Upd ofInt_natCast toNat_ofNat_lt wp_mov wp_movm wp_store
  wp_addi wp_subi wp_sub wp_add wp_cmp wp_test wp_movzx8 wp_store8 wp_mov32i wp_andi wp_shr test_ok
  sx1 ofNat_succ ofNat_pred ofNat_beq_zero sub_ofNat contains_offset contains_offset' sub_offset ea_at
  Saved saveMem saveMem_saved saveMem_frame)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR stateAt_congr
  bytesAt_congr bytesAt_add blockAt_congr compressBlocks_congr)

variable {w : Nat} {P : VG.Spec.Blake2.Params w} {callee : Impl.Blake2.X86_64.Stream.Callee}

/-! ## Saving the caller's registers

As the Merkle–Damgård hash functions do, after the compression function's
512 bytes of scratch space. -/

/-- The Merkle–Damgård streaming parameters with the same saved registers. -/
def mdP : Impl.MdStream.X86_64.Params := ⟨1, 64, 1, 512, [], []⟩

theorem mdP_dims : MdStream.X86_64.Dims VG.Proof.Blake2.X86_64.Stream.Update.mdP := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem save_eq (b : Reg) : save b = Impl.MdStream.X86_64.save VG.Proof.Blake2.X86_64.Stream.Update.mdP b := rfl
theorem restore_eq' : restore = Impl.MdStream.X86_64.restore VG.Proof.Blake2.X86_64.Stream.Update.mdP := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev dp : Addr := s₀.gpr .rdx
abbrev len : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Update.st s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Update.dp s₀, VG.Proof.Blake2.X86_64.Stream.Update.len s₀⟩
/-- Where the calls of the compression function store the return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
abbrev scR : Region := ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, 576⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.X86_64.Stream.Update.dR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Update.scR s₀]
  st_scr : (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.scR s₀)
  d_st : (VG.Proof.Blake2.X86_64.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w)
  d_scr : (VG.Proof.Blake2.X86_64.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.scR s₀)
  ret_st : (VG.Proof.Blake2.X86_64.Stream.Update.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w)
  ret_scr : (VG.Proof.Blake2.X86_64.Stream.Update.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.scR s₀)
  stk_st : (VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w)
  stk_d : (VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.dR s₀)
  stk_scr : (VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.scR s₀)

theorem pre_of {s₀ : State} (h : (VG.Proof.Blake2.updateX86_64 P).pre s₀) : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem ret_stk (s₀ : State) : (VG.Proof.Blake2.X86_64.Stream.Update.retR s₀).Disjoint (VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega)
  rwa [BitVec.sub_add_cancel] at this

theorem len_lt (s₀ : State) : VG.Proof.Blake2.X86_64.Stream.Update.len s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
theorem cnt_lt (s₀ : State) : VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ < 2 ^ 64 := (s₀.gpr .rsi).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : VG.Spec.Blake2.Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) d ∧ s₀.gpr .rsi = BitVec.ofNat 64 d.length ∧
    d.length + VG.Proof.Blake2.X86_64.Stream.Update.len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : VG.Proof.Blake2.X86_64.Stream.Update.R₀ P s₀ h0 d) :
    VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega)]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.Blake2.X86_64.Stream.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Update.st s₀
  r15 : s.gpr .r15 = VG.Proof.Blake2.X86_64.Stream.Update.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ + c)
  frame : Frame [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.X86_64.Saved VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8 s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : VG.Spec.Blake2.Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s where
  r13 : s.gpr .r13 = BitVec.ofNat 64 r
  repr : ∀ h0 d, VG.Proof.Blake2.X86_64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ c) r

theorem Common.congr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg]; exact h.rbx
  r15 := by rw [hg]; exact h.r15
  rsp := by rw [hg]; exact h.rsp
  rbp := by rw [hg]; exact h.rbp
  r12 := by rw [hg]; exact h.r12
  r14 := by rw [hg]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.rbx, .r15, .rsp, .rbp, .r12, .r14]

theorem ne_rax : ∀ x ∈ VG.Proof.Blake2.X86_64.Stream.Update.commonRegs, x ≠ .rax := by decide
theorem ne_r13 : ∀ x ∈ VG.Proof.Blake2.X86_64.Stream.Update.commonRegs, x ≠ .r13 := by decide

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s)
    (hg : ∀ r ∈ VG.Proof.Blake2.X86_64.Stream.Update.commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  r14 := by rw [hg _ (by simp)]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.congr' {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s)
    (hg : ∀ r, r ≠ .r13 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s' :=
  h.of_gpr (fun r hr => hg r (VG.Proof.Blake2.X86_64.Stream.Update.ne_r13 r hr)) hm hrd hwr

theorem Inv.congr {s₀ : State} {c r : Nat} {s s' : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c r s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c r s' :=
  { h.toCommon.congr hg hm hrd hwr with
    r13 := by rw [hg]; exact h.r13
    repr := by rw [hm]; exact h.repr }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c : Nat} {s : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s) {i : Nat}
    (hi : i < VG.Proof.Blake2.X86_64.Stream.Update.len s₀) : s.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := VG.Proof.Blake2.X86_64.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (Nat.le_of_lt (VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀)) hi

/-! ## Prologue -/

theorem common_zero {s₀ : State} {s : State} (hm : s.mem = VG.Proof.MdStream.X86_64.saveMem VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hrbx : s.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (hr15 : s.gpr .r15 = VG.Proof.Blake2.X86_64.Stream.Update.scr s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrbp : s.gpr .rbp = VG.Proof.Blake2.X86_64.Stream.Update.dp s₀) (hr12 : s.gpr .r12 = s₀.gpr .rcx)
    (hr14 : s.gpr .r14 = s₀.gpr .rsi) : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ 0 s where
  c_le := Nat.zero_le _
  rd := hrd
  wr := hwr
  rbx := hrbx
  r15 := hr15
  rsp := hrsp
  rbp := by rw [hrbp]; simp
  r12 := by rw [hr12]; simp
  r14 := by rw [hr14]; simp
  frame := by
    rw [hm]
    exact (VG.Proof.MdStream.X86_64.saveMem_frame VG.Proof.Blake2.X86_64.Stream.Update.mdP_dims).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, by simp, Region.sub_prefix (by decide)⟩
  saved := by rw [hm]; exact VG.Proof.MdStream.X86_64.saveMem_saved VG.Proof.Blake2.X86_64.Stream.Update.mdP_dims

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s => VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ 0 s ∧ s.mem = VG.Proof.MdStream.X86_64.saveMem VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8 := by
  have o : ∀ d : Nat, d + 8 ≤ 512 + 48 → InRegions s₀.wr (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, by simp [hp.wr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 512 (by omega); have o1 := o (512 + 8) (by omega); have o2 := o (512 + 16) (by omega)
  have o3 := o (512 + 24) (by omega); have o4 := o (512 + 32) (by omega); have o5 := o (512 + 40) (by omega)
  apply WP.of_runBlock
  rw [updateStart, VG.Proof.Blake2.X86_64.Stream.Update.save_eq, MdStream.X86_64.save_eq]
  simp only [List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, VG.Proof.MdStream.X86_64.ea_at, VG.Proof.Blake2.X86_64.Stream.Update.mdP,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Blake2.X86_64.Stream.Update.common_zero rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩ <;>
    simp (config := {decide := true}) only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
      not_false_eq_true]

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  have hN : bufOff w + blockBytes w < 2 ^ 64 := by rcases hP.bb with h | h <;> rw [hP.N, h] <;> decide
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

/-! ## The bytes in the buffer -/

theorem mask_mod (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (x : BitVec 64) :
    x &&& (BitVec.ofNat 32 (B w - 1)).signExtend 64 = BitVec.ofNat 64 (x.toNat % blockBytes w) :=
  MdStream.X86_64.and_mask hP.bb x

theorem bufLen_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {s : State} (hC : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ 0 s)
    (hm : s.mem = VG.Proof.MdStream.X86_64.saveMem VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8) :
    WP isa (Impl.Blake2.X86_64.Stream.bufLen (w := w)) s (VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ 0 (Blake2.bufLen w (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀))) := by
  have hc := VG.Proof.Blake2.X86_64.Stream.Update.cnt_lt s₀
  have hbb := hP.bb
  have h14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀) := by rw [hC.r14, Nat.add_zero]
  -- The representation.
  have hrepr : ∀ h0 d, VG.Proof.Blake2.X86_64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ 0) (Blake2.bufLen w (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀)) := by
    intro h0 d hd
    have e : VG.Proof.Blake2.X86_64.Stream.Update.D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine VG.Proof.Blake2.X86_64.Stream.Update.repr_congr hP (fun i hi => ?_) hd.1
    have hN : bufOff w + blockBytes w ≤ 2 ^ 64 := by
      rcases hbb with h | h <;> rw [hP.N, h] <;> decide
    have hd : (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w).Disjoint ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, mdP.so + 48⟩ :=
      hp.st_scr.sub_right (Region.sub_prefix (by decide))
    rw [hm]
    exact (VG.Proof.MdStream.X86_64.saveMem_frame VG.Proof.Blake2.X86_64.Stream.Update.mdP_dims).bytes (R := VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w) (by simpa using hd) hN hi
  unfold Impl.Blake2.X86_64.Stream.bufLen
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_andi fun s₃ u₃ =>
    wp_addi fun s₄ u₄ => wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r13 → s₅.gpr r = s.gpr r := fun r h => by
    rw [g₅, u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have hm₅ : s₅.mem = s.mem := by rw [m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₅.rd = s.rd := by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₅.wr = s.wr := by rw [wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hC₅ : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ 0 s₅ := hC.congr' g hm₅ hrd hwr
  have hz : isa.eval .e s₅ = some (decide (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ = 0)) := by
    have e : s₄.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h14]
    simp only [eval, z₅, e, BitVec.and_self, ofNat_beq_zero hc]
  refine WP.ite (decide (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_mov32i fun s₆ u₆ _ _ => WP.block_nil ?_
    refine { hC₅.congr' (fun r h => u₆.other r h) u₆.mem u₆.rd u₆.wr with r13 := ?_, repr := ?_ }
    · rw [u₆.gpr, Blake2.bufLen, hb]; rfl
    · rw [u₆.mem, hm₅]; exact hrepr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₅ with r13 := ?_, repr := ?_ }
    · rw [g₅, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h14, sx1, ofNat_pred (by omega), VG.Proof.Blake2.X86_64.Stream.Update.mask_mod hP,
        toNat_ofNat_lt (by omega), Blake2.bufLen, ite_eq_right_of_eq_false _ _ (eq_false hb), ← ofNat_succ]
    · rw [hm₅]; exact hrepr

/-! ## Copying data into the buffer -/

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact VG.WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, VG.WriteBytes.writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-- Writes to the state, the compression function's scratch space and below
the stack keep the saved registers. -/
theorem saved_frame {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {m m' : Mem} (h : VG.Proof.MdStream.X86_64.Saved VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8 m)
    (hf : Frame [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, 512⟩, VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀] m m') : VG.Proof.MdStream.X86_64.Saved VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8 m' := by
  intro p hp'
  obtain ⟨h₁, h₂⟩ := MdStream.X86_64.saved_offset VG.Proof.Blake2.X86_64.Stream.Update.mdP_dims hp'
  simp only [VG.Proof.Blake2.X86_64.Stream.Update.mdP] at h₁ h₂
  rw [← h p hp']
  refine hf.readW (r := ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  have e : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩ (VG.Proof.Blake2.X86_64.Stream.Update.scR s₀) := by
    rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact sub_offset (by omega) (by omega)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact Offset.disjoint_base _ (by omega) (by omega)
  · exact hp.stk_scr.symm.sub_left e

theorem ok_len (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) : bufOff w + blockBytes w ≤ 256 := by
  rcases hP.bb with h | h <;> rw [hP.N, h] <;> decide

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ VG.Proof.Blake2.X86_64.Stream.Update.len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hrbx : s.gpr .rbx = VG.Proof.Blake2.X86_64.Stream.Update.st s₀)
    (hrbp : s.gpr .rbp = VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) (hr13 : s.gpr .r13 = BitVec.ofNat 64 r)
    (hrax : s.gpr .rax = BitVec.ofNat 64 k) (hf : Frame [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀] s₀.mem s.mem)
    (hs : VG.Proof.MdStream.X86_64.Saved VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8 s.mem)
    (hrepr : ∀ h0 d, VG.Proof.Blake2.X86_64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → s'.gpr x = s.gpr x) ∧
      s'.gpr .rbp = VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .r13 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ Frame [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀] s₀.mem s'.mem ∧
      VG.Proof.MdStream.X86_64.Saved VG.Proof.Blake2.X86_64.Stream.Update.mdP s₀ .r8 s'.mem ∧
      ∀ h0 d, VG.Proof.Blake2.X86_64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s'.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ (c + k)) (r + k) := by
  have hl := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨VG.Proof.Blake2.X86_64.Stream.Update.dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hdst : ∀ i < k, InRegions s.wr (VG.Proof.Blake2.X86_64.Stream.Update.st s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨VG.Proof.Blake2.X86_64.Stream.Update.st s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (sub_offset (by omega) (by omega))).sub_right (sub_offset (by omega) (by omega))
  refine VG.Proof.Blake2.X86_64.Stream.copyLoop_ok (w := w) hk (by omega) hrbx hrbp hr13 hrax hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : bytesAt s.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := VG.Proof.Blake2.X86_64.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
        (Nat.le_of_lt hL) (show c + i < VG.Proof.Blake2.X86_64.Stream.Update.len s₀ by omega)
  have hm : s'.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length]), hx]
  have hfw : Frame [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w] s.mem s'.mem := by
    rw [hm]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length]; exact contains_offset (by omega) (by omega))
  refine ⟨h.other, h.rbp.trans (Offset.add_add _ _ _), h.r13, h.rd.trans hrd, h.wr.trans hwr,
    hf.trans (hfw.mono (by simp)), VG.Proof.Blake2.X86_64.Stream.Update.saved_frame hp hs (hfw.mono (by simp)), fun h0 d hd => ?_⟩
  have e : d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ (c + k) = d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ c ++ bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k := by
    rw [VG.Proof.Blake2.X86_64.Stream.Update.D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length]; exact hrk) ?_ ?_
  · rwa [VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by rw [VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length]; omega)
  · rw [hm, ← Offset.add_add, VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_writeBytes _ _ _ _ (by rw [VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length]; omega)]

/-! ## Calling the compression function -/

/-- The blocks compressed are the (full) buffer or blocks of data. -/
def Src (w : Nat) (s₀ : State) (src : Addr) (n : Nat) : Prop :=
  (src = VG.Proof.Blake2.X86_64.Stream.Update.st s₀ + BitVec.ofNat 64 (bufOff w) ∧ n = blockBytes w) ∨
    ∃ c₀, src = VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + n ≤ VG.Proof.Blake2.X86_64.Stream.Update.len s₀

theorem callOk (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c : Nat} {s : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s)
    {src : Addr} {n : Nat} (hsrc : VG.Proof.Blake2.X86_64.Stream.Update.Src w s₀ src n) : VG.Proof.Blake2.X86_64.Stream.CallOk (w := w) s (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀) src n := by
  have hl := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP; have := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  have eN : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Update.st s₀, bufOff w⟩ (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, 512⟩ (VG.Proof.Blake2.X86_64.Stream.Update.scR s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨src, n⟩ (VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (VG.Proof.Blake2.X86_64.Stream.Update.dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (by omega) (by omega))
    · exact .inr (h' ▸ sub_offset (by omega) (by omega))
  have hsp := h.rsp
  refine ⟨h.rbx, h.r15, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_,
    by rw [hsp]; exact hp.stk_st.sub_right eN, by rw [hsp]; exact hp.stk_scr.sub_right eso, ?_, ?_, ?_,
    by omega, by rcases hsrc with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega⟩
  · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega) (by omega))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [hsp]
    rcases eSrc with e | e
    · exact hp.stk_st.sub_right e
    · exact hp.stk_d.sub_right e
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, by simp, bufOff w, h', by simp⟩
      · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, by simp, 0, by simp, by simp⟩

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c : Nat} {s s' : State}
    (h : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨VG.Proof.Blake2.X86_64.Stream.Update.st s₀, bufOff w⟩, ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem) :
    VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s' := by
  have hl := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP
  have hf' : Frame [VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, ⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, 512⟩, VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨VG.Proof.Blake2.X86_64.Stream.Update.scr s₀, 512⟩, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀, by simp, by rw [h.rsp]; exact fun _ h => h⟩
  exact ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hcs _ (by decide)]; exact h.rbx,
    by rw [hcs _ (by decide)]; exact h.r15, by rw [hcs _ (by decide)]; exact h.rsp,
    by rw [hcs _ (by decide)]; exact h.rbp, by rw [hcs _ (by decide)]; exact h.r12,
    by rw [hcs _ (by decide)]; exact h.r14,
    h.frame.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stR s₀ w, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨VG.Proof.Blake2.X86_64.Stream.Update.stkR s₀, by simp, fun _ h => h⟩),
    VG.Proof.Blake2.X86_64.Stream.Update.saved_frame hp h.saved hf'⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀)
    {c : Nat} {s : State} (hI : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c (blockBytes w) s) :
    WP isa (compressBuf (w := w) callee) s (VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c 0) := by
  have hl := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (VG.Proof.Blake2.X86_64.Stream.compressWith_ok (src := VG.Proof.Blake2.X86_64.Stream.Update.st s₀ + BitVec.ofNat 64 (bufOff w)) (n := 1)
    (t := BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ + c)) (last := false) hf ?_
    (by simpa using VG.Proof.Blake2.X86_64.Stream.Update.callOk hP hp hI.toCommon (.inl ⟨rfl, rfl⟩)) fun s' hrd hwr hcs hfr hst => ?_)
  · simp only [List.cons_append, List.nil_append]
    refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ =>
      wp_mov fun s₅ u₅ _ _ => wp_mov32i fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.rbx, VG.Proof.Blake2.X86_64.Stream.N_eq, MdStream.X86_64.sx_ofNat (by omega)]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.r14]
    · rw [u₇.other _ (by decide), u₆.gpr]; rfl
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_mov32i fun s₂ u₂ _ _ => WP.block_nil ?_
  have hC := hI.toCommon.after_call hP hp hrd hwr hcs hfr
  have hC₂ := hC.congr' (fun r h => u₂.other r h) u₂.mem u₂.rd u₂.wr
  refine { hC₂ with r13 := ?_, repr := fun h0 d hd => ?_ }
  · rw [u₂.gpr]; rfl
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  rw [hst, show (1 : BitVec 64).toNat = 1 from rfl, VG.Proof.Blake2.X86_64.Stream.Update.compressBlocks_one, List.length_append, VG.Proof.Blake2.X86_64.Stream.Update.D, VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length, ← hd.cnt_eq,
    toNat_ofNat_lt (by have := hd.2.2; rw [← hd.cnt_eq] at this; omega)]

/-! ## `head`: filling the buffer -/

/-- Copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c r s) :
    WP isa (VG.Impl.Blake2.X86_64.Stream.fill (w := w)) s (VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ (c + min (blockBytes w - r) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c))
      (r + min (blockBytes w - r) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c))) := by
  have hl := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  have hcn := VG.Proof.Blake2.X86_64.Stream.Update.cnt_lt s₀
  have hc := hI.c_le
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold VG.Impl.Blake2.X86_64.Stream.fill
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r13, VG.Proof.Blake2.X86_64.Stream.B_eq,
      MdStream.X86_64.zx_ofNat (by omega), sub_ofNat hr]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.r12]
  have g₂ : ∀ x, x ≠ .rax → s₃.gpr x = s.gpr x := fun x h => by rw [g₃, u₂.other x h, u₁.other x h]
  -- `rax` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .rax = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .rax → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ fun t ht => ?_)
  · have hm : s₃.mem = s.mem := by rw [m₃, u₂.mem, u₁.mem]
    have hrd : s₃.rd = s.rd := by rw [rd₃, u₂.rd, u₁.rd]
    have hwr : s₃.wr = s.wr := by rw [wr₃, u₂.wr, u₁.wr]
    have hcf : isa.eval .b s₃ = some (decide (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c < blockBytes w - r)) := by
      simp only [eval, cf₃, h12₂, hrax₂, toNat_ofNat_lt (show VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c < 2 ^ 64 by omega),
        toNat_ofNat_lt (show blockBytes w - r < 2 ^ 64 by omega)]
    refine WP.ite _ hcf (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov fun s₄ u₄ _ _ => WP.block_nil ⟨?_, fun x h => by rw [u₄.other x h, g₂ x h],
        by rw [u₄.mem, hm], by rw [u₄.rd, hrd], by rw [u₄.wr, hwr]⟩
      rw [u₄.gpr, g₃, h12₂, ha, Nat.min_eq_right (by omega)]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, g₂, hm, hrd, hwr⟩
      rw [g₃, hrax₂, ha, Nat.min_eq_left (by omega)]
  obtain ⟨tax, tg, tm, trd, twr⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ _ => wp_add fun s₆ u₆ => wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_)
  have g₇' : ∀ x, x ≠ .rax → x ≠ .r12 → x ≠ .r14 → s₇.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [g₇, u₆.other x h3, u₅.other x h2, tg x h1]
  have h7ax : s₇.gpr .rax = BitVec.ofNat 64 a := by
    rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), tax]
  have h712 : s₇.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - (c + a)) := by
    rw [g₇, u₆.other _ (by decide), u₅.gpr, tax, tg _ (by decide), hI.r12, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have h714 : s₇.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ + (c + a)) := by
    rw [g₇, u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tax, tg _ (by decide), hI.r14, ← BitVec.ofNat_add,
      Nat.add_assoc]
  have hm₇ : s₇.mem = s.mem := by rw [m₇, u₆.mem, u₅.mem, tm]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, u₆.rd, u₅.rd, trd]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, u₆.wr, u₅.wr, twr]
  have hz : isa.eval .e s₇ = some (decide (a = 0)) := by
    have e : s₆.gpr .rax = BitVec.ofNat 64 a := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), tax]
    simp only [eval, z₇, e, BitVec.and_self, ofNat_beq_zero (show a < 2 ^ 64 by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    have hg : ∀ x, x ≠ .rax → x ≠ .r12 → x ≠ .r14 → s₇.gpr x = s.gpr x := g₇'
    refine WP.block_nil ⟨⟨by omega, hrd₇.trans hI.rd, hwr₇.trans hI.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rbx
    · rw [hg _ (by decide) (by decide) (by decide)]; exact hI.r15
    · rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rsp
    · rw [hg _ (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.rbp
    · exact h712
    · exact h714
    · rw [hm₇]; exact hI.frame
    · rw [hm₇]; exact hI.saved
    · rw [hg _ (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.r13
    · rw [hm₇, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.copy_ok hP hp (c := c) (r := r) (k := a) (by omega) (by omega) (by omega)
      (hrd₇.trans hI.rd) (hwr₇.trans hI.wr)
      (by rw [g₇' _ (by decide) (by decide) (by decide)]; exact hI.rbx)
      (by rw [g₇' _ (by decide) (by decide) (by decide)]; exact hI.rbp)
      (by rw [g₇' _ (by decide) (by decide) (by decide)]; exact hI.r13) h7ax
      (by rw [hm₇]; exact hI.frame) (by rw [hm₇]; exact hI.saved) (by rw [hm₇]; exact hI.repr))
      fun s₈ ⟨g₈, h8bp, h813, rd₈, wr₈, f₈, sv₈, rp₈⟩ => ?_
    have e : ∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → x ≠ .r12 → x ≠ .r14 →
        s₈.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 => by rw [g₈ x h1 h2 h3 h4, g₇' x h2 h5 h6]
    refine ⟨⟨by omega, rd₈, wr₈, ?_, ?_, ?_, h8bp, ?_, ?_, f₈, sv₈⟩, h813, rp₈⟩
    · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rbx
    · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.r15
    · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rsp
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide)]; exact h712
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide)]; exact h714

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c r s ∧ ((c = VG.Proof.Blake2.X86_64.Stream.Update.len s₀ ∧ 1 ≤ r) ∨ (c < VG.Proof.Blake2.X86_64.Stream.Update.len s₀ ∧ r = 0))

theorem head_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < VG.Proof.Blake2.X86_64.Stream.Update.len s₀) {s : State} (hI : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ 0 r s) :
    WP isa (head (w := w) callee) s (VG.Proof.Blake2.X86_64.Stream.Update.HeadPost P s₀) := by
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  have hl' := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP
  unfold head
  refine WP.seq (WP.mono (test_ok .r13) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hI₁ := hI.congr g₁ m₁ rd₁ wr₁
  have hz : isa.eval .e s₁ = some (decide (r = 0)) := by
    simp only [eval, z₁, hI.r13, BitVec.and_self, ofNat_beq_zero (show r < 2 ^ 64 by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI₁, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.fill_ok hP hp hr hI₁) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.seq (WP.mono (test_ok .r12) fun s₃ ⟨g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
    have hI₃ := hI₂.congr g₃ m₃ rd₃ wr₃
    have hz₃ : isa.eval .e s₃ = some (decide (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - min (blockBytes w - r) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) = 0)) := by
      simp only [eval, z₃, hI₂.r12, BitVec.and_self,
        ofNat_beq_zero (show VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - min (blockBytes w - r) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) < 2 ^ 64 by omega)]
    refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₃, .inl ⟨by omega, by omega⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) = blockBytes w := by omega
      rw [e] at hI₃
      exact WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.compressBuf_ok hP hf hp hI₃) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

theorem ok_lg (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) : 1 ≤ Nat.log2 (B w) ∧ Nat.log2 (B w) ≤ 63 ∧ 2 ^ Nat.log2 (B w) = blockBytes w := by
  rw [VG.Proof.Blake2.X86_64.Stream.B_eq]
  rcases hP.bb with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem shr_ofNat (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {m : Nat} (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> Nat.log2 (B w) = BitVec.ofNat 64 (m / blockBytes w) := by
  obtain ⟨-, -, lgB⟩ := VG.Proof.Blake2.X86_64.Stream.Update.ok_lg hP
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c : Nat}
    (hc : c < VG.Proof.Blake2.X86_64.Stream.Update.len s₀) {s : State} (hI : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c 0 s) :
    WP isa (direct (w := w) callee) s (VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ (c + blockBytes w * ((VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := VG.Proof.Blake2.X86_64.Stream.Update.ok_len hP
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  have hcn := VG.Proof.Blake2.X86_64.Stream.Update.cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨lg₁, lg₂, -⟩ := VG.Proof.Blake2.X86_64.Stream.Update.ok_lg hP
  obtain ⟨k, hk⟩ : ∃ k, k = (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hkle : k ≤ VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_shr ⟨lg₁, lg₂⟩ fun s₃ u₃ =>
    wp_test fun s₄ g₄ m₄ rd₄ wr₄ z₄ => WP.block_nil ?_)
  have hrax : s₄.gpr .rax = BitVec.ofNat 64 k := by
    rw [g₄, u₃.gpr, u₂.gpr, u₁.gpr, hI.r12, sx1, ofNat_pred (by omega), VG.Proof.Blake2.X86_64.Stream.Update.shr_ofNat hP (by omega), hk]
  have g : ∀ x, x ≠ .rax → s₄.gpr x = s.gpr x := fun x h => by
    rw [g₄, u₃.other x h, u₂.other x h, u₁.other x h]
  have hm₄ : s₄.mem = s.mem := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [rd₄, u₃.rd, u₂.rd, u₁.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [wr₄, u₃.wr, u₂.wr, u₁.wr]
  have hz : isa.eval .e s₄ = some (decide (k = 0)) := by
    have e : s₃.gpr .rax = BitVec.ofNat 64 k := by rw [← hrax, g₄]
    simp only [eval, z₄, e, BitVec.and_self, ofNat_beq_zero (show k < 2 ^ 64 by omega)]
  have hC₄ : VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ c s₄ := hI.toCommon.of_gpr (fun x hx => g x (VG.Proof.Blake2.X86_64.Stream.Update.ne_rax x hx)) hm₄ hrd₄ hwr₄
  have h13 : s₄.gpr .r13 = BitVec.ofNat 64 0 := by rw [g _ (by decide)]; exact hI.r13
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₄, h13, by rw [hm₄]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  have hBk : blockBytes w * k + 1 ≤ VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c := by omega
  have hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega)
  have hsrc : VG.Proof.Blake2.X86_64.Stream.Update.Src w s₀ (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) (blockBytes w * (BitVec.ofNat 64 k).toNat) :=
    .inr ⟨c, rfl, by rw [toNat_ofNat_lt (by omega)]; omega⟩
  refine WP.seq (VG.Proof.Blake2.X86_64.Stream.compressWith_ok (src := VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) (n := BitVec.ofNat 64 k)
    (t := BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀ + c + blockBytes w)) (last := false) hf ?_
    (VG.Proof.Blake2.X86_64.Stream.Update.callOk hP hp hC₄ hsrc) fun s' hrd hwr hcs hfr hst => ?_)
  · simp only [List.cons_append, List.nil_append]
    refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₅ u₅ _ _ =>
      wp_addi fun s₆ u₆ => wp_mov32i fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hC₄.rbp]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hrax]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hC₄.r14, VG.Proof.Blake2.X86_64.Stream.B_eq, MdStream.X86_64.sx_ofNat (by omega),
        ← BitVec.ofNat_add]
    · rw [u₈.other _ (by decide), u₇.gpr]; rfl
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₃.mem, u₂.mem, u₁.mem]
  have hC' := hC₄.after_call hP hp hrd hwr hcs hfr
  refine wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_andi fun s₃ u₃ => wp_addi fun s₅ u₅ =>
    wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ => wp_mov fun s₉ u₉ _ _ => WP.block_nil ?_
  have hm : (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) % blockBytes w + 1 = VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - (c + blockBytes w * k) := by omega
  have hrax₅ : s₅.gpr .rax = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hC'.r12, sx1, ofNat_pred (by omega), VG.Proof.Blake2.X86_64.Stream.Update.mask_mod hP,
      toNat_ofNat_lt (by omega), ← ofNat_succ, hm]
  have h12₆ : s₆.gpr .r12 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hC'.r12, hrax₅, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have hg : ∀ x, x ≠ .rax → x ≠ .r12 → x ≠ .rbp → x ≠ .r14 → s₉.gpr x = s'.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₉.other x h2, u₈.other x h4, u₇.other x h3, u₆.other x h2, u₅.other x h1, u₃.other x h1,
      u₂.other x h1, u₁.other x h1]
  have hm₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₃.rd, u₂.rd, u₁.rd, hC'.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₃.wr, u₂.wr, u₁.wr, hC'.wr]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact hC'.rbx
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact hC'.r15
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact hC'.rsp
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), h12₆,
      u₅.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hC'.rbp, Offset.add_add]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), hrax₅]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other .r14 (by decide), u₇.other .r12 (by decide), h12₆,
      u₆.other _ (by decide), u₅.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hC'.r14, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide), hcs _ (by decide), h13]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    have e : d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ (c + blockBytes w * k) =
        d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ c ++ bytesAt s₄.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [VG.Proof.Blake2.X86_64.Stream.Update.D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₄.data hp (by omega)).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₄]; exact hI.repr h0 d hd) ?_
    rw [hst, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega), List.length_append, VG.Proof.Blake2.X86_64.Stream.Update.D, VG.Proof.Blake2.X86_64.Stream.Update.bytesAt_length,
      ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {c : Nat} (hc₁ : c < VG.Proof.Blake2.X86_64.Stream.Update.len s₀)
    (hc₂ : VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c ≤ blockBytes w) {s : State} (hI : VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ c 0 s) :
    WP isa (tail (w := w)) s (VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c)) := by
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_add fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .rax → x ≠ .r14 → x ≠ .r12 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have hax : s₃.gpr .rax = BitVec.ofNat 64 (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r12]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.copy_ok hP hp (c := c) (r := 0) (k := VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c) (by omega) (by omega) (by omega)
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rbx)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rbp)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.r13) hax
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h4bp, h413, rd₄, wr₄, f₄, sv₄, rp₄⟩ => ?_
  have e : c + (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c) = VG.Proof.Blake2.X86_64.Stream.Update.len s₀ := by omega
  rw [e] at h4bp rp₄
  rw [Nat.zero_add] at h413 rp₄
  have g : ∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → x ≠ .r14 → x ≠ .r12 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 => by rw [g₄ x h1 h2 h3 h4, hg x h2 h5 h6]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, ?_, ?_, ?_, h4bp, ?_, ?_, f₄, sv₄⟩, h413, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rbx
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.r15
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rsp
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]; rfl
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.gpr, hI.r14, hI.r12, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)

/-- All the data is in, and the buffer is not empty. -/
def Full (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop := ∃ r, VG.Proof.Blake2.X86_64.Stream.Update.Inv P s₀ (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {s : State}
    (h : VG.Proof.Blake2.X86_64.Stream.Update.HeadPost P s₀ s) : WP isa (rest (w := w) callee) s (VG.Proof.Blake2.X86_64.Stream.Update.Full P s₀) := by
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  unfold rest
  refine WP.seq (WP.mono (test_ok .r12) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hI₁ := hI.congr g₁ m₁ rd₁ wr₁
  have hz : isa.eval .e s₁ = some (decide (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c = 0)) := by
    simp only [eval, z₁, hI.r12, BitVec.and_self, ofNat_beq_zero (show VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c < 2 ^ 64 by omega)]
  have hc := hI.c_le
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI₁, hr⟩
    · omega
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega
    refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.direct_ok hP hf hp hc' hI₁) fun s₂ hI₂ => ?_)
    have hdm := Nat.div_add_mod (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) (blockBytes w)
    have hmod := Nat.mod_lt (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ - c - 1) hpos
    exact WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.tail_ok hP hp (by omega) (by omega) hI₂) fun s₃ hI₃ => ⟨_, hI₃, by omega⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop :=
  VG.Proof.Blake2.X86_64.Stream.Update.Common w s₀ (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) s ∧
    ∀ h0 d, VG.Proof.Blake2.X86_64.Stream.Update.R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (VG.Proof.Blake2.X86_64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.X86_64.Stream.Update.D s₀ (VG.Proof.Blake2.X86_64.Stream.Update.len s₀))

theorem Full.done (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) {s₀ : State} {s : State} (h : VG.Proof.Blake2.X86_64.Stream.Update.Full P s₀ s) : VG.Proof.Blake2.X86_64.Stream.Update.Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) {s : State} (hI : VG.Proof.Blake2.X86_64.Stream.Update.Done P s₀ s) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ (VG.Proof.Blake2.updateX86_64 P).post s₀ s' := by
  have i : ∀ d : Nat, d + 8 ≤ 512 + 48 →
      InRegions (s.rd ++ s.wr) (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨VG.Proof.Blake2.X86_64.Stream.Update.scR s₀, by simp [hI.1.rd, hI.1.wr, hp.wr], contains_offset' (by omega) (by omega)⟩
  have i0 := i 512 (by omega); have i1 := i (512 + 8) (by omega); have i2 := i (512 + 16) (by omega)
  have i3 := i (512 + 24) (by omega); have i4 := i (512 + 32) (by omega); have i5 := i (512 + 40) (by omega)
  have sv := hI.1.saved
  have g0 : s.mem.readW (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 ((512 : Nat) : Int)) 64 = s₀.gpr .rbx :=
    sv (.rbx, 512) (by simp [Impl.MdStream.X86_64.saved, VG.Proof.Blake2.X86_64.Stream.Update.mdP])
  have g1 : s.mem.readW (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 ((512 + 8 : Nat) : Int)) 64 = s₀.gpr .rbp :=
    sv (.rbp, 512 + 8) (by simp [Impl.MdStream.X86_64.saved, VG.Proof.Blake2.X86_64.Stream.Update.mdP])
  have g2 : s.mem.readW (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 ((512 + 16 : Nat) : Int)) 64 = s₀.gpr .r12 :=
    sv (.r12, 512 + 16) (by simp [Impl.MdStream.X86_64.saved, VG.Proof.Blake2.X86_64.Stream.Update.mdP])
  have g3 : s.mem.readW (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 ((512 + 24 : Nat) : Int)) 64 = s₀.gpr .r13 :=
    sv (.r13, 512 + 24) (by simp [Impl.MdStream.X86_64.saved, VG.Proof.Blake2.X86_64.Stream.Update.mdP])
  have g4 : s.mem.readW (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 ((512 + 32 : Nat) : Int)) 64 = s₀.gpr .r14 :=
    sv (.r14, 512 + 32) (by simp [Impl.MdStream.X86_64.saved, VG.Proof.Blake2.X86_64.Stream.Update.mdP])
  have g5 : s.mem.readW (VG.Proof.Blake2.X86_64.Stream.Update.scr s₀ + BitVec.ofInt 64 ((512 + 40 : Nat) : Int)) 64 = s₀.gpr .r15 :=
    sv (.r15, 512 + 40) (by simp [Impl.MdStream.X86_64.saved, VG.Proof.Blake2.X86_64.Stream.Update.mdP])
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hI.1.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, VG.Proof.Blake2.X86_64.Stream.Update.ret_stk s₀⟩)
      (by decide)
  have hrsp := hI.1.rsp
  have hr15 := hI.1.r15
  have hrepr := hI.2
  apply WP.of_runBlock
  rw [VG.Proof.Blake2.X86_64.Stream.Update.restore_eq', MdStream.X86_64.restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, VG.Proof.MdStream.X86_64.ea_at, State.load64, VG.Proof.Blake2.X86_64.Stream.Update.mdP,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun h0 d hd hc hl => hrepr h0 d ⟨hd, hc, hl⟩⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]

theorem correct (hP : VG.Proof.Blake2.X86_64.Stream.Ok P) (hf : VG.Proof.Blake2.X86_64.Stream.CalleeOk P callee.code) {s₀ : State} (hp : VG.Proof.Blake2.X86_64.Stream.Update.Pre w s₀) :
    WP isa (update P callee) s₀ fun s' => gprPreserved s₀ s' ∧ (VG.Proof.Blake2.updateX86_64 P).post s₀ s' := by
  have hL := VG.Proof.Blake2.X86_64.Stream.Update.len_lt s₀
  unfold update
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.bufLen_ok hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (test_ok .r12) fun s₃ ⟨g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
  have hI₃ := hI.congr g₃ m₃ rd₃ wr₃
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.X86_64.Stream.Update.Done P s₀) ?_ fun s₄ h => VG.Proof.Blake2.X86_64.Stream.Update.epilogue_ok hp h)
  have hz : isa.eval .e s₃ = some (decide (VG.Proof.Blake2.X86_64.Stream.Update.len s₀ = 0)) := by
    simp only [eval, z₃, hI.r12, BitVec.and_self, Nat.sub_zero,
      ofNat_beq_zero (show VG.Proof.Blake2.X86_64.Stream.Update.len s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI₃.toCommon, fun h0 d hd => ?_⟩
    have := hI₃.repr h0 d hd
    have e0 : ∀ n, n = 0 → bytesAt s₀.mem (VG.Proof.Blake2.X86_64.Stream.Update.dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show VG.Proof.Blake2.X86_64.Stream.Update.D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show VG.Proof.Blake2.X86_64.Stream.Update.D s₀ (VG.Proof.Blake2.X86_64.Stream.Update.len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not] at hb
    have hr := bufLen_le (w := w) hP.pos (VG.Proof.Blake2.X86_64.Stream.Update.cnt s₀)
    exact WP.seq (WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.head_ok hP hf hp hr (by omega) hI₃) fun s₄ h =>
      WP.mono (VG.Proof.Blake2.X86_64.Stream.Update.rest_ok hP hf hp h) fun s₅ h => h.done hP)

end VG.Proof.Blake2.X86_64.Stream.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified`. -/
section

/-!
# Streaming BLAKE2 on x86-64: `Verified`

Correctness (from `Init`, `Update` and `Finalize`, with the compression
function of `Proof/Blake2/X86_64/Compress.lean`), constant time (from `CT`),
and a state satisfying each precondition, for BLAKE2b and BLAKE2s.
-/

namespace VG.Proof.Blake2.X86_64.Stream

open VG VG.X86_64 VG.Spec.Blake2

theorem calleeB : VG.Proof.Blake2.X86_64.Stream.CalleeOk b (Impl.Blake2.X86_64.compress b) :=
  CalleeOk.of_verified Proof.Blake2.X86_64.compressB_correct (by lit_decide) (by lit_decide)

theorem calleeS : VG.Proof.Blake2.X86_64.Stream.CalleeOk s (Impl.Blake2.X86_64.compress s) :=
  CalleeOk.of_verified Proof.Blake2.X86_64.compressS_correct (by lit_decide) (by lit_decide)

/-! ## States satisfying the preconditions -/

/-- `init` for BLAKE2b, with no key. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 192⟩]

/-- `update`, with no data, for `w`-bit words. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-! ## BLAKE2b -/

theorem initB_correct (st : State) (hs : (VG.Proof.Blake2.initX86_64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.init b) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.initX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Init.correct VG.Proof.Blake2.X86_64.Stream.okB hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem updateB_correct (st : State) (hs : (VG.Proof.Blake2.updateX86_64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.update b) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.updateX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Update.correct (callee := Impl.Blake2.X86_64.Stream.scalar b) VG.Proof.Blake2.X86_64.Stream.okB VG.Proof.Blake2.X86_64.Stream.calleeB (Update.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem finalizeB_correct (st : State) (hs : (VG.Proof.Blake2.finalizeX86_64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.finalize b) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.finalizeX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Finalize.correct (callee := Impl.Blake2.X86_64.Stream.scalar b) VG.Proof.Blake2.X86_64.Stream.okB VG.Proof.Blake2.X86_64.Stream.calleeB hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem initB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.init b) (Spec.Blake2.initBContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Blake2.X86_64.Stream.initB_correct VG.Proof.Blake2.X86_64.Stream.initB_ct (by
    contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes,
      X86_64.abi, X86_64.argRegs] [initSat] using VG.Proof.Blake2.X86_64.Stream.initSat)

theorem updateB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.update b)
      (Spec.Blake2.updateBScratchContract X86_64.abi 8) :=
  Verified.of_correct VG.Proof.Blake2.X86_64.Stream.updateB_correct VG.Proof.Blake2.X86_64.Stream.updateB_ct (by
    sig_implies [Spec.Blake2.updateBScratchContract, Spec.Blake2.updateBScratchSig, Proof.Blake2.updateX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi, X86_64.argRegs]
      [updateSat] using VG.Proof.Blake2.X86_64.Stream.updateSat 64)

theorem finalizeB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.finalize b)
      (Spec.Blake2.finalizeBScratchContract X86_64.abi 8) :=
  Verified.of_correct VG.Proof.Blake2.X86_64.Stream.finalizeB_correct VG.Proof.Blake2.X86_64.Stream.finalizeB_ct (by
    sig_implies [Spec.Blake2.finalizeBScratchContract, Spec.Blake2.finalizeBScratchSig,
      Proof.Blake2.finalizeX86_64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi,
      X86_64.argRegs]
      [finalizeSat] using VG.Proof.Blake2.X86_64.Stream.finalizeSat 64)

/-! ## BLAKE2s -/

/-- `init` for BLAKE2s, with no key. -/
def initSatS : State := { VG.Proof.Blake2.X86_64.Stream.initSat with
                                       wr := [⟨0x1000, 96⟩] }


theorem initS_correct (st : State) (hs : (VG.Proof.Blake2.initX86_64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.init s) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.initX86_64 s).post st s' := by
  obtain ⟨t, s', he, h⟩ := Init.correct VG.Proof.Blake2.X86_64.Stream.okS hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem initS_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.init s) (Spec.Blake2.initSContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Blake2.X86_64.Stream.initS_correct VG.Proof.Blake2.X86_64.Stream.initS_ct (by
    contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes,
      X86_64.abi, X86_64.argRegs] [initSatS] using VG.Proof.Blake2.X86_64.Stream.initSatS)

end VG.Proof.Blake2.X86_64.Stream

end
