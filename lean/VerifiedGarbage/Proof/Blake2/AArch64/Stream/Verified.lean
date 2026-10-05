import VerifiedGarbage.Proof.Blake2.AArch64.Compress
import VerifiedGarbage.Impl.Blake2.AArch64.Stream
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit`. -/
section

/-!
# Streaming BLAKE2 on AArch64: the code as literals

`init`, `update` and `finalize` of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), whose calls refer to the
literals of the compression functions (`Proof/Blake2/AArch64/Lit.lean`).
-/

namespace VG.Proof.Blake2.AArch64.Stream

materialize_code initB := Impl.Blake2.AArch64.Stream.init Spec.Blake2.b
materialize_code updateB := Impl.Blake2.AArch64.Stream.update Spec.Blake2.b
materialize_code finalizeB := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.b
materialize_code initS := Impl.Blake2.AArch64.Stream.init Spec.Blake2.s
materialize_code updateS := Impl.Blake2.AArch64.Stream.update Spec.Blake2.s
materialize_code finalizeS := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.s

end VG.Proof.Blake2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common`. -/
section

/-!
# Streaming BLAKE2 on AArch64: common lemmas

The contracts the proofs of `init`, `update` and `finalize` are written
against, what they need of the compression function they call (`CalleeOk`),
the call (`compressWith_ok`), and the loops copying bytes into the buffer and
zeroing it.
-/

namespace VG.Proof.Blake2

open VG.AArch64 VG.Spec.Blake2

section
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- AArch64 contract for `init(state = x0, outlen = x1, key = x2, keylen =
x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, VG.Proof.Blake2.bufOff w + blockBytes w⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧
    1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ P.maxBytes ∧ (s.gpr .x3).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .x1).toNat (s.gpr .x3).toNat) s'.mem
    (s.gpr .x0) (keyBlock w (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- AArch64 contract for `update(state = x0, count = x1, data = x2, len = x3,
scratch = x4)`. -/
def updateAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, VG.Proof.Blake2.bufOff w + blockBytes w⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 576⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .x0) d →
    s.gpr .x1 = BitVec.ofNat 64 d.length → d.length + (s.gpr .x3).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (s.gpr .x0) (d ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- AArch64 contract for `finalize(state = x0, count = x1, out = x2, scratch =
x3)`. -/
def finalizeAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, VG.Proof.Blake2.bufOff w + blockBytes w⟩
    let out : Region := ⟨s.gpr .x2, VG.Proof.Blake2.bufOff w⟩
    let scratch : Region := ⟨s.gpr .x3, 576⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .x0) d → d.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 d.length → bytesAt s'.mem (s.gpr .x2) (VG.Proof.Blake2.bufOff w) = finalHash P h0 d
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end

namespace AArch64.Stream

open VG.Impl.Blake2.AArch64.Stream (N B mov copyLoop zeroLoop compressWith saved save restore)
open VG.Impl.Blake2.AArch64 (lbb compress)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_addImm wp_subImm wp_movz wp_add wp_sub
  wp_and wp_lsr wp_ldrb wp_strb wp_str wp_ldr eval_zero eval_nonzero ofNat_succ ofNat_pred ofNat_beq_zero)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## Sizes -/

/-- The word sizes, and keys fitting a block. -/
structure Ok (P : VG.Spec.Blake2.Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : VG.Proof.Blake2.AArch64.Stream.Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N (h : VG.Proof.Blake2.AArch64.Stream.Ok P) : VG.Proof.Blake2.bufOff w = blockBytes w / 2 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : VG.Proof.Blake2.AArch64.Stream.Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

/-- The sizes, all small. -/
theorem Ok.len (h : VG.Proof.Blake2.AArch64.Stream.Ok P) : VG.Proof.Blake2.bufOff w + blockBytes w ≤ 192 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N64 (h : VG.Proof.Blake2.AArch64.Stream.Ok P) : VG.Proof.Blake2.bufOff w ≤ 64 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.lbb (h : VG.Proof.Blake2.AArch64.Stream.Ok P) : VG.Impl.Blake2.AArch64.lbb w < 64 ∧ 2 ^ VG.Impl.Blake2.AArch64.lbb w = blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : VG.Impl.Blake2.AArch64.Stream.N w = VG.Proof.Blake2.bufOff w := rfl
theorem B_eq : B w = blockBytes w := rfl

/-- `x >>> lbb`: division by the block size. -/
theorem shr_ofNat (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {m : Nat} (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> VG.Impl.Blake2.AArch64.lbb w = BitVec.ofNat 64 (m / blockBytes w) := by
  obtain ⟨-, lgB⟩ := hP.lbb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- `x & (B - 1)`: the remainder modulo the block size. -/
theorem mask_mod (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (x : BitVec 64) :
    x &&& (BitVec.ofNat 16 (B w - 1)).setWidth 64 = BitVec.ofNat 64 (x.toNat % blockBytes w) := by
  apply BitVec.eq_of_toNat_eq
  rcases hP.w with rfl | rfl
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat,
      show ((BitVec.ofNat 16 (B 64 - 1)).setWidth 64).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 64 = 2 ^ 7 from rfl]
    omega
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat,
      show ((BitVec.ofNat 16 (B 32 - 1)).setWidth 64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 32 = 2 ^ 6 from rfl]
    omega

theorem movz_B (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) : (BitVec.ofNat 16 (B w)).setWidth 64 = BitVec.ofNat 64 (blockBytes w) := by
  rcases hP.w with rfl | rfl <;> rfl

theorem movz_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) :=
  MdStream.AArch64.sub_ofNat h

/-! ## The compression function -/

/-- What the calls need of the compression function: its contract, and that it
pushes no frames. -/
structure CalleeOk (P : VG.Spec.Blake2.Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressAArch64 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressAArch64 P).post s s'
  noFrames : code.noFrames = true

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

/-- What the call of the compression function needs of the state `s` before
the argument set-up: the hash value `st` at `x19`, the scratch space `scr` at
`x20` and the `len` bytes of blocks at `src` do not overlap each other, and
may be accessed. -/
structure CallOk (s : State) (st scr src : Addr) (len : Nat) : Prop where
  x19 : s.gpr .x19 = st
  x20 : s.gpr .x20 = scr
  d₁ : Region.Disjoint ⟨st, VG.Proof.Blake2.bufOff w⟩ ⟨scr, 512⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, VG.Proof.Blake2.bufOff w⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, 512⟩
  hc : Covers [⟨src, len⟩, ⟨st, VG.Proof.Blake2.bufOff w⟩, ⟨scr, 512⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, VG.Proof.Blake2.bufOff w⟩, ⟨scr, 512⟩] s.wr

/-- The arguments of the call, set up from `σ`. -/
structure Setup (σ s : State) (src n t : BitVec 64) (last : Bool) : Prop where
  x0 : s.gpr .x0 = σ.gpr .x19
  x1 : s.gpr .x1 = src
  x2 : s.gpr .x2 = n
  x3 : s.gpr .x3 = t
  x4 : ((s.gpr .x4).setWidth 32 != 0) = last
  x5 : s.gpr .x5 = σ.gpr .x20
  cs : ∀ r ∈ preserved, s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- Compressing the `n` blocks at `src` into the hash value at `x19`, with
scratch space at `x20`, by calling the compression function, after `args`
set up its arguments. -/
theorem compressWith_ok {args : List Instr} (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s : State}
    {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (hs : WP isa (.block (([mov .x0 .x19] : List Instr) ++ args ++ ([mov .x5 .x20] : List Instr))) s
      fun s' => VG.Proof.Blake2.AArch64.Stream.Setup s s' src n t last)
    (h : VG.Proof.Blake2.AArch64.Stream.CallOk (w := w) s st scr src (blockBytes w * n.toNat))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨st, VG.Proof.Blake2.bufOff w⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt w s'.mem st = compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last →
      Q s') :
    WP isa (compressWith P args) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono hs fun s₁ hs => ?_)
  have e0 : s₁.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
  have e1 : s₁.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans hs.x1
  have e2 : s₁.callEntry.gpr .x2 = n := (State.callEntry_gpr _ (by decide)).trans hs.x2
  have e3 : s₁.callEntry.gpr .x3 = t := (State.callEntry_gpr _ (by decide)).trans hs.x3
  have e4 : s₁.callEntry.gpr .x4 = s₁.gpr .x4 := State.callEntry_gpr _ (by decide)
  have e5 : s₁.callEntry.gpr .x5 = scr := (State.callEntry_gpr _ (by decide)).trans (hs.x5.trans h.x20)
  refine WP.call (k := compressAArch64 P) hf.verified
    (rd := [⟨src, blockBytes w * n.toNat⟩]) (wr := [⟨st, VG.Proof.Blake2.bufOff w⟩, ⟨scr, 512⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [compressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, e0, e1, e2, e5]
    exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw
  · intro s' hrd hwr hsp hfr hcs _ hpost
    simp only [compressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, e0, e1, e2, e3, e4, hs.x4, hs.mem] at hpost
    exact hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (hsp.trans hs.sp)
      (fun r hr h30 => (hcs r hr h30).trans (hs.cs r hr)) (hs.mem ▸ hfr) hpost

/-! ## Copying bytes into the buffer -/

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (dst src : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  x21 : s.gpr .x21 = src + BitVec.ofNat 64 j
  x23 : s.gpr .x23 = BitVec.ofNat 64 (r + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

theorem nonzero_iff (s : State) {k : Nat} (h : s.gpr .x11 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    isa.eval (.nonzero .x .x11) s = some (decide (k ≠ 0)) := by
  show VG.AArch64.eval (.nonzero .x .x11) s = _
  rw [eval_nonzero, h, bne, ofNat_beq_zero hk]
  simp

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The loop copying `k ≥ 1` bytes from `src` (at `x21`) to the buffer, from
byte `r` on (in `x23`). -/
theorem copyLoop_ok {s₀ : State} {st src : Addr} {r k : Nat} (hN : VG.Proof.Blake2.bufOff w ≤ 64) (hk : 1 ≤ k)
    (hk' : r + k < 2 ^ 32)
    (hx19 : s₀.gpr .x19 = st) (hx21 : s₀.gpr .x21 = src) (hx23 : s₀.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s₀.gpr .x11 = BitVec.ofNat 64 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, k⟩ ⟨st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, VG.Proof.Blake2.AArch64.Stream.CopyI s₀ (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r)) src r k k s → Q s) :
    WP isa (copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.AArch64.Stream.CopyI s₀ (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hx21],
      by rw [hx23, Nat.add_zero], by rw [hx11, Nat.sub_zero], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (VG.WriteBytes.writeBytes_frame s₀.mem _ _ (VG.Proof.Blake2.AArch64.Stream.contains_prefix (k := k) _ (by simp; omega))).bytes (R := ⟨src, k⟩)
      (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  -- The byte written.
  have hout : InRegions s.wr (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hx19' : s.gpr .x19 = st := by
    rw [h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide), hx19]
  refine wp_ldrb (a := src + BitVec.ofNat 64 j) (by decide) (by rw [h.x21]; simp) hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_strb (a := st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [VG.Proof.Blake2.AArch64.Stream.N_eq]; omega) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hx19', h.x23, VG.Proof.Blake2.AArch64.Stream.N_eq]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
    wp_subImm (by decide) fun s₆ u₆ => WP.block_nil ?_
  have hx11' : s₆.gpr .x11 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x11, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.AArch64.Stream.CopyI s₀ (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r)) src r k (j + 1) s₆ := by
    refine ⟨by omega, ?_, ?_, hx11', fun x h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₆.other x h5, u₅.other x h4, u₄.other x h3, g₃.gpr, u₂.other x h2, u₁.other x h1,
        h.other x h1 h2 h3 h4 h5]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₀.mem src k).length := by simp [bytesAt]; omega
      have hl : (List.take j (bytesAt s₀.mem src k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, VG.Proof.Blake2.AArch64.Stream.setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [VG.Proof.Blake2.AArch64.Stream.nonzero_iff s₆ hx11' (by omega)]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [VG.Proof.Blake2.AArch64.Stream.nonzero_iff s₆ hx11' (by omega)]; simp; omega,
      k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Zeroing the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (r + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .x12 → x ≠ .x23 → x ≠ .x11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer, from byte `r` on (in `x23`). -/
theorem zeroLoop_ok {s₀ : State} {st : Addr} {r k : Nat} (hN : VG.Proof.Blake2.bufOff w ≤ 64) (hk : 1 ≤ k)
    (hk' : r + k < 2 ^ 32)
    (hx19 : s₀.gpr .x19 = st) (hx23 : s₀.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s₀.gpr .x11 = BitVec.ofNat 64 k) (hx9 : s₀.gpr .x9 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, VG.Proof.Blake2.AArch64.Stream.ZI s₀ (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r)) r k k s → Q s) :
    WP isa (zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.AArch64.Stream.ZI s₀ (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by rw [hx23, Nat.add_zero], by rw [hx11, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hx19' : s.gpr .x19 = st := by rw [h.other .x19 (by decide) (by decide) (by decide), hx19]
  refine wp_add fun s₁ u₁ => wp_strb (a := st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [VG.Proof.Blake2.AArch64.Stream.N_eq]; omega) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19', h.x23, VG.Proof.Blake2.AArch64.Stream.N_eq]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addImm (by decide) fun s₃ u₃ => wp_subImm (by decide) fun s₄ u₄ => WP.block_nil ?_
  have hx11' : s₄.gpr .x11 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x11, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega),
      Nat.sub_sub]
  have hI : VG.Proof.Blake2.AArch64.Stream.ZI s₀ (st + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hx11', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add,
        Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .x9 (by decide) (by decide) (by decide), hx9, h.mem,
        List.replicate_succ', VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [VG.Proof.Blake2.AArch64.Stream.nonzero_iff s₄ hx11' (by omega)]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [VG.Proof.Blake2.AArch64.Stream.nonzero_iff s₄ hx11' (by omega)]; simp; omega,
      k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Saving and restoring the caller's registers -/

/-- The caller's callee-saved registers `g` are saved in the scratch space at `b`. -/
abbrev Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved b g saved m

/-- The memory after saving `x19`–`x24` (values `g`) at `b + 512 …`. -/
abbrev saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem := Spill.saveMem m b g saved

theorem saved_off : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) : VG.Proof.Blake2.AArch64.Stream.Saved b g (VG.Proof.Blake2.AArch64.Stream.saveMem m b g) :=
  Spill.saveMem_saved (by decide) m b g

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 512, 48⟩] m (VG.Proof.Blake2.AArch64.Stream.saveMem m b g) :=
  Spill.saveMem_frame (by decide) (by decide) m b g

/-- Saving `x19`–`x24` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.Proof.Blake2.AArch64.Stream.saveMem s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q :=
  Spill.save_ok (l := saved) (by decide) (fun p hp => hin _ (by revert p; decide) (by revert p; decide))
    (k _ rfl rfl rfl rfl rfl)

/-- `restore`, `x20` (the base) last. -/
abbrev restored : List (Reg × Nat) :=
  [(.x19, 512), (.x21, 528), (.x22, 536), (.x23, 544), (.x24, 552), (.x20, 520)]

/-- Restoring `x19`–`x24` from the save area at `scr`. -/
theorem restore_ok {s : State} {scr : Addr} (h20 : s.gpr .x20 = scr)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : VG.Proof.Blake2.AArch64.Stream.Saved scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q :=
  WP.mono (Spill.restore_wp (l := VG.Proof.Blake2.AArch64.Stream.restored) h20 (by decide) (by decide)
    (fun p hp => hin _ (by revert p; decide) (by revert p; decide)) (hsv.sub (by decide)))
    fun s' h => have h := h.perm (l' := saved) (by decide) (by decide)
      k s' h.gpr h.other h.mem h.rd h.wr h.sp

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
abbrev untouched : List Reg := [.x25, .x26, .x27, .x28]

theorem notU {r : Reg} (hr : r ∈ VG.Proof.Blake2.AArch64.Stream.untouched) (x : Reg) (hx : x ∉ VG.Proof.Blake2.AArch64.Stream.untouched := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

/-- The callee-saved registers but `x30` are the caller's again once `restore`
has run and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r := by
  intro r hr h30
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.x19, 512) (by simp [saved])
  · exact hsv (.x20, 520) (by simp [saved])
  · exact hsv (.x21, 528) (by simp [saved])
  · exact hsv (.x22, 536) (by simp [saved])
  · exact hsv (.x23, 544) (by simp [saved])
  · exact hsv (.x24, 552) (by simp [saved])
  all_goals first | exact absurd rfl h30 | exact hu _ (by simp [VG.Proof.Blake2.AArch64.Stream.untouched])

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  MdStream.AArch64.write_frame_bytes hd hR hi

/-! ## Branches, the number of buffered bytes, and the buffer's arguments -/

theorem zero_iff (s : State) {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (k = 0)) := by
  show VG.AArch64.eval (.zero .x r) s = _
  rw [eval_zero, h, ofNat_beq_zero hk]

theorem bufLen_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s : State} :
    WP isa (Impl.Blake2.AArch64.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 (Blake2.bufLen w (s.gpr .x24).toNat) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold Impl.Blake2.AArch64.Stream.bufLen
  have hn := (s.gpr .x24).isLt
  generalize hn' : (s.gpr .x24).toNat = n at hn
  have hx24 : s.gpr .x24 = BitVec.ofNat 64 n := by rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_and fun s₃ u₃ =>
    wp_addImm (by decide) fun s₄ u₄ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .x9 → r ≠ .x23 → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₄.other r h2, u₃.other r h2, u₂.other r h1, u₁.other r h2]
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hsp : s₄.sp = s.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (decide (n = 0)) (VG.Proof.Blake2.AArch64.Stream.zero_iff s₄ (by rw [g _ (by decide) (by decide), hx24]) hn)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movz fun s₅ u₅ => WP.block_nil ⟨?_, fun r h1 h2 => by rw [u₅.other r h2, g r h1 h2],
      by rw [u₅.mem, hm], by rw [u₅.rd, hrd], by rw [u₅.wr, hwr], by rw [u₅.sp, hsp]⟩
    rw [u₅.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr, hsp⟩
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hx24, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega), VG.Proof.Blake2.AArch64.Stream.mask_mod hP,
      toNat_ofNat_lt (by omega), ← BitVec.ofNat_add]
    simp only [Blake2.bufLen, hb, ↓reduceIte]

/-- The arguments for compressing the buffer, with the byte count in `x24` as
the counter and the final block flag `imm`. -/
theorem bufArgs_ok {σ : State} {imm : BitVec 16} (hN : VG.Proof.Blake2.bufOff w < 4096) :
    WP isa (.block (([mov .x0 .x19] : List Instr) ++ ([.addImm .x .x1 .x19 (VG.Impl.Blake2.AArch64.Stream.N w), .movz .x .x2 1 0,
      mov .x3 .x24, .movz .x .x4 imm 0] : List Instr) ++ ([mov .x5 .x20] : List Instr))) σ
      fun s => VG.Proof.Blake2.AArch64.Stream.Setup σ s (σ.gpr .x19 + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) (BitVec.setWidth 64 (1 : BitVec 16))
        (σ.gpr .x24) ((imm.setWidth 64).setWidth 32 != 0) := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addImm hN fun s₂ u₂ => wp_movz fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hcs : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), VG.Proof.Blake2.AArch64.Stream.N_eq]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < VG.Proof.Blake2.bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  have hN := hP.len
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

end AArch64.Stream

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.AArch64.Stream.CT`. -/
section

/-!
# Streaming BLAKE2 on AArch64: constant time

The taint analysis of `init`, `update` and `finalize` (the compression
function they call included), from the public arguments: the pointers,
`outlen`, `keylen`, `count` and `len`, and the stack pointer.
-/

namespace VG.Proof.Blake2.AArch64.Stream

open VG VG.AArch64 VG.Spec.Blake2

theorem init_agree {w : Nat} {P : VG.Spec.Blake2.Params w} {s₁ s₂ : State} (hpub : (VG.Proof.Blake2.initAArch64 P).pub s₁ s₂) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem update_agree {w : Nat} {P : VG.Spec.Blake2.Params w} {s₁ s₂ : State} (hpub : (VG.Proof.Blake2.updateAArch64 P).pub s₁ s₂) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem finalize_agree {w : Nat} {P : VG.Spec.Blake2.Params w} {s₁ s₂ : State}
    (hpub : (VG.Proof.Blake2.finalizeAArch64 P).pub s₁ s₂) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem okB : VG.Proof.Blake2.AArch64.Stream.Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩
theorem okS : VG.Proof.Blake2.AArch64.Stream.Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem initB_ct : ConstantTime isa (VG.Proof.Blake2.initAArch64 b).pre (VG.Proof.Blake2.initAArch64 b).pub
    (Impl.Blake2.AArch64.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => VG.Proof.Blake2.AArch64.Stream.init_agree hp) (by taint_decide)

theorem initS_ct : ConstantTime isa (VG.Proof.Blake2.initAArch64 s).pre (VG.Proof.Blake2.initAArch64 s).pub
    (Impl.Blake2.AArch64.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => VG.Proof.Blake2.AArch64.Stream.init_agree hp) (by taint_decide)

theorem updateB_ct : ConstantTime isa (VG.Proof.Blake2.updateAArch64 b).pre (VG.Proof.Blake2.updateAArch64 b).pub
    (Impl.Blake2.AArch64.Stream.update b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => VG.Proof.Blake2.AArch64.Stream.update_agree hp) (by taint_decide)

theorem updateS_ct : ConstantTime isa (VG.Proof.Blake2.updateAArch64 s).pre (VG.Proof.Blake2.updateAArch64 s).pub
    (Impl.Blake2.AArch64.Stream.update s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => VG.Proof.Blake2.AArch64.Stream.update_agree hp) (by taint_decide)

theorem finalizeB_ct : ConstantTime isa (VG.Proof.Blake2.finalizeAArch64 b).pre (VG.Proof.Blake2.finalizeAArch64 b).pub
    (Impl.Blake2.AArch64.Stream.finalize b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => VG.Proof.Blake2.AArch64.Stream.finalize_agree hp) (by taint_decide)

theorem finalizeS_ct : ConstantTime isa (VG.Proof.Blake2.finalizeAArch64 s).pre (VG.Proof.Blake2.finalizeAArch64 s).pub
    (Impl.Blake2.AArch64.Stream.finalize s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => VG.Proof.Blake2.AArch64.Stream.finalize_agree hp) (by taint_decide)

end VG.Proof.Blake2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.AArch64.Stream.Init`. -/
section

/-!
# Streaming BLAKE2 on AArch64: `init`

`initState` stores the initial hash value (`initState_ok`); for a key,
`keyBlock` zeroes the buffer (`zero_ok`) and copies the key into it
(`keyLoop_ok`). `init` is a leaf function writing only `x2`, `x3` and
`x9`–`x12`.
-/

namespace VG.Proof.Blake2.AArch64.Stream.Init

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B initState)
open VG.Impl.Blake2.AArch64 (sz ws movImm64)
open VG.Proof.Blake2 (initAArch64 bufOff repr_keyBlock stateAt_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd WP.cons toNat_ofNat_lt wp_movz wp_addImm wp_subImm wp_ldrb wp_strb
  wp_str wp_str32 ofNat_succ)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  write_eq_writeBytes)

/-! ## Instructions at the word size -/

section
variable {w : Nat} {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movImm64 {d : Reg} {v : BitVec 64} {rest : List Instr}
    (k : ∀ s', Upd s s' d v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm64 d v ++ rest)) s Q := by
  simp only [movImm64, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩))))
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, h]

theorem wp_strw (hw : w = 64 ∨ w = 32) {t n : Reg} {off : Nat} {a : Addr}
    (ho : off % (w / 8) = 0 ∧ off < 4096 * (w / 8))
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a (w / 8))
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth w)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str (sz w) t n off :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact wp_str ho ha hout fun s' h => k s' (by rwa [BitVec.setWidth_eq])
  · exact wp_str32 ho ha hout k

theorem wp_lslw (hw : w = 64 ∨ w = 32) {d n : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth w <<< 8).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl (sz w) d n 8 :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.write s .x d _))
  · exact WP.cons rfl (k _ (Upd.write s .w d _))

theorem wp_eorw (hw : w = 64 ∨ w = 32) {d n m : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth w ^^^ (s.gpr m).setWidth w).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor (sz w) d n m :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.write s .x d _))
  · exact WP.cons rfl (k _ (Upd.write s .w d _))

end

/-! ## Sizes -/

section
variable {w : Nat} (hw : w = 64 ∨ w = 32)
include hw

theorem w_le : w ≤ 64 := by omega

theorem word_in {j : Nat} (hj : j < 8) : w / 8 * j + w / 8 ≤ VG.Proof.Blake2.bufOff w := by
  rcases hw with rfl | rfl <;> simp only [VG.Proof.Blake2.bufOff] <;> omega

theorem word_sep {j k : Nat} (h : j ≠ k) :
    w / 8 * j + w / 8 ≤ w / 8 * k ∨ w / 8 * k + w / 8 ≤ w / 8 * j := by
  rcases hw with rfl | rfl <;> omega

theorem sizes : VG.Proof.Blake2.bufOff w + blockBytes w < 2 ^ 32 ∧ 16 ≤ blockBytes w ∧ blockBytes w % 8 = 0 ∧
    blockBytes w < 2 ^ (w - 8) ∧ w / 8 < 2 ^ 64 ∧ VG.Proof.Blake2.bufOff w ≤ 64 ∧ 0 < w / 8 ∧ w / 8 ≤ 8 := by
  rcases hw with rfl | rfl <;> decide

theorem readW_writeW_self_w (m : Mem) (a : Addr) (v : BitVec w) : (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

theorem setWidth_back (x : BitVec w) : (x.setWidth 64).setWidth w = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (w_le hw), BitVec.setWidth_eq]

end

/-! ## The initial hash value -/

section
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec w := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  movImm64 .x9 ((VG.Proof.Blake2.AArch64.Stream.Init.ivAt P (k + 1)).setWidth 64) ++ [.str (sz w) .x9 .x0 (ws w * (k + 1))]

theorem initState_eq : initState P = (List.range 7).flatMap (VG.Proof.Blake2.AArch64.Stream.Init.ivStep P) ++
    (movImm64 .x9 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
    ([.lsl (sz w) .x10 .x3 8, .logic .eor (sz w) .x9 .x9 .x10, .logic .eor (sz w) .x9 .x9 .x1,
      .str (sz w) .x9 .x0 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .x0, VG.Proof.Blake2.bufOff w⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (j + 1))) w = VG.Proof.Blake2.AArch64.Stream.Init.ivAt P (j + 1)

variable {P}

theorem iv_step (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .x0, VG.Proof.Blake2.bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : VG.Proof.Blake2.AArch64.Stream.Init.IvInv P s₀ k s) :
    WP isa (.block (VG.Proof.Blake2.AArch64.Stream.Init.ivStep P k)) s (VG.Proof.Blake2.AArch64.Stream.Init.IvInv P s₀ (k + 1)) := by
  have hs := VG.Proof.Blake2.AArch64.Stream.Init.sizes hw
  have hin : (⟨s₀.gpr .x0, VG.Proof.Blake2.bufOff w⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (k + 1))) (w / 8) :=
    Offset.contains_base _ (VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (by omega)) (by have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := k + 1) (by omega); omega)
  refine VG.Proof.Blake2.AArch64.Stream.Init.wp_movImm64 fun s₁ u₁ => VG.Proof.Blake2.AArch64.Stream.Init.wp_strw hw (a := s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (k + 1)))
    ⟨Nat.mul_mod_right _ _, by unfold ws; have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := k + 1) (by omega); omega⟩ ?_ ?_
    fun s₂ g₂ => WP.block_nil ?_
  · rw [u₁.other _ (by decide), h.gpr _ (by decide)]; rfl
  · rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have hv : (s₁.gpr .x9).setWidth w = VG.Proof.Blake2.AArch64.Stream.Init.ivAt P (k + 1) := by rw [u₁.gpr, VG.Proof.Blake2.AArch64.Stream.Init.setWidth_back hw]
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, hv, u₁.mem]
    by_cases e : j = k
    · subst e; exact VG.Proof.Blake2.AArch64.Stream.Init.readW_writeW_self_w hw _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (VG.Proof.Blake2.AArch64.Stream.Init.word_sep hw (fun h => e (by omega)))
        (by have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := j + 1) (by omega); omega)
        (by have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := k + 1) (by omega); omega)) hs.2.2.2.2.1]
      exact h.words j (by omega)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .x0, VG.Proof.Blake2.bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (s₀.gpr .x0) = Spec.Blake2.init P (s₀.gpr .x1).toNat (s₀.gpr .x3).toNat

theorem initState_ok (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .x0, VG.Proof.Blake2.bufOff w⟩] a n → InRegions s₀.wr a n) :
    WP isa (.block (initState P)) s₀ (VG.Proof.Blake2.AArch64.Stream.Init.StateOk (P := P) s₀) := by
  have hs := VG.Proof.Blake2.AArch64.Stream.Init.sizes hw
  have hle := w_le hw
  rw [VG.Proof.Blake2.AArch64.Stream.Init.initState_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Blake2.AArch64.Stream.Init.IvInv P s₀) (VG.Proof.Blake2.AArch64.Stream.Init.iv_step hw hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .x0, VG.Proof.Blake2.bufOff w⟩ : Region).Contains (s₀.gpr .x0 + BitVec.ofNat 64 0) (w / 8) :=
    Offset.contains_base _ (by have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := 0) (by omega); omega) (by omega)
  refine VG.Proof.Blake2.AArch64.Stream.Init.wp_movImm64 fun s₁ u₁ => VG.Proof.Blake2.AArch64.Stream.Init.wp_lslw hw fun s₂ u₂ => VG.Proof.Blake2.AArch64.Stream.Init.wp_eorw hw fun s₃ u₃ => VG.Proof.Blake2.AArch64.Stream.Init.wp_eorw hw fun s₄ u₄ =>
    VG.Proof.Blake2.AArch64.Stream.Init.wp_strw hw (a := s₀.gpr .x0 + BitVec.ofNat 64 0) ⟨Nat.zero_mod _, by omega⟩ ?_ ?_
    fun s₅ g₅ => WP.block_nil ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h₇.gpr _ (by decide)]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → s₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₅.gpr, u₄.other r h1, u₃.other r h1, u₂.other r h2, u₁.other r h1, h₇.gpr r h1]
  -- The word stored.
  have hv : (s₄.gpr .x9).setWidth w = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat w (s₀.gpr .x3).toNat <<< 8) ^^^ BitVec.ofNat w (s₀.gpr .x1).toNat := by
    rw [u₄.gpr, VG.Proof.Blake2.AArch64.Stream.Init.setWidth_back hw, u₃.other .x1 (by decide),
      u₃.gpr, VG.Proof.Blake2.AArch64.Stream.Init.setWidth_back hw, u₂.other .x9 (by decide), u₂.gpr, VG.Proof.Blake2.AArch64.Stream.Init.setWidth_back hw, u₁.gpr,
      VG.Proof.Blake2.AArch64.Stream.Init.setWidth_back hw, u₂.other .x1 (by decide), u₁.other .x1 (by decide), u₁.other .x3 (by decide),
      h₇.gpr .x1 (by decide), h₇.gpr .x3 (by decide), BitVec.ofNat_toNat, BitVec.ofNat_toNat]
    rfl
  have hm : s₅.mem = s₇.mem.writeW (s₀.gpr .x0 + BitVec.ofNat 64 0) ((s₄.gpr .x9).setWidth w) := by
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd],
    by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr], by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp],
    ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, VG.Proof.Blake2.AArch64.Stream.Init.readW_writeW_self_w hw, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsep : Mem.Sep (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (j + 1))) (w / 8)
          (s₀.gpr .x0 + BitVec.ofNat 64 0) (w / 8) :=
        Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega))
          (by have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := j + 1) hj; omega) (by have := VG.Proof.Blake2.AArch64.Stream.Init.word_in hw (j := 0) (by omega); omega)
      rw [Mem.readW_writeW_sep hsep hs.2.2.2.2.1, h₇.words j (by omega)]
      simp only [VG.Proof.Blake2.AArch64.Stream.Init.ivAt, hj, ↓reduceDIte]

end

/-! ## The key block -/

section
variable {w : Nat}

theorem writeW_zero (m : Mem) (a : Addr) :
    m.writeW a (0 : BitVec 64) = VG.WriteBytes.writeBytes m a (List.replicate 8 0) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl

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
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Blake2.AArch64.Stream.Init.writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · simp only [hi, ↓reduceIte]
    rw [hz i h1, List.getElem_append_right (by omega), List.getElem_replicate]

/-- After zeroing `8 · j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  mem : s.mem = VG.WriteBytes.writeBytes σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) (List.replicate (8 * j) 0)

theorem zero_ok (hw : w = 64 ∨ w = 32) {σ : State} (hx9 : σ.gpr .x9 = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .x0, VG.Proof.Blake2.bufOff w + blockBytes w⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (B w / 8)).flatMap fun j => [.str .x .x9 .x0 (VG.Impl.Blake2.AArch64.Stream.N w + 8 * j)])) σ
      (VG.Proof.Blake2.AArch64.Stream.Init.ZInv (w := w) σ (blockBytes w / 8)) := by
  have hs := VG.Proof.Blake2.AArch64.Stream.Init.sizes hw
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.AArch64.Stream.Init.ZInv (w := w) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Blake2.AArch64.Stream.B_eq] at hj
  refine wp_str (a := σ.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + 8 * j)) ⟨?_, ?_⟩ (by rw [h.gpr, VG.Proof.Blake2.AArch64.Stream.N_eq])
    ?_ fun s' g' => WP.block_nil ⟨g'.gpr.trans h.gpr, g'.rd.trans h.rd, g'.wr.trans h.wr, g'.sp.trans h.sp, ?_⟩
  · rw [VG.Proof.Blake2.AArch64.Stream.N_eq]; rcases hw with rfl | rfl <;> simp only [VG.Proof.Blake2.bufOff] <;> omega
  · rw [VG.Proof.Blake2.AArch64.Stream.N_eq]; rcases hw with rfl | rfl <;> simp only [VG.Proof.Blake2.bufOff, blockBytes] at hj ⊢ <;> omega
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · have e := VG.WriteBytes.writeBytes_append σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w))
      (List.replicate (8 * j) 0) (List.replicate 8 0) (by simp; omega)
    rw [List.length_replicate] at e
    rw [g'.mem, h.mem, h.gpr, hx9, VG.Proof.Blake2.AArch64.Stream.Init.writeW_zero, ← Offset.add_ofNat_add_ofNat, e,
      List.replicate_append_replicate, Nat.mul_succ]

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev kp : Addr := s₀.gpr .x2
abbrev kk : Nat := (s₀.gpr .x3).toNat
abbrev buf (w : Nat) : Addr := VG.Proof.Blake2.AArch64.Stream.Init.st s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Init.st s₀, VG.Proof.Blake2.bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Init.kp s₀, VG.Proof.Blake2.AArch64.Stream.Init.kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Init.kp s₀) (VG.Proof.Blake2.AArch64.Stream.Init.kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ VG.Proof.Blake2.AArch64.Stream.Init.kk s₀
  x2 : s.gpr .x2 = VG.Proof.Blake2.AArch64.Stream.Init.kp s₀ + BitVec.ofNat 64 j
  x12 : s.gpr .x12 = VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w + BitVec.ofNat 64 j
  x3 : s.gpr .x3 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ - j)
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes Z (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) ((VG.Proof.Blake2.AArch64.Stream.Init.key s₀).take j)

theorem keyLoop_ok (hw : w = 64 ∨ w = 32) {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [VG.Proof.Blake2.AArch64.Stream.Init.kR s₀]) (hwr : s₀.wr = [VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w]) (hd : (VG.Proof.Blake2.AArch64.Stream.Init.kR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w))
    (hk : 1 ≤ VG.Proof.Blake2.AArch64.Stream.Init.kk s₀) (hkb : VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ ≤ blockBytes w) (hZ : Frame [VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w] s₀.mem Z)
    (hσ : VG.Proof.Blake2.AArch64.Stream.Init.KInv (w := w) s₀ Z 0 σ) :
    WP isa (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1,
        .addImm .x .x12 .x12 1, .subImm .x .x3 .x3 1]) (.nonzero .x .x3)) σ
      (VG.Proof.Blake2.AArch64.Stream.Init.KInv (w := w) s₀ Z (VG.Proof.Blake2.AArch64.Stream.Init.kk s₀)) := by
  have hs := VG.Proof.Blake2.AArch64.Stream.Init.sizes hw
  have hkl : VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ - j ∧ j < VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ ∧ VG.Proof.Blake2.AArch64.Stream.Init.KInv (w := w) s₀ Z j s)
    ?_ (VG.Proof.Blake2.AArch64.Stream.Init.kk s₀) σ ⟨0, by omega, by omega, hσ⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The key byte read is unchanged.
  have hbyte : s.mem (VG.Proof.Blake2.AArch64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) = s₀.mem (VG.Proof.Blake2.AArch64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hf : Frame [VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w] s₀.mem (VG.WriteBytes.writeBytes Z (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) ((VG.Proof.Blake2.AArch64.Stream.Init.key s₀).take j)) :=
      hZ.trans (VG.WriteBytes.writeBytes_frame Z _ _ (Offset.contains_base _ (by simp; omega) (by omega)))
    exact hf.bytes (R := VG.Proof.Blake2.AArch64.Stream.Init.kR s₀) (by simpa using hd) (by simp; omega) hj
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.Blake2.AArch64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hrd]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hout : InRegions s.wr (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w + BitVec.ofNat 64 j) 1 := by
    rw [h.wr, hwr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ldrb (a := VG.Proof.Blake2.AArch64.Stream.Init.kp s₀ + BitVec.ofNat 64 j) (by decide) (by rw [h.x2]; simp) hin fun s₁ u₁ => ?_
  refine wp_strb (a := VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide), h.x12]; simp)
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hx3 : s₅.gpr .x3 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x3,
      VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.AArch64.Stream.Init.KInv (w := w) s₀ Z (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hx3, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x2,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x12,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other r h4, u₄.other r h5, u₃.other r h3, g₂.gpr, u₁.other r h1, h.other r h1 h2 h3 h4 h5]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (VG.Proof.Blake2.AArch64.Stream.Init.key s₀).length := by simp [bytesAt]; omega
      have hl : (List.take j (VG.Proof.Blake2.AArch64.Stream.Init.key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, VG.Proof.Blake2.AArch64.Stream.setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = VG.Proof.Blake2.AArch64.Stream.Init.kk s₀
  · refine .inl ⟨?_, hjk ▸ hI⟩
    show VG.AArch64.eval (.nonzero .x .x3) s₅ = _
    rw [MdStream.AArch64.eval_nonzero, hx3, bne, MdStream.AArch64.ofNat_beq_zero (by omega)]
    simp; omega
  · refine .inr ⟨?_, VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    show VG.AArch64.eval (.nonzero .x .x3) s₅ = _
    rw [MdStream.AArch64.eval_nonzero, hx3, bne, MdStream.AArch64.ofNat_beq_zero (by omega)]
    simp; omega

end

section
variable {w : Nat} {P : VG.Spec.Blake2.Params w}

theorem keyBlock_eq : Impl.Blake2.AArch64.Stream.keyBlock (w := w) =
    .seq (.block ((.movz .x .x9 0 0 :: (List.range (B w / 8)).flatMap fun j =>
        ([.str .x .x9 .x0 (VG.Impl.Blake2.AArch64.Stream.N w + 8 * j)] : List Instr)) ++ ([.addImm .x .x12 .x0 (VG.Impl.Blake2.AArch64.Stream.N w)] : List Instr)))
      (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1, .addImm .x .x12 .x12 1,
        .subImm .x .x3 .x3 1]) (.nonzero .x .x3)) := by
  rw [Impl.Blake2.AArch64.Stream.keyBlock, List.map_eq_flatMap]

theorem keyBlock_ok (hw : w = 64 ∨ w = 32) {s₀ σ : State}
    (hrd : s₀.rd = [VG.Proof.Blake2.AArch64.Stream.Init.kR s₀]) (hwr : s₀.wr = [VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w]) (hd : (VG.Proof.Blake2.AArch64.Stream.Init.kR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w))
    (hk : 1 ≤ VG.Proof.Blake2.AArch64.Stream.Init.kk s₀) (hkb : VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ ≤ blockBytes w) (hσ : VG.Proof.Blake2.AArch64.Stream.Init.StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.AArch64.Stream.keyBlock (w := w)) σ fun s =>
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → s.gpr r = s₀.gpr r) ∧
      s.sp = s₀.sp ∧ Frame [⟨VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w, blockBytes w⟩] σ.mem s.mem ∧
      bytesAt s.mem (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) (blockBytes w) = VG.Proof.Blake2.AArch64.Stream.Init.key s₀ ++ List.replicate (blockBytes w - VG.Proof.Blake2.AArch64.Stream.Init.kk s₀) 0 := by
  have hs := VG.Proof.Blake2.AArch64.Stream.Init.sizes hw
  have hxs : (VG.Proof.Blake2.AArch64.Stream.Init.key s₀).length = VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes w → (VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w).Contains (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) n := fun n hn =>
    Offset.contains_base _ (by omega) (by omega)
  have hσ0 : σ.gpr .x0 = VG.Proof.Blake2.AArch64.Stream.Init.st s₀ := hσ.gpr _ (by decide) (by decide)
  rw [VG.Proof.Blake2.AArch64.Stream.Init.keyBlock_eq]
  refine WP.seq (wp_movz fun σ₁ u₁ => ?_)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.AArch64.Stream.Init.zero_ok hw (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_) fun s₂ h₂ => ?_
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσ0]; exact fun _ _ h => h
  have hZ : s₂.mem = VG.WriteBytes.writeBytes σ.mem (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) (List.replicate (blockBytes w) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσ0, u₁.mem, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.2.2.1)]
  have hfZ : Frame [VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans
      (VG.WriteBytes.writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine wp_addImm (by rw [VG.Proof.Blake2.AArch64.Stream.N_eq]; omega) fun s₃ u₃ => WP.block_nil ?_
  refine WP.mono (VG.Proof.Blake2.AArch64.Stream.Init.keyLoop_ok hw hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, ?_, ?_, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr],
    by rw [u₃.sp, h₂.sp, u₁.sp, hσ.sp], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide)]; simp
  · rw [u₃.gpr, h₂.gpr, u₁.other _ (by decide), hσ0, VG.Proof.Blake2.AArch64.Stream.N_eq]; simp
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3 h4 h5
    rw [u₃.other r h5, h₂.gpr, u₁.other r h1, hσ.gpr r h1 h2]
  · rw [u₃.mem, List.take_zero, VG.WriteBytes.writeBytes_nil]
  have hm : s.mem = VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes σ.mem (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) (List.replicate (blockBytes w) 0))
      (VG.Proof.Blake2.AArch64.Stream.Init.buf s₀ w) (VG.Proof.Blake2.AArch64.Stream.Init.key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega), hZ]
  refine ⟨h.other, h.sp, ?_, ?_⟩
  · rw [hm]
    exact (VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.AArch64.Stream.contains_prefix _ (by simp))).trans
      (VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.AArch64.Stream.contains_prefix _ (by omega)))
  · rw [hm, VG.Proof.Blake2.AArch64.Stream.Init.bytesAt_writeBytes (by omega) (by omega) fun i hi => ?_, hxs]
    rw [VG.Proof.Blake2.AArch64.Stream.Init.writeBytes_at _ _ _ (by omega)]
    simp [hi]

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ : State} (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hp : (VG.Proof.Blake2.initAArch64 P).pre s₀) :
    WP isa (Impl.Blake2.AArch64.Stream.init P) s₀ fun s' =>
      GprAbi s₀ s' ∧ (VG.Proof.Blake2.initAArch64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, -, -, hkk⟩ := hp
  have hw := hP.w
  have hs := VG.Proof.Blake2.AArch64.Stream.Init.sizes hw
  have hkb : VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ ≤ blockBytes w := Nat.le_trans hkk hP.max
  have hxs : (VG.Proof.Blake2.AArch64.Stream.Init.key s₀).length = VG.Proof.Blake2.AArch64.Stream.Init.kk s₀ := by simp [bytesAt]
  have hsub : ∀ r ∈ [(⟨VG.Proof.Blake2.AArch64.Stream.Init.st s₀, VG.Proof.Blake2.bufOff w⟩ : Region)], ∃ r' ∈ [VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Blake2.AArch64.Stream.Init.stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have hcs : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x12 := by decide
  unfold Impl.Blake2.AArch64.Stream.init
  refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Init.initState_ok (P := P) hw (fun a n h => ?_)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  have hx3 : σ.gpr .x3 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Init.kk s₀) := by
    rw [hσ.gpr _ (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff σ hx3 (s₀.gpr .x3).isLt) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => hσ.gpr r (hcs r hr).1 (hcs r hr).2.1, hσ.sp⟩, ?_⟩
    exact repr_keyBlock P hP.pos (hxs ▸ hkb) hσ.state fun h => absurd (hxs ▸ hb) h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (VG.Proof.Blake2.AArch64.Stream.Init.keyBlock_ok hw hrd hwr hd (by omega) hkb hσ) fun s ⟨hg, hsp, hf, hb'⟩ => ?_
    refine ⟨⟨fun r hr => hg r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2.1 (hcs r hr).2.2.2.1
      (hcs r hr).2.2.2.2, hsp⟩, ?_⟩
    refine repr_keyBlock P hP.pos (hxs ▸ hkb) ?_ fun _ => by rw [hxs]; exact hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨VG.Proof.Blake2.AArch64.Stream.Init.st s₀, VG.Proof.Blake2.bufOff w⟩)
      (by simpa using Offset.base_disjoint (VG.Proof.Blake2.AArch64.Stream.Init.st s₀) (Nat.le_refl (VG.Proof.Blake2.bufOff w)) (n := blockBytes w) (by omega))
      (by simp only; omega) hi

end VG.Proof.Blake2.AArch64.Stream.Init

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.AArch64.Stream.Update`. -/
section

/-!
# Streaming BLAKE2 on AArch64: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`). The same structure as the x86-64 proof
(`VG.Proof.Blake2.X86_64.Stream.Update`), inside the frame saving `x30`
(`WP.frameReg`).
-/

namespace VG.Proof.Blake2.AArch64.Stream.Update

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B mov copyLoop fill compressBuf head direct tail rest updateStart
  updateMain update saved save restore)
open VG.Impl.Blake2.AArch64 (lbb compress)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_addImm wp_subImm wp_movz wp_add wp_sub
  wp_and wp_lsr ofNat_beq_zero)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR
  stateAt_congr bytesAt_congr bytesAt_add updateAArch64)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev dp : Addr := s₀.gpr .x2
abbrev len : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Update.st s₀, VG.Proof.Blake2.bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Update.dp s₀, VG.Proof.Blake2.AArch64.Stream.Update.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Update.scr s₀, 576⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀) c
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.AArch64.Stream.Update.dR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Update.scR s₀]
  st_scr : (VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w).Disjoint (VG.Proof.Blake2.AArch64.Stream.Update.scR s₀)
  d_st : (VG.Proof.Blake2.AArch64.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w)
  d_scr : (VG.Proof.Blake2.AArch64.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Update.scR s₀)

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (w : Nat) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (VG.Proof.Blake2.AArch64.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w)
  d : (VG.Proof.Blake2.AArch64.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Update.dR s₀)
  scr : (VG.Proof.Blake2.AArch64.Stream.Update.stkR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Update.scR s₀)

theorem pre_of {s₀ : State} (h : (VG.Proof.Blake2.updateAArch64 P).pre s₀) : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀ ∧ VG.Proof.Blake2.AArch64.Stream.Update.Stack w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem len_lt (s₀ : State) : VG.Proof.Blake2.AArch64.Stream.Update.len s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
theorem cnt_lt (s₀ : State) : VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀ < 2 ^ 64 := (s₀.gpr .x1).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : VG.Spec.Blake2.Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) d ∧ s₀.gpr .x1 = BitVec.ofNat 64 d.length ∧
    d.length + VG.Proof.Blake2.AArch64.Stream.Update.len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : VG.Proof.Blake2.AArch64.Stream.Update.R₀ P s₀ h0 d) :
    VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega)]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.Blake2.AArch64.Stream.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = VG.Proof.Blake2.AArch64.Stream.Update.st s₀
  x20 : s.gpr .x20 = VG.Proof.Blake2.AArch64.Stream.Update.scr s₀
  x21 : s.gpr .x21 = VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀ + c)
  keep : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.untouched, s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Update.scR s₀] s₀.mem s.mem
  saved : VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : VG.Spec.Blake2.Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 r
  repr : ∀ h0 d, VG.Proof.Blake2.AArch64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28]

theorem notC {r : Reg} (hr : r ∈ VG.Proof.Blake2.AArch64.Stream.Update.commonRegs) (x : Reg) (hx : x ∉ VG.Proof.Blake2.AArch64.Stream.Update.commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s)
    (hg : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.Update.commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  x24 := by rw [hg _ (by simp)]; exact h.x24
  keep := fun r hr => by rw [hg r (by simp only [VG.Proof.Blake2.AArch64.Stream.untouched] at hr; simp [hr])]; exact h.keep r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c r s)
    (hg : ∀ r ∈ .x23 :: VG.Proof.Blake2.AArch64.Stream.Update.commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c r s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm hrd hwr hsp with
    x23 := by rw [hg _ (by simp)]; exact h.x23
    repr := by rw [hm]; exact h.repr }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c : Nat} {s : State} (h : VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s) {i : Nat}
    (hi : i < VG.Proof.Blake2.AArch64.Stream.Update.len s₀) : s.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := VG.Proof.Blake2.AArch64.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀)) hi

/-- Writes to the state and the compression function's scratch space keep the
saved registers. -/
theorem saved_frame {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {m m' : Mem} (h : VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr m)
    (hf : Frame [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, ⟨VG.Proof.Blake2.AArch64.Stream.Update.scr s₀, 512⟩] m m') : VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr m' :=
  Spill.Saved.frame h hf fun p hp' r' hr' => by
    have hoff := VG.Proof.Blake2.AArch64.Stream.saved_off p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))
    · exact Offset.disjoint_base _ (by omega) (by omega)

/-! ## Prologue -/

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s => VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ 0 s ∧ s.mem = VG.Proof.Blake2.AArch64.Stream.saveMem s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr := by
  refine VG.Proof.Blake2.AArch64.Stream.save_ok (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.AArch64.Stream.Update.scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x24 := by
      simp only [VG.Proof.Blake2.AArch64.Stream.untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [u₆.other _ this.2.2.2.2, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1, u₃.other _ this.2.1,
      u₂.other _ this.1, g₁]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    exact (VG.Proof.Blake2.AArch64.Stream.saveMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.scR s₀, by simp, Offset.sub_base _ (by omega)⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; exact VG.Proof.Blake2.AArch64.Stream.saveMem_saved _ _ _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## The bytes in the buffer -/

theorem bufLen_ok' (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {s : State} (hC : VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ 0 s)
    (hm : s.mem = VG.Proof.Blake2.AArch64.Stream.saveMem s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr) :
    WP isa (Impl.Blake2.AArch64.Stream.bufLen (w := w)) s (VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ 0 (Blake2.bufLen w (VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀))) := by
  have hN := hP.len
  have hrepr : ∀ h0 d, VG.Proof.Blake2.AArch64.Stream.Update.R₀ P s₀ h0 d →
      ReprR P h0 s.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ 0) (Blake2.bufLen w (VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀)) := by
    intro h0 d hd
    have e : VG.Proof.Blake2.AArch64.Stream.Update.D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine VG.Proof.Blake2.AArch64.Stream.repr_congr hP (fun i hi => ?_) hd.1
    rw [hm]
    exact (VG.Proof.Blake2.AArch64.Stream.saveMem_frame _ _ _).bytes (R := VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w)
      (by simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega))) (by simp only; omega) hi
  refine WP.mono (VG.Proof.Blake2.AArch64.Stream.bufLen_ok hP) fun s' ⟨h23, g, m, rd, wr, sp⟩ => ?_
  rw [hC.x24, Nat.add_zero, toNat_ofNat_lt (VG.Proof.Blake2.AArch64.Stream.Update.cnt_lt s₀)] at h23
  exact { hC.of_gpr (fun r hr => g r (VG.Proof.Blake2.AArch64.Stream.Update.notC hr .x9) (VG.Proof.Blake2.AArch64.Stream.Update.notC hr .x23)) m rd wr sp with
    x23 := h23, repr := by rw [m]; exact hrepr }

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

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ VG.Proof.Blake2.AArch64.Stream.Update.len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hx19 : s.gpr .x19 = VG.Proof.Blake2.AArch64.Stream.Update.st s₀)
    (hx21 : s.gpr .x21 = VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s.gpr .x11 = BitVec.ofNat 64 k) (hf : Frame [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Update.scR s₀] s₀.mem s.mem)
    (hs : VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr s.mem)
    (hrepr : ∀ h0 d, VG.Proof.Blake2.AArch64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → s'.gpr x = s.gpr x) ∧
      s'.gpr .x21 = VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .x23 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s.sp ∧ Frame [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Update.scR s₀] s₀.mem s'.mem ∧
      VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) s₀.gpr s'.mem ∧
      ∀ h0 d, VG.Proof.Blake2.AArch64.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s'.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨VG.Proof.Blake2.AArch64.Stream.Update.dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hdst : ∀ i < k, InRegions s.wr (VG.Proof.Blake2.AArch64.Stream.Update.st s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨VG.Proof.Blake2.AArch64.Stream.Update.st s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  refine VG.Proof.Blake2.AArch64.Stream.copyLoop_ok (w := w) hP.N64 hk (by omega) hx19 hx21 hx23 hx11 hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : bytesAt s.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := VG.Proof.Blake2.AArch64.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt hL) (show c + i < VG.Proof.Blake2.AArch64.Stream.Update.len s₀ by omega)
  have hm : s'.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w + r))
      (bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length]), hx]
  have hfw : Frame [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w] s.mem s'.mem := by
    rw [hm]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length]; exact Offset.contains_base _ (by omega) (by omega))
  refine ⟨h.other, h.x21.trans (Offset.add_add _ _ _), h.x23, h.rd.trans hrd, h.wr.trans hwr, h.sp,
    hf.trans (hfw.mono (by simp)), VG.Proof.Blake2.AArch64.Stream.Update.saved_frame hp hs (hfw.mono (by simp)), fun h0 d hd => ?_⟩
  have e : d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ (c + k) = d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ c ++ bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k := by
    rw [VG.Proof.Blake2.AArch64.Stream.Update.D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length]; exact hrk) ?_ ?_
  · rwa [VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by rw [VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length]; omega)
  · rw [hm, ← Offset.add_add, VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_writeBytes _ _ _ _ (by rw [VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length]; omega)]

/-! ## Calling the compression function -/

/-- The blocks compressed are the (full) buffer or blocks of data. -/
def Src (w : Nat) (s₀ : State) (src : Addr) (n : Nat) : Prop :=
  (src = VG.Proof.Blake2.AArch64.Stream.Update.st s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w) ∧ n = blockBytes w) ∨
    ∃ c₀, src = VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + n ≤ VG.Proof.Blake2.AArch64.Stream.Update.len s₀

theorem callOk (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c : Nat} {s : State} (h : VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s)
    {src : Addr} {n : Nat} (hsrc : VG.Proof.Blake2.AArch64.Stream.Update.Src w s₀ src n) : VG.Proof.Blake2.AArch64.Stream.CallOk (w := w) s (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) (VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) src n := by
  have hl := hP.len; have := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  have eN : Region.Sub ⟨VG.Proof.Blake2.AArch64.Stream.Update.st s₀, VG.Proof.Blake2.bufOff w⟩ (VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.Blake2.AArch64.Stream.Update.scr s₀, 512⟩ (VG.Proof.Blake2.AArch64.Stream.Update.scR s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨src, n⟩ (VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (VG.Proof.Blake2.AArch64.Stream.Update.dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ Offset.sub_base _ (by omega))
    · exact .inr (h' ▸ Offset.sub_base _ (by omega))
  refine ⟨h.x19, h.x20, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_, ?_, ?_⟩
  · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ Offset.sub_base _ (by omega))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, by simp, VG.Proof.Blake2.bufOff w, h', by simp⟩
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.scR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.scR s₀, by simp, 0, by simp, by simp⟩

theorem commonRegs_preserved : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.Update.commonRegs, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c : Nat} {s s' : State}
    (h : VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r)
    (hf : Frame [⟨VG.Proof.Blake2.AArch64.Stream.Update.st s₀, VG.Proof.Blake2.bufOff w⟩, ⟨VG.Proof.Blake2.AArch64.Stream.Update.scr s₀, 512⟩] s.mem s'.mem) :
    VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s' := by
  have hl := hP.len
  have hf' : Frame [VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, ⟨VG.Proof.Blake2.AArch64.Stream.Update.scr s₀, 512⟩] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨VG.Proof.Blake2.AArch64.Stream.Update.scr s₀, 512⟩, by simp, fun _ h => h⟩
  have hg : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.Update.commonRegs, s'.gpr r = s.gpr r := fun r hr =>
    hcs r (VG.Proof.Blake2.AArch64.Stream.Update.commonRegs_preserved r hr).1 (VG.Proof.Blake2.AArch64.Stream.Update.commonRegs_preserved r hr).2
  refine ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, by rw [hg _ (by simp)]; exact h.x19,
    by rw [hg _ (by simp)]; exact h.x20, by rw [hg _ (by simp)]; exact h.x21,
    by rw [hg _ (by simp)]; exact h.x22, by rw [hg _ (by simp)]; exact h.x24,
    fun r hr => by rw [hg r (by simp only [VG.Proof.Blake2.AArch64.Stream.untouched] at hr; simp [hr])]; exact h.keep r hr,
    h.frame.trans (hf'.sub fun r hr => ?_), VG.Proof.Blake2.AArch64.Stream.Update.saved_frame hp h.saved hf'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨VG.Proof.Blake2.AArch64.Stream.Update.scR s₀, by simp, Region.sub_prefix (by omega)⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀)
    {c : Nat} {s : State} (hI : VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c (blockBytes w) s) :
    WP isa (compressBuf P) s (VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c 0) := by
  have hl := hP.len
  have hN := hP.N64
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (VG.Proof.Blake2.AArch64.Stream.compressWith_ok hf (VG.Proof.Blake2.AArch64.Stream.bufArgs_ok (by omega))
    (by rw [VG.Proof.Blake2.AArch64.Stream.Update.one_toNat, Nat.mul_one]; exact VG.Proof.Blake2.AArch64.Stream.Update.callOk hP hp hI.toCommon (.inl ⟨by rw [hI.x19], rfl⟩))
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  refine wp_movz fun s₂ u₂ => WP.block_nil ?_
  have hC := hI.toCommon.after_call hP hp hrd hwr hsp hcs hfr
  refine { hC.of_gpr (fun r hr => u₂.other r (VG.Proof.Blake2.AArch64.Stream.Update.notC hr .x23)) u₂.mem u₂.rd u₂.wr u₂.sp with
    x23 := by rw [u₂.gpr]; rfl, repr := fun h0 d hd => ?_ }
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  have hlt := hd.2.2
  rw [hst, VG.Proof.Blake2.AArch64.Stream.Update.one_toNat, VG.Proof.Blake2.AArch64.Stream.Update.compressBlocks_one, hI.x19, hI.x24, List.length_append, VG.Proof.Blake2.AArch64.Stream.Update.D, VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length,
    ← hd.cnt_eq, toNat_ofNat_lt (by rw [← hd.cnt_eq] at hlt; omega)]
  rfl

/-! ## `head`: filling the buffer -/

theorem lt_of_div_zero {x b : Nat} (hb : 0 < b) (h : x / b = 0) : x < b := by
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.div_pos hc hb
  omega

theorem le_of_div_ne {x b : Nat} (h : x / b ≠ 0) : b ≤ x := by
  refine Nat.le_of_not_lt fun hc => h (Nat.div_eq_of_lt hc)

/-- Copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c r s) :
    WP isa (VG.Impl.Blake2.AArch64.Stream.fill (w := w)) s (VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ (c + min (blockBytes w - r) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c))
      (r + min (blockBytes w - r) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c))) := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  have hcn := VG.Proof.Blake2.AArch64.Stream.Update.cnt_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold VG.Impl.Blake2.AArch64.Stream.fill
  refine WP.seq (wp_movz fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr hP.lbb.1 fun s₃ u₃ => WP.block_nil ?_)
  have h11 : s₃.gpr .x11 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23, VG.Proof.Blake2.AArch64.Stream.movz_B hP, VG.Proof.Blake2.AArch64.Stream.sub_ofNat hr]
  have h9 : s₃.gpr .x9 = BitVec.ofNat 64 ((VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c) / blockBytes w) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22, VG.Proof.Blake2.AArch64.Stream.shr_ofNat hP (by omega)]
  have g₃ : ∀ x, x ≠ .x9 → x ≠ .x11 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h1, u₂.other x h2, u₁.other x h2]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- `x11` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .x11 = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .x9 → x ≠ .x11 → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ fun t ht => ?_)
  · refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₃ h9 (by have := Nat.div_le_self (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c) (blockBytes w); omega))
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hlt := VG.Proof.Blake2.AArch64.Stream.Update.lt_of_div_zero hpos hb
      refine WP.seq (wp_add fun s₄ u₄ => wp_lsr hP.lbb.1 fun s₅ u₅ => WP.block_nil ?_)
      have h9' : s₅.gpr .x9 = BitVec.ofNat 64 ((VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c + r) / blockBytes w) := by
        rw [u₅.gpr, u₄.gpr, g₃ _ (by decide) (by decide), g₃ _ (by decide) (by decide), hI.x22, hI.x23,
          ← BitVec.ofNat_add, VG.Proof.Blake2.AArch64.Stream.shr_ofNat hP (by omega)]
      have g₅ : ∀ x, x ≠ .x9 → x ≠ .x11 → s₅.gpr x = s.gpr x := fun x h1 h2 => by
        rw [u₅.other x h1, u₄.other x h1, g₃ x h1 h2]
      have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, hm₃]
      have hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, hrd₃]
      have hwr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, hwr₃]
      have hsp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, hsp₃]
      refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₅ h9' (by have := Nat.div_le_self (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c + r) (blockBytes w); omega))
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        have hlt' := VG.Proof.Blake2.AArch64.Stream.Update.lt_of_div_zero hpos hb'
        refine wp_mov fun s₆ u₆ => WP.block_nil ⟨?_, fun x h1 h2 => by rw [u₆.other x h2, g₅ x h1 h2],
          by rw [u₆.mem, hm₅], by rw [u₆.rd, hrd₅], by rw [u₆.wr, hwr₅], by rw [u₆.sp, hsp₅]⟩
        rw [u₆.gpr, g₅ _ (by decide) (by decide), hI.x22, ha, Nat.min_eq_right (by omega)]
      · simp only [decide_eq_false_iff_not] at hb'
        have hle := VG.Proof.Blake2.AArch64.Stream.Update.le_of_div_ne hb'
        refine WP.block_nil ⟨?_, g₅, hm₅, hrd₅, hwr₅, hsp₅⟩
        rw [u₅.other _ (by decide), u₄.other _ (by decide), h11, ha, Nat.min_eq_left (by omega)]
    · simp only [decide_eq_false_iff_not] at hb
      have hle := VG.Proof.Blake2.AArch64.Stream.Update.le_of_div_ne hb
      refine WP.block_nil ⟨?_, g₃, hm₃, hrd₃, hwr₃, hsp₃⟩
      rw [h11, ha, Nat.min_eq_left (by omega)]
  obtain ⟨tx11, tg, tm, trd, twr, tsp⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_)
  have g₆ : ∀ x, x ≠ .x9 → x ≠ .x11 → x ≠ .x22 → x ≠ .x24 → s₆.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₆.other x h4, u₅.other x h3, tg x h1 h2]
  have h611 : s₆.gpr .x11 = BitVec.ofNat 64 a := by rw [u₆.other _ (by decide), u₅.other _ (by decide), tx11]
  have h622 : s₆.gpr .x22 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - (c + a)) := by
    rw [u₆.other _ (by decide), u₅.gpr, tx11, tg _ (by decide) (by decide), hI.x22, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have h624 : s₆.gpr .x24 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀ + (c + a)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tx11, tg _ (by decide) (by decide), hI.x24,
      ← BitVec.ofNat_add, Nat.add_assoc]
  have hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, tm]
  have hrd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, trd]
  have hwr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, twr]
  have hsp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, tsp]
  have hkeep₆ : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.untouched, s₆.gpr r = s₀.gpr r := fun r hr => by
    rw [g₆ r (VG.Proof.Blake2.AArch64.Stream.notU hr .x9) (VG.Proof.Blake2.AArch64.Stream.notU hr .x11) (VG.Proof.Blake2.AArch64.Stream.notU hr .x22) (VG.Proof.Blake2.AArch64.Stream.notU hr .x24), hI.keep r hr]
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₆ h611 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨⟨by omega, hrd₆.trans hI.rd, hwr₆.trans hI.wr, hsp₆.trans hI.sp, ?_, ?_, ?_, h622,
      h624, hkeep₆, by rw [hm₆]; exact hI.frame, by rw [hm₆]; exact hI.saved⟩, ?_, ?_⟩
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.x21
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.x23
    · rw [hm₆, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.copy_ok hP hp (c := c) (r := r) (k := a) (by omega) (by omega) (by omega)
      (hrd₆.trans hI.rd) (hwr₆.trans hI.wr)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x21)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x23) h611
      (by rw [hm₆]; exact hI.frame) (by rw [hm₆]; exact hI.saved) (by rw [hm₆]; exact hI.repr))
      fun s₈ ⟨g₈, h821, h823, rd₈, wr₈, sp₈, f₈, sv₈, rp₈⟩ => ?_
    refine ⟨⟨by omega, rd₈, wr₈, sp₈.trans (hsp₆.trans hI.sp), ?_, ?_, h821, ?_, ?_, fun r hr => ?_, f₈, sv₈⟩,
      h823, rp₈⟩
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h622
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h624
    · rw [g₈ r (VG.Proof.Blake2.AArch64.Stream.notU hr .x9) (VG.Proof.Blake2.AArch64.Stream.notU hr .x12) (VG.Proof.Blake2.AArch64.Stream.notU hr .x21) (VG.Proof.Blake2.AArch64.Stream.notU hr .x23) (VG.Proof.Blake2.AArch64.Stream.notU hr .x11)]
      exact hkeep₆ r hr

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c r s ∧ ((c = VG.Proof.Blake2.AArch64.Stream.Update.len s₀ ∧ 1 ≤ r) ∨ (c < VG.Proof.Blake2.AArch64.Stream.Update.len s₀ ∧ r = 0))

theorem head_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < VG.Proof.Blake2.AArch64.Stream.Update.len s₀) {s : State} (hI : VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ 0 r s) :
    WP isa (head P) s (VG.Proof.Blake2.AArch64.Stream.Update.HeadPost P s₀) := by
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s hI.x23 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.fill_ok hP hp hr hI) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₂ hI₂.x22 (by omega)) (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₂, .inl ⟨by omega, by omega⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) = blockBytes w := by omega
      rw [e] at hI₂
      exact WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.compressBuf_ok hP hf hp hI₂) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

/-- The arguments for compressing blocks of data. -/
theorem directArgs_ok {σ : State} (hB : B w < 4096) :
    WP isa (.block (([mov .x0 .x19] : List Instr) ++ ([mov .x1 .x21, mov .x2 .x10,
      .addImm .x .x3 .x24 (B w), .movz .x .x4 0 0] : List Instr) ++ ([mov .x5 .x20] : List Instr))) σ
      fun s => VG.Proof.Blake2.AArch64.Stream.Setup σ s (σ.gpr .x21) (σ.gpr .x10) (σ.gpr .x24 + BitVec.ofNat 64 (B w)) false := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addImm hB fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hcs : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c : Nat}
    (hc : c < VG.Proof.Blake2.AArch64.Stream.Update.len s₀) {s : State} (hI : VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c 0 s) :
    WP isa (direct P) s (VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ (c + blockBytes w * ((VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  have hcn := VG.Proof.Blake2.AArch64.Stream.Update.cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨k, hk⟩ : ∃ k, k = (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hkle : k ≤ VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_lsr hP.lbb.1 fun s₂ u₂ => WP.block_nil ?_)
  have h10 : s₂.gpr .x10 = BitVec.ofNat 64 k := by
    rw [u₂.gpr, u₁.gpr, hI.x22, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega), VG.Proof.Blake2.AArch64.Stream.shr_ofNat hP (by omega), hk]
  have hC₂ : VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ c s₂ := hI.toCommon.of_gpr
    (fun r hr => by rw [u₂.other r (VG.Proof.Blake2.AArch64.Stream.Update.notC hr .x10), u₁.other r (VG.Proof.Blake2.AArch64.Stream.Update.notC hr .x9)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  have h23 : s₂.gpr .x23 = BitVec.ofNat 64 0 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hI.x23
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₂ h10 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₂, h23, by rw [hm₂]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  have hBk : blockBytes w * k + 1 ≤ VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c := by omega
  have hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega)
  have hsrc : VG.Proof.Blake2.AArch64.Stream.Update.Src w s₀ (s₂.gpr .x21) (blockBytes w * (s₂.gpr .x10).toNat) :=
    .inr ⟨c, hC₂.x21, by rw [h10, toNat_ofNat_lt (by omega)]; omega⟩
  refine WP.seq (VG.Proof.Blake2.AArch64.Stream.compressWith_ok hf (VG.Proof.Blake2.AArch64.Stream.Update.directArgs_ok (by rw [VG.Proof.Blake2.AArch64.Stream.B_eq]; omega)) (VG.Proof.Blake2.AArch64.Stream.Update.callOk hP hp hC₂ hsrc)
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  have hC' := hC₂.after_call hP hp hrd hwr hsp hcs hfr
  refine wp_subImm (by decide) fun s₁ u₁ => wp_movz fun s₃ u₃ => wp_and fun s₄ u₄ =>
    wp_addImm (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_mov fun s₉ u₉ => WP.block_nil ?_
  have hm : (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) % blockBytes w + 1 = VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - (c + blockBytes w * k) := by omega
  have hx9 : s₅.gpr .x9 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₁.gpr, hC'.x22, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega), VG.Proof.Blake2.AArch64.Stream.mask_mod hP,
      toNat_ofNat_lt (by omega), ← BitVec.ofNat_add, hm]
  have h10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₁.other _ (by decide), hC'.x22, hx9, VG.Proof.Blake2.AArch64.Stream.sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have hg : ∀ x, x ≠ .x9 → x ≠ .x10 → x ≠ .x21 → x ≠ .x22 → x ≠ .x24 → s₉.gpr x = s'.gpr x :=
    fun x h1 h2 h3 h4 h5 => by
      rw [u₉.other x h4, u₈.other x h5, u₇.other x h3, u₆.other x h2, u₅.other x h1, u₄.other x h1,
        u₃.other x h2, u₁.other x h1]
  have hm₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₁.mem]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₁.rd, hC'.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₁.wr, hC'.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₁.sp, hC'.sp]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.x19
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.x20
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), h10₆,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide),
      hC'.x21, Offset.add_add]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), hx9]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other .x24 (by decide), u₇.other .x10 (by decide), h10₆,
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₁.other _ (by decide), hC'.x24, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg r (VG.Proof.Blake2.AArch64.Stream.notU hr .x9) (VG.Proof.Blake2.AArch64.Stream.notU hr .x10) (VG.Proof.Blake2.AArch64.Stream.notU hr .x21) (VG.Proof.Blake2.AArch64.Stream.notU hr .x22) (VG.Proof.Blake2.AArch64.Stream.notU hr .x24)]; exact hC'.keep r hr
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), hcs _ (by decide) (by decide), h23]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    have e : d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ (c + blockBytes w * k) =
        d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ c ++ bytesAt s₂.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [VG.Proof.Blake2.AArch64.Stream.Update.D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₂.data hp (by omega)).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₂]; exact hI.repr h0 d hd) ?_
    rw [hst, h10, hC₂.x21, hC₂.x24, VG.Proof.Blake2.AArch64.Stream.B_eq, ← BitVec.ofNat_add, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega), List.length_append, VG.Proof.Blake2.AArch64.Stream.Update.D, VG.Proof.Blake2.AArch64.Stream.Update.bytesAt_length, ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {c : Nat} (hc₁ : c < VG.Proof.Blake2.AArch64.Stream.Update.len s₀)
    (hc₂ : VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c ≤ blockBytes w) {s : State} (hI : VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ c 0 s) :
    WP isa (tail (w := w)) s (VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c)) := by
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .x11 → x ≠ .x24 → x ≠ .x22 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have h11 : s₃.gpr .x11 = BitVec.ofNat 64 (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.x22]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.copy_ok hP hp (c := c) (r := 0) (k := VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c) (by omega) (by omega) (by omega)
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x19)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x21)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x23) h11
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h421, h423, rd₄, wr₄, sp₄, f₄, sv₄, rp₄⟩ => ?_
  have e : c + (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c) = VG.Proof.Blake2.AArch64.Stream.Update.len s₀ := by omega
  rw [e] at h421 rp₄
  rw [Nat.zero_add] at h423 rp₄
  have g : ∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → x ≠ .x24 → x ≠ .x22 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 => by rw [g₄ x h1 h2 h3 h4 h5, hg x h5 h6 h7]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, by rw [sp₄, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, h421, ?_, ?_,
    fun r hr => ?_, f₄, sv₄⟩, h423, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]; rfl
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), hI.x24, hI.x22, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  · rw [g r (VG.Proof.Blake2.AArch64.Stream.notU hr .x9) (VG.Proof.Blake2.AArch64.Stream.notU hr .x12) (VG.Proof.Blake2.AArch64.Stream.notU hr .x21) (VG.Proof.Blake2.AArch64.Stream.notU hr .x23) (VG.Proof.Blake2.AArch64.Stream.notU hr .x11) (VG.Proof.Blake2.AArch64.Stream.notU hr .x24)
      (VG.Proof.Blake2.AArch64.Stream.notU hr .x22)]
    exact hI.keep r hr

/-- All the data is in, and the buffer is not empty. -/
def Full (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop := ∃ r, VG.Proof.Blake2.AArch64.Stream.Update.Inv P s₀ (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {s : State}
    (h : VG.Proof.Blake2.AArch64.Stream.Update.HeadPost P s₀ s) : WP isa (rest P) s (VG.Proof.Blake2.AArch64.Stream.Update.Full P s₀) := by
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  have hc := hI.c_le
  unfold rest
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s hI.x22 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI, hr⟩
    · omega
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega
    refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.direct_ok hP hf hp hc' hI) fun s₂ hI₂ => ?_)
    have hdm := Nat.div_add_mod (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) (blockBytes w)
    have hmod := Nat.mod_lt (VG.Proof.Blake2.AArch64.Stream.Update.len s₀ - c - 1) hpos
    exact WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.tail_ok hP hp (by omega) (by omega) hI₂) fun s₃ hI₃ => ⟨_, hI₃, by omega⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : VG.Spec.Blake2.Params w) (s₀ : State) (s : State) : Prop :=
  VG.Proof.Blake2.AArch64.Stream.Update.Common w s₀ (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) s ∧
    ∀ h0 d, VG.Proof.Blake2.AArch64.Stream.Update.R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (VG.Proof.Blake2.AArch64.Stream.Update.st s₀) (d ++ VG.Proof.Blake2.AArch64.Stream.Update.D s₀ (VG.Proof.Blake2.AArch64.Stream.Update.len s₀))

theorem Full.done (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) {s₀ : State} {s : State} (h : VG.Proof.Blake2.AArch64.Stream.Update.Full P s₀ s) : VG.Proof.Blake2.AArch64.Stream.Update.Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

/-- The epilogue's postcondition. -/
def Post (P : VG.Spec.Blake2.Params w) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ (VG.Proof.Blake2.updateAArch64 P).post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) {s : State} (hI : VG.Proof.Blake2.AArch64.Stream.Update.Done P s₀ s) :
    WP isa (.block restore) s (VG.Proof.Blake2.AArch64.Stream.Update.Post P s₀) := by
  refine VG.Proof.Blake2.AArch64.Stream.restore_ok (scr := VG.Proof.Blake2.AArch64.Stream.Update.scr s₀) hI.1.x20
    (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.AArch64.Stream.Update.scR s₀, by simp [hI.1.rd, hI.1.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    s₀.gpr hI.1.saved fun s' hs ho hmem _ _ hsp => ⟨VG.Proof.Blake2.AArch64.Stream.preserved_of hs fun r hr => ?_, by rw [hsp, hI.1.sp],
      fun h0 d hr hc hl => ?_⟩
  · rw [ho r (by simp only [VG.Proof.Blake2.AArch64.Stream.untouched] at hr; simp only [saved, List.map_cons, List.map_nil]; decide +revert),
      hI.1.keep r hr]
  · rw [hmem]; exact hI.2 h0 d ⟨hr, hc, hl⟩

/-- `update` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Update.Pre w s₀) :
    WP isa (updateMain P) s₀ (VG.Proof.Blake2.AArch64.Stream.Update.Post P s₀) := by
  have hL := VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀
  unfold updateMain
  refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.bufLen_ok' hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.AArch64.Stream.Update.Done P s₀) ?_ fun s₄ h => VG.Proof.Blake2.AArch64.Stream.Update.epilogue_ok hp h)
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₂ hI.x22 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq, Nat.sub_zero] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI.toCommon, fun h0 d hd => ?_⟩
    have := hI.repr h0 d hd
    have e0 : ∀ n, n = 0 → bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show VG.Proof.Blake2.AArch64.Stream.Update.D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show VG.Proof.Blake2.AArch64.Stream.Update.D s₀ (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not, Nat.sub_zero] at hb
    have hr := bufLen_le (w := w) hP.pos (VG.Proof.Blake2.AArch64.Stream.Update.cnt s₀)
    exact WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.head_ok hP hf hp hr (by omega) hI) fun s₄ h =>
      WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.rest_ok hP hf hp h) fun s₅ h => h.done hP)

theorem noFrames_updateMain (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) : (updateMain P).noFrames = true := by
  simp only [updateMain, head, rest, VG.Impl.Blake2.AArch64.Stream.fill, compressBuf, direct, tail, Impl.Blake2.AArch64.Stream.compressWith,
    copyLoop, Impl.Blake2.AArch64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The state `updateMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State}
    (hpre : (VG.Proof.Blake2.updateAArch64 P).pre s₀) :
    WP isa (update P) s₀ fun s' => GprAbi s₀ s' ∧ (VG.Proof.Blake2.updateAArch64 P).post s₀ s' := by
  obtain ⟨hp, hs⟩ := VG.Proof.Blake2.AArch64.Stream.Update.pre_of hpre
  have hl := hP.len
  have hpi : VG.Proof.Blake2.AArch64.Stream.Update.Pre w (VG.Proof.Blake2.AArch64.Stream.Update.inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (VG.Proof.Blake2.AArch64.Stream.Update.correctMain hP hf hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
    (by rw [VG.Proof.Blake2.AArch64.Stream.fdepth_of_noFrames (VG.Proof.Blake2.AArch64.Stream.Update.noFrames_updateMain hf)]; decide)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun h0 d hm hc hlt => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (VG.Proof.Blake2.AArch64.Stream.Update.inner s₀).mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) = bytesAt s₀.mem (VG.Proof.Blake2.AArch64.Stream.Update.dp s₀) (VG.Proof.Blake2.AArch64.Stream.Update.len s₀) :=
        bytesAt_congr fun i hi => VG.Proof.Blake2.AArch64.Stream.write_frame_bytes hs.d (VG.Proof.Blake2.AArch64.Stream.Update.len_lt s₀) hi
      have := hpost h0 d (VG.Proof.Blake2.AArch64.Stream.repr_congr hP (fun i hi => VG.Proof.Blake2.AArch64.Stream.write_frame_bytes (R := VG.Proof.Blake2.AArch64.Stream.Update.stR s₀ w) hs.st
        (by show VG.Proof.Blake2.bufOff w + blockBytes w < 2 ^ 64; omega) hi) hm) hc hlt
      rw [e] at this
      exact this

end VG.Proof.Blake2.AArch64.Stream.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified`. -/
section

section

/-!
# Streaming BLAKE2 on AArch64: `finalize`

Inside the frame saving `x30` (`WP.frameReg`), `finalize` saves the
callee-saved registers (`prologue_ok`), computes the number of buffered bytes
(`bufLen_ok`), zeroes the rest of the buffer (`pad_ok`), compresses it as the
last block (`compressWith_ok`), copies the hash value out (`output_ok`) and
restores the registers (`restore_ok`).
-/

namespace VG.Proof.Blake2.AArch64.Stream.Finalize

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B mov zeroLoop pad compressLast output finalizeMain finalize saved save
  restore)
open VG.Impl.Blake2.AArch64 (compress)
open VG.Proof.Blake2 (finalizeAArch64 bufOff final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_movz wp_sub wp_ldr wp_str)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame writeBytes_append writeBytes_before
  write_eq_writeBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev op : Addr := s₀.gpr .x2
abbrev scr : Addr := s₀.gpr .x3
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.op s₀, bufOff w⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀, 576⟩
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀]
  st_out : (VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w)
  st_scr : (VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀)
  out_scr : (VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w).Disjoint (VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀)

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (w : Nat) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (VG.Proof.Blake2.AArch64.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w)
  out : (VG.Proof.Blake2.AArch64.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w)
  scr : (VG.Proof.Blake2.AArch64.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀)

theorem pre_of {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ : State} (h : (VG.Proof.Blake2.finalizeAArch64 P).pre s₀) :
    VG.Proof.Blake2.AArch64.Stream.Finalize.Pre w s₀ ∧ VG.Proof.Blake2.AArch64.Stream.Finalize.Stack w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w : Nat} {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Finalize.Pre w s₀) {g : Reg → BitVec 64} {m m' : Mem}
    (h : VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀) g m) (hf : Frame [VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w, ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀, 512⟩] m m') :
    VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀) g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have hoff := VG.Proof.Blake2.AArch64.Stream.saved_off p hp'
    have hsub : Region.Sub ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left hsub
    · exact hp.out_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀
  x20 : s.gpr .x20 = VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀
  x21 : s.gpr .x21 = VG.Proof.Blake2.AArch64.Stream.Finalize.op s₀
  x24 : s.gpr .x24 = s₀.gpr .x1
  keep : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.untouched, s.gpr r = s₀.gpr r
  mem : s.mem = VG.Proof.Blake2.AArch64.Stream.saveMem s₀.mem (VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀) s₀.gpr

theorem prologue_ok {w : Nat} {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Finalize.Pre w s₀) :
    WP isa (.block (save .x3 ++ ([mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x24 .x1] : List Instr)))
      s₀ (VG.Proof.Blake2.AArch64.Stream.Finalize.Start s₀) := by
  refine VG.Proof.Blake2.AArch64.Stream.save_ok (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (VG.Proof.Blake2.AArch64.Stream.notU hr .x24), u₄.other _ (VG.Proof.Blake2.AArch64.Stream.notU hr .x21), u₃.other _ (VG.Proof.Blake2.AArch64.Stream.notU hr .x20),
      u₂.other _ (VG.Proof.Blake2.AArch64.Stream.notU hr .x19), g₁]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## Zeroing the rest of the buffer -/

section
variable {w : Nat}

/-- Zeroing the buffer from byte `r` (in `x23`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hN : bufOff w ≤ 64) (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2 ^ 16) (hx19 : s.gpr .x19 = st) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad (w := w)) s fun s' =>
      (∀ x, x ≠ .x9 → x ≠ .x11 → x ≠ .x12 → x ≠ .x23 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold pad
  refine WP.seq (wp_movz fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_sub fun s₃ u₃ => WP.block_nil ?_)
  have g : ∀ x, x ≠ .x9 → x ≠ .x11 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  have h11 : s₃.gpr .x11 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .x23 (by decide), u₂.gpr, u₁.other .x23 (by decide), hx23,
      VG.Proof.Blake2.AArch64.Stream.movz_ofNat (n := B w) hbb, VG.Proof.Blake2.AArch64.Stream.B_eq, VG.Proof.Blake2.AArch64.Stream.sub_ofNat hr]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite _ (VG.Proof.Blake2.AArch64.Stream.zero_iff s₃ h11 (by omega)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ _ => g x h1 h2, hrd₃, hwr₃, hsp₃, ?_⟩
    rw [hb, List.replicate_zero, VG.WriteBytes.writeBytes_nil, hm₃]
  · simp only [decide_eq_false_iff_not] at hb
    refine VG.Proof.Blake2.AArch64.Stream.zeroLoop_ok (st := st) (r := r) hN (by omega) (by omega)
      (by rw [g _ (by decide) (by decide), hx19])
      (by rw [g _ (by decide) (by decide), hx23]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl)
      (fun i hi => by rw [hwr₃]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 h4 => by rw [h.other x h3 h4 h2, g x h1 h2], by rw [h.rd, hrd₃],
      by rw [h.wr, hwr₃], by rw [h.sp, hsp₃], ?_⟩
    rw [h.mem, hm₃]

end

/-! ## Bytes -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    VG.WriteBytes.writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes, Mem.sub_ofNat_toNat q hi]

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = VG.WriteBytes.writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Blake2.AArch64.Stream.Finalize.writeBytes_at m q xs (by omega : i < 2 ^ 64),
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
  · rw [hm]; exact VG.Proof.Blake2.AArch64.Stream.Finalize.bytesAt_writeBytes_self _ _ (by simp) (by omega)

/-! ## Copying the hash value out -/

section
variable {w : Nat}

theorem output_eq : output (w := w) = (List.range (VG.Impl.Blake2.AArch64.Stream.N w / 8)).flatMap fun k =>
    [.ldr .x .x9 .x19 (8 * k), .str .x .x9 .x21 (8 * k)] := rfl

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .x9 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
    s.mem = VG.WriteBytes.writeBytes σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (8 * k))

theorem output_ok {σ : State} (hN : bufOff w ≤ 64) (hN8 : bufOff w % 8 = 0)
    (hin : ∀ a n, (⟨σ.gpr .x19, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .x21, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .x19, bufOff w⟩ ⟨σ.gpr .x21, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .x9 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = VG.WriteBytes.writeBytes σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (bufOff w)) := by
  have e : 8 * (VG.Impl.Blake2.AArch64.Stream.N w / 8) = bufOff w := by rw [VG.Proof.Blake2.AArch64.Stream.N_eq]; omega
  rw [VG.Proof.Blake2.AArch64.Stream.Finalize.output_eq, ← e]
  refine wp_range_flatMap (M := isa) (VG.Proof.Blake2.AArch64.Stream.Finalize.OInv σ) (fun k s hk ⟨hg, hrd, hwr, hsp, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Blake2.AArch64.Stream.N_eq] at hk
  have hk8 : 8 * k + 8 ≤ bufOff w := by omega
  have hl : (bytesAt σ.mem (σ.gpr .x19) (8 * k)).length = 8 * k := by simp [bytesAt]
  refine wp_ldr (a := σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩
    (by rw [hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ hk8 (by omega)))
    fun s₁ u₁ => wp_str (a := σ.gpr .x21 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩ ?_ ?_ fun s₂ g₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, hg r hr], by rw [g₂.rd, u₁.rd, hrd],
        by rw [g₂.wr, u₁.wr, hwr], by rw [g₂.sp, u₁.sp, hsp], ?_⟩
  · rw [u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ hk8 (by omega))
  · have hv : s.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64 =
        σ.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64 := by
      rw [hm]
      exact (VG.WriteBytes.writeBytes_frame (R := ⟨σ.gpr .x21, bufOff w⟩) _ _ _
        (VG.Proof.Blake2.AArch64.Stream.contains_prefix _ (by omega))).readW
        (Offset.contains_base (k := bufOff w) _ hk8 (by omega)) (by simpa using hd) (by decide)
    have e := VG.WriteBytes.writeBytes_append σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (8 * k))
      (wordBytes (σ.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64))
      (by rw [hl]; simp [wordBytes]; omega)
    rw [hl] at e
    rw [g₂.mem, u₁.gpr, u₁.mem, hv, hm, VG.Proof.Blake2.AArch64.Stream.Finalize.writeW_eq, e,
      VG.Proof.Blake2.wordBytes_readW _ _ (.inr rfl), ← bytesAt_add, Nat.mul_succ]

end

/-! ## The whole function -/

section
variable {w : Nat} {P : VG.Spec.Blake2.Params w}

theorem noFrames_finalizeMain (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) : (finalizeMain P).noFrames = true := by
  simp only [finalizeMain, pad, compressLast, Impl.Blake2.AArch64.Stream.compressWith, zeroLoop,
    Impl.Blake2.AArch64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The registers kept from the prologue to the epilogue. -/
abbrev commonKeep : List Reg := [.x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28]

theorem commonKeep_ok : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.Finalize.commonKeep,
    r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x9 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x23 := by decide

/-- The epilogue's postcondition. -/
def Post (P : VG.Spec.Blake2.Params w) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ (VG.Proof.Blake2.finalizeAArch64 P).post s₀ s'

/-- `finalize` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State} (hp : VG.Proof.Blake2.AArch64.Stream.Finalize.Pre w s₀) :
    WP isa (finalizeMain P) s₀ (VG.Proof.Blake2.AArch64.Stream.Finalize.Post P s₀) := by
  have hl := hP.len
  have hN := hP.N64
  have hbb := hP.bb
  have hN8 : bufOff w % 8 = 0 := by simp only [bufOff]; omega
  have hstN : Region.Sub ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀, bufOff w⟩ (VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w) := Region.sub_prefix (by omega)
  have hsave_st : ∀ r ∈ [(⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀ + BitVec.ofNat 64 512, 48⟩ : Region)], (VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega))
  unfold finalizeMain
  refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Finalize.prologue_ok hp) fun s₁ h₁ => ?_)
  have hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [h₁.mem]; exact (VG.Proof.Blake2.AArch64.Stream.saveMem_frame _ _ _).bytes (R := VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w) hsave_st (by simp only; omega) hi
  refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.bufLen_ok hP) fun s₂ ⟨r23₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [h₁.x24] at r23₂
  generalize hn : (s₀.gpr .x1).toNat = n at r23₂
  have hr : Blake2.bufLen w n ≤ blockBytes w := bufLen_le (by omega) n
  have hx19₂ : s₂.gpr .x19 = VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ := by rw [g₂ _ (by decide) (by decide), h₁.x19]
  refine WP.seq (WP.mono (VG.Proof.Blake2.AArch64.Stream.Finalize.pad_ok (st := VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀) hN hr (by omega) hx19₂ r23₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have g₃' : ∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x12 → r ≠ .x23 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h4]
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have hsp₃ : s₃.sp = s₀.sp := by rw [sp₃, sp₂, h₁.sp]
  have hx19₃ : s₃.gpr .x19 = VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x19]
  have hx20₃ : s₃.gpr .x20 = VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x20]
  have hm₃ : s₃.mem = VG.WriteBytes.writeBytes s₁.mem (VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ + BitVec.ofNat 64 (bufOff w + Blake2.bufLen w n))
      (List.replicate (blockBytes w - Blake2.bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  have hbuf : Region.Sub ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w) :=
    Offset.sub_base _ (by omega)
  have hscr : Region.Sub ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀, 512⟩ (VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀) := Region.sub_prefix (by omega)
  have hcall : VG.Proof.Blake2.AArch64.Stream.CallOk (w := w) s₃ (VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀) (VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀) (s₃.gpr .x19 + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (BitVec.setWidth 64 (1 : BitVec 16)).toNat) := by
    rw [show (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 from rfl, Nat.mul_one, hx19₃]
    refine ⟨hx19₃, hx20₃, (hp.st_scr.sub_left hstN).sub_right hscr,
      Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hp.st_scr.sub_left hbuf).sub_right hscr, ?_, ?_⟩
    · rw [hrd₃, hwr₃, hp.rd, hp.wr, List.nil_append]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, by simp, bufOff w, rfl, by simp only; omega⟩
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · rw [hwr₃, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
      · exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  unfold compressLast
  refine WP.seq (VG.Proof.Blake2.AArch64.Stream.compressWith_ok hf (VG.Proof.Blake2.AArch64.Stream.bufArgs_ok (by omega)) hcall fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_)
  have cs : ∀ r ∈ VG.Proof.Blake2.AArch64.Stream.Finalize.commonKeep, s₄.gpr r = s₁.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := VG.Proof.Blake2.AArch64.Stream.Finalize.commonKeep_ok r hr
    rw [cs₄ r h1 h2, g₃' r h3 h4 h5 h6]
  have hx19₄ : s₄.gpr .x19 = VG.Proof.Blake2.AArch64.Stream.Finalize.st s₀ := by rw [cs _ (by simp), h₁.x19]
  have hx21₄ : s₄.gpr .x21 = VG.Proof.Blake2.AArch64.Stream.Finalize.op s₀ := by rw [cs _ (by simp), h₁.x21]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.AArch64.Stream.Finalize.output_ok (σ := s₄) hN hN8 (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, sp₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hx19₄] at h
    exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega⟩
  · rw [hwr₄, hp.wr]
    rw [hx21₄] at h
    exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w, by simp, h⟩
  · rw [hx19₄, hx21₄]; exact hp.st_out.sub_left hstN
  -- What the call and the stores wrote.
  have F₁ : Frame [VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w, ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀, 512⟩] s₁.mem s₅.mem := by
    have f₃ : Frame [VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega) (by omega))
    have f₅ : Frame [VG.Proof.Blake2.AArch64.Stream.Finalize.outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hx21₄]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (VG.Proof.Blake2.AArch64.Stream.contains_prefix _ (by simp [bytesAt]))
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have hsv : VG.Proof.Blake2.AArch64.Stream.Saved (VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀) s₀.gpr s₅.mem := Saved.frame hp (h₁.mem ▸ VG.Proof.Blake2.AArch64.Stream.saveMem_saved _ _ _) F₁
  refine VG.Proof.Blake2.AArch64.Stream.restore_ok (scr := VG.Proof.Blake2.AArch64.Stream.Finalize.scr s₀) (by rw [g₅ _ (by decide), cs _ (by simp), h₁.x20])
    (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.AArch64.Stream.Finalize.scR s₀, by simp [rd₅, wr₅, rd₄, wr₄, hrd₃, hwr₃, hp.wr],
      Offset.contains_base _ (by omega) (by omega)⟩) s₀.gpr hsv
    fun s₆ hs ho m₆ _ _ sp₆ => ⟨VG.Proof.Blake2.AArch64.Stream.preserved_of hs fun r hr => ?_, by rw [sp₆, sp₅, sp₄, hsp₃], ?_⟩
  · rw [ho r (by simp only [VG.Proof.Blake2.AArch64.Stream.untouched] at hr; simp only [saved, List.map_cons, List.map_nil]; decide +revert),
      g₅ r (VG.Proof.Blake2.AArch64.Stream.notU hr .x9), cs r (by simp only [VG.Proof.Blake2.AArch64.Stream.untouched] at hr; simp [hr]), h₁.keep r hr]
  · intro h0 d hR hlt hcnt
    have hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    have hx24₃ : (s₃.gpr .x24).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x24, hn]
    rw [m₆, m₅, hx21₄, hx19₄, VG.Proof.Blake2.AArch64.Stream.Finalize.bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega),
      bytesAt_state _ _ hP.w.symm, e₄, show (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 0 + 1 from rfl,
      compressBlocks_succ, compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero,
      hx24₃, hx19₃, show (((1 : BitVec 16).setWidth 64).setWidth 32 != 0) = true from rfl]
    refine final_eq P (by omega) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, VG.WriteBytes.writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + Blake2.bufLen w d.length)
          (by simp; omega), hkeep i (by omega)]
    · rw [VG.Proof.Blake2.AArch64.Stream.Finalize.pad_bytes hr (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega)]

/-- The state `finalizeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hP : VG.Proof.Blake2.AArch64.Stream.Ok P) (hf : VG.Proof.Blake2.AArch64.Stream.CalleeOk P (VG.Impl.Blake2.AArch64.compress P)) {s₀ : State}
    (hpre : (VG.Proof.Blake2.finalizeAArch64 P).pre s₀) :
    WP isa (finalize P) s₀ fun s' => GprAbi s₀ s' ∧ (VG.Proof.Blake2.finalizeAArch64 P).post s₀ s' := by
  obtain ⟨hp, hs⟩ := VG.Proof.Blake2.AArch64.Stream.Finalize.pre_of hpre
  have hl := hP.len
  have hpi : VG.Proof.Blake2.AArch64.Stream.Finalize.Pre w (VG.Proof.Blake2.AArch64.Stream.Finalize.inner s₀) := ⟨hp.rd, hp.wr, hp.st_out, hp.st_scr, hp.out_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (VG.Proof.Blake2.AArch64.Stream.Finalize.correctMain hP hf hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
    (by rw [VG.Proof.Blake2.AArch64.Stream.fdepth_of_noFrames (VG.Proof.Blake2.AArch64.Stream.Finalize.noFrames_finalizeMain hf)]; decide)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hs.st
    · exact hs.out
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun h0 d hm hlt hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · exact hpost h0 d (VG.Proof.Blake2.AArch64.Stream.repr_congr hP (fun i hi => VG.Proof.Blake2.AArch64.Stream.write_frame_bytes (R := VG.Proof.Blake2.AArch64.Stream.Finalize.stR s₀ w) hs.st
        (by show bufOff w + blockBytes w < 2 ^ 64; omega) hi) hm) hlt hc

end

end VG.Proof.Blake2.AArch64.Stream.Finalize

end

/-!
# Streaming BLAKE2 on AArch64: `Verified`

Correctness (from `Init`, `Update` and `Finalize`, with the compression
function of `Proof/Blake2/AArch64/Compress.lean`), constant time (from `CT`),
and a state satisfying each precondition, for BLAKE2b and BLAKE2s. `update`
and `finalize` save `x30` in 16 bytes below the stack pointer.
-/

namespace VG.Proof.Blake2.AArch64.Stream

open VG VG.AArch64 VG.Spec.Blake2

theorem calleeB : VG.Proof.Blake2.AArch64.Stream.CalleeOk b (Impl.Blake2.AArch64.compress b) :=
  ⟨Proof.Blake2.AArch64.compressB_correct, Proof.Blake2.AArch64.compressB_noFrames⟩

theorem calleeS : VG.Proof.Blake2.AArch64.Stream.CalleeOk s (Impl.Blake2.AArch64.compress s) :=
  ⟨Proof.Blake2.AArch64.compressS_correct, Proof.Blake2.AArch64.compressS_noFrames⟩

/-! ## States satisfying the preconditions -/

/-- `init` for `w`-bit words, with no key. -/
def initSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `update`, with no data, for `w`-bit words. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-! ## BLAKE2b -/

theorem initB_correct (st : State) (hs : (VG.Proof.Blake2.initAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.init b) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.initAArch64 b).post st s' :=
  WP.withPreservedV (Init.correct VG.Proof.Blake2.AArch64.Stream.okB hs) (by lit_decide)

theorem updateB_correct (st : State) (hs : (VG.Proof.Blake2.updateAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update b) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.updateAArch64 b).post st s' :=
  WP.withPreservedV (Update.correct VG.Proof.Blake2.AArch64.Stream.okB VG.Proof.Blake2.AArch64.Stream.calleeB hs) (by lit_decide)

theorem finalizeB_correct (st : State) (hs : (VG.Proof.Blake2.finalizeAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize b) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.finalizeAArch64 b).post st s' :=
  WP.withPreservedV (Finalize.correct VG.Proof.Blake2.AArch64.Stream.okB VG.Proof.Blake2.AArch64.Stream.calleeB hs) (by lit_decide)

theorem initB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.init b)
      (Spec.Blake2.initBContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Blake2.AArch64.Stream.initB_correct VG.Proof.Blake2.AArch64.Stream.initB_ct (by
    contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs] [initSat]
      using VG.Proof.Blake2.AArch64.Stream.initSat 64)

theorem updateB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update b)
      (Spec.Blake2.updateBScratchContract AArch64.abi 16) :=
  Verified.of_correct VG.Proof.Blake2.AArch64.Stream.updateB_correct VG.Proof.Blake2.AArch64.Stream.updateB_ct (by
    sig_implies [Spec.Blake2.updateBScratchContract, Spec.Blake2.updateBScratchSig, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using VG.Proof.Blake2.AArch64.Stream.updateSat 64)

theorem finalizeB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize b)
      (Spec.Blake2.finalizeBScratchContract AArch64.abi 16) :=
  Verified.of_correct VG.Proof.Blake2.AArch64.Stream.finalizeB_correct VG.Proof.Blake2.AArch64.Stream.finalizeB_ct (by
    sig_implies [Spec.Blake2.finalizeBScratchContract, Spec.Blake2.finalizeBScratchSig,
      Proof.Blake2.finalizeAArch64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi,
      AArch64.argRegs]
      [finalizeSat] using VG.Proof.Blake2.AArch64.Stream.finalizeSat 64)

/-! ## BLAKE2s -/

theorem initS_correct (st : State) (hs : (VG.Proof.Blake2.initAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.init s) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.initAArch64 s).post st s' :=
  WP.withPreservedV (Init.correct VG.Proof.Blake2.AArch64.Stream.okS hs) (by lit_decide)

theorem updateS_correct (st : State) (hs : (VG.Proof.Blake2.updateAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update s) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.updateAArch64 s).post st s' :=
  WP.withPreservedV (Update.correct VG.Proof.Blake2.AArch64.Stream.okS VG.Proof.Blake2.AArch64.Stream.calleeS hs) (by lit_decide)

theorem finalizeS_correct (st : State) (hs : (VG.Proof.Blake2.finalizeAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize s) st t s' ∧ abiPreserved st s' ∧
      (VG.Proof.Blake2.finalizeAArch64 s).post st s' :=
  WP.withPreservedV (Finalize.correct VG.Proof.Blake2.AArch64.Stream.okS VG.Proof.Blake2.AArch64.Stream.calleeS hs) (by lit_decide)

theorem initS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.init s)
      (Spec.Blake2.initSContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Blake2.AArch64.Stream.initS_correct VG.Proof.Blake2.AArch64.Stream.initS_ct (by
    contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs] [initSat]
      using VG.Proof.Blake2.AArch64.Stream.initSat 32)

theorem updateS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update s)
      (Spec.Blake2.updateSScratchContract AArch64.abi 16) :=
  Verified.of_correct VG.Proof.Blake2.AArch64.Stream.updateS_correct VG.Proof.Blake2.AArch64.Stream.updateS_ct (by
    sig_implies [Spec.Blake2.updateSScratchContract, Spec.Blake2.updateSScratchSig, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using VG.Proof.Blake2.AArch64.Stream.updateSat 32)

theorem finalizeS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize s)
      (Spec.Blake2.finalizeSScratchContract AArch64.abi 16) :=
  Verified.of_correct VG.Proof.Blake2.AArch64.Stream.finalizeS_correct VG.Proof.Blake2.AArch64.Stream.finalizeS_ct (by
    sig_implies [Spec.Blake2.finalizeSScratchContract, Spec.Blake2.finalizeSScratchSig,
      Proof.Blake2.finalizeAArch64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi,
      AArch64.argRegs]
      [finalizeSat] using VG.Proof.Blake2.AArch64.Stream.finalizeSat 32)

/-! ## `update` and `finalize` with their working space in a frame of their own

The theorems above are of the streaming functions with their working space
as an argument (`update_scratch`, `finalize_scratch`); `update` and
`finalize` run them in a frame that allocates it (`Verified.stackScratch`).
-/

theorem updateB_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 576 .x4 (Impl.Blake2.AArch64.Stream.update b))
    (Spec.Blake2.updateBContract AArch64.abi (16 + 576)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 576)
    VG.Proof.Blake2.AArch64.Stream.updateB_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalizeB_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 576 .x3 (Impl.Blake2.AArch64.Stream.finalize b))
    (Spec.Blake2.finalizeBContract AArch64.abi (16 + 576)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 576)
    VG.Proof.Blake2.AArch64.Stream.finalizeB_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem updateS_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 576 .x4 (Impl.Blake2.AArch64.Stream.update s))
    (Spec.Blake2.updateSContract AArch64.abi (16 + 576)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 576)
    VG.Proof.Blake2.AArch64.Stream.updateS_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalizeS_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 576 .x3 (Impl.Blake2.AArch64.Stream.finalize s))
    (Spec.Blake2.finalizeSContract AArch64.abi (16 + 576)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 576)
    VG.Proof.Blake2.AArch64.Stream.finalizeS_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blake2.AArch64.Stream

end
