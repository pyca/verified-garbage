module

import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.EntryBranch
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.TCB.Artifact

/-!
# HMAC over any streaming hash function on PPC64LE: the shared contracts

The generic proofs (`Init.correct`, `Finalize.correct`, `InitLong.correct`)
are written against `initG`, `finG` and `longG`, with the working space the
code uses; with each hash function's constant time (checked for its code)
they are widened to the working space of the shared contracts of
`Spec/Hmac/Generic.lean` (`Verified.widen`) and moved to those contracts
(`generic_implies`), for any instance `I` of the hash function.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Shared

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- The initial taint of `init`, `initLong` and `finalize`: only the
arguments are public. -/
theorem agree {s₁ s₂ : State}
    (h : s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p3, p4, p5, p6, p7, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

variable {H : Hash} (hH : HashOK H) {I : Spec.Hmac.Instance} (hSH : hH.SH = I.S)

/-! ## `init` and `finalize` with their working space as an argument -/

theorem initImp (hs : ∃ s, (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96).pre s) :
    (initG I.S (8 * I.scratch) 96).Implies (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96) := by
  generic_implies [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract,
    Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, initG, PPC64LE.abi,
    PPC64LE.argRegs] using hs

theorem finImp (hs : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96).pre s) :
    (finG I.S (8 * I.scratch) 96).Implies (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96) := by
  generic_implies [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, finG, PPC64LE.abi, PPC64LE.argRegs] using hs

include hSH in
/-- `init` with its working space in `scratch`, against the shared contract,
given its constant time. -/
theorem initScratch (hfit : H.W + 48 ≤ 8 * I.scratch)
    (ct : ConstantTime isa (initG hH.SH (H.W + 48) 96).pre (initG hH.SH (H.W + 48) 96).pub H.init)
    (hs : ∃ s, (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96).pre s) :
    Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96) := by
  have imp := initImp hs
  rw [← hSH] at imp
  have wide : ∀ s, (initG hH.SH (8 * I.scratch) 96).pre s →
      (initG hH.SH (H.W + 48) 96).pre (s.withRegions s.rd [⟨s.gpr .r3, hH.SH.stateBytes⟩,
        ⟨s.gpr .r4, hH.SH.stateBytes⟩, ⟨s.gpr .r7, H.W + 48⟩]) := by
    intro s ⟨h0, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    exact ⟨h0, h1, rfl, h3, h4.sub_right (Region.sub_prefix hfit), h5.sub_right (Region.sub_prefix hfit),
      h6, h7, h8.sub_right (Region.sub_prefix hfit), h9, h10, h11, h12, h13.sub_right (Region.sub_prefix hfit)⟩
  have v : Verified PPC64LE.target H.init (initG hH.SH (H.W + 48) 96) :=
    ⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := Init.correct hH hs; exact ⟨t, s', he, h₁, h₂⟩, ct,
      imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .r3, hH.SH.stateBytes⟩, ⟨s.gpr .r4, hH.SH.stateBytes⟩,
      ⟨s.gpr .r7, H.W + 48⟩]) wide (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
      imp.sat_left).of_implies imp
  obtain ⟨_, _, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil))

include hSH in
/-- `finalize` with its working space in `scratch`, against the shared
contract, given its constant time. -/
theorem finalizeScratch (hfit : H.W + 48 + H.FD ≤ 8 * I.scratch)
    (ct : ConstantTime isa (finG hH.SH (H.W + 48 + H.FD) 96).pre (finG hH.SH (H.W + 48 + H.FD) 96).pub
      H.finalize)
    (hs : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96).pre s) :
    Verified PPC64LE.target H.finalize (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96) := by
  have imp := finImp hs
  rw [← hSH] at imp
  have wide : ∀ s, (finG hH.SH (8 * I.scratch) 96).pre s →
      (finG hH.SH (H.W + 48 + H.FD) 96).pre (s.withRegions s.rd [⟨s.gpr .r3, hH.SH.stateBytes⟩,
        ⟨s.gpr .r6, hH.SH.digestBytes⟩, ⟨s.gpr .r7, H.W + 48 + H.FD⟩]) := by
    intro s ⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    exact ⟨h1, rfl, h3, h4, h5.sub_right (Region.sub_prefix hfit), h6, h7.sub_right (Region.sub_prefix hfit),
      h8.sub_right (Region.sub_prefix hfit), h9, h10, h11, h12, h13.sub_right (Region.sub_prefix hfit)⟩
  have v : Verified PPC64LE.target H.finalize (finG hH.SH (H.W + 48 + H.FD) 96) :=
    ⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := Finalize.correct hH hs; exact ⟨t, s', he, h₁, h₂⟩, ct,
      imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .r3, hH.SH.stateBytes⟩, ⟨s.gpr .r6, hH.SH.digestBytes⟩,
      ⟨s.gpr .r7, H.W + 48 + H.FD⟩]) wide (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
      imp.sat_left).of_implies imp
  obtain ⟨_, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil))

/-! ## `init` for a key longer than a block -/

/-- A key longer than a block. -/
def longPre (S : Spec.Hmac.StreamingHash) (pb : Nat) : Curry ((Spec.Hmac.initSig S).words pb) (Mem → Prop) :=
  fun _inner _outer _key keyLen _ => S.H.blockSize < keyLen.toNat

theorem longPre_local (S : Spec.Hmac.StreamingHash) (pb : Nat) : ∀ vs m₁ m₂,
    vs.length = ((Spec.Hmac.initSig S).words pb).length →
    (∀ b ∈ Sig.bufs (Spec.Hmac.initSig S).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((Spec.Hmac.initSig S).words pb) (longPre S pb) vs m₁ →
      Curry.apply ((Spec.Hmac.initSig S).words pb) (longPre S pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- `initLong`'s contract, with its working space passed in `scratch` (`n`
doublewords). -/
def longScratchContract (S : Spec.Hmac.StreamingHash) (n : Nat) : Contract PPC64LE.isa :=
  (Proof.Hmac.initScratchSig S n).contract PPC64LE.abi
    (pre := fun inner outer key keyLen _scratch => longPre S PPC64LE.abi.ptrBits inner outer key keyLen)
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S PPC64LE.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 144)

/-- `initLong` in a frame of `bytes` bytes of its own: a key longer than a
block. -/
def longContract (S : Spec.Hmac.StreamingHash) (bytes : Nat) : Contract PPC64LE.isa :=
  (Spec.Hmac.initSig S).contract PPC64LE.abi (pre := longPre S PPC64LE.abi.ptrBits)
    (post := Spec.Hmac.initPost S PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 144 + bytes)

theorem longImp (S : Spec.Hmac.StreamingHash) (n : Nat) (hs : ∃ s, (longScratchContract S n).pre s) :
    (longG S (8 * n) 144).Implies (longScratchContract S n) := by
  generic_implies [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, longG, initG,
    PPC64LE.abi, PPC64LE.argRegs] using hs

/-- `initLong` with its working space in `scratch` (`n` doublewords, all of
it), given its constant time. -/
theorem longScratch {n : Nat} (hn : 8 * n = H.lbytes)
    (ct : ConstantTime isa (longG hH.SH H.lbytes 144).pre (longG hH.SH H.lbytes 144).pub H.initLong)
    (hs : ∃ s, (longScratchContract hH.SH n).pre s) :
    Verified PPC64LE.target H.initLong (longScratchContract hH.SH n) := by
  have imp := longImp hH.SH n hs
  rw [hn] at imp
  have v : Verified PPC64LE.target H.initLong (longG hH.SH H.lbytes 144) :=
    ⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := InitLong.correct hH hs; exact ⟨t, s', he, h₁, h₂⟩, ct,
      imp.sat_left⟩
  exact v.of_implies imp

/-! ## The functions with their working space in a frame of their own -/

/-- `init` with its working space in a frame of `bytes` bytes. -/
theorem initFrame {bytes : Nat} (h : Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96))
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ I.scratch * 8 + 32 ≤ bytes)
    (hsat : ∃ s, (I.initContract PPC64LE.abi (96 + bytes)).pre s) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch bytes .r7 H.init)
      (I.initContract PPC64LE.abi (96 + bytes)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S PPC64LE.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S PPC64LE.abi.ptrBits) (wa := true) (stack := 96) (bytes := bytes) h
    (by exact (by decide : 4 < 8)) hb (Proof.Hmac.initPre_local _ _) (Proof.Hmac.initPost_local _ _) hsat rfl

/-- `finalize` with its working space in a frame of `bytes` bytes. -/
theorem finalizeFrame {bytes : Nat}
    (h : Verified PPC64LE.target H.finalize (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96))
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ I.scratch * 8 + 32 ≤ bytes)
    (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (I.finalizeContract PPC64LE.abi (96 + bytes)).pre s) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch bytes .r7 H.finalize)
      (I.finalizeContract PPC64LE.abi (96 + bytes)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S PPC64LE.abi.ptrBits) (wa := true) (stack := 96)
    (bytes := bytes) h (by exact (by decide : 4 < 8)) hb
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Hmac.finalizePost_local _ _ hR hS) hsat rfl

/-- `initLong` in a frame of `bytes` bytes of its own, the first `n`
doublewords of which (its working space) it zeroes before returning. -/
theorem longFrame {n bytes : Nat} (h : Verified PPC64LE.target H.initLong (longScratchContract I.S n))
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * 8 + 32 ≤ bytes)
    (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (longContract I.S bytes).pre s) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped bytes .r7 n H.initLong)
      (longContract I.S bytes) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64) (n := n)
    (pre := longPre I.S PPC64LE.abi.ptrBits) (post := Spec.Hmac.initPost I.S PPC64LE.abi.ptrBits) (wa := true)
    (stack := 144) (bytes := bytes) (words := n) h (by exact (by decide : 4 < 8)) hb
    (by simp only [Elem.size]; omega) (longPre_local _ _) (Proof.Hmac.initPost_local _ _)
    (Proof.Hmac.initPostOut_local _ _ hR hS) hsat rfl

/-! ## `init` for a key of any length, choosing on entry -/

/-- What `entryCmp` leaves of a state: all but `r11` and `r12`. -/
structure Ran (s u : State) : Prop where
  g : ∀ r, r ≠ .r11 → r ≠ .r12 → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  lr : u.lr = s.lr
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

/-- `(x >>> (b + 1)) + ((x &&& (2 B - 1)) + B - 1) >>> (b + 1)`, with
`B = 2 ^ b`, is nonzero exactly when `x` is more than `B`. -/
theorem cmp_ne {b : Nat} (hb : b = 6 ∨ b = 7) (x : BitVec 64) :
    ((x >>> (b + 1)) + ((x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)) + BitVec.ofNat 64 (2 ^ b - 1)) >>> (b + 1)
      != 0) = decide (2 ^ b < x.toNat) := by
  have hx := x.isLt
  have ha : (x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)).toNat = x.toNat % 2 ^ (b + 1) := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hb with rfl | rfl <;> decide),
      Nat.and_two_pow_sub_one_eq_mod]
  have hb' : ((x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)) + BitVec.ofNat 64 (2 ^ b - 1)).toNat =
      x.toNat % 2 ^ (b + 1) + (2 ^ b - 1) := by
    rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ b - 1)
      (by rcases hb with rfl | rfl <;> decide)]
    rcases hb with rfl | rfl <;> omega
  have hv : ((x >>> (b + 1)) + ((x &&& BitVec.ofNat 64 (2 ^ (b + 1) - 1)) + BitVec.ofNat 64 (2 ^ b - 1)) >>>
      (b + 1)).toNat = x.toNat / 2 ^ (b + 1) + (x.toNat % 2 ^ (b + 1) + (2 ^ b - 1)) / 2 ^ (b + 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, hb', Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    rcases hb with rfl | rfl <;> omega
  by_cases h : 2 ^ b < x.toNat
  · rw [decide_eq_true h]
    simp only [bne_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [hv] at this
    simp at this
    rcases hb with rfl | rfl <;> omega
  · rw [decide_eq_false h]
    simp only [bne_eq_false_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hv]
    simp
    rcases hb with rfl | rfl <;> omega

theorem entry_run {b : Nat} (hb : b = 6 ∨ b = 7) (s : State) :
    ∃ u, execBlock isa (Hash.entryCmp b) s = some (u, []) ∧ Ran s u ∧
      eval (.nonzero .d .r12) u = some (decide (2 ^ b < (s.gpr .r6).toNat)) := by
  rcases hb with rfl | rfl <;>
  · refine ⟨_, rfl, ⟨fun r h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · simp [State.write, h11, h12]
    · simp only [eval, State.read, State.write, Size.ext, reduceCtorEq, ↓reduceIte, Option.some.injEq]
      exact cmp_ne (by decide) _

/-- `init` for a key of any length: `initLong` in its frame (`long`) for a
key longer than a block, `init` in its frame (`short`) otherwise, with the
same stack. -/
theorem initAny {b : Nat} (hb : b = 6 ∨ b = 7) (hbB : I.S.H.blockSize = 2 ^ b) {short long : Prog isa}
    {Fl Fs : Nat} (hst : 144 + Fl = 96 + Fs)
    (hshort : Verified PPC64LE.target short (I.initContract PPC64LE.abi (96 + Fs)))
    (hlong : Verified PPC64LE.target long (longContract I.S Fl))
    (hsat : ∃ s, (I.initAnyKeyContract PPC64LE.abi (96 + Fs)).pre s) :
    Verified PPC64LE.target (Hash.initEntry b short long) (I.initAnyKeyContract PPC64LE.abi (96 + Fs)) := by
  have hp : ∀ r ∈ preserved, r ≠ .r11 ∧ r ≠ .r12 := by decide
  rw [show 96 + Fs = 144 + Fl by omega] at hshort hsat ⊢
  refine Verified.entryBranch (p := fun s => decide (2 ^ b < (s.gpr .r6).toNat))
    (fun _ => []) hlong hshort (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, r, ev⟩ := entry_run hb s
    have g3 := r.g .r3 (by decide) (by decide)
    have g4 := r.g .r4 (by decide) (by decide)
    have g5 := r.g .r5 (by decide) (by decide)
    have g6 := r.g .r6 (by decide) (by decide)
    have abi : ∀ s', PPC64LE.target.abiPreserved u s' → PPC64LE.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by
        obtain ⟨h11, h12⟩ := hp x hx
        rw [a.1 x hx, r.g x h11 h12], by rw [a.2.1, r.sp], by rw [a.2.2, r.lr]⟩
    refine ⟨u, e, ev, fun hl => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hl => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · have hk : 2 ^ b < (s.gpr .r6).toNat := of_decide_eq_true hl
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hs
      sig_pre [longContract, longPre, Spec.Hmac.initSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [g3, g4, g5, g6, r.sp, r.rd, r.wr, hbB]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hs
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      sig_post [longContract, longPre, Spec.Hmac.initSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
    · have hk : (s.gpr .r6).toNat ≤ 2 ^ b := by have := of_decide_eq_false hl; omega
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hs
      sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [g3, g4, g5, g6, r.sp, r.rd, r.wr, hbB]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hs
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, r, -⟩ := entry_run hb s
    obtain ⟨u₀', e₀', r', -⟩ := entry_run hb s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hq'
    obtain ⟨qsp, q3, q4, q5, q6⟩ := hq'
    have e3 := r.g .r3 (by decide) (by decide)
    have e4 := r.g .r4 (by decide) (by decide)
    have e5 := r.g .r5 (by decide) (by decide)
    have e6 := r.g .r6 (by decide) (by decide)
    have e3' := r'.g .r3 (by decide) (by decide)
    have e4' := r'.g .r4 (by decide) (by decide)
    have e5' := r'.g .r5 (by decide) (by decide)
    have e6' := r'.g .r6 (by decide) (by decide)
    refine ⟨rfl, by rw [q6], fun _ => ?_, fun _ => ?_⟩
    · sig_pub [longContract, longPre, Spec.Hmac.initSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6']
      exact ⟨qsp, q3, q4, q5, q6⟩
    · sig_pub [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6']
      exact ⟨qsp, q3, q4, q5, q6⟩

end VG.Proof.Hmac.Stream.PPC64LE.Shared
