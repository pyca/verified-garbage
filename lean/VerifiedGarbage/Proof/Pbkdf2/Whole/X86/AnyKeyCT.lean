module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Md5.X86.Lit
public import VerifiedGarbage.Proof.Sha512.X86.Lit

/-! ### `Pbkdf2.Whole.X86.AnyKey`, which only this module used -/

section

/-!
# HMAC's `init` for a key of any length on x86 (32-bit): correct

`initAny` (`Impl/Pbkdf2/Md/AnyKey/X86.lean`) saves our caller's registers in
`scratch` (`prologue_ok`), makes the key as `pbkdf2` makes it from a password
(`key_ok`: the key, or its digest, hashed into `scratch` with the streaming
functions, if it is longer than a block), calls HMAC's `init` with it
(`call_ok`, through its shared contract), and loads our caller's registers
back. Each step is `pbkdf2`'s (`Key.lean`, `Setup.lean`), for this function's
arguments, every one on the stack (cdecl): `inner`, `outer`, `key`,
`key_len`, `scratch`. `anyN` is the contract the proof is written against.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Any

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK Sizes layout end_le L8_le stk After hi5 HiArgs hi_frame below_eq
  toNat_ofNat32 save_ok blockKey_hash hash_len)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK SavedRegs saveR InitArgs UpdArgs FinArgs init_frame upd_frame fin_frame
  zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_cmpi)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash blockKey xorPad ipad opad)

/-! ## The contract -/

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length, with
`8 W` bytes of scratch space and 76 bytes of stack below the return address,
its arguments readable: `VG.Spec.Hmac.initAnyKeyContract` with its working
space as an argument, with the arguments apart from the writable regions, as
the taint analysis needs them (`AnyKeyCT.lean` moves it to the shared
contract). -/
def anyN (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint key ∧ inner.Disjoint scratch ∧ inner.Disjoint args ∧
    outer.Disjoint key ∧ outer.Disjoint scratch ∧ outer.Disjoint args ∧ key.Disjoint scratch ∧
    scratch.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint key ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + W * 8 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    S.Repr s'.mem ((arg s 0).setWidth 64) (xorPad k0 ipad) ∧ S.Repr s'.mem ((arg s 1).setWidth 64) (xorPad k0 opad)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev out : BitVec 32 := arg s₀ 1
abbrev key : BitVec 32 := arg s₀ 2
abbrev kln : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev keyR : Region := ⟨(key s₀).setWidth 64, kln s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 76
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨(scr s₀).setWidth 64, k⟩

end

section
variable (F) (s₀ : State)
abbrev innR : Region := ⟨(inn s₀).setWidth 64, F.H.S⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, F.H.S⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, F.L8⟩
/-- The save area of our caller's registers. -/
abbrev svR : Region := saveR F.L (scr s₀)
/-- The regions everything writes: the states, `scratch` and the stack below `esp`. -/
abbrev wrs : List Region := [innR F s₀, outR F s₀, scR F s₀, stkR s₀]
end

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp76 : 76 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [innR F s₀, outR F s₀, scR F s₀]
  i_o : (innR F s₀).Disjoint (outR F s₀)
  i_k : (innR F s₀).Disjoint (keyR s₀)
  i_s : (innR F s₀).Disjoint (scR F s₀)
  i_a : (innR F s₀).Disjoint (argR s₀)
  o_k : (outR F s₀).Disjoint (keyR s₀)
  o_s : (outR F s₀).Disjoint (scR F s₀)
  o_a : (outR F s₀).Disjoint (argR s₀)
  k_s : (keyR s₀).Disjoint (scR F s₀)
  s_a : (scR F s₀).Disjoint (argR s₀)
  r_i : (retR s₀).Disjoint (innR F s₀)
  r_o : (retR s₀).Disjoint (outR F s₀)
  r_k : (retR s₀).Disjoint (keyR s₀)
  r_s : (retR s₀).Disjoint (scR F s₀)
  r_a : (retR s₀).Disjoint (argR s₀)
  b_i : (stkR s₀).Disjoint (innR F s₀)
  b_o : (stkR s₀).Disjoint (outR F s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (scR F s₀)
  b_a : (stkR s₀).Disjoint (argR s₀)
  ni : (inn s₀).toNat + F.H.S ≤ 2 ^ 32
  no : (out s₀).toNat + F.H.S ≤ 2 ^ 32
  nk : (key s₀).toNat + kln s₀ ≤ 2 ^ 32
  nsc : (scr s₀).toNat + F.L8 ≤ 2 ^ 32

theorem pre_of (hF : FnsOK F) {s₀ : State} (h : (anyN hF.hH.SH (F.W + F.H.S)).pre s₀) : Pre F s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  have hS := hF.hH.hS
  have e : (⟨(s₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩ : Region) = stkR s₀ := by
    rw [stkR, below_eq h0]
  rw [e] at h18 h19 h20 h21 h22
  simp only [hS] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

/-! ## The parts of `scratch` -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : (dO s₀ o).setWidth 64 = A s₀ o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.setWidth_add (by omega_using [ho, this])

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.toNat_add_ofNat (by omega_using [ho, this])

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (sR s₀ o n) (scR F s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.disjoint _ h (by omega_using [ha, this]) (by omega_using [hb, this])

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.base_disjoint _ hk (by omega_using [hbn, this])

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (lowR s₀ k) (scR F s₀) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR F s₀) (scR F s₀) := by
  have := end_le hz; have := layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 16 ≤ F.L8; omega_arith)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8) : (svR F s₀).Disjoint (sR s₀ o n) := by
  have := L8_le hz
  exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega_using [ho])) (by simp only [Fns.L]; omega_using [ho, hon, this]) (by omega_using [hon, this])

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (svR F s₀).Disjoint (lowR s₀ k) := by
  have := L8_le hz; have := end_le hz; have := layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 16) (by simp only [Fns.L]; omega_using [hk])
    (by simp only [Fns.L]; omega_arith)).symm

omit hz in
theorem sc_mem : scR F s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  saved : SavedRegs F.L (scr s₀) s₀ s.mem
  frame : Frame (wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

theorem KR.stkE {s₀ s : State} (h : KR F s₀ s) : stk s = stkR s₀ := by
  rw [stk, h.esp]

/-- `KR` survives changes to other registers, and to memory in the states,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F s₀, Region.Sub r r') :
    KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- What a call leaves, writing the states, parts of `scratch` after the
save area, or the working space, and the stack below `esp`. -/
theorem KR.call {s₀ s s' : State} (hp : Pre F s₀) (hz : Sizes F) (h : KR F s₀ s) {ws : List Region}
    (ha : After s ws s')
    (hw : ∀ r ∈ ws, r = innR F s₀ ∨ r = outR F s₀ ∨ (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = sR s₀ o n ∧ 8 * F.W + 16 ≤ o ∧ o + n ≤ F.L8) : KR F s₀ s' := by
  have hL := end_le hz; have := layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact (hp.i_s.sub_right (sv_sub hz)).symm
      · exact (hp.o_s.sub_right (sv_sub hz)).symm
      · exact sv_low hz hk
      · exact sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scR F s₀, by simp, low_sub (F := F) (by omega_using [hL, this, hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

/-! ## The arguments, the return address and the key, while `KR` holds -/

section
variable {s₀ : State} (hp : Pre F s₀)
include hp

omit hp in
theorem argR_eq : argR s₀ = ⟨addr (E s₀) 4, 20⟩ := rfl

theorem KR.argEq {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 5) : arg s i = arg s₀ i := by
  have hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨addr (E s₀) 4, 20⟩ r := by
    rw [← argR_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_a.symm
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.b_a.symm
  exact Pbkdf2.Stream.X86.arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega) hk.frame hd (by omega_using [hi])

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [show s.ea (at_ .esp (4 + 4 * i)) = addr (s.gpr .esp) (4 + 4 * i) from rfl, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.wr]
  exact ⟨argR s₀, by simp, by
    rw [argR_eq]; exact Pbkdf2.Stream.X86.arg_contains rfl (by omega_using [hi]) (by have := hp.spf; omega)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := hk.argEq hp hi
  simp only [arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by
    rw [Pbkdf2.Stream.X86.argAddr_eq, Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

/-- `mov d, [esp + 4 + 4 i]`: argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : KR F s₀ s) {d : Reg} {i : Nat} (hi : i < 5) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (Fns.argM i) :: is)) s Q :=
  wp_movm (a := argAddr s₀ i) (argW hk.esp i) (argIn hp hk.rd hk.wr hi)
    fun s' u => k s' (by rw [hk.readArg hp hi] at u; exact u)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : KR F s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_o
    · exact hp.r_s
    · rw [stkR, below_eq hp.sp76]
      exact (Offset.below_disjoint _ (by omega_using [])).symm) (by decide)

theorem KR.keyBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem ((key s₀).setWidth 64) (kln s₀) = bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀) :=
  bytes_keep hk.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.i_k.symm
    · exact hp.o_k.symm
    · exact hp.k_s
    · exact hp.b_k.symm) (by have := hp.nk; omega_using [this])

end

/-- `d ← scratch + o`, while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : KR F s₀ s) {d : Reg} {o : Nat} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ =>
    k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, hk.ebp]

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## The prologue -/

theorem prologue_ok : WP isa (.block F.anyPrologue) s₀ (KR F s₀) := by
  have hL := end_le hz; have := layout (F := F)
  have hsc := sc_mem hp
  simp only [Fns.anyPrologue, List.cons_append]
  refine wp_movm (a := argAddr s₀ 4) (argW rfl 4) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok F.L (sc := scr s₀) (L := F.L8) u₁.gpr (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 16 ≤ F.L8; omega_arith) hp.nsc fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  refine wp_mov fun s₃ u₃ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨by rw [u₃.rd, rd₂, u₁.rd], by rw [u₃.wr, wr₂, u₁.wr], by rw [u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₃.gpr, g₂, u₁.gpr]; rfl, ?_, ?_⟩
  · rw [u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [Pbkdf2.Stream.X86.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)
  · rw [u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR F s₀, by simp, sv_sub hz⟩

/-! ## The stack and `scratch`, while `KR` holds -/

omit hz in
theorem stk48_sub {s : State} (hk : KR F s₀ s) : Region.Sub (Pbkdf2.Stream.X86.stk s) (stkR s₀) := by
  rw [Pbkdf2.Stream.X86.stk, hk.esp]; exact below_sub (by decide) hp.sp76

omit hz in
theorem b76 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR F s₀)) :
    (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b48 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR F s₀)) :
    (Pbkdf2.Stream.X86.stk s).Disjoint R :=
  (hp.b_s.sub_left (stk48_sub hp hk)).sub_right hR

omit hz in
theorem cov_part {s : State} (hk : KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR F s₀, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR F s₀, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_key {s : State} (hk : KR F s₀ s) : Covers [keyR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a key longer than a block -/

variable (hH : HashOK F.H)
include hH

omit hp hz hH in
/-- `edi ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO)) s fun t =>
      KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO)]
  exact scr_ok hk fun s₁ u₁ => WP.block_nil ⟨hk.upd (by decide) u₁, u₁.gpr, u₁.mem⟩

omit hH in
theorem hk2_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    InitArgs (H := F.H) s .edi (dO s₀ F.stWO) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  refine ⟨hdi, by decide, by rw [hk.esp]; have := hp.sp76; omega_arith, ?_, ?_, ?_⟩
  · rw [ea]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk (hz.stWO_S)
  · rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
  · rw [dO_toNat hp (hz.stWO_lt)]; have := hp.nsc; omega_arith

theorem hk2_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (F.H.callInit .edi) s fun t => KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  refine init_frame hH (hk2_args hp hz hk hdi) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, by rw [← ea]; exact r, a.cs _ (by decide)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact .inr (.inr (.inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩))

omit hz hH in
/-- `update`'s arguments: the key. -/
theorem hk3_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block Fns.anyHk3) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .esi = 0 ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 3 ∧ t.gpr .edx = key s₀ ∧ t.mem = s.mem := by
  simp only [Fns.anyHk3]
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  refine wp_arg hp k₂ (by decide) fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨k₃.upd (by decide) u₄, ?_, ?_, ?_, ?_, u₄.gpr, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr]

theorem hk4_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3) (hdx : s.gpr .edx = key s₀) :
    UpdArgs hH s .esi .edi (dO s₀ F.stWO) (key s₀) (scr s₀) 0 (kln s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 3).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega_arith
      cd := cov_key hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_low hp hk (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega_arith) (hz.stWO_S)).symm
      d_st := by rw [ea]; exact hp.k_s.sub_right (part_sub (hz.stWO_S))
      d_sc := hp.k_s.sub_right (low_sub (by omega_arith))
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
      b_d := hp.b_k.sub_left (stk48_sub hp hk)
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (hz.stWO_lt)]; have := hp.nsc; omega_arith
      nd := hp.nk
      nsc := by have := hp.nsc; omega_arith }

theorem hk4_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3) (hdx : s.gpr .edx = key s₀)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) []) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) (bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀)) ∧
        t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  refine upd_frame hH (hk4_args hp hz hH hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, a.cs _ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (.inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩))
    · exact .inr (.inr (.inl ⟨_, rfl, by omega_arith⟩))
  · have := r [] (by rw [ea]; exact hr) rfl
    rwa [List.nil_append, ea, hk.keyBytes hp] at this

omit hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block F.anyHk5) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .eax = arg s₀ 3 ∧ t.gpr .ecx = 0 ∧
        t.gpr .edx = dO s₀ F.hkO ∧ t.mem = s.mem := by
  simp only [Fns.anyHk5, List.cons_append, List.nil_append]
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO)]
  refine scr_ok k₂ fun s₃ u₃ => WP.block_nil ⟨k₂.upd (by decide) u₃, ?_, ?_, ?_, u₃.gpr, by
    rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem hk6_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = arg s₀ 3)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO) :
    FinArgs hH s .edi (dO s₀ F.stWO) (dO s₀ F.hkO) (scr s₀) (arg s₀ 3) 0 := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have eh := dO_addr hp (o := F.hkO) (hz.hkO_lt)
  exact
    { hst := hdi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      sp48 := by rw [hk.esp]; have := hp.sp76; omega_arith
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_part hp hk (hz.hkO_F)
          · exact cov_low hp hk (by omega_arith)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by omega_arith)) (hz.stWO_S) (hz.hkO_F)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega_arith) (hz.stWO_S)).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega_arith) (hz.hkO_F)).symm
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
      b_o := by rw [eh]; exact b48 hp hk (part_sub (hz.hkO_F))
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (hz.stWO_lt)]; have := hp.nsc; omega_arith
      no := by rw [dO_toNat hp (hz.hkO_lt)]; have := hp.nsc; omega_arith
      nsc := by have := hp.nsc; omega_arith }

theorem hk6_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = arg s₀ 3)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) (bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀))) :
    WP isa (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5)) s
      fun t => KR F s₀ t ∧
        bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have eh := dO_addr hp (o := F.hkO) (hz.hkO_lt)
  refine fin_frame hH (hk6_args hp hz hH hk hdi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (.inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩))
    · exact .inr (.inr (.inr ⟨_, _, by rw [eh], by omega_arith, by omega_arith⟩))
    · exact .inr (.inr (.inl ⟨_, rfl, by omega_arith⟩))
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (arg s₀ 3).isLt (by decide))
      (by rw [bytesAt_length, ← zero_append_ofNat (arg s₀ 3).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp hz hH in
theorem hk7_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil ⟨(hk.upd (by decide) u₁).upd (by decide) u₂,
    by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr, by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : KR F s₀ s) :
    WP isa F.anyHashKey s fun t => KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀)) := by
  unfold Fns.anyHashKey
  refine WP.seq (WP.mono (hk1_ok hk) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  have d₂ : s₂.gpr .edi = dO s₀ F.stWO := e₂.trans d₁
  refine WP.seq (WP.mono (hk3_ok hp k₂ d₂) fun s₃ ⟨k₃, d₃, i₃, a₃, c₃, x₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ d₃ i₃ a₃ c₃ x₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, r₄, e₄⟩ => ?_)
  have d₄ : s₄.gpr .edi = dO s₀ F.stWO := e₄.trans d₃
  refine WP.seq (WP.mono (hk5_ok hp k₄ d₄) fun s₅ ⟨k₅, d₅, a₅, c₅, x₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ d₅ a₅ c₅ x₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

/-! ## The key -/

omit hH in
theorem cmp_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block F.anyCmp) s fun t => KR F s₀ t ∧ t.gpr .ecx = arg s₀ 3 ∧
      t.cf = some (decide (kln s₀ < F.H.B + 1)) ∧ t.mem = s.mem := by
  have := hz.B
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
  refine ⟨(hk.upd (by decide) u₁).same f₂.rd f₂.wr (fun r _ => by rw [f₂.gpr]) f₂.mem, by rw [f₂.gpr, u₁.gpr], ?_,
    by rw [f₂.mem, u₁.mem]⟩
  rw [c₂, u₁.gpr, toNat_ofNat32 (by omega_arith)]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if kln s₀ < F.H.B + 1 then key s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if kln s₀ < F.H.B + 1 then kln s₀ else F.H.D

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hH : HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : KR F s₀ s) :
    WP isa F.anyKey s fun t => KR F s₀ t ∧ t.gpr .edx = kp F s₀ ∧ t.gpr .ecx = BitVec.ofNat 32 (kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem ((kp F s₀).setWidth 64) (kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀)) := by
  unfold Fns.anyKey
  refine WP.seq (WP.mono (cmp_ok hp hz hk) fun s₁ ⟨k₁, c₁, f₁, _⟩ => ?_)
  refine WP.ite (decide (F.H.B + 1 ≤ kln s₀)) (by
    show (s₁.cf.map (!·)) = _
    rw [f₁]; simp only [Option.map_some, ← decide_not, Nat.not_lt])
    (fun hT => ?_) fun hF => ?_
  · have hlt : ¬ kln s₀ < F.H.B + 1 := by have := of_decide_eq_true hT; omega_arith
    simp only [kp, kl, hlt, ↓reduceIte]
    refine WP.mono (hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D
    rw [show (dO s₀ F.hkO).setWidth 64 = A s₀ F.hkO from dO_addr hp (hz.hkO_lt),
      b, blockKey_hash hz hH (by rw [bytesAt_length]; omega_arith) (hash_len hH b)]
  · have hlt : kln s₀ < F.H.B + 1 := by have := of_decide_eq_false hF; omega_arith
    simp only [kp, kl, hlt, ↓reduceIte]
    refine wp_arg hp k₁ (by decide) fun s₂ u₂ => WP.block_nil ⟨k₁.upd (by decide) u₂, u₂.gpr, ?_, ?_⟩
    · rw [u₂.other _ (by decide), c₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [u₂.mem, k₁.keyBytes hp]

end

/-! ## Where the key is -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- The key's region is the key, or its digest in `scratch`. -/
theorem key_cases : (kp F s₀ = key s₀ ∧ kl F s₀ = kln s₀ ∧ kln s₀ ≤ F.H.B) ∨
    ((kp F s₀).setWidth 64 = A s₀ F.hkO ∧ kl F s₀ = F.H.D) := by
  by_cases h : kln s₀ < F.H.B + 1
  · exact .inl ⟨by simp [kp, h], by simp [kl, h], by omega_arith⟩
  · refine .inr ⟨?_, by simp [kl, h]⟩
    simp only [kp, h, ↓reduceIte]
    exact dO_addr hp (hz.hkO_lt)

theorem kl_le : kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega_arith

theorem key_toNat : (kp F s₀).toNat + kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : kln s₀ < F.H.B + 1
  · simp only [kp, kl, h, ↓reduceIte]; exact hp.nk
  · simp only [kp, kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp (hz.hkO_lt)]
    have := hp.nsc; omega_arith

/-- The key is apart from the states, from the working space, and from the
stack below `esp`. -/
theorem key_disj {R : Region} (hR : Region.Sub R (scR F s₀))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ R := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.k_s.sub_right hR
  · rw [h, h']; exact hd.symm

theorem key_inn : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (innR F s₀) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.i_k.symm
  · rw [h, h']; exact (hp.i_s.sub_right (part_sub (hz.hkO_D))).symm

theorem key_out : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (outR F s₀) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.o_k.symm
  · rw [h, h']; exact (hp.o_s.sub_right (part_sub (hz.hkO_D))).symm

theorem key_stk {s : State} (hk : KR F s₀ s) : (stk s).Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ := by
  rw [hk.stkE]
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_k
  · rw [h, h']; exact hp.b_s.sub_right (part_sub (hz.hkO_D))

theorem key_cov {s : State} (hk : KR F s₀ s) : Covers [⟨(kp F s₀).setWidth 64, kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact cov_key hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.hkO) (n := F.H.D) (hz.hkO_D)
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

/-! ## HMAC's `init` -/

/-- `K₀`, the key padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀))

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  edx : s.gpr .edx = kp F s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem ((kp F s₀).setWidth 64) (kl F s₀)) = K0 hF s₀

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : KR F s₀ s) : WP isa F.anyKey s (Keyed hF s₀) :=
  WP.mono (key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hz in
theorem args_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa (.block Fns.anyArgs) s
      fun t => Keyed hF s₀ t ∧ t.gpr .edi = inn s₀ ∧ t.gpr .esi = out s₀ := by
  simp only [Fns.anyArgs]
  refine wp_arg hp h.kr (by decide) fun s₁ u₁ => ?_
  have k₁ := h.kr.upd (by decide) u₁
  refine wp_arg hp k₁ (by decide) fun s₂ u₂ => WP.block_nil ⟨⟨k₁.upd (by decide) u₂, ?_, ?_, ?_⟩, ?_, u₂.gpr⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₂.mem, u₁.mem]; exact h.k0
  · rw [u₂.other _ (by decide), u₁.gpr]

theorem call_args {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = inn s₀) (hsi : s.gpr .esi = out s₀) :
    HiArgs hF.hH.SH hF.Wi s (inn s₀) (out s₀) (kp F s₀) (scr s₀) (kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have hk := h.kr
  have kls : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    key_disj hp hz (low_sub (by omega_arith)) (low_disj hz (by omega_arith) (hz.hkO_D))
  exact
    { edi := hdi
      esi := hsi
      edx := h.edx
      ecx := h.ecx
      ebp := hk.ebp
      klB := by rw [hF.hH.hB]; exact kl_le hp hz
      kl32 := by have := kl_le hp hz; have := hz.B; omega_arith
      sp := by rw [hk.esp]; exact hp.sp76
      cr := key_cov hp hz hk
      cw := by
        rw [hS]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨innR F s₀, by rw [hk.wr, hp.wr]; simp, 0, by simp, by simp⟩
          · exact ⟨outR F s₀, by rw [hk.wr, hp.wr]; simp, 0, by simp, by simp⟩
          · exact cov_low hp hk (by omega_arith)
      i_o := by rw [hS]; exact hp.i_o
      i_k := by rw [hS]; exact (key_inn hp hz).symm
      i_s := by rw [hS]; exact hp.i_s.sub_right (low_sub (by omega_arith))
      o_k := by rw [hS]; exact (key_out hp hz).symm
      o_s := by rw [hS]; exact hp.o_s.sub_right (low_sub (by omega_arith))
      k_s := kls
      b_i := by rw [hS, hk.stkE]; exact hp.b_i
      b_o := by rw [hS, hk.stkE]; exact hp.b_o
      b_k := key_stk hp hz hk
      b_s := b76 hp hk (low_sub (by omega_arith))
      ni := by rw [hS]; exact hp.ni
      no := by rw [hS]; exact hp.no
      nk := key_toNat hp hz
      nsc := by have := hp.nsc; omega_arith }

theorem call_ok {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = inn s₀) (hsi : s.gpr .esi = out s₀) :
    WP isa (.frame (.push hi5) (.call F.hiN F.hiC) (.pop .eax hi5.length)) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem ((inn s₀).setWidth 64) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem ((out s₀).setWidth 64) (xorPad (K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  refine hi_frame hF.hi hF.hiSp hF.hiSU (call_args hp hz hF h hdi hsi) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (by rw [hS])
    · exact .inr (.inl (by rw [hS]))
    · exact .inr (.inr (.inl ⟨_, rfl, by omega_arith⟩))
  · rw [h.k0] at r0; exact r0
  · rw [h.k0] at r1; exact r1

/-! ## The function -/

theorem correct : WP isa F.hmacInitAny s₀ fun s' =>
    abiPreserved s₀ s' ∧ (anyN hF.hH.SH (F.W + F.H.S)).post s₀ s' := by
  unfold Fns.hmacInitAny
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (keyed_ok hp hz hF k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (args_ok hp hF h₂) fun s₃ ⟨h₃, d₃, i₃⟩ => ?_)
  refine WP.seq (WP.mono (call_ok hp hz hF h₃ d₃ i₃) fun s₄ ⟨k₄, r0, r1⟩ => ?_)
  have hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (Pbkdf2.Stream.X86.restore_ok F.L k₄.ebp k₄.saved (by rw [k₄.wr]; exact sc_mem hp)
    (show 8 * F.W + 16 ≤ F.L8 by have hz_fits := hz.fits; omega_arith) hp.nsc)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact k₄.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₄.esp]
    · exact hg r (Pbkdf2.Stream.X86.callee_saved r hr he)
  · show hF.hH.SH.Repr s'.mem ((inn s₀).setWidth 64) _ ∧ hF.hH.SH.Repr s'.mem ((out s₀).setWidth 64) _
    rw [hm]; exact ⟨r0, r1⟩

end

end VG.Proof.Pbkdf2.Whole.X86.Any

end

end


/-!
# HMAC's `init` for a key of any length on x86 (32-bit): constant time, and the shared contract

As for `pbkdf2` (`CT.lean`): the pieces of code between the calls are checked
by the taint analysis (`AnyChecks`, which the kernel evaluates for each hash
function), with the arguments, `esp` and `ebp` public (`piece`); the calls are
related by their contracts (`init_rel`, `upd_rel`, `fin_rel`, `hi_rel`), whose
public arguments are the same in two runs with the same public arguments
(`PubEq`). The only branch, whether the key is hashed, depends only on
`key_len`.

`anyG` (the arguments writable, as the shared contract has them) follows from
`anyN` (`Verified.narrowTo`), and implies `anyScratchContract`:
`VG.Spec.Hmac.initAnyKeyContract` with its working space as a last argument,
from which the function that allocates it in a frame of its own and wipes it
(`withStackScratchWiped`) is verified (`anyFramed`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Any

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK Sizes layout end_le hi_rel hash_len blockKey_hash shapeOf setWidth_inj32)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel upd_rel fin_rel)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash blockKey xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs (4 + 4 * 5)) c hc).isSome = true

/-- The taint checks of the pieces of `initAny` between its calls. -/
structure AnyChecks (F : Fns) : Prop where
  pro : Ck [] (.block F.anyPrologue)
  cmp : Ck [.ebp] (.block F.anyCmp)
  hk1 : Ck [.ebp] (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO))
  hk3 : Ck [.ebp] (.block Fns.anyHk3)
  hk5 : Ck [.ebp] (.block F.anyHk5)
  hk7 : Ck [.ebp]
    (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO ++ ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr)))
  short : Ck [.ebp] (.block Fns.anyShort)
  args : Ck [.ebp] (.block Fns.anyArgs)
  restore : Ck [.ebp] (.block F.L.restore)

/-- The checks depend only on the sizes of `F`. -/
theorem anyChecks_of_shape {F : Fns} (h : AnyChecks (shapeOf F)) : AnyChecks F :=
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.args, h.restore⟩

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : E s₀ = E s₀'
  args : ∀ i < 5, arg s₀ i = arg s₀' i

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 5) : arg s₀' i = arg s₀ i := (hq.args i hi).symm
theorem PubEq.E' : E s₀' = E s₀ := hq.esp.symm
theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a (by decide)
theorem PubEq.innEq : inn s₀' = inn s₀ := hq.a (by decide)
theorem PubEq.outEq : out s₀' = out s₀ := hq.a (by decide)
theorem PubEq.keyEq : key s₀' = key s₀ := hq.a (by decide)
theorem PubEq.klnEq : kln s₀' = kln s₀ := by show (arg s₀' 3).toNat = _; rw [hq.a (by decide)]
theorem PubEq.dOEq (o : Nat) : dO s₀' o = dO s₀ o := by show scr s₀' + _ = _; rw [hq.scrEq]
theorem PubEq.kpEq : kp F s₀' = kp F s₀ := by
  show (if kln s₀' < F.H.B + 1 then arg s₀' 2 else dO s₀' F.hkO) = _
  rw [hq.klnEq, hq.a (by decide), hq.dOEq]
theorem PubEq.klEq : kl F s₀' = kl F s₀ := by
  show (if kln s₀' < F.H.B + 1 then kln s₀' else F.H.D) = _
  rw [hq.klnEq]

end

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre F t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_i h.i_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_o h.o_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_s h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree_argTaint (hag s s' h h')
      (by rw [(hk h).esp, (hk h').esp, hq.esp])
      (args_out hp (hk h).esp (hk h).wr) (args_out hp' (hk h').esp (hk h').wr)
      fun i hi => by rw [(hk h).argEq hp hi, (hk h').argEq hp' hi, hq.args i hi]) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_ebp {s s' : State} (h : KR F s₀ s) (h' : KR F s₀' s') : ∀ r ∈ [Reg.ebp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.ebp, h'.ebp, hq.scrEq]

end

/-! ## The key -/

/-- The key is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ kln t₀

/-- The pieces of hashing the key: the state for its digest, then `update`
with the key, then `finalize`. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = arg t₀ 3 ∧
    s.gpr .edx = key t₀ ∧ hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((key t₀).setWidth 64) (kln t₀)) ∧
    s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .eax = arg t₀ 3 ∧ s.gpr .ecx = 0 ∧ s.gpr .edx = dO t₀ F.hkO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((key t₀).setWidth 64) (kln t₀))) ∧ Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem ((key t₀).setWidth 64) (kln t₀))) ∧
    Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ s.gpr .ecx = arg t₀ 3 ∧ s.cf = some (decide (kln t₀ < F.H.B + 1))

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
  (hc : AnyChecks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (KR F s₀ s ∧ Long F s₀) ∧ (KR F s₀' s' ∧ Long F s₀')) F.anyHashKey
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  unfold Fns.anyHashKey
  have r1 := piece hp hp' hq (fun t₀ s => KR F t₀ s ∧ Long F t₀) (Hk1 F) (fun h => h.1)
    (fun s s' h h' => ag_ebp hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (hk1_ok h.1) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2 : RelCT isa (fun s s' => Hk1 F s₀ s ∧ Hk1 F s₀' s') (F.H.callInit .edi)
      fun s s' => Hk2 hF.hH s₀ s ∧ Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (sp := E s₀) (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, d⟩, _⟩, ⟨⟨k', d'⟩, _⟩⟩ =>
        ⟨hk2_args hp hz k d, by have := hk2_args hp' hz k' d'; rwa [hq.dOEq] at this, k.esp,
          by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (hk2_ok hp hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (hk2_ok hp' hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
  have r3 := piece hp hp' hq (Hk2 hF.hH) (Hk3 hF.hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1)
    hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk3_ok hp₀ k d) fun t ⟨k', d', i, a, c, x, m⟩ =>
      ⟨⟨k', d', i, a, c, x, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => Hk3 hF.hH s₀ s ∧ Hk3 hF.hH s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => Hk4 hF.hH s₀ s ∧ Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, i, a, c, x, _⟩, _⟩, ⟨⟨k', d', i', a', c', x', _⟩, _⟩⟩ =>
        ⟨hk4_args hp hz hF.hH k d i a c x,
          by have := hk4_args hp' hz hF.hH k' d' i' a' c' x'; rwa [hq.dOEq, hq.keyEq, hq.scrEq,
            hq.klnEq] at this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (hk4_ok hp hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (hk4_ok hp' hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
  have r5 := piece hp hp' hq (Hk4 hF.hH) (Hk5 hF.hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1)
    hc.hk5
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk5_ok hp₀ k d) fun t ⟨k', d', a, c, x, m⟩ =>
      ⟨⟨k', d', a, c, x, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => Hk5 hF.hH s₀ s ∧ Hk5 hF.hH s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5))
      fun s s' => Hk6 hF.hH s₀ s ∧ Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, a, c, x, _⟩, _⟩, ⟨⟨k', d', a', c', x', _⟩, _⟩⟩ =>
        ⟨hk6_args hp hz hF.hH k d a c x,
          by have := hk6_args hp' hz hF.hH k' d' a' c' x'; rwa [hq.dOEq, hq.dOEq, hq.scrEq,
            show arg s₀' 3 = arg s₀ 3 from hq.a (by decide)] at this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (hk6_ok hp hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (hk6_ok hp' hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
  have r7 := piece hp hp' hq (Hk6 hF.hH) (Keyed hF) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1)
    hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (hk7_ok k) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ kln t₀ < F.H.B + 1 := by omega
      have ekp : kp F t₀ = dO t₀ F.hkO := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = F.H.D := by simp only [kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ (hz.hkO_lt), m, b, blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega_using [hlt])
        (hash_len hF.hH b)])
  exact r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))

theorem key_rel :
    RelCT isa (fun s s' => KR F s₀ s ∧ KR F s₀' s') F.anyKey fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.anyKey
  have rc := piece hp hp' hq (fun t₀ s => KR F t₀ s) (Cmp F) id (fun s s' h h' => ag_ebp hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (cmp_ok hp₀ hz k) fun t ⟨k', c, f, _⟩ => ⟨k', c, f⟩)
  have ev : ∀ {t₀ t : State}, Cmp F t₀ t → isa.eval .ae t = some (decide (F.H.B + 1 ≤ kln t₀)) := by
    intro t₀ t h
    show t.cf.map (!·) = _
    rw [h.2.2]; simp only [Option.map_some, ← decide_not, Nat.not_lt]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.klnEq]) ?_ ?_)
  · refine (hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, this⟩, h.1.2.1, by show F.H.B + 1 ≤ kln s₀'; rw [hq.klnEq]; exact this⟩
  · refine (piece hp hp' hq (fun t₀ s => Cmp F t₀ s ∧ kln t₀ < F.H.B + 1) (Keyed hF) (fun h => h.1.1)
      (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, c, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : kp F t₀ = key t₀ := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = kln t₀ := by simp only [kl, hlt, ↓reduceIte]
      refine wp_arg hp₀ k (by decide) fun s₂ u₂ => WP.block_nil ⟨k.upd (by decide) u₂, by rw [u₂.gpr, ekp], ?_, ?_⟩
      · rw [u₂.other _ (by decide), c, ekl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [u₂.mem, ekp, ekl, k.keyBytes hp₀]
    · have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      have hlt : kln s₀ < F.H.B + 1 := by omega_using [this]
      exact ⟨⟨h.1.1, hlt⟩, h.1.2, by rw [hq.klnEq]; exact hlt⟩

/-- After `anyArgs`. -/
abbrev Ag (hF : FnsOK F) (t₀ t : State) : Prop := Keyed hF t₀ t ∧ t.gpr .edi = inn t₀ ∧ t.gpr .esi = out t₀

/-- After HMAC's `init`. -/
abbrev Done (hF : FnsOK F) (t₀ t : State) : Prop :=
  KR F t₀ t ∧ hF.hH.SH.Repr t.mem ((inn t₀).setWidth 64) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr t.mem ((out t₀).setWidth 64) (xorPad (K0 hF t₀) opad)

include hF in
/-- `initAny` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.hmacInitAny fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := KR F s₀) (G' := KR F s₀')
    (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  have ra := piece hp hp' hq (Keyed hF) (Ag hF) (fun h => h.kr) (fun s s' h h' => ag_ebp hq h.kr h'.kr) hc.args
    (fun hp₀ s h => args_ok hp₀ hF h)
  have rc : RelCT isa (fun s s' => Ag hF s₀ s ∧ Ag hF s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call F.hiN F.hiC) (.pop .eax 5))
      fun s s' => Done hF s₀ s ∧ Done hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := E s₀) fun s s' ⟨⟨h, d, i⟩, ⟨h', d', i'⟩⟩ =>
        ⟨call_args hp hz hF h d i,
          by have := call_args hp' hz hF h' d' i'; rwa [hq.innEq, hq.outEq, hq.kpEq, hq.scrEq, hq.klEq] at this,
          h.kr.esp, by rw [h'.kr.esp, hq.E']⟩)
      (fun s ⟨h, d, i⟩ => call_ok hp hz hF h d i) (fun s ⟨h, d, i⟩ => call_ok hp' hz hF h d i)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Done hF s₀ s ∧ Done hF s₀' s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint [.ebp] (4 + 4 * 5)) (fun s s' h => agree_argTaint (ag_ebp hq h.1.1 h.2.1)
      (by rw [h.1.1.esp, h.2.1.esp, hq.esp]) (args_out hp h.1.1.esp h.1.1.wr) (args_out hp' h.2.1.esp h.2.1.wr)
      fun i hi => by rw [h.1.1.argEq hp hi, h.2.1.argEq hp' hi, hq.args i hi]) hr
  unfold Fns.hmacInitAny
  exact pro.seq ((key_rel hp hp' hq hc).seq (ra.seq (rc.seq restore)))

end

/-- `initAny` is verified against `anyN`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verifiedN (hF : FnsOK F) (hc : AnyChecks F) (hsat : ∃ s, (anyN hF.hH.SH (F.W + F.H.S)).pre s) :
    Verified X86.target F.hmacInitAny (anyN hF.hH.SH (F.W + F.H.S)) := by
  refine ⟨fun s hs => correct (pre_of hF hs) hF.sizes hF, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (ct (hF := hF) (pre_of hF h₁) (pre_of hF h₂) ⟨h1, h2⟩ hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The shared contract -/

variable (S : StreamingHash) (W : Nat)

/-- `anyN` with the arguments writable, as the shared contract has them. -/
def anyG : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint key ∧ inner.Disjoint scratch ∧ inner.Disjoint args ∧
    outer.Disjoint key ∧ outer.Disjoint scratch ∧ outer.Disjoint args ∧ key.Disjoint scratch ∧
    key.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint key ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + W * 8 ≤ 2 ^ 32
  post := (anyN S W).post
  pub := (anyN S W).pub

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space (`W` words) as
an argument (as `Proof.Hmac.initScratchContract` is `initContract`'s), and
76 bytes of stack: the contract that the function allocating the working
space follows from (`Verified.stackScratchWiped`). -/
def anyScratchContract : Contract isa :=
  (Proof.Hmac.initScratchSig S W).contract X86.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S X86.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 76)

/-- `anyG` implies the shared contract for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem anyImp (h : ∃ s, (anyScratchContract S W).pre s) : (anyG S W).Implies (anyScratchContract S W) := by
  exact
    { pre := by
        intro s h
        sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, X86.abi] at h
        simp only [argVal32, toNat_setWidth64, show argBytes [32, 32, 32, 32, 32] = 20 from rfl] at h
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27⟩ := h
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27⟩
      post := by
        rintro s s' - h
        sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, a0, a1, a2, a3, a4⟩ := h
        refine ⟨e, fun i hi => ?_⟩
        rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
        · exact setWidth_inj32 a0
        · exact setWidth_inj32 a1
        · exact setWidth_inj32 a2
        · exact setWidth_inj32 a3
        · exact setWidth_inj32 a4
      sat := h }

/-- The regions the proof gives `initAny`: the arguments readable. -/
def narrowRd (s : State) : List Region := [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (S W : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 1).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, W * 8⟩]

/-- A state for `anyG`, given the regions `anyN` gives. -/
theorem anyN_pre {s : State} (h : (anyG S W).pre s) :
    (anyN S W).pre (s.withRegions (narrowRd s) (narrowWr S.stateBytes W s)) := by
  obtain ⟨h0, h1, _, _, h4, h5, h6, h7, h8, h9, h10, h11, _, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27⟩ := h
  simp only [anyN, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨h0, h1, trivial, trivial, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27⟩

/-- Verified against `anyN`, so against `anyG`. -/
theorem verified_anyG {c : Prog isa} (h : Verified X86.target c (anyN S W)) (hsat : ∃ s, (anyG S W).pre s) :
    Verified X86.target c (anyG S W) := by
  refine Verified.narrowTo h narrowRd (narrowWr S.stateBytes W) (fun s h => anyN_pre S W h) (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, _, h2, h3, _⟩ := h
    rw [h2, h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨_, _, _, h3, _⟩ := h
    rw [h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp

/-- `initAny` is verified against the shared contract, given the taint checks
and a state satisfying the shared contract. -/
theorem verified (hF : FnsOK F) (hc : AnyChecks F) {S : StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (anyScratchContract S W).pre s) :
    Verified X86.target F.hmacInitAny (anyScratchContract S W) := by
  subst hS hW
  have imp := anyImp hF.hH.SH (F.W + F.H.S) hsat
  have gsat : ∃ s, (anyG hF.hH.SH (F.W + F.H.S)).pre s := hsat.elim fun s h => ⟨s, imp.pre s h⟩
  exact (verified_anyG _ _ (verifiedN hF hc (gsat.elim fun s h => ⟨_, anyN_pre _ _ h⟩)) gsat).of_implies imp

/-! ## Its stack, and `esp` -/

/-- `initAny` uses at most 76 bytes of stack. -/
theorem hmacInitAny_stack (hF : FnsOK F) : stackUse F.hmacInitAny ≤ 76 := by
  have := hF.hH.initSU; have := hF.hH.updSU; have := hF.hH.finSU; have := hF.hiSU
  simp only [Fns.hmacInitAny, Fns.anyKey, Fns.anyHashKey, Impl.Pbkdf2.Stream.X86.Hash.callInit,
    stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at *
  omega_arith

/-- `initAny`'s instructions all satisfy `p` if those of the functions it
calls do and those of its own pieces do (`shapeOf`, decided for each hash
function). -/
theorem hmacInitAny_allInstrs {p : Instr → Bool} (hb : (shapeOf F).hmacInitAny.allInstrs p = true)
    (hi : F.H.initC.allInstrs p = true) (hu : F.H.updC.allInstrs p = true) (hf : F.H.finC.allInstrs p = true)
    (hh : F.hiC.allInstrs p = true) : F.hmacInitAny.allInstrs p = true := by
  have e1 : (shapeOf F).H.initC = .block [] := rfl
  have e2 : (shapeOf F).H.updC = .block [] := rfl
  have e3 : (shapeOf F).H.finC = .block [] := rfl
  have e4 : (shapeOf F).hiC = .block [] := rfl
  simp only [Fns.hmacInitAny, Fns.anyKey, Fns.anyHashKey, Impl.Pbkdf2.Stream.X86.Hash.callInit, Code.allInstrs,
    e1, e2, e3, e4, hi, hu, hf, hh, Bool.and_true] at hb ⊢
  exact hb

theorem allInstrs_of_noSp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp [h i hi]

theorem all_writesSp_eq (c : Prog isa) :
    c.all (fun i => !isa.writesSp i) = c.allInstrs (fun i => !Taint.clobbers i .esp) := by
  rw [Whole.X86.all_eq, Code.allInstrs_eq]
  simp only [Whole.X86.clobbers_esp]

/-- `initAny` writes `esp` only through its frames' pushes and pops. -/
theorem hmacInitAny_noEsp (hF : FnsOK F)
    (hb : (shapeOf F).hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true) :
    F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_allInstrs hb (allInstrs_of_noSp hF.hH.initSp) (allInstrs_of_noSp hF.hH.updSp)
    (allInstrs_of_noSp hF.hH.finSp) (allInstrs_of_noSp hF.hiSp)

/-! ## In a frame of its own, wiped -/

/-- The bytes of `init`'s frame: its return address, a copy of its four
argument slots and the working space. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := 8 + 16 + 8 * I.initAnyKeyScratch

/-- `initAny` in a frame holding its working space, which it wipes before
returning: verified against `initAnyKeyContract`, from the locality of its
postcondition (`Proof/Hmac/AnyKey.lean`). -/
theorem anyFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified X86.target c (anyScratchContract I.S I.initAnyKeyScratch))
    (hR : Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (I.initAnyKeyContract X86.abi (76 + anyFrame I)).pre s)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true)
    (hd : stackUse c ≤ 76) (hs : 8 * I.initAnyKeyScratch < 4072 := by decide) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame I) 4 (2 * I.initAnyKeyScratch) c)
      (I.initAnyKeyContract X86.abi (76 + anyFrame I)) :=
  X86.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S X86.abi.ptrBits) (wa := true) (stack := 76)
    (bytes := anyFrame I) (words := 2 * I.initAnyKeyScratch) h
    (by
      refine ⟨?_, by simp only [anyFrame]; omega_using [hs], by simp only [anyFrame]; omega_using []⟩
      change 8 + 4 * 4 + I.initAnyKeyScratch * 8 ≤ anyFrame I
      simp only [anyFrame]; omega_using [])
    hsp hd (by change 4 * (2 * I.initAnyKeyScratch) ≤ I.initAnyKeyScratch * 8; omega_using [])
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.initPost_local I.S _) (Hmac.initPostOut_local I.S _ hR hS) hsat rfl

/-- The frame of `withStackScratchWiped` keeps the stack pointer for any `c`
that does, if it does for an empty body and its wipe (decided for literal
sizes). -/
theorem withStackScratchWiped_spSafe {bytes n words : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true)
    (hw : (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * n) words) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by decide +kernel)
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true := by decide +kernel) :
    (Impl.StackScratch.X86.withStackScratchWiped bytes n words c).all (fun i => !isa.writesSp i) = true :=
  Md.X86.withStackScratch_spSafe (c := .seq c (.block _)) (by simp only [Code.all, h, Bool.true_and]; exact hw) hf

end VG.Proof.Pbkdf2.Whole.X86.Any
