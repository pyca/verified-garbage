module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Key
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Stream

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
  have := hp.nsc; exact Pbkdf2.Stream.X86.setWidth_add (by omega)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.toNat_add_ofNat (by omega)

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (sR s₀ o n) (scR F s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.base_disjoint _ hk (by omega)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (lowR s₀ k) (scR F s₀) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR F s₀) (scR F s₀) := by
  have := end_le hz; have := layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 16 ≤ F.L8; omega)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8) : (svR F s₀).Disjoint (sR s₀ o n) := by
  have := L8_le hz
  exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega)) (by simp only [Fns.L]; omega) (by omega)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (svR F s₀).Disjoint (lowR s₀ k) := by
  have := L8_le hz; have := end_le hz; have := layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 16) (by simp only [Fns.L]; omega)
    (by simp only [Fns.L]; omega)).symm

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
      · exact ⟨scR F s₀, by simp, low_sub (F := F) (by omega)⟩
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
  exact Pbkdf2.Stream.X86.arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega) hk.frame hd (by omega)

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [show s.ea (at_ .esp (4 + 4 * i)) = addr (s.gpr .esp) (4 + 4 * i) from rfl, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.wr]
  exact ⟨argR s₀, by simp, by
    rw [argR_eq]; exact Pbkdf2.Stream.X86.arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

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
      exact (Offset.below_disjoint _ (by omega)).symm) (by decide)

theorem KR.keyBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem ((key s₀).setWidth 64) (kln s₀) = bytesAt s₀.mem ((key s₀).setWidth 64) (kln s₀) :=
  bytes_keep hk.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.i_k.symm
    · exact hp.o_k.symm
    · exact hp.k_s
    · exact hp.b_k.symm) (by have := hp.nk; omega)

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
