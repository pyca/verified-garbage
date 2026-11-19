module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.AArch64
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkLoop
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Sha512.AArch64.Variant
public import VerifiedGarbage.Proof.Sha256.AArch64.Variant
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Pbkdf2.Scratch

/-! ### `Pbkdf2.Md.AArch64.AnyKeyCT`, which only this module used -/

section

/-! ### `Pbkdf2.Md.AArch64.AnyKey`, which only this module used -/

section

/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function on AArch64: correct

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/AnyKey.lean`): `initAny`
(`Impl/Pbkdf2/Md/AnyKey/AArch64.lean`) saves our caller's registers and our
return address, makes the key as `pbkdf2` makes it from a password (hashing a
key longer than a block with the streaming functions, into `scratch`), calls
HMAC's `init` with it, and loads the registers back. Each step is `pbkdf2`'s
(`Pbkdf2.lean`), for this function's arguments: `anyG` is the contract the
proof is written against.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Any

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_subImm wp_movz wp_lsr eval_zero sub_beq)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.Md.AArch64.Pbk (PSizes layout end_le L_lt InitArgs hinit_call hash_len blockKey_hash
  eregs epub kregs kregs_pres shr_beq_zero log2_B)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG After SavedRegs SavedRegs.frame save_ok saveR UpdArgs stk
  untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self bytesAt_take covers_one)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey)

/-! ## The contract -/

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length, with
`8 W` bytes of scratch space: `VG.Spec.Hmac.initAnyKeyContract` with its
working space as an argument. -/
def anyG (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint inner ∧ (stk s).Disjoint outer ∧ (stk s).Disjoint key ∧
    (stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    S.Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev key : Addr := s₀.gpr .x2
abbrev kln : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev keyR : Region := ⟨key s₀, kln s₀⟩
abbrev stkR : Region := stk s₀
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩

end

section
variable (H) (s₀ : State)
abbrev innR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev scR : Region := ⟨scr s₀, (H.W + H.S) * 8⟩
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨scr s₀, 8 * H.W⟩
/-- Where our caller's registers and our return address are saved. -/
abbrev hdrR : Region := sR s₀ H.sv 56
end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [innR H s₀, outR H s₀, scR H s₀]
  i_o : (innR H s₀).Disjoint (outR H s₀)
  i_s : (innR H s₀).Disjoint (scR H s₀)
  o_s : (outR H s₀).Disjoint (scR H s₀)
  k_i : (keyR s₀).Disjoint (innR H s₀)
  k_o : (keyR s₀).Disjoint (outR H s₀)
  k_s : (keyR s₀).Disjoint (scR H s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (stkR s₀).Disjoint (innR H s₀)
  stk_o : (stkR s₀).Disjoint (outR H s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR H s₀)
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (anyG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hS := hH.hS
  simp only [hS, Nat.mul_comm 8] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-! ## The parts of `scratch` -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

theorem part_sub {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) : Region.Sub (sR s₀ o n) (scR H s₀) :=
  Offset.sub_base _ h

include hz in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ (H.W + H.S) * 8)
    (hb : b + n ≤ (H.W + H.S) * 8) : Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L_lt hz; exact Offset.disjoint _ h (by omega_using [ha, this]) (by omega_using [hb, this])

include hz in
theorem low_disj {b n : Nat} (hb : 8 * H.W ≤ b) (hbn : b + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (sR s₀ b n) (lowR H s₀) := by
  have := L_lt hz; exact Offset.disjoint_base _ hb (by omega_using [hbn, this])

theorem low_sub : Region.Sub (lowR H s₀) (scR H s₀) :=
  Region.sub_prefix (by show 8 * H.W ≤ (H.W + H.S) * 8; omega_using [])

include hp in
theorem sc_mem : scR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

include hz in
/-- The header, after the working space of the functions we call and before
the parts `pbkdf2`'s code writes. -/
theorem hdr_disj {o n : Nat} (h₁ : H.st0O ≤ o) (h₂ : o + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (hdrR H s₀) (sR s₀ o n) := by
  have e : H.st0O = H.sv + 80 := rfl
  have := hz.o_sv_80_le_L
  exact part_disj hz (Or.inl (by omega_using [h₁, e])) (by omega_using [this]) h₂

include hz in
theorem hdr_low : Region.Disjoint (hdrR H s₀) (lowR H s₀) := by
  have := hz.o_sv_80_le_L; have e : H.sv = 8 * H.W := rfl
  exact low_disj hz (by omega_using [e]) (by omega_using [this])

include hz in
theorem hdr_sub : Region.Sub (hdrR H s₀) (scR H s₀) := by
  have := hz.o_sv_80_le_L
  exact part_sub (by omega_using [this])

theorem save_hdr : Region.Sub (saveR H.hh (scr s₀)) (hdrR H s₀) := Region.sub_prefix (Nat.le_refl _)

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's
registers (those we save in `scratch`, and `x25`–`x28`, which nothing we run
writes), and everything written is in a state, `scratch` or the 16 bytes
below the stack pointer. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  frame : Frame [innR H s₀, outR H s₀, scR H s₀, stkR s₀] s₀.mem s.mem

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR H s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [innR H s₀, outR H s₀, scR H s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (by revert hr; decide +revert)).trans (h.cs r hr),
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left save_hdr, h.frame.trans (hf.sub hsub)⟩

omit hp hz in
theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h)
    (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ kregs) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

omit hz in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {R : Region} (hR : Region.Sub R (scR H s₀)) :
    (below s.sp 16).Disjoint R := by
  rw [h.sp]; exact hp.stk_s.sub_right hR

/-- What a call leaves, writing the states, parts of `scratch` after its
header, or its working space, and the 16 bytes below the stack pointer. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) {ws : List Region}
    (hf : Frame (ws ++ [below s.sp 16]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, r = innR H s₀ ∨ r = outR H s₀ ∨ (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  refine h.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (hp.i_s.sub_right (hdr_sub hz)).symm
      · exact (hp.o_s.sub_right (hdr_sub hz)).symm
      · exact (hdr_low hz).sub_right (Region.sub_prefix hk)
      · exact hdr_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (stk_sc hp h (hdr_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨_, by simp, Region.sub_prefix (Nat.le_refl _)⟩
      · exact ⟨_, by simp, Region.sub_prefix (Nat.le_refl _)⟩
      · exact ⟨scR H s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega_using [hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.sp]
      exact ⟨_, by simp, fun _ h => h⟩

omit hz in
theorem KR.keyBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (key s₀) (kln s₀) = bytesAt s₀.mem (key s₀) (kln s₀) :=
  bytes_keep h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.stk_k.symm) (Nat.le_of_lt (s₀.gpr .x3).isLt)

omit hz in
theorem in_wr {s : State} (h : KR (H := H) s₀ s) : scR H s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

omit hz in
theorem cov_part {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (in_wr hp h) hn

end

/-! ## The entry -/

/-- What the entry sets up, kept until HMAC's `init` is called: `x19` =
`key`, `x20` = `key_len`, `x21` = `inner`, `x22` = `outer`. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  x19 : s.gpr .x19 = key s₀
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = inn s₀
  x22 : s.gpr .x22 = out s₀

theorem KE.upd {s₀ s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_eregs d h'),
    by rw [u.other _ (ne _ (by simp)), h.x19],
    by rw [u.other _ (ne _ (by simp)), h.x20], by rw [u.other _ (ne _ (by simp)), h.x21],
    by rw [u.other _ (ne _ (by simp)), h.x22]⟩

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz a.rd a.wr a.sp a.cs a.frame fun r hr => .inr (.inr (hw r hr)),
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x19],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x20], by rw [a.cs _ (by simp [preserved]) (by decide), h.x21],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x22]⟩

theorem entry_ok : WP isa (.block H.anyEntry) s₀ (KE (H := H) s₀) := by
  simp only [Hash.anyEntry]
  refine save_ok H.hh (scr := scr s₀) (L := (H.W + H.S) * 8) rfl (by show H.W ≤ 1024; exact hz.o_W_le_1024)
    (sc_mem hp) (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L)
    fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x23 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → s₆.gpr r = s₀.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₆.other r h₅, u₅.other r h₄, u₄.other r h₃, u₃.other r h₂, u₂.other r h₁, g₁]
  have m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁],
    fun r hr => by
      have : r ≠ .x23 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 := by revert hr; decide +revert
      exact g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2,
    m₆ ▸ sv₁,
    m₆ ▸ f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR H s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L)⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]

end

/-! ## The key

As `pbkdf2`'s (`Pbk.key_ok`), for the key and its length in `x19` and `x20`. -/

/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if kln s₀ < H.P.B + 1 then key s₀ else A s₀ H.hkO
abbrev kl (H : Hash) (s₀ : State) : Nat := if kln s₀ < H.P.B + 1 then kln s₀ else H.D

/-- The key HMAC's `init` gets: the key, or the digest of a key longer than a
block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = key s₀ ∧ kl = kln s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (key s₀) (kln s₀))

/-- `K₀`, the key padded to a block (or its digest, if longer). -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (key s₀) (kln s₀))

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.hkInit) s fun t => KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO := by
  simp only [Hash.hkInit]
  exact wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ =>
    WP.block_nil ⟨h.upd u₁ (by decide), by rw [u₁.gpr, h.kr.x23]⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hx0 : s.gpr .x0 = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] :=
  VG.Proof.Pbkdf2.Md.AArch64.Calls.init_call hH.stream (st := A s₀ H.stWO) hx0
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    fun s₂ a₂ r₂ => ⟨h.call hp hz a₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the key. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block H.hkUpd) s fun t => KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stWO) (key s₀) (scr s₀) (kln s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hWb := hH.wb_le
  simp only [Hash.hkUpd]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x19]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cd := covers_one (List.mem_append_left _ (by rw [k₅.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₅.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp k₅.kr (by exact hz.o_hsWb_le_L hH)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right
        (Region.sub_prefix hWb)
      d_st := hp.k_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.k_s.sub_right (Region.sub_prefix (by exact hz.o_hsWb_le_L hH))
      sp16 := by rw [k₅.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₅.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := by rw [k₅.kr.sp]; exact hp.stk_k
      stk_sc := stk_sc hp k₅.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : UpdArgs hH.stream s (A s₀ H.stWO) (key s₀) (scr s₀) (kln s₀))
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  have hWb := hH.wb_le
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream ua fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr hx1
    rwa [List.nil_append, h.kr.keyBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀))) :
    WP isa (.block H.hkFin) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .x1 = s₀.gpr .x3 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  have hWb := hH.wb_le
  simp only [Hash.hkFin]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_mov fun s₂ u₂ =>
    wp_addImm (by exact hz.o_hkO_lt_4096) fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil ?_
  have k₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨k₄, ?_, by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x20],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      x3 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₄.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_part hp k₄.kr (by exact hz.o_hkO_hsF_le_L)
        · exact cov_low hp k₄.kr (by exact hz.o_hsWb_le_L hH)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L)
        (by exact hz.o_hkO_hsF_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right
        (Region.sub_prefix hWb)
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_hsF_le_L)).sub_right
        (Region.sub_prefix hWb)
      sp16 := by rw [k₄.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₄.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := stk_sc hp k₄.kr (part_sub (by exact hz.o_hkO_hsF_le_L))
      stk_sc := stk_sc hp k₄.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hx1 : s.gpr .x1 = s₀.gpr .x3) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  have hWb := hH.wb_le
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by exact hz.o_hkO_hsF_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ (show H.D ≤ H.stream.F by exact hz.o_D_le_hsF)]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .x3).isLt)
      (by rw [hx1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.hkKey) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧ t.mem = s.mem := by
  simp only [Hash.hkKey]
  refine wp_addImm (by exact hz.o_hkO_lt_4096) fun s₁ u₁ => wp_movz fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.kr.x23],
    by rw [u₂.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.D < 2 ^ 16 by exact hz.o_D_lt_p16),
      Nat.mod_eq_of_lt (show H.D < 2 ^ 64 by exact hz.o_D_lt_p64)],
    by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

omit hz in
theorem short_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hs : kln s₀ < H.P.B + 1) :
    WP isa (.block Hash.short) s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧
      (t.gpr .x3).toNat = kl H s₀ ∧ KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have e₁ : kp H s₀ = key s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  have e₂ : kl H s₀ = kln s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  rw [e₁, e₂]
  simp only [Hash.short]
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil ?_
  refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.x19],
    by rw [u₂.gpr, u₁.other _ (by decide), h.x20], ⟨.inl ⟨rfl, rfl⟩, by omega_using [hs], ?_⟩⟩
  rw [u₂.mem, u₁.mem, h.kr.keyBytes hp]

theorem long_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hs : ¬ kln s₀ < H.P.B + 1) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧
      (t.gpr .x3).toNat = kl H s₀ ∧ KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hs)
  have e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hs)
  rw [e₁, e₂]
  refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, x2, x3, hb⟩ =>
    ⟨k, x2, x3, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
  rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega_using [hs])]

omit hp in
/-- The value of `x9` the key's first branch tests. -/
theorem key_shr {s : State} (h : KE (H := H) s₀ s) {s₁ : State}
    (u : Upd s s₁ .x9 (s.gpr .x20 >>> Nat.log2 H.P.B)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (kln s₀ < H.P.B)) := by
  change eval (.zero .x .x9) s₁ = _
  rw [eval_zero, u.gpr, h.x20, shr_beq_zero, (log2_B hz).1]

omit hp hz in
/-- The value of `x9` the key's second branch tests. -/
theorem key_sub {s : State} (h : KE (H := H) s₀ s) {s₂ : State}
    (u : Upd s s₂ .x9 (s.gpr .x20 - BitVec.ofNat 64 H.P.B)) (hB : H.P.B < 2 ^ 64) :
    isa.eval (.zero .x .x9) s₂ = some (decide (kln s₀ = H.P.B)) := by
  change eval (.zero .x .x9) s₂ = _
  have ex : s₀.gpr .x3 = BitVec.ofNat 64 (kln s₀) := by simp
  rw [eval_zero, u.gpr, h.x20, ex, sub_beq (s₀.gpr .x3).isLt hB]

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧ (t.gpr .x3).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hB := hz.B_le
  unfold Hash.key Hash.keyShr Hash.keySub
  refine WP.seq (wp_lsr (log2_B hz).2 fun s₁ u₁ => WP.block_nil ?_)
  have k₁ := h.upd u₁ (by decide)
  refine WP.ite _ (key_shr hz h u₁) (fun hT => short_ok hp hH k₁ (by have := of_decide_eq_true hT; omega_using [this]))
    fun hF => ?_
  refine WP.seq (wp_subImm (by exact hz.o_B_lt_4096) fun s₂ u₂ => WP.block_nil ?_)
  have k₂ := k₁.upd u₂ (by decide)
  refine WP.ite _ (key_sub k₁ u₂ (by exact hz.o_B_lt_p64)) (fun hT => short_ok hp hH k₂ (by
    have := of_decide_eq_true hT; omega_using [this])) fun hF' => long_ok hp hz hH k₂ (by
      have := of_decide_eq_false hF; have := of_decide_eq_false hF'; omega_arith)

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ (innR H s₀) ∧
      Region.Disjoint ⟨kp, kl⟩ (outR H s₀) ∧ Region.Disjoint ⟨kp, kl⟩ (lowR H s₀) ∧
      (below s.sp 16).Disjoint ⟨kp, kl⟩ := by
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.k_i, hp.k_o, hp.k_s.sub_right low_sub, by rw [h.sp]; exact hp.stk_k⟩
  · refine ⟨Covers.of_sub fun r hr => ?_,
      (hp.i_s.sub_right (part_sub (by exact hz.o_hkO_D_le_L))).symm,
      (hp.o_s.sub_right (part_sub (by exact hz.o_hkO_D_le_L))).symm,
      low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      stk_sc hp h (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-! ## HMAC's `init` -/

/-- HMAC's `init`'s arguments: the two states, the key and the working space. -/
theorem args_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hx2 : s.gpr .x2 = kp H s₀)
    (hx3 : (s.gpr .x3).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block Hash.anyArgs) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (inn s₀) (out s₀) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hsnw := hp.snw
  simp only [Hash.anyArgs]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { x0 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x21]
      x1 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x22]
      x2 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx2]
      x3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx3]
      x4 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_of_self (show innR H s₀ ∈ s₃.wr by rw [k₃.kr.wr, hp.wr]; simp) (Nat.le_refl _)
        · exact sub_of_self (show outR H s₀ ∈ s₃.wr by rw [k₃.kr.wr, hp.wr]; simp) (Nat.le_refl _)
        · exact cov_low hp k₃.kr (by exact hz.o_W8_le_L)
      i_o := hp.i_o
      i_s := hp.i_s.sub_right low_sub
      o_s := hp.o_s.sub_right low_sub
      k_i := k_i
      k_o := k_o
      k_s := k_s
      sp16 := by rw [k₃.kr.sp]; exact hp.sp16
      stk_i := by rw [k₃.kr.sp]; exact hp.stk_i
      stk_o := by rw [k₃.kr.sp]; exact hp.stk_o
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega_using [hsnw] }

/-- HMAC's `init`: the states. -/
theorem call_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (inn s₀) (out s₀) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KR (H := H) s₀ t ∧
      hH.SH.Repr t.mem (inn s₀) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (out s₀) (xorPad (K0 hH s₀) opad) := by
  refine hinit_call hH hI hId ia fun s₄ a₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.kr.call hp hz a₄.rd a₄.wr a₄.sp a₄.cs a₄.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl ⟨_, rfl, Nat.le_refl _⟩))
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

end

/-! ## The function -/

section
variable {H : Hash} (hH : HashOK H)
include hH

/-- `initAny` uses only scalar instructions around its verified callees. -/
theorem hmacInitAny_keepsV : H.hmacInitAny.allInstrs keepsV = true := by
  have hi := hH.initKeepsV
  have hu := hH.updKeepsV
  have hf := hH.finKeepsV
  have hinit : H.hmacInit.allInstrs keepsV = true := hH.hmacInit_keepsV
  have hk : H.key.allInstrs keepsV = true := by
    simp [Hash.key, Hash.keyShr, Hash.keySub, Hash.short, Hash.hashKey, Hash.hkInit,
      Hash.hkUpd, Hash.hkFin, Hash.hkKey, Impl.MdStream.AArch64.mov,
      Code.allInstrs, keepsV, vdstOf, hi, hu, hf]
  simp [Hash.hmacInitAny, Hash.anyEntry, Hash.anyArgs, Hash.exit, Impl.Pbkdf2.Md.AArch64.Stream.save,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.Pbkdf2.Md.AArch64.Stream.restore, Impl.MdStream.AArch64.mov,
    Code.allInstrs, keepsV, vdstOf, hk, hinit]

end

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem correct (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) :
    WP isa H.hmacInitAny s₀ fun s' => abiPreserved s₀ s' ∧ (anyG hH.SH (H.W + H.S)).post s₀ s' := by
  apply WP.withPreservedV (hc := hmacInitAny_keepsV hH)
  unfold Hash.hmacInitAny
  refine WP.seq (WP.mono (entry_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (key_ok hp hz hH k₁) fun s₂ ⟨k₂, x2₂, x3₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (args_ok hp hz hH k₂ x2₂ x3₂ ka) fun s₃ ⟨k₃, a₃, h₃⟩ => ?_)
  refine WP.seq (WP.mono (call_ok hp hz hH hI hId k₃ a₃ h₃) fun s₄ ⟨k₄, i₄, o₄⟩ => ?_)
  unfold Hash.exit
  refine WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Calls.restore_ok H.hh k₄.x23
    (by show H.W ≤ 1024; exact hz.o_W_le_1024) k₄.saved (in_wr hp k₄)
    (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L))
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hsp, k₄.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hg _ (by decide)
      | exact (ho _ (by decide)).trans (k₄.cs _ (by decide))
  · show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
    rw [hm]; exact ⟨i₄, o₄⟩

end

end VG.Proof.Pbkdf2.Md.AArch64.Any

end

end


/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function on AArch64: constant time, verified

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/AnyKeyCT.lean`): the pieces between the
calls are checked by the taint analysis: the entry and HMAC's `init`'s
arguments (`AnyOK`, for each hash function), and the pieces `pbkdf2` shares
(`Pbk.Checks`: the key's, and the exit), each from registers that the
correctness proof fixes to public values (`KE`, `KR`). The calls are
constant time by their callees' proofs, and the branches on the key's length
go the same way in both runs. `hmacInitAny_verified` puts it together for
each hash function, verified against the shared contract.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Any

open VG.AArch64
open VG.Proof.MdStream.AArch64 (wp_lsr wp_subImm)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK CoreOK core)
open VG.Proof.Pbkdf2.Md.AArch64.Pbk (PSizes layout end_le hinit_rel epub log2_B)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG rel_taint rel_wp PubEq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash)

variable {H : Hash}

/-! ## The key's branches, one run at a time -/

section
variable {s₀ : State} (hz : PSizes H)
include hz

theorem keyShr_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.keyShr) s fun t =>
      KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ < H.P.B)) := by
  unfold Hash.keyShr
  exact wp_lsr (log2_B hz).2 fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), key_shr hz h u₁⟩

theorem keySub_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.keySub) s fun t =>
      KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ = H.P.B)) := by
  have hB := hz.B_le
  unfold Hash.keySub
  exact wp_subImm (by omega_using [hB]) fun s₂ u₂ => WP.block_nil ⟨h.upd u₂ (by decide), key_sub h u₂ (by omega_using [hB])⟩

end

/-! ## What agrees in the two runs -/

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem scr_eq : scr s₀' = scr s₀ := hq.x4.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show scr s₀' + _ = scr s₀ + _; rw [scr_eq hq]
theorem key_eq : key s₀' = key s₀ := hq.x2.symm
theorem kln_eq : kln s₀' = kln s₀ := by show (s₀'.gpr .x3).toNat = _; rw [← hq.x3]
theorem kp_eq : kp H s₀' = kp H s₀ := by
  show (if kln s₀' < H.P.B + 1 then key s₀' else A s₀' H.hkO) = _; rw [kln_eq hq, key_eq hq, A_eq hq]
theorem kl_eq : kl H s₀' = kl H s₀ := by
  show (if kln s₀' < H.P.B + 1 then kln s₀' else H.D) = _; rw [kln_eq hq]

theorem kr_agree {s s' : State} (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ [Reg.x23], s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [h.x23, h'.x23, scr_eq hq]

theorem ke_agree {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ epub, s.gpr r = s'.gpr r := by
  refine ⟨(kr_agree hq h.kr h'.kr).1, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, key_eq hq]
  · rw [h.x20, h'.x20, hq.x3]
  · rw [h.x21, h'.x21]; exact hq.x0
  · rw [h.x22, h'.x22]; exact hq.x1
  · exact (kr_agree hq h.kr h'.kr).2 _ (by simp)

end

/-! ## The pieces in two runs -/

/-- The taint check of `initAny`'s entry, the piece `pbkdf2` does not have. -/
abbrev EntryCheck (H : Hash) : Prop :=
  ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Calls.args) (.block H.anyEntry) hc).isSome = true

/-- The taint check of the arguments of HMAC's `init`. -/
abbrev ArgsCheck : Prop :=
  ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block Hash.anyArgs) hc).isSome = true

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Pbk.Checks H)
include hH hp hp' hz hq hc

omit hH hc in
theorem entry_rel (he : EntryCheck H) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.anyEntry)
      fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s' :=
  rel_taint VG.Proof.Pbkdf2.Md.AArch64.Calls.args (fun s s' e e' => by
      rw [e, e']
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hq.x0, hq.x1, hq.x2, hq.x3, hq.x4]) he
    (fun _ e => by rw [e]; exact entry_ok hp hz) (fun _ e => by rw [e]; exact entry_ok hp' hz)

/-- Hashing a key longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO)
    (G' := fun t => KE (H := H) s₀' t ∧ t.gpr .x0 = A s₀' H.stWO) epub ag hc.hk1
    (fun _ h => hk1_ok hz h) (fun _ h => hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, Pre (H := H) σ₀ → KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.stream.S⟩] s.wr :=
    fun hp h => Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega_using [hl, he, hSS])
  have c₂ := rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x0 = A s₀ H.stWO) ∧
        (KE (H := H) s₀' s' ∧ s'.gpr .x0 = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i, i', (ke_agree hq h.1.1 h.2.1).1⟩)
    (fun _ h => hk2_ok hp hz hH h.1 h.2) (fun _ h => hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) epub
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => hk3_ok hp hz hH h.1 h.2) (fun _ h => hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (key s₀') (kln s₀')))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => hk5_ok hp hz hH h.1 h.2) (fun _ h => hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (key s₀') (kln s₀')))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, key_eq hq, scr_eq hq, kln_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], (ke_agree hq k k').1⟩)
        (fun _ h => hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, A_eq hq, scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.x3], (ke_agree hq k k').1⟩)
        (fun _ h => hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.key
    fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .x2 = kp H s₀' ∧ (s'.gpr .x3).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')) := by
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  obtain ⟨_, hs⟩ := hc.short
  have short : ∀ {P : State → State → Prop}, (∀ s s', P s s' → KE (H := H) s₀ s ∧ KE (H := H) s₀' s') →
      RelCT isa P (.block Hash.short) fun _ _ => True := fun hP =>
    RelCT.taint (A := taint) (Taint.ofRegs epub) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := ke_agree hq (hP _ _ h).1 (hP _ _ h).2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hs
  have ite : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.key fun _ _ => True := by
    unfold Hash.key
    have r₁ := rel_taint
      (G := fun t => KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ < H.P.B)))
      (G' := fun t => KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀' < H.P.B)))
      epub ag hc.keyShr (fun _ h => keyShr_ok hz h) (fun _ h => keyShr_ok hz h)
    refine r₁.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, kln_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)
    have r₂ := rel_taint
      (F := fun t => KE (H := H) s₀ t) (F' := fun t => KE (H := H) s₀' t)
      (G := fun t => KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ = H.P.B)))
      (G' := fun t => KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀' = H.P.B)))
      epub ag hc.keySub (fun _ h => keySub_ok hz h) (fun _ h => keySub_ok hz h)
    refine (r₂.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, kln_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    exact (hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  exact (ite.wp fun s s' h => ⟨key_ok hp hz hH h.1, key_ok hp' hz hH h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

omit hc in
/-- HMAC's `init`, with its arguments. -/
theorem init_rel (ha : ArgsCheck) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .x2 = kp H s₀' ∧ (s'.gpr .x3).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')))
      (.seq (.block Hash.anyArgs) (.call H.hmacInitN H.hmacInit))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  have r₁ := rel_taint
    (F := fun s => KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
      KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀))
    (F' := fun s => KE (H := H) s₀' s ∧ s.gpr .x2 = kp H s₀' ∧ (s.gpr .x3).toNat = kl H s₀' ∧
      KeyAt hH s₀' s.mem (kp H s₀') (kl H s₀'))
    epub (fun s s' h h' => ke_agree hq h.1 h'.1) ha
    (fun _ h => args_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => args_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine r₁.seq ((rel_wp (hinit_rel hH hI fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [kp_eq hq, scr_eq hq, kl_eq hq, show inn s₀' = inn s₀ from hq.x0.symm,
          show out s₀' = out s₀ from hq.x1.symm] at a'
        exact ⟨a, a', (ke_agree hq k k').1⟩)
      (fun _ h => call_ok hp hz hH hI hId h.1 h.2.1 h.2.2)
      (fun _ h => call_ok hp' hz hH hI hId h.1 h.2.1 h.2.2)).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.1.1, h.2.1⟩)

theorem ct (he : EntryCheck H) (ha : ArgsCheck) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInitAny fun _ _ => True := by
  unfold Hash.hmacInitAny
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.exit) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x23]) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hx
  exact (entry_rel hp hp' hz hq he).seq ((key_rel hH hp hp' hz hq hc).seq
    (RelCT.assoc ((init_rel hH hp hp' hz hq ha hI hId).seq ex)))

end

/-- `initAny` is verified against `anyG`, given the taint checks and the
proof of HMAC's `init`. -/
theorem verified (hH : HashOK H) (hc : Pbk.Checks H) (he : EntryCheck H) (ha : ArgsCheck)
    (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hId : H.hmacInit.aarch64Depth ≤ 1)
    (hsat : ∃ s, (anyG hH.SH (H.W + H.S)).pre s) :
    Verified AArch64.target H.hmacInitAny (anyG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => correct (pre_of hH hs) hH.psizes hH hI hId,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH h₁) (pre_of hH h₂) hH.psizes ⟨h1, h2, h3, h4, h5, h6⟩ hc he ha hI hId
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## For each hash function -/

/-- What the kernel checks of `initAny`'s own code (`core H`), once for each
hash function: the taint checks of its entry and of HMAC's `init`'s
arguments. -/
structure AnyOK (C : Hash) : Prop where
  entry : EntryCheck C
  args : ArgsCheck

/-! ## The shared contract -/

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space (`W` words) as
an argument (as `Proof.Hmac.initScratchContract` is `initContract`'s): the
contract that the function allocating the working space follows from
(`Verified.stackScratchWiped`). -/
def anyScratchContract (S : StreamingHash) (W : Nat) : Contract isa :=
  (Proof.Hmac.initScratchSig S W).contract AArch64.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S AArch64.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 16)

/-- `anyG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem anyImp (S : StreamingHash) (W : Nat) (h : ∃ s, (anyScratchContract S W).pre s) :
    (anyG S W).Implies (anyScratchContract S W) := by
  generic_implies [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, anyG,
    VG.Proof.Pbkdf2.Md.AArch64.Calls.stk, AArch64.abi, AArch64.argRegs] using h

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H)) (A : AnyOK (core H))
include hH C A

/-- `initAny`, verified against the shared contract. -/
theorem hmacInitAny_verified
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s)
    (hsat : ∃ s, (anyScratchContract hH.SH (H.W + H.S)).pre s) :
    Verified AArch64.target H.hmacInitAny (anyScratchContract hH.SH (H.W + H.S)) :=
  (verified hH (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Checks.of_core C.pbk) A.entry A.args
    (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_ok hH C hsI)
    (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_fdepth hH.stream.initDepth hH.comp.noFrames)
    (anyImp _ _ hsat).sat_left).of_implies (anyImp _ _ hsat)

end

end VG.Proof.Pbkdf2.Md.AArch64.Any

end

end


/-!
# Merkle–Damgård hash functions on AArch64, as variants

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Variant.lean`): an `MdHash` is one
Merkle–Damgård hash function with one implementation of its compression
function, a variant of the interface `MdHash` on AArch64
(`Variants/MdHash/AArch64/`), and each function built on the hash function (in
`Generic/MdHash/AArch64/`) is emitted once for each of them: HMAC's `init` and
`finalize`, and PBKDF2's `iterate` and `pbkdf2`, named with the variant's
`suffix`.

`MdHash.of` builds one from what the proofs need of the hash function's
code (`HashOK`), what the kernel checks of the code HMAC and PBKDF2 add to
it (`CoreOK`, once for each hash function), and the satisfiability of the
shared contracts, which the kernel checks for each instance.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- One of the streaming functions made with an implementation of a hash
function's compression function, which `Generic/MdHash/AArch64/Stream.lean`
emits, naming it with the variant's suffix: its `Api` (in `Spec/`), and its
code, verified against the contract the `Api` gives it (`ofApi`, as
`Artifact.ofApi`) with `stack` bytes of stack, whose postcondition reads the
memory on return only within its buffers (`scrubOk`), so that it is
registered scrubbed whole (`StreamFn.reg`). -/
structure StreamFn where
  api : Api
  code : Prog AArch64.target.isa
  contract : Contract AArch64.target.isa
  stack : Nat := 0
  verified : Verified AArch64.target code contract
  ofSig : ∃ pre post leak,
      contract = api.sig.contract (AArch64.target.abi) pre post api.writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  ofApi : contract = api.contract AArch64.target.abi stack := by exact rfl
  spSafe : code.all (fun i => !AArch64.target.isa.writesSp i) = true
  scrubOk : AArch64.ScrubAll.ScrubAllOk contract stack (api.sig.retBits AArch64.abi.ptrBits)

/-- `f` as a registration of its `Api` (`Api.artifact`), as it is. -/
def StreamFn.reg₀ (f : StreamFn) : Registration f.api AArch64.target where
  consts := []
  tables := []
  code := f.code
  contract := f.contract
  stack := f.stack
  verified := f.verified
  ofApi := f.ofApi
  ofSig := f.ofSig
  spSafe := f.spSafe

/-- `f` as a registration of its `Api` (`Api.artifact`), returning with the
registers it may write cleared and its stack zeroed
(`AArch64.ScrubAll.withScrubAll`). -/
def StreamFn.reg (f : StreamFn) : Registration f.api AArch64.target :=
  AArch64.ScrubAll.withScrubAll f.reg₀ f.scrubOk

/-- The bytes of the frame in which HMAC's `init` and `finalize` (of
instance `I`) keep their working space, for their `_scratch` forms. -/
def hmacFrame (I : Spec.Hmac.Instance) : Nat := 8 * I.scratch

/-- The bytes of the frame in which HMAC's `init` for a key of any length (of
instance `I`) keeps its working space (`VG.Spec.Hmac.Instance.initAnyKeyScratch`
words), which it wipes before returning. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := 8 * I.initAnyKeyScratch

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`: for a key
of at most a block, `init_scratch` (`Hash.hmacInit`) in a frame holding its
working space; for a longer key (cold), `Hash.hmacInitAny`, in a frame
holding its larger working space, which it wipes. -/
def initCode (H : Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  Impl.Pbkdf2.Md.AArch64.initEntry I.S.H.blockSize
    (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacInit)
    (Impl.StackScratch.AArch64.withStackScratchWiped (anyFrame I) .x4 I.initAnyKeyScratch H.hmacInitAny)

/-- The bytes of the frame in which PBKDF2's `pbkdf2` (of instance `I`) keeps
its working space, for its `_scratch` form. -/
def pbkdf2Frame (I : Spec.Hmac.Instance) : Nat := 8 * I.pbkdf2Scratch

/-- A Merkle–Damgård hash function on AArch64, with one implementation of
its compression function: its functions, verified against the contracts of
its instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`). -/
structure MdHash where
  /-- The hash function's code and the names of its functions. -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  /-- What the proofs know of the hash function's code (for the callers that
  work at the level of its compression function: RSASSA-PSS's,
  `Generic/RsaPrivateCrt/AllMdHash/AArch64/RsaPss.lean`). -/
  ok : HashOK H
  /-- The hash function as RSA's padding takes it. -/
  mgf : MgfLink H ok
  hmacInit : Verified AArch64.target H.hmacInit (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16)
  hmacFin : Verified AArch64.target H.hmacFin (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16)
  iterate : Verified AArch64.target H.iterate (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi)
  pbkdf2 : Verified AArch64.target H.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16)
  /-- HMAC's `init` for a key of any length (`initEntry`): for a key of at
  most a block, `init_scratch` with its working space in a frame of its own;
  for a longer key, `hmacInitAny` with its working space in a frame of its
  own, wiped before returning; and `finalize` with its working space in a
  frame of its own (`hmacFin` is its `_scratch` form). -/
  hmacInitF : Verified AArch64.target (initCode H I) (I.initAnyKeyContract AArch64.abi (16 + anyFrame I))
  hmacFinF : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacFin)
    (I.finalizeContract AArch64.abi (16 + hmacFrame I))
  /-- PBKDF2's `pbkdf2` with its working space in a frame of its own
  (`pbkdf2` is its `_scratch` form). -/
  pbkdf2F : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch (pbkdf2Frame I) .x7 H.pbkdf2)
    (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I))
  /-- What the kernel checked of the code HMAC and PBKDF2 add to the hash
  function's (`CoreOK`), and that the instance's streaming hash function is
  the code's (its state's representation and its working space): what a
  function generic over the variant that calls HMAC's `_scratch` functions
  needs (deterministic ECDSA's, through a table of `Hmac`,
  `Proof/Ecdsa/Rfc6979/AArch64/Regs.lean`). -/
  C : CoreOK (core H)
  hSH : ok.SH = I.S
  hW : H.W = I.scratch
  /-- The state's representation is determined by its bytes (`Proof.Hmac.ReprLocal`). -/
  reprLocal : Proof.Hmac.ReprLocal I.S
  /-- The words of working space HMAC's `init` for a key of at most a block
  (`initW`) and its `finalize` (`finW`) use, of the `I.scratch` their shared
  contracts give them: those of the streaming functions they call, then our
  caller's registers and, for `finalize`, the inner digest
  (`Impl.Pbkdf2.Md.AArch64.Stream.buf`). -/
  initW : Nat
  finW : Nat
  /-- `init` for a key of at most a block and `finalize`, in frames of those
  sizes, and `init` for a longer key in its own (`initCode`'s branches). -/
  hmacShortR : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch (8 * initW) .x4 H.hmacInit)
    (I.initContract AArch64.abi (16 + 8 * initW))
  hmacFinR : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch (8 * finW) .x4 H.hmacFin)
    (I.finalizeContract AArch64.abi (16 + 8 * finW))
  hmacAnyF : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratchWiped (anyFrame I) .x4 I.initAnyKeyScratch H.hmacInitAny)
    (I.initAnyKeyContract AArch64.abi (16 + anyFrame I))
  /-- What the names of the functions emitted for it end with (nothing for
  the baseline implementation). -/
  suffix : String
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- The streaming `update` and `finalize` made with this implementation of
  the compression function, when no other variant shares them (otherwise
  they are in the hash function's registration file). -/
  stream : List StreamFn := []

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H))
  (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
include hH C hSH hW

theorem hmacInit_of (hs : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16) := by
  simp only [Proof.Hmac.Instance.initScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacInit_verified hH C hs

theorem hmacFin_of (hs : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16) := by
  simp only [Proof.Hmac.Instance.finalizeScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacFin_verified hH C hs

theorem iterate_of (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi) := by
  simp only [Proof.Pbkdf2.Instance.iterateContract, ← hSH, ← hW] at hs ⊢
  exact iterate_verified hH C hs

theorem pbkdf2_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s)
    (hs : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16).pre s) :
    Verified AArch64.target H.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16) := by
  simp only [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.Instance.finalizeScratchContract,
    Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.Instance.pbkdf2ScratchContract,
    Spec.Hmac.Instance.pbkdf2Scratch, ← hSH, ← hW, hH.hS] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C hsI hsF hsT hs

theorem hmacInitAny_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s) :
    Verified AArch64.target H.hmacInitAny (Any.anyScratchContract I.S I.initAnyKeyScratch) := by
  simp only [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, ← hSH, ← hW,
    hH.hS] at hsI hs ⊢
  exact Any.hmacInitAny_verified hH C A hsI hs

theorem hmacInitAnyF_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : 0 < I.initAnyKeyScratch ∧ I.initAnyKeyScratch < 512 ∧ I.initAnyKeyScratch % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)).pre s) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped (anyFrame I) .x4 I.initAnyKeyScratch H.hmacInitAny)
      (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := anyFrame I) (words := I.initAnyKeyScratch) (hmacInitAny_of hH C hSH hW A hsI hs)
    (by exact (by decide : 4 < 8)) (by simp only [anyFrame, Elem.size]; omega_arith) (by simp only [Elem.size]; omega_arith)
    (Proof.Hmac.initPostOut_local I.S _ hR (by
      rw [← hSH, hH.hS]; have := hH.N_le; have := hH.B_le
      omega_arith)) hsat

theorem hmacShortF_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0) (hR : Proof.Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.initContract AArch64.abi (16 + hmacFrame I)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacInit)
      (I.initContract AArch64.abi (16 + hmacFrame I)) :=
  AArch64.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S AArch64.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacInit_of hH C hSH hW hsI) (by exact (by decide : 4 < 8))
    (by simp only [hmacFrame, Elem.size]; omega_arith)
    (fun vs m m₁ m₂ r hl _ => Proof.Hmac.initPostOut_local I.S _ hR (by
      rw [← hSH, hH.hS]; have := hH.N_le; have := hH.B_le
      omega_arith) vs m m₁ m₂ r hl) hsat

theorem hmacInitF_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (hsIF : ∃ s, (I.initContract AArch64.abi (16 + hmacFrame I)).pre s)
    (hsA : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : 0 < I.initAnyKeyScratch ∧ I.initAnyKeyScratch < 512 ∧ I.initAnyKeyScratch % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S) (hB : I.S.H.blockSize < 2 ^ 16)
    (hsat : ∃ s, (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)).pre s) :
    Verified AArch64.target (initCode H I) (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)) :=
  initEntry_verified (hmacShortF_of hH C hSH hW hsI hs hR hsIF) (hmacInitAnyF_of hH C hSH hW A hsI hsA ha hR hsat)
    (by omega_arith) (by simp only [hmacFrame, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch]; omega_arith) hB hsat

theorem hmacFinF_of (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (hsat : ∃ s, (I.finalizeContract AArch64.abi (16 + hmacFrame I)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacFin)
      (I.finalizeContract AArch64.abi (16 + hmacFrame I)) :=
  AArch64.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacFin_of hH C hSH hW hsF) (by exact (by decide : 4 < 8))
    (by simp only [hmacFrame, Elem.size]; omega_arith)
    (fun vs m m₁ m₂ r hl _ => Proof.Hmac.finalizePostOut_local I.S _ vs m m₁ m₂ r hl) hsat

theorem pbkdf2F_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16).pre s)
    (hp : 0 < I.pbkdf2Scratch ∧ I.pbkdf2Scratch < 512 ∧ I.pbkdf2Scratch % 2 = 0)
    (hsat : ∃ s, (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (pbkdf2Frame I) .x7 H.pbkdf2)
      (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)) :=
  AArch64.Verified.stackScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S AArch64.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := pbkdf2Frame I) (pbkdf2_of hH C hSH hW hsI hsF hsT hsP) (by exact (by decide : 7 < 8))
    (by simp only [pbkdf2Frame, Elem.size]; omega_arith)
    (fun vs m m₁ m₂ r hl _ => Proof.Pbkdf2.pbkdf2PostOut_local I.S _ vs m m₁ m₂ r hl) hsat

omit hW in
/-- HMAC's `init` for a key of at most a block, in a frame of the `w` words
it uses (`HmacInit.verified`, whose working space may be any that holds its
buffers). -/
theorem hmacShortR_of {w : Nat} (hfit : H.stream.buf ≤ 8 * w) (hw : 0 < w ∧ w < 512 ∧ w % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S) (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S w AArch64.abi 16).pre s)
    (hsat : ∃ s, (I.initContract AArch64.abi (16 + 8 * w)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (8 * w) .x4 H.hmacInit)
      (I.initContract AArch64.abi (16 + 8 * w)) := by
  have hv : Verified AArch64.target H.hmacInit (Proof.Hmac.initScratchContract I.S w AArch64.abi 16) := by
    simp only [← hSH] at hsI ⊢
    exact (HmacInit.verified hH (HmacInit.Checks.of_core C.hinit) hfit (initImp _ _ hsI).sat_left).of_implies
      (initImp _ _ hsI)
  exact AArch64.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := w) (pre := Spec.Hmac.initPre I.S AArch64.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 8 * w) hv (by exact (by decide : 4 < 8)) (by simp only [Elem.size]; omega)
    (fun vs m m₁ m₂ r hl _ => Proof.Hmac.initPostOut_local I.S _ hR (by
      rw [← hSH, hH.hS]; have := hH.N_le; have := hH.B_le
      omega_arith) vs m m₁ m₂ r hl) hsat

omit hW in
/-- HMAC's `finalize`, in a frame of the `w` words it uses (`HmacFin.verified`). -/
theorem hmacFinR_of {w : Nat} (hfit : H.stream.buf + H.stream.F ≤ 8 * w) (hw : 0 < w ∧ w < 512 ∧ w % 2 = 0)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract I.S w AArch64.abi 16).pre s)
    (hsat : ∃ s, (I.finalizeContract AArch64.abi (16 + 8 * w)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (8 * w) .x4 H.hmacFin)
      (I.finalizeContract AArch64.abi (16 + 8 * w)) := by
  have hv : Verified AArch64.target H.hmacFin (Proof.Hmac.finalizeScratchContract I.S w AArch64.abi 16) := by
    simp only [← hSH] at hsF ⊢
    exact (HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) hfit (finImp _ _ hsF).sat_left).of_implies
      (finImp _ _ hsF)
  exact AArch64.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := w) (post := Spec.Hmac.finalizePost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 8 * w) hv (by exact (by decide : 4 < 8)) (by simp only [Elem.size]; omega)
    (fun vs m m₁ m₂ r hl _ => Proof.Hmac.finalizePostOut_local I.S _ vs m m₁ m₂ r hl) hsat

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it and the satisfiability of the shared contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (lk : MgfLink H hH)
    (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
    (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (A : Any.AnyOK (core H)) (hsA : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : 0 < I.initAnyKeyScratch ∧ I.initAnyKeyScratch < 512 ∧ I.initAnyKeyScratch % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S)
    (hsAF : ∃ s, (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)).pre s)
    (hsIF : ∃ s, (I.initContract AArch64.abi (16 + hmacFrame I)).pre s) (hB : I.S.H.blockSize < 2 ^ 16)
    (hsFF : ∃ s, (I.finalizeContract AArch64.abi (16 + hmacFrame I)).pre s)
    (hp : 0 < I.pbkdf2Scratch ∧ I.pbkdf2Scratch < 512 ∧ I.pbkdf2Scratch % 2 = 0)
    (hsPF : ∃ s, (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)).pre s)
    (initW finW : Nat) (hiw : H.stream.buf ≤ 8 * initW ∧ 0 < initW ∧ initW < 512 ∧ initW % 2 = 0)
    (hfw : H.stream.buf + H.stream.F ≤ 8 * finW ∧ 0 < finW ∧ finW < 512 ∧ finW % 2 = 0)
    (hsIR : ∃ s, (Proof.Hmac.initScratchContract I.S initW AArch64.abi 16).pre s)
    (hsIRF : ∃ s, (I.initContract AArch64.abi (16 + 8 * initW)).pre s)
    (hsFR : ∃ s, (Proof.Hmac.finalizeScratchContract I.S finW AArch64.abi 16).pre s)
    (hsFRF : ∃ s, (I.finalizeContract AArch64.abi (16 + 8 * finW)).pre s)
    (suffix : String) (features : List String) (stream : List StreamFn := []) : MdHash where
  H := H
  I := I
  ok := hH
  mgf := lk
  hmacInit := MdHash.hmacInit_of hH C hSH hW hsI
  hmacFin := MdHash.hmacFin_of hH C hSH hW hsF
  iterate := MdHash.iterate_of hH C hSH hW hsT
  pbkdf2 := MdHash.pbkdf2_of hH C hSH hW hsI hsF hsT hsP
  hmacInitF := MdHash.hmacInitF_of hH C hSH hW A hsI hs hsIF hsA ha hR hB hsAF
  hmacFinF := MdHash.hmacFinF_of hH C hSH hW hsF hs hsFF
  pbkdf2F := MdHash.pbkdf2F_of hH C hSH hW hsI hsF hsT hsP hp hsPF
  C := C
  hSH := hSH
  hW := hW
  reprLocal := hR
  initW := initW
  finW := finW
  hmacShortR := MdHash.hmacShortR_of hH C hSH hiw.1 hiw.2 hR hsIR hsIRF
  hmacFinR := MdHash.hmacFinR_of hH C hSH hfw.1 hfw.2 hsFR hsFRF
  hmacAnyF := MdHash.hmacInitAnyF_of hH C hSH hW A hsI hsA ha hR hsAF
  suffix := suffix
  features := features
  stream := stream

namespace MdHash

/-- `vg_pbkdf2_hmac_<hash>`'s postcondition reads the memory on return only
within `out` (`Proof.Pbkdf2.pbkdf2PostOut_local`). -/
theorem pbkdf2Ok (I : Spec.Hmac.Instance) :
    AArch64.ScrubAll.ScrubAllOk (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)) (16 + pbkdf2Frame I)
      (Spec.Pbkdf2.pbkdf2Sig.retBits AArch64.abi.ptrBits) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Pbkdf2.pbkdf2Sig) (W := 16 + pbkdf2Frame I) (by decide)
    (by omega) (Nat.le_refl _) (Proof.Pbkdf2.pbkdf2PostOut_local I.S _)

/-- `vg_pbkdf2_hmac_<hash>` with `v`, its working space in a frame of its own
(`pbkdf2F`), as it is. -/
def pbkdf2Reg₀ (v : MdHash) : Registration v.I.pbkdf2Api AArch64.target where
  suffix := v.suffix
  consts := []
  tables := []
  code := Impl.StackScratch.AArch64.withStackScratch (pbkdf2Frame v.I) .x7 v.H.pbkdf2
  contract := v.I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame v.I)
  stack := 16 + pbkdf2Frame v.I
  verified := v.pbkdf2F
  ofApi := rfl
  ofSig := by
    unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
    exact ⟨_, _, _, rfl⟩
  spSafe := Code.all_of_forall (fun _ => rfl) _

/-- `pbkdf2Reg₀`, returning with the registers it may write cleared and its
stack zeroed (`AArch64.ScrubAll.withScrubAll`): its many compressions dwarf
the zeroing of its frame. -/
def pbkdf2Reg (v : MdHash) : Registration v.I.pbkdf2Api AArch64.target :=
  AArch64.ScrubAll.withScrubAll v.pbkdf2Reg₀ (pbkdf2Ok v.I)

/-! ## HMAC's functions, scrubbed -/

/-- `vg_hmac_<hash>_finalize`'s postcondition reads the memory on return only
within `out` (`Proof.Hmac.finalizePostOut_local`). -/
theorem finOk (I : Spec.Hmac.Instance) (w : Nat) :
    AArch64.ScrubAll.ScrubAllOk (I.finalizeContract AArch64.abi (16 + 8 * w)) (16 + 8 * w)
      ((Spec.Hmac.finalizeSig I.S).retBits AArch64.abi.ptrBits) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Hmac.finalizeSig I.S) (W := 16 + 8 * w) (Nat.le_of_ble_eq_true rfl)
    (by omega) (Nat.le_refl _) (Proof.Hmac.finalizePostOut_local I.S _)

/-- `vg_hmac_<hash>_finalize` with `v`, in a frame of the `finW` words it uses, as it is. -/
def hmacFinReg₀ (v : MdHash) : Registration v.I.finalizeApi AArch64.target where
  suffix := v.suffix
  consts := []
  tables := []
  code := Impl.StackScratch.AArch64.withStackScratch (8 * v.finW) .x4 v.H.hmacFin
  contract := v.I.finalizeContract AArch64.abi (16 + 8 * v.finW)
  stack := 16 + 8 * v.finW
  verified := v.hmacFinR
  ofApi := rfl
  ofSig := by
    unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
    exact ⟨_, _, _, rfl⟩
  spSafe := Code.all_of_forall (fun _ => rfl) _

/-- `hmacFinReg₀`, returning with the registers it may write cleared and its
stack zeroed (`AArch64.ScrubAll.withScrubAll`). -/
def hmacFinReg (v : MdHash) : Registration v.I.finalizeApi AArch64.target :=
  AArch64.ScrubAll.withScrubAll v.hmacFinReg₀ (finOk v.I v.finW)

/-- `vg_hmac_<hash>_init`'s postcondition, under the contract of either
branch, reads the memory on return only within the two states
(`Proof.Hmac.initPostOut_local`). -/
theorem initShortOk (I : Spec.Hmac.Instance) (w : Nat) (hR : Proof.Hmac.ReprLocal I.S)
    (hS : I.S.stateBytes < 2 ^ 64) :
    AArch64.ScrubAll.ScrubAllOk (I.initContract AArch64.abi (16 + 8 * w)) (16 + 8 * w)
      ((Spec.Hmac.initSig I.S).retBits AArch64.abi.ptrBits) := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  exact AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Hmac.initSig I.S) (W := 16 + 8 * w) (Nat.le_of_ble_eq_true rfl)
    (by omega) (Nat.le_refl _) (Proof.Hmac.initPostOut_local I.S _ hR hS)

theorem initLongOk (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64) :
    AArch64.ScrubAll.ScrubAllOk (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)) (16 + anyFrame I)
      ((Spec.Hmac.initSig I.S).retBits AArch64.abi.ptrBits) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Hmac.initSig I.S) (W := 16 + anyFrame I) (Nat.le_of_ble_eq_true rfl)
    (by omega) (Nat.le_refl _) (Proof.Hmac.initPostOut_local I.S _ hR hS)

theorem stateBytes_lt (v : MdHash) : v.I.S.stateBytes < 2 ^ 64 := by
  rw [← v.hSH, v.ok.hS]; have := v.ok.N_le; have := v.ok.B_le
  omega_arith

/-- HMAC's `init` for a key of at most a block with `v`, in a frame of the
`initW` words it uses. -/
abbrev initShort (v : MdHash) : Prog isa :=
  Impl.StackScratch.AArch64.withStackScratch (8 * v.initW) .x4 v.H.hmacInit

/-- HMAC's `init` for a longer key with `v`, in its frame, which it wipes. -/
abbrev initLong (v : MdHash) : Prog isa :=
  Impl.StackScratch.AArch64.withStackScratchWiped (anyFrame v.I) .x4 v.I.initAnyKeyScratch v.H.hmacInitAny

/-- The result's bits of `vg_hmac_<hash>_init`. -/
abbrev initRb (v : MdHash) : Nat := (Spec.Hmac.initSig v.I.S).retBits AArch64.abi.ptrBits

/-- `vg_hmac_<hash>_init` with each branch scrubbed on its own
(`Impl.Residue.AArch64.scrubAll`): a key of at most a block, the common case,
zeroes only the frame of `initShort`, and a longer one, the frame of
`initLong`. -/
def initScrubbed (v : MdHash) : Prog isa :=
  Impl.Pbkdf2.Md.AArch64.initEntry v.I.S.H.blockSize
    (VG.Impl.Residue.AArch64.scrubAll (16 + 8 * v.initW) v.initRb (VG.Impl.Residue.AArch64.Clear.of v.initShort)
      v.initShort)
    (VG.Impl.Residue.AArch64.scrubAll (16 + anyFrame v.I) v.initRb (VG.Impl.Residue.AArch64.Clear.of v.initLong)
      v.initLong)

/-- What `hmacInitReg` needs of the code, which the emitter evaluates: as
`AArch64.ScrubAll.withScrubAll` asks of each branch. -/
def InitConds (v : MdHash) : Prop :=
  (0 < 16 + 8 * v.initW ∧ 16 + 8 * v.initW < 4096 ∧ (16 + 8 * v.initW) % 16 = 0) ∧
  (0 < 16 + anyFrame v.I ∧ 16 + anyFrame v.I < 4096 ∧ (16 + anyFrame v.I) % 16 = 0) ∧
  16 * v.initShort.aarch64Depth ≤ 16 + 8 * v.initW ∧ 16 * v.initLong.aarch64Depth ≤ 16 + anyFrame v.I ∧
  v.initShort.all (fun i => !i.writesDit) = true ∧ v.initLong.all (fun i => !i.writesDit) = true ∧
  AArch64.ScrubAll.noIcall v.initShort = true ∧ AArch64.ScrubAll.noIcall v.initLong = true ∧
  (v.initRb = 0 ∨ v.initRb = 32 ∨ v.initRb = 64) ∧ 8 * v.initW ≤ anyFrame v.I ∧
  v.I.S.H.blockSize < 2 ^ 16

instance (v : MdHash) : Decidable v.InitConds := by unfold InitConds; infer_instance

theorem noResidue_branch {c : Prog isa} {k : Contract isa} {W rb : Nat} (hv : Verified AArch64.target c k)
    (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hok : AArch64.ScrubAll.ScrubAllOk k W rb)
    (hd : 16 * c.aarch64Depth ≤ W) (hdit : c.all (fun i => !i.writesDit) = true)
    (hn : AArch64.ScrubAll.noIcall c = true) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    NoResidue (VG.Impl.Residue.AArch64.scrubAll W rb (VG.Impl.Residue.AArch64.Clear.of c) c) k rb :=
  AArch64.ScrubAll.noResidue_scrubAll (VG.Impl.Residue.AArch64.Clear.of_wf _)
    (VG.Impl.Residue.AArch64.Clear.of_keeps _) hv hW hok.sp hd hdit
    (fun _ _ _ n hn' => by rw [AArch64.ScrubAll.inames_of_noIcall hn] at hn'; cases hn') hrb

/-- `vg_hmac_<hash>_init` with `v`, each branch scrubbed (`initScrubbed`), if
`InitConds` holds; otherwise as it is (`initCode`, `hmacInitF`), without a
proof that it returns without residue. -/
def hmacInitReg (v : MdHash) : Registration v.I.initAnyKeyApi AArch64.target :=
  if h : v.InitConds then
    { suffix := v.suffix
      consts := []
      tables := []
      code := v.initScrubbed
      contract := v.I.initAnyKeyContract AArch64.abi (16 + anyFrame v.I)
      stack := 16 + anyFrame v.I
      verified := initEntry_verified
        (AArch64.ScrubAll.Verified.scrubAll (VG.Impl.Residue.AArch64.Clear.of_wf _) v.hmacShortR h.1 h.2.2.2.2.2.2.2.2.1
          (initShortOk v.I v.initW v.reprLocal v.stateBytes_lt))
        (AArch64.ScrubAll.Verified.scrubAll (VG.Impl.Residue.AArch64.Clear.of_wf _) v.hmacAnyF h.2.1 h.2.2.2.2.2.2.2.2.1
          (initLongOk v.I v.reprLocal v.stateBytes_lt))
        h.1.1 (by have := h.2.2.2.2.2.2.2.2.2.1; omega) h.2.2.2.2.2.2.2.2.2.2 v.hmacAnyF.2.2
      ofApi := rfl
      ofSig := by
        unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
        exact ⟨_, _, _, rfl⟩
      spSafe := Code.all_of_forall (fun _ => rfl) _
      residue := some ⟨initEntry_noResidue
        (noResidue_branch v.hmacShortR h.1 (initShortOk v.I v.initW v.reprLocal v.stateBytes_lt) h.2.2.1
          h.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1)
        (noResidue_branch v.hmacAnyF h.2.1 (initLongOk v.I v.reprLocal v.stateBytes_lt) h.2.2.2.1
          h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1)
        h.1.1 (by have := h.2.2.2.2.2.2.2.2.2.1; omega) h.2.2.2.2.2.2.2.2.2.2⟩ }
  else
    { suffix := v.suffix
      consts := []
      tables := []
      code := initCode v.H v.I
      contract := v.I.initAnyKeyContract AArch64.abi (16 + anyFrame v.I)
      stack := 16 + anyFrame v.I
      verified := v.hmacInitF
      ofApi := rfl
      ofSig := by
        unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
        exact ⟨_, _, _, rfl⟩
      spSafe := Code.all_of_forall (fun _ => rfl) _ }

end MdHash

end VG.Proof.Pbkdf2.Md.AArch64
