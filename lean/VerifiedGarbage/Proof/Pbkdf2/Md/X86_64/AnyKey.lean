module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Pbkdf2
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkLoop
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words

/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function on x86-64: correct

`initAny` (`Impl/Pbkdf2/Md/AnyKey/X86_64.lean`) saves our caller's
registers, makes the key as `pbkdf2` makes it from a password (hashing a key
longer than a block with the streaming functions, into `scratch`), calls
HMAC's `init` with it, and loads our caller's registers back. Each step is
`pbkdf2`'s (`Pbkdf2.lean`), for this function's arguments: `anyG` is the
contract the proof is written against.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Any

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat)
open VG.Proof.Pbkdf2.Md.X86_64.Pbk (PSizes layout end_le L_lt InitArgs hinit_call hash_len blockKey_hash eregs)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey)

/-! ## The contract -/

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length, with
`8 W` bytes of scratch space and calls two deep below its own:
`VG.Spec.Hmac.initAnyKeyContract` with its working space as an argument. -/
def anyG (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    S.Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev key : Addr := s₀.gpr .rdx
abbrev kln : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev keyR : Region := ⟨key s₀, kln s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 24, 24⟩
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
/-- Where our caller's registers are saved. -/
abbrev hdrR : Region := sR s₀ H.sv 48
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
  ret_i : (retR s₀).Disjoint (innR H s₀)
  ret_o : (retR s₀).Disjoint (outR H s₀)
  ret_s : (retR s₀).Disjoint (scR H s₀)
  stk_i : (stkR s₀).Disjoint (innR H s₀)
  stk_o : (stkR s₀).Disjoint (outR H s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR H s₀)
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (anyG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have hS := hH.hS
  simp only [hS, Nat.mul_comm 8] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

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

include hp hz in
theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) :
    InRegions s.wr (A s₀ o) n := by
  have := L_lt hz
  exact ⟨scR H s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega_using [h, this])⟩

include hp in
theorem sc_mem : scR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  fun x h₁ h₂ => Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by omega_using []) x h₂ h₁

theorem below_stk {n : Nat} (hn : n ≤ 24) : Region.Sub (below (s₀.gpr .rsp) n) (stkR s₀) :=
  below_sub hn (by omega_using [])

include hz in
/-- The header, after the working space of the functions we call and before
the parts `pbkdf2`'s code writes. -/
theorem hdr_disj {o n : Nat} (h₁ : H.st0O ≤ o) (h₂ : o + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (hdrR H s₀) (sR s₀ o n) := by
  have e : H.st0O = H.sv + 64 := rfl
  have := hz.o_sv_64_le_L
  exact part_disj hz (Or.inl (by omega_using [h₁, e])) (by omega_using [this]) h₂

include hz in
theorem hdr_low : Region.Disjoint (hdrR H s₀) (lowR H s₀) := by
  have := hz.o_sv_64_le_L
  exact low_disj hz hz.o_W8_le_sv (by omega_using [this])

include hz in
theorem hdr_sub : Region.Sub (hdrR H s₀) (scR H s₀) := by
  have := hz.o_sv_64_le_L
  exact part_sub (by omega_using [this])

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's
registers, saved in `scratch`, and everything written is in a state,
`scratch` or the stack. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  frame : Frame [innR H s₀, outR H s₀, scR H s₀, stkR s₀] s₀.mem s.mem

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR H s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [innR H s₀, outR H s₀, scR H s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' := by
  have hs : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H.hh (scr s₀)) (hdrR H s₀) :=
    Region.sub_prefix (Nat.le_refl _)
  exact ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, h15.trans h.r15,
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left hs, h.frame.trans (hf.sub hsub)⟩

/-- What a call leaves, writing the states, parts of `scratch` after its
header, or its working space, and the stack below `rsp`. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, r = innR H s₀ ∨ r = outR H s₀ ∨ (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  refine h.keep hrd hwr (hcs _ (by simp [calleeSaved])) (hcs _ (by simp [calleeSaved])) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (hp.i_s.sub_right (hdr_sub hz)).symm
      · exact (hp.o_s.sub_right (hdr_sub hz)).symm
      · exact (hdr_low hz).sub_right (Region.sub_prefix hk)
      · exact hdr_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ((hp.stk_s.sub_left (below_stk hn)).sub_right (hdr_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨_, by simp, Region.sub_prefix (Nat.le_refl _)⟩
      · exact ⟨_, by simp, Region.sub_prefix (Nat.le_refl _)⟩
      · exact ⟨scR H s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega_using [hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ⟨_, by simp, below_stk hn⟩

omit hz in
theorem KR.keyBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (key s₀) (kln s₀) = bytesAt s₀.mem (key s₀) (kln s₀) :=
  bytes_keep h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.stk_k.symm) (Nat.le_of_lt (s₀.gpr .rcx).isLt)

omit hz in
theorem KR.ret {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
  h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_i
    · exact hp.ret_o
    · exact hp.ret_s
    · exact stk_ret.symm) (by decide)

end

/-! ## The entry -/

/-- What the entry sets up, kept until HMAC's `init` is called. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  rbx : s.gpr .rbx = key s₀
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = inn s₀
  r13 : s.gpr .r13 = out s₀

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem entry_ok : WP isa (.block H.anyEntry) s₀ fun s => KE (H := H) s₀ s ∧
    s.cf = some (decide (kln s₀ < H.P.B + 1)) := by
  have hW := hz.W
  simp only [Hash.anyEntry]
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.save_ok H.hh (scr := scr s₀) rfl hW (L := (H.W + H.S) * 8)
    (sc_mem hp) (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)
    fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ =>
    wp_mov fun s₅ u₅ _ _ => wp_mov fun s₆ u₆ _ _ => wp_cmpi fun s₇ g₇ m₇ rd₇ wr₇ c₇ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₇.gpr r = s₀.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [g₇, u₆.other r h₅, u₅.other r h₄, u₄.other r h₃, u₃.other r h₂, u₂.other r h₁, g₁]
  have m₇' : s₇.mem = s₁.mem := by rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨⟨by rw [rd₇, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
    by rw [wr₇, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    g _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁],
    m₇' ▸ sv₁,
    m₇' ▸ f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR H s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)⟩⟩,
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  · rw [g₇, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  · rw [g₇, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  · rw [c₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁, sx_ofNat (by exact hz.o_B_1_lt_p31),
      toNat_ofNat_lt (by exact hz.o_B_1_lt_p64)]

end

/-! ## Helpers -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h) (fun _ h => by simp at h)

theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ≠ .r15 ∧ d ≠ .rsp) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr (u.other _ hd.2.symm) (u.other _ hd.1.symm) u.mem

/-- `d ← scratch + o`. -/
theorem scr_ok {s : State} {d : Reg} (h15 : s.gpr .r15 = scr s₀) {o : Nat} (ho : o < 2 ^ 31)
    {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' d (A s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, h15, sx_ofNat ho]

theorem stk_sub {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below (s.gpr .rsp) n) (stkR s₀) := by
  rw [h.rsp]; exact below_stk hn

include hp in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) {R : Region}
    (hR : Region.Sub R (scR H s₀)) : (below (s.gpr .rsp) n).Disjoint R :=
  (hp.stk_s.sub_left (stk_sub h hn)).sub_right hR

include hp in
theorem in_wr {s : State} (h : KR (H := H) s₀ s) : scR H s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

include hp in
theorem cov_part {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (in_wr hp h) hon

include hp in
theorem cov_low {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (in_wr hp h) hn

theorem KE.upd {s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, by rw [u.other _ (ne _ (by simp)), h.rbx],
    by rw [u.other _ (ne _ (by simp)), h.rbp], by rw [u.other _ (ne _ (by simp)), h.r12],
    by rw [u.other _ (ne _ (by simp)), h.r13]⟩

include hp hz in
theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz hrd hwr hcs hn hf fun r hr => .inr (.inr (hw r hr)),
    by rw [hcs _ (by simp [calleeSaved]), h.rbx],
    by rw [hcs _ (by simp [calleeSaved]), h.rbp], by rw [hcs _ (by simp [calleeSaved]), h.r12],
    by rw [hcs _ (by simp [calleeSaved]), h.r13]⟩

end

/-! ## The key

As `pbkdf2`'s (`Pbk.key_ok`), for the key and its length in `rbx` and `rbp`. -/

/-- The key HMAC's `init` gets: the key, or the digest of a key longer than a
block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = key s₀ ∧ kl = kln s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (key s₀) (kln s₀))

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO := by
  rw [← List.append_nil (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)]
  exact scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), u₁.gpr⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdi : s.gpr .rdi = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] :=
  VG.Proof.Pbkdf2.Md.X86_64.Calls.init_call hH.stream (st := A s₀ H.stWO) hdi
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    (stk_sc hp h.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))) fun s₂ a₂ r₂ =>
      ⟨h.call hp hz a₂.rd a₂.wr a₂.cs (by decide) a₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the key. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stWO) (key s₀) (scr s₀) (kln s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbx]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbp]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₇.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₇.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp k₇.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right
        (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.k_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.k_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := stk_sc hp k₇.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := (hp.stk_k.sub_left (stk_sub k₇.kr (by decide)))
      stk_sc := stk_sc hp k₇.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (key s₀) (scr s₀) (kln s₀))
    (hsi : s.gpr .rsi = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua
    (Nat.le_of_lt (s₀.gpr .rcx).isLt) fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈.rd a₈.wr a₈.cs (by decide) a₈.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · have := r₈ [] hr hsi
    rwa [List.nil_append, h.kr.keyBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀))) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .rsi = s₀.gpr .rcx ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ _ _ => ?_
  refine scr_ok (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]) (by exact hz.o_hkO_lt_p31)
    fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  have k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.rbp], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { rdi := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
      rdx := by rw [u₁₂.other _ (by decide), u₁₁.gpr]
      rcx := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₁₂.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_part hp k₁₂.kr (by rw [hF]; exact hz.o_hkO_N_le_L)
        · exact cov_low hp k₁₂.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L)
        (by rw [hF]; exact hz.o_hkO_N_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right
        (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by rw [hF]; exact hz.o_hkO_N_le_L)).sub_right
        (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      stk_st := stk_sc hp k₁₂.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := stk_sc hp k₁₂.kr (by decide) (part_sub (by rw [hF]; exact hz.o_hkO_N_le_L))
      stk_sc := stk_sc hp k₁₂.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hsi : s.gpr .rsi = s₀.gpr .rcx) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃.rd a₁₃.wr a₁₃.cs (by decide) a₁₃.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by rw [hF]; exact hz.o_hkO_N_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · rw [bytesAt_take _ _ hD.2.1]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .rcx).isLt)
      (by rw [hsi, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧ t.mem = s.mem := by
  refine scr_ok h.kr.r15 (by exact hz.o_hkO_lt_p31) fun s₁₄ u₁₄ => wp_mov32i fun s₁₅ u₁₅ _ _ => WP.block_nil ?_
  exact ⟨(h.upd u₁₄ (by decide)).upd u₁₅ (by decide), by rw [u₁₅.other _ (by decide), u₁₄.gpr],
    by rw [u₁₅.gpr, zx_ofNat (by exact hz.o_D_lt_p32),
      toNat_ofNat_lt (by exact hz.o_D_lt_p64)], by rw [u₁₅.mem, u₁₄.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if kln s₀ < H.P.B + 1 then key s₀ else A s₀ H.hkO
abbrev kl (H : Hash) (s₀ : State) : Nat := if kln s₀ < H.P.B + 1 then kln s₀ else H.D

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hcf : s.cf = some (decide (kln s₀ < H.P.B + 1))) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = kp H s₀ ∧ (t.gpr .rcx).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  unfold Hash.key
  refine WP.ite (!decide (kln s₀ < H.P.B + 1)) (by simp [eval, hcf]) (fun hT => ?_) fun hF => ?_
  · have hlong : ¬ kln s₀ < H.P.B + 1 := of_decide_eq_false (Bool.not_eq_true' _ ▸ hT)
    have e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    have e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    rw [e₁, e₂]
    refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, rdx, rcx, hb⟩ =>
      ⟨k, rdx, rcx, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
    rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega)]
  · have hshort : kln s₀ < H.P.B + 1 := of_decide_eq_true (by simpa using hF)
    have e₁ : kp H s₀ = key s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    have e₂ : kl H s₀ = kln s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    rw [e₁, e₂]
    refine wp_mov fun t₁ u₁ _ _ => wp_mov fun t₂ u₂ _ _ => WP.block_nil ?_
    refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.rbx],
      by rw [u₂.gpr, u₁.other _ (by decide), h.rbp], ⟨.inl ⟨rfl, rfl⟩, by omega, ?_⟩⟩
    rw [u₂.mem, u₁.mem, h.kr.keyBytes hp]

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ (innR H s₀) ∧
      Region.Disjoint ⟨kp, kl⟩ (outR H s₀) ∧ Region.Disjoint ⟨kp, kl⟩ (lowR H s₀) ∧
      (below (s.gpr .rsp) 24).Disjoint ⟨kp, kl⟩ := by
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.k_i, hp.k_o, hp.k_s.sub_right low_sub, hp.stk_k.sub_left (stk_sub h (Nat.le_refl _))⟩
  · refine ⟨Covers.of_sub fun r hr => ?_,
      (hp.i_s.sub_right (part_sub (by exact hz.o_hkO_D_le_L))).symm,
      (hp.o_s.sub_right (part_sub (by exact hz.o_hkO_D_le_L))).symm,
      low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      stk_sc hp h (Nat.le_refl _) (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-! ## HMAC's `init` -/

/-- HMAC's `init`'s arguments: the two states, the key and the working space. -/
theorem args_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdx : s.gpr .rdx = kp H s₀)
    (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block Hash.anyArgs) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (inn s₀) (out s₀) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hsnw := hp.snw
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { rdi := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r12]
      rsi := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r13]
      rdx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdx]
      rcx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
      r8 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r15]
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
      stk_i := hp.stk_i.sub_left (stk_sub k₃.kr (Nat.le_refl _))
      stk_o := hp.stk_o.sub_left (stk_sub k₃.kr (Nat.le_refl _))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr (Nat.le_refl _) low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega }

/-- `K₀`, the key padded to a block (or its digest, if longer). -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (key s₀) (kln s₀))

/-- HMAC's `init`: the states. -/
theorem call_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (inn s₀) (out s₀) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KR (H := H) s₀ t ∧
      hH.SH.Repr t.mem (inn s₀) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (out s₀) (xorPad (K0 hH s₀) opad) := by
  refine hinit_call hH hI hIsp hId ia fun s₄ rd₄ wr₄ cs₄ f₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.kr.call hp hz rd₄ wr₄ cs₄ (Nat.le_refl _) f₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl ⟨_, rfl, Nat.le_refl _⟩))
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-! ## The function -/

theorem correct (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) :
    WP isa H.hmacInitAny s₀ fun s' => gprPreserved s₀ s' ∧ (anyG hH.SH (H.W + H.S)).post s₀ s' := by
  have hW := hz.W
  unfold Hash.hmacInitAny
  refine WP.seq (WP.mono (entry_ok hp hz) fun s₁ ⟨k₁, cf⟩ => ?_)
  refine WP.seq (WP.mono (key_ok hp hz hH k₁ cf) fun s₂ ⟨k₂, dx₂, cx₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (args_ok hp hz hH k₂ dx₂ cx₂ ka) fun s₃ ⟨k₃, a₃, h₃⟩ => ?_)
  refine WP.seq (WP.mono (call_ok hp hz hH hI hIsp hId k₃ a₃ h₃) fun s₄ ⟨k₄, i₄, o₄⟩ => ?_)
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.restore_ok H.hh k₄.r15 hW k₄.saved (in_wr hp k₄)
    (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L))
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₄.ret hp]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₄.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  · show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
    rw [hm]; exact ⟨i₄, o₄⟩

end

end VG.Proof.Pbkdf2.Md.X86_64.Any
