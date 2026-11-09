module

public import VerifiedGarbage.Impl.MdStream.Arm.Digest
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.MdStream.DigestScratch
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the generic proof, which builds in parallel with the proofs of the hash functions that its instances (`DigestInstances.lean`) import

/-!
# The one-shot digest over any streaming hash function on 32-bit ARM: correct

`digestMain` (`Impl/MdStream/Arm/Digest.lean`) saves our caller's registers
in `scratch` (`prologue_ok`), hashes the message with the streaming `init`,
`update` and `finalize` into `scratch`, through their contracts
(`init_call`, `upd_frame`, `fin_frame`), as HMAC's `init` hashes a long key
(`Proof/Pbkdf2/Whole/Arm/AnyKey.lean`), copies the digest to `out`
(`copy_ok`), and loads our caller's registers back (`restore_ok`).
`digestScratch` is the contract it is verified against:
`VG.Spec.Sha256.digestContract` with its working space as a last argument, in
`r3`, and 16 bytes of stack (the frames of the calls).
-/

@[expose] public section

namespace VG.Proof.MdStream.Arm.Digest

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)
open VG.Impl.MdStream.Arm.Digest (stO dgO dbytes prologue updArgs digestMain digest)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK After below init_call fin_frame FinArgs SavedRegs saveR
  savedRegs copy_ok Copied cclob)
open VG.Proof.Pbkdf2.Whole.Arm (UpdL upd_frame)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take add_ofNat_add bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt digestSig digestPost)

/-! ## The contract -/

/-- `Spec.Sha256.digestContract` with a last argument, `scratch`, of `n`
64-bit words, and 16 bytes of stack. -/
def digestScratch (D : Nat) (hash : List Byte → List Byte) (n : Nat) : Contract isa :=
  Sig.scratchContract Arm.abi (digestSig D) "scratch" .u64 n (Curry.const (fun _ => True) _)
    (digestPost D hash Arm.abi.ptrBits) false 16

/-- The 64-bit words of `scratch`. -/
abbrev nw (H : Hash) : Nat := dbytes H / 8

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev dp : BitVec 32 := s₀.gpr .r0
abbrev dl : Nat := (s₀.gpr .r1).toNat
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev dR : Region := ⟨State.addr (dp s₀), dl s₀⟩
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := State.addr (scr s₀) + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨State.addr (scr s₀), k⟩
/-- The message. -/
abbrev M : List Byte := bytesAt s₀.mem (State.addr (dp s₀)) (dl s₀)

end

section
variable (H : Hash) (s₀ : State)
abbrev oR : Region := ⟨State.addr (op s₀), H.D⟩
abbrev scR : Region := ⟨State.addr (scr s₀), nw H * 8⟩
/-- The save area of our caller's registers. -/
abbrev svR : Region := saveR H (scr s₀)
end

/-- The precondition. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [oR H s₀, scR H s₀]
  d_o : (dR s₀).Disjoint (oR H s₀)
  d_s : (dR s₀).Disjoint (scR H s₀)
  o_s : (oR H s₀).Disjoint (scR H s₀)
  b_d : (below s₀).Disjoint (dR s₀)
  b_o : (below s₀).Disjoint (oR H s₀)
  b_s : (below s₀).Disjoint (scR H s₀)
  nd : (dp s₀).toNat + dl s₀ ≤ 2 ^ 32
  no : (op s₀).toNat + H.D ≤ 2 ^ 32
  nsc : (scr s₀).toNat + nw H * 8 ≤ 2 ^ 32

theorem pre_of {H : Hash} {hash : List Byte → List Byte} {s₀ : State}
    (h : (digestScratch H.D hash (nw H)).pre s₀) : Pre H s₀ := by
  sig_pre [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := h
  exact ⟨h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Lay (H : Hash) : Prop where
  W : H.W ≤ 64
  S : 0 < H.S ∧ H.S ≤ 256
  D : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64
  buf : H.buf = 8 * H.W + 36
  fit : H.buf + H.S + H.F ≤ nw H * 8
  reach : nw H * 8 ≤ 4096

theorem lay {H : Hash} (hH : HashOK H) : Lay H := by
  have := hH.hW; have := hH.hSB; have := hH.hDF; have := hH.hF
  refine ⟨hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩, rfl, ?_, ?_⟩ <;>
    simp only [nw, dbytes, Hash.buf] <;> omega

variable {H : Hash}

section
variable {s₀ : State} (hp : Pre H s₀) (hz : Lay H)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < nw H * 8) : State.addr (dO s₀ o) = A s₀ o := by
  have := hp.nsc; exact addr_add (by omega_arith)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < nw H * 8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ nw H * 8) : Region.Sub (sR s₀ o n) (scR H s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ nw H * 8) (hb : b + n ≤ nw H * 8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := hz.reach; exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ nw H * 8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := hz.reach; exact Offset.base_disjoint _ hk (by omega_arith)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ nw H * 8) : Region.Sub (lowR s₀ k) (scR H s₀) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR H s₀) (scR H s₀) := by
  have := hz.fit; have := hz.buf
  exact Offset.sub_base _ (by omega_arith)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : H.buf ≤ o) (hon : o + n ≤ nw H * 8) : (svR H s₀).Disjoint (sR s₀ o n) := by
  have := hz.reach; have := hz.buf
  exact Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * H.W) : (svR H s₀).Disjoint (lowR s₀ k) := by
  have := hz.reach; have := hz.fit; have := hz.buf
  exact (Offset.base_disjoint _ (k := k) (e := 8 * H.W) (n := 36) hk (by omega_arith)).symm

omit hz in
theorem sc_mem : scR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

omit hz in
theorem o_mem : oR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the prologue on. -/
structure KR (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = op s₀
  r8 : s.gpr .r8 = dp s₀
  r9 : s.gpr .r9 = s₀.gpr .r1
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame [scR H s₀, below s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r5, .r8, .r9, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {s₀ s s' : State}

theorem KR.belowE (h : KR H s₀ s) : below s = below s₀ := by simp only [below, h.sp]

/-- `KR` survives changes to other registers, and to memory in `scratch`
(away from the save area) and the stack. -/
theorem KR.keep (h : KR H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR H s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ [scR H s₀, below s₀], Region.Sub r r') :
    KR H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r8,
    (hg _ (by simp)).trans h.r9, (hg _ (by simp)).trans h.r11, h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same (h : KR H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR H s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd (h : KR H s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32} (u : Upd s s' d v) : KR H s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- What a call leaves, writing the working space or parts of `scratch`
after the save area, and the stack below the stack pointer. -/
theorem KR.call (hp : Pre H s₀) (hz : Lay H) (h : KR H s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = lowR s₀ k ∧ k ≤ 8 * H.W) ∨
      ∃ o n, r = sR s₀ o n ∧ H.buf ≤ o ∧ o + n ≤ nw H * 8) : KR H s₀ s' := by
  have hf := hz.fit; have hb := hz.buf
  have f := ha.frame
  rw [h.belowE] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact sv_low hz hk
      · exact sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨scR H s₀, by simp, low_sub (by omega_arith)⟩
      · exact ⟨scR H s₀, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

theorem KR.dataBytes (hp : Pre H s₀) (hk : KR H s₀ s) :
    bytesAt s.mem (State.addr (dp s₀)) (dl s₀) = M s₀ :=
  bytes_keep hk.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_s
    · exact hp.b_d.symm) (by have := hp.nd; omega_arith)

/-- A part of `scratch` is in a region the code may write. -/
theorem cov_part (hp : Pre H s₀) (hk : KR H s₀ s) {o n : Nat} (h : o + n ≤ nw H * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR H s₀, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

theorem cov_low (hp : Pre H s₀) (hk : KR H s₀ s) {k : Nat} (h : k ≤ nw H * 8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR H s₀, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

end

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` and `r12` changed. -/
structure Upd12 (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → r ≠ .r12 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem KR.upd12 {s₀ s s' : State} (h : KR H s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd12 s s' d v) : KR H s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r (fun e => hd (e ▸ hr)) (by
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) u.mem

/-- `d ← r11 + o` (through `r12`). -/
theorem scr_ok {s : State} {d : Reg} {o : Nat} (ho : o < 2 ^ 16) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd12 s s' d (s.gpr .r11 + BitVec.ofNat 32 o) → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ => wp_add (op2_reg _ _)
    fun s₂ u₂ => k s₂ ⟨?_, fun r h₁ h₂ => by rw [u₂.other r h₁, u₁.other r h₂], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), Pbkdf2.Stream.Arm.movw_ofNat ho]

theorem zero_append (x : BitVec 32) : (0 : BitVec 32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  have := x.isLt
  simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
  omega_arith

/-! ## The pieces -/

section
variable {s₀ : State} (hp : Pre H s₀) (hz : Lay H)
include hp hz

/-- After the prologue: `KR`, and the streaming state's address in `r4`. -/
abbrev K4 (H : Hash) (s₀ s : State) : Prop := KR H s₀ s ∧ s.gpr .r4 = dO s₀ (stO H)

theorem prologue_ok : WP isa (.block (prologue H)) s₀ (K4 H s₀) := by
  have hf := hz.fit; have hb := hz.buf; have hr := hz.reach
  simp only [prologue, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  refine Pbkdf2.Stream.Arm.save_ok H (scr := scr s₀) (L := nw H * 8) u₁.gpr hz.W (by rw [u₁.wr]; exact sc_mem hp)
    (by omega_arith) hp.nsc fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  rw [← List.append_nil (scrAt .r4 (stO H))]
  refine scr_ok (show stO H < 2 ^ 16 by simp only [stO]; omega_arith) fun s₇ u₇ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have e11 : s₆.gpr .r11 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide) (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), e₂ _ (by decide)]
  · rw [u₇.other _ (by decide) (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), e₂ _ (by decide)]
  · rw [u₇.other _ (by decide) (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), e₂ _ (by decide)]
  · rw [u₇.other _ (by decide) (by decide), e11]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
    exact SavedRegs.of_eq H sv₂ fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR H s₀, by simp, sv_sub hz⟩
  · rw [u₇.gpr, e11]

omit hp hz in
/-- `r0 ← r4`, before `init`. -/
theorem init1_ok {s : State} (hk : K4 H s₀ s) :
    WP isa (.block [.mov .r0 (.reg .r4)]) s fun t => K4 H s₀ t ∧ t.gpr .r0 = dO s₀ (stO H) := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ⟨⟨hk.1.upd (by decide) u₁, ?_⟩, ?_⟩
  · rw [u₁.other _ (by decide), hk.2]
  · rw [u₁.gpr, hk.2]

/-- After `init`: the streaming state represents the empty message. -/
abbrev KI (hH : HashOK H) (s₀ s : State) : Prop := K4 H s₀ s ∧ hH.SH.Repr s.mem (A s₀ (stO H)) []

variable (hH : HashOK H)
include hH

omit hp hH in
theorem stO_S : stO H + H.S ≤ nw H * 8 := by
  have := hz.fit; have := hz.D; simp only [stO]; omega_arith

omit hp hH in
theorem dgO_F : dgO H + H.F ≤ nw H * 8 := by
  have := hz.fit; simp only [dgO]; omega_arith

/-- `init` on the streaming state. -/
theorem init2_ok {s : State} (hk : K4 H s₀ s) (h0 : s.gpr .r0 = dO s₀ (stO H)) :
    WP isa (.call H.initN H.initC) s (KI hH s₀) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have cw : Covers [⟨State.addr (dO s₀ (stO H)), H.S⟩] s.wr := by
    rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk.1 hl
  refine init_call hH (st := dO s₀ (stO H)) h0 (by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith)
    cw fun s' a r => ?_
  refine ⟨⟨hk.1.call hp hz a fun r hr => ?_, ?_⟩, by rw [← ea]; exact r⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr ⟨_, _, by rw [ea], by simp only [stO]; omega_arith, hl⟩
  · rw [a.cs _ (by decide) (by decide), hk.2]

omit hp hz in
/-- `update`'s arguments: the message. -/
theorem upd1_ok {s : State} (hk : KI hH s₀ s) :
    WP isa (.block updArgs) s fun t => KI hH s₀ t ∧ t.gpr .r0 = dO s₀ (stO H) ∧ t.gpr .r1 = dp s₀ ∧
      t.gpr .r7 = s₀.gpr .r1 ∧ t.gpr .r10 = scr s₀ ∧ Pbkdf2.Stream.Arm.count t = BitVec.ofNat 64 0 := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide))
    fun s₆ u₆ => WP.block_nil ?_
  have k₆ := (((((hk.1.1.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
    (by decide) u₅).upd (by decide) u₆
  refine ⟨⟨⟨k₆, ?_⟩, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hk.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.1.2]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hk.1.2]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), hk.1.1.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hk.1.1.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hk.1.1.r11]
  · simp only [Pbkdf2.Stream.Arm.count]; rw [u₆.gpr, u₆.other .r2 (by decide), u₅.gpr]; rfl

theorem upd_args {s : State} (hk : KR H s₀ s) (h0 : s.gpr .r0 = dO s₀ (stO H)) (h1 : s.gpr .r1 = dp s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r1) (h10 : s.gpr .r10 = scr s₀) :
    UpdL hH s (dO s₀ (stO H)) (dp s₀) (scr s₀) (dl s₀) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf; have := hH.hWb; have := hz.fit
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have hst : Region.Sub ⟨State.addr (dO s₀ (stO H)), H.S⟩ (scR H s₀) := by rw [ea]; exact part_sub hl
  have hlo : Region.Sub (lowR s₀ hH.Wb) (scR H s₀) := low_sub (by omega_arith)
  have hb16 : Region.Sub (below s) (below s₀) := by rw [hk.belowE]; exact fun _ h => h
  exact
    { r0 := h0
      r1 := h1
      r7 := by rw [h7]; simp
      r10 := h10
      hlen := (s₀.gpr .r1).isLt
      sp16 := by rw [hk.sp]; exact hp.sp16
      cd := Pbkdf2.Stream.Arm.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk hl
          · exact cov_low hp hk (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by simp only [stO]; omega_arith) hl).symm
      d_st := hp.d_s.sub_right hst
      d_sc := hp.d_s.sub_right hlo
      b_st := (hp.b_s.sub_left hb16).sub_right hst
      b_d := hp.b_d.sub_left hb16
      b_sc := (hp.b_s.sub_left hb16).sub_right hlo
      nst := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      nd := hp.nd
      nsc := by have := hp.nsc; omega_arith }

/-- After `update`: the streaming state represents the message. -/
abbrev KU (hH : HashOK H) (s₀ s : State) : Prop := K4 H s₀ s ∧ hH.SH.Repr s.mem (A s₀ (stO H)) (M s₀)

theorem upd2_ok {s : State} (hk : KI hH s₀ s) (h0 : s.gpr .r0 = dO s₀ (stO H)) (h1 : s.gpr .r1 = dp s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r1) (h10 : s.gpr .r10 = scr s₀) (hc : Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 0) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call H.updN H.updC) (.pop .r1 16)) s (KU hH s₀) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf; have := hH.hWb
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  refine upd_frame hH (upd_args hp hz hH hk.1.1 h0 h1 h7 h10) fun s' a r => ⟨⟨hk.1.1.call hp hz a
    fun r hr => ?_, by rw [a.cs _ (by decide) (by decide), hk.1.2]⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by simp only [stO]; omega_arith, hl⟩
    · exact .inl ⟨_, rfl, hH.hWb⟩
  · have := r [] (by rw [ea]; exact hk.2) hc
    rwa [List.nil_append, ea, hk.1.1.dataBytes hp] at this

omit hp hz in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem fin1_ok {s : State} (hk : KU hH s₀ s) (ho : dgO H < 2 ^ 16) :
    WP isa (.block (([.mov .r0 (.reg .r4)] : List Instr) ++ ([.mov .r2 (.reg .r9), .mov .r3 (.imm 0)] : List Instr) ++
      scrAt .r1 (dgO H) ++
      ([.mov .r12 (.reg .r11)] : List Instr))) s fun t =>
        KU hH s₀ t ∧ t.gpr .r0 = dO s₀ (stO H) ∧ t.gpr .r1 = dO s₀ (dgO H) ∧
        t.gpr .r12 = scr s₀ ∧ Pbkdf2.Stream.Arm.count t = BitVec.ofNat 64 (dl s₀) := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_imm (by decide))
    fun s₃ u₃ => ?_
  have k₃ := ((hk.1.1.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine scr_ok ho fun s₄ u₄ => ?_
  have k₄ := k₃.upd12 (by decide) u₄
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have k₅ := k₄.upd (by decide) u₅
  have e9 : s₁.gpr .r9 = s₀.gpr .r1 := by rw [u₁.other _ (by decide), hk.1.1.r9]
  refine ⟨⟨⟨k₅, ?_⟩, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hk.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.1.2]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hk.1.2]
  · rw [u₅.other _ (by decide), u₄.gpr, k₃.r11]
  · rw [u₅.gpr, k₄.r11]
  · simp only [Pbkdf2.Stream.Arm.count]
    rw [u₅.other .r3 (by decide), u₅.other .r2 (by decide), u₄.other .r3 (by decide) (by decide),
      u₄.other .r2 (by decide) (by decide), u₃.gpr, u₃.other .r2 (by decide), u₂.gpr, e9, zero_append]

theorem fin_args {s : State} (hk : KR H s₀ s) (h0 : s.gpr .r0 = dO s₀ (stO H)) (h1 : s.gpr .r1 = dO s₀ (dgO H))
    (h12 : s.gpr .r12 = scr s₀) : FinArgs hH s (dO s₀ (stO H)) (dO s₀ (dgO H)) (scr s₀) := by
  have hl := stO_S hz; have hg := dgO_F hz; have := hz.S; have := hz.D; have hb := hz.buf
  have := hH.hWb; have := hz.fit
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have eh := dO_addr hp (o := dgO H) (by omega_arith)
  have hb16 : Region.Sub (below s) (below s₀) := by rw [hk.belowE]; exact fun _ h => h
  have hlo : Region.Sub (lowR s₀ hH.Wb) (scR H s₀) := low_sub (by omega_arith)
  exact
    { r0 := h0
      r1 := h1
      r12 := h12
      sp16 := by rw [hk.sp]; exact hp.sp16
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk hl
          · exact cov_part hp hk hg
          · exact cov_low hp hk (by omega_arith)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by simp only [stO, dgO]; omega_arith)) hl hg
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by simp only [stO]; omega_arith) hl).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by simp only [dgO]; omega_arith) hg).symm
      b_st := by rw [ea]; exact (hp.b_s.sub_left hb16).sub_right (part_sub hl)
      b_o := by rw [eh]; exact (hp.b_s.sub_left hb16).sub_right (part_sub hg)
      b_sc := (hp.b_s.sub_left hb16).sub_right hlo
      nst := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      no := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      nsc := by have := hp.nsc; omega_arith }

/-- After `finalize`: the digest in `scratch`. -/
abbrev KF (hH : HashOK H) (s₀ s : State) : Prop :=
  KR H s₀ s ∧ bytesAt s.mem (A s₀ (dgO H)) H.D = hH.SH.H.hash (M s₀)

theorem fin2_ok {s : State} (hk : KU hH s₀ s) (h0 : s.gpr .r0 = dO s₀ (stO H)) (h1 : s.gpr .r1 = dO s₀ (dgO H))
    (h12 : s.gpr .r12 = scr s₀) (hc : Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 (dl s₀)) :
    WP isa (.frame (.push [.r1, .r12]) (.call H.finN H.finC) (.pop .r1 8)) s (KF hH s₀) := by
  have hl := stO_S hz; have hg := dgO_F hz; have := hz.S; have := hz.D; have hb := hz.buf
  have := hH.hWb
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have eh := dO_addr hp (o := dgO H) (by omega_arith)
  refine fin_frame hH (fin_args hp hz hH hk.1.1 h0 h1 h12) fun s' a r => ⟨hk.1.1.call hp hz a
    fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by simp only [stO]; omega_arith, hl⟩
    · exact .inr ⟨_, _, by rw [eh], by simp only [dgO]; omega_arith, hg⟩
    · exact .inl ⟨_, rfl, hH.hWb⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hk.2) (by rw [bytesAt_length]; exact Nat.lt_trans (s₀.gpr .r1).isLt (by decide))
      (by rw [bytesAt_length]; exact hc)

/-- The digest copied to `out`, and our caller's registers loaded back. -/
theorem tail_ok {s : State} (hk : KF hH s₀ s) :
    WP isa (.seq (copy .r11 (dgO H) .r5 0 H.D) (.block H.restore)) s fun t =>
      abiPreserved s₀ t ∧ bytesAt t.mem (State.addr (op s₀)) H.D = hH.SH.H.hash (M s₀) := by
  have hg := dgO_F hz; have hD := hz.D; have hb := hz.buf; have hr := hz.reach; have := hz.W; have := hz.S
  have := hz.fit
  have k := hk.1
  have hsep : Region.Disjoint (sR s₀ (dgO H) H.D) (oR H s₀) :=
    (hp.o_s.sub_right (part_sub (by omega_arith))).symm
  have e0 : State.addr (op s₀) + BitVec.ofNat 64 0 = State.addr (op s₀) := BitVec.add_zero _
  refine WP.seq (WP.mono (copy_ok (src := .r11) (dst := .r5) (by decide) (by decide) (so := dgO H) (d := 0)
    (n := H.D) (by simp only [dgO]; omega_arith) (by decide) hD.1 (by omega_arith)
    (by rw [k.r11]; have := hp.nsc; omega_arith) (by rw [k.r5]; have := hp.no; omega_arith)
    (fun j hj => ?_) (fun j hj => ?_) (by rw [k.r11, k.r5, e0]; exact hsep)) fun t (c : Copied ..) => ?_)
  · rw [k.r11, add_ofNat_add]
    exact ⟨scR H s₀, List.mem_append_right _ (by rw [k.wr]; exact sc_mem hp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [k.r5, e0]
    exact ⟨oR H s₀, by rw [k.wr]; exact o_mem hp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [k.r11, k.r5, e0] at c
  have ht : bytesAt t.mem (State.addr (op s₀)) H.D = hH.SH.H.hash (M s₀) := by
    rw [c.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_arith), hk.2]
  have hf : Frame [oR H s₀] s.mem t.mem := by
    rw [c.mem]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have sv : SavedRegs H (scr s₀) s₀ t.mem :=
    k.saved.frame H hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.o_s.sub_right (sv_sub hz)).symm
  have e11 : t.gpr .r11 = scr s₀ := by rw [c.other _ (by decide), k.r11]
  refine WP.mono (Pbkdf2.Stream.Arm.restore_ok H e11 hz.W sv (by rw [c.wr, k.wr]; exact sc_mem hp) (by omega_arith) hp.nsc)
    fun t' ⟨hm, _, _, hsp, hgs, _⟩ => ⟨⟨fun r hr => hgs r (Pbkdf2.Stream.Arm.preserved_saved r hr), by
      rw [hsp, c.sp, k.sp]⟩, by rw [hm]; exact ht⟩

/-! ## The function -/

theorem correct :
    WP isa (digestMain H) s₀ fun s' => abiPreserved s₀ s' ∧ (digestScratch H.D hH.SH.H.hash (nw H)).post s₀ s' := by
  have hg := dgO_F hz; have hb := hz.buf; have hr := hz.reach; have := hz.W; have := hz.S
  unfold digestMain Hash.callInit Hash.callFin
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.seq (WP.mono (init1_ok k₁) fun s₂ ⟨k₂, a₂⟩ => init2_ok hp hz hH k₂ a₂) |>.mono
    fun s₃ k₃ => ?_)
  refine WP.seq (WP.mono (upd1_ok hH k₃) fun s₄ ⟨k₄, a₀, a₁, a₇, a₁₀, c₄⟩ => ?_)
  refine WP.seq (WP.mono (upd2_ok hp hz hH k₄ a₀ a₁ a₇ a₁₀ c₄) fun s₅ k₅ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1_ok hH k₅ (by simp only [dgO]; omega_arith))
    fun s₆ ⟨k₆, a₀', a₁', a₁₂, c₆⟩ => fin2_ok hp hz hH k₆ a₀' a₁' a₁₂ c₆) |>.mono fun s₇ k₇ => ?_)
  refine WP.mono (tail_ok hp hz hH k₇) fun s' ⟨ha, hd⟩ => ⟨ha, ?_⟩
  sig_post [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact hd

end

/-! ## Constant time

As for HMAC's `init` (`Proof/Pbkdf2/Whole/Arm/AnyKeyCT.lean`): the pieces of
code between the calls are checked by the taint analysis (`Checks`, which the
kernel evaluates for each hash function), with the registers holding pointers
and `len` public (`piece`); the calls are related by their contracts
(`init_rel`, `upd_rel`, `fin_rel`), whose public arguments are the same in two
runs with the same public arguments (`PubEq`). -/

/-- A piece of code the taint analysis accepts with `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- The registers holding pointers and `len` after the prologue. -/
abbrev k4regs : List Reg := [.r4, .r5, .r8, .r9, .r11]

/-- The taint checks of the pieces of `digestMain` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : Ck [.r0, .r1, .r2, .r3] (.block (prologue H))
  i1 : Ck k4regs (.block [.mov .r0 (.reg .r4)])
  u1 : Ck k4regs (.block updArgs)
  f1 : Ck k4regs (.block (([.mov .r0 (.reg .r4)] : List Instr) ++ ([.mov .r2 (.reg .r9), .mov .r3 (.imm 0)] : List Instr) ++
      scrAt .r1 (dgO H) ++
    ([.mov .r12 (.reg .r11)] : List Instr)))
  tail : Ck kregs (.seq (copy .r11 (dgO H) .r5 0 H.D) (.block H.restore))

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.dpEq : dp s₀' = dp s₀ := hq.r0.symm
theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.r3.symm
theorem PubEq.dOEq (o : Nat) : dO s₀' o = dO s₀ o := by
  show s₀'.gpr .r3 + BitVec.ofNat 32 o = s₀.gpr .r3 + BitVec.ofNat 32 o; rw [hq.r3]
theorem PubEq.dlEq : dl s₀' = dl s₀ := by show (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat; rw [hq.r1]

theorem ag_k {s s' : State} (h : KR H s₀ s) (h' : KR H s₀' s') : ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.r5, h'.r5]; exact hq.r2
  · rw [h.r8, h'.r8]; exact hq.r0
  · rw [h.r9, h'.r9, hq.r1]
  · rw [h.r11, h'.r11]; exact hq.r3

theorem ag_k4 {s s' : State} (h : K4 H s₀ s) (h' : K4 H s₀' s') : ∀ r ∈ k4regs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [k4regs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h.2, h'.2, hq.dOEq]
  · exact ag_k hq h.1 h'.1 _ (by simpa using hr)

end

section
variable {s₀ s₀' : State} (hp : Pre H s₀) (hp' : Pre H s₀') (hz : Lay H) (hH : HashOK H) (hq : PubEq s₀ s₀')
  (hc : Checks H)
include hp hp' hz hH hq hc

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (digestMain H) fun _ _ => True := by
  have hl := stO_S hz; have hg := dgO_F hz; have := hz.S; have := hz.W; have hb := hz.buf
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have cw : ∀ {t₀ : State}, Pre H t₀ → ∀ {s : State}, KR H t₀ s →
      Covers [⟨State.addr (dO t₀ (stO H)), H.S⟩] s.wr := fun {t₀} hp₀ {s} k => by
    rw [dO_addr hp₀ (o := stO H) (by omega_arith)]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp₀ k hl
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (prologue H))
      fun s s' => K4 H s₀ s ∧ K4 H s₀' s' :=
    Pbkdf2.Stream.Arm.rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀') _ (fun s s' e e' => by
        subst e e'
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  have i1 : RelCT isa (fun s s' => K4 H s₀ s ∧ K4 H s₀' s') (.block [.mov .r0 (.reg .r4)])
      fun s s' => (K4 H s₀ s ∧ s.gpr .r0 = dO s₀ (stO H)) ∧ (K4 H s₀' s' ∧ s'.gpr .r0 = dO s₀' (stO H)) :=
    Pbkdf2.Stream.Arm.rel_taint _ (fun s s' h h' => ag_k4 hq h h') hc.i1 (fun _ h => init1_ok h)
      (fun _ h => init1_ok h)
  have i2 : RelCT isa (fun s s' => (K4 H s₀ s ∧ s.gpr .r0 = dO s₀ (stO H)) ∧
      (K4 H s₀' s' ∧ s'.gpr .r0 = dO s₀' (stO H))) (.call H.initN H.initC)
      fun s s' => KI hH s₀ s ∧ KI hH s₀' s' :=
    Pbkdf2.Stream.Arm.rel_wp (Pbkdf2.Stream.Arm.init_rel hH (st := dO s₀ (stO H))
        fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
        ⟨a, by rw [a', hq.dOEq], by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith, cw hp k.1,
          by have := cw hp' k'.1; rwa [hq.dOEq] at this⟩)
      (fun s ⟨k, a⟩ => init2_ok hp hz hH k a) (fun s ⟨k, a⟩ => init2_ok hp' hz hH k a)
  have u1 := Pbkdf2.Stream.Arm.rel_taint (F := KI hH s₀) (F' := KI hH s₀') _
    (fun s s' h h' => ag_k4 hq h.1 h'.1) hc.u1 (fun _ h => upd1_ok hH h) (fun _ h => upd1_ok hH h)
  have u2 : RelCT isa (fun s s' =>
      (KI hH s₀ s ∧ s.gpr .r0 = dO s₀ (stO H) ∧ s.gpr .r1 = dp s₀ ∧ s.gpr .r7 = s₀.gpr .r1 ∧
        s.gpr .r10 = scr s₀ ∧ Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 0) ∧
      (KI hH s₀' s' ∧ s'.gpr .r0 = dO s₀' (stO H) ∧ s'.gpr .r1 = dp s₀' ∧ s'.gpr .r7 = s₀'.gpr .r1 ∧
        s'.gpr .r10 = scr s₀' ∧ Pbkdf2.Stream.Arm.count s' = BitVec.ofNat 64 0))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call H.updN H.updC) (.pop .r1 16))
      fun s s' => KU hH s₀ s ∧ KU hH s₀' s' :=
    Pbkdf2.Stream.Arm.rel_wp (Pbkdf2.Whole.Arm.upd_rel hH (sp := s₀.sp)
        fun s s' ⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, ⟨k', a₀', a₁', a₇', a₁₀', c'⟩⟩ =>
        ⟨upd_args hp hz hH k.1.1 a₀ a₁ a₇ a₁₀,
          by have := upd_args hp' hz hH k'.1.1 a₀' a₁' a₇' a₁₀'; rwa [hq.dOEq, hq.dpEq, hq.scrEq, hq.dlEq] at this,
          by rw [c, c'], k.1.1.sp, by rw [k'.1.1.sp, hq.sp]⟩)
      (fun s ⟨k, a₀, a₁, a₇, a₁₀, c⟩ => upd2_ok hp hz hH k a₀ a₁ a₇ a₁₀ c)
      (fun s ⟨k, a₀, a₁, a₇, a₁₀, c⟩ => upd2_ok hp' hz hH k a₀ a₁ a₇ a₁₀ c)
  have ho : dgO H < 2 ^ 16 := by simp only [dgO]; omega_arith
  have f1 := Pbkdf2.Stream.Arm.rel_taint (F := KU hH s₀) (F' := KU hH s₀') _
    (fun s s' h h' => ag_k4 hq h.1 h'.1) hc.f1 (fun _ h => fin1_ok hH h ho) (fun _ h => fin1_ok hH h ho)
  have f2 : RelCT isa (fun s s' =>
      (KU hH s₀ s ∧ s.gpr .r0 = dO s₀ (stO H) ∧ s.gpr .r1 = dO s₀ (dgO H) ∧ s.gpr .r12 = scr s₀ ∧
        Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 (dl s₀)) ∧
      (KU hH s₀' s' ∧ s'.gpr .r0 = dO s₀' (stO H) ∧ s'.gpr .r1 = dO s₀' (dgO H) ∧ s'.gpr .r12 = scr s₀' ∧
        Pbkdf2.Stream.Arm.count s' = BitVec.ofNat 64 (dl s₀')))
      (.frame (.push [.r1, .r12]) (.call H.finN H.finC) (.pop .r1 8))
      fun s s' => KF hH s₀ s ∧ KF hH s₀' s' :=
    Pbkdf2.Stream.Arm.rel_wp (Pbkdf2.Stream.Arm.fin_rel hH (sp := s₀.sp)
        fun s s' ⟨⟨k, a₀, a₁, a₁₂, c⟩, ⟨k', a₀', a₁', a₁₂', c'⟩⟩ =>
        ⟨fin_args hp hz hH k.1.1 a₀ a₁ a₁₂,
          by have := fin_args hp' hz hH k'.1.1 a₀' a₁' a₁₂'; rwa [hq.dOEq, hq.dOEq, hq.scrEq] at this,
          by rw [c, c', hq.dlEq], k.1.1.sp, by rw [k'.1.1.sp, hq.sp]⟩)
      (fun s ⟨k, a₀, a₁, a₁₂, c⟩ => fin2_ok hp hz hH k a₀ a₁ a₁₂ c)
      (fun s ⟨k, a₀, a₁, a₁₂, c⟩ => fin2_ok hp' hz hH k a₀ a₁ a₁₂ c)
  have tl := Pbkdf2.Stream.Arm.rel_taint (F := KF hH s₀) (F' := KF hH s₀') _
    (fun s s' h h' => ag_k hq h.1 h'.1) hc.tail (fun _ h => tail_ok hp hz hH h) (fun _ h => tail_ok hp' hz hH h)
  unfold digestMain Hash.callInit Hash.callFin
  exact (pro.seq ((i1.seq i2).seq (u1.seq (u2.seq ((f1.seq f2).seq tl))))).mono (fun _ _ h => h) fun _ _ _ => trivial

end

/-- The public arguments of the contract. -/
theorem pub_of {D : Nat} {hash : List Byte → List Byte} {n : Nat} {s₁ s₂ : State}
    (h : (digestScratch D hash n).pub s₁ s₂) : PubEq s₁ s₂ := by
  sig_pub [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `digestMain` is verified against `digestScratch`, given the taint checks
and a state satisfying it. -/
theorem verified (hH : HashOK H) (hc : Checks H) (hsat : ∃ s, (digestScratch H.D hH.SH.H.hash (nw H)).pre s) :
    Verified Arm.target (digestMain H) (digestScratch H.D hH.SH.H.hash (nw H)) :=
  ⟨fun _ hs => correct (pre_of hs) (lay hH) hH,
    fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
      (ct (pre_of h₁) (pre_of h₂) (lay hH) hH (pub_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩

/-! ## In a frame of its own, wiped -/

/-- `digest`: `digestMain` in a frame holding its working space, which it
wipes before returning, verified against `Spec.Sha256.digestContract`, from
the locality of its postcondition (`Proof/MdStream/DigestScratch.lean`). -/
theorem framed (hH : HashOK H) (h : Verified Arm.target (digestMain H) (digestScratch H.D hH.SH.H.hash (nw H)))
    (hsat : ∃ s, (Spec.Sha256.digestContract Arm.abi H.D hH.SH.H.hash (16 + dbytes H)).pre s)
    (hb : FitsR (dbytes H) .u64 (nw H) := by decide) :
    Verified Arm.target (digest H) (Spec.Sha256.digestContract Arm.abi H.D hH.SH.H.hash (16 + dbytes H)) :=
  Arm.Verified.regScratchWiped (sig := digestSig H.D) (nm := "scratch") (e := .u64) (n := nw H)
    (post := digestPost H.D hH.SH.H.hash Arm.abi.ptrBits) (wa := false) (stack := 16) (words := dbytes H / 4)
    h ⟨by decide, rfl, rfl⟩ rfl hb (by simp only [nw, dbytes, Elem.size]; omega)
    (MdStream.Digest.digestPostOut_local _ _ _) hsat rfl

/-- A state satisfying `digestMain`'s precondition, with a digest of `D`
bytes, `L` bytes of `scratch` and an empty message. -/
def digestSat (D L : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | .r3 => 0x3000
    | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, D⟩, ⟨0x3000, L⟩]

/-- A state satisfying `digest`'s precondition, with a digest of `D` bytes
and an empty message. -/
def digestFrameSat (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000
    | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, D⟩]

end VG.Proof.MdStream.Arm.Digest
