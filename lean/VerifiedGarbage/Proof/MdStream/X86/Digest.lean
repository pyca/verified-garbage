module

public import VerifiedGarbage.Impl.MdStream.X86.Digest
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.MdStream.DigestScratch
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Stream

-- separate module: the generic proof, which builds in parallel with the proofs of the hash functions that its instances (`DigestInstances.lean`) import

/-!
# The one-shot digest over any streaming hash function on x86 (32-bit): correct

`digestMain` (`Impl/MdStream/X86/Digest.lean`) saves our caller's registers
in `scratch` (`prologue_ok`), hashes the message with the streaming `init`,
`update` and `finalize` into `scratch`, through their contracts
(`init_ok`, `upd_ok`, `fin_ok`), as HMAC's `init` hashes a long key
(`Proof/Pbkdf2/Whole/X86/AnyKey.lean`), copies the digest to `out` and loads
our caller's registers back (`tail_ok`). Every argument is on the stack
(cdecl): `data`, `len`, `out`, `scratch`. `digestScratch` is the contract it
is verified against: `VG.Spec.Sha256.digestContract` with its working space
as a last argument, and 48 bytes of stack (the frames of the calls).
-/

@[expose] public section

namespace VG.Proof.MdStream.X86.Digest

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Impl.MdStream.X86.Digest (stO dgO dbytes dframe prologue updArgs finArgs outArg digestMain digest)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK After stk SavedRegs saveR savedRegs InitArgs UpdArgs FinArgs init_frame
  upd_frame fin_frame zero_append_ofNat copy_ok Copied cclob argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel
  upd_rel fin_rel)
open VG.Proof.Pbkdf2.Whole.X86 (below_eq argVal32 toNat_setWidth64 setWidth32_64)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take add_ofNat_add bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt digestSig digestPost)

/-! ## The contract -/

/-- `Spec.Sha256.digestContract` with a last argument, `scratch`, of `n`
64-bit words, and 48 bytes of stack. -/
def digestScratch (D : Nat) (hash : List Byte → List Byte) (n : Nat) : Contract isa :=
  Sig.scratchContract X86.abi (digestSig D) "scratch" .u64 n (Curry.const (fun _ => True) _)
    (digestPost D hash X86.abi.ptrBits) false 48

/-- The 64-bit words of `scratch`. -/
abbrev nw (H : Hash) : Nat := dbytes H / 8

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev dp : BitVec 32 := arg s₀ 0
abbrev dl : Nat := (arg s₀ 1).toNat
abbrev op : BitVec 32 := arg s₀ 2
abbrev scr : BitVec 32 := arg s₀ 3
abbrev dR : Region := ⟨(dp s₀).setWidth 64, dl s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨(scr s₀).setWidth 64, k⟩
/-- The message. -/
abbrev M : List Byte := bytesAt s₀.mem ((dp s₀).setWidth 64) (dl s₀)

end

section
variable (H : Hash) (s₀ : State)
abbrev oR : Region := ⟨(op s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, nw H * 8⟩
/-- The save area of our caller's registers. -/
abbrev svR : Region := saveR H (scr s₀)
/-- The regions everything writes: `out`, `scratch` and the stack below `esp`. -/
abbrev wrs : List Region := [oR H s₀, scR H s₀, stkR s₀]
end

/-- The precondition. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 20 ≤ 2 ^ 32
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [oR H s₀, scR H s₀]
  d_o : (dR s₀).Disjoint (oR H s₀)
  d_s : (dR s₀).Disjoint (scR H s₀)
  o_s : (oR H s₀).Disjoint (scR H s₀)
  o_a : (oR H s₀).Disjoint (argR s₀)
  s_a : (scR H s₀).Disjoint (argR s₀)
  r_d : (retR s₀).Disjoint (dR s₀)
  r_o : (retR s₀).Disjoint (oR H s₀)
  r_s : (retR s₀).Disjoint (scR H s₀)
  r_a : (retR s₀).Disjoint (argR s₀)
  b_d : (stkR s₀).Disjoint (dR s₀)
  b_o : (stkR s₀).Disjoint (oR H s₀)
  b_s : (stkR s₀).Disjoint (scR H s₀)
  b_a : (stkR s₀).Disjoint (argR s₀)
  nd : (dp s₀).toNat + dl s₀ ≤ 2 ^ 32
  no : (op s₀).toNat + H.D ≤ 2 ^ 32
  nsc : (scr s₀).toNat + nw H * 8 ≤ 2 ^ 32

theorem pre_of {H : Hash} {hash : List Byte → List Byte} {s₀ : State}
    (h : (digestScratch H.D hash (nw H)).pre s₀) : Pre H s₀ := by
  sig_pre [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    X86.abi] at h
  simp only [argVal32, toNat_setWidth64] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, -⟩ := h
  rw [← below_eq h0] at h13 h14 h15 h16
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Lay (H : Hash) : Prop where
  W : H.W ≤ 64
  S : 0 < H.S ∧ H.S ≤ 256
  D : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64
  buf : H.buf = 8 * H.W + 16
  fit : H.buf + H.S + H.F ≤ nw H * 8
  reach : nw H * 8 ≤ 4096

theorem lay {H : Hash} (hH : HashOK H) : Lay H := by
  have := hH.hW; have := hH.hSB; have := hH.hDF; have := hH.hF
  refine ⟨hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩, rfl, ?_, ?_⟩ <;>
    simp only [nw, dbytes, Hash.buf] <;> omega_arith

variable {H : Hash}

section
variable {s₀ : State} (hp : Pre H s₀) (hz : Lay H)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < nw H * 8) : (dO s₀ o).setWidth 64 = A s₀ o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.setWidth_add (by omega_arith)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < nw H * 8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.toNat_add_ofNat (by omega_arith)

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
  exact (Offset.base_disjoint _ (k := k) (e := 8 * H.W) (n := 16) hk (by omega_arith)).symm

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
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame (wrs H s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {s₀ s s' : State}

theorem KR.stkE (h : KR H s₀ s) : stk s = stkR s₀ := by
  rw [stk, h.esp]

/-- `KR` survives changes to other registers, and to memory in `out`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep (h : KR H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR H s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs H s₀, Region.Sub r r') :
    KR H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same (h : KR H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR H s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd (h : KR H s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32} (u : Upd s s' d v) : KR H s₀ s' :=
  h.same u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- What a call leaves, writing parts of `scratch` after the save area, or
the working space, and the stack below `esp`. -/
theorem KR.call (hp : Pre H s₀) (hz : Lay H) (h : KR H s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = lowR s₀ k ∧ k ≤ 8 * H.W) ∨
      ∃ o n, r = sR s₀ o n ∧ H.buf ≤ o ∧ o + n ≤ nw H * 8) : KR H s₀ s' := by
  have hf := hz.fit; have hb := hz.buf
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
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

end

/-! ## The arguments, the return address and the message, while `KR` holds -/

section
variable {s₀ : State} (hp : Pre H s₀)
include hp

omit hp in
theorem argR_eq : argR s₀ = ⟨addr (E s₀) 4, 16⟩ := rfl

theorem KR.argEq {s : State} (hk : KR H s₀ s) {i : Nat} (hi : i < 4) : arg s i = arg s₀ i := by
  have hd : ∀ r ∈ wrs H s₀, Region.Disjoint ⟨addr (E s₀) 4, 16⟩ r := by
    rw [← argR_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.b_a.symm
  exact Pbkdf2.Stream.X86.arg_keep rfl hk.esp (n := 16) (by have := hp.spf; omega_arith) hk.frame hd (by omega_arith)

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [show s.ea (at_ .esp (4 + 4 * i)) = addr (s.gpr .esp) (4 + 4 * i) from rfl, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hp.rd]
  exact ⟨argR s₀, by simp, by
    rw [argR_eq]; exact Pbkdf2.Stream.X86.arg_contains rfl (by omega_arith) (by have := hp.spf; omega_arith)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : KR H s₀ s) {i : Nat} (hi : i < 4) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := hk.argEq hp hi
  simp only [arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by
    rw [Pbkdf2.Stream.X86.argAddr_eq, Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

/-- `mov d, [esp + 4 + 4 i]`: argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : KR H s₀ s) {d : Reg} {i : Nat} (hi : i < 4) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (Impl.Pbkdf2.Whole.X86.Fns.argM i) :: is)) s Q :=
  wp_movm (a := argAddr s₀ i) (argW hk.esp i) (argIn hp hk.rd hi)
    fun s' u => k s' (by rw [hk.readArg hp hi] at u; exact u)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : KR H s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_o
    · exact hp.r_s
    · rw [stkR, below_eq hp.sp48]
      exact (Offset.below_disjoint _ (by omega_arith)).symm) (by decide)

theorem KR.dataBytes {s : State} (hk : KR H s₀ s) :
    bytesAt s.mem ((dp s₀).setWidth 64) (dl s₀) = M s₀ :=
  bytes_keep hk.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.d_o
    · exact hp.d_s
    · exact hp.b_d.symm) (by have := hp.nd; omega_arith)

theorem cov_part {s : State} (hk : KR H s₀ s) {o n : Nat} (h : o + n ≤ nw H * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR H s₀, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

theorem cov_low {s : State} (hk : KR H s₀ s) {k : Nat} (h : k ≤ nw H * 8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR H s₀, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

theorem b48 {s : State} (hk : KR H s₀ s) {R : Region} (hR : Region.Sub R (scR H s₀)) :
    (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

end

/-- `d ← scratch + o`, while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : KR H s₀ s) {d : Reg} {o : Nat} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ =>
    k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, hk.ebp]

/-! ## The pieces -/

section
variable {s₀ : State} (hp : Pre H s₀) (hz : Lay H)
include hp hz

/-- After the prologue: `KR`, and the streaming state's address in `edi`. -/
abbrev K1 (H : Hash) (s₀ s : State) : Prop := KR H s₀ s ∧ s.gpr .edi = dO s₀ (stO H)

theorem prologue_ok : WP isa (.block (prologue H)) s₀ (K1 H s₀) := by
  have hf := hz.fit; have hb := hz.buf; have hr := hz.reach
  have hsc := sc_mem hp
  simp only [prologue, List.append_assoc, List.cons_append]
  refine wp_movm (a := argAddr s₀ 3) (argW rfl 3) (argIn hp rfl (by decide)) fun s₁ u₁ => ?_
  refine Pbkdf2.Stream.X86.save_ok H (scr := scr s₀) (L := nw H * 8) u₁.gpr hz.W (by rw [u₁.wr]; exact hsc)
    (by omega_arith) hp.nsc fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  refine wp_mov fun s₃ u₃ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have k₃ : KR H s₀ s₃ := by
    refine ⟨by rw [u₃.rd, rd₂, u₁.rd], by rw [u₃.wr, wr₂, u₁.wr], by rw [u₃.other _ (by decide), e₂ _ (by decide)],
      by rw [u₃.gpr, g₂, u₁.gpr]; rfl, ?_, ?_⟩
    · rw [u₃.mem]
      exact sv₂.of_eq H fun r hr => u₁.other r (by
        simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)
    · rw [u₃.mem, ← u₁.mem]
      exact f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR H s₀, by simp, sv_sub hz⟩
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi (stO H))]
  exact scr_ok k₃ fun s₄ u₄ => WP.block_nil ⟨k₃.upd (by decide) u₄, u₄.gpr⟩

/-- After `init`: the streaming state represents the empty message. -/
abbrev KI (hH : HashOK H) (s₀ s : State) : Prop := K1 H s₀ s ∧ hH.SH.Repr s.mem (A s₀ (stO H)) []

variable (hH : HashOK H)
include hH

omit hp hH in
theorem stO_S : stO H + H.S ≤ nw H * 8 := by
  have := hz.fit; have := hz.D; simp only [stO]; omega_arith

omit hp hH in
theorem dgO_F : dgO H + H.F ≤ nw H * 8 := by
  have := hz.fit; simp only [dgO]; omega_arith

omit hH in
theorem init_args {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) :
    InitArgs (H := H) s .edi (dO s₀ (stO H)) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  refine ⟨hdi, by decide, by rw [hk.esp]; exact hp.sp48, ?_, ?_, ?_⟩
  · rw [ea]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk hl
  · rw [ea]; exact b48 hp hk (part_sub hl)
  · rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith

/-- `init` on the streaming state. -/
theorem init_ok {s : State} (hk : K1 H s₀ s) : WP isa (H.callInit .edi) s (KI hH s₀) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  refine init_frame hH (init_args hp hz hk.1 hk.2) fun s' a r => ⟨⟨hk.1.call hp hz a fun r hr => ?_, ?_⟩,
    by rw [← ea]; exact r⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr ⟨_, _, by rw [ea], by simp only [stO]; omega_arith, hl⟩
  · rw [a.cs _ (by decide), hk.2]

omit hz hH in
/-- `update`'s arguments: the message. -/
theorem upd1_ok {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) :
    WP isa (.block updArgs) s
      fun t => KR H s₀ t ∧ t.gpr .edi = dO s₀ (stO H) ∧ t.gpr .esi = 0 ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 1 ∧ t.gpr .edx = dp s₀ ∧ t.mem = s.mem := by
  simp only [updArgs]
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

theorem upd_args {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 1) (hdx : s.gpr .edx = dp s₀) :
    UpdArgs hH s .esi .edi (dO s₀ (stO H)) (dp s₀) (scr s₀) 0 (dl s₀) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf; have := hH.hWb; have := hz.fit
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 1).isLt
      sp48 := by rw [hk.esp]; exact hp.sp48
      cd := Pbkdf2.Stream.X86.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk hl
          · exact cov_low hp hk (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by simp only [stO]; omega_arith) hl).symm
      d_st := by rw [ea]; exact hp.d_s.sub_right (part_sub hl)
      d_sc := hp.d_s.sub_right (low_sub (by omega_arith))
      b_st := by rw [ea]; exact b48 hp hk (part_sub hl)
      b_d := by rw [hk.stkE]; exact hp.b_d
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      nd := hp.nd
      nsc := by have := hp.nsc; omega_arith }

/-- After `update`: the streaming state represents the message. -/
abbrev KU (hH : HashOK H) (s₀ s : State) : Prop := K1 H s₀ s ∧ hH.SH.Repr s.mem (A s₀ (stO H)) (M s₀)

theorem upd_ok {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 1) (hdx : s.gpr .edx = dp s₀)
    (hr : hH.SH.Repr s.mem (A s₀ (stO H)) []) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call H.updN H.updC) (.pop .eax 6)) s
      (KU hH s₀) := by
  have hl := stO_S hz; have := hz.S; have hb := hz.buf; have := hH.hWb
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  refine upd_frame hH (upd_args hp hz hH hk hdi hsi hax hcx hdx) fun s' a r => ⟨⟨hk.call hp hz a fun r hr => ?_,
    by rw [a.cs _ (by decide), hdi]⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by simp only [stO]; omega_arith, hl⟩
    · exact .inl ⟨_, rfl, hH.hWb⟩
  · have := r [] (by rw [ea]; exact hr) rfl
    rwa [List.nil_append, ea, hk.dataBytes hp] at this

omit hz hH in
/-- `finalize`'s arguments: `len` as the count, and its output into `scratch`. -/
theorem fin1_ok {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) :
    WP isa (.block (finArgs H)) s
      fun t => KR H s₀ t ∧ t.gpr .edi = dO s₀ (stO H) ∧ t.gpr .eax = arg s₀ 1 ∧ t.gpr .ecx = 0 ∧
        t.gpr .edx = dO s₀ (dgO H) ∧ t.mem = s.mem := by
  simp only [finArgs, List.cons_append, List.nil_append]
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx (dgO H))]
  refine scr_ok k₂ fun s₃ u₃ => WP.block_nil ⟨k₂.upd (by decide) u₃, ?_, ?_, ?_, u₃.gpr, by
    rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem fin_args {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) (hax : s.gpr .eax = arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ (dgO H)) :
    FinArgs hH s .edi (dO s₀ (stO H)) (dO s₀ (dgO H)) (scr s₀) (arg s₀ 1) 0 := by
  have hl := stO_S hz; have hg := dgO_F hz; have := hz.S; have := hz.D; have hb := hz.buf
  have := hH.hWb; have := hz.fit
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have eh := dO_addr hp (o := dgO H) (by omega_arith)
  exact
    { hst := hdi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      sp48 := by rw [hk.esp]; exact hp.sp48
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
      b_st := by rw [ea]; exact b48 hp hk (part_sub hl)
      b_o := by rw [eh]; exact b48 hp hk (part_sub hg)
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      no := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      nsc := by have := hp.nsc; omega_arith }

/-- After `finalize`: the digest in `scratch`. -/
abbrev KF (hH : HashOK H) (s₀ s : State) : Prop :=
  KR H s₀ s ∧ bytesAt s.mem (A s₀ (dgO H)) H.D = hH.SH.H.hash (M s₀)

theorem fin_ok {s : State} (hk : KR H s₀ s) (hdi : s.gpr .edi = dO s₀ (stO H)) (hax : s.gpr .eax = arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ (dgO H)) (hr : hH.SH.Repr s.mem (A s₀ (stO H)) (M s₀)) :
    WP isa (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call H.finN H.finC) (.pop .eax 5)) s (KF hH s₀) := by
  have hl := stO_S hz; have hg := dgO_F hz; have := hz.S; have := hz.D; have hb := hz.buf
  have := hH.hWb
  have ea := dO_addr hp (o := stO H) (by omega_arith)
  have eh := dO_addr hp (o := dgO H) (by omega_arith)
  refine fin_frame hH (fin_args hp hz hH hk hdi hax hcx hdx) fun s' a r => ⟨hk.call hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by simp only [stO]; omega_arith, hl⟩
    · exact .inr ⟨_, _, by rw [eh], by simp only [dgO]; omega_arith, hg⟩
    · exact .inl ⟨_, rfl, hH.hWb⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (arg s₀ 1).isLt (by decide))
      (by rw [bytesAt_length, ← zero_append_ofNat (arg s₀ 1).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `out` loaded, the digest copied to it, and our caller's registers loaded back. -/
theorem tail_ok {s : State} (hk : KF hH s₀ s) :
    WP isa (.seq (.block outArg) (.seq (VG.Impl.Pbkdf2.Stream.X86.copy .ebp (dgO H) .esi 0 H.D) (.block H.restore))) s
      fun t => abiPreserved s₀ t ∧ bytesAt t.mem ((op s₀).setWidth 64) H.D = hH.SH.H.hash (M s₀) := by
  have hg := dgO_F hz; have hD := hz.D; have hb := hz.buf; have hr := hz.reach; have := hz.W; have := hz.S
  have := hz.fit
  have k := hk.1
  have a₁ : WP isa (.block outArg) s fun t => KF hH s₀ t ∧ t.gpr .esi = op s₀ :=
    wp_arg hp k (by decide) fun s₁ u₁ => WP.block_nil ⟨⟨k.upd (by decide) u₁, by rw [u₁.mem]; exact hk.2⟩, u₁.gpr⟩
  refine WP.seq (WP.mono a₁ fun s₁ ⟨⟨k₁, b₁⟩, e₁⟩ => ?_)
  have hsep : Region.Disjoint (sR s₀ (dgO H) H.D) (oR H s₀) :=
    (hp.o_s.sub_right (part_sub (by omega_arith))).symm
  have e0 : (op s₀).setWidth 64 + BitVec.ofNat 64 0 = (op s₀).setWidth 64 := BitVec.add_zero _
  refine WP.seq (WP.mono (copy_ok (src := .ebp) (dst := .esi) (by decide) (by decide) (so := dgO H) (d := 0)
    (n := H.D) hD.1 (by omega_arith)
    (by rw [k₁.ebp]; have := hp.nsc; omega_arith) (by rw [e₁]; have := hp.no; omega_arith)
    (fun j hj => ?_) (fun j hj => ?_) (by rw [k₁.ebp, e₁, e0]; exact hsep)) fun t (c : Copied ..) => ?_)
  · rw [k₁.ebp, add_ofNat_add]
    exact ⟨scR H s₀, List.mem_append_right _ (by rw [k₁.wr]; exact sc_mem hp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [e₁, e0]
    exact ⟨oR H s₀, by rw [k₁.wr]; exact o_mem hp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [k₁.ebp, e₁, e0] at c
  have ht : bytesAt t.mem ((op s₀).setWidth 64) H.D = hH.SH.H.hash (M s₀) := by
    rw [c.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_arith), b₁]
  have hf : Frame [oR H s₀] s₁.mem t.mem := by
    rw [c.mem]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have k' : KR H s₀ t := k₁.keep c.rd c.wr (fun r hr => c.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)) hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.o_s.sub_right (sv_sub hz)).symm)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  refine WP.mono (Pbkdf2.Stream.X86.restore_ok H k'.ebp k'.saved (by rw [k'.wr]; exact sc_mem hp)
    (show 8 * H.W + 16 ≤ nw H * 8 by omega_arith) hp.nsc)
    fun t' ⟨hm, _, _, hgs, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact k'.ret hp⟩, by rw [hm]; exact ht⟩
  by_cases he : r = .esp
  · subst he; rw [ho _ (by decide) (by decide), k'.esp]
  · exact hgs r (Pbkdf2.Stream.X86.callee_saved r hr he)

/-! ## The function -/

theorem correct :
    WP isa (digestMain H) s₀ fun s' => abiPreserved s₀ s' ∧ (digestScratch H.D hH.SH.H.hash (nw H)).post s₀ s' := by
  unfold digestMain
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (init_ok hp hz hH k₁) fun s₂ ⟨⟨k₂, d₂⟩, r₂⟩ => ?_)
  refine WP.seq (WP.mono (upd1_ok hp k₂ d₂) fun s₃ ⟨k₃, d₃, i₃, a₃, c₃, x₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (upd_ok hp hz hH k₃ d₃ i₃ a₃ c₃ x₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨⟨k₄, d₄⟩, r₄⟩ => ?_)
  refine WP.seq (WP.mono (fin1_ok hp k₄ d₄) fun s₅ ⟨k₅, d₅, a₅, c₅, x₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (fin_ok hp hz hH k₅ d₅ a₅ c₅ x₅ (by rw [m₅]; exact r₄)) fun s₆ k₆ => ?_)
  refine WP.mono (tail_ok hp hz hH k₆) fun s' ⟨ha, hd⟩ => ⟨ha, ?_⟩
  sig_post [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    X86.abi]
  simp only [argVal32, setWidth32_64]
  exact hd

end

/-! ## Constant time

As for HMAC's `init` (`Proof/Pbkdf2/Whole/X86/AnyKeyCT.lean`): the pieces of
code between the calls are checked by the taint analysis (`Checks`, which the
kernel evaluates for each hash function), with the arguments, `esp` and
`ebp` public (`piece`); the calls are related by their contracts
(`init_rel`, `upd_rel`, `fin_rel`), whose public arguments are the same in two
runs with the same public arguments (`PubEq`). -/

/-- A piece of code the taint analysis accepts with the arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs (4 + 4 * 4)) c hc).isSome = true

/-- The taint checks of the pieces of `digestMain` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : Ck [] (.block (prologue H))
  u1 : Ck [.ebp] (.block updArgs)
  f1 : Ck [.ebp] (.block (finArgs H))
  tail : Ck [.ebp]
    (.seq (.block outArg) (.seq (VG.Impl.Pbkdf2.Stream.X86.copy .ebp (dgO H) .esi 0 H.D) (.block H.restore)))

/-- The sizes of `H`, which are all the taint checks depend on, with no
code. -/
def shapeOf (H : Hash) : Hash := ⟨H.B, H.S, H.D, H.F, H.W, "", .block [], "", .block [], "", .block []⟩

/-- The checks depend only on the sizes of `H`. -/
theorem checks_of_shape (h : Checks (shapeOf H)) : Checks H := ⟨h.pro, h.u1, h.f1, h.tail⟩

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : E s₀ = E s₀'
  args : ∀ i < 4, arg s₀ i = arg s₀' i

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 4) : arg s₀' i = arg s₀ i := (hq.args i hi).symm
theorem PubEq.E' : E s₀' = E s₀ := hq.esp.symm
theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a (by decide)
theorem PubEq.dpEq : dp s₀' = dp s₀ := hq.a (by decide)
theorem PubEq.dlEq : dl s₀' = dl s₀ := by show (arg s₀' 1).toNat = _; rw [hq.a (by decide)]
theorem PubEq.dOEq (o : Nat) : dO s₀' o = dO s₀ o := by show scr s₀' + _ = _; rw [hq.scrEq]

end

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre H t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 4 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 4⟩ : Region) = ⟨(E t).setWidth 64, 4 + 16⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega_arith) h.r_o h.o_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega_arith) h.r_s h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre H s₀) (hp' : Pre H s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR H t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre H t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree_argTaint (hag s s' h h')
      (by rw [(hk h).esp, (hk h').esp, hq.esp])
      (args_out hp (hk h).esp (hk h).wr) (args_out hp' (hk h').esp (hk h').wr)
      fun i hi => by rw [(hk h).argEq hp hi, (hk h').argEq hp' hi, hq.args i hi]) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_ebp {s s' : State} (h : KR H s₀ s) (h' : KR H s₀' s') : ∀ r ∈ [Reg.ebp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.ebp, h'.ebp, hq.scrEq]

end

/-- After `update`'s arguments. -/
abbrev KA (hH : HashOK H) (t₀ s : State) : Prop :=
  KR H t₀ s ∧ s.gpr .edi = dO t₀ (stO H) ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = arg t₀ 1 ∧
    s.gpr .edx = dp t₀ ∧ hH.SH.Repr s.mem (A t₀ (stO H)) []

/-- After `finalize`'s arguments. -/
abbrev KB (hH : HashOK H) (t₀ s : State) : Prop :=
  KR H t₀ s ∧ s.gpr .edi = dO t₀ (stO H) ∧ s.gpr .eax = arg t₀ 1 ∧ s.gpr .ecx = 0 ∧
    s.gpr .edx = dO t₀ (dgO H) ∧ hH.SH.Repr s.mem (A t₀ (stO H)) (M t₀)

/-- After the copy and the restore. -/
abbrev KT (hH : HashOK H) (t₀ s : State) : Prop :=
  abiPreserved t₀ s ∧ bytesAt s.mem ((op t₀).setWidth 64) H.D = hH.SH.H.hash (M t₀)

section
variable {s₀ s₀' : State} (hp : Pre H s₀) (hp' : Pre H s₀') (hz : Lay H) (hH : HashOK H) (hq : PubEq s₀ s₀')
  (hc : Checks H)
include hp hp' hz hH hq hc

/-- `digestMain` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (digestMain H) fun _ _ => True := by
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := K1 H s₀) (G' := K1 H s₀')
    (argTaint [] (4 + 4 * 4)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  have ri : RelCT isa (fun s s' => K1 H s₀ s ∧ K1 H s₀' s') (H.callInit .edi)
      fun s s' => KI hH s₀ s ∧ KI hH s₀' s' :=
    rel_wp (init_rel hH (sp := E s₀) (st := dO s₀ (stO H)) fun s s' ⟨k, k'⟩ =>
        ⟨init_args hp hz k.1 k.2, by have := init_args hp' hz k'.1 k'.2; rwa [hq.dOEq] at this, k.1.esp,
          by rw [k'.1.esp, hq.E']⟩)
      (fun s k => init_ok hp hz hH k) (fun s k => init_ok hp' hz hH k)
  have r1 := piece hp hp' hq (KI hH) (KA hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.u1
    (fun hp₀ s ⟨⟨k, d⟩, r⟩ => WP.mono (upd1_ok hp₀ k d) fun t ⟨k', d', i, a, c, x, m⟩ =>
      ⟨k', d', i, a, c, x, by rw [m]; exact r⟩)
  have ru : RelCT isa (fun s s' => KA hH s₀ s ∧ KA hH s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call H.updN H.updC) (.pop .eax 6))
      fun s s' => KU hH s₀ s ∧ KU hH s₀' s' :=
    rel_wp (upd_rel hH (sp := E s₀) fun s s' ⟨⟨k, d, i, a, c, x, _⟩, ⟨k', d', i', a', c', x', _⟩⟩ =>
        ⟨upd_args hp hz hH k d i a c x,
          by have := upd_args hp' hz hH k' d' i' a' c' x'; rwa [hq.dOEq, hq.dpEq, hq.scrEq, hq.dlEq] at this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨k, d, i, a, c, x, r⟩ => upd_ok hp hz hH k d i a c x r)
      (fun s ⟨k, d, i, a, c, x, r⟩ => upd_ok hp' hz hH k d i a c x r)
  have r2 := piece hp hp' hq (KU hH) (KB hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.f1
    (fun hp₀ s ⟨⟨k, d⟩, r⟩ => WP.mono (fin1_ok hp₀ k d) fun t ⟨k', d', a, c, x, m⟩ =>
      ⟨k', d', a, c, x, by rw [m]; exact r⟩)
  have rf : RelCT isa (fun s s' => KB hH s₀ s ∧ KB hH s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call H.finN H.finC) (.pop .eax 5))
      fun s s' => KF hH s₀ s ∧ KF hH s₀' s' :=
    rel_wp (fin_rel hH (sp := E s₀) fun s s' ⟨⟨k, d, a, c, x, _⟩, ⟨k', d', a', c', x', _⟩⟩ =>
        ⟨fin_args hp hz hH k d a c x,
          by have := fin_args hp' hz hH k' d' a' c' x'; rwa [hq.dOEq, hq.dOEq, hq.scrEq,
            show arg s₀' 1 = arg s₀ 1 from hq.a (by decide)] at this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨k, d, a, c, x, r⟩ => fin_ok hp hz hH k d a c x r)
      (fun s ⟨k, d, a, c, x, r⟩ => fin_ok hp' hz hH k d a c x r)
  have rt := piece hp hp' hq (KF hH) (KT hH) (fun h => h.1) (fun s s' h h' => ag_ebp hq h.1 h'.1) hc.tail
    (fun hp₀ s h => tail_ok hp₀ hz hH h)
  unfold digestMain
  exact (pro.seq (ri.seq (r1.seq (ru.seq (r2.seq (rf.seq rt)))))).mono (fun _ _ h => h) fun _ _ _ => trivial

end

/-- The public arguments of the contract. -/
theorem pub_of {D : Nat} {hash : List Byte → List Byte} {n : Nat} {s₁ s₂ : State}
    (h : (digestScratch D hash n).pub s₁ s₂) : PubEq s₁ s₂ := by
  sig_pub [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    X86.abi] at h
  simp only [argVal32] at h
  obtain ⟨e, a0, a1, a2, a3⟩ := h
  refine ⟨e, fun i hi => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rwa [setWidth32_64, setWidth32_64] at a0
  · rwa [setWidth32_64, setWidth32_64] at a1
  · rwa [setWidth32_64, setWidth32_64] at a2
  · rwa [setWidth32_64, setWidth32_64] at a3

/-- `digestMain` is verified against `digestScratch`, given the taint checks
and a state satisfying it. -/
theorem verified (hH : HashOK H) (hc : Checks H) (hsat : ∃ s, (digestScratch H.D hH.SH.H.hash (nw H)).pre s) :
    Verified X86.target (digestMain H) (digestScratch H.D hH.SH.H.hash (nw H)) :=
  ⟨fun _ hs => correct (pre_of hs) (lay hH) hH,
    fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
      (ct (pre_of h₁) (pre_of h₂) (lay hH) hH (pub_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩

/-! ## Its stack, and `esp` -/

/-- `digestMain` uses at most 48 bytes of stack. -/
theorem digestMain_stack (hH : HashOK H) : stackUse (digestMain H) ≤ 48 := by
  have := hH.initSU; have := hH.updSU; have := hH.finSU
  simp only [digestMain, Impl.Pbkdf2.Stream.X86.copy, Hash.callInit, stackUse, frameBytes, List.length_cons,
    List.length_nil, Nat.max_le] at *
  omega

/-- `digestMain`'s instructions all satisfy `p` if those of the functions it
calls do and those of its own pieces do (`shapeOf`, decided for each hash
function). -/
theorem digestMain_allInstrs {p : Instr → Bool} (hb : (digestMain (shapeOf H)).allInstrs p = true)
    (hi : H.initC.allInstrs p = true) (hu : H.updC.allInstrs p = true) (hf : H.finC.allInstrs p = true) :
    (digestMain H).allInstrs p = true := by
  have e1 : (shapeOf H).initC = .block [] := rfl
  have e2 : (shapeOf H).updC = .block [] := rfl
  have e3 : (shapeOf H).finC = .block [] := rfl
  simp only [digestMain, Hash.callInit, Code.allInstrs, e1, e2, e3, hi, hu, hf, Bool.and_true] at hb ⊢
  exact hb

/-! ## In a frame of its own, wiped -/

/-- `digest`: `digestMain` in a frame holding its working space, which it
wipes before returning, verified against `Spec.Sha256.digestContract`, from
the locality of its postcondition (`Proof/MdStream/DigestScratch.lean`). -/
theorem framed (hH : HashOK H) (h : Verified X86.target (digestMain H) (digestScratch H.D hH.SH.H.hash (nw H)))
    (hsat : ∃ s, (Spec.Sha256.digestContract X86.abi H.D hH.SH.H.hash (48 + dframe H)).pre s)
    (hsp : (digestMain H).allInstrs (fun i => !Taint.clobbers i .esp) = true) :
    Verified X86.target (digest H) (Spec.Sha256.digestContract X86.abi H.D hH.SH.H.hash (48 + dframe H)) := by
  have hz := lay hH
  have := hz.fit; have := hz.W; have := hz.S; have := hz.D; have := hz.buf
  exact X86.Verified.stackScratchWiped (sig := digestSig H.D) (nm := "scratch") (e := .u64) (n := nw H)
    (post := digestPost H.D hH.SH.H.hash X86.abi.ptrBits) (wa := false) (stack := 48) (bytes := dframe H)
    (words := dbytes H / 4) h
    (by
      change 8 + 4 * 3 + nw H * 8 ≤ dframe H ∧ dframe H < 4096 ∧ dframe H % 4 = 0
      simp only [nw, dframe, dbytes, Hash.buf] at *; omega)
    hsp (digestMain_stack hH)
    (by simp only [nw, dbytes, Elem.size]; omega)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (MdStream.Digest.digestPost_local _ _ _)
    (MdStream.Digest.digestPostOut_local _ _ _) hsat (hl := rfl)

/-- Memory holding the arguments `0x1000, 0, 0x2000, 0x3000` at `0x6004`. -/
def digestMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x600D then 0x20 else if a = 0x6011 then 0x30 else 0

/-- A state satisfying `digestMain`'s precondition, with a digest of `D`
bytes, `L` bytes of `scratch` and an empty message. -/
def digestSat (D L : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := digestMem
  rd := [⟨0x1000, 0⟩, ⟨0x6004, 16⟩]
  wr := [⟨0x2000, D⟩, ⟨0x3000, L⟩]

/-- A state satisfying `digest`'s precondition, with a digest of `D` bytes
and an empty message. -/
def digestFrameSat (D : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := digestMem
  rd := [⟨0x1000, 0⟩, ⟨0x6004, 12⟩]
  wr := [⟨0x2000, D⟩]

end VG.Proof.MdStream.X86.Digest
