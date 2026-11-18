module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Hmac.Generic.Common

/-! ### `Pbkdf2.Md.X86.IterateCT`, which the modules that import this one used -/

section

/-! ### `Pbkdf2.Md.X86.Iterate`, which only this module used -/

section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86 (32-bit): correct

The iteration (`Impl/Pbkdf2/Md/X86.lean`) is correct for any hash function
whose code the proofs know (`MdOk`): `Md.hmac_step` says that its two
compressions per step compute HMAC. The arguments are on the stack: `scratch`,
`key`, `n` and `u` are loaded first (after our caller's registers are saved in
`scratch`), and `t` in each step. The loop counts the steps left in `edi` down
with `sub`, and branches on its result.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash copyW)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK iterG SavedRegs saveR savedRegs save_ok restore_ok callee_saved ea_at stk
  After setWidth_add toNat_add_ofNat stk_ret stk_args arg_contains arg_keep argAddr_eq saved_mem test_z)
open VG.Proof.Hmac.Generic.Common (InRegions.right' bytesAt_writeBytes_self' bytesAt_take covers_one)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_test
  sub_offset ofNat_beq_zero sub_ofNat eval_e eval_ne)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := arg s₀ 0
abbrev up : BitVec 32 := arg s₀ 1
abbrev tp : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
/-- The number of steps. -/
abbrev nn : Nat := (arg s₀ 2).toNat
abbrev keyR : Region := ⟨(key s₀).setWidth 64, 2 * H.S⟩
abbrev uR : Region := ⟨(up s₀).setWidth 64, H.D⟩
abbrev tR : Region := ⟨(tp s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- Byte `o` of `scratch`. -/
abbrev SA (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
/-- The hash value being compressed, as `ebx` holds it, and its address;
the block is right after it. -/
abbrev hv : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.st.buf
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨(scr s₀).setWidth 64, H.so⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR H s₀, uR H s₀, argR s₀]
  wr : s₀.wr = [tR H s₀, scR sc s₀]
  k_t : (keyR H s₀).Disjoint (tR H s₀)
  k_s : (keyR H s₀).Disjoint (scR sc s₀)
  u_t : (uR H s₀).Disjoint (tR H s₀)
  u_s : (uR H s₀).Disjoint (scR sc s₀)
  t_s : (tR H s₀).Disjoint (scR sc s₀)
  a_t : (argR s₀).Disjoint (tR H s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_t : (retR s₀).Disjoint (tR H s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_k : (stkR s₀).Disjoint (keyR H s₀)
  b_u : (stkR s₀).Disjoint (uR H s₀)
  b_t : (stkR s₀).Disjoint (tR H s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  nk : (key s₀).toNat + 2 * H.S ≤ 2 ^ 32
  nu : (up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (tp s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc
  hz : Sizes H

theorem pre_of {H : Hash} (hH : HashOK H.st) {sc : Nat} {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hz : Sizes H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  obtain e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h19]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit, hz⟩

/-! ## The parts of `scratch` -/

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ H.st.buf + H.N + H.B ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ 0 < H.D ∧ H.D ≤ H.N ∧ H.B ≤ 128 ∧ 64 ≤ H.B ∧
    H.S = H.N + H.B :=
  ⟨rfl, hp.fits, hp.nw, hp.hz.so, hp.hz.W, hp.hz.N.1, hp.hz.N.2.1, hp.hz.D.1, hp.hz.D.2.1, hp.hz.B4.2.2,
    hp.hz.B4.2.1, hp.hz.S⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) : Region.Sub ⟨SA s₀ o, n⟩ (scR sc s₀) :=
  sub_offset h (by have hp_nw := hp.nw; omega_using [h, hp_nw])

theorem hv_eq : (hv H s₀).setWidth 64 = SA s₀ H.st.buf :=
  setWidth_add (by have := bounds hp; omega_using [this])

theorem hv_toNat : (hv H s₀).toNat = (scr s₀).toNat + H.st.buf :=
  toNat_add_ofNat (by have := bounds hp; omega_using [this])

/-- The hash value and the block. -/
theorem hvR_sub : Region.Sub ⟨(hv H s₀).setWidth 64, H.N + H.B⟩ (scR sc s₀) := by
  rw [hv_eq hp]; obtain ⟨-, hf, -⟩ := bounds hp; exact off_sub hp (by omega_using [hf])

theorem cmp_sub : Region.Sub (cmpR H s₀) (scR sc s₀) := by
  obtain ⟨hb, hf, -, hso, -⟩ := bounds hp; exact Region.sub_prefix (by omega_using [hb, hf, hso])

theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by omega_using [hb, hf])

/-- The parts of `scratch` do not overlap. -/
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * sc) (hb : b + n ≤ 8 * sc) :
    Region.Disjoint ⟨SA s₀ a, m⟩ ⟨SA s₀ b, n⟩ :=
  VG.Proof.Hmac.Generic.Common.off_disj _ h (by have hp_nw := hp.nw; omega_using [ha, hp_nw]) (by have hp_nw := hp.nw; omega_using [hb, hp_nw])

theorem hv_cmp : Region.Disjoint ⟨(hv H s₀).setWidth 64, H.N + H.B⟩ (cmpR H s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := bounds hp
  rw [hv_eq hp]; exact Offset.disjoint_base _ (by omega_using [hb, hso]) (by omega_using [hw, hf])

theorem save_hv {n : Nat} (h : n ≤ H.N + H.B) : (saveR H.st (scr s₀)).Disjoint ⟨(hv H s₀).setWidth 64, n⟩ := by
  obtain ⟨hb, hf, -⟩ := bounds hp
  rw [hv_eq hp]; exact part_disj hp (by omega_using [hb]) (by omega_using [hf, hb]) (by omega_using [h, hf])

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR H s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := bounds hp
  exact Offset.disjoint_base _ (by omega_using [hso]) (hp.hz.buf_le64)

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have hp_spf := hp.spf; omega_using [hp_spf])

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have hp_spf := hp.spf; omega_using [hp_spf])

theorem t_blk : Region.Disjoint (tR H s₀) ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ := by
  obtain ⟨hb, hf, hw, -⟩ := bounds hp
  refine hp.t_s.sub_right fun a ha => hvR_sub hp a (Offset.sub_base _ (Nat.le_refl _) a ha)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: `T`, `scratch` and the stack below `esp`. -/
abbrev wrs (H : Hash) (sc : Nat) (s₀ : State) : List Region := [tR H s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on, with `m` steps left. -/
structure KR (H : Hash) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  ebx : s.gpr .ebx = hv H s₀
  esi : s.gpr .esi = key s₀
  edi : s.gpr .edi = BitVec.ofNat 32 m
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame (wrs H sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .ebx, .esi, .edi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {m : Nat} {s s' : State} (h : KR H sc s₀ m s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs H sc s₀, Region.Sub r r') : KR H sc s₀ m s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, (hg _ (by simp)).trans h.esi, (hg _ (by simp)).trans h.edi,
    h.saved.frame H.st hf hs, h.frame.trans (hf.sub hsub)⟩

/-- `KR` after code that writes only `eax`, `ecx` and `edx` and a part of
`scratch` other than where our caller's registers are. -/
theorem KR.write {m : Nat} {s s' : State} (h : KR H sc s₀ m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) {R : Region} (hf : Frame [R] s.mem s'.mem)
    (hs : (saveR H.st (scr s₀)).Disjoint R) (hsub : ∃ r' ∈ wrs H sc s₀, Region.Sub R r') : KR H sc s₀ m s' :=
  h.keep hrd hwr (fun r hr => hg r (by revert hr; decide +revert) (by revert hr; decide +revert)
    (by revert hr; decide +revert)) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub)

theorem stk_eq {m : Nat} {s : State} (hk : KR H sc s₀ m s) : stk s = stkR s₀ := by rw [stk, hk.esp]

end

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem mem_wr : scR sc s₀ ∈ s₀.wr ∧ tR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega_using [hi]) (by have hp_spf := hp.spf; omega_using [hp_spf])⟩

theorem KR.argEq {m : Nat} {s : State} (hk : KR H sc s₀ m s) {i : Nat} (hi : i < 5) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have hp_spf := hp.spf; omega_using [hp_spf]) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_t
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega_using [hi])

theorem KR.readArg {m : Nat} {s : State} (hk : KR H sc s₀ m s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {m : Nat} {s : State} (hk : KR H sc s₀ m s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_t
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

/-- `KR` after a call that writes parts of `scratch`. -/
theorem KR.call {m : Nat} {s s' : State} (h : KR H sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H.st (scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (scR sc s₀)) :
    KR H sc s₀ m s' := by
  have f := ha.frame
  rw [stk_eq h] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.b_s.symm.sub_left (save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The hash value and block are writable. -/
theorem cov_hv {s : State} (hwr : s.wr = s₀.wr) : Covers [⟨(hv H s₀).setWidth 64, H.N + H.B⟩] s.wr := by
  obtain ⟨hb, hf, -⟩ := bounds hp
  rw [hv_eq hp, hwr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scR sc s₀, (mem_wr hp).1, H.st.buf, rfl, by simp only; omega_using [hf]⟩

/-- The arguments of the compression of the block. -/
theorem cmpArgs {m : Nat} {s : State} (hk : KR H sc s₀ m s) (hax : s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N) :
    CmpArgs H.N H.B H.so s (hv H s₀) (scr s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := bounds hp
  have := hv_toNat hp
  exact
    { ebx := hk.ebx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := cov_hv hp hk.wr
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scR sc s₀, (mem_wr hp).1, 0, by simp, by simp only; omega_using [hb, hf, hso]⟩
      st_sc := hv_cmp hp
      b_st := by rw [stk_eq hk]; exact hp.b_s.sub_right (hvR_sub hp)
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cmp_sub hp)
      nst := by omega_using [hf, hw, this]
      nsc := by omega_using [hb, hso, this] }

/-- The key's bytes are as on entry. -/
theorem key_bytes {m : Nat} {s : State} (hk : KR H sc s₀ m s) {i : Nat} (hi : i < 2 * H.S) :
    s.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 i) :=
  hk.frame.bytes (R := keyR H s₀) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.k_t
    · exact hp.k_s
    · exact hp.b_k.symm) (by show 2 * H.S ≤ 2 ^ 64; have hp_nk := hp.nk; omega_using [hp_nk]) hi

end

/-! ## The loop invariant -/

section
variable {H : Hash} (hO : MdOk H) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  hO.md.step H.D (hO.md.stateAt s₀.mem ((key s₀).setWidth 64))
    (hO.md.stateAt s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 H.S))

end

/-- The loop invariant, with `m` steps left. -/
structure Inv {H : Hash} (hO : MdOk H) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop
    extends KR H sc s₀ m s where
  pad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB
  le : m ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM hO s₀) (nn s₀) (bytesAt s₀.mem ((up s₀).setWidth 64) H.D)
      (bytesAt s₀.mem ((tp s₀).setWidth 64) H.D) =
    Spec.Pbkdf2.iterate (stepM hO s₀) m (bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)
      (bytesAt s.mem ((tp s₀).setWidth 64) H.D)

/-! ## Loading a hash value of the key and compressing the block into it -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

/-- The block, after the hash value, is outside what the load and the
compression write. -/
theorem blk_disj {a n : Nat} (h₁ : H.N ≤ a) (h₂ : a + n ≤ H.N + H.B) :
    ∀ r ∈ [(⟨(hv H s₀).setWidth 64, H.N⟩ : Region), cmpR H s₀, stkR s₀],
      Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
  obtain ⟨hb, hf, hw, -⟩ := bounds hp
  have := hv_toNat hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ h₁ (by omega_using [hw, hf, h₂])
  · exact (hv_cmp hp).sub_left (Offset.sub_base _ (by omega_using [h₂]))
  · exact (hp.b_s.sub_right fun a' ha' => hvR_sub hp a' (Offset.sub_base _ (by omega_using [h₂]) a' ha')).symm

/-- Loading the key's hash value at `key + o` into the hash value being
compressed, and `eax` at the block. -/
theorem load_ok {o : Nat} (ho : o + H.N ≤ 2 * H.S) {m : Nat} {s : State} (h : KR H sc s₀ m s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ m s' → s'.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N →
      Frame [⟨(hv H s₀).setWidth 64, H.N⟩] s.mem s'.mem →
      hO.md.stateAt s'.mem ((hv H s₀).setWidth 64) = hO.md.stateAt s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.loadKey o ++ H.atBlk ++ rest)) s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have hN4 := hp.hz.N.2.2
  obtain hn4 : 4 * (H.N / 4) = H.N := by omega_using [hN4]
  obtain hvt := hv_toNat hp
  have nk := hp.nk
  obtain kc : Covers [keyR H s₀] (s.rd ++ s.wr) := covers_one (by rw [h.rd, hp.rd]; simp)
  rw [List.append_assoc]
  refine copyW_ok (by decide) (by decide) (H.N / 4) _ s _ h.esi h.ebx (by omega_using [nk, ho]) (by omega_using [hvt, hw, hf])
    (fun j hj => by rw [addr_eq (by omega_using [hj, nk, ho])]; exact inReg kc (by omega_using [hj, ho]) (by omega_using [hS, hw, hf]))
    (fun j hj => by rw [addr_eq (by omega_using [hj, hvt, hw, hf])]; exact inReg (cov_hv hp h.wr) (by omega_using [hj]) (by omega_using [hw, hf])) ?_
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [hn4]
    exact hp.k_s.sep (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho, nk]))
      (by rw [BitVec.add_zero, hv_eq hp]; exact Offset.contains_base _ (by omega_using [hf]) (by omega_using [hvt]))
  rw [hn4, BitVec.add_zero] at m₁
  obtain f₁ : Frame [⟨(hv H s₀).setWidth 64, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => ?_
  obtain k₂ : KR H sc s₀ m s₂ := h.write (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r h1 h2 _ => by rw [g₂ r h1, g₁ r h2]) (m₂ ▸ f₁) (save_hv hp (Nat.le_add_right _ _))
    ⟨scR sc s₀, by simp, fun a ha => hvR_sub hp a (Region.sub_prefix (Nat.le_add_right _ _) a ha)⟩
  refine k s₂ k₂ (by rw [e₂, g₁ _ (by decide), h.ebx]) (m₂ ▸ f₁) ?_
  refine hO.reloc _ _ _ _ fun i hi => ?_
  rw [m₂, m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hS, nk]),
    bytesAt_getD' _ _ hi, Memory.add_ofNat]
  exact key_bytes hp h (by omega_using [hi, ho])

/-- The compression of the block into the hash value. -/
theorem cmpS_ok {m : Nat} {s : State} (h : KR H sc s₀ m s) (hax : s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ m s' → Frame [⟨(hv H s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((hv H s₀).setWidth 64) = hO.md.compress (hO.md.stateAt s.mem ((hv H s₀).setWidth 64))
        (hO.md.blockAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  refine cmp_ok hO.comp (by omega_using [hB64]) (cmpArgs hp h hax) fun s₃ ha e₃ => ?_
  obtain k₃ : KR H sc s₀ m s₃ := h.call hp ha (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact save_hv hp (Nat.le_add_right _ _)
      · exact save_cmp hp) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact fun a ha => hvR_sub hp a (Region.sub_prefix (Nat.le_add_right _ _) a ha)
      · exact cmp_sub hp)
  have f := ha.frame
  rw [stk_eq h] at f
  exact k s₃ k₃ (f.mono (by simp)) e₃

theorem lc_ok {o : Nat} (ho : o + H.N ≤ 2 * H.S) {m : Nat} {s : State} (h : KR H sc s₀ m s)
    (hpad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ m s' → Frame [⟨(hv H s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((hv H s₀).setWidth 64) = hO.md.compress
        (hO.md.stateAt s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 o))
        (hO.md.tailBlock H.D (bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)) →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D → WP isa c s' Q) :
    WP isa (.block (H.loadKey o ++ H.atBlk)) s fun s' => WP isa (.seq H.cmp c) s' Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  rw [← List.append_nil (H.loadKey o ++ H.atBlk)]
  refine load_ok hO hp ho h fun s₂ k₂ ax₂ f₁ st₂ => WP.block_nil (WP.seq (cmpS_ok hO hp k₂ ax₂ fun s₃ k₃ f₂ e₃ => ?_))
  obtain dB : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
      ∀ r ∈ [(⟨(hv H s₀).setWidth 64, H.N⟩ : Region)], Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r :=
    fun h₁ h₂ r hr => blk_disj hp h₁ h₂ r (by simp only [List.mem_singleton] at hr; simp [hr])
  obtain pad₂ : bytesAt s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 H.D) (H.B - H.D) =
      hO.md.tailPad H.D := by
    rw [Memory.add_ofNat, Memory.frame_bytesAt f₁ (dB (by omega_using []) (hp.hz.NDB_le)) (by omega_using [hB]), hpad, hO.tail]
  obtain u₂ : bytesAt s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
      bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D :=
    Memory.frame_bytesAt f₁ (dB (by omega_using []) (by omega_using [hB64, hDN, hN])) (hp.hz.D_le64)
  obtain f₃ : Frame [⟨(hv H s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s₃.mem :=
    (f₁.mono (by simp)).trans f₂
  refine k s₃ k₃ f₃ ?_ ?_ ?_
  · rw [e₃, st₂, Md.blockAt_tailPad (by omega_using [hB64, hDN, hN]) pad₂, u₂]
  · rw [Memory.frame_bytesAt f₃ (blk_disj hp (by omega_using []) (hp.hz.NDB_le)) (by omega_using [hB]), hpad]
  · exact Memory.frame_bytesAt f₃ (blk_disj hp (by omega_using []) (by omega_using [hN, hDN, hB64])) (hp.hz.D_le64)

/-! ## The end of a step: the digest, `T ← T ⊕ U` and the count -/

omit hp in
theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  refine congrArg (writeBytes m d) ?_
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

omit hp in
theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine VG.Proof.Sha256.X86.Stream.WP.cons
    (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 32) false false).setReg d (s.gpr d ^^^ s.mem.readW a 32))
    ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load32, ha, hin]

omit hp in
/-- `T ← T ⊕ U` for the first `n` words of `T` at `t` (in `edx`) and `U` at
`x + N` (`x` in `ebx`). -/
theorem xor_ok {x t : BitVec 32} (hd : Region.Disjoint ⟨t.setWidth 64, H.D⟩ ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩)
    (fx : x.toNat + H.N + H.D ≤ 2 ^ 32) (ft : t.toNat + H.D ≤ 2 ^ 32) :
    ∀ n, 4 * n ≤ H.D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebx = x → s.gpr .edx = t →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr t (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (t.setWidth 64)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (t.setWidth 64) (4 * n))
          (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbx hdx hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_using [hn]) _ s Q hbx hdx (fun j hj => hin j (by omega_using [hj])) (fun j hj => hout j (by omega_using [hj]))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.xorW, List.cons_append, List.nil_append]
    obtain eU : addr x (H.N + 4 * n) = x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n) := by
      rw [addr_eq (by omega_using [fx, hn]), Memory.add_ofNat]
    obtain eT : addr t (4 * n) = t.setWidth 64 + BitVec.ofNat 64 (4 * n) := addr_eq (by omega_using [ft, hn])
    refine wp_movm (a := addr x (H.N + 4 * n)) (by rw [ea_at, g₁ _ (by decide), hbx])
      (by rw [rd₁, wr₁]; exact hin n (Nat.lt_succ_self _)) fun s₂ u₂ => ?_
    obtain hw := hout n (Nat.lt_succ_self _)
    refine wp_xorm (a := addr t (4 * n)) (by rw [ea_at, u₂.other _ (by decide), g₁ _ (by decide), hdx])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact InRegions.right' hw) fun s₃ u₃ => ?_
    refine wp_store (a := addr t (4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hdx])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw) fun s₄ u₄ => k s₄ (fun r hr => by
        rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr]) (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁])
        (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    obtain hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (t.setWidth 64) (4 * n))
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, writeW_xor32, m₁, eU, eT,
      bytesAt_writeBytes_sep (p := t.setWidth 64 + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem (t.setWidth 64) _ (Spec.Pbkdf2.xorBytes
        (bytesAt s.mem (t.setWidth 64 + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_using [ft, hn])
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro y h₁ h₂
      rw [hl] at h₂
      exact hd y (by simp only [Region.Contains]; omega_using [hn, h₂]) (Memory.off_contains h₁ (by omega_using [hn]) (by omega_using [ft, hn]))
    · omega_using []
    · intro y h₁ h₂
      rw [hl] at h₂
      exact Memory.sep_after h₁ h₂ (by omega_using [ft, hn])
    · omega_using []

theorem tail_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : KR H sc s₀ m s)
    (hpad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB)
    {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ (m - 1) s' → s'.zf = some (decide (m - 1 = 0)) →
      Frame [⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩, tR H s₀] s.mem s'.mem →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        (hO.md.digest (hO.md.stateAt s.mem ((hv H s₀).setWidth 64))).take H.D →
      bytesAt s'.mem ((tp s₀).setWidth 64) H.D = Spec.Pbkdf2.xorBytes (bytesAt s.mem ((tp s₀).setWidth 64) H.D)
        ((hO.md.digest (hO.md.stateAt s.mem ((hv H s₀).setWidth 64))).take H.D) → Q s') :
    WP isa (.block (H.digest ++ H.tStep)) s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have hD4 := hp.hz.D.2.2
  obtain hvt := hv_toNat hp
  have nt := hp.nt
  obtain hD4' : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  obtain sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (Nat.le_refl _) a ha)
  refine digest_ok hp.hz hO.out h.ebx (by omega_using [hvt, hw, hf]) (cov_hv hp h.wr) hpad fun s₁ g₁ rd₁ wr₁ f₁ b₁ p₁ => ?_
  obtain k₁ : KR H sc s₀ m s₁ := h.write rd₁ wr₁ g₁ f₁
    ((save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (Nat.le_refl _))) ⟨scR sc s₀, by simp, sbB⟩
  simp only [Hash.tStep, List.cons_append, List.nil_append]
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, k₁.esp]; rfl) (argIn hp k₁.rd k₁.wr (by decide))
    fun s₂ u₂ => ?_
  obtain dx₂ : s₂.gpr .edx = tp s₀ := by rw [u₂.gpr, k₁.readArg hp (by decide)]
  obtain k₂ : KR H sc s₀ m s₂ := k₁.write u₂.rd u₂.wr (fun r _ _ h3 => u₂.other r h3) (R := ⟨0, 0⟩)
    (by rw [u₂.mem]; exact Frame.refl _ _) (fun _ _ h => by simp [Region.Contains] at h)
    ⟨scR sc s₀, by simp, fun _ h => by simp [Region.Contains] at h⟩
  obtain hd : Region.Disjoint ⟨(tp s₀).setWidth 64, H.D⟩ ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩ :=
    (t_blk hp).sub_right (Region.sub_prefix (by omega_using [hB64, hDN, hN]))
  refine xor_ok hd (by omega_using [hvt, hB64, hDN, hN, hw, hf]) nt (H.D / 4) (by omega_using []) _ s₂ _ k₂.ebx dx₂
    (fun j hj => by
      rw [addr_eq (by omega_using [hf, hw, hN, hDN, hB64, hvt, hj])]
      exact InRegions.right' (inReg (cov_hv hp k₂.wr) (by omega_using [hj, hB64, hDN, hN]) (by omega_using [hN, hB])))
    (fun j hj => by
      rw [addr_eq (by omega_using [hj, nt]), k₂.wr]
      exact ⟨tR H s₀, (mem_wr hp).2, Offset.contains_base _ (by omega_using [hj]) (by omega_using [nt, hj])⟩)
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  rw [hD4'] at m₃
  obtain hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₂.mem ((tp s₀).setWidth 64) H.D)
      (bytesAt s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)).length = H.D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  obtain f₃ : Frame [tR H s₀] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  obtain k₃ : KR H sc s₀ m s₃ := k₂.write rd₃ wr₃ (fun r _ h2 _ => g₃ r h2) f₃
    (hp.t_s.sub_right (save_sub hp)).symm ⟨tR H s₀, by simp, fun _ h => h⟩
  refine wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  obtain e₄ : s₃.gpr .edi - 1 = BitVec.ofNat 32 (m - 1) := by
    rw [k₃.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hm]
  obtain k₄ : KR H sc s₀ (m - 1) s₄ :=
    ⟨by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.other _ (by decide), k₃.esp],
      by rw [u₄.other _ (by decide), k₃.ebp], by rw [u₄.other _ (by decide), k₃.ebx],
      by rw [u₄.other _ (by decide), k₃.esi], by rw [u₄.gpr, e₄], u₄.mem ▸ k₃.saved, u₄.mem ▸ k₃.frame⟩
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  obtain tB : ∀ r ∈ [tR H s₀], Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact (t_blk hp).symm
  obtain tB' : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
      ∀ r ∈ [tR H s₀], Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h₁ h₂ r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ((t_blk hp).sub_right (Offset.sub _ (by omega_using [h₁]) (by omega_using [h₂]))).symm
  refine k s₄ k₄ (by rw [z₄, e₄, ofNat_beq_zero (by omega_using [hn])]) ?_ ?_ ?_ ?_
  · rw [u₄.mem]; exact (f₁.mono (by simp)).trans (m₂ ▸ f₃.mono (by simp))
  · rw [u₄.mem, Memory.frame_bytesAt f₃ (tB' (by omega_using []) (hp.hz.NDB_le)) (by omega_using [hB]), m₂, p₁]
  · rw [u₄.mem, Memory.frame_bytesAt f₃ (tB' (Nat.le_refl _) (by omega_using [hB64, hDN, hN])) (hp.hz.D_le64), m₂, b₁]
  · have hT₁ : bytesAt s₁.mem ((tp s₀).setWidth 64) H.D = bytesAt s.mem ((tp s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact t_blk hp) (by omega_using [nt])
    rw [u₄.mem, m₃, bytesAt_writeBytes_self' hxl (by omega_using [nt]), m₂, hT₁, b₁]

end

/-! ## A step -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

omit hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {r : Nat} {s : State} (h : Inv hO sc s₀ (r + 1) s) :
    WP isa H.body s fun s' => eval .ne s' = some (r != 0) ∧ Inv hO sc s₀ r s' := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  obtain hvt := hv_toNat hp
  obtain hlt : r + 1 < 2 ^ 32 := by have h_le := h.le; have := (arg s₀ 2).isLt; simp only [nn] at *; omega_using [h_le]
  obtain sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (Nat.le_refl _) a ha)
  unfold Hash.body
  refine WP.seq (lc_ok hO hp (o := 0) (by omega_using [hS]) h.toKR h.pad fun s₂ k₂ f₂ e₂ p₂ u₂ => ?_)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine digest_ok hp.hz hO.out k₂.ebx (by omega_using [hf, hw, hvt]) (cov_hv hp k₂.wr) p₂ fun s₃ g₃ rd₃ wr₃ f₃ b₃ p₃ => ?_
  obtain k₃ : KR H sc s₀ (r + 1) s₃ := k₂.write rd₃ wr₃ g₃ f₃
    ((save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (Nat.le_refl _))) ⟨scR sc s₀, by simp, sbB⟩
  refine lc_ok hO hp (o := H.S) (by omega_using [hS]) k₃ p₃ fun s₅ k₅ f₅ e₅ p₅ u₅ => ?_
  refine tail_ok hO hp (m := r + 1) (by omega_using []) hlt k₅ p₅ fun s₈ k₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [Nat.add_sub_cancel] at k₈ z₈
  -- `T` is untouched until the end.
  obtain dT : ∀ {rs : List Region}, (∀ q ∈ rs, Region.Sub q (scR sc s₀) ∨ q = stkR s₀) →
      ∀ q ∈ rs, Region.Disjoint ⟨(tp s₀).setWidth 64, H.D⟩ q := by
    intro rs hrs q hq
    rcases hrs q hq with hq | rfl
    · exact hp.t_s.sub_right hq
    · exact hp.b_t.symm
  obtain sub₁ : ∀ q ∈ [(⟨(hv H s₀).setWidth 64, H.N⟩ : Region), cmpR H s₀, stkR s₀],
      Region.Sub q (scR sc s₀) ∨ q = stkR s₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl)
    · exact .inl fun a ha => hvR_sub hp a (Region.sub_prefix (Nat.le_add_right _ _) a ha)
    · exact .inl (cmp_sub hp)
    · exact .inr rfl
  obtain hT₅ : bytesAt s₅.mem ((tp s₀).setWidth 64) H.D = bytesAt s.mem ((tp s₀).setWidth 64) H.D := by
    rw [Memory.frame_bytesAt f₅ (dT sub₁) (by omega_using [hN, hDN]),
      Memory.frame_bytesAt f₃ (dT (by simp only [List.mem_singleton]; rintro q rfl; exact .inl sbB)) (by omega_using [hN, hDN]),
      Memory.frame_bytesAt f₂ (dT sub₁) (by omega_using [hN, hDN])]
  rw [hT₅, e₅, b₃, e₂, show (key s₀).setWidth 64 + BitVec.ofNat 64 0 = (key s₀).setWidth 64 by simp] at t₈
  rw [e₅, b₃, e₂, show (key s₀).setWidth 64 + BitVec.ofNat 64 0 = (key s₀).setWidth 64 by simp] at b₈
  refine ⟨?_, { k₈ with pad := p₈, le := by have h_le := h.le; omega_using [h_le], val := ?_ }⟩
  · rw [eval_ne, z₈, Option.map_some]
    cases r <;> rfl
  · rw [h.val, iterate_succ, b₈, t₈]; rfl

theorem loop_ok {n : Nat} {s : State} (h : Inv hO sc s₀ n s) (hz' : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop H.body .ne)) s (Inv hO sc s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show s.zf = _; exact hz') (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega_using [hb]⟩
    refine WP.loop (fun m s => Inv hO sc s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hO hp hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega_using [], hi⟩

end

/-! ## The prologue and the epilogue -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem pro_ok : WP isa (.block H.prologue) s₀ fun s => Inv hO sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)) := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  obtain ⟨sR, tR'⟩ := mem_wr hp
  obtain hvt := hv_toNat hp
  have hD4 := hp.hz.D.2.2
  obtain hD4' : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  have tl := hp.hz.tail_length
  obtain nu := hp.nu; have nt := hp.nt
  obtain dA : ∀ r ∈ [saveR H.st (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  simp only [Hash.prologue, List.append_assoc, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at]; rfl) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega_using [hf, hb]) (by omega_using [hw])
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  obtain e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  obtain rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.arg_sub rfl (by omega_using [hi]) (by have hp_spf := hp.spf; omega_using [hp_spf]))) (by decide)
  obtain i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 0) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 2) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 2 (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide))
    fun s₈ u₈ => ?_
  obtain m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  obtain wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  obtain bp₈ : s₈.gpr .ebp = scr s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl
  obtain bx₈ : s₈.gpr .ebx = hv H s₀ := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]
    rfl
  obtain si₈ : s₈.gpr .esi = key s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.mem, rA 0 (by decide)]
  obtain di₈ : s₈.gpr .edi = arg s₀ 2 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem,
      rA 2 (by decide)]
  obtain dx₈ : s₈.gpr .edx = up s₀ := by
    rw [u₈.gpr, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, rA 1 (by decide)]
  obtain sp₈ : s₈.gpr .esp = E s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
  obtain ucov : Covers [uR H s₀] (s₈.rd ++ s₈.wr) := covers_one (by rw [rd₈, hp.rd]; simp)
  -- `U` into the block.
  refine copyW_ok (by decide) (by decide) (H.D / 4) _ s₈ _ dx₈ bx₈ (by omega_using [nu]) (by omega_using [hf, hw, hN, hDN, hB64, hvt])
    (fun j hj => by
      rw [addr_eq (by omega_using [hj, nu])]; have := inReg (o := 4 * j) (n := 4) ucov (by omega_using [hj]) (by omega_using [nt])
      rwa [show 0 + 4 * j = 4 * j by omega_using []])
    (fun j hj => by rw [addr_eq (by omega_using [hf, hw, hN, hDN, hB64, hvt, hj])]; exact inReg (cov_hv hp wr₈) (by omega_using [hj, hB64, hDN, hN]) (by omega_using [hN, hB])) ?_
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  · rw [hD4', BitVec.add_zero]
    exact hp.u_s.sep (Region.contains_self _ _)
      (by rw [hv_eq hp, Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hB64, hDN, hN, hf]) (by omega_using [hw, hf]))
  rw [hD4', BitVec.add_zero] at m₉
  -- The padding.
  refine pad_ok hp.hz (s := s₉) (x := hv H s₀) (by rw [g₉ _ (by decide), bx₈]) (by omega_using [hvt, hw, hf]) (cov_hv hp (wr₉.trans wr₈))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  refine wp_test fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  obtain m₁₁ : s₁₁.mem = writeBytes (writeBytes s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N)
      (bytesAt s₂.mem ((up s₀).setWidth 64) H.D)) ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB := by
    rw [u₁₁.mem, m₁₀, m₉, m₈]
  obtain gr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₁.gpr r = s₈.gpr r := fun r _ h2 _ => by
    rw [u₁₁.gpr, g₁₀ r h2, g₉ r h2]
  obtain fB : Frame [⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₂.mem s₁₁.mem := by
    rw [m₁₁]
    refine (writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (k := H.B)
        (by omega_using [hB64, hDN, hN]) (by omega_using [])
      rwa [BitVec.add_zero] at this
    · rw [tl, ← Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hB64, hDN, hN]) (by omega_using [nt])
  obtain sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (Nat.le_refl _) a ha)
  obtain dsB : (saveR H.st (scr s₀)).Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ :=
    (save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (Nat.le_refl _))
  obtain sv : SavedRegs H.st (scr s₀) s₀ s₁₁.mem :=
    (sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)).frame H.st fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dsB)
  obtain fr : Frame (wrs H sc s₀) s₀.mem s₁₁.mem :=
    (f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩).trans
    (fB.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, sbB⟩)
  obtain edi : s₁₁.gpr .edi = BitVec.ofNat 32 (nn s₀) := by
    rw [gr _ (by decide) (by decide) (by decide), di₈, nn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain dU : Mem.Sep ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D
      ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB.length := by
    rw [tl, ← Memory.add_ofNat]
    have := Offset.sep ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (e := H.D)
      (k := H.B - H.D) (.inl (by omega_using [])) (by omega_using [nt]) (by omega_using [hB, nt])
    rwa [BitVec.add_zero] at this
  refine ⟨⟨⟨by rw [u₁₁.rd, rd₁₀, rd₉, rd₈], by rw [u₁₁.wr, wr₁₀, wr₉, wr₈],
    by rw [gr _ (by decide) (by decide) (by decide), sp₈], by rw [gr _ (by decide) (by decide) (by decide), bp₈],
    by rw [gr _ (by decide) (by decide) (by decide), bx₈], by rw [gr _ (by decide) (by decide) (by decide), si₈],
    edi, sv, fr⟩, ?_, Nat.le_refl _, ?_⟩, ?_⟩
  · rw [m₁₁, ← tl, bytesAt_writeBytes_self' rfl (by omega_using [hB, tl])]
  · -- `U` and `T`.
    obtain hU₂ : bytesAt s₂.mem ((up s₀).setWidth 64) H.D = bytesAt s₀.mem ((up s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt f₂' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.u_s.sub_right (save_sub hp)) (by omega_using [nt])
    obtain hU : bytesAt s₁₁.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        bytesAt s₀.mem ((up s₀).setWidth 64) H.D := by
      rw [m₁₁, bytesAt_writeBytes_sep _ _ dU (by omega_using [nt]), bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hp.hz.D_lt64),
        hU₂]
    obtain hT : bytesAt s₁₁.mem ((tp s₀).setWidth 64) H.D = bytesAt s₀.mem ((tp s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt ((f₂'.mono (rs' := [saveR H.st (scr s₀), ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩])
        (by simp)).trans (fB.mono (by simp))) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.t_s.sub_right (save_sub hp)
        · exact t_blk hp) (by omega_using [nt])
    rw [hU, hT]
  · rw [z₁₁, g₁₀ _ (by decide), g₉ _ (by decide), di₈, test_z]

omit hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {m : Mem}
    (hT : bytesAt m ((tp s₀).setWidth 64) H.D = Spec.Pbkdf2.iterate (stepM hO s₀) (nn s₀)
      (bytesAt s₀.mem ((up s₀).setWidth 64) H.D) (bytesAt s₀.mem ((tp s₀).setWidth 64) H.D))
    {k0 : List Byte} (hk : k0.length = hO.hH.SH.H.blockSize)
    (hi : hO.hH.SH.Repr s₀.mem ((key s₀).setWidth 64) (xorPad k0 ipad))
    (ho : hO.hH.SH.Repr s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 hO.hH.SH.stateBytes) (xorPad k0 opad)) :
    bytesAt m ((tp s₀).setWidth 64) hO.hH.SH.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey hO.hH.SH.H k0) (nn s₀) (bytesAt s₀.mem ((up s₀).setWidth 64) hO.hH.SH.digestBytes)
        (bytesAt s₀.mem ((tp s₀).setWidth 64) hO.hH.SH.digestBytes) := by
  have hl := hO.link
  obtain hB : 0 < H.B := by have hl_DL := hl.DL; omega_using [hl_DL]
  rw [hl.hB] at hk
  rw [hl.hS, ← hO.sizes.S] at ho
  obtain li : (xorPad k0 ipad).length = H.B := by simp [xorPad, hk]
  obtain lo : (xorPad k0 opad).length = H.B := by simp [xorPad, hk]
  obtain ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  obtain eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length _ hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem epilogue_ok {s : State} (h : Inv hO sc s₀ 0 s) :
    WP isa (.block H.st.restore) s fun s' => abiPreserved s₀ s' ∧ (iterG hO.hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf, hw, -⟩ := bounds hp
  refine WP.mono (restore_ok H.st h.ebp h.saved (by rw [h.wr]; exact (mem_wr hp).1) (by omega_using [hf, hb]) hp.nw)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact h.toKR.ret hp⟩, fun k0 hk hi ho' => ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), h.esp]
    · exact hg r (callee_saved r hr he)
  · rw [hm]; exact post_eq hO h.val.symm hk hi ho'

theorem correct : WP isa H.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hO.hH.SH sc).post s₀ s' := by
  unfold Hash.iterate
  refine WP.seq (WP.mono (pro_ok hO hp) fun s₁ ⟨h, hz'⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hO hp h hz') fun s₂ h₂ => epilogue_ok hO hp h₂)

end

end VG.Proof.Pbkdf2.Md.X86.Iterate

end

end

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86 (32-bit): constant time

As for HMAC's `init` (`HmacInitCT.lean`): the pieces between the calls are
checked by the taint analysis, those that read the arguments on the stack (the
prologue, and the end of a step, which loads `t`) with the arguments public
(`argTaint`); the calls of the compression function are related by `cmp_rel`,
from its contract. Then `iterate` is verified against the contract with the
arguments read only (`iterG`), and with them writable (`iterW`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (HashOK iterG iterW argTaint ArgsOut agree_argTaint rel_agree rel_wp stk)
open VG.Proof.Sha256.X86.Stream (eval_e eval_ne)
open Spec.Sha256 (bytesAt)

/-- The registers `KR` fixes. -/
abbrev pubRegs : List Reg := [.esp, .ebp, .ebx, .esi, .edi]

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block H.prologue) hc).isSome = true
  load : ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block (H.loadKey 0 ++ H.atBlk)) hc).isSome = true
  mid : ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block (H.digest ++ H.loadKey H.S ++ H.atBlk)) hc).isSome = true
  tail : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .esi, .edi] (4 + 4 * 5))
    (.block (H.digest ++ H.tStep)) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.st.restore) hc).isSome = true

theorem skip_check : ∃ hc, (VG.Taint.check taint (τr []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, arg s₀ i = arg s₀' i

/-- What the pieces keep, and the padding. -/
structure KP (H : Hash) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop extends KR H sc s₀ m s where
  pad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB

/-! ## Each piece, in one run -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hO hp

theorem b1_ok {m : Nat} {s : State} (h : KP H sc s₀ m s) :
    WP isa (.block (H.loadKey 0 ++ H.atBlk)) s fun t =>
      KP H sc s₀ m t ∧ t.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N := by
  rw [← List.append_nil (H.loadKey 0 ++ H.atBlk)]
  have := bounds hp
  refine load_ok hO hp (by have := hp.hz.S; omega_arith) h.toKR fun s₂ k₂ ax₂ f₁ _ => WP.block_nil ⟨⟨k₂, ?_⟩, ax₂⟩
  rw [Memory.frame_bytesAt f₁ (fun r hr => blk_disj hp (by omega_arith) (by omega_arith) r (by
    simp only [List.mem_singleton] at hr; simp [hr])) (by omega_arith), h.pad]

theorem c_ok {m : Nat} {s : State} (h : KP H sc s₀ m s) (hax : s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N) :
    WP isa H.cmp s (KP H sc s₀ m) := by
  have := bounds hp
  refine cmpS_ok hO hp h.toKR hax fun s₃ k₃ f₃ _ => ⟨k₃, ?_⟩
  rw [Memory.frame_bytesAt f₃ (blk_disj hp (by omega_arith) (by omega_arith)) (by omega_arith), h.pad]

theorem b2_ok {m : Nat} {s : State} (h : KP H sc s₀ m s) :
    WP isa (.block (H.digest ++ H.loadKey H.S ++ H.atBlk)) s fun t =>
      KP H sc s₀ m t ∧ t.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have := hv_toNat hp; have := hp.hz.DL
  have sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (by omega_arith) a ha)
  rw [List.append_assoc]
  refine digest_ok hp.hz hO.out h.ebx (by omega_arith) (cov_hv hp h.wr) h.pad fun s₃ g₃ rd₃ wr₃ f₃ _ p₃ => ?_
  have k₃ : KR H sc s₀ m s₃ := h.toKR.write rd₃ wr₃ g₃ f₃
    ((save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega_arith))) ⟨scR sc s₀, by simp, sbB⟩
  rw [← List.append_nil (H.loadKey H.S ++ H.atBlk)]
  refine load_ok hO hp (by omega_arith) k₃ fun s₂ k₂ ax₂ f₁ _ => WP.block_nil ⟨⟨k₂, ?_⟩, ax₂⟩
  rw [Memory.frame_bytesAt f₁ (fun r hr => blk_disj hp (by omega_arith) (by omega_arith) r (by
    simp only [List.mem_singleton] at hr; simp [hr])) (by omega_arith), p₃]

theorem b3_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : KP H sc s₀ m s) :
    WP isa (.block (H.digest ++ H.tStep)) s fun t => KP H sc s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)) :=
  tail_ok hO hp hm hn h.toKR h.pad fun _ k z _ p _ _ => ⟨⟨k, p⟩, z⟩

end

/-! ## Two runs -/

variable {H : Hash} (hO : MdOk H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [hq.args 2 (by decide)]

theorem eqs (hq : PubEq s₀ s₀') : scr s₀' = scr s₀ ∧ hv H s₀' = hv H s₀ :=
  ⟨(hq.args 4 (by decide)).symm, by rw [hv, hv, scr, scr, hq.args 4 (by decide)]⟩

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR H sc s₀ m s)
    (h' : KR H sc s₀' m s') : ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, (eqs (H := H) hq).1]
  · rw [h.ebx, h'.ebx, (eqs (H := H) hq).2]
  · rw [h.esi, h'.esi, key, key, hq.args 0 (by decide)]
  · rw [h.edi, h'.edi]

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre H sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega_arith) h.r_t h.a_t
  · exact Taint.frame_disjoint (by have := h.spf; omega_arith) h.r_s h.a_s

include hO hp hp' hq

/-- A call of the compression function, in both runs. -/
theorem cmp_rel' {m : Nat} :
    RelCT isa (fun s s' => (KP H sc s₀ m s ∧ s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N) ∧
        (KP H sc s₀' m s' ∧ s'.gpr .eax = hv H s₀' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => KP H sc s₀ m s ∧ KP H sc s₀' m s' := by
  obtain ⟨e4, ehv⟩ := eqs (H := H) hq
  have hB : 0 < H.B := by have := hp.hz.B4; omega_arith
  exact rel_wp (cmp_rel hO.comp hB (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
      ⟨cmpArgs hp k.toKR a, by have := cmpArgs hp' k'.toKR a'; rwa [e4, ehv] at this, k.esp,
        by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, a⟩ => c_ok hO hp k a) (fun _ ⟨k, a⟩ => c_ok hO hp' k a)

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) :
    RelCT isa (fun s s' => KP H sc s₀ m s ∧ KP H sc s₀' m s') H.body
      fun s s' => (KP H sc s₀ (m - 1) s ∧ s.zf = some (decide (m - 1 = 0))) ∧
        (KP H sc s₀' (m - 1) s' ∧ s'.zf = some (decide (m - 1 = 0))) := by
  have b1 := rel_agree (F := KP H sc s₀ m) (F' := KP H sc s₀' m) (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h.toKR h'.toKR)) hc.load
    (fun _ h => b1_ok hO hp h) (fun _ h => b1_ok hO hp' h)
  have b2 := rel_agree (F := KP H sc s₀ m) (F' := KP H sc s₀' m) (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h.toKR h'.toKR)) hc.mid
    (fun _ h => b2_ok hO hp h) (fun _ h => b2_ok hO hp' h)
  have b3 := rel_agree (F := KP H sc s₀ m) (F' := KP H sc s₀' m) (argTaint [.ebp, .ebx, .esi, .edi] (4 + 4 * 5)) (fun s s' k k' =>
      agree_argTaint (fun r hr => kr_agree hq k.toKR k'.toKR r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind))
        (kr_agree hq k.toKR k'.toKR .esp (by simp)) (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
        fun j hj => by rw [k.toKR.argEq hp hj, k'.toKR.argEq hp' hj, hq.args j hj]) hc.tail
    (fun _ h => b3_ok hO hp hm hn h) (fun _ h => b3_ok hO hp' hm hn h)
  exact b1.seq ((cmp_rel' hO hp hp' hq).seq (b2.seq ((cmp_rel' hO hp hp' hq).seq b3)))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ KP H sc s₀ n s ∧ KP H sc s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') n) H.body fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → KP H sc s₀ 0 s ∧ KP H sc s₀' 0 s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt : nn s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · refine ((body_rel hO hp hp' hq hc hn.1 (by omega_arith)).mono
      (P' := LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
      fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e : isa.eval .ne t = some (!decide (n - 1 = 0)) := by show eval .ne t = _; rw [eval_ne, z]; rfl
    have e' : isa.eval .ne t' = some (!decide (n - 1 = 0)) := by show eval .ne t' = _; rw [eval_ne, z']; rfl
    rw [e, e']
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega_arith, by omega_arith, by omega_arith, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : Checks H) :
    RelCT isa (fun s s' => (KP H sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (KP H sc s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop H.body .ne))
      fun s s' => KP H sc s₀ 0 s ∧ KP H sc s₀' 0 s' := by
  have hN := hq.nn
  have ev : ∀ {t : State} {k : Nat}, t.zf = some (decide (k = 0)) → isa.eval .e t = some (decide (k = 0)) :=
    fun h => by show eval .e _ = _; rw [eval_e, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_agree (c := .block [])
        (F := fun s => KP H sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
        (F' := fun s => KP H sc s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0)))
        (G := KP H sc s₀ 0) (G' := KP H sc s₀' 0) (τr [])
        (fun s s' h h' => agree_regs (by simp)) skip_check
        (fun s h => WP.block_nil (e ▸ h.1)) (fun s h => WP.block_nil (e' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀'))
      (step_rel hO hp hp' hq hc) (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega_arith, Nat.le_refl _, h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.iterate fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => KP H sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
    (G' := fun s => KP H sc s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0)))
    (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact WP.mono (pro_ok hO hp) fun _ ⟨h, z⟩ => ⟨⟨h.toKR, h.pad⟩, z⟩)
    (fun _ e => by rw [e]; exact WP.mono (pro_ok hO hp') fun _ ⟨h, z⟩ => ⟨⟨h.toKR, h.pad⟩, z⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KP H sc s₀ 0 s ∧ KP H sc s₀' 0 s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact kr_agree hq h.1.toKR h.2.toKR .ebp (by simp)) hr
  exact pro.seq ((loop_rel hO hp hp' hq hc).seq restore)

end VG.Proof.Pbkdf2.Md.X86.Iterate

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (iterG iterW)

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) (hsat : ∃ s, (iterG hO.hH.SH sc).pre s) :
    Verified X86.target H.iterate (iterG hO.hH.SH sc) := by
  refine ⟨fun s hs => correct hO (pre_of hO.hH hs hO.sizes hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (ct hO (pre_of hO.hH h₁ hO.sizes hfit) (pre_of hO.hH h₂ hO.sizes hfit) ⟨h1, h2⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `iterate` reads and writes, of those `iterW` gives it. -/
def narrowRd (S D : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 2 * S⟩, ⟨(arg s 1).setWidth 64, D⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (D sc : Nat) (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, D⟩, ⟨(arg s 4).setWidth 64, 8 * sc⟩]

/-- `iterate` is verified against `iterW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) (hsat : ∃ s, (iterW hO.hH.SH sc).pre s) :
    Verified X86.target H.iterate (iterW hO.hH.SH sc) := by
  have pre : ∀ s, (iterW hO.hH.SH sc).pre s → (iterG hO.hH.SH sc).pre
      (s.withRegions (narrowRd hO.hH.SH.stateBytes hO.hH.SH.digestBytes s) (narrowWr hO.hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
    simp only [iterG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  refine Verified.narrowTo (verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd hO.hH.SH.stateBytes hO.hH.SH.digestBytes) (narrowWr hO.hH.SH.digestBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Md.X86.Iterate

end

end

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `finalize`, constant time

As for HMAC's `init` (`HmacInitCT.lean`): the pieces between the calls are
checked by the taint analysis, the prologue and the arguments of the first
call, which read the arguments on the stack, with them public (`argTaint`);
the call of the streaming `finalize` is related by `fin_rel`, that of the
compression function by `cmp_rel`. Then `finalize` is verified against the
contract with the arguments read only (`finG`), and with them writable
(`finW`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (HashOK finG finW argTaint ArgsOut agree_argTaint rel_agree rel_wp stk fin_rel
  FinArgs fin5)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (Pre KR E inn outer op scr tO pre_of pro_ok fin1Args_ok finCall_ok
  stk_eq)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 6)) (.block H.st.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6))
    (.block ([] ++ Impl.Pbkdf2.Stream.X86.Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.st.buf)) hc).isSome = true
  mid : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi, .esi]) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi]) (.block H.finOut) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 6, arg s₀ i = arg s₀' i

variable {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H.st) sc s₀) (hp' : Pre (H := H.st) sc s₀') (hq : PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre (H := H.st) sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 6 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 6⟩ : Region) = ⟨(E t).setWidth 64, 4 + 24⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_i h.a_i
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_p h.a_p
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_s h.a_s

include hq in
theorem kr_agree {s s' : State} (h : KR (H := H.st) sc s₀ s) (h' : KR (H := H.st) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .ebx, .edi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, scr, scr, hq.args 5 (by decide)]
  · rw [h.ebx, h'.ebx, inn, inn, hq.args 0 (by decide)]
  · rw [h.edi, h'.edi, op, op, hq.args 4 (by decide)]

theorem sub_regs {l l' : List Reg} (h : ∀ r ∈ l, r ∈ l') {s s' : State} (hs : ∀ r ∈ l', s.gpr r = s'.gpr r) :
    ∀ r ∈ l, s.gpr r = s'.gpr r := fun r hr => hs r (h r hr)

include hO hc hp hp' hq

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have hH := hO.hH
  have e5 : scr s₀' = scr s₀ := (hq.args 5 (by decide)).symm
  have e0 : inn s₀' = inn s₀ := (hq.args 0 (by decide)).symm
  have eT : tO (H := H.st) s₀' = tO (H := H.st) s₀ := by rw [tO, tO, e5]
  have e2 : arg s₀' 2 = arg s₀ 2 := (hq.args 2 (by decide)).symm
  have e3 : arg s₀' 3 = arg s₀ 3 := (hq.args 3 (by decide)).symm
  -- The prologue.
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.st.finPrologue)
      fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [] (4 + 4 * 6)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact WP.mono (pro_ok hp) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ e => by subst e; exact WP.mono (pro_ok hp') fun _ h => ⟨h.1, h.2.1⟩)
  -- The call of the streaming `finalize`.
  have a1 : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀'))
      (.block ([] ++ Impl.Pbkdf2.Stream.X86.Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.st.buf))
      fun s s' => (KR (H := H.st) sc s₀ s ∧
          FinArgs hH s .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧
          FinArgs hH s' .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6)) (fun s s' ⟨k, _⟩ ⟨k', _⟩ =>
        agree_argTaint (sub_regs (by decide) (kr_agree hq k k')) (by rw [k.esp, k'.esp, E, E, hq.esp])
          (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.fin1
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp k) fun _ ⟨k₁, a, s₁, _⟩ => ⟨k₁, a, s₁.trans si⟩)
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp' k) fun _ ⟨k₁, a, s₁, _⟩ =>
        ⟨k₁, by rw [← e0, ← eT, ← e5, ← e2, ← e3]; exact a, s₁.trans si⟩)
  have c1 : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧
        FinArgs hH s .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧
          FinArgs hH s' .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s'.gpr .esi = outer s₀'))
      (.frame (.push (fin5 .ebx)) (.call H.st.finN H.st.finC) (.pop .eax (fin5 .ebx).length))
      fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_wp (fin_rel hH (sp := E s₀) fun s s' ⟨⟨k, a, _⟩, ⟨k', a', _⟩⟩ =>
        ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp k a fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp' k (by rw [e0, eT, e5]; exact a)
        fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
  -- The outer block.
  have mid : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀')) (.block H.finMid)
      fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .eax = inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi, .esi]) (fun s s' ⟨k, si⟩ ⟨k', si'⟩ => agree_regs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · rw [si, si', outer, outer, hq.args 1 (by decide)]) hc.mid
      (fun _ ⟨k, si⟩ => WP.mono (mid_ok hO hp k si) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ ⟨k, si⟩ => WP.mono (mid_ok hO hp' k si) fun _ h => ⟨h.1, h.2.1⟩)
  -- The compression.
  have hB : 0 < H.B := by have := hO.sizes.B4; omega_using [this]
  have cm : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .eax = inn s₀' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => KR (H := H.st) sc s₀ s ∧ KR (H := H.st) sc s₀' s' :=
    rel_wp (cmp_rel hO.comp hB (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
        ⟨cmpArgs hO.sizes hp k a, by have := cmpArgs hO.sizes hp' k' a'; rwa [e0, e5] at this, k.esp,
          by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a⟩ => cmpF_ok hO hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a⟩ => cmpF_ok hO hp' k a fun _ k' _ _ => k')
  -- The MAC, and the end.
  obtain ⟨_, ho⟩ := hc.out
  have out : RelCT isa (fun s s' => KR (H := H.st) sc s₀ s ∧ KR (H := H.st) sc s₀' s') (.block H.finOut)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.esp, .ebp, .ebx, .edi]) (fun _ _ h => agree_regs (kr_agree hq h.1 h.2)) ho
  exact pro.seq ((a1.seq c1).seq (mid.seq (cm.seq out)))

end VG.Proof.Pbkdf2.Md.X86.HmacFin

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (finG finW)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (pre_of)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.st.F ≤ 8 * sc) (hsat : ∃ s, (finG hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacFin (finG hO.hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hO (pre_of hO.hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (ct hO hc (pre_of hO.hH sc h₁ hfit) (pre_of hO.hH sc h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `finalize` reads and writes, of those `finW` gives it. -/
def narrowRd (S : Nat) (s : State) : List Region := [⟨(arg s 1).setWidth 64, S⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (S D sc : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, D⟩, ⟨(arg s 5).setWidth 64, 8 * sc⟩]

/-- `finalize` is verified against `finW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.st.F ≤ 8 * sc) (hsat : ∃ s, (finW hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacFin (finW hO.hH.SH sc) := by
  have pre : ∀ s, (finW hO.hH.SH sc).pre s → (finG hO.hH.SH sc).pre
      (s.withRegions (narrowRd hO.hH.SH.stateBytes s)
        (narrowWr hO.hH.SH.stateBytes hO.hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23⟩ := h
    simp only [finG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23⟩
  refine Verified.narrowTo (verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd hO.hH.SH.stateBytes) (narrowWr hO.hH.SH.stateBytes hO.hH.SH.digestBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Md.X86.HmacFin
