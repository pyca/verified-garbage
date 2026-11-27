module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Hmac.Generic.Common

/-! ### `Pbkdf2.Md.X86.HmacFinCT`, which the modules that import this one used -/

section

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

end

end

/-! ### `Pbkdf2.Md.X86.HmacInit`, which only this module used -/

section

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `init`, correct

HMAC's `init` (`Impl/Pbkdf2/Md/X86.lean`): the prologue (`pro_ok`), the
streaming `init` of both states (`callInit_ok`), `ipad` in every byte of the
inner state's buffer (`fill_ok`) and the key XORed into its start
(`key_ok`), the outer buffer from the inner one, word by word
(`opadW_ok`), and one compression of each buffer into its state's hash
value (`cmpI_ok`, `cmpO_ok`): each state then represents its block
(`Md.repr_block`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_test
  wp_movzx8 wp_store8 ofNat_beq_zero ofNat_pred ofNat_succ addr_add_ofNat)
open VG.Proof.Pbkdf2.Stream.X86 (ea_at wp_xori count_loop)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep extractLsb'_read)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)

/-! ## Words of a constant, and words XORed with a constant -/

/-- `n` words of `ecx` stored at `[y + o]`, `[y + o + 4]`, … -/
theorem fillW_ok {dst : Reg} {y : BitVec 32} {o : Nat} {b : Byte} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ecx = b ++ b ++ b ++ b →
    s.gpr dst = y → y.toNat + o + 4 * n ≤ 2 ^ 32 → (∀ k < n, InRegions s.wr (addr y (o + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o) (List.replicate (4 * n) b) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store (at_ dst (o + 4 * k)) .ecx) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hc hy fy hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hc hy (by omega_arith) (fun j hj => hout j (by omega_arith)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_store (a := addr y (o + 4 * n)) (by rw [ea_at, g₁, hy]) (by rw [wr₁]; exact hout n (Nat.lt_succ_self _))
      fun s₂ u₂ => ?_
    refine k s₂ (by rw [u₂.gpr, g₁]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) ?_
    rw [u₂.mem, m₁, g₁, hc, addr_word fy (by omega_arith : n < n + 1), MdKeys.writeW_rep,
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate]) (by simp; omega_arith), List.replicate_append_replicate,
      show 4 * n + 4 = 4 * (n + 1) by omega_arith]

/-- The outer state's buffer, from the inner one's: `n` words of
`[ebx + N + 4 k]`, XORed with `0x6a` in every byte, into `[esi + N + 4 k]`. -/
theorem opadW_ok (H : Hash) {x y : BitVec 32} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebx = x → s.gpr .esi = y →
    x.toNat + H.N + 4 * n ≤ 2 ^ 32 → y.toNat + H.N + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (H.N + 4 * k)) 4) →
    Region.Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ ⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega_arith) (by omega_arith) (fun j hj => hin j (by omega_arith)) (fun j hj => hout j (by omega_arith))
      ((hsep.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (H.N + 4 * n)) (by rw [ea_at, g₁ _ (by decide), hx])
      (by rw [rd₁, wr₁]; exact hin n (Nat.lt_succ_self _)) fun s₂ u₂ => wp_xori fun s₃ u₃ => ?_
    refine wp_store (a := addr y (H.N + 4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (Nat.lt_succ_self _)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    obtain hl : ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ (0x6a : Byte))).length =
        4 * n := by simp [bytesAt_length]
    obtain f₁ : Frame [⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
    obtain dX : ∀ r ∈ [(⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ : Region)],
        Region.Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n), 4⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
    rw [u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, addr_word fx (by omega_arith : n < n + 1),
      addr_word fy (by omega_arith : n < n + 1),
      f₁.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) dX (by decide), MdKeys.c6a, MdKeys.writeW_xorRep, m₁,
      Memory.writeBytes_append' _ _ _ (by rw [hl]) (by simp [bytesAt_length]; omega_arith), ← List.map_append,
      ← bytesAt_add, show 4 * n + 4 = 4 * (n + 1) by omega_arith]

/-! ## The key loop -/

/-- After `j` bytes of the key loop, from `s`: the key at `K`, its `kl`
bytes, XORed with `ipad`, written at `P`. -/
structure KeyInv (s : State) (kp p : BitVec 32) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r
  edi : t.gpr .edi = kp + BitVec.ofNat 32 j
  edx : t.gpr .edx = p + BitVec.ofNat 32 j
  ecx : t.gpr .ecx = BitVec.ofNat 32 (kl - j)
  mem : t.mem = writeBytes s.mem (p.setWidth 64) ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad))

theorem key_step {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨p.setWidth 64, kl⟩) {j : Nat} (hj : j < kl) {t : State}
    (h : KeyInv s kp p kl j t) :
    WP isa (.block [.movzx8 .eax (at_ .edi 0), .alu .xor .eax (.imm 0x36), .store8 (at_ .edx 0) .al,
      .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun t' => KeyInv s kp p kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  obtain hl : ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad)).length = j := by
    simp [bytesAt_length]
  obtain hbyte : t.mem (kp.setWidth 64 + BitVec.ofNat 64 j) = s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    refine (writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨kp.setWidth 64, kl⟩) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact hsep.sub_right (Region.sub_prefix (by omega_arith))) (by show kl ≤ 2 ^ 64; omega_arith) hj
  refine wp_movzx8 (a := kp.setWidth 64 + BitVec.ofNat 64 j)
    (by rw [ea_at, h.edi, addr_add_ofNat (by omega_using [hj, hkp]), Nat.add_zero]) (by rw [h.rd, h.wr]; exact hin j hj)
    fun t₁ u₁ => wp_xori fun t₂ u₂ => ?_
  refine wp_store8 (a := p.setWidth 64 + BitVec.ofNat 64 j)
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.edx, addr_add_ofNat (by omega_using [hj, hp]), Nat.add_zero])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout j hj) fun t₃ u₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_subi fun t₆ u₆ z₆ => WP.block_nil ?_
  obtain ecx₅ : t₅.gpr .ecx = BitVec.ofNat 32 (kl - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.ecx]
  obtain v : (t₂.gpr Reg8.al.reg).setWidth 8 = s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad := by
    show (t₂.gpr .eax).setWidth 8 = _
    rw [u₂.gpr, u₁.gpr, MdKeys.xor_byte, hbyte]; rfl
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [u₆.other r h2, u₅.other r h3, u₄.other r h4, u₃.gpr, u₂.other r h1, u₁.other r h1, h.other r h1 h2 h3 h4],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edi, ofNat_succ, BitVec.add_assoc],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx, ofNat_succ, BitVec.add_assoc],
    by rw [u₆.gpr, ecx₅, ofNat_pred (by omega_using [hj]), show kl - j - 1 = kl - (j + 1) by omega_arith], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem, h.mem]
    obtain e := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem (p.setWidth 64)
      ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad))
      (s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad) (by rw [hl]; omega_using [hj, hkp])
    rw [hl] at e
    rw [e, VG.Proof.Hmac.Generic.Common.bytesAt_snoc', List.map_append, List.map_singleton]
  · rw [z₆, ecx₅, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- The key loop, skipped for an empty key: from the flags of `kl = 0`. -/
theorem key_ok {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨p.setWidth 64, kl⟩)
    (h0 : KeyInv s kp p kl 0 s) (hz : s.zf = some (decide (kl = 0))) :
    WP isa (.ite .e (.block []) Hash.keyLoop) s (KeyInv s kp p kl kl) := by
  refine WP.ite (decide (kl = 0)) (by show eval .e s = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, hz])
    (fun e => WP.block_nil ?_) fun e => ?_
  · have : kl = 0 := by simpa using e
    subst this; exact h0
  · exact count_loop (by simp at e; omega_arith) _ (fun j hj t h => key_step hkp hp hkl hin hout hsep hj h) h0

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK initG SavedRegs saveR savedRegs save_ok restore_ok callee_saved ea_at stk
  After stk_args stk_ret arg_keep arg_contains arg_sub argAddr_eq init_frame setWidth_add toNat_add_ofNat)
open VG.Proof.Hmac.Generic.Common (off_disj off_disj0 covers_one InRegions.right' bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_add wp_addi wp_test sub_offset ofNat_beq_zero)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev out : BitVec 32 := arg s₀ 1
abbrev kp : BitVec 32 := arg s₀ 2
abbrev kl : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev inR : Region := ⟨(inn s₀).setWidth 64, H.N + H.B⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, H.N + H.B⟩
abbrev keyR : Region := ⟨(kp s₀).setWidth 64, kl s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨(scr s₀).setWidth 64, H.so⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_o : (retR s₀).Disjoint (outR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.st.buf ≤ 8 * sc

theorem pre_of (hO : MdOk H) {s₀ : State} (h : (initG hO.hH.SH sc).pre s₀) (hfit : H.st.buf ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩ := h
  obtain hS : hO.hH.SH.stateBytes = H.N + H.B := hO.hH.hS.trans hO.sizes.S
  have hB := hO.hH.hB
  obtain e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h23]; rfl
  simp only [hS, hB, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, hfit⟩

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ 8 * H.st.W + 16 ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ H.N % 4 = 0 ∧ H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 ∧
    (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (kp s₀).toNat + kl s₀ ≤ 2 ^ 32 ∧ kl s₀ ≤ H.B := by
  have := hz.B4
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N.1, hz.N.2.1, hz.N.2.2, this.1, this.2.1, this.2.2, hp.ni, hp.no,
    hp.nk, hp.kl_le⟩

theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  have := bounds hz hp; exact sub_offset (by omega_arith) (by omega_arith)

theorem cmp_sub : Region.Sub (cmpR (H := H) s₀) (scR sc s₀) := by
  have := bounds hz hp; exact Region.sub_prefix (by omega_arith)

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR (H := H) s₀) := by
  have := bounds hz hp
  exact Offset.disjoint_base _ (hz.so) (hz.buf_le64)

omit hz hp in
/-- A part of a state at `p`. -/
theorem st_sub (p : BitVec 32) {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨p.setWidth 64 + BitVec.ofNat 64 a, n⟩ ⟨p.setWidth 64, H.N + H.B⟩ := Offset.sub_base _ h

/-- The states, `scratch` and the stack below `esp`, as the code sees them. -/
theorem st_facts {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p.setWidth 64, H.N + H.B⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p.setWidth 64, H.N + H.B⟩ ∧
      (saveR H.st (scr s₀)).Disjoint ⟨p.setWidth 64, H.N + H.B⟩ ∧ p.toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
      ⟨p.setWidth 64, H.N + H.B⟩ ∈ s₀.wr := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (save_sub hz hp), hp.ni, by rw [hp.wr]; simp⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (save_sub hz hp), hp.no, by rw [hp.wr]; simp⟩

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  esi : s.gpr .esi = out s₀
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .esi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {sc : Nat}

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') : KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.esi, h.saved.frame H.st hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem stk_eq {s₀ s : State} (hk : KR (H := H) sc s₀ s) : stk s = stkR s₀ := by rw [stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have hp_spf := hp.spf; omega_arith)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have hp_spf := hp.spf; omega_arith)

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, by rw [hp.rd]; simp, arg_contains rfl (by omega_arith) (by have hp_spf := hp.spf; omega_arith)⟩

theorem KR.argEq {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) : arg s i = arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have hp_spf := hp.spf; omega_arith) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega_arith)

theorem KR.readArg {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := hk.argEq hp hi
  simp only [arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {s : State} (hk : KR (H := H) sc s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_o
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

/-- The key, while `KR` holds. -/
theorem KR.key {s : State} (hk : KR (H := H) sc s₀ s) :
    bytesAt s.mem ((kp s₀).setWidth 64) (kl s₀) = bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀) :=
  Memory.frame_bytesAt hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (arg s₀ 3).isLt (by decide)))

end

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hz : Sizes H) (hp : Pre (H := H) sc s₀)
include hz hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ fun s => KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀ := by
  obtain ⟨hb, hf, nw, -, hW, -⟩ := bounds hz hp
  obtain sR : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  obtain dA : ∀ r ∈ [saveR H.st (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hz hp)
  simp only [Hash.initPrologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at]; rfl) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega_arith) (by omega_arith)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  obtain e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  obtain rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega_arith) (by have hp_spf := hp.spf; omega_arith))) (by decide)
  obtain i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 0) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)],
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hz hp⟩⟩,
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 0 (by decide)]⟩

end

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hz : Sizes H) (hp : Pre (H := H) sc s₀)
include hz hp

/-- `KR` after a call that writes `rs`, parts of our buffers. -/
theorem KR.call {s s' : State} (hk : KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [stk_eq hk] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (save_sub hz hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hsub r hr
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call of the streaming `init` on the state at `p`, in `st`, needs. -/
theorem initArgs {s : State} (hk : KR (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) (hsr : s.gpr st = p) :
    VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H.st) s st p := by
  obtain hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, dK, _, np, hin⟩ := st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  exact
    { hst := hsr
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      sp48 := by rw [hk.esp]; exact hp.sp48
      cw := by rw [hk.wr, hS]; exact covers_one hin
      b_st := by rw [stk_eq hk, hS]; exact dK
      nst := by rw [hS]; exact np }

/-- A call of the streaming `init` on the state at `p`, in `st`. -/
theorem callInit_ok (hO : MdOk H) {s : State} (hk : KR (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) (hsr : s.gpr st = p) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ s' → s'.gpr .ebx = s.gpr .ebx →
      Frame [⟨p.setWidth 64, H.N + H.B⟩, stkR s₀] s.mem s'.mem → hO.hH.SH.Repr s'.mem (p.setWidth 64) [] → Q s') :
    WP isa (H.st.callInit st) s Q := by
  obtain hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, _, dV, _, _⟩ := st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  refine init_frame hO.hH (initArgs hz hp hk hst hsr) fun s' ha hr => ?_
  rw [hS] at ha
  have f := ha.frame
  rw [stk_eq hk] at f
  exact hQ s' (KR.call hz hp hk ha (by simp only [List.mem_singleton]; rintro r rfl; exact dV)
    (by
      simp only [List.mem_singleton]; rintro r rfl
      rcases hpR with rfl | rfl
      · exact ⟨inR (H := H) s₀, by simp, fun _ h => h⟩
      · exact ⟨outR (H := H) s₀, by simp, fun _ h => h⟩)) (ha.cs .ebx (by decide)) f hr

/-- What the compression of the buffer of the state at `p`, in `ebx`, with
`eax` at the buffer, needs. -/
theorem cmpArgs {s : State} (hk : KR (H := H) sc s₀ s) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (hbx : s.gpr .ebx = p) (hax : s.gpr .eax = p + BitVec.ofNat 32 H.N) :
    CmpArgs H.N H.B H.so s p (scr s₀) := by
  obtain ⟨hb, hf, nw, hso, hW, -⟩ := bounds hz hp
  obtain ⟨dS, dK, dV, np, hin⟩ := st_facts hz hp hpR
  exact
    { ebx := hbx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := by rw [hk.wr]; exact covers_one hin
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scR sc s₀, by rw [hp.wr]; simp, 0, by simp, by simp only; omega_arith⟩
      st_sc := dS.sub_right (cmp_sub hz hp)
      b_st := by rw [stk_eq hk]; exact dK
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cmp_sub hz hp)
      nst := np
      nsc := by omega_arith }

/-- The compression of the buffer of the state at `p`, in `ebx`, with `eax`
at the buffer. -/
theorem cmpS_ok (hO : MdOk H) {s : State} (hk : KR (H := H) sc s₀ s) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (hbx : s.gpr .ebx = p) (hax : s.gpr .eax = p + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ s' → s'.gpr .ebx = p →
      Frame [⟨p.setWidth 64, H.N⟩, cmpR (H := H) s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem (p.setWidth 64) = hO.md.compress (hO.md.stateAt s.mem (p.setWidth 64))
        (hO.md.blockAt s.mem (p.setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  obtain ⟨hb, hf, nw, hso, hW, hN0, hN, -, -, hB64, -⟩ := bounds hz hp
  obtain ⟨dS, dK, dV, np, hin⟩ := st_facts hz hp hpR
  refine cmp_ok hO.comp (hz.B_pos) (cmpArgs hz hp hk hpR hbx hax) fun s' ha e => ?_
  have f := ha.frame
  rw [stk_eq hk] at f
  obtain sN : Region.Sub ⟨p.setWidth 64, H.N⟩ ⟨p.setWidth 64, H.N + H.B⟩ := Region.sub_prefix (Nat.le_add_right _ _)
  refine hQ s' (KR.call hz hp hk ha ?_ ?_) (ha.cs .ebx (by decide) |>.trans hbx) (f.mono (by simp)) e
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV.sub_right sN
    · exact save_cmp hz hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨inR (H := H) s₀, by simp, sN⟩
      · exact ⟨outR (H := H) s₀, by simp, sN⟩
    · exact ⟨scR sc s₀, by simp, cmp_sub hz hp⟩

end

/-! ## The blocks -/

section
variable {sc : Nat} {s₀ : State} (hz : Sizes H) (hp : Pre (H := H) sc s₀)
include hz hp

/-- A word of the buffer of the state at `p`. -/
theorem buf_word {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) {k : Nat} (hk : k < H.B / 4) :
    InRegions s₀.wr (addr p (H.N + 4 * k)) 4 := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, -⟩ := bounds hz hp
  obtain ⟨-, -, -, np, hin⟩ := st_facts hz hp hpR
  rw [addr_eq (by omega_arith)]
  exact ⟨_, hin, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- `ipad` in every byte of the inner buffer, then the key's arguments. -/
theorem fill_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) :
    WP isa (.block H.fillIpad) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧ t.gpr .edi = kp s₀ ∧
      t.gpr .edx = inn s₀ + BitVec.ofNat 32 H.N ∧ t.gpr .ecx = BitVec.ofNat 32 (kl s₀) ∧
      t.zf = some (decide (kl s₀ = 0)) ∧
      t.mem = writeBytes s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) (List.replicate H.B 0x36) := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, hB64, hB, ni, -⟩ := bounds hz hp
  obtain h4 : 4 * (H.B / 4) = H.B := by omega_arith
  simp only [Hash.fillIpad, List.cons_append]
  refine wp_movi fun s₁ u₁ => ?_
  refine fillW_ok (H.B / 4) _ s₁ _ (b := 0x36) (u₁.gpr.trans (by decide)) (by rw [u₁.other _ (by decide), hbx])
    (by omega_arith) (fun j hj => by rw [u₁.wr, hk.wr]; exact buf_word hz hp (.inl rfl) hj) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  rw [h4] at m₂
  obtain f₂ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₂.mem := by
    rw [m₂, u₁.mem]; exact writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact Region.contains_self _ _)
  obtain sB : Region.Sub ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (inR (H := H) s₀) := st_sub _ (Nat.le_refl _)
  obtain k₂ : KR (H := H) sc s₀ s₂ := hk.keep (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])
    (fun r hr => by rw [g₂, u₁.other r (by revert hr; decide +revert)]) f₂
    (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
    (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩)
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, k₂.esp]; rfl) (argIn hp k₂.rd k₂.wr (by decide))
    fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, u₃.other _ (by decide), k₂.esp]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact argIn hp k₂.rd k₂.wr (by decide)) fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_test fun s₇ f₇ z₇ => WP.block_nil ?_
  obtain hcx : s₇.gpr .ecx = arg s₀ 3 := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, k₂.readArg hp (by decide)]
  obtain bx₂ : s₂.gpr .ebx = inn s₀ := by rw [g₂, u₁.other _ (by decide), hbx]
  obtain bx : s₇.gpr .ebx = inn s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), bx₂]
  obtain k₇ : KR (H := H) sc s₀ s₇ :=
    ((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).keep f₇.rd f₇.wr
      (fun r _ => by rw [f₇.gpr]) (rs := []) (by rw [f₇.mem]; exact Frame.refl _ _) (by simp) (by simp)
  refine ⟨k₇, bx, ?_, ?_, ?_, ?_, by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]⟩
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      k₂.readArg hp (by decide)]
  · rw [f₇.gpr, u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), bx₂]
  · rw [hcx, kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [z₇, ← f₇.gpr, hcx, VG.Proof.Pbkdf2.Stream.X86.test_z]


/-- The key loop: the key XORed with `ipad` over the start of the inner buffer. -/
theorem keys_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) (hdi : s.gpr .edi = kp s₀)
    (hdx : s.gpr .edx = inn s₀ + BitVec.ofNat 32 H.N) (hcx : s.gpr .ecx = BitVec.ofNat 32 (kl s₀))
    (hzf : s.zf = some (decide (kl s₀ = 0)))
    (hm : bytesAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36) :
    WP isa (.ite .e (.block []) Hash.keyLoop) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧
      Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem ∧
      bytesAt t.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
        (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀)).map (· ^^^ ipad) ++ List.replicate (H.B - kl s₀) ipad := by
  obtain ⟨-, -, -, -, -, -, hN, -, -, hB64, hB, ni, -, nk, hkl⟩ := bounds hz hp
  obtain kl32 : kl s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  obtain ap : (inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 = (inn s₀).setWidth 64 + BitVec.ofNat 64 H.N :=
    setWidth_add (by omega_arith)
  obtain tp : (inn s₀ + BitVec.ofNat 32 H.N).toNat = (inn s₀).toNat + H.N := toNat_add_ofNat (by omega_arith)
  obtain hin : ∀ j < kl s₀, InRegions (s.rd ++ s.wr) ((kp s₀).setWidth 64 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hk.rd, hp.rd]; exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_using [hj, nk])⟩
  obtain hout : ∀ j < kl s₀, InRegions s.wr ((inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hk.wr, hp.wr, ap, Memory.add_ofNat]
      exact ⟨inR (H := H) s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_using [hj, nk, hN])⟩
  obtain hsep : Region.Disjoint ⟨(kp s₀).setWidth 64, kl s₀⟩ ⟨(inn s₀ + BitVec.ofNat 32 H.N).setWidth 64, kl s₀⟩ := by
    rw [ap]; exact hp.k_i.sub_right (st_sub _ (by omega_arith))
  obtain h0 : KeyInv s (kp s₀) (inn s₀ + BitVec.ofNat 32 H.N) (kl s₀) 0 s :=
    ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [hdi]; exact (BitVec.add_zero _).symm,
      by rw [hdx]; exact (BitVec.add_zero _).symm, by rw [hcx, Nat.sub_zero],
      by rw [show bytesAt s.mem ((kp s₀).setWidth 64) 0 = [] from rfl, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (key_ok (by omega_arith) (by rw [tp]; omega_using [hkl, ni]) kl32 hin hout hsep h0 hzf) fun t ht => ?_
  obtain hl : ((bytesAt s.mem ((kp s₀).setWidth 64) (kl s₀)).map (· ^^^ ipad)).length = kl s₀ := by
    simp [bytesAt_length]
  obtain sB := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain ft : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem := by
    rw [ht.mem, ap]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Memory.contains_base hkl)
  refine ⟨hk.keep ht.rd ht.wr (fun r hr => ht.other r (by revert hr; decide +revert) (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert)) ft
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩),
    by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), hbx], ft, ?_⟩
  rw [ht.mem, ap, MdKeys.bytes_over (by rw [hl]; omega_arith) (hz.B_lt64) hm, hl, hk.key hp]
  rfl


/-- The outer buffer from the inner one, and `eax` at the inner one. -/
theorem opad_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) :
    WP isa (.block H.fillOpad) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧
      t.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N ∧
      t.mem = writeBytes s.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a)) := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, hB64, hB, ni, no, -⟩ := bounds hz hp
  obtain h4 : 4 * (H.B / 4) = H.B := by omega_arith
  obtain sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  unfold Hash.fillOpad
  refine opadW_ok H (H.B / 4) _ s _ hbx hk.esi (by omega_arith) (by omega_arith)
    (fun j hj => by rw [hk.wr, hk.rd]; exact InRegions.right' (buf_word hz hp (.inl rfl) hj))
    (fun j hj => by rw [hk.wr]; exact buf_word hz hp (.inr rfl) hj)
    (by rw [h4]; exact (hp.i_o.sub_left sBI).sub_right sBO) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [h4] at m₁
  rw [← List.append_nil H.atBlk]
  refine atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  obtain hl : ((bytesAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  obtain f : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₂.mem := by
    rw [m₂, m₁]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
      (fun r hr => by rw [g₂ r (by revert hr; decide +revert), g₁ r (by revert hr; decide +revert)]) f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.o_s.symm.sub_left (save_sub hz hp)).sub_right sBO)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sBO⟩),
    by rw [g₂ _ (by decide), g₁ _ (by decide), hbx], by rw [e₂, g₁ _ (by decide), hbx], by rw [m₂, m₁]⟩


/-- The two blocks, as the constant-time proof needs them. -/
theorem blocks_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) :
    WP isa H.blocks s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧
      t.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N := by
  have := (bounds hz hp).2.2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (fill_ok hz hp hk hbx) fun s₄ ⟨k₄, b₄, d₄, x₄, c₄, z₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ b₄ d₄ x₄ c₄ z₄ (by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (hz.B_lt64)])) fun s₅ ⟨k₅, b₅, _⟩ => ?_)
  exact WP.mono (opad_ok hz hp k₅ b₅) fun _ ⟨k₆, b₆, a₆, _⟩ => ⟨k₆, b₆, a₆⟩

omit hz hp in
/-- `ebx` at the outer state, and `eax` at its buffer. -/
theorem toOuter_ok {s : State} (hk : KR (H := H) sc s₀ s) :
    WP isa (.block H.toOuter) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = out s₀ ∧
      t.gpr .eax = out s₀ + BitVec.ofNat 32 H.N ∧ t.mem = s.mem := by
  unfold Hash.toOuter
  refine wp_mov fun s₁ u₁ => ?_
  rw [← List.append_nil H.atBlk]
  refine atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  obtain k₁ := hk.upd (by decide) u₁
  exact ⟨k₁.keep rd₂ wr₂ (fun r hr => g₂ r (by revert hr; decide +revert)) (rs := [])
      (by rw [m₂]; exact Frame.refl _ _) (by simp) (by simp),
    by rw [g₂ _ (by decide), u₁.gpr, hk.esi], by rw [e₂, u₁.gpr, hk.esi], by rw [m₂, u₁.mem]⟩

end


/-! ## Correctness -/

section
variable {sc : Nat} {s₀ : State} (hO : MdOk H) (hp : Pre (H := H) sc s₀)
include hO hp

omit hp in
theorem keep_st {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) : hO.md.stateAt m' p = hO.md.stateAt m p :=
  hO.md.stateAt_congr fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have := hO.sizes.N; show H.N ≤ 2 ^ 64; omega_arith) hi

omit hp in
theorem keep_repr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N + H.B⟩ r) {x : List Byte} (hr : hO.md.Repr hO.iv m p x) :
    hO.md.Repr hO.iv m' p x :=
  hO.md.repr_congr (by have := hO.sizes.B4; omega_arith) (fun i hi => hf.bytes (R := ⟨p, H.N + H.B⟩) hd
    (by have := hO.sizes.B4; have := hO.sizes.N; show H.N + H.B ≤ 2 ^ 64; omega_arith) hi) hr

theorem correct :
    WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hO.hH.SH sc).post s₀ s' := by
  have hz := hO.sizes
  obtain ⟨hb, hf, nw, hso, hW, hN0, hN, hN4, hB4, hB64, hB, ni, no, nk, hkl⟩ := bounds hz hp
  have hl := hO.link
  -- Where things are.
  obtain sNI := st_sub (H := H) (inn s₀) (a := 0) (n := H.N) (by omega_using [])
  obtain sNO := st_sub (H := H) (out s₀) (a := 0) (n := H.N) (by omega_arith)
  rw [BitVec.add_zero] at sNI sNO
  obtain sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain nb : ∀ (x : BitVec 32), Region.Disjoint ⟨x.setWidth 64, H.N⟩ ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun _ => Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hN])
  obtain iv0 : ∀ {m : Mem} {p : Addr}, hO.hH.SH.Repr m p [] → hO.md.stateAt m p = hO.iv := fun h => by
    have := (hl.repr _ _ _ h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  refine WP.seq (WP.mono (pro_ok hz hp) fun s₁ ⟨k₁, b₁⟩ => ?_)
  refine WP.seq (callInit_ok hz hp hO k₁ (.inl ⟨rfl, rfl⟩) b₁ fun s₂ k₂ b₂ _ r₂ => ?_)
  refine WP.seq (callInit_ok hz hp hO k₂ (.inr ⟨rfl, rfl⟩) k₂.esi fun s₃ k₃ b₃ f₃ r₃ => ?_)
  obtain vI₃ : hO.md.stateAt s₃.mem ((inn s₀).setWidth 64) = hO.iv := by
    rw [keep_st hO f₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left sNI
      · exact hp.b_i.symm.sub_left sNI), iv0 r₂]
  obtain vO₃ := iv0 r₃
  refine WP.seq (WP.seq (WP.mono (fill_ok hz hp k₃ (b₃.trans (b₂.trans b₁)))
    fun s₄ ⟨k₄, b₄, d₄, x₄, c₄, z₄, m₄⟩ => ?_))
  obtain rep₄ : bytesAt s₄.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36 := by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (hz.B_lt64)]
  obtain f₄ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ b₄ d₄ x₄ c₄ z₄ rep₄) fun s₅ ⟨k₅, b₅, f₅, bI₅⟩ => ?_)
  refine WP.mono (opad_ok hz hp k₅ b₅) fun s₆ ⟨k₆, b₆, a₆, m₆⟩ => ?_
  obtain hl6 : ((bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  obtain f₆ : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [hl6]; exact Region.contains_self _ _)
  obtain bO₆ : bytesAt s₆.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      (bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a) := by
    rw [m₆, bytesAt_writeBytes_self' hl6 (hz.B_lt64)]
  obtain bI₆ : bytesAt s₆.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B :=
    Memory.frame_bytesAt f₆ (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sBI).sub_right sBO) (by omega_using [hB])
  -- The hash values are those `init` left.
  obtain vI₆ : hO.md.stateAt s₆.mem ((inn s₀).setWidth 64) = hO.iv := by
    rw [keep_st hO f₆ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sNI).sub_right sBO),
      keep_st hO f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hO f₄ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _), vI₃]
  obtain vO₆ : hO.md.stateAt s₆.mem ((out s₀).setWidth 64) = hO.iv := by
    rw [keep_st hO f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hO f₅ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI),
      keep_st hO f₄ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI), vO₃]
  refine WP.seq (cmpS_ok hz hp hO k₆ (.inl rfl) b₆ a₆ fun s₇ k₇ _ f₇ e₇ => ?_)
  refine WP.seq (WP.mono (toOuter_ok k₇) fun s₈ ⟨k₈, b₈, a₈, m₈⟩ => ?_)
  refine WP.seq (cmpS_ok hz hp hO k₈ (.inr rfl) b₈ a₈ fun s₉ k₉ _ f₉ e₉ => ?_)
  -- The key.
  obtain hK : xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) ipad =
      bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B := by
    rw [bI₅, MdKeys.blockKey_short _ (by rw [bytesAt_length, hO.hH.hB]; exact hkl), MdKeys.xorPad_short,
      bytesAt_length, hO.hH.hB]
  obtain hKl : (xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) ipad).length = H.B := by
    rw [hK, bytesAt_length]
  -- The inner state.
  obtain rI₇ := Md.repr_block (H := hO.md) (iv := hO.iv) (hz.B_pos) hKl (by rw [bI₆, hK]) (by rw [e₇, vI₆])
  obtain dI₉ : ∀ r ∈ [(⟨(out s₀).setWidth 64, H.N⟩ : Region), cmpR (H := H) s₀, stkR s₀],
      Region.Disjoint ⟨(inn s₀).setWidth 64, H.N + H.B⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.sub_right sNO
    · exact hp.i_s.sub_right (cmp_sub hz hp)
    · exact hp.b_i.symm
  obtain rI₉ := keep_repr hO f₉ dI₉ (m₈ ▸ rI₇)
  -- The outer state.
  obtain d₇ : ∀ {a n : Nat}, a + n ≤ H.N + H.B → ∀ r ∈ [(⟨(inn s₀).setWidth 64, H.N⟩ : Region), cmpR (H := H) s₀,
      stkR s₀], Region.Disjoint ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_o.symm.sub_left (st_sub _ h)).sub_right sNI
    · exact (hp.o_s.sub_left (st_sub _ h)).sub_right (cmp_sub hz hp)
    · exact hp.b_o.symm.sub_left (st_sub _ h)
  obtain vO₈ : hO.md.stateAt s₈.mem ((out s₀).setWidth 64) = hO.iv := by
    rw [m₈, keep_st hO f₇ (by have := d₇ (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this), vO₆]
  obtain bO₈ : bytesAt s₈.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) opad := by
    rw [m₈, Memory.frame_bytesAt f₇ (d₇ (Nat.le_refl _)) (by omega_using [hB]), bO₆, ← hK, MdKeys.xorOpad_ipad]
  obtain rO₉ := Md.repr_block (H := hO.md) (iv := hO.iv) (hz.B_pos) (by rw [xorPad_length, ← xorPad_length _ ipad, hKl])
    bO₈ (by rw [e₉, vO₈])
  -- The end.
  obtain hsc : ⟨(scr s₀).setWidth 64, 8 * sc⟩ ∈ s₉.wr := by rw [k₉.wr, hp.wr]; simp
  refine WP.mono (restore_ok H.st k₉.ebp k₉.saved hsc (by omega_arith) nw) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hm]; exact k₉.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₉.esp]
    · exact hg r (callee_saved r hr he)
  · show hO.hH.SH.Repr s'.mem ((inn s₀).setWidth 64) _ ∧ hO.hH.SH.Repr s'.mem ((out s₀).setWidth 64) _
    rw [hm]
    exact ⟨hO.back _ _ _ rI₉, hO.back _ _ _ rO₉⟩

end

end VG.Proof.Pbkdf2.Md.X86.HmacInit

end

end


/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `init`, constant time

As `finalize` (`HmacFinCT.lean`): the pieces between the calls are checked
by the taint analysis, the prologue and the blocks, which read the arguments
on the stack, with them public (`argTaint`); the calls of the streaming
`init` are related by `init_rel`, those of the compression function by
`cmp_rel`. Then `init` is verified against the contract with the arguments
read only (`initG`), and with them writable (`initW`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initG initW argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel)

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block H.initPrologue) hc).isSome = true
  blocks : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .esi] (4 + 4 * 5)) H.blocks hc).isSome = true
  toOuter : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .esi]) (.block H.toOuter) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.st.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, arg s₀ i = arg s₀' i

variable {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre (H := H) sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  obtain e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_i h.a_i
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_o h.a_o
  · exact Taint.frame_disjoint (by have := h.spf; omega_using [this]) h.r_s h.a_s

include hq in
theorem kr_agree {s s' : State} (h : KR (H := H) sc s₀ s) (h' : KR (H := H) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .esi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, scr, scr, hq.args 4 (by decide)]
  · rw [h.esi, h'.esi, out, out, hq.args 1 (by decide)]

include hO hp hp' hq

/-- A call of the streaming `init` on the state in `st` (`ebx` for `inner`,
`esi` for `outer`), with `ebx` at `inner`. -/
theorem callInit_rel {st : Reg} {p : BitVec 32} (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) :
    RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀'))
      (H.st.callInit st)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀') := by
  have hz := hO.sizes
  obtain hst' : st = .ebx ∧ p = inn s₀' ∨ st = .esi ∧ p = out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, inn, inn, hq.args 0 (by decide)]⟩
    · exact .inr ⟨h1, by rw [h2, out, out, hq.args 1 (by decide)]⟩
  obtain hsr : ∀ {t u : State}, KR (H := H) sc t u → u.gpr .ebx = inn t →
      (st = .ebx ∧ p = inn t ∨ st = .esi ∧ p = out t) → u.gpr st = p := fun k b h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact b
    · exact k.esi
  refine rel_wp (F := fun s => KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀)
    (F' := fun s => KR (H := H) sc s₀' s ∧ s.gpr .ebx = inn s₀')
    (init_rel hO.hH (sp := E s₀) (r := st) (st := p) fun s s' ⟨⟨k, b⟩, ⟨k', b'⟩⟩ =>
      ⟨initArgs hz hp k hst (hsr k b hst), initArgs hz hp' k' hst' (hsr k' b' hst'), k.esp,
        by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, b⟩ => callInit_ok hz hp hO k hst (hsr k b hst) fun _ k' b' _ _ => ⟨k', b'.trans b⟩)
    (fun _ ⟨k, b⟩ => callInit_ok hz hp' hO k hst' (hsr k b hst') fun _ k' b' _ _ => ⟨k', b'.trans b⟩)

/-- A compression of the buffer of the state at `p`, in `ebx`, with `eax`
at it. -/
theorem cmpS_rel {p p' : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) (hpR' : p' = inn s₀' ∨ p' = out s₀')
    (he : p' = p) :
    RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = p ∧ s.gpr .eax = p + BitVec.ofNat 32 H.N) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = p' ∧ s'.gpr .eax = p' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' := by
  have hz := hO.sizes
  obtain hB : 0 < H.B := by have := hz.B4; omega_using [this]
  obtain e4 : scr s₀' = scr s₀ := (hq.args 4 (by decide)).symm
  exact rel_wp (cmp_rel hO.comp hB (sp := E s₀) fun s s' ⟨⟨k, b, a⟩, ⟨k', b', a'⟩⟩ =>
      ⟨cmpArgs hz hp k hpR b a, by have := cmpArgs hz hp' k' hpR' b' a'; rwa [he, e4] at this, k.esp,
        by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, b, a⟩ => cmpS_ok hz hp hO k hpR b a fun _ k' _ _ _ => k')
    (fun _ ⟨k, b, a⟩ => cmpS_ok hz hp' hO k hpR' b a fun _ k' _ _ _ => k')

include hc in
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have hz := hO.sizes
  obtain e0 : inn s₀' = inn s₀ := (hq.args 0 (by decide)).symm
  obtain e1 : out s₀' = out s₀ := (hq.args 1 (by decide)).symm
  -- The prologue.
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀') :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact pro_ok hz hp)
      (fun _ e => by subst e; exact pro_ok hz hp')
  -- The blocks.
  obtain blk : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀')) H.blocks
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀ ∧ s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀' ∧ s'.gpr .eax = inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (argTaint [.ebp, .ebx, .esi] (4 + 4 * 5)) (fun s s' ⟨k, b⟩ ⟨k', b'⟩ =>
        agree_argTaint (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact kr_agree hq k k' _ (by simp)
            · rw [b, b', e0]
            · exact kr_agree hq k k' _ (by simp))
          (kr_agree hq k k' _ (by simp)) (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.blocks
      (fun _ ⟨k, b⟩ => blocks_ok hz hp k b)
      (fun _ ⟨k, b⟩ => blocks_ok hz hp' k b)
  -- From the inner state to the outer one.
  obtain tO : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (.block H.toOuter)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = out s₀ ∧ s.gpr .eax = out s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = out s₀' ∧ s'.gpr .eax = out s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (τr [.esp, .ebp, .esi]) (fun _ _ k k' => agree_regs (kr_agree hq k k')) hc.toOuter
      (fun _ k => WP.mono (toOuter_ok k) fun _ ⟨k', b, a, _⟩ => ⟨k', b, a⟩)
      (fun _ k => WP.mono (toOuter_ok k) fun _ ⟨k', b, a, _⟩ => ⟨k', b, a⟩)
  -- The end.
  obtain ⟨_, hr⟩ := hc.restore
  obtain restore : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact kr_agree hq h.1 h.2 _ (by simp)) hr
  exact pro.seq ((callInit_rel hO hp hp' hq (.inl ⟨rfl, rfl⟩)).seq
    ((callInit_rel hO hp hp' hq (.inr ⟨rfl, rfl⟩)).seq
    (blk.seq ((cmpS_rel hO hp hp' hq (.inl rfl) (.inl rfl) e0).seq
    (tO.seq ((cmpS_rel hO hp hp' hq (.inr rfl) (.inr rfl) e1).seq restore))))))

end VG.Proof.Pbkdf2.Md.X86.HmacInit

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initG initW)

/-- `init` is verified against `initG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H) (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initG hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacInit (initG hO.hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hO (pre_of sc hO hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (ct hO hc (pre_of sc hO h₁ hfit) (pre_of sc hO h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `init` reads and writes, of those `initW` gives it. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (S sc : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 1).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, 8 * sc⟩]

/-- `init` is verified against `initW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H) (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initW hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacInit (initW hO.hH.SH sc) := by
  obtain pre : ∀ s, (initW hO.hH.SH sc).pre s →
      (initG hO.hH.SH sc).pre (s.withRegions (narrowRd s)
        (narrowWr hO.hH.SH.stateBytes sc s)) := by
    intro s h
    obtain ⟨h0, _, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩ := h
    simp only [initG, narrowRd, narrowWr, arg_withRegions,
      argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
    exact ⟨h0, trivial, trivial, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩
  refine Verified.narrowTo (verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd) (narrowWr hO.hH.SH.stateBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
  · obtain ⟨_, _, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Md.X86.HmacInit
